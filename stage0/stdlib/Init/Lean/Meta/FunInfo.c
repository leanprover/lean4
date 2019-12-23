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
size_t l_USize_add(size_t, size_t);
size_t l_Lean_Meta_TransparencyMode_hash(uint8_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClassExpensive___main(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main(lean_object*, lean_object*, lean_object*);
extern size_t l_PersistentHashMap_insertAux___main___rarg___closed__2;
lean_object* l_Array_qsortAux___main___at___private_Init_Lean_Meta_FunInfo_4__collectDeps___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_FunInfo_4__collectDeps(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClassQuick___main(lean_object*, lean_object*, lean_object*);
size_t l_USize_sub(size_t, size_t);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at___private_Init_Lean_Meta_FunInfo_4__collectDeps___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__7(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find_x3f___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__1___boxed(lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_FunInfo_4__collectDeps___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_6__forallTelescopeReducingAux___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t l_Option_hash___at_Lean_Meta_InfoCacheKey_Hashable___spec__1(lean_object*);
lean_object* l___private_Init_Lean_Meta_FunInfo_2__whenHasVar___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_indexOfAux___main___at___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_indexOfAux___main___at___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Meta_FunInfo_5__updateHasFwdDeps___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
extern lean_object* l_PersistentHashMap_insertAux___main___rarg___closed__3;
size_t l_Lean_Expr_hash(lean_object*);
lean_object* l___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__2(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshId___rarg(lean_object*);
size_t l_USize_mul(size_t, size_t);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___private_Init_Lean_Meta_FunInfo_3__collectDepsAux(lean_object*, lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsortAux___main___at___private_Init_Lean_Meta_FunInfo_4__collectDeps___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_FunInfo_5__updateHasFwdDeps___boxed(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_BinderInfo_beq(uint8_t, uint8_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l___private_Init_Lean_Meta_FunInfo_2__whenHasVar___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at___private_Init_Lean_Meta_FunInfo_4__collectDeps___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_FunInfo_2__whenHasVar(lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Meta_FunInfo_5__updateHasFwdDeps___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l_PersistentHashMap_find_x3f___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l___private_Init_Lean_Meta_Basic_6__forallTelescopeReducingAux___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__2___closed__1;
size_t lean_usize_mix_hash(size_t, size_t);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_object* l_Array_contains___at___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__2___boxed(lean_object*, lean_object*);
extern lean_object* l_Nat_Inhabited;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Array_contains___at___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_FunInfo_5__updateHasFwdDeps(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insert___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*);
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
lean_object* l_PersistentHashMap_find_x3f___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 6);
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
x_11 = l_PersistentHashMap_find_x3f___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__1(x_9, x_10);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
x_25 = lean_ctor_get(x_14, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
lean_inc(x_16);
x_26 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4(x_24, x_10, x_16);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_13, 2, x_27);
return x_12;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_28 = lean_ctor_get(x_13, 0);
x_29 = lean_ctor_get(x_13, 1);
x_30 = lean_ctor_get(x_13, 3);
x_31 = lean_ctor_get(x_13, 4);
x_32 = lean_ctor_get(x_13, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_13);
x_33 = lean_ctor_get(x_14, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_14, 2);
lean_inc(x_35);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_36 = x_14;
} else {
 lean_dec_ref(x_14);
 x_36 = lean_box(0);
}
lean_inc(x_16);
x_37 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4(x_34, x_10, x_16);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 3, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_35);
x_39 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_39, 0, x_28);
lean_ctor_set(x_39, 1, x_29);
lean_ctor_set(x_39, 2, x_38);
lean_ctor_set(x_39, 3, x_30);
lean_ctor_set(x_39, 4, x_31);
lean_ctor_set(x_39, 5, x_32);
lean_ctor_set(x_12, 1, x_39);
return x_12;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_40 = lean_ctor_get(x_12, 0);
lean_inc(x_40);
lean_dec(x_12);
x_41 = lean_ctor_get(x_13, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_13, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_13, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_13, 4);
lean_inc(x_44);
x_45 = lean_ctor_get(x_13, 5);
lean_inc(x_45);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 lean_ctor_release(x_13, 4);
 lean_ctor_release(x_13, 5);
 x_46 = x_13;
} else {
 lean_dec_ref(x_13);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_14, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_14, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_14, 2);
lean_inc(x_49);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_50 = x_14;
} else {
 lean_dec_ref(x_14);
 x_50 = lean_box(0);
}
lean_inc(x_40);
x_51 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4(x_48, x_10, x_40);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 3, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_49);
if (lean_is_scalar(x_46)) {
 x_53 = lean_alloc_ctor(0, 6, 0);
} else {
 x_53 = x_46;
}
lean_ctor_set(x_53, 0, x_41);
lean_ctor_set(x_53, 1, x_42);
lean_ctor_set(x_53, 2, x_52);
lean_ctor_set(x_53, 3, x_43);
lean_ctor_set(x_53, 4, x_44);
lean_ctor_set(x_53, 5, x_45);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_40);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_10);
x_55 = !lean_is_exclusive(x_12);
if (x_55 == 0)
{
return x_12;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_12, 0);
x_57 = lean_ctor_get(x_12, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_12);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_59 = lean_ctor_get(x_11, 0);
lean_inc(x_59);
lean_dec(x_11);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_5);
return x_60;
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
lean_object* l_PersistentHashMap_find_x3f___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_find_x3f___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__1(x_1, x_2);
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
lean_object* l___private_Init_Lean_Meta_FunInfo_2__whenHasVar___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Init_Lean_Meta_FunInfo_2__whenHasVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_FunInfo_2__whenHasVar___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_FunInfo_2__whenHasVar___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_FunInfo_2__whenHasVar___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_indexOfAux___main___at___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
uint8_t l_Array_contains___at___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__3(x_1, x_2, x_1, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_indexOfAux___main___at___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__1(x_1, x_2, x_4);
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
x_7 = l_Array_contains___at___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__2(x_3, x_6);
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
x_12 = l___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main(x_1, x_9, x_3);
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
x_17 = l___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main(x_1, x_14, x_3);
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
x_22 = l___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main(x_1, x_19, x_3);
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
x_28 = l___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main(x_1, x_24, x_3);
x_29 = l___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main(x_1, x_25, x_28);
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
lean_object* l_Array_indexOfAux___main___at___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_indexOfAux___main___at___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_contains___at___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_FunInfo_3__collectDepsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_FunInfo_3__collectDepsAux(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at___private_Init_Lean_Meta_FunInfo_4__collectDeps___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Array_qsortAux___main___at___private_Init_Lean_Meta_FunInfo_4__collectDeps___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_24 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at___private_Init_Lean_Meta_FunInfo_4__collectDeps___spec__2(x_3, x_19, x_17, x_2, x_2);
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
x_27 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at___private_Init_Lean_Meta_FunInfo_4__collectDeps___spec__2(x_3, x_26, x_25, x_2, x_2);
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
x_32 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at___private_Init_Lean_Meta_FunInfo_4__collectDeps___spec__2(x_3, x_30, x_28, x_2, x_2);
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
x_35 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at___private_Init_Lean_Meta_FunInfo_4__collectDeps___spec__2(x_3, x_34, x_33, x_2, x_2);
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
x_8 = l_Array_qsortAux___main___at___private_Init_Lean_Meta_FunInfo_4__collectDeps___spec__1(x_6, x_2, x_5);
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
lean_object* l___private_Init_Lean_Meta_FunInfo_4__collectDeps(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Array_empty___closed__1;
x_4 = l___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main(x_1, x_2, x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_5, x_6);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_qsortAux___main___at___private_Init_Lean_Meta_FunInfo_4__collectDeps___spec__1(x_4, x_8, x_7);
lean_dec(x_7);
return x_9;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at___private_Init_Lean_Meta_FunInfo_4__collectDeps___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at___private_Init_Lean_Meta_FunInfo_4__collectDeps___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_qsortAux___main___at___private_Init_Lean_Meta_FunInfo_4__collectDeps___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsortAux___main___at___private_Init_Lean_Meta_FunInfo_4__collectDeps___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_FunInfo_4__collectDeps___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Meta_FunInfo_4__collectDeps(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Meta_FunInfo_5__updateHasFwdDeps___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_array_fget(x_3, x_2);
x_9 = lean_box(0);
x_10 = x_9;
x_11 = lean_array_fset(x_3, x_2, x_10);
x_12 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_13 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 1);
x_14 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 2);
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_2, x_16);
if (x_14 == 0)
{
uint8_t x_18; 
x_18 = l_Array_contains___at___private_Init_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__2(x_1, x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
lean_inc(x_8);
x_19 = x_8;
lean_dec(x_8);
x_20 = lean_array_fset(x_11, x_2, x_19);
lean_dec(x_2);
x_2 = x_17;
x_3 = x_20;
goto _start;
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = 1;
x_23 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_12);
lean_ctor_set_uint8(x_23, sizeof(void*)*1 + 1, x_13);
lean_ctor_set_uint8(x_23, sizeof(void*)*1 + 2, x_22);
x_24 = x_23;
lean_dec(x_8);
x_25 = lean_array_fset(x_11, x_2, x_24);
lean_dec(x_2);
x_2 = x_17;
x_3 = x_25;
goto _start;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_15);
lean_inc(x_8);
x_27 = x_8;
lean_dec(x_8);
x_28 = lean_array_fset(x_11, x_2, x_27);
lean_dec(x_2);
x_2 = x_17;
x_3 = x_28;
goto _start;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_FunInfo_5__updateHasFwdDeps(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Array_umapMAux___main___at___private_Init_Lean_Meta_FunInfo_5__updateHasFwdDeps___spec__1(x_2, x_4, x_1);
return x_6;
}
else
{
return x_1;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Meta_FunInfo_5__updateHasFwdDeps___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Init_Lean_Meta_FunInfo_5__updateHasFwdDeps___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_FunInfo_5__updateHasFwdDeps___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Meta_FunInfo_5__updateHasFwdDeps(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_3, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_3, x_9);
lean_dec(x_3);
x_11 = lean_nat_sub(x_2, x_10);
x_12 = lean_nat_sub(x_11, x_9);
lean_dec(x_11);
x_13 = l_Lean_Expr_Inhabited;
x_14 = lean_array_get(x_13, x_1, x_12);
lean_dec(x_12);
lean_inc(x_5);
x_15 = l_Lean_Meta_getFVarLocalDecl(x_14, x_5, x_6);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_LocalDecl_type(x_16);
x_19 = l___private_Init_Lean_Meta_FunInfo_4__collectDeps(x_1, x_18);
lean_dec(x_18);
x_20 = l___private_Init_Lean_Meta_FunInfo_5__updateHasFwdDeps(x_4, x_19);
x_21 = l_Lean_LocalDecl_binderInfo(x_16);
lean_dec(x_16);
x_22 = 1;
x_23 = l_Lean_BinderInfo_beq(x_21, x_22);
x_24 = 3;
x_25 = l_Lean_BinderInfo_beq(x_21, x_24);
x_26 = 0;
x_27 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*1 + 1, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1 + 2, x_26);
x_28 = lean_array_push(x_20, x_27);
x_3 = x_10;
x_4 = x_28;
x_6 = x_17;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_5);
lean_dec(x_3);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_6);
return x_34;
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_4);
x_9 = lean_nat_dec_lt(x_5, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
x_10 = l_Array_empty___closed__1;
lean_inc(x_2);
x_11 = l_Nat_foldMAux___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__1(x_1, x_2, x_2, x_10, x_6, x_7);
lean_dec(x_2);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l___private_Init_Lean_Meta_FunInfo_4__collectDeps(x_1, x_3);
x_15 = l___private_Init_Lean_Meta_FunInfo_5__updateHasFwdDeps(x_13, x_14);
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
x_19 = l___private_Init_Lean_Meta_FunInfo_4__collectDeps(x_1, x_3);
x_20 = l___private_Init_Lean_Meta_FunInfo_5__updateHasFwdDeps(x_17, x_19);
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
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_array_fget(x_4, x_5);
lean_inc(x_6);
x_28 = l_Lean_Meta_getFVarLocalDecl(x_27, x_6, x_7);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_LocalDecl_type(x_29);
lean_dec(x_29);
lean_inc(x_6);
lean_inc(x_31);
x_32 = l_Lean_Meta_isClassQuick___main(x_31, x_6, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
switch (lean_obj_tag(x_33)) {
case 0:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_27);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_5, x_35);
lean_dec(x_5);
x_5 = x_36;
x_7 = x_34;
goto _start;
}
case 1:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_31);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_dec(x_32);
x_39 = lean_ctor_get(x_33, 0);
lean_inc(x_39);
lean_dec(x_33);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_5, x_40);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_38, 2);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_43, 2);
x_46 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_43, 2, x_46);
x_47 = !lean_is_exclusive(x_6);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_6, 2);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_27);
x_50 = lean_array_push(x_48, x_49);
lean_ctor_set(x_6, 2, x_50);
x_51 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4(x_1, x_2, x_3, x_4, x_41, x_6, x_38);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_52, 2);
lean_inc(x_53);
x_54 = !lean_is_exclusive(x_51);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_51, 1);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_52, 2);
lean_dec(x_57);
x_58 = !lean_is_exclusive(x_53);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_53, 2);
lean_dec(x_59);
lean_ctor_set(x_53, 2, x_45);
return x_51;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_53, 0);
x_61 = lean_ctor_get(x_53, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_53);
x_62 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_62, 2, x_45);
lean_ctor_set(x_52, 2, x_62);
return x_51;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_63 = lean_ctor_get(x_52, 0);
x_64 = lean_ctor_get(x_52, 1);
x_65 = lean_ctor_get(x_52, 3);
x_66 = lean_ctor_get(x_52, 4);
x_67 = lean_ctor_get(x_52, 5);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_52);
x_68 = lean_ctor_get(x_53, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_53, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 lean_ctor_release(x_53, 2);
 x_70 = x_53;
} else {
 lean_dec_ref(x_53);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 3, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
lean_ctor_set(x_71, 2, x_45);
x_72 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_72, 0, x_63);
lean_ctor_set(x_72, 1, x_64);
lean_ctor_set(x_72, 2, x_71);
lean_ctor_set(x_72, 3, x_65);
lean_ctor_set(x_72, 4, x_66);
lean_ctor_set(x_72, 5, x_67);
lean_ctor_set(x_51, 1, x_72);
return x_51;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_73 = lean_ctor_get(x_51, 0);
lean_inc(x_73);
lean_dec(x_51);
x_74 = lean_ctor_get(x_52, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_52, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_52, 3);
lean_inc(x_76);
x_77 = lean_ctor_get(x_52, 4);
lean_inc(x_77);
x_78 = lean_ctor_get(x_52, 5);
lean_inc(x_78);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 lean_ctor_release(x_52, 4);
 lean_ctor_release(x_52, 5);
 x_79 = x_52;
} else {
 lean_dec_ref(x_52);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_53, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_53, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 lean_ctor_release(x_53, 2);
 x_82 = x_53;
} else {
 lean_dec_ref(x_53);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 3, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
lean_ctor_set(x_83, 2, x_45);
if (lean_is_scalar(x_79)) {
 x_84 = lean_alloc_ctor(0, 6, 0);
} else {
 x_84 = x_79;
}
lean_ctor_set(x_84, 0, x_74);
lean_ctor_set(x_84, 1, x_75);
lean_ctor_set(x_84, 2, x_83);
lean_ctor_set(x_84, 3, x_76);
lean_ctor_set(x_84, 4, x_77);
lean_ctor_set(x_84, 5, x_78);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_73);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_ctor_get(x_51, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_86, 2);
lean_inc(x_87);
x_88 = !lean_is_exclusive(x_51);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_51, 1);
lean_dec(x_89);
x_90 = !lean_is_exclusive(x_86);
if (x_90 == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_86, 2);
lean_dec(x_91);
x_92 = !lean_is_exclusive(x_87);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_87, 2);
lean_dec(x_93);
lean_ctor_set(x_87, 2, x_45);
return x_51;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_87, 0);
x_95 = lean_ctor_get(x_87, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_87);
x_96 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_96, 2, x_45);
lean_ctor_set(x_86, 2, x_96);
return x_51;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_97 = lean_ctor_get(x_86, 0);
x_98 = lean_ctor_get(x_86, 1);
x_99 = lean_ctor_get(x_86, 3);
x_100 = lean_ctor_get(x_86, 4);
x_101 = lean_ctor_get(x_86, 5);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_86);
x_102 = lean_ctor_get(x_87, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_87, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 lean_ctor_release(x_87, 2);
 x_104 = x_87;
} else {
 lean_dec_ref(x_87);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(0, 3, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
lean_ctor_set(x_105, 2, x_45);
x_106 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_106, 0, x_97);
lean_ctor_set(x_106, 1, x_98);
lean_ctor_set(x_106, 2, x_105);
lean_ctor_set(x_106, 3, x_99);
lean_ctor_set(x_106, 4, x_100);
lean_ctor_set(x_106, 5, x_101);
lean_ctor_set(x_51, 1, x_106);
return x_51;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_107 = lean_ctor_get(x_51, 0);
lean_inc(x_107);
lean_dec(x_51);
x_108 = lean_ctor_get(x_86, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_86, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_86, 3);
lean_inc(x_110);
x_111 = lean_ctor_get(x_86, 4);
lean_inc(x_111);
x_112 = lean_ctor_get(x_86, 5);
lean_inc(x_112);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 lean_ctor_release(x_86, 2);
 lean_ctor_release(x_86, 3);
 lean_ctor_release(x_86, 4);
 lean_ctor_release(x_86, 5);
 x_113 = x_86;
} else {
 lean_dec_ref(x_86);
 x_113 = lean_box(0);
}
x_114 = lean_ctor_get(x_87, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_87, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 lean_ctor_release(x_87, 2);
 x_116 = x_87;
} else {
 lean_dec_ref(x_87);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(0, 3, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
lean_ctor_set(x_117, 2, x_45);
if (lean_is_scalar(x_113)) {
 x_118 = lean_alloc_ctor(0, 6, 0);
} else {
 x_118 = x_113;
}
lean_ctor_set(x_118, 0, x_108);
lean_ctor_set(x_118, 1, x_109);
lean_ctor_set(x_118, 2, x_117);
lean_ctor_set(x_118, 3, x_110);
lean_ctor_set(x_118, 4, x_111);
lean_ctor_set(x_118, 5, x_112);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_107);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_120 = lean_ctor_get(x_6, 0);
x_121 = lean_ctor_get(x_6, 1);
x_122 = lean_ctor_get(x_6, 2);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_6);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_39);
lean_ctor_set(x_123, 1, x_27);
x_124 = lean_array_push(x_122, x_123);
x_125 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_125, 0, x_120);
lean_ctor_set(x_125, 1, x_121);
lean_ctor_set(x_125, 2, x_124);
x_126 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4(x_1, x_2, x_3, x_4, x_41, x_125, x_38);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_127, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_126, 0);
lean_inc(x_129);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_130 = x_126;
} else {
 lean_dec_ref(x_126);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_127, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_127, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_127, 3);
lean_inc(x_133);
x_134 = lean_ctor_get(x_127, 4);
lean_inc(x_134);
x_135 = lean_ctor_get(x_127, 5);
lean_inc(x_135);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 lean_ctor_release(x_127, 3);
 lean_ctor_release(x_127, 4);
 lean_ctor_release(x_127, 5);
 x_136 = x_127;
} else {
 lean_dec_ref(x_127);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get(x_128, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_128, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 lean_ctor_release(x_128, 2);
 x_139 = x_128;
} else {
 lean_dec_ref(x_128);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(0, 3, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
lean_ctor_set(x_140, 2, x_45);
if (lean_is_scalar(x_136)) {
 x_141 = lean_alloc_ctor(0, 6, 0);
} else {
 x_141 = x_136;
}
lean_ctor_set(x_141, 0, x_131);
lean_ctor_set(x_141, 1, x_132);
lean_ctor_set(x_141, 2, x_140);
lean_ctor_set(x_141, 3, x_133);
lean_ctor_set(x_141, 4, x_134);
lean_ctor_set(x_141, 5, x_135);
if (lean_is_scalar(x_130)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_130;
}
lean_ctor_set(x_142, 0, x_129);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_143 = lean_ctor_get(x_126, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_143, 2);
lean_inc(x_144);
x_145 = lean_ctor_get(x_126, 0);
lean_inc(x_145);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_146 = x_126;
} else {
 lean_dec_ref(x_126);
 x_146 = lean_box(0);
}
x_147 = lean_ctor_get(x_143, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_143, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_143, 3);
lean_inc(x_149);
x_150 = lean_ctor_get(x_143, 4);
lean_inc(x_150);
x_151 = lean_ctor_get(x_143, 5);
lean_inc(x_151);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 lean_ctor_release(x_143, 2);
 lean_ctor_release(x_143, 3);
 lean_ctor_release(x_143, 4);
 lean_ctor_release(x_143, 5);
 x_152 = x_143;
} else {
 lean_dec_ref(x_143);
 x_152 = lean_box(0);
}
x_153 = lean_ctor_get(x_144, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_144, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 lean_ctor_release(x_144, 2);
 x_155 = x_144;
} else {
 lean_dec_ref(x_144);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(0, 3, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
lean_ctor_set(x_156, 2, x_45);
if (lean_is_scalar(x_152)) {
 x_157 = lean_alloc_ctor(0, 6, 0);
} else {
 x_157 = x_152;
}
lean_ctor_set(x_157, 0, x_147);
lean_ctor_set(x_157, 1, x_148);
lean_ctor_set(x_157, 2, x_156);
lean_ctor_set(x_157, 3, x_149);
lean_ctor_set(x_157, 4, x_150);
lean_ctor_set(x_157, 5, x_151);
if (lean_is_scalar(x_146)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_146;
}
lean_ctor_set(x_158, 0, x_145);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_159 = lean_ctor_get(x_43, 0);
x_160 = lean_ctor_get(x_43, 1);
x_161 = lean_ctor_get(x_43, 2);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_43);
x_162 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_163 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_163, 0, x_159);
lean_ctor_set(x_163, 1, x_160);
lean_ctor_set(x_163, 2, x_162);
lean_ctor_set(x_38, 2, x_163);
x_164 = lean_ctor_get(x_6, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_6, 1);
lean_inc(x_165);
x_166 = lean_ctor_get(x_6, 2);
lean_inc(x_166);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 x_167 = x_6;
} else {
 lean_dec_ref(x_6);
 x_167 = lean_box(0);
}
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_39);
lean_ctor_set(x_168, 1, x_27);
x_169 = lean_array_push(x_166, x_168);
if (lean_is_scalar(x_167)) {
 x_170 = lean_alloc_ctor(0, 3, 0);
} else {
 x_170 = x_167;
}
lean_ctor_set(x_170, 0, x_164);
lean_ctor_set(x_170, 1, x_165);
lean_ctor_set(x_170, 2, x_169);
x_171 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4(x_1, x_2, x_3, x_4, x_41, x_170, x_38);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_172, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_171, 0);
lean_inc(x_174);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_175 = x_171;
} else {
 lean_dec_ref(x_171);
 x_175 = lean_box(0);
}
x_176 = lean_ctor_get(x_172, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_172, 1);
lean_inc(x_177);
x_178 = lean_ctor_get(x_172, 3);
lean_inc(x_178);
x_179 = lean_ctor_get(x_172, 4);
lean_inc(x_179);
x_180 = lean_ctor_get(x_172, 5);
lean_inc(x_180);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 lean_ctor_release(x_172, 2);
 lean_ctor_release(x_172, 3);
 lean_ctor_release(x_172, 4);
 lean_ctor_release(x_172, 5);
 x_181 = x_172;
} else {
 lean_dec_ref(x_172);
 x_181 = lean_box(0);
}
x_182 = lean_ctor_get(x_173, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_173, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 lean_ctor_release(x_173, 2);
 x_184 = x_173;
} else {
 lean_dec_ref(x_173);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(0, 3, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
lean_ctor_set(x_185, 2, x_161);
if (lean_is_scalar(x_181)) {
 x_186 = lean_alloc_ctor(0, 6, 0);
} else {
 x_186 = x_181;
}
lean_ctor_set(x_186, 0, x_176);
lean_ctor_set(x_186, 1, x_177);
lean_ctor_set(x_186, 2, x_185);
lean_ctor_set(x_186, 3, x_178);
lean_ctor_set(x_186, 4, x_179);
lean_ctor_set(x_186, 5, x_180);
if (lean_is_scalar(x_175)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_175;
}
lean_ctor_set(x_187, 0, x_174);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_188 = lean_ctor_get(x_171, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_188, 2);
lean_inc(x_189);
x_190 = lean_ctor_get(x_171, 0);
lean_inc(x_190);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_191 = x_171;
} else {
 lean_dec_ref(x_171);
 x_191 = lean_box(0);
}
x_192 = lean_ctor_get(x_188, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_188, 1);
lean_inc(x_193);
x_194 = lean_ctor_get(x_188, 3);
lean_inc(x_194);
x_195 = lean_ctor_get(x_188, 4);
lean_inc(x_195);
x_196 = lean_ctor_get(x_188, 5);
lean_inc(x_196);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 lean_ctor_release(x_188, 4);
 lean_ctor_release(x_188, 5);
 x_197 = x_188;
} else {
 lean_dec_ref(x_188);
 x_197 = lean_box(0);
}
x_198 = lean_ctor_get(x_189, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_189, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 lean_ctor_release(x_189, 2);
 x_200 = x_189;
} else {
 lean_dec_ref(x_189);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(0, 3, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
lean_ctor_set(x_201, 2, x_161);
if (lean_is_scalar(x_197)) {
 x_202 = lean_alloc_ctor(0, 6, 0);
} else {
 x_202 = x_197;
}
lean_ctor_set(x_202, 0, x_192);
lean_ctor_set(x_202, 1, x_193);
lean_ctor_set(x_202, 2, x_201);
lean_ctor_set(x_202, 3, x_194);
lean_ctor_set(x_202, 4, x_195);
lean_ctor_set(x_202, 5, x_196);
if (lean_is_scalar(x_191)) {
 x_203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_203 = x_191;
}
lean_ctor_set(x_203, 0, x_190);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_204 = lean_ctor_get(x_38, 2);
x_205 = lean_ctor_get(x_38, 0);
x_206 = lean_ctor_get(x_38, 1);
x_207 = lean_ctor_get(x_38, 3);
x_208 = lean_ctor_get(x_38, 4);
x_209 = lean_ctor_get(x_38, 5);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
lean_inc(x_204);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_38);
x_210 = lean_ctor_get(x_204, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_204, 1);
lean_inc(x_211);
x_212 = lean_ctor_get(x_204, 2);
lean_inc(x_212);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 lean_ctor_release(x_204, 2);
 x_213 = x_204;
} else {
 lean_dec_ref(x_204);
 x_213 = lean_box(0);
}
x_214 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_213)) {
 x_215 = lean_alloc_ctor(0, 3, 0);
} else {
 x_215 = x_213;
}
lean_ctor_set(x_215, 0, x_210);
lean_ctor_set(x_215, 1, x_211);
lean_ctor_set(x_215, 2, x_214);
x_216 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_216, 0, x_205);
lean_ctor_set(x_216, 1, x_206);
lean_ctor_set(x_216, 2, x_215);
lean_ctor_set(x_216, 3, x_207);
lean_ctor_set(x_216, 4, x_208);
lean_ctor_set(x_216, 5, x_209);
x_217 = lean_ctor_get(x_6, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_6, 1);
lean_inc(x_218);
x_219 = lean_ctor_get(x_6, 2);
lean_inc(x_219);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 x_220 = x_6;
} else {
 lean_dec_ref(x_6);
 x_220 = lean_box(0);
}
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_39);
lean_ctor_set(x_221, 1, x_27);
x_222 = lean_array_push(x_219, x_221);
if (lean_is_scalar(x_220)) {
 x_223 = lean_alloc_ctor(0, 3, 0);
} else {
 x_223 = x_220;
}
lean_ctor_set(x_223, 0, x_217);
lean_ctor_set(x_223, 1, x_218);
lean_ctor_set(x_223, 2, x_222);
x_224 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4(x_1, x_2, x_3, x_4, x_41, x_223, x_216);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
x_226 = lean_ctor_get(x_225, 2);
lean_inc(x_226);
x_227 = lean_ctor_get(x_224, 0);
lean_inc(x_227);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_228 = x_224;
} else {
 lean_dec_ref(x_224);
 x_228 = lean_box(0);
}
x_229 = lean_ctor_get(x_225, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_225, 1);
lean_inc(x_230);
x_231 = lean_ctor_get(x_225, 3);
lean_inc(x_231);
x_232 = lean_ctor_get(x_225, 4);
lean_inc(x_232);
x_233 = lean_ctor_get(x_225, 5);
lean_inc(x_233);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 lean_ctor_release(x_225, 2);
 lean_ctor_release(x_225, 3);
 lean_ctor_release(x_225, 4);
 lean_ctor_release(x_225, 5);
 x_234 = x_225;
} else {
 lean_dec_ref(x_225);
 x_234 = lean_box(0);
}
x_235 = lean_ctor_get(x_226, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_226, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 lean_ctor_release(x_226, 2);
 x_237 = x_226;
} else {
 lean_dec_ref(x_226);
 x_237 = lean_box(0);
}
if (lean_is_scalar(x_237)) {
 x_238 = lean_alloc_ctor(0, 3, 0);
} else {
 x_238 = x_237;
}
lean_ctor_set(x_238, 0, x_235);
lean_ctor_set(x_238, 1, x_236);
lean_ctor_set(x_238, 2, x_212);
if (lean_is_scalar(x_234)) {
 x_239 = lean_alloc_ctor(0, 6, 0);
} else {
 x_239 = x_234;
}
lean_ctor_set(x_239, 0, x_229);
lean_ctor_set(x_239, 1, x_230);
lean_ctor_set(x_239, 2, x_238);
lean_ctor_set(x_239, 3, x_231);
lean_ctor_set(x_239, 4, x_232);
lean_ctor_set(x_239, 5, x_233);
if (lean_is_scalar(x_228)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_228;
}
lean_ctor_set(x_240, 0, x_227);
lean_ctor_set(x_240, 1, x_239);
return x_240;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_241 = lean_ctor_get(x_224, 1);
lean_inc(x_241);
x_242 = lean_ctor_get(x_241, 2);
lean_inc(x_242);
x_243 = lean_ctor_get(x_224, 0);
lean_inc(x_243);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_244 = x_224;
} else {
 lean_dec_ref(x_224);
 x_244 = lean_box(0);
}
x_245 = lean_ctor_get(x_241, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_241, 1);
lean_inc(x_246);
x_247 = lean_ctor_get(x_241, 3);
lean_inc(x_247);
x_248 = lean_ctor_get(x_241, 4);
lean_inc(x_248);
x_249 = lean_ctor_get(x_241, 5);
lean_inc(x_249);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 lean_ctor_release(x_241, 2);
 lean_ctor_release(x_241, 3);
 lean_ctor_release(x_241, 4);
 lean_ctor_release(x_241, 5);
 x_250 = x_241;
} else {
 lean_dec_ref(x_241);
 x_250 = lean_box(0);
}
x_251 = lean_ctor_get(x_242, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_242, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 lean_ctor_release(x_242, 2);
 x_253 = x_242;
} else {
 lean_dec_ref(x_242);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(0, 3, 0);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_251);
lean_ctor_set(x_254, 1, x_252);
lean_ctor_set(x_254, 2, x_212);
if (lean_is_scalar(x_250)) {
 x_255 = lean_alloc_ctor(0, 6, 0);
} else {
 x_255 = x_250;
}
lean_ctor_set(x_255, 0, x_245);
lean_ctor_set(x_255, 1, x_246);
lean_ctor_set(x_255, 2, x_254);
lean_ctor_set(x_255, 3, x_247);
lean_ctor_set(x_255, 4, x_248);
lean_ctor_set(x_255, 5, x_249);
if (lean_is_scalar(x_244)) {
 x_256 = lean_alloc_ctor(1, 2, 0);
} else {
 x_256 = x_244;
}
lean_ctor_set(x_256, 0, x_243);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
default: 
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_32, 1);
lean_inc(x_257);
lean_dec(x_32);
lean_inc(x_6);
x_258 = l_Lean_Meta_isClassExpensive___main(x_31, x_6, x_257);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_27);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec(x_258);
x_261 = lean_unsigned_to_nat(1u);
x_262 = lean_nat_add(x_5, x_261);
lean_dec(x_5);
x_5 = x_262;
x_7 = x_260;
goto _start;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; 
x_264 = lean_ctor_get(x_258, 1);
lean_inc(x_264);
lean_dec(x_258);
x_265 = lean_ctor_get(x_259, 0);
lean_inc(x_265);
lean_dec(x_259);
x_266 = lean_unsigned_to_nat(1u);
x_267 = lean_nat_add(x_5, x_266);
lean_dec(x_5);
x_268 = !lean_is_exclusive(x_264);
if (x_268 == 0)
{
lean_object* x_269; uint8_t x_270; 
x_269 = lean_ctor_get(x_264, 2);
x_270 = !lean_is_exclusive(x_269);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; uint8_t x_273; 
x_271 = lean_ctor_get(x_269, 2);
x_272 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_269, 2, x_272);
x_273 = !lean_is_exclusive(x_6);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_274 = lean_ctor_get(x_6, 2);
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_265);
lean_ctor_set(x_275, 1, x_27);
x_276 = lean_array_push(x_274, x_275);
lean_ctor_set(x_6, 2, x_276);
x_277 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4(x_1, x_2, x_3, x_4, x_267, x_6, x_264);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; uint8_t x_280; 
x_278 = lean_ctor_get(x_277, 1);
lean_inc(x_278);
x_279 = lean_ctor_get(x_278, 2);
lean_inc(x_279);
x_280 = !lean_is_exclusive(x_277);
if (x_280 == 0)
{
lean_object* x_281; uint8_t x_282; 
x_281 = lean_ctor_get(x_277, 1);
lean_dec(x_281);
x_282 = !lean_is_exclusive(x_278);
if (x_282 == 0)
{
lean_object* x_283; uint8_t x_284; 
x_283 = lean_ctor_get(x_278, 2);
lean_dec(x_283);
x_284 = !lean_is_exclusive(x_279);
if (x_284 == 0)
{
lean_object* x_285; 
x_285 = lean_ctor_get(x_279, 2);
lean_dec(x_285);
lean_ctor_set(x_279, 2, x_271);
return x_277;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_279, 0);
x_287 = lean_ctor_get(x_279, 1);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_279);
x_288 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
lean_ctor_set(x_288, 2, x_271);
lean_ctor_set(x_278, 2, x_288);
return x_277;
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_289 = lean_ctor_get(x_278, 0);
x_290 = lean_ctor_get(x_278, 1);
x_291 = lean_ctor_get(x_278, 3);
x_292 = lean_ctor_get(x_278, 4);
x_293 = lean_ctor_get(x_278, 5);
lean_inc(x_293);
lean_inc(x_292);
lean_inc(x_291);
lean_inc(x_290);
lean_inc(x_289);
lean_dec(x_278);
x_294 = lean_ctor_get(x_279, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_279, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 lean_ctor_release(x_279, 2);
 x_296 = x_279;
} else {
 lean_dec_ref(x_279);
 x_296 = lean_box(0);
}
if (lean_is_scalar(x_296)) {
 x_297 = lean_alloc_ctor(0, 3, 0);
} else {
 x_297 = x_296;
}
lean_ctor_set(x_297, 0, x_294);
lean_ctor_set(x_297, 1, x_295);
lean_ctor_set(x_297, 2, x_271);
x_298 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_298, 0, x_289);
lean_ctor_set(x_298, 1, x_290);
lean_ctor_set(x_298, 2, x_297);
lean_ctor_set(x_298, 3, x_291);
lean_ctor_set(x_298, 4, x_292);
lean_ctor_set(x_298, 5, x_293);
lean_ctor_set(x_277, 1, x_298);
return x_277;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_299 = lean_ctor_get(x_277, 0);
lean_inc(x_299);
lean_dec(x_277);
x_300 = lean_ctor_get(x_278, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_278, 1);
lean_inc(x_301);
x_302 = lean_ctor_get(x_278, 3);
lean_inc(x_302);
x_303 = lean_ctor_get(x_278, 4);
lean_inc(x_303);
x_304 = lean_ctor_get(x_278, 5);
lean_inc(x_304);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 lean_ctor_release(x_278, 2);
 lean_ctor_release(x_278, 3);
 lean_ctor_release(x_278, 4);
 lean_ctor_release(x_278, 5);
 x_305 = x_278;
} else {
 lean_dec_ref(x_278);
 x_305 = lean_box(0);
}
x_306 = lean_ctor_get(x_279, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_279, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 lean_ctor_release(x_279, 2);
 x_308 = x_279;
} else {
 lean_dec_ref(x_279);
 x_308 = lean_box(0);
}
if (lean_is_scalar(x_308)) {
 x_309 = lean_alloc_ctor(0, 3, 0);
} else {
 x_309 = x_308;
}
lean_ctor_set(x_309, 0, x_306);
lean_ctor_set(x_309, 1, x_307);
lean_ctor_set(x_309, 2, x_271);
if (lean_is_scalar(x_305)) {
 x_310 = lean_alloc_ctor(0, 6, 0);
} else {
 x_310 = x_305;
}
lean_ctor_set(x_310, 0, x_300);
lean_ctor_set(x_310, 1, x_301);
lean_ctor_set(x_310, 2, x_309);
lean_ctor_set(x_310, 3, x_302);
lean_ctor_set(x_310, 4, x_303);
lean_ctor_set(x_310, 5, x_304);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_299);
lean_ctor_set(x_311, 1, x_310);
return x_311;
}
}
else
{
lean_object* x_312; lean_object* x_313; uint8_t x_314; 
x_312 = lean_ctor_get(x_277, 1);
lean_inc(x_312);
x_313 = lean_ctor_get(x_312, 2);
lean_inc(x_313);
x_314 = !lean_is_exclusive(x_277);
if (x_314 == 0)
{
lean_object* x_315; uint8_t x_316; 
x_315 = lean_ctor_get(x_277, 1);
lean_dec(x_315);
x_316 = !lean_is_exclusive(x_312);
if (x_316 == 0)
{
lean_object* x_317; uint8_t x_318; 
x_317 = lean_ctor_get(x_312, 2);
lean_dec(x_317);
x_318 = !lean_is_exclusive(x_313);
if (x_318 == 0)
{
lean_object* x_319; 
x_319 = lean_ctor_get(x_313, 2);
lean_dec(x_319);
lean_ctor_set(x_313, 2, x_271);
return x_277;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_313, 0);
x_321 = lean_ctor_get(x_313, 1);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_313);
x_322 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
lean_ctor_set(x_322, 2, x_271);
lean_ctor_set(x_312, 2, x_322);
return x_277;
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_323 = lean_ctor_get(x_312, 0);
x_324 = lean_ctor_get(x_312, 1);
x_325 = lean_ctor_get(x_312, 3);
x_326 = lean_ctor_get(x_312, 4);
x_327 = lean_ctor_get(x_312, 5);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_312);
x_328 = lean_ctor_get(x_313, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_313, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 lean_ctor_release(x_313, 2);
 x_330 = x_313;
} else {
 lean_dec_ref(x_313);
 x_330 = lean_box(0);
}
if (lean_is_scalar(x_330)) {
 x_331 = lean_alloc_ctor(0, 3, 0);
} else {
 x_331 = x_330;
}
lean_ctor_set(x_331, 0, x_328);
lean_ctor_set(x_331, 1, x_329);
lean_ctor_set(x_331, 2, x_271);
x_332 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_332, 0, x_323);
lean_ctor_set(x_332, 1, x_324);
lean_ctor_set(x_332, 2, x_331);
lean_ctor_set(x_332, 3, x_325);
lean_ctor_set(x_332, 4, x_326);
lean_ctor_set(x_332, 5, x_327);
lean_ctor_set(x_277, 1, x_332);
return x_277;
}
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_333 = lean_ctor_get(x_277, 0);
lean_inc(x_333);
lean_dec(x_277);
x_334 = lean_ctor_get(x_312, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_312, 1);
lean_inc(x_335);
x_336 = lean_ctor_get(x_312, 3);
lean_inc(x_336);
x_337 = lean_ctor_get(x_312, 4);
lean_inc(x_337);
x_338 = lean_ctor_get(x_312, 5);
lean_inc(x_338);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 lean_ctor_release(x_312, 2);
 lean_ctor_release(x_312, 3);
 lean_ctor_release(x_312, 4);
 lean_ctor_release(x_312, 5);
 x_339 = x_312;
} else {
 lean_dec_ref(x_312);
 x_339 = lean_box(0);
}
x_340 = lean_ctor_get(x_313, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_313, 1);
lean_inc(x_341);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 lean_ctor_release(x_313, 2);
 x_342 = x_313;
} else {
 lean_dec_ref(x_313);
 x_342 = lean_box(0);
}
if (lean_is_scalar(x_342)) {
 x_343 = lean_alloc_ctor(0, 3, 0);
} else {
 x_343 = x_342;
}
lean_ctor_set(x_343, 0, x_340);
lean_ctor_set(x_343, 1, x_341);
lean_ctor_set(x_343, 2, x_271);
if (lean_is_scalar(x_339)) {
 x_344 = lean_alloc_ctor(0, 6, 0);
} else {
 x_344 = x_339;
}
lean_ctor_set(x_344, 0, x_334);
lean_ctor_set(x_344, 1, x_335);
lean_ctor_set(x_344, 2, x_343);
lean_ctor_set(x_344, 3, x_336);
lean_ctor_set(x_344, 4, x_337);
lean_ctor_set(x_344, 5, x_338);
x_345 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_345, 0, x_333);
lean_ctor_set(x_345, 1, x_344);
return x_345;
}
}
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_346 = lean_ctor_get(x_6, 0);
x_347 = lean_ctor_get(x_6, 1);
x_348 = lean_ctor_get(x_6, 2);
lean_inc(x_348);
lean_inc(x_347);
lean_inc(x_346);
lean_dec(x_6);
x_349 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_349, 0, x_265);
lean_ctor_set(x_349, 1, x_27);
x_350 = lean_array_push(x_348, x_349);
x_351 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_351, 0, x_346);
lean_ctor_set(x_351, 1, x_347);
lean_ctor_set(x_351, 2, x_350);
x_352 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4(x_1, x_2, x_3, x_4, x_267, x_351, x_264);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_353 = lean_ctor_get(x_352, 1);
lean_inc(x_353);
x_354 = lean_ctor_get(x_353, 2);
lean_inc(x_354);
x_355 = lean_ctor_get(x_352, 0);
lean_inc(x_355);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_356 = x_352;
} else {
 lean_dec_ref(x_352);
 x_356 = lean_box(0);
}
x_357 = lean_ctor_get(x_353, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_353, 1);
lean_inc(x_358);
x_359 = lean_ctor_get(x_353, 3);
lean_inc(x_359);
x_360 = lean_ctor_get(x_353, 4);
lean_inc(x_360);
x_361 = lean_ctor_get(x_353, 5);
lean_inc(x_361);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 lean_ctor_release(x_353, 4);
 lean_ctor_release(x_353, 5);
 x_362 = x_353;
} else {
 lean_dec_ref(x_353);
 x_362 = lean_box(0);
}
x_363 = lean_ctor_get(x_354, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_354, 1);
lean_inc(x_364);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 lean_ctor_release(x_354, 2);
 x_365 = x_354;
} else {
 lean_dec_ref(x_354);
 x_365 = lean_box(0);
}
if (lean_is_scalar(x_365)) {
 x_366 = lean_alloc_ctor(0, 3, 0);
} else {
 x_366 = x_365;
}
lean_ctor_set(x_366, 0, x_363);
lean_ctor_set(x_366, 1, x_364);
lean_ctor_set(x_366, 2, x_271);
if (lean_is_scalar(x_362)) {
 x_367 = lean_alloc_ctor(0, 6, 0);
} else {
 x_367 = x_362;
}
lean_ctor_set(x_367, 0, x_357);
lean_ctor_set(x_367, 1, x_358);
lean_ctor_set(x_367, 2, x_366);
lean_ctor_set(x_367, 3, x_359);
lean_ctor_set(x_367, 4, x_360);
lean_ctor_set(x_367, 5, x_361);
if (lean_is_scalar(x_356)) {
 x_368 = lean_alloc_ctor(0, 2, 0);
} else {
 x_368 = x_356;
}
lean_ctor_set(x_368, 0, x_355);
lean_ctor_set(x_368, 1, x_367);
return x_368;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_369 = lean_ctor_get(x_352, 1);
lean_inc(x_369);
x_370 = lean_ctor_get(x_369, 2);
lean_inc(x_370);
x_371 = lean_ctor_get(x_352, 0);
lean_inc(x_371);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_372 = x_352;
} else {
 lean_dec_ref(x_352);
 x_372 = lean_box(0);
}
x_373 = lean_ctor_get(x_369, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_369, 1);
lean_inc(x_374);
x_375 = lean_ctor_get(x_369, 3);
lean_inc(x_375);
x_376 = lean_ctor_get(x_369, 4);
lean_inc(x_376);
x_377 = lean_ctor_get(x_369, 5);
lean_inc(x_377);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 lean_ctor_release(x_369, 2);
 lean_ctor_release(x_369, 3);
 lean_ctor_release(x_369, 4);
 lean_ctor_release(x_369, 5);
 x_378 = x_369;
} else {
 lean_dec_ref(x_369);
 x_378 = lean_box(0);
}
x_379 = lean_ctor_get(x_370, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_370, 1);
lean_inc(x_380);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 lean_ctor_release(x_370, 2);
 x_381 = x_370;
} else {
 lean_dec_ref(x_370);
 x_381 = lean_box(0);
}
if (lean_is_scalar(x_381)) {
 x_382 = lean_alloc_ctor(0, 3, 0);
} else {
 x_382 = x_381;
}
lean_ctor_set(x_382, 0, x_379);
lean_ctor_set(x_382, 1, x_380);
lean_ctor_set(x_382, 2, x_271);
if (lean_is_scalar(x_378)) {
 x_383 = lean_alloc_ctor(0, 6, 0);
} else {
 x_383 = x_378;
}
lean_ctor_set(x_383, 0, x_373);
lean_ctor_set(x_383, 1, x_374);
lean_ctor_set(x_383, 2, x_382);
lean_ctor_set(x_383, 3, x_375);
lean_ctor_set(x_383, 4, x_376);
lean_ctor_set(x_383, 5, x_377);
if (lean_is_scalar(x_372)) {
 x_384 = lean_alloc_ctor(1, 2, 0);
} else {
 x_384 = x_372;
}
lean_ctor_set(x_384, 0, x_371);
lean_ctor_set(x_384, 1, x_383);
return x_384;
}
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_385 = lean_ctor_get(x_269, 0);
x_386 = lean_ctor_get(x_269, 1);
x_387 = lean_ctor_get(x_269, 2);
lean_inc(x_387);
lean_inc(x_386);
lean_inc(x_385);
lean_dec(x_269);
x_388 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_389 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_389, 0, x_385);
lean_ctor_set(x_389, 1, x_386);
lean_ctor_set(x_389, 2, x_388);
lean_ctor_set(x_264, 2, x_389);
x_390 = lean_ctor_get(x_6, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_6, 1);
lean_inc(x_391);
x_392 = lean_ctor_get(x_6, 2);
lean_inc(x_392);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 x_393 = x_6;
} else {
 lean_dec_ref(x_6);
 x_393 = lean_box(0);
}
x_394 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_394, 0, x_265);
lean_ctor_set(x_394, 1, x_27);
x_395 = lean_array_push(x_392, x_394);
if (lean_is_scalar(x_393)) {
 x_396 = lean_alloc_ctor(0, 3, 0);
} else {
 x_396 = x_393;
}
lean_ctor_set(x_396, 0, x_390);
lean_ctor_set(x_396, 1, x_391);
lean_ctor_set(x_396, 2, x_395);
x_397 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4(x_1, x_2, x_3, x_4, x_267, x_396, x_264);
if (lean_obj_tag(x_397) == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_398 = lean_ctor_get(x_397, 1);
lean_inc(x_398);
x_399 = lean_ctor_get(x_398, 2);
lean_inc(x_399);
x_400 = lean_ctor_get(x_397, 0);
lean_inc(x_400);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 x_401 = x_397;
} else {
 lean_dec_ref(x_397);
 x_401 = lean_box(0);
}
x_402 = lean_ctor_get(x_398, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_398, 1);
lean_inc(x_403);
x_404 = lean_ctor_get(x_398, 3);
lean_inc(x_404);
x_405 = lean_ctor_get(x_398, 4);
lean_inc(x_405);
x_406 = lean_ctor_get(x_398, 5);
lean_inc(x_406);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 lean_ctor_release(x_398, 1);
 lean_ctor_release(x_398, 2);
 lean_ctor_release(x_398, 3);
 lean_ctor_release(x_398, 4);
 lean_ctor_release(x_398, 5);
 x_407 = x_398;
} else {
 lean_dec_ref(x_398);
 x_407 = lean_box(0);
}
x_408 = lean_ctor_get(x_399, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_399, 1);
lean_inc(x_409);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 lean_ctor_release(x_399, 2);
 x_410 = x_399;
} else {
 lean_dec_ref(x_399);
 x_410 = lean_box(0);
}
if (lean_is_scalar(x_410)) {
 x_411 = lean_alloc_ctor(0, 3, 0);
} else {
 x_411 = x_410;
}
lean_ctor_set(x_411, 0, x_408);
lean_ctor_set(x_411, 1, x_409);
lean_ctor_set(x_411, 2, x_387);
if (lean_is_scalar(x_407)) {
 x_412 = lean_alloc_ctor(0, 6, 0);
} else {
 x_412 = x_407;
}
lean_ctor_set(x_412, 0, x_402);
lean_ctor_set(x_412, 1, x_403);
lean_ctor_set(x_412, 2, x_411);
lean_ctor_set(x_412, 3, x_404);
lean_ctor_set(x_412, 4, x_405);
lean_ctor_set(x_412, 5, x_406);
if (lean_is_scalar(x_401)) {
 x_413 = lean_alloc_ctor(0, 2, 0);
} else {
 x_413 = x_401;
}
lean_ctor_set(x_413, 0, x_400);
lean_ctor_set(x_413, 1, x_412);
return x_413;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_414 = lean_ctor_get(x_397, 1);
lean_inc(x_414);
x_415 = lean_ctor_get(x_414, 2);
lean_inc(x_415);
x_416 = lean_ctor_get(x_397, 0);
lean_inc(x_416);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 x_417 = x_397;
} else {
 lean_dec_ref(x_397);
 x_417 = lean_box(0);
}
x_418 = lean_ctor_get(x_414, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_414, 1);
lean_inc(x_419);
x_420 = lean_ctor_get(x_414, 3);
lean_inc(x_420);
x_421 = lean_ctor_get(x_414, 4);
lean_inc(x_421);
x_422 = lean_ctor_get(x_414, 5);
lean_inc(x_422);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 lean_ctor_release(x_414, 2);
 lean_ctor_release(x_414, 3);
 lean_ctor_release(x_414, 4);
 lean_ctor_release(x_414, 5);
 x_423 = x_414;
} else {
 lean_dec_ref(x_414);
 x_423 = lean_box(0);
}
x_424 = lean_ctor_get(x_415, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_415, 1);
lean_inc(x_425);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 lean_ctor_release(x_415, 2);
 x_426 = x_415;
} else {
 lean_dec_ref(x_415);
 x_426 = lean_box(0);
}
if (lean_is_scalar(x_426)) {
 x_427 = lean_alloc_ctor(0, 3, 0);
} else {
 x_427 = x_426;
}
lean_ctor_set(x_427, 0, x_424);
lean_ctor_set(x_427, 1, x_425);
lean_ctor_set(x_427, 2, x_387);
if (lean_is_scalar(x_423)) {
 x_428 = lean_alloc_ctor(0, 6, 0);
} else {
 x_428 = x_423;
}
lean_ctor_set(x_428, 0, x_418);
lean_ctor_set(x_428, 1, x_419);
lean_ctor_set(x_428, 2, x_427);
lean_ctor_set(x_428, 3, x_420);
lean_ctor_set(x_428, 4, x_421);
lean_ctor_set(x_428, 5, x_422);
if (lean_is_scalar(x_417)) {
 x_429 = lean_alloc_ctor(1, 2, 0);
} else {
 x_429 = x_417;
}
lean_ctor_set(x_429, 0, x_416);
lean_ctor_set(x_429, 1, x_428);
return x_429;
}
}
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_430 = lean_ctor_get(x_264, 2);
x_431 = lean_ctor_get(x_264, 0);
x_432 = lean_ctor_get(x_264, 1);
x_433 = lean_ctor_get(x_264, 3);
x_434 = lean_ctor_get(x_264, 4);
x_435 = lean_ctor_get(x_264, 5);
lean_inc(x_435);
lean_inc(x_434);
lean_inc(x_433);
lean_inc(x_430);
lean_inc(x_432);
lean_inc(x_431);
lean_dec(x_264);
x_436 = lean_ctor_get(x_430, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_430, 1);
lean_inc(x_437);
x_438 = lean_ctor_get(x_430, 2);
lean_inc(x_438);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 lean_ctor_release(x_430, 2);
 x_439 = x_430;
} else {
 lean_dec_ref(x_430);
 x_439 = lean_box(0);
}
x_440 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_439)) {
 x_441 = lean_alloc_ctor(0, 3, 0);
} else {
 x_441 = x_439;
}
lean_ctor_set(x_441, 0, x_436);
lean_ctor_set(x_441, 1, x_437);
lean_ctor_set(x_441, 2, x_440);
x_442 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_442, 0, x_431);
lean_ctor_set(x_442, 1, x_432);
lean_ctor_set(x_442, 2, x_441);
lean_ctor_set(x_442, 3, x_433);
lean_ctor_set(x_442, 4, x_434);
lean_ctor_set(x_442, 5, x_435);
x_443 = lean_ctor_get(x_6, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_6, 1);
lean_inc(x_444);
x_445 = lean_ctor_get(x_6, 2);
lean_inc(x_445);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 x_446 = x_6;
} else {
 lean_dec_ref(x_6);
 x_446 = lean_box(0);
}
x_447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_447, 0, x_265);
lean_ctor_set(x_447, 1, x_27);
x_448 = lean_array_push(x_445, x_447);
if (lean_is_scalar(x_446)) {
 x_449 = lean_alloc_ctor(0, 3, 0);
} else {
 x_449 = x_446;
}
lean_ctor_set(x_449, 0, x_443);
lean_ctor_set(x_449, 1, x_444);
lean_ctor_set(x_449, 2, x_448);
x_450 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4(x_1, x_2, x_3, x_4, x_267, x_449, x_442);
if (lean_obj_tag(x_450) == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_451 = lean_ctor_get(x_450, 1);
lean_inc(x_451);
x_452 = lean_ctor_get(x_451, 2);
lean_inc(x_452);
x_453 = lean_ctor_get(x_450, 0);
lean_inc(x_453);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 lean_ctor_release(x_450, 1);
 x_454 = x_450;
} else {
 lean_dec_ref(x_450);
 x_454 = lean_box(0);
}
x_455 = lean_ctor_get(x_451, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_451, 1);
lean_inc(x_456);
x_457 = lean_ctor_get(x_451, 3);
lean_inc(x_457);
x_458 = lean_ctor_get(x_451, 4);
lean_inc(x_458);
x_459 = lean_ctor_get(x_451, 5);
lean_inc(x_459);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 lean_ctor_release(x_451, 1);
 lean_ctor_release(x_451, 2);
 lean_ctor_release(x_451, 3);
 lean_ctor_release(x_451, 4);
 lean_ctor_release(x_451, 5);
 x_460 = x_451;
} else {
 lean_dec_ref(x_451);
 x_460 = lean_box(0);
}
x_461 = lean_ctor_get(x_452, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_452, 1);
lean_inc(x_462);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 lean_ctor_release(x_452, 1);
 lean_ctor_release(x_452, 2);
 x_463 = x_452;
} else {
 lean_dec_ref(x_452);
 x_463 = lean_box(0);
}
if (lean_is_scalar(x_463)) {
 x_464 = lean_alloc_ctor(0, 3, 0);
} else {
 x_464 = x_463;
}
lean_ctor_set(x_464, 0, x_461);
lean_ctor_set(x_464, 1, x_462);
lean_ctor_set(x_464, 2, x_438);
if (lean_is_scalar(x_460)) {
 x_465 = lean_alloc_ctor(0, 6, 0);
} else {
 x_465 = x_460;
}
lean_ctor_set(x_465, 0, x_455);
lean_ctor_set(x_465, 1, x_456);
lean_ctor_set(x_465, 2, x_464);
lean_ctor_set(x_465, 3, x_457);
lean_ctor_set(x_465, 4, x_458);
lean_ctor_set(x_465, 5, x_459);
if (lean_is_scalar(x_454)) {
 x_466 = lean_alloc_ctor(0, 2, 0);
} else {
 x_466 = x_454;
}
lean_ctor_set(x_466, 0, x_453);
lean_ctor_set(x_466, 1, x_465);
return x_466;
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_467 = lean_ctor_get(x_450, 1);
lean_inc(x_467);
x_468 = lean_ctor_get(x_467, 2);
lean_inc(x_468);
x_469 = lean_ctor_get(x_450, 0);
lean_inc(x_469);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 lean_ctor_release(x_450, 1);
 x_470 = x_450;
} else {
 lean_dec_ref(x_450);
 x_470 = lean_box(0);
}
x_471 = lean_ctor_get(x_467, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_467, 1);
lean_inc(x_472);
x_473 = lean_ctor_get(x_467, 3);
lean_inc(x_473);
x_474 = lean_ctor_get(x_467, 4);
lean_inc(x_474);
x_475 = lean_ctor_get(x_467, 5);
lean_inc(x_475);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 lean_ctor_release(x_467, 2);
 lean_ctor_release(x_467, 3);
 lean_ctor_release(x_467, 4);
 lean_ctor_release(x_467, 5);
 x_476 = x_467;
} else {
 lean_dec_ref(x_467);
 x_476 = lean_box(0);
}
x_477 = lean_ctor_get(x_468, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_468, 1);
lean_inc(x_478);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 lean_ctor_release(x_468, 1);
 lean_ctor_release(x_468, 2);
 x_479 = x_468;
} else {
 lean_dec_ref(x_468);
 x_479 = lean_box(0);
}
if (lean_is_scalar(x_479)) {
 x_480 = lean_alloc_ctor(0, 3, 0);
} else {
 x_480 = x_479;
}
lean_ctor_set(x_480, 0, x_477);
lean_ctor_set(x_480, 1, x_478);
lean_ctor_set(x_480, 2, x_438);
if (lean_is_scalar(x_476)) {
 x_481 = lean_alloc_ctor(0, 6, 0);
} else {
 x_481 = x_476;
}
lean_ctor_set(x_481, 0, x_471);
lean_ctor_set(x_481, 1, x_472);
lean_ctor_set(x_481, 2, x_480);
lean_ctor_set(x_481, 3, x_473);
lean_ctor_set(x_481, 4, x_474);
lean_ctor_set(x_481, 5, x_475);
if (lean_is_scalar(x_470)) {
 x_482 = lean_alloc_ctor(1, 2, 0);
} else {
 x_482 = x_470;
}
lean_ctor_set(x_482, 0, x_469);
lean_ctor_set(x_482, 1, x_481);
return x_482;
}
}
}
}
else
{
uint8_t x_483; 
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_483 = !lean_is_exclusive(x_258);
if (x_483 == 0)
{
return x_258;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_484 = lean_ctor_get(x_258, 0);
x_485 = lean_ctor_get(x_258, 1);
lean_inc(x_485);
lean_inc(x_484);
lean_dec(x_258);
x_486 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_486, 0, x_484);
lean_ctor_set(x_486, 1, x_485);
return x_486;
}
}
}
}
}
else
{
uint8_t x_487; 
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_487 = !lean_is_exclusive(x_32);
if (x_487 == 0)
{
return x_32;
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_488 = lean_ctor_get(x_32, 0);
x_489 = lean_ctor_get(x_32, 1);
lean_inc(x_489);
lean_inc(x_488);
lean_dec(x_32);
x_490 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_490, 0, x_488);
lean_ctor_set(x_490, 1, x_489);
return x_490;
}
}
}
else
{
uint8_t x_491; 
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_491 = !lean_is_exclusive(x_28);
if (x_491 == 0)
{
return x_28;
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_492 = lean_ctor_get(x_28, 0);
x_493 = lean_ctor_get(x_28, 1);
lean_inc(x_493);
lean_inc(x_492);
lean_dec(x_28);
x_494 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_494, 0, x_492);
lean_ctor_set(x_494, 1, x_493);
return x_494;
}
}
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_isForall(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_11 = l_Array_empty___closed__1;
lean_inc(x_2);
x_12 = l_Nat_foldMAux___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__1(x_1, x_2, x_2, x_11, x_8, x_9);
lean_dec(x_2);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l___private_Init_Lean_Meta_FunInfo_4__collectDeps(x_1, x_3);
lean_dec(x_1);
x_16 = l___private_Init_Lean_Meta_FunInfo_5__updateHasFwdDeps(x_14, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = l___private_Init_Lean_Meta_FunInfo_4__collectDeps(x_1, x_3);
lean_dec(x_1);
x_21 = l___private_Init_Lean_Meta_FunInfo_5__updateHasFwdDeps(x_18, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; 
x_28 = l___private_Init_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__3(x_4, x_5, x_6, x_1, x_2, x_7, x_8, x_9);
return x_28;
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_inc(x_8);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_whnf), 3, 1);
lean_closure_set(x_13, 0, x_8);
x_14 = lean_box(x_1);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5___lambda__1___boxed), 9, 6);
lean_closure_set(x_15, 0, x_4);
lean_closure_set(x_15, 1, x_7);
lean_closure_set(x_15, 2, x_8);
lean_closure_set(x_15, 3, x_14);
lean_closure_set(x_15, 4, x_2);
lean_closure_set(x_15, 5, x_3);
x_16 = lean_array_get_size(x_9);
x_17 = lean_nat_dec_lt(x_10, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(x_13, x_15, x_11, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_13);
x_19 = lean_array_fget(x_9, x_10);
lean_inc(x_11);
x_20 = l_Lean_Meta_getFVarLocalDecl(x_19, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_LocalDecl_type(x_21);
lean_dec(x_21);
lean_inc(x_11);
lean_inc(x_23);
x_24 = l_Lean_Meta_isClassQuick___main(x_23, x_11, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
switch (lean_obj_tag(x_25)) {
case 0:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_23);
lean_dec(x_19);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_10, x_27);
lean_dec(x_10);
x_10 = x_28;
x_12 = x_26;
goto _start;
}
case 1:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_23);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_10, x_32);
lean_dec(x_10);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_30, 2);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_35, 2);
x_38 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_35, 2, x_38);
x_39 = !lean_is_exclusive(x_11);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_11, 2);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_19);
x_42 = lean_array_push(x_40, x_41);
lean_ctor_set(x_11, 2, x_42);
x_43 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33, x_11, x_30);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 2);
lean_inc(x_45);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_43, 1);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_44, 2);
lean_dec(x_49);
x_50 = !lean_is_exclusive(x_45);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_45, 2);
lean_dec(x_51);
lean_ctor_set(x_45, 2, x_37);
return x_43;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_45, 0);
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_45);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_37);
lean_ctor_set(x_44, 2, x_54);
return x_43;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_55 = lean_ctor_get(x_44, 0);
x_56 = lean_ctor_get(x_44, 1);
x_57 = lean_ctor_get(x_44, 3);
x_58 = lean_ctor_get(x_44, 4);
x_59 = lean_ctor_get(x_44, 5);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_44);
x_60 = lean_ctor_get(x_45, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_45, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 x_62 = x_45;
} else {
 lean_dec_ref(x_45);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(0, 3, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
lean_ctor_set(x_63, 2, x_37);
x_64 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_64, 0, x_55);
lean_ctor_set(x_64, 1, x_56);
lean_ctor_set(x_64, 2, x_63);
lean_ctor_set(x_64, 3, x_57);
lean_ctor_set(x_64, 4, x_58);
lean_ctor_set(x_64, 5, x_59);
lean_ctor_set(x_43, 1, x_64);
return x_43;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_65 = lean_ctor_get(x_43, 0);
lean_inc(x_65);
lean_dec(x_43);
x_66 = lean_ctor_get(x_44, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_44, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_44, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_44, 4);
lean_inc(x_69);
x_70 = lean_ctor_get(x_44, 5);
lean_inc(x_70);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 lean_ctor_release(x_44, 4);
 lean_ctor_release(x_44, 5);
 x_71 = x_44;
} else {
 lean_dec_ref(x_44);
 x_71 = lean_box(0);
}
x_72 = lean_ctor_get(x_45, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_45, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 x_74 = x_45;
} else {
 lean_dec_ref(x_45);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(0, 3, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
lean_ctor_set(x_75, 2, x_37);
if (lean_is_scalar(x_71)) {
 x_76 = lean_alloc_ctor(0, 6, 0);
} else {
 x_76 = x_71;
}
lean_ctor_set(x_76, 0, x_66);
lean_ctor_set(x_76, 1, x_67);
lean_ctor_set(x_76, 2, x_75);
lean_ctor_set(x_76, 3, x_68);
lean_ctor_set(x_76, 4, x_69);
lean_ctor_set(x_76, 5, x_70);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_65);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_43, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_78, 2);
lean_inc(x_79);
x_80 = !lean_is_exclusive(x_43);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_43, 1);
lean_dec(x_81);
x_82 = !lean_is_exclusive(x_78);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_78, 2);
lean_dec(x_83);
x_84 = !lean_is_exclusive(x_79);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_79, 2);
lean_dec(x_85);
lean_ctor_set(x_79, 2, x_37);
return x_43;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_79, 0);
x_87 = lean_ctor_get(x_79, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_79);
x_88 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_88, 2, x_37);
lean_ctor_set(x_78, 2, x_88);
return x_43;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_89 = lean_ctor_get(x_78, 0);
x_90 = lean_ctor_get(x_78, 1);
x_91 = lean_ctor_get(x_78, 3);
x_92 = lean_ctor_get(x_78, 4);
x_93 = lean_ctor_get(x_78, 5);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_78);
x_94 = lean_ctor_get(x_79, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_79, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 lean_ctor_release(x_79, 2);
 x_96 = x_79;
} else {
 lean_dec_ref(x_79);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 3, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
lean_ctor_set(x_97, 2, x_37);
x_98 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_98, 0, x_89);
lean_ctor_set(x_98, 1, x_90);
lean_ctor_set(x_98, 2, x_97);
lean_ctor_set(x_98, 3, x_91);
lean_ctor_set(x_98, 4, x_92);
lean_ctor_set(x_98, 5, x_93);
lean_ctor_set(x_43, 1, x_98);
return x_43;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_99 = lean_ctor_get(x_43, 0);
lean_inc(x_99);
lean_dec(x_43);
x_100 = lean_ctor_get(x_78, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_78, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_78, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_78, 4);
lean_inc(x_103);
x_104 = lean_ctor_get(x_78, 5);
lean_inc(x_104);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 lean_ctor_release(x_78, 2);
 lean_ctor_release(x_78, 3);
 lean_ctor_release(x_78, 4);
 lean_ctor_release(x_78, 5);
 x_105 = x_78;
} else {
 lean_dec_ref(x_78);
 x_105 = lean_box(0);
}
x_106 = lean_ctor_get(x_79, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_79, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 lean_ctor_release(x_79, 2);
 x_108 = x_79;
} else {
 lean_dec_ref(x_79);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(0, 3, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
lean_ctor_set(x_109, 2, x_37);
if (lean_is_scalar(x_105)) {
 x_110 = lean_alloc_ctor(0, 6, 0);
} else {
 x_110 = x_105;
}
lean_ctor_set(x_110, 0, x_100);
lean_ctor_set(x_110, 1, x_101);
lean_ctor_set(x_110, 2, x_109);
lean_ctor_set(x_110, 3, x_102);
lean_ctor_set(x_110, 4, x_103);
lean_ctor_set(x_110, 5, x_104);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_99);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_112 = lean_ctor_get(x_11, 0);
x_113 = lean_ctor_get(x_11, 1);
x_114 = lean_ctor_get(x_11, 2);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_11);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_31);
lean_ctor_set(x_115, 1, x_19);
x_116 = lean_array_push(x_114, x_115);
x_117 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_117, 0, x_112);
lean_ctor_set(x_117, 1, x_113);
lean_ctor_set(x_117, 2, x_116);
x_118 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33, x_117, x_30);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_119, 2);
lean_inc(x_120);
x_121 = lean_ctor_get(x_118, 0);
lean_inc(x_121);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_122 = x_118;
} else {
 lean_dec_ref(x_118);
 x_122 = lean_box(0);
}
x_123 = lean_ctor_get(x_119, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_119, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_119, 3);
lean_inc(x_125);
x_126 = lean_ctor_get(x_119, 4);
lean_inc(x_126);
x_127 = lean_ctor_get(x_119, 5);
lean_inc(x_127);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 lean_ctor_release(x_119, 2);
 lean_ctor_release(x_119, 3);
 lean_ctor_release(x_119, 4);
 lean_ctor_release(x_119, 5);
 x_128 = x_119;
} else {
 lean_dec_ref(x_119);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_120, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_120, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 lean_ctor_release(x_120, 2);
 x_131 = x_120;
} else {
 lean_dec_ref(x_120);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(0, 3, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
lean_ctor_set(x_132, 2, x_37);
if (lean_is_scalar(x_128)) {
 x_133 = lean_alloc_ctor(0, 6, 0);
} else {
 x_133 = x_128;
}
lean_ctor_set(x_133, 0, x_123);
lean_ctor_set(x_133, 1, x_124);
lean_ctor_set(x_133, 2, x_132);
lean_ctor_set(x_133, 3, x_125);
lean_ctor_set(x_133, 4, x_126);
lean_ctor_set(x_133, 5, x_127);
if (lean_is_scalar(x_122)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_122;
}
lean_ctor_set(x_134, 0, x_121);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_135 = lean_ctor_get(x_118, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_135, 2);
lean_inc(x_136);
x_137 = lean_ctor_get(x_118, 0);
lean_inc(x_137);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_138 = x_118;
} else {
 lean_dec_ref(x_118);
 x_138 = lean_box(0);
}
x_139 = lean_ctor_get(x_135, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_135, 1);
lean_inc(x_140);
x_141 = lean_ctor_get(x_135, 3);
lean_inc(x_141);
x_142 = lean_ctor_get(x_135, 4);
lean_inc(x_142);
x_143 = lean_ctor_get(x_135, 5);
lean_inc(x_143);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 lean_ctor_release(x_135, 2);
 lean_ctor_release(x_135, 3);
 lean_ctor_release(x_135, 4);
 lean_ctor_release(x_135, 5);
 x_144 = x_135;
} else {
 lean_dec_ref(x_135);
 x_144 = lean_box(0);
}
x_145 = lean_ctor_get(x_136, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_136, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 lean_ctor_release(x_136, 2);
 x_147 = x_136;
} else {
 lean_dec_ref(x_136);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(0, 3, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
lean_ctor_set(x_148, 2, x_37);
if (lean_is_scalar(x_144)) {
 x_149 = lean_alloc_ctor(0, 6, 0);
} else {
 x_149 = x_144;
}
lean_ctor_set(x_149, 0, x_139);
lean_ctor_set(x_149, 1, x_140);
lean_ctor_set(x_149, 2, x_148);
lean_ctor_set(x_149, 3, x_141);
lean_ctor_set(x_149, 4, x_142);
lean_ctor_set(x_149, 5, x_143);
if (lean_is_scalar(x_138)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_138;
}
lean_ctor_set(x_150, 0, x_137);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_151 = lean_ctor_get(x_35, 0);
x_152 = lean_ctor_get(x_35, 1);
x_153 = lean_ctor_get(x_35, 2);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_35);
x_154 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_155 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_155, 0, x_151);
lean_ctor_set(x_155, 1, x_152);
lean_ctor_set(x_155, 2, x_154);
lean_ctor_set(x_30, 2, x_155);
x_156 = lean_ctor_get(x_11, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_11, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_11, 2);
lean_inc(x_158);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 x_159 = x_11;
} else {
 lean_dec_ref(x_11);
 x_159 = lean_box(0);
}
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_31);
lean_ctor_set(x_160, 1, x_19);
x_161 = lean_array_push(x_158, x_160);
if (lean_is_scalar(x_159)) {
 x_162 = lean_alloc_ctor(0, 3, 0);
} else {
 x_162 = x_159;
}
lean_ctor_set(x_162, 0, x_156);
lean_ctor_set(x_162, 1, x_157);
lean_ctor_set(x_162, 2, x_161);
x_163 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33, x_162, x_30);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_164, 2);
lean_inc(x_165);
x_166 = lean_ctor_get(x_163, 0);
lean_inc(x_166);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_167 = x_163;
} else {
 lean_dec_ref(x_163);
 x_167 = lean_box(0);
}
x_168 = lean_ctor_get(x_164, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_164, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_164, 3);
lean_inc(x_170);
x_171 = lean_ctor_get(x_164, 4);
lean_inc(x_171);
x_172 = lean_ctor_get(x_164, 5);
lean_inc(x_172);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 lean_ctor_release(x_164, 2);
 lean_ctor_release(x_164, 3);
 lean_ctor_release(x_164, 4);
 lean_ctor_release(x_164, 5);
 x_173 = x_164;
} else {
 lean_dec_ref(x_164);
 x_173 = lean_box(0);
}
x_174 = lean_ctor_get(x_165, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_165, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 lean_ctor_release(x_165, 2);
 x_176 = x_165;
} else {
 lean_dec_ref(x_165);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(0, 3, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
lean_ctor_set(x_177, 2, x_153);
if (lean_is_scalar(x_173)) {
 x_178 = lean_alloc_ctor(0, 6, 0);
} else {
 x_178 = x_173;
}
lean_ctor_set(x_178, 0, x_168);
lean_ctor_set(x_178, 1, x_169);
lean_ctor_set(x_178, 2, x_177);
lean_ctor_set(x_178, 3, x_170);
lean_ctor_set(x_178, 4, x_171);
lean_ctor_set(x_178, 5, x_172);
if (lean_is_scalar(x_167)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_167;
}
lean_ctor_set(x_179, 0, x_166);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_180 = lean_ctor_get(x_163, 1);
lean_inc(x_180);
x_181 = lean_ctor_get(x_180, 2);
lean_inc(x_181);
x_182 = lean_ctor_get(x_163, 0);
lean_inc(x_182);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_183 = x_163;
} else {
 lean_dec_ref(x_163);
 x_183 = lean_box(0);
}
x_184 = lean_ctor_get(x_180, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_180, 1);
lean_inc(x_185);
x_186 = lean_ctor_get(x_180, 3);
lean_inc(x_186);
x_187 = lean_ctor_get(x_180, 4);
lean_inc(x_187);
x_188 = lean_ctor_get(x_180, 5);
lean_inc(x_188);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 lean_ctor_release(x_180, 2);
 lean_ctor_release(x_180, 3);
 lean_ctor_release(x_180, 4);
 lean_ctor_release(x_180, 5);
 x_189 = x_180;
} else {
 lean_dec_ref(x_180);
 x_189 = lean_box(0);
}
x_190 = lean_ctor_get(x_181, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_181, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 lean_ctor_release(x_181, 2);
 x_192 = x_181;
} else {
 lean_dec_ref(x_181);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(0, 3, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_191);
lean_ctor_set(x_193, 2, x_153);
if (lean_is_scalar(x_189)) {
 x_194 = lean_alloc_ctor(0, 6, 0);
} else {
 x_194 = x_189;
}
lean_ctor_set(x_194, 0, x_184);
lean_ctor_set(x_194, 1, x_185);
lean_ctor_set(x_194, 2, x_193);
lean_ctor_set(x_194, 3, x_186);
lean_ctor_set(x_194, 4, x_187);
lean_ctor_set(x_194, 5, x_188);
if (lean_is_scalar(x_183)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_183;
}
lean_ctor_set(x_195, 0, x_182);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_196 = lean_ctor_get(x_30, 2);
x_197 = lean_ctor_get(x_30, 0);
x_198 = lean_ctor_get(x_30, 1);
x_199 = lean_ctor_get(x_30, 3);
x_200 = lean_ctor_get(x_30, 4);
x_201 = lean_ctor_get(x_30, 5);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_196);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_30);
x_202 = lean_ctor_get(x_196, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_196, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_196, 2);
lean_inc(x_204);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 lean_ctor_release(x_196, 2);
 x_205 = x_196;
} else {
 lean_dec_ref(x_196);
 x_205 = lean_box(0);
}
x_206 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_205)) {
 x_207 = lean_alloc_ctor(0, 3, 0);
} else {
 x_207 = x_205;
}
lean_ctor_set(x_207, 0, x_202);
lean_ctor_set(x_207, 1, x_203);
lean_ctor_set(x_207, 2, x_206);
x_208 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_208, 0, x_197);
lean_ctor_set(x_208, 1, x_198);
lean_ctor_set(x_208, 2, x_207);
lean_ctor_set(x_208, 3, x_199);
lean_ctor_set(x_208, 4, x_200);
lean_ctor_set(x_208, 5, x_201);
x_209 = lean_ctor_get(x_11, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_11, 1);
lean_inc(x_210);
x_211 = lean_ctor_get(x_11, 2);
lean_inc(x_211);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 x_212 = x_11;
} else {
 lean_dec_ref(x_11);
 x_212 = lean_box(0);
}
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_31);
lean_ctor_set(x_213, 1, x_19);
x_214 = lean_array_push(x_211, x_213);
if (lean_is_scalar(x_212)) {
 x_215 = lean_alloc_ctor(0, 3, 0);
} else {
 x_215 = x_212;
}
lean_ctor_set(x_215, 0, x_209);
lean_ctor_set(x_215, 1, x_210);
lean_ctor_set(x_215, 2, x_214);
x_216 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33, x_215, x_208);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
x_218 = lean_ctor_get(x_217, 2);
lean_inc(x_218);
x_219 = lean_ctor_get(x_216, 0);
lean_inc(x_219);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_220 = x_216;
} else {
 lean_dec_ref(x_216);
 x_220 = lean_box(0);
}
x_221 = lean_ctor_get(x_217, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_217, 1);
lean_inc(x_222);
x_223 = lean_ctor_get(x_217, 3);
lean_inc(x_223);
x_224 = lean_ctor_get(x_217, 4);
lean_inc(x_224);
x_225 = lean_ctor_get(x_217, 5);
lean_inc(x_225);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 lean_ctor_release(x_217, 2);
 lean_ctor_release(x_217, 3);
 lean_ctor_release(x_217, 4);
 lean_ctor_release(x_217, 5);
 x_226 = x_217;
} else {
 lean_dec_ref(x_217);
 x_226 = lean_box(0);
}
x_227 = lean_ctor_get(x_218, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_218, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 lean_ctor_release(x_218, 2);
 x_229 = x_218;
} else {
 lean_dec_ref(x_218);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(0, 3, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_228);
lean_ctor_set(x_230, 2, x_204);
if (lean_is_scalar(x_226)) {
 x_231 = lean_alloc_ctor(0, 6, 0);
} else {
 x_231 = x_226;
}
lean_ctor_set(x_231, 0, x_221);
lean_ctor_set(x_231, 1, x_222);
lean_ctor_set(x_231, 2, x_230);
lean_ctor_set(x_231, 3, x_223);
lean_ctor_set(x_231, 4, x_224);
lean_ctor_set(x_231, 5, x_225);
if (lean_is_scalar(x_220)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_220;
}
lean_ctor_set(x_232, 0, x_219);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_233 = lean_ctor_get(x_216, 1);
lean_inc(x_233);
x_234 = lean_ctor_get(x_233, 2);
lean_inc(x_234);
x_235 = lean_ctor_get(x_216, 0);
lean_inc(x_235);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_236 = x_216;
} else {
 lean_dec_ref(x_216);
 x_236 = lean_box(0);
}
x_237 = lean_ctor_get(x_233, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_233, 1);
lean_inc(x_238);
x_239 = lean_ctor_get(x_233, 3);
lean_inc(x_239);
x_240 = lean_ctor_get(x_233, 4);
lean_inc(x_240);
x_241 = lean_ctor_get(x_233, 5);
lean_inc(x_241);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 lean_ctor_release(x_233, 2);
 lean_ctor_release(x_233, 3);
 lean_ctor_release(x_233, 4);
 lean_ctor_release(x_233, 5);
 x_242 = x_233;
} else {
 lean_dec_ref(x_233);
 x_242 = lean_box(0);
}
x_243 = lean_ctor_get(x_234, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_234, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 x_245 = x_234;
} else {
 lean_dec_ref(x_234);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(0, 3, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set(x_246, 1, x_244);
lean_ctor_set(x_246, 2, x_204);
if (lean_is_scalar(x_242)) {
 x_247 = lean_alloc_ctor(0, 6, 0);
} else {
 x_247 = x_242;
}
lean_ctor_set(x_247, 0, x_237);
lean_ctor_set(x_247, 1, x_238);
lean_ctor_set(x_247, 2, x_246);
lean_ctor_set(x_247, 3, x_239);
lean_ctor_set(x_247, 4, x_240);
lean_ctor_set(x_247, 5, x_241);
if (lean_is_scalar(x_236)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_236;
}
lean_ctor_set(x_248, 0, x_235);
lean_ctor_set(x_248, 1, x_247);
return x_248;
}
}
}
default: 
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_24, 1);
lean_inc(x_249);
lean_dec(x_24);
lean_inc(x_11);
x_250 = l_Lean_Meta_isClassExpensive___main(x_23, x_11, x_249);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_19);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_253 = lean_unsigned_to_nat(1u);
x_254 = lean_nat_add(x_10, x_253);
lean_dec(x_10);
x_10 = x_254;
x_12 = x_252;
goto _start;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; 
x_256 = lean_ctor_get(x_250, 1);
lean_inc(x_256);
lean_dec(x_250);
x_257 = lean_ctor_get(x_251, 0);
lean_inc(x_257);
lean_dec(x_251);
x_258 = lean_unsigned_to_nat(1u);
x_259 = lean_nat_add(x_10, x_258);
lean_dec(x_10);
x_260 = !lean_is_exclusive(x_256);
if (x_260 == 0)
{
lean_object* x_261; uint8_t x_262; 
x_261 = lean_ctor_get(x_256, 2);
x_262 = !lean_is_exclusive(x_261);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_263 = lean_ctor_get(x_261, 2);
x_264 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_261, 2, x_264);
x_265 = !lean_is_exclusive(x_11);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_266 = lean_ctor_get(x_11, 2);
x_267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_267, 0, x_257);
lean_ctor_set(x_267, 1, x_19);
x_268 = lean_array_push(x_266, x_267);
lean_ctor_set(x_11, 2, x_268);
x_269 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_259, x_11, x_256);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; uint8_t x_272; 
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
x_271 = lean_ctor_get(x_270, 2);
lean_inc(x_271);
x_272 = !lean_is_exclusive(x_269);
if (x_272 == 0)
{
lean_object* x_273; uint8_t x_274; 
x_273 = lean_ctor_get(x_269, 1);
lean_dec(x_273);
x_274 = !lean_is_exclusive(x_270);
if (x_274 == 0)
{
lean_object* x_275; uint8_t x_276; 
x_275 = lean_ctor_get(x_270, 2);
lean_dec(x_275);
x_276 = !lean_is_exclusive(x_271);
if (x_276 == 0)
{
lean_object* x_277; 
x_277 = lean_ctor_get(x_271, 2);
lean_dec(x_277);
lean_ctor_set(x_271, 2, x_263);
return x_269;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_271, 0);
x_279 = lean_ctor_get(x_271, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_271);
x_280 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
lean_ctor_set(x_280, 2, x_263);
lean_ctor_set(x_270, 2, x_280);
return x_269;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_281 = lean_ctor_get(x_270, 0);
x_282 = lean_ctor_get(x_270, 1);
x_283 = lean_ctor_get(x_270, 3);
x_284 = lean_ctor_get(x_270, 4);
x_285 = lean_ctor_get(x_270, 5);
lean_inc(x_285);
lean_inc(x_284);
lean_inc(x_283);
lean_inc(x_282);
lean_inc(x_281);
lean_dec(x_270);
x_286 = lean_ctor_get(x_271, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_271, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 lean_ctor_release(x_271, 2);
 x_288 = x_271;
} else {
 lean_dec_ref(x_271);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(0, 3, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_286);
lean_ctor_set(x_289, 1, x_287);
lean_ctor_set(x_289, 2, x_263);
x_290 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_290, 0, x_281);
lean_ctor_set(x_290, 1, x_282);
lean_ctor_set(x_290, 2, x_289);
lean_ctor_set(x_290, 3, x_283);
lean_ctor_set(x_290, 4, x_284);
lean_ctor_set(x_290, 5, x_285);
lean_ctor_set(x_269, 1, x_290);
return x_269;
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_291 = lean_ctor_get(x_269, 0);
lean_inc(x_291);
lean_dec(x_269);
x_292 = lean_ctor_get(x_270, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_270, 1);
lean_inc(x_293);
x_294 = lean_ctor_get(x_270, 3);
lean_inc(x_294);
x_295 = lean_ctor_get(x_270, 4);
lean_inc(x_295);
x_296 = lean_ctor_get(x_270, 5);
lean_inc(x_296);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 lean_ctor_release(x_270, 2);
 lean_ctor_release(x_270, 3);
 lean_ctor_release(x_270, 4);
 lean_ctor_release(x_270, 5);
 x_297 = x_270;
} else {
 lean_dec_ref(x_270);
 x_297 = lean_box(0);
}
x_298 = lean_ctor_get(x_271, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_271, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 lean_ctor_release(x_271, 2);
 x_300 = x_271;
} else {
 lean_dec_ref(x_271);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(0, 3, 0);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_298);
lean_ctor_set(x_301, 1, x_299);
lean_ctor_set(x_301, 2, x_263);
if (lean_is_scalar(x_297)) {
 x_302 = lean_alloc_ctor(0, 6, 0);
} else {
 x_302 = x_297;
}
lean_ctor_set(x_302, 0, x_292);
lean_ctor_set(x_302, 1, x_293);
lean_ctor_set(x_302, 2, x_301);
lean_ctor_set(x_302, 3, x_294);
lean_ctor_set(x_302, 4, x_295);
lean_ctor_set(x_302, 5, x_296);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_291);
lean_ctor_set(x_303, 1, x_302);
return x_303;
}
}
else
{
lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_304 = lean_ctor_get(x_269, 1);
lean_inc(x_304);
x_305 = lean_ctor_get(x_304, 2);
lean_inc(x_305);
x_306 = !lean_is_exclusive(x_269);
if (x_306 == 0)
{
lean_object* x_307; uint8_t x_308; 
x_307 = lean_ctor_get(x_269, 1);
lean_dec(x_307);
x_308 = !lean_is_exclusive(x_304);
if (x_308 == 0)
{
lean_object* x_309; uint8_t x_310; 
x_309 = lean_ctor_get(x_304, 2);
lean_dec(x_309);
x_310 = !lean_is_exclusive(x_305);
if (x_310 == 0)
{
lean_object* x_311; 
x_311 = lean_ctor_get(x_305, 2);
lean_dec(x_311);
lean_ctor_set(x_305, 2, x_263);
return x_269;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = lean_ctor_get(x_305, 0);
x_313 = lean_ctor_get(x_305, 1);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_305);
x_314 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
lean_ctor_set(x_314, 2, x_263);
lean_ctor_set(x_304, 2, x_314);
return x_269;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_315 = lean_ctor_get(x_304, 0);
x_316 = lean_ctor_get(x_304, 1);
x_317 = lean_ctor_get(x_304, 3);
x_318 = lean_ctor_get(x_304, 4);
x_319 = lean_ctor_get(x_304, 5);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_304);
x_320 = lean_ctor_get(x_305, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_305, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 lean_ctor_release(x_305, 2);
 x_322 = x_305;
} else {
 lean_dec_ref(x_305);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(0, 3, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_320);
lean_ctor_set(x_323, 1, x_321);
lean_ctor_set(x_323, 2, x_263);
x_324 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_324, 0, x_315);
lean_ctor_set(x_324, 1, x_316);
lean_ctor_set(x_324, 2, x_323);
lean_ctor_set(x_324, 3, x_317);
lean_ctor_set(x_324, 4, x_318);
lean_ctor_set(x_324, 5, x_319);
lean_ctor_set(x_269, 1, x_324);
return x_269;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_325 = lean_ctor_get(x_269, 0);
lean_inc(x_325);
lean_dec(x_269);
x_326 = lean_ctor_get(x_304, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_304, 1);
lean_inc(x_327);
x_328 = lean_ctor_get(x_304, 3);
lean_inc(x_328);
x_329 = lean_ctor_get(x_304, 4);
lean_inc(x_329);
x_330 = lean_ctor_get(x_304, 5);
lean_inc(x_330);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 lean_ctor_release(x_304, 2);
 lean_ctor_release(x_304, 3);
 lean_ctor_release(x_304, 4);
 lean_ctor_release(x_304, 5);
 x_331 = x_304;
} else {
 lean_dec_ref(x_304);
 x_331 = lean_box(0);
}
x_332 = lean_ctor_get(x_305, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_305, 1);
lean_inc(x_333);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 lean_ctor_release(x_305, 2);
 x_334 = x_305;
} else {
 lean_dec_ref(x_305);
 x_334 = lean_box(0);
}
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(0, 3, 0);
} else {
 x_335 = x_334;
}
lean_ctor_set(x_335, 0, x_332);
lean_ctor_set(x_335, 1, x_333);
lean_ctor_set(x_335, 2, x_263);
if (lean_is_scalar(x_331)) {
 x_336 = lean_alloc_ctor(0, 6, 0);
} else {
 x_336 = x_331;
}
lean_ctor_set(x_336, 0, x_326);
lean_ctor_set(x_336, 1, x_327);
lean_ctor_set(x_336, 2, x_335);
lean_ctor_set(x_336, 3, x_328);
lean_ctor_set(x_336, 4, x_329);
lean_ctor_set(x_336, 5, x_330);
x_337 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_337, 0, x_325);
lean_ctor_set(x_337, 1, x_336);
return x_337;
}
}
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_338 = lean_ctor_get(x_11, 0);
x_339 = lean_ctor_get(x_11, 1);
x_340 = lean_ctor_get(x_11, 2);
lean_inc(x_340);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_11);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_257);
lean_ctor_set(x_341, 1, x_19);
x_342 = lean_array_push(x_340, x_341);
x_343 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_343, 0, x_338);
lean_ctor_set(x_343, 1, x_339);
lean_ctor_set(x_343, 2, x_342);
x_344 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_259, x_343, x_256);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_345 = lean_ctor_get(x_344, 1);
lean_inc(x_345);
x_346 = lean_ctor_get(x_345, 2);
lean_inc(x_346);
x_347 = lean_ctor_get(x_344, 0);
lean_inc(x_347);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_348 = x_344;
} else {
 lean_dec_ref(x_344);
 x_348 = lean_box(0);
}
x_349 = lean_ctor_get(x_345, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_345, 1);
lean_inc(x_350);
x_351 = lean_ctor_get(x_345, 3);
lean_inc(x_351);
x_352 = lean_ctor_get(x_345, 4);
lean_inc(x_352);
x_353 = lean_ctor_get(x_345, 5);
lean_inc(x_353);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 lean_ctor_release(x_345, 2);
 lean_ctor_release(x_345, 3);
 lean_ctor_release(x_345, 4);
 lean_ctor_release(x_345, 5);
 x_354 = x_345;
} else {
 lean_dec_ref(x_345);
 x_354 = lean_box(0);
}
x_355 = lean_ctor_get(x_346, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_346, 1);
lean_inc(x_356);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 lean_ctor_release(x_346, 2);
 x_357 = x_346;
} else {
 lean_dec_ref(x_346);
 x_357 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_358 = lean_alloc_ctor(0, 3, 0);
} else {
 x_358 = x_357;
}
lean_ctor_set(x_358, 0, x_355);
lean_ctor_set(x_358, 1, x_356);
lean_ctor_set(x_358, 2, x_263);
if (lean_is_scalar(x_354)) {
 x_359 = lean_alloc_ctor(0, 6, 0);
} else {
 x_359 = x_354;
}
lean_ctor_set(x_359, 0, x_349);
lean_ctor_set(x_359, 1, x_350);
lean_ctor_set(x_359, 2, x_358);
lean_ctor_set(x_359, 3, x_351);
lean_ctor_set(x_359, 4, x_352);
lean_ctor_set(x_359, 5, x_353);
if (lean_is_scalar(x_348)) {
 x_360 = lean_alloc_ctor(0, 2, 0);
} else {
 x_360 = x_348;
}
lean_ctor_set(x_360, 0, x_347);
lean_ctor_set(x_360, 1, x_359);
return x_360;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_361 = lean_ctor_get(x_344, 1);
lean_inc(x_361);
x_362 = lean_ctor_get(x_361, 2);
lean_inc(x_362);
x_363 = lean_ctor_get(x_344, 0);
lean_inc(x_363);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_364 = x_344;
} else {
 lean_dec_ref(x_344);
 x_364 = lean_box(0);
}
x_365 = lean_ctor_get(x_361, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_361, 1);
lean_inc(x_366);
x_367 = lean_ctor_get(x_361, 3);
lean_inc(x_367);
x_368 = lean_ctor_get(x_361, 4);
lean_inc(x_368);
x_369 = lean_ctor_get(x_361, 5);
lean_inc(x_369);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 lean_ctor_release(x_361, 1);
 lean_ctor_release(x_361, 2);
 lean_ctor_release(x_361, 3);
 lean_ctor_release(x_361, 4);
 lean_ctor_release(x_361, 5);
 x_370 = x_361;
} else {
 lean_dec_ref(x_361);
 x_370 = lean_box(0);
}
x_371 = lean_ctor_get(x_362, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_362, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 lean_ctor_release(x_362, 2);
 x_373 = x_362;
} else {
 lean_dec_ref(x_362);
 x_373 = lean_box(0);
}
if (lean_is_scalar(x_373)) {
 x_374 = lean_alloc_ctor(0, 3, 0);
} else {
 x_374 = x_373;
}
lean_ctor_set(x_374, 0, x_371);
lean_ctor_set(x_374, 1, x_372);
lean_ctor_set(x_374, 2, x_263);
if (lean_is_scalar(x_370)) {
 x_375 = lean_alloc_ctor(0, 6, 0);
} else {
 x_375 = x_370;
}
lean_ctor_set(x_375, 0, x_365);
lean_ctor_set(x_375, 1, x_366);
lean_ctor_set(x_375, 2, x_374);
lean_ctor_set(x_375, 3, x_367);
lean_ctor_set(x_375, 4, x_368);
lean_ctor_set(x_375, 5, x_369);
if (lean_is_scalar(x_364)) {
 x_376 = lean_alloc_ctor(1, 2, 0);
} else {
 x_376 = x_364;
}
lean_ctor_set(x_376, 0, x_363);
lean_ctor_set(x_376, 1, x_375);
return x_376;
}
}
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_377 = lean_ctor_get(x_261, 0);
x_378 = lean_ctor_get(x_261, 1);
x_379 = lean_ctor_get(x_261, 2);
lean_inc(x_379);
lean_inc(x_378);
lean_inc(x_377);
lean_dec(x_261);
x_380 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_381 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_381, 0, x_377);
lean_ctor_set(x_381, 1, x_378);
lean_ctor_set(x_381, 2, x_380);
lean_ctor_set(x_256, 2, x_381);
x_382 = lean_ctor_get(x_11, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_11, 1);
lean_inc(x_383);
x_384 = lean_ctor_get(x_11, 2);
lean_inc(x_384);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 x_385 = x_11;
} else {
 lean_dec_ref(x_11);
 x_385 = lean_box(0);
}
x_386 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_386, 0, x_257);
lean_ctor_set(x_386, 1, x_19);
x_387 = lean_array_push(x_384, x_386);
if (lean_is_scalar(x_385)) {
 x_388 = lean_alloc_ctor(0, 3, 0);
} else {
 x_388 = x_385;
}
lean_ctor_set(x_388, 0, x_382);
lean_ctor_set(x_388, 1, x_383);
lean_ctor_set(x_388, 2, x_387);
x_389 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_259, x_388, x_256);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_390 = lean_ctor_get(x_389, 1);
lean_inc(x_390);
x_391 = lean_ctor_get(x_390, 2);
lean_inc(x_391);
x_392 = lean_ctor_get(x_389, 0);
lean_inc(x_392);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 x_393 = x_389;
} else {
 lean_dec_ref(x_389);
 x_393 = lean_box(0);
}
x_394 = lean_ctor_get(x_390, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_390, 1);
lean_inc(x_395);
x_396 = lean_ctor_get(x_390, 3);
lean_inc(x_396);
x_397 = lean_ctor_get(x_390, 4);
lean_inc(x_397);
x_398 = lean_ctor_get(x_390, 5);
lean_inc(x_398);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 lean_ctor_release(x_390, 1);
 lean_ctor_release(x_390, 2);
 lean_ctor_release(x_390, 3);
 lean_ctor_release(x_390, 4);
 lean_ctor_release(x_390, 5);
 x_399 = x_390;
} else {
 lean_dec_ref(x_390);
 x_399 = lean_box(0);
}
x_400 = lean_ctor_get(x_391, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_391, 1);
lean_inc(x_401);
if (lean_is_exclusive(x_391)) {
 lean_ctor_release(x_391, 0);
 lean_ctor_release(x_391, 1);
 lean_ctor_release(x_391, 2);
 x_402 = x_391;
} else {
 lean_dec_ref(x_391);
 x_402 = lean_box(0);
}
if (lean_is_scalar(x_402)) {
 x_403 = lean_alloc_ctor(0, 3, 0);
} else {
 x_403 = x_402;
}
lean_ctor_set(x_403, 0, x_400);
lean_ctor_set(x_403, 1, x_401);
lean_ctor_set(x_403, 2, x_379);
if (lean_is_scalar(x_399)) {
 x_404 = lean_alloc_ctor(0, 6, 0);
} else {
 x_404 = x_399;
}
lean_ctor_set(x_404, 0, x_394);
lean_ctor_set(x_404, 1, x_395);
lean_ctor_set(x_404, 2, x_403);
lean_ctor_set(x_404, 3, x_396);
lean_ctor_set(x_404, 4, x_397);
lean_ctor_set(x_404, 5, x_398);
if (lean_is_scalar(x_393)) {
 x_405 = lean_alloc_ctor(0, 2, 0);
} else {
 x_405 = x_393;
}
lean_ctor_set(x_405, 0, x_392);
lean_ctor_set(x_405, 1, x_404);
return x_405;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_406 = lean_ctor_get(x_389, 1);
lean_inc(x_406);
x_407 = lean_ctor_get(x_406, 2);
lean_inc(x_407);
x_408 = lean_ctor_get(x_389, 0);
lean_inc(x_408);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 x_409 = x_389;
} else {
 lean_dec_ref(x_389);
 x_409 = lean_box(0);
}
x_410 = lean_ctor_get(x_406, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_406, 1);
lean_inc(x_411);
x_412 = lean_ctor_get(x_406, 3);
lean_inc(x_412);
x_413 = lean_ctor_get(x_406, 4);
lean_inc(x_413);
x_414 = lean_ctor_get(x_406, 5);
lean_inc(x_414);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 lean_ctor_release(x_406, 1);
 lean_ctor_release(x_406, 2);
 lean_ctor_release(x_406, 3);
 lean_ctor_release(x_406, 4);
 lean_ctor_release(x_406, 5);
 x_415 = x_406;
} else {
 lean_dec_ref(x_406);
 x_415 = lean_box(0);
}
x_416 = lean_ctor_get(x_407, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_407, 1);
lean_inc(x_417);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 lean_ctor_release(x_407, 1);
 lean_ctor_release(x_407, 2);
 x_418 = x_407;
} else {
 lean_dec_ref(x_407);
 x_418 = lean_box(0);
}
if (lean_is_scalar(x_418)) {
 x_419 = lean_alloc_ctor(0, 3, 0);
} else {
 x_419 = x_418;
}
lean_ctor_set(x_419, 0, x_416);
lean_ctor_set(x_419, 1, x_417);
lean_ctor_set(x_419, 2, x_379);
if (lean_is_scalar(x_415)) {
 x_420 = lean_alloc_ctor(0, 6, 0);
} else {
 x_420 = x_415;
}
lean_ctor_set(x_420, 0, x_410);
lean_ctor_set(x_420, 1, x_411);
lean_ctor_set(x_420, 2, x_419);
lean_ctor_set(x_420, 3, x_412);
lean_ctor_set(x_420, 4, x_413);
lean_ctor_set(x_420, 5, x_414);
if (lean_is_scalar(x_409)) {
 x_421 = lean_alloc_ctor(1, 2, 0);
} else {
 x_421 = x_409;
}
lean_ctor_set(x_421, 0, x_408);
lean_ctor_set(x_421, 1, x_420);
return x_421;
}
}
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_422 = lean_ctor_get(x_256, 2);
x_423 = lean_ctor_get(x_256, 0);
x_424 = lean_ctor_get(x_256, 1);
x_425 = lean_ctor_get(x_256, 3);
x_426 = lean_ctor_get(x_256, 4);
x_427 = lean_ctor_get(x_256, 5);
lean_inc(x_427);
lean_inc(x_426);
lean_inc(x_425);
lean_inc(x_422);
lean_inc(x_424);
lean_inc(x_423);
lean_dec(x_256);
x_428 = lean_ctor_get(x_422, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_422, 1);
lean_inc(x_429);
x_430 = lean_ctor_get(x_422, 2);
lean_inc(x_430);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 lean_ctor_release(x_422, 1);
 lean_ctor_release(x_422, 2);
 x_431 = x_422;
} else {
 lean_dec_ref(x_422);
 x_431 = lean_box(0);
}
x_432 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_431)) {
 x_433 = lean_alloc_ctor(0, 3, 0);
} else {
 x_433 = x_431;
}
lean_ctor_set(x_433, 0, x_428);
lean_ctor_set(x_433, 1, x_429);
lean_ctor_set(x_433, 2, x_432);
x_434 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_434, 0, x_423);
lean_ctor_set(x_434, 1, x_424);
lean_ctor_set(x_434, 2, x_433);
lean_ctor_set(x_434, 3, x_425);
lean_ctor_set(x_434, 4, x_426);
lean_ctor_set(x_434, 5, x_427);
x_435 = lean_ctor_get(x_11, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_11, 1);
lean_inc(x_436);
x_437 = lean_ctor_get(x_11, 2);
lean_inc(x_437);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 x_438 = x_11;
} else {
 lean_dec_ref(x_11);
 x_438 = lean_box(0);
}
x_439 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_439, 0, x_257);
lean_ctor_set(x_439, 1, x_19);
x_440 = lean_array_push(x_437, x_439);
if (lean_is_scalar(x_438)) {
 x_441 = lean_alloc_ctor(0, 3, 0);
} else {
 x_441 = x_438;
}
lean_ctor_set(x_441, 0, x_435);
lean_ctor_set(x_441, 1, x_436);
lean_ctor_set(x_441, 2, x_440);
x_442 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_259, x_441, x_434);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_443 = lean_ctor_get(x_442, 1);
lean_inc(x_443);
x_444 = lean_ctor_get(x_443, 2);
lean_inc(x_444);
x_445 = lean_ctor_get(x_442, 0);
lean_inc(x_445);
if (lean_is_exclusive(x_442)) {
 lean_ctor_release(x_442, 0);
 lean_ctor_release(x_442, 1);
 x_446 = x_442;
} else {
 lean_dec_ref(x_442);
 x_446 = lean_box(0);
}
x_447 = lean_ctor_get(x_443, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_443, 1);
lean_inc(x_448);
x_449 = lean_ctor_get(x_443, 3);
lean_inc(x_449);
x_450 = lean_ctor_get(x_443, 4);
lean_inc(x_450);
x_451 = lean_ctor_get(x_443, 5);
lean_inc(x_451);
if (lean_is_exclusive(x_443)) {
 lean_ctor_release(x_443, 0);
 lean_ctor_release(x_443, 1);
 lean_ctor_release(x_443, 2);
 lean_ctor_release(x_443, 3);
 lean_ctor_release(x_443, 4);
 lean_ctor_release(x_443, 5);
 x_452 = x_443;
} else {
 lean_dec_ref(x_443);
 x_452 = lean_box(0);
}
x_453 = lean_ctor_get(x_444, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_444, 1);
lean_inc(x_454);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 lean_ctor_release(x_444, 2);
 x_455 = x_444;
} else {
 lean_dec_ref(x_444);
 x_455 = lean_box(0);
}
if (lean_is_scalar(x_455)) {
 x_456 = lean_alloc_ctor(0, 3, 0);
} else {
 x_456 = x_455;
}
lean_ctor_set(x_456, 0, x_453);
lean_ctor_set(x_456, 1, x_454);
lean_ctor_set(x_456, 2, x_430);
if (lean_is_scalar(x_452)) {
 x_457 = lean_alloc_ctor(0, 6, 0);
} else {
 x_457 = x_452;
}
lean_ctor_set(x_457, 0, x_447);
lean_ctor_set(x_457, 1, x_448);
lean_ctor_set(x_457, 2, x_456);
lean_ctor_set(x_457, 3, x_449);
lean_ctor_set(x_457, 4, x_450);
lean_ctor_set(x_457, 5, x_451);
if (lean_is_scalar(x_446)) {
 x_458 = lean_alloc_ctor(0, 2, 0);
} else {
 x_458 = x_446;
}
lean_ctor_set(x_458, 0, x_445);
lean_ctor_set(x_458, 1, x_457);
return x_458;
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_459 = lean_ctor_get(x_442, 1);
lean_inc(x_459);
x_460 = lean_ctor_get(x_459, 2);
lean_inc(x_460);
x_461 = lean_ctor_get(x_442, 0);
lean_inc(x_461);
if (lean_is_exclusive(x_442)) {
 lean_ctor_release(x_442, 0);
 lean_ctor_release(x_442, 1);
 x_462 = x_442;
} else {
 lean_dec_ref(x_442);
 x_462 = lean_box(0);
}
x_463 = lean_ctor_get(x_459, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_459, 1);
lean_inc(x_464);
x_465 = lean_ctor_get(x_459, 3);
lean_inc(x_465);
x_466 = lean_ctor_get(x_459, 4);
lean_inc(x_466);
x_467 = lean_ctor_get(x_459, 5);
lean_inc(x_467);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 lean_ctor_release(x_459, 4);
 lean_ctor_release(x_459, 5);
 x_468 = x_459;
} else {
 lean_dec_ref(x_459);
 x_468 = lean_box(0);
}
x_469 = lean_ctor_get(x_460, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_460, 1);
lean_inc(x_470);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 x_471 = x_460;
} else {
 lean_dec_ref(x_460);
 x_471 = lean_box(0);
}
if (lean_is_scalar(x_471)) {
 x_472 = lean_alloc_ctor(0, 3, 0);
} else {
 x_472 = x_471;
}
lean_ctor_set(x_472, 0, x_469);
lean_ctor_set(x_472, 1, x_470);
lean_ctor_set(x_472, 2, x_430);
if (lean_is_scalar(x_468)) {
 x_473 = lean_alloc_ctor(0, 6, 0);
} else {
 x_473 = x_468;
}
lean_ctor_set(x_473, 0, x_463);
lean_ctor_set(x_473, 1, x_464);
lean_ctor_set(x_473, 2, x_472);
lean_ctor_set(x_473, 3, x_465);
lean_ctor_set(x_473, 4, x_466);
lean_ctor_set(x_473, 5, x_467);
if (lean_is_scalar(x_462)) {
 x_474 = lean_alloc_ctor(1, 2, 0);
} else {
 x_474 = x_462;
}
lean_ctor_set(x_474, 0, x_461);
lean_ctor_set(x_474, 1, x_473);
return x_474;
}
}
}
}
else
{
uint8_t x_475; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_475 = !lean_is_exclusive(x_250);
if (x_475 == 0)
{
return x_250;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_476 = lean_ctor_get(x_250, 0);
x_477 = lean_ctor_get(x_250, 1);
lean_inc(x_477);
lean_inc(x_476);
lean_dec(x_250);
x_478 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_478, 0, x_476);
lean_ctor_set(x_478, 1, x_477);
return x_478;
}
}
}
}
}
else
{
uint8_t x_479; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_479 = !lean_is_exclusive(x_24);
if (x_479 == 0)
{
return x_24;
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_480 = lean_ctor_get(x_24, 0);
x_481 = lean_ctor_get(x_24, 1);
lean_inc(x_481);
lean_inc(x_480);
lean_dec(x_24);
x_482 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_482, 0, x_480);
lean_ctor_set(x_482, 1, x_481);
return x_482;
}
}
}
else
{
uint8_t x_483; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_483 = !lean_is_exclusive(x_20);
if (x_483 == 0)
{
return x_20;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_484 = lean_ctor_get(x_20, 0);
x_485 = lean_ctor_get(x_20, 1);
lean_inc(x_485);
lean_inc(x_484);
lean_dec(x_20);
x_486 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_486, 0, x_484);
lean_ctor_set(x_486, 1, x_485);
return x_486;
}
}
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_4);
x_9 = lean_nat_dec_lt(x_5, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
x_10 = l_Array_empty___closed__1;
lean_inc(x_2);
x_11 = l_Nat_foldMAux___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__1(x_1, x_2, x_2, x_10, x_6, x_7);
lean_dec(x_2);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l___private_Init_Lean_Meta_FunInfo_4__collectDeps(x_1, x_3);
x_15 = l___private_Init_Lean_Meta_FunInfo_5__updateHasFwdDeps(x_13, x_14);
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
x_19 = l___private_Init_Lean_Meta_FunInfo_4__collectDeps(x_1, x_3);
x_20 = l___private_Init_Lean_Meta_FunInfo_5__updateHasFwdDeps(x_17, x_19);
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
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_array_fget(x_4, x_5);
lean_inc(x_6);
x_28 = l_Lean_Meta_getFVarLocalDecl(x_27, x_6, x_7);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_LocalDecl_type(x_29);
lean_dec(x_29);
lean_inc(x_6);
lean_inc(x_31);
x_32 = l_Lean_Meta_isClassQuick___main(x_31, x_6, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
switch (lean_obj_tag(x_33)) {
case 0:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_27);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_5, x_35);
lean_dec(x_5);
x_5 = x_36;
x_7 = x_34;
goto _start;
}
case 1:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_31);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_dec(x_32);
x_39 = lean_ctor_get(x_33, 0);
lean_inc(x_39);
lean_dec(x_33);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_5, x_40);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_38, 2);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_43, 2);
x_46 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_43, 2, x_46);
x_47 = !lean_is_exclusive(x_6);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_6, 2);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_27);
x_50 = lean_array_push(x_48, x_49);
lean_ctor_set(x_6, 2, x_50);
x_51 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6(x_1, x_2, x_3, x_4, x_41, x_6, x_38);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_52, 2);
lean_inc(x_53);
x_54 = !lean_is_exclusive(x_51);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_51, 1);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_52, 2);
lean_dec(x_57);
x_58 = !lean_is_exclusive(x_53);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_53, 2);
lean_dec(x_59);
lean_ctor_set(x_53, 2, x_45);
return x_51;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_53, 0);
x_61 = lean_ctor_get(x_53, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_53);
x_62 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_62, 2, x_45);
lean_ctor_set(x_52, 2, x_62);
return x_51;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_63 = lean_ctor_get(x_52, 0);
x_64 = lean_ctor_get(x_52, 1);
x_65 = lean_ctor_get(x_52, 3);
x_66 = lean_ctor_get(x_52, 4);
x_67 = lean_ctor_get(x_52, 5);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_52);
x_68 = lean_ctor_get(x_53, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_53, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 lean_ctor_release(x_53, 2);
 x_70 = x_53;
} else {
 lean_dec_ref(x_53);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 3, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
lean_ctor_set(x_71, 2, x_45);
x_72 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_72, 0, x_63);
lean_ctor_set(x_72, 1, x_64);
lean_ctor_set(x_72, 2, x_71);
lean_ctor_set(x_72, 3, x_65);
lean_ctor_set(x_72, 4, x_66);
lean_ctor_set(x_72, 5, x_67);
lean_ctor_set(x_51, 1, x_72);
return x_51;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_73 = lean_ctor_get(x_51, 0);
lean_inc(x_73);
lean_dec(x_51);
x_74 = lean_ctor_get(x_52, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_52, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_52, 3);
lean_inc(x_76);
x_77 = lean_ctor_get(x_52, 4);
lean_inc(x_77);
x_78 = lean_ctor_get(x_52, 5);
lean_inc(x_78);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 lean_ctor_release(x_52, 4);
 lean_ctor_release(x_52, 5);
 x_79 = x_52;
} else {
 lean_dec_ref(x_52);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_53, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_53, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 lean_ctor_release(x_53, 2);
 x_82 = x_53;
} else {
 lean_dec_ref(x_53);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 3, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
lean_ctor_set(x_83, 2, x_45);
if (lean_is_scalar(x_79)) {
 x_84 = lean_alloc_ctor(0, 6, 0);
} else {
 x_84 = x_79;
}
lean_ctor_set(x_84, 0, x_74);
lean_ctor_set(x_84, 1, x_75);
lean_ctor_set(x_84, 2, x_83);
lean_ctor_set(x_84, 3, x_76);
lean_ctor_set(x_84, 4, x_77);
lean_ctor_set(x_84, 5, x_78);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_73);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_ctor_get(x_51, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_86, 2);
lean_inc(x_87);
x_88 = !lean_is_exclusive(x_51);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_51, 1);
lean_dec(x_89);
x_90 = !lean_is_exclusive(x_86);
if (x_90 == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_86, 2);
lean_dec(x_91);
x_92 = !lean_is_exclusive(x_87);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_87, 2);
lean_dec(x_93);
lean_ctor_set(x_87, 2, x_45);
return x_51;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_87, 0);
x_95 = lean_ctor_get(x_87, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_87);
x_96 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_96, 2, x_45);
lean_ctor_set(x_86, 2, x_96);
return x_51;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_97 = lean_ctor_get(x_86, 0);
x_98 = lean_ctor_get(x_86, 1);
x_99 = lean_ctor_get(x_86, 3);
x_100 = lean_ctor_get(x_86, 4);
x_101 = lean_ctor_get(x_86, 5);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_86);
x_102 = lean_ctor_get(x_87, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_87, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 lean_ctor_release(x_87, 2);
 x_104 = x_87;
} else {
 lean_dec_ref(x_87);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(0, 3, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
lean_ctor_set(x_105, 2, x_45);
x_106 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_106, 0, x_97);
lean_ctor_set(x_106, 1, x_98);
lean_ctor_set(x_106, 2, x_105);
lean_ctor_set(x_106, 3, x_99);
lean_ctor_set(x_106, 4, x_100);
lean_ctor_set(x_106, 5, x_101);
lean_ctor_set(x_51, 1, x_106);
return x_51;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_107 = lean_ctor_get(x_51, 0);
lean_inc(x_107);
lean_dec(x_51);
x_108 = lean_ctor_get(x_86, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_86, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_86, 3);
lean_inc(x_110);
x_111 = lean_ctor_get(x_86, 4);
lean_inc(x_111);
x_112 = lean_ctor_get(x_86, 5);
lean_inc(x_112);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 lean_ctor_release(x_86, 2);
 lean_ctor_release(x_86, 3);
 lean_ctor_release(x_86, 4);
 lean_ctor_release(x_86, 5);
 x_113 = x_86;
} else {
 lean_dec_ref(x_86);
 x_113 = lean_box(0);
}
x_114 = lean_ctor_get(x_87, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_87, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 lean_ctor_release(x_87, 2);
 x_116 = x_87;
} else {
 lean_dec_ref(x_87);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(0, 3, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
lean_ctor_set(x_117, 2, x_45);
if (lean_is_scalar(x_113)) {
 x_118 = lean_alloc_ctor(0, 6, 0);
} else {
 x_118 = x_113;
}
lean_ctor_set(x_118, 0, x_108);
lean_ctor_set(x_118, 1, x_109);
lean_ctor_set(x_118, 2, x_117);
lean_ctor_set(x_118, 3, x_110);
lean_ctor_set(x_118, 4, x_111);
lean_ctor_set(x_118, 5, x_112);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_107);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_120 = lean_ctor_get(x_6, 0);
x_121 = lean_ctor_get(x_6, 1);
x_122 = lean_ctor_get(x_6, 2);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_6);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_39);
lean_ctor_set(x_123, 1, x_27);
x_124 = lean_array_push(x_122, x_123);
x_125 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_125, 0, x_120);
lean_ctor_set(x_125, 1, x_121);
lean_ctor_set(x_125, 2, x_124);
x_126 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6(x_1, x_2, x_3, x_4, x_41, x_125, x_38);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_127, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_126, 0);
lean_inc(x_129);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_130 = x_126;
} else {
 lean_dec_ref(x_126);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_127, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_127, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_127, 3);
lean_inc(x_133);
x_134 = lean_ctor_get(x_127, 4);
lean_inc(x_134);
x_135 = lean_ctor_get(x_127, 5);
lean_inc(x_135);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 lean_ctor_release(x_127, 3);
 lean_ctor_release(x_127, 4);
 lean_ctor_release(x_127, 5);
 x_136 = x_127;
} else {
 lean_dec_ref(x_127);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get(x_128, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_128, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 lean_ctor_release(x_128, 2);
 x_139 = x_128;
} else {
 lean_dec_ref(x_128);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(0, 3, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
lean_ctor_set(x_140, 2, x_45);
if (lean_is_scalar(x_136)) {
 x_141 = lean_alloc_ctor(0, 6, 0);
} else {
 x_141 = x_136;
}
lean_ctor_set(x_141, 0, x_131);
lean_ctor_set(x_141, 1, x_132);
lean_ctor_set(x_141, 2, x_140);
lean_ctor_set(x_141, 3, x_133);
lean_ctor_set(x_141, 4, x_134);
lean_ctor_set(x_141, 5, x_135);
if (lean_is_scalar(x_130)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_130;
}
lean_ctor_set(x_142, 0, x_129);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_143 = lean_ctor_get(x_126, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_143, 2);
lean_inc(x_144);
x_145 = lean_ctor_get(x_126, 0);
lean_inc(x_145);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_146 = x_126;
} else {
 lean_dec_ref(x_126);
 x_146 = lean_box(0);
}
x_147 = lean_ctor_get(x_143, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_143, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_143, 3);
lean_inc(x_149);
x_150 = lean_ctor_get(x_143, 4);
lean_inc(x_150);
x_151 = lean_ctor_get(x_143, 5);
lean_inc(x_151);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 lean_ctor_release(x_143, 2);
 lean_ctor_release(x_143, 3);
 lean_ctor_release(x_143, 4);
 lean_ctor_release(x_143, 5);
 x_152 = x_143;
} else {
 lean_dec_ref(x_143);
 x_152 = lean_box(0);
}
x_153 = lean_ctor_get(x_144, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_144, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 lean_ctor_release(x_144, 2);
 x_155 = x_144;
} else {
 lean_dec_ref(x_144);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(0, 3, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
lean_ctor_set(x_156, 2, x_45);
if (lean_is_scalar(x_152)) {
 x_157 = lean_alloc_ctor(0, 6, 0);
} else {
 x_157 = x_152;
}
lean_ctor_set(x_157, 0, x_147);
lean_ctor_set(x_157, 1, x_148);
lean_ctor_set(x_157, 2, x_156);
lean_ctor_set(x_157, 3, x_149);
lean_ctor_set(x_157, 4, x_150);
lean_ctor_set(x_157, 5, x_151);
if (lean_is_scalar(x_146)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_146;
}
lean_ctor_set(x_158, 0, x_145);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_159 = lean_ctor_get(x_43, 0);
x_160 = lean_ctor_get(x_43, 1);
x_161 = lean_ctor_get(x_43, 2);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_43);
x_162 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_163 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_163, 0, x_159);
lean_ctor_set(x_163, 1, x_160);
lean_ctor_set(x_163, 2, x_162);
lean_ctor_set(x_38, 2, x_163);
x_164 = lean_ctor_get(x_6, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_6, 1);
lean_inc(x_165);
x_166 = lean_ctor_get(x_6, 2);
lean_inc(x_166);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 x_167 = x_6;
} else {
 lean_dec_ref(x_6);
 x_167 = lean_box(0);
}
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_39);
lean_ctor_set(x_168, 1, x_27);
x_169 = lean_array_push(x_166, x_168);
if (lean_is_scalar(x_167)) {
 x_170 = lean_alloc_ctor(0, 3, 0);
} else {
 x_170 = x_167;
}
lean_ctor_set(x_170, 0, x_164);
lean_ctor_set(x_170, 1, x_165);
lean_ctor_set(x_170, 2, x_169);
x_171 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6(x_1, x_2, x_3, x_4, x_41, x_170, x_38);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_172, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_171, 0);
lean_inc(x_174);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_175 = x_171;
} else {
 lean_dec_ref(x_171);
 x_175 = lean_box(0);
}
x_176 = lean_ctor_get(x_172, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_172, 1);
lean_inc(x_177);
x_178 = lean_ctor_get(x_172, 3);
lean_inc(x_178);
x_179 = lean_ctor_get(x_172, 4);
lean_inc(x_179);
x_180 = lean_ctor_get(x_172, 5);
lean_inc(x_180);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 lean_ctor_release(x_172, 2);
 lean_ctor_release(x_172, 3);
 lean_ctor_release(x_172, 4);
 lean_ctor_release(x_172, 5);
 x_181 = x_172;
} else {
 lean_dec_ref(x_172);
 x_181 = lean_box(0);
}
x_182 = lean_ctor_get(x_173, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_173, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 lean_ctor_release(x_173, 2);
 x_184 = x_173;
} else {
 lean_dec_ref(x_173);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(0, 3, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
lean_ctor_set(x_185, 2, x_161);
if (lean_is_scalar(x_181)) {
 x_186 = lean_alloc_ctor(0, 6, 0);
} else {
 x_186 = x_181;
}
lean_ctor_set(x_186, 0, x_176);
lean_ctor_set(x_186, 1, x_177);
lean_ctor_set(x_186, 2, x_185);
lean_ctor_set(x_186, 3, x_178);
lean_ctor_set(x_186, 4, x_179);
lean_ctor_set(x_186, 5, x_180);
if (lean_is_scalar(x_175)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_175;
}
lean_ctor_set(x_187, 0, x_174);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_188 = lean_ctor_get(x_171, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_188, 2);
lean_inc(x_189);
x_190 = lean_ctor_get(x_171, 0);
lean_inc(x_190);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_191 = x_171;
} else {
 lean_dec_ref(x_171);
 x_191 = lean_box(0);
}
x_192 = lean_ctor_get(x_188, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_188, 1);
lean_inc(x_193);
x_194 = lean_ctor_get(x_188, 3);
lean_inc(x_194);
x_195 = lean_ctor_get(x_188, 4);
lean_inc(x_195);
x_196 = lean_ctor_get(x_188, 5);
lean_inc(x_196);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 lean_ctor_release(x_188, 4);
 lean_ctor_release(x_188, 5);
 x_197 = x_188;
} else {
 lean_dec_ref(x_188);
 x_197 = lean_box(0);
}
x_198 = lean_ctor_get(x_189, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_189, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 lean_ctor_release(x_189, 2);
 x_200 = x_189;
} else {
 lean_dec_ref(x_189);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(0, 3, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
lean_ctor_set(x_201, 2, x_161);
if (lean_is_scalar(x_197)) {
 x_202 = lean_alloc_ctor(0, 6, 0);
} else {
 x_202 = x_197;
}
lean_ctor_set(x_202, 0, x_192);
lean_ctor_set(x_202, 1, x_193);
lean_ctor_set(x_202, 2, x_201);
lean_ctor_set(x_202, 3, x_194);
lean_ctor_set(x_202, 4, x_195);
lean_ctor_set(x_202, 5, x_196);
if (lean_is_scalar(x_191)) {
 x_203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_203 = x_191;
}
lean_ctor_set(x_203, 0, x_190);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_204 = lean_ctor_get(x_38, 2);
x_205 = lean_ctor_get(x_38, 0);
x_206 = lean_ctor_get(x_38, 1);
x_207 = lean_ctor_get(x_38, 3);
x_208 = lean_ctor_get(x_38, 4);
x_209 = lean_ctor_get(x_38, 5);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
lean_inc(x_204);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_38);
x_210 = lean_ctor_get(x_204, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_204, 1);
lean_inc(x_211);
x_212 = lean_ctor_get(x_204, 2);
lean_inc(x_212);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 lean_ctor_release(x_204, 2);
 x_213 = x_204;
} else {
 lean_dec_ref(x_204);
 x_213 = lean_box(0);
}
x_214 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_213)) {
 x_215 = lean_alloc_ctor(0, 3, 0);
} else {
 x_215 = x_213;
}
lean_ctor_set(x_215, 0, x_210);
lean_ctor_set(x_215, 1, x_211);
lean_ctor_set(x_215, 2, x_214);
x_216 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_216, 0, x_205);
lean_ctor_set(x_216, 1, x_206);
lean_ctor_set(x_216, 2, x_215);
lean_ctor_set(x_216, 3, x_207);
lean_ctor_set(x_216, 4, x_208);
lean_ctor_set(x_216, 5, x_209);
x_217 = lean_ctor_get(x_6, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_6, 1);
lean_inc(x_218);
x_219 = lean_ctor_get(x_6, 2);
lean_inc(x_219);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 x_220 = x_6;
} else {
 lean_dec_ref(x_6);
 x_220 = lean_box(0);
}
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_39);
lean_ctor_set(x_221, 1, x_27);
x_222 = lean_array_push(x_219, x_221);
if (lean_is_scalar(x_220)) {
 x_223 = lean_alloc_ctor(0, 3, 0);
} else {
 x_223 = x_220;
}
lean_ctor_set(x_223, 0, x_217);
lean_ctor_set(x_223, 1, x_218);
lean_ctor_set(x_223, 2, x_222);
x_224 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6(x_1, x_2, x_3, x_4, x_41, x_223, x_216);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
x_226 = lean_ctor_get(x_225, 2);
lean_inc(x_226);
x_227 = lean_ctor_get(x_224, 0);
lean_inc(x_227);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_228 = x_224;
} else {
 lean_dec_ref(x_224);
 x_228 = lean_box(0);
}
x_229 = lean_ctor_get(x_225, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_225, 1);
lean_inc(x_230);
x_231 = lean_ctor_get(x_225, 3);
lean_inc(x_231);
x_232 = lean_ctor_get(x_225, 4);
lean_inc(x_232);
x_233 = lean_ctor_get(x_225, 5);
lean_inc(x_233);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 lean_ctor_release(x_225, 2);
 lean_ctor_release(x_225, 3);
 lean_ctor_release(x_225, 4);
 lean_ctor_release(x_225, 5);
 x_234 = x_225;
} else {
 lean_dec_ref(x_225);
 x_234 = lean_box(0);
}
x_235 = lean_ctor_get(x_226, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_226, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 lean_ctor_release(x_226, 2);
 x_237 = x_226;
} else {
 lean_dec_ref(x_226);
 x_237 = lean_box(0);
}
if (lean_is_scalar(x_237)) {
 x_238 = lean_alloc_ctor(0, 3, 0);
} else {
 x_238 = x_237;
}
lean_ctor_set(x_238, 0, x_235);
lean_ctor_set(x_238, 1, x_236);
lean_ctor_set(x_238, 2, x_212);
if (lean_is_scalar(x_234)) {
 x_239 = lean_alloc_ctor(0, 6, 0);
} else {
 x_239 = x_234;
}
lean_ctor_set(x_239, 0, x_229);
lean_ctor_set(x_239, 1, x_230);
lean_ctor_set(x_239, 2, x_238);
lean_ctor_set(x_239, 3, x_231);
lean_ctor_set(x_239, 4, x_232);
lean_ctor_set(x_239, 5, x_233);
if (lean_is_scalar(x_228)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_228;
}
lean_ctor_set(x_240, 0, x_227);
lean_ctor_set(x_240, 1, x_239);
return x_240;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_241 = lean_ctor_get(x_224, 1);
lean_inc(x_241);
x_242 = lean_ctor_get(x_241, 2);
lean_inc(x_242);
x_243 = lean_ctor_get(x_224, 0);
lean_inc(x_243);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_244 = x_224;
} else {
 lean_dec_ref(x_224);
 x_244 = lean_box(0);
}
x_245 = lean_ctor_get(x_241, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_241, 1);
lean_inc(x_246);
x_247 = lean_ctor_get(x_241, 3);
lean_inc(x_247);
x_248 = lean_ctor_get(x_241, 4);
lean_inc(x_248);
x_249 = lean_ctor_get(x_241, 5);
lean_inc(x_249);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 lean_ctor_release(x_241, 2);
 lean_ctor_release(x_241, 3);
 lean_ctor_release(x_241, 4);
 lean_ctor_release(x_241, 5);
 x_250 = x_241;
} else {
 lean_dec_ref(x_241);
 x_250 = lean_box(0);
}
x_251 = lean_ctor_get(x_242, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_242, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 lean_ctor_release(x_242, 2);
 x_253 = x_242;
} else {
 lean_dec_ref(x_242);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(0, 3, 0);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_251);
lean_ctor_set(x_254, 1, x_252);
lean_ctor_set(x_254, 2, x_212);
if (lean_is_scalar(x_250)) {
 x_255 = lean_alloc_ctor(0, 6, 0);
} else {
 x_255 = x_250;
}
lean_ctor_set(x_255, 0, x_245);
lean_ctor_set(x_255, 1, x_246);
lean_ctor_set(x_255, 2, x_254);
lean_ctor_set(x_255, 3, x_247);
lean_ctor_set(x_255, 4, x_248);
lean_ctor_set(x_255, 5, x_249);
if (lean_is_scalar(x_244)) {
 x_256 = lean_alloc_ctor(1, 2, 0);
} else {
 x_256 = x_244;
}
lean_ctor_set(x_256, 0, x_243);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
default: 
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_32, 1);
lean_inc(x_257);
lean_dec(x_32);
lean_inc(x_6);
x_258 = l_Lean_Meta_isClassExpensive___main(x_31, x_6, x_257);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_27);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec(x_258);
x_261 = lean_unsigned_to_nat(1u);
x_262 = lean_nat_add(x_5, x_261);
lean_dec(x_5);
x_5 = x_262;
x_7 = x_260;
goto _start;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; 
x_264 = lean_ctor_get(x_258, 1);
lean_inc(x_264);
lean_dec(x_258);
x_265 = lean_ctor_get(x_259, 0);
lean_inc(x_265);
lean_dec(x_259);
x_266 = lean_unsigned_to_nat(1u);
x_267 = lean_nat_add(x_5, x_266);
lean_dec(x_5);
x_268 = !lean_is_exclusive(x_264);
if (x_268 == 0)
{
lean_object* x_269; uint8_t x_270; 
x_269 = lean_ctor_get(x_264, 2);
x_270 = !lean_is_exclusive(x_269);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; uint8_t x_273; 
x_271 = lean_ctor_get(x_269, 2);
x_272 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_269, 2, x_272);
x_273 = !lean_is_exclusive(x_6);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_274 = lean_ctor_get(x_6, 2);
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_265);
lean_ctor_set(x_275, 1, x_27);
x_276 = lean_array_push(x_274, x_275);
lean_ctor_set(x_6, 2, x_276);
x_277 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6(x_1, x_2, x_3, x_4, x_267, x_6, x_264);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; uint8_t x_280; 
x_278 = lean_ctor_get(x_277, 1);
lean_inc(x_278);
x_279 = lean_ctor_get(x_278, 2);
lean_inc(x_279);
x_280 = !lean_is_exclusive(x_277);
if (x_280 == 0)
{
lean_object* x_281; uint8_t x_282; 
x_281 = lean_ctor_get(x_277, 1);
lean_dec(x_281);
x_282 = !lean_is_exclusive(x_278);
if (x_282 == 0)
{
lean_object* x_283; uint8_t x_284; 
x_283 = lean_ctor_get(x_278, 2);
lean_dec(x_283);
x_284 = !lean_is_exclusive(x_279);
if (x_284 == 0)
{
lean_object* x_285; 
x_285 = lean_ctor_get(x_279, 2);
lean_dec(x_285);
lean_ctor_set(x_279, 2, x_271);
return x_277;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_279, 0);
x_287 = lean_ctor_get(x_279, 1);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_279);
x_288 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
lean_ctor_set(x_288, 2, x_271);
lean_ctor_set(x_278, 2, x_288);
return x_277;
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_289 = lean_ctor_get(x_278, 0);
x_290 = lean_ctor_get(x_278, 1);
x_291 = lean_ctor_get(x_278, 3);
x_292 = lean_ctor_get(x_278, 4);
x_293 = lean_ctor_get(x_278, 5);
lean_inc(x_293);
lean_inc(x_292);
lean_inc(x_291);
lean_inc(x_290);
lean_inc(x_289);
lean_dec(x_278);
x_294 = lean_ctor_get(x_279, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_279, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 lean_ctor_release(x_279, 2);
 x_296 = x_279;
} else {
 lean_dec_ref(x_279);
 x_296 = lean_box(0);
}
if (lean_is_scalar(x_296)) {
 x_297 = lean_alloc_ctor(0, 3, 0);
} else {
 x_297 = x_296;
}
lean_ctor_set(x_297, 0, x_294);
lean_ctor_set(x_297, 1, x_295);
lean_ctor_set(x_297, 2, x_271);
x_298 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_298, 0, x_289);
lean_ctor_set(x_298, 1, x_290);
lean_ctor_set(x_298, 2, x_297);
lean_ctor_set(x_298, 3, x_291);
lean_ctor_set(x_298, 4, x_292);
lean_ctor_set(x_298, 5, x_293);
lean_ctor_set(x_277, 1, x_298);
return x_277;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_299 = lean_ctor_get(x_277, 0);
lean_inc(x_299);
lean_dec(x_277);
x_300 = lean_ctor_get(x_278, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_278, 1);
lean_inc(x_301);
x_302 = lean_ctor_get(x_278, 3);
lean_inc(x_302);
x_303 = lean_ctor_get(x_278, 4);
lean_inc(x_303);
x_304 = lean_ctor_get(x_278, 5);
lean_inc(x_304);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 lean_ctor_release(x_278, 2);
 lean_ctor_release(x_278, 3);
 lean_ctor_release(x_278, 4);
 lean_ctor_release(x_278, 5);
 x_305 = x_278;
} else {
 lean_dec_ref(x_278);
 x_305 = lean_box(0);
}
x_306 = lean_ctor_get(x_279, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_279, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 lean_ctor_release(x_279, 2);
 x_308 = x_279;
} else {
 lean_dec_ref(x_279);
 x_308 = lean_box(0);
}
if (lean_is_scalar(x_308)) {
 x_309 = lean_alloc_ctor(0, 3, 0);
} else {
 x_309 = x_308;
}
lean_ctor_set(x_309, 0, x_306);
lean_ctor_set(x_309, 1, x_307);
lean_ctor_set(x_309, 2, x_271);
if (lean_is_scalar(x_305)) {
 x_310 = lean_alloc_ctor(0, 6, 0);
} else {
 x_310 = x_305;
}
lean_ctor_set(x_310, 0, x_300);
lean_ctor_set(x_310, 1, x_301);
lean_ctor_set(x_310, 2, x_309);
lean_ctor_set(x_310, 3, x_302);
lean_ctor_set(x_310, 4, x_303);
lean_ctor_set(x_310, 5, x_304);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_299);
lean_ctor_set(x_311, 1, x_310);
return x_311;
}
}
else
{
lean_object* x_312; lean_object* x_313; uint8_t x_314; 
x_312 = lean_ctor_get(x_277, 1);
lean_inc(x_312);
x_313 = lean_ctor_get(x_312, 2);
lean_inc(x_313);
x_314 = !lean_is_exclusive(x_277);
if (x_314 == 0)
{
lean_object* x_315; uint8_t x_316; 
x_315 = lean_ctor_get(x_277, 1);
lean_dec(x_315);
x_316 = !lean_is_exclusive(x_312);
if (x_316 == 0)
{
lean_object* x_317; uint8_t x_318; 
x_317 = lean_ctor_get(x_312, 2);
lean_dec(x_317);
x_318 = !lean_is_exclusive(x_313);
if (x_318 == 0)
{
lean_object* x_319; 
x_319 = lean_ctor_get(x_313, 2);
lean_dec(x_319);
lean_ctor_set(x_313, 2, x_271);
return x_277;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_313, 0);
x_321 = lean_ctor_get(x_313, 1);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_313);
x_322 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
lean_ctor_set(x_322, 2, x_271);
lean_ctor_set(x_312, 2, x_322);
return x_277;
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_323 = lean_ctor_get(x_312, 0);
x_324 = lean_ctor_get(x_312, 1);
x_325 = lean_ctor_get(x_312, 3);
x_326 = lean_ctor_get(x_312, 4);
x_327 = lean_ctor_get(x_312, 5);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_312);
x_328 = lean_ctor_get(x_313, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_313, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 lean_ctor_release(x_313, 2);
 x_330 = x_313;
} else {
 lean_dec_ref(x_313);
 x_330 = lean_box(0);
}
if (lean_is_scalar(x_330)) {
 x_331 = lean_alloc_ctor(0, 3, 0);
} else {
 x_331 = x_330;
}
lean_ctor_set(x_331, 0, x_328);
lean_ctor_set(x_331, 1, x_329);
lean_ctor_set(x_331, 2, x_271);
x_332 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_332, 0, x_323);
lean_ctor_set(x_332, 1, x_324);
lean_ctor_set(x_332, 2, x_331);
lean_ctor_set(x_332, 3, x_325);
lean_ctor_set(x_332, 4, x_326);
lean_ctor_set(x_332, 5, x_327);
lean_ctor_set(x_277, 1, x_332);
return x_277;
}
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_333 = lean_ctor_get(x_277, 0);
lean_inc(x_333);
lean_dec(x_277);
x_334 = lean_ctor_get(x_312, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_312, 1);
lean_inc(x_335);
x_336 = lean_ctor_get(x_312, 3);
lean_inc(x_336);
x_337 = lean_ctor_get(x_312, 4);
lean_inc(x_337);
x_338 = lean_ctor_get(x_312, 5);
lean_inc(x_338);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 lean_ctor_release(x_312, 2);
 lean_ctor_release(x_312, 3);
 lean_ctor_release(x_312, 4);
 lean_ctor_release(x_312, 5);
 x_339 = x_312;
} else {
 lean_dec_ref(x_312);
 x_339 = lean_box(0);
}
x_340 = lean_ctor_get(x_313, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_313, 1);
lean_inc(x_341);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 lean_ctor_release(x_313, 2);
 x_342 = x_313;
} else {
 lean_dec_ref(x_313);
 x_342 = lean_box(0);
}
if (lean_is_scalar(x_342)) {
 x_343 = lean_alloc_ctor(0, 3, 0);
} else {
 x_343 = x_342;
}
lean_ctor_set(x_343, 0, x_340);
lean_ctor_set(x_343, 1, x_341);
lean_ctor_set(x_343, 2, x_271);
if (lean_is_scalar(x_339)) {
 x_344 = lean_alloc_ctor(0, 6, 0);
} else {
 x_344 = x_339;
}
lean_ctor_set(x_344, 0, x_334);
lean_ctor_set(x_344, 1, x_335);
lean_ctor_set(x_344, 2, x_343);
lean_ctor_set(x_344, 3, x_336);
lean_ctor_set(x_344, 4, x_337);
lean_ctor_set(x_344, 5, x_338);
x_345 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_345, 0, x_333);
lean_ctor_set(x_345, 1, x_344);
return x_345;
}
}
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_346 = lean_ctor_get(x_6, 0);
x_347 = lean_ctor_get(x_6, 1);
x_348 = lean_ctor_get(x_6, 2);
lean_inc(x_348);
lean_inc(x_347);
lean_inc(x_346);
lean_dec(x_6);
x_349 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_349, 0, x_265);
lean_ctor_set(x_349, 1, x_27);
x_350 = lean_array_push(x_348, x_349);
x_351 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_351, 0, x_346);
lean_ctor_set(x_351, 1, x_347);
lean_ctor_set(x_351, 2, x_350);
x_352 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6(x_1, x_2, x_3, x_4, x_267, x_351, x_264);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_353 = lean_ctor_get(x_352, 1);
lean_inc(x_353);
x_354 = lean_ctor_get(x_353, 2);
lean_inc(x_354);
x_355 = lean_ctor_get(x_352, 0);
lean_inc(x_355);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_356 = x_352;
} else {
 lean_dec_ref(x_352);
 x_356 = lean_box(0);
}
x_357 = lean_ctor_get(x_353, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_353, 1);
lean_inc(x_358);
x_359 = lean_ctor_get(x_353, 3);
lean_inc(x_359);
x_360 = lean_ctor_get(x_353, 4);
lean_inc(x_360);
x_361 = lean_ctor_get(x_353, 5);
lean_inc(x_361);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 lean_ctor_release(x_353, 4);
 lean_ctor_release(x_353, 5);
 x_362 = x_353;
} else {
 lean_dec_ref(x_353);
 x_362 = lean_box(0);
}
x_363 = lean_ctor_get(x_354, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_354, 1);
lean_inc(x_364);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 lean_ctor_release(x_354, 2);
 x_365 = x_354;
} else {
 lean_dec_ref(x_354);
 x_365 = lean_box(0);
}
if (lean_is_scalar(x_365)) {
 x_366 = lean_alloc_ctor(0, 3, 0);
} else {
 x_366 = x_365;
}
lean_ctor_set(x_366, 0, x_363);
lean_ctor_set(x_366, 1, x_364);
lean_ctor_set(x_366, 2, x_271);
if (lean_is_scalar(x_362)) {
 x_367 = lean_alloc_ctor(0, 6, 0);
} else {
 x_367 = x_362;
}
lean_ctor_set(x_367, 0, x_357);
lean_ctor_set(x_367, 1, x_358);
lean_ctor_set(x_367, 2, x_366);
lean_ctor_set(x_367, 3, x_359);
lean_ctor_set(x_367, 4, x_360);
lean_ctor_set(x_367, 5, x_361);
if (lean_is_scalar(x_356)) {
 x_368 = lean_alloc_ctor(0, 2, 0);
} else {
 x_368 = x_356;
}
lean_ctor_set(x_368, 0, x_355);
lean_ctor_set(x_368, 1, x_367);
return x_368;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_369 = lean_ctor_get(x_352, 1);
lean_inc(x_369);
x_370 = lean_ctor_get(x_369, 2);
lean_inc(x_370);
x_371 = lean_ctor_get(x_352, 0);
lean_inc(x_371);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_372 = x_352;
} else {
 lean_dec_ref(x_352);
 x_372 = lean_box(0);
}
x_373 = lean_ctor_get(x_369, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_369, 1);
lean_inc(x_374);
x_375 = lean_ctor_get(x_369, 3);
lean_inc(x_375);
x_376 = lean_ctor_get(x_369, 4);
lean_inc(x_376);
x_377 = lean_ctor_get(x_369, 5);
lean_inc(x_377);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 lean_ctor_release(x_369, 2);
 lean_ctor_release(x_369, 3);
 lean_ctor_release(x_369, 4);
 lean_ctor_release(x_369, 5);
 x_378 = x_369;
} else {
 lean_dec_ref(x_369);
 x_378 = lean_box(0);
}
x_379 = lean_ctor_get(x_370, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_370, 1);
lean_inc(x_380);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 lean_ctor_release(x_370, 2);
 x_381 = x_370;
} else {
 lean_dec_ref(x_370);
 x_381 = lean_box(0);
}
if (lean_is_scalar(x_381)) {
 x_382 = lean_alloc_ctor(0, 3, 0);
} else {
 x_382 = x_381;
}
lean_ctor_set(x_382, 0, x_379);
lean_ctor_set(x_382, 1, x_380);
lean_ctor_set(x_382, 2, x_271);
if (lean_is_scalar(x_378)) {
 x_383 = lean_alloc_ctor(0, 6, 0);
} else {
 x_383 = x_378;
}
lean_ctor_set(x_383, 0, x_373);
lean_ctor_set(x_383, 1, x_374);
lean_ctor_set(x_383, 2, x_382);
lean_ctor_set(x_383, 3, x_375);
lean_ctor_set(x_383, 4, x_376);
lean_ctor_set(x_383, 5, x_377);
if (lean_is_scalar(x_372)) {
 x_384 = lean_alloc_ctor(1, 2, 0);
} else {
 x_384 = x_372;
}
lean_ctor_set(x_384, 0, x_371);
lean_ctor_set(x_384, 1, x_383);
return x_384;
}
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_385 = lean_ctor_get(x_269, 0);
x_386 = lean_ctor_get(x_269, 1);
x_387 = lean_ctor_get(x_269, 2);
lean_inc(x_387);
lean_inc(x_386);
lean_inc(x_385);
lean_dec(x_269);
x_388 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_389 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_389, 0, x_385);
lean_ctor_set(x_389, 1, x_386);
lean_ctor_set(x_389, 2, x_388);
lean_ctor_set(x_264, 2, x_389);
x_390 = lean_ctor_get(x_6, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_6, 1);
lean_inc(x_391);
x_392 = lean_ctor_get(x_6, 2);
lean_inc(x_392);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 x_393 = x_6;
} else {
 lean_dec_ref(x_6);
 x_393 = lean_box(0);
}
x_394 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_394, 0, x_265);
lean_ctor_set(x_394, 1, x_27);
x_395 = lean_array_push(x_392, x_394);
if (lean_is_scalar(x_393)) {
 x_396 = lean_alloc_ctor(0, 3, 0);
} else {
 x_396 = x_393;
}
lean_ctor_set(x_396, 0, x_390);
lean_ctor_set(x_396, 1, x_391);
lean_ctor_set(x_396, 2, x_395);
x_397 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6(x_1, x_2, x_3, x_4, x_267, x_396, x_264);
if (lean_obj_tag(x_397) == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_398 = lean_ctor_get(x_397, 1);
lean_inc(x_398);
x_399 = lean_ctor_get(x_398, 2);
lean_inc(x_399);
x_400 = lean_ctor_get(x_397, 0);
lean_inc(x_400);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 x_401 = x_397;
} else {
 lean_dec_ref(x_397);
 x_401 = lean_box(0);
}
x_402 = lean_ctor_get(x_398, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_398, 1);
lean_inc(x_403);
x_404 = lean_ctor_get(x_398, 3);
lean_inc(x_404);
x_405 = lean_ctor_get(x_398, 4);
lean_inc(x_405);
x_406 = lean_ctor_get(x_398, 5);
lean_inc(x_406);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 lean_ctor_release(x_398, 1);
 lean_ctor_release(x_398, 2);
 lean_ctor_release(x_398, 3);
 lean_ctor_release(x_398, 4);
 lean_ctor_release(x_398, 5);
 x_407 = x_398;
} else {
 lean_dec_ref(x_398);
 x_407 = lean_box(0);
}
x_408 = lean_ctor_get(x_399, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_399, 1);
lean_inc(x_409);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 lean_ctor_release(x_399, 2);
 x_410 = x_399;
} else {
 lean_dec_ref(x_399);
 x_410 = lean_box(0);
}
if (lean_is_scalar(x_410)) {
 x_411 = lean_alloc_ctor(0, 3, 0);
} else {
 x_411 = x_410;
}
lean_ctor_set(x_411, 0, x_408);
lean_ctor_set(x_411, 1, x_409);
lean_ctor_set(x_411, 2, x_387);
if (lean_is_scalar(x_407)) {
 x_412 = lean_alloc_ctor(0, 6, 0);
} else {
 x_412 = x_407;
}
lean_ctor_set(x_412, 0, x_402);
lean_ctor_set(x_412, 1, x_403);
lean_ctor_set(x_412, 2, x_411);
lean_ctor_set(x_412, 3, x_404);
lean_ctor_set(x_412, 4, x_405);
lean_ctor_set(x_412, 5, x_406);
if (lean_is_scalar(x_401)) {
 x_413 = lean_alloc_ctor(0, 2, 0);
} else {
 x_413 = x_401;
}
lean_ctor_set(x_413, 0, x_400);
lean_ctor_set(x_413, 1, x_412);
return x_413;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_414 = lean_ctor_get(x_397, 1);
lean_inc(x_414);
x_415 = lean_ctor_get(x_414, 2);
lean_inc(x_415);
x_416 = lean_ctor_get(x_397, 0);
lean_inc(x_416);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 x_417 = x_397;
} else {
 lean_dec_ref(x_397);
 x_417 = lean_box(0);
}
x_418 = lean_ctor_get(x_414, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_414, 1);
lean_inc(x_419);
x_420 = lean_ctor_get(x_414, 3);
lean_inc(x_420);
x_421 = lean_ctor_get(x_414, 4);
lean_inc(x_421);
x_422 = lean_ctor_get(x_414, 5);
lean_inc(x_422);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 lean_ctor_release(x_414, 2);
 lean_ctor_release(x_414, 3);
 lean_ctor_release(x_414, 4);
 lean_ctor_release(x_414, 5);
 x_423 = x_414;
} else {
 lean_dec_ref(x_414);
 x_423 = lean_box(0);
}
x_424 = lean_ctor_get(x_415, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_415, 1);
lean_inc(x_425);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 lean_ctor_release(x_415, 2);
 x_426 = x_415;
} else {
 lean_dec_ref(x_415);
 x_426 = lean_box(0);
}
if (lean_is_scalar(x_426)) {
 x_427 = lean_alloc_ctor(0, 3, 0);
} else {
 x_427 = x_426;
}
lean_ctor_set(x_427, 0, x_424);
lean_ctor_set(x_427, 1, x_425);
lean_ctor_set(x_427, 2, x_387);
if (lean_is_scalar(x_423)) {
 x_428 = lean_alloc_ctor(0, 6, 0);
} else {
 x_428 = x_423;
}
lean_ctor_set(x_428, 0, x_418);
lean_ctor_set(x_428, 1, x_419);
lean_ctor_set(x_428, 2, x_427);
lean_ctor_set(x_428, 3, x_420);
lean_ctor_set(x_428, 4, x_421);
lean_ctor_set(x_428, 5, x_422);
if (lean_is_scalar(x_417)) {
 x_429 = lean_alloc_ctor(1, 2, 0);
} else {
 x_429 = x_417;
}
lean_ctor_set(x_429, 0, x_416);
lean_ctor_set(x_429, 1, x_428);
return x_429;
}
}
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_430 = lean_ctor_get(x_264, 2);
x_431 = lean_ctor_get(x_264, 0);
x_432 = lean_ctor_get(x_264, 1);
x_433 = lean_ctor_get(x_264, 3);
x_434 = lean_ctor_get(x_264, 4);
x_435 = lean_ctor_get(x_264, 5);
lean_inc(x_435);
lean_inc(x_434);
lean_inc(x_433);
lean_inc(x_430);
lean_inc(x_432);
lean_inc(x_431);
lean_dec(x_264);
x_436 = lean_ctor_get(x_430, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_430, 1);
lean_inc(x_437);
x_438 = lean_ctor_get(x_430, 2);
lean_inc(x_438);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 lean_ctor_release(x_430, 2);
 x_439 = x_430;
} else {
 lean_dec_ref(x_430);
 x_439 = lean_box(0);
}
x_440 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_439)) {
 x_441 = lean_alloc_ctor(0, 3, 0);
} else {
 x_441 = x_439;
}
lean_ctor_set(x_441, 0, x_436);
lean_ctor_set(x_441, 1, x_437);
lean_ctor_set(x_441, 2, x_440);
x_442 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_442, 0, x_431);
lean_ctor_set(x_442, 1, x_432);
lean_ctor_set(x_442, 2, x_441);
lean_ctor_set(x_442, 3, x_433);
lean_ctor_set(x_442, 4, x_434);
lean_ctor_set(x_442, 5, x_435);
x_443 = lean_ctor_get(x_6, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_6, 1);
lean_inc(x_444);
x_445 = lean_ctor_get(x_6, 2);
lean_inc(x_445);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 x_446 = x_6;
} else {
 lean_dec_ref(x_6);
 x_446 = lean_box(0);
}
x_447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_447, 0, x_265);
lean_ctor_set(x_447, 1, x_27);
x_448 = lean_array_push(x_445, x_447);
if (lean_is_scalar(x_446)) {
 x_449 = lean_alloc_ctor(0, 3, 0);
} else {
 x_449 = x_446;
}
lean_ctor_set(x_449, 0, x_443);
lean_ctor_set(x_449, 1, x_444);
lean_ctor_set(x_449, 2, x_448);
x_450 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6(x_1, x_2, x_3, x_4, x_267, x_449, x_442);
if (lean_obj_tag(x_450) == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_451 = lean_ctor_get(x_450, 1);
lean_inc(x_451);
x_452 = lean_ctor_get(x_451, 2);
lean_inc(x_452);
x_453 = lean_ctor_get(x_450, 0);
lean_inc(x_453);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 lean_ctor_release(x_450, 1);
 x_454 = x_450;
} else {
 lean_dec_ref(x_450);
 x_454 = lean_box(0);
}
x_455 = lean_ctor_get(x_451, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_451, 1);
lean_inc(x_456);
x_457 = lean_ctor_get(x_451, 3);
lean_inc(x_457);
x_458 = lean_ctor_get(x_451, 4);
lean_inc(x_458);
x_459 = lean_ctor_get(x_451, 5);
lean_inc(x_459);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 lean_ctor_release(x_451, 1);
 lean_ctor_release(x_451, 2);
 lean_ctor_release(x_451, 3);
 lean_ctor_release(x_451, 4);
 lean_ctor_release(x_451, 5);
 x_460 = x_451;
} else {
 lean_dec_ref(x_451);
 x_460 = lean_box(0);
}
x_461 = lean_ctor_get(x_452, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_452, 1);
lean_inc(x_462);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 lean_ctor_release(x_452, 1);
 lean_ctor_release(x_452, 2);
 x_463 = x_452;
} else {
 lean_dec_ref(x_452);
 x_463 = lean_box(0);
}
if (lean_is_scalar(x_463)) {
 x_464 = lean_alloc_ctor(0, 3, 0);
} else {
 x_464 = x_463;
}
lean_ctor_set(x_464, 0, x_461);
lean_ctor_set(x_464, 1, x_462);
lean_ctor_set(x_464, 2, x_438);
if (lean_is_scalar(x_460)) {
 x_465 = lean_alloc_ctor(0, 6, 0);
} else {
 x_465 = x_460;
}
lean_ctor_set(x_465, 0, x_455);
lean_ctor_set(x_465, 1, x_456);
lean_ctor_set(x_465, 2, x_464);
lean_ctor_set(x_465, 3, x_457);
lean_ctor_set(x_465, 4, x_458);
lean_ctor_set(x_465, 5, x_459);
if (lean_is_scalar(x_454)) {
 x_466 = lean_alloc_ctor(0, 2, 0);
} else {
 x_466 = x_454;
}
lean_ctor_set(x_466, 0, x_453);
lean_ctor_set(x_466, 1, x_465);
return x_466;
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_467 = lean_ctor_get(x_450, 1);
lean_inc(x_467);
x_468 = lean_ctor_get(x_467, 2);
lean_inc(x_468);
x_469 = lean_ctor_get(x_450, 0);
lean_inc(x_469);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 lean_ctor_release(x_450, 1);
 x_470 = x_450;
} else {
 lean_dec_ref(x_450);
 x_470 = lean_box(0);
}
x_471 = lean_ctor_get(x_467, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_467, 1);
lean_inc(x_472);
x_473 = lean_ctor_get(x_467, 3);
lean_inc(x_473);
x_474 = lean_ctor_get(x_467, 4);
lean_inc(x_474);
x_475 = lean_ctor_get(x_467, 5);
lean_inc(x_475);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 lean_ctor_release(x_467, 2);
 lean_ctor_release(x_467, 3);
 lean_ctor_release(x_467, 4);
 lean_ctor_release(x_467, 5);
 x_476 = x_467;
} else {
 lean_dec_ref(x_467);
 x_476 = lean_box(0);
}
x_477 = lean_ctor_get(x_468, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_468, 1);
lean_inc(x_478);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 lean_ctor_release(x_468, 1);
 lean_ctor_release(x_468, 2);
 x_479 = x_468;
} else {
 lean_dec_ref(x_468);
 x_479 = lean_box(0);
}
if (lean_is_scalar(x_479)) {
 x_480 = lean_alloc_ctor(0, 3, 0);
} else {
 x_480 = x_479;
}
lean_ctor_set(x_480, 0, x_477);
lean_ctor_set(x_480, 1, x_478);
lean_ctor_set(x_480, 2, x_438);
if (lean_is_scalar(x_476)) {
 x_481 = lean_alloc_ctor(0, 6, 0);
} else {
 x_481 = x_476;
}
lean_ctor_set(x_481, 0, x_471);
lean_ctor_set(x_481, 1, x_472);
lean_ctor_set(x_481, 2, x_480);
lean_ctor_set(x_481, 3, x_473);
lean_ctor_set(x_481, 4, x_474);
lean_ctor_set(x_481, 5, x_475);
if (lean_is_scalar(x_470)) {
 x_482 = lean_alloc_ctor(1, 2, 0);
} else {
 x_482 = x_470;
}
lean_ctor_set(x_482, 0, x_469);
lean_ctor_set(x_482, 1, x_481);
return x_482;
}
}
}
}
else
{
uint8_t x_483; 
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_483 = !lean_is_exclusive(x_258);
if (x_483 == 0)
{
return x_258;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_484 = lean_ctor_get(x_258, 0);
x_485 = lean_ctor_get(x_258, 1);
lean_inc(x_485);
lean_inc(x_484);
lean_dec(x_258);
x_486 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_486, 0, x_484);
lean_ctor_set(x_486, 1, x_485);
return x_486;
}
}
}
}
}
else
{
uint8_t x_487; 
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_487 = !lean_is_exclusive(x_32);
if (x_487 == 0)
{
return x_32;
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_488 = lean_ctor_get(x_32, 0);
x_489 = lean_ctor_get(x_32, 1);
lean_inc(x_489);
lean_inc(x_488);
lean_dec(x_32);
x_490 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_490, 0, x_488);
lean_ctor_set(x_490, 1, x_489);
return x_490;
}
}
}
else
{
uint8_t x_491; 
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_491 = !lean_is_exclusive(x_28);
if (x_491 == 0)
{
return x_28;
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_492 = lean_ctor_get(x_28, 0);
x_493 = lean_ctor_get(x_28, 1);
lean_inc(x_493);
lean_inc(x_492);
lean_dec(x_28);
x_494 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_494, 0, x_492);
lean_ctor_set(x_494, 1, x_493);
return x_494;
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
if (lean_obj_tag(x_6) == 7)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_22 = lean_ctor_get(x_6, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_6, 2);
lean_inc(x_24);
x_25 = lean_ctor_get_uint64(x_6, sizeof(void*)*3);
lean_dec(x_6);
x_26 = lean_array_get_size(x_4);
x_27 = lean_expr_instantiate_rev_range(x_23, x_5, x_26, x_4);
lean_dec(x_26);
lean_dec(x_23);
x_28 = l_Lean_Meta_mkFreshId___rarg(x_8);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = (uint8_t)((x_25 << 24) >> 61);
lean_inc(x_29);
x_32 = lean_local_ctx_mk_local_decl(x_3, x_29, x_22, x_27, x_31);
x_33 = l_Lean_mkFVar(x_29);
x_34 = lean_array_push(x_4, x_33);
x_3 = x_32;
x_4 = x_34;
x_6 = x_24;
x_8 = x_30;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint64_t x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_36 = lean_ctor_get(x_6, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_6, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_6, 2);
lean_inc(x_38);
x_39 = lean_ctor_get_uint64(x_6, sizeof(void*)*3);
x_40 = lean_ctor_get(x_2, 0);
lean_inc(x_40);
x_41 = lean_array_get_size(x_4);
x_42 = lean_nat_dec_lt(x_41, x_40);
lean_dec(x_40);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_2);
x_43 = lean_expr_instantiate_rev_range(x_6, x_5, x_41, x_4);
lean_dec(x_6);
x_44 = !lean_is_exclusive(x_7);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_7, 1);
lean_dec(x_45);
lean_ctor_set(x_7, 1, x_3);
x_46 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6(x_4, x_41, x_43, x_4, x_5, x_7, x_8);
lean_dec(x_43);
lean_dec(x_4);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_7, 0);
x_48 = lean_ctor_get(x_7, 2);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_7);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_3);
lean_ctor_set(x_49, 2, x_48);
x_50 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6(x_4, x_41, x_43, x_4, x_5, x_49, x_8);
lean_dec(x_43);
lean_dec(x_4);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_6);
x_51 = lean_expr_instantiate_rev_range(x_37, x_5, x_41, x_4);
lean_dec(x_41);
lean_dec(x_37);
x_52 = l_Lean_Meta_mkFreshId___rarg(x_8);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = (uint8_t)((x_39 << 24) >> 61);
lean_inc(x_53);
x_56 = lean_local_ctx_mk_local_decl(x_3, x_53, x_36, x_51, x_55);
x_57 = l_Lean_mkFVar(x_53);
x_58 = lean_array_push(x_4, x_57);
x_3 = x_56;
x_4 = x_58;
x_6 = x_38;
x_8 = x_54;
goto _start;
}
}
}
else
{
lean_object* x_60; 
x_60 = lean_box(0);
x_9 = x_60;
goto block_21;
}
block_21:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_9);
x_10 = lean_array_get_size(x_4);
x_11 = lean_expr_instantiate_rev_range(x_6, x_5, x_10, x_4);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_7, 1);
lean_dec(x_13);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_3);
if (x_1 == 0)
{
lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_14 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4(x_4, x_10, x_11, x_4, x_5, x_7, x_8);
lean_dec(x_11);
lean_dec(x_4);
return x_14;
}
else
{
lean_object* x_15; 
lean_inc(x_5);
lean_inc(x_4);
x_15 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_11, x_4, x_5, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 2);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
lean_inc(x_3);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set(x_18, 2, x_17);
if (x_1 == 0)
{
lean_object* x_19; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_19 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4(x_4, x_10, x_11, x_4, x_5, x_18, x_8);
lean_dec(x_11);
lean_dec(x_4);
return x_19;
}
else
{
lean_object* x_20; 
lean_inc(x_5);
lean_inc(x_4);
x_20 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_11, x_4, x_5, x_18, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_20;
}
}
}
}
}
lean_object* _init_l___private_Init_Lean_Meta_Basic_6__forallTelescopeReducingAux___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_Basic_6__forallTelescopeReducingAux___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Lean_Meta_whnf(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Expr_isForall(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_2);
x_9 = l_Array_empty___closed__1;
x_10 = l___private_Init_Lean_Meta_Basic_6__forallTelescopeReducingAux___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__2___closed__1;
x_11 = l_Nat_foldMAux___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__1(x_9, x_10, x_10, x_9, x_3, x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l___private_Init_Lean_Meta_FunInfo_4__collectDeps(x_9, x_1);
lean_dec(x_1);
x_15 = l___private_Init_Lean_Meta_FunInfo_5__updateHasFwdDeps(x_13, x_14);
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
x_19 = l___private_Init_Lean_Meta_FunInfo_4__collectDeps(x_9, x_1);
lean_dec(x_1);
x_20 = l___private_Init_Lean_Meta_FunInfo_5__updateHasFwdDeps(x_17, x_19);
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
lean_dec(x_1);
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
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
x_28 = 1;
x_29 = l_Array_empty___closed__1;
x_30 = lean_unsigned_to_nat(0u);
x_31 = l___private_Init_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__3(x_28, x_2, x_27, x_29, x_30, x_6, x_3, x_7);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_5);
if (x_32 == 0)
{
return x_5;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_5, 0);
x_34 = lean_ctor_get(x_5, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_5);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 6);
x_11 = lean_ctor_get(x_4, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_13 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_10);
x_14 = l_PersistentHashMap_find_x3f___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__1(x_12, x_13);
lean_dec(x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_inc(x_3);
x_15 = l_Lean_Meta_inferType(x_1, x_3, x_4);
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_3, 2);
lean_dec(x_17);
x_18 = lean_ctor_get(x_3, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_3, 0);
lean_dec(x_19);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = 1;
lean_ctor_set_uint8(x_5, sizeof(void*)*1 + 6, x_22);
x_23 = l___private_Init_Lean_Meta_Basic_6__forallTelescopeReducingAux___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__2(x_20, x_2, x_3, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_24, 2);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
x_33 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4(x_32, x_13, x_27);
lean_ctor_set(x_25, 1, x_33);
return x_23;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_25, 0);
x_35 = lean_ctor_get(x_25, 1);
x_36 = lean_ctor_get(x_25, 2);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_25);
lean_inc(x_27);
x_37 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4(x_35, x_13, x_27);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_36);
lean_ctor_set(x_24, 2, x_38);
return x_23;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_39 = lean_ctor_get(x_24, 0);
x_40 = lean_ctor_get(x_24, 1);
x_41 = lean_ctor_get(x_24, 3);
x_42 = lean_ctor_get(x_24, 4);
x_43 = lean_ctor_get(x_24, 5);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_24);
x_44 = lean_ctor_get(x_25, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_25, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_25, 2);
lean_inc(x_46);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 x_47 = x_25;
} else {
 lean_dec_ref(x_25);
 x_47 = lean_box(0);
}
lean_inc(x_27);
x_48 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4(x_45, x_13, x_27);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 3, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_49, 2, x_46);
x_50 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_50, 0, x_39);
lean_ctor_set(x_50, 1, x_40);
lean_ctor_set(x_50, 2, x_49);
lean_ctor_set(x_50, 3, x_41);
lean_ctor_set(x_50, 4, x_42);
lean_ctor_set(x_50, 5, x_43);
lean_ctor_set(x_23, 1, x_50);
return x_23;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_51 = lean_ctor_get(x_23, 0);
lean_inc(x_51);
lean_dec(x_23);
x_52 = lean_ctor_get(x_24, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_24, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_24, 3);
lean_inc(x_54);
x_55 = lean_ctor_get(x_24, 4);
lean_inc(x_55);
x_56 = lean_ctor_get(x_24, 5);
lean_inc(x_56);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 lean_ctor_release(x_24, 3);
 lean_ctor_release(x_24, 4);
 lean_ctor_release(x_24, 5);
 x_57 = x_24;
} else {
 lean_dec_ref(x_24);
 x_57 = lean_box(0);
}
x_58 = lean_ctor_get(x_25, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_25, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_25, 2);
lean_inc(x_60);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 x_61 = x_25;
} else {
 lean_dec_ref(x_25);
 x_61 = lean_box(0);
}
lean_inc(x_51);
x_62 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4(x_59, x_13, x_51);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 3, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_60);
if (lean_is_scalar(x_57)) {
 x_64 = lean_alloc_ctor(0, 6, 0);
} else {
 x_64 = x_57;
}
lean_ctor_set(x_64, 0, x_52);
lean_ctor_set(x_64, 1, x_53);
lean_ctor_set(x_64, 2, x_63);
lean_ctor_set(x_64, 3, x_54);
lean_ctor_set(x_64, 4, x_55);
lean_ctor_set(x_64, 5, x_56);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_51);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_dec(x_13);
x_66 = !lean_is_exclusive(x_23);
if (x_66 == 0)
{
return x_23;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_23, 0);
x_68 = lean_ctor_get(x_23, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_23);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_free_object(x_3);
lean_dec(x_13);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_70 = !lean_is_exclusive(x_15);
if (x_70 == 0)
{
return x_15;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_15, 0);
x_72 = lean_ctor_get(x_15, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_15);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_15, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_15, 1);
lean_inc(x_75);
lean_dec(x_15);
x_76 = 1;
lean_ctor_set_uint8(x_5, sizeof(void*)*1 + 6, x_76);
x_77 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_77, 0, x_5);
lean_ctor_set(x_77, 1, x_6);
lean_ctor_set(x_77, 2, x_7);
x_78 = l___private_Init_Lean_Meta_Basic_6__forallTelescopeReducingAux___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__2(x_74, x_2, x_77, x_75);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_79, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_82 = x_78;
} else {
 lean_dec_ref(x_78);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_79, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_79, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_79, 3);
lean_inc(x_85);
x_86 = lean_ctor_get(x_79, 4);
lean_inc(x_86);
x_87 = lean_ctor_get(x_79, 5);
lean_inc(x_87);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 lean_ctor_release(x_79, 2);
 lean_ctor_release(x_79, 3);
 lean_ctor_release(x_79, 4);
 lean_ctor_release(x_79, 5);
 x_88 = x_79;
} else {
 lean_dec_ref(x_79);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_80, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_80, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_80, 2);
lean_inc(x_91);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 lean_ctor_release(x_80, 2);
 x_92 = x_80;
} else {
 lean_dec_ref(x_80);
 x_92 = lean_box(0);
}
lean_inc(x_81);
x_93 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4(x_90, x_13, x_81);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 3, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_89);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set(x_94, 2, x_91);
if (lean_is_scalar(x_88)) {
 x_95 = lean_alloc_ctor(0, 6, 0);
} else {
 x_95 = x_88;
}
lean_ctor_set(x_95, 0, x_83);
lean_ctor_set(x_95, 1, x_84);
lean_ctor_set(x_95, 2, x_94);
lean_ctor_set(x_95, 3, x_85);
lean_ctor_set(x_95, 4, x_86);
lean_ctor_set(x_95, 5, x_87);
if (lean_is_scalar(x_82)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_82;
}
lean_ctor_set(x_96, 0, x_81);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_13);
x_97 = lean_ctor_get(x_78, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_78, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_99 = x_78;
} else {
 lean_dec_ref(x_78);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_13);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_101 = lean_ctor_get(x_15, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_15, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_103 = x_15;
} else {
 lean_dec_ref(x_15);
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
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_13);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_105 = lean_ctor_get(x_14, 0);
lean_inc(x_105);
lean_dec(x_14);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_4);
return x_106;
}
}
else
{
lean_object* x_107; uint8_t x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_107 = lean_ctor_get(x_5, 0);
x_108 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_109 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_110 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 2);
x_111 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 3);
x_112 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 4);
x_113 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 5);
x_114 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 6);
lean_inc(x_107);
lean_dec(x_5);
x_115 = lean_ctor_get(x_4, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec(x_115);
lean_inc(x_2);
lean_inc(x_1);
x_117 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_117, 0, x_1);
lean_ctor_set(x_117, 1, x_2);
lean_ctor_set_uint8(x_117, sizeof(void*)*2, x_114);
x_118 = l_PersistentHashMap_find_x3f___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__1(x_116, x_117);
lean_dec(x_116);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; 
lean_inc(x_3);
x_119 = l_Lean_Meta_inferType(x_1, x_3, x_4);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_120 = x_3;
} else {
 lean_dec_ref(x_3);
 x_120 = lean_box(0);
}
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
lean_dec(x_119);
x_123 = 1;
x_124 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_124, 0, x_107);
lean_ctor_set_uint8(x_124, sizeof(void*)*1, x_108);
lean_ctor_set_uint8(x_124, sizeof(void*)*1 + 1, x_109);
lean_ctor_set_uint8(x_124, sizeof(void*)*1 + 2, x_110);
lean_ctor_set_uint8(x_124, sizeof(void*)*1 + 3, x_111);
lean_ctor_set_uint8(x_124, sizeof(void*)*1 + 4, x_112);
lean_ctor_set_uint8(x_124, sizeof(void*)*1 + 5, x_113);
lean_ctor_set_uint8(x_124, sizeof(void*)*1 + 6, x_123);
if (lean_is_scalar(x_120)) {
 x_125 = lean_alloc_ctor(0, 3, 0);
} else {
 x_125 = x_120;
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_6);
lean_ctor_set(x_125, 2, x_7);
x_126 = l___private_Init_Lean_Meta_Basic_6__forallTelescopeReducingAux___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__2(x_121, x_2, x_125, x_122);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_127, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_126, 0);
lean_inc(x_129);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_130 = x_126;
} else {
 lean_dec_ref(x_126);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_127, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_127, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_127, 3);
lean_inc(x_133);
x_134 = lean_ctor_get(x_127, 4);
lean_inc(x_134);
x_135 = lean_ctor_get(x_127, 5);
lean_inc(x_135);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 lean_ctor_release(x_127, 3);
 lean_ctor_release(x_127, 4);
 lean_ctor_release(x_127, 5);
 x_136 = x_127;
} else {
 lean_dec_ref(x_127);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get(x_128, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_128, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_128, 2);
lean_inc(x_139);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 lean_ctor_release(x_128, 2);
 x_140 = x_128;
} else {
 lean_dec_ref(x_128);
 x_140 = lean_box(0);
}
lean_inc(x_129);
x_141 = l_PersistentHashMap_insert___at___private_Init_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4(x_138, x_117, x_129);
if (lean_is_scalar(x_140)) {
 x_142 = lean_alloc_ctor(0, 3, 0);
} else {
 x_142 = x_140;
}
lean_ctor_set(x_142, 0, x_137);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set(x_142, 2, x_139);
if (lean_is_scalar(x_136)) {
 x_143 = lean_alloc_ctor(0, 6, 0);
} else {
 x_143 = x_136;
}
lean_ctor_set(x_143, 0, x_131);
lean_ctor_set(x_143, 1, x_132);
lean_ctor_set(x_143, 2, x_142);
lean_ctor_set(x_143, 3, x_133);
lean_ctor_set(x_143, 4, x_134);
lean_ctor_set(x_143, 5, x_135);
if (lean_is_scalar(x_130)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_130;
}
lean_ctor_set(x_144, 0, x_129);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_117);
x_145 = lean_ctor_get(x_126, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_126, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_147 = x_126;
} else {
 lean_dec_ref(x_126);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_120);
lean_dec(x_117);
lean_dec(x_107);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_149 = lean_ctor_get(x_119, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_119, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_151 = x_119;
} else {
 lean_dec_ref(x_119);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_117);
lean_dec(x_107);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_153 = lean_ctor_get(x_118, 0);
lean_inc(x_153);
lean_dec(x_118);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_4);
return x_154;
}
}
}
}
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_foldMAux___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5___lambda__1(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_withNewLocalInstances___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l___private_Init_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__3(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Meta_getFunInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = l___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux(x_1, x_5, x_3, x_4);
return x_6;
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
l___private_Init_Lean_Meta_Basic_6__forallTelescopeReducingAux___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__2___closed__1 = _init_l___private_Init_Lean_Meta_Basic_6__forallTelescopeReducingAux___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__2___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_Basic_6__forallTelescopeReducingAux___at___private_Init_Lean_Meta_FunInfo_6__getFunInfoAux___spec__2___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
