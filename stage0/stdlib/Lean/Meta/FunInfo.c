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
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Meta_TransparencyMode_hash(uint8_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClassExpensive___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_FunInfo_2__whenHasVar(lean_object*);
lean_object* l_Array_indexOfAux___main___at___private_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_qsortAux___main___at___private_Lean_Meta_FunInfo_4__collectDeps___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_5__forallTelescopeReducingAux___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__2___closed__1;
lean_object* l_Lean_Meta_isClassQuick___main(lean_object*, lean_object*, lean_object*);
size_t l_USize_sub(size_t, size_t);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_FunInfo_5__updateHasFwdDeps___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_FunInfo_5__updateHasFwdDeps___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Std_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_FunInfo_4__collectDeps___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at___private_Lean_Meta_FunInfo_4__collectDeps___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_FunInfo_3__collectDepsAux___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t l_Option_hash___at_Lean_Meta_InfoCacheKey_Hashable___spec__1(lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_qsortAux___main___at___private_Lean_Meta_FunInfo_4__collectDeps___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentHashMap_insertAux___main___rarg___closed__3;
lean_object* l___private_Lean_Meta_FunInfo_4__collectDeps(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_5__forallTelescopeReducingAux___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
size_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__2___boxed(lean_object*, lean_object*, lean_object*);
extern size_t l_Std_PersistentHashMap_insertAux___main___rarg___closed__2;
uint8_t l_Lean_Meta_TransparencyMode_beq(uint8_t, uint8_t);
lean_object* l___private_Lean_Meta_FunInfo_3__collectDepsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshId___rarg(lean_object*);
size_t l_USize_mul(size_t, size_t);
lean_object* l_Array_contains___at___private_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Array_indexOfAux___main___at___private_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___private_Lean_Meta_FunInfo_6__getFunInfoAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Std_PersistentHashMap_findAtAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_FunInfo_3__collectDepsAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__2(lean_object*, size_t, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__7(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_BinderInfo_beq(uint8_t, uint8_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at___private_Lean_Meta_FunInfo_4__collectDeps___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_FunInfo_2__whenHasVar___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__1(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_FunInfo_3__collectDepsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at___private_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
size_t lean_usize_mix_hash(size_t, size_t);
lean_object* l___private_Lean_Meta_FunInfo_5__updateHasFwdDeps(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Nat_Inhabited;
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l___private_Lean_Meta_FunInfo_2__whenHasVar___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_FunInfo_5__updateHasFwdDeps___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_4__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_FunInfo_1__checkFunInfoCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_4__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Std_PersistentHashMap_findAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
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
lean_object* x_40; size_t x_41; 
x_40 = lean_ctor_get(x_10, 0);
lean_inc(x_40);
lean_dec(x_10);
x_41 = x_2 >> x_5;
x_1 = x_40;
x_2 = x_41;
goto _start;
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
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
lean_dec(x_1);
x_46 = lean_unsigned_to_nat(0u);
x_47 = l_Std_PersistentHashMap_findAtAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__3(x_44, x_45, lean_box(0), x_46, x_3);
lean_dec(x_45);
lean_dec(x_44);
return x_47;
}
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Lean_Meta_TransparencyMode_hash(x_4);
x_8 = l_Lean_Expr_hash(x_5);
x_9 = l_Option_hash___at_Lean_Meta_InfoCacheKey_Hashable___spec__1(x_6);
x_10 = lean_usize_mix_hash(x_8, x_9);
x_11 = lean_usize_mix_hash(x_7, x_10);
x_12 = l_Std_PersistentHashMap_findAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__2(x_3, x_11, x_2);
return x_12;
}
}
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__7(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_26 = l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__5(x_6, x_25, x_1, x_9, x_10);
x_5 = x_16;
x_6 = x_26;
goto _start;
}
}
}
lean_object* l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Std_PersistentHashMap_insertAux___main___rarg___closed__2;
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
x_28 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
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
x_32 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
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
x_36 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
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
x_39 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
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
x_45 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
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
x_49 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
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
x_62 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_53, x_54, x_4, x_5);
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
x_66 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_53, x_54, x_4, x_5);
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
x_71 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_53, x_54, x_4, x_5);
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
x_74 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_53, x_54, x_4, x_5);
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
x_80 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_53, x_54, x_4, x_5);
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
x_84 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_53, x_54, x_4, x_5);
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
x_93 = l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__5(x_90, x_91, x_92, x_4, x_5);
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
x_98 = l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__5(x_95, x_96, x_97, x_4, x_5);
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
x_106 = l_Std_PersistentHashMap_insertAux___main___rarg___closed__2;
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
x_125 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_115, x_116, x_4, x_5);
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
x_130 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_115, x_116, x_4, x_5);
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
x_137 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_115, x_116, x_4, x_5);
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
x_141 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_115, x_116, x_4, x_5);
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
x_148 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_115, x_116, x_4, x_5);
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
x_153 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_115, x_116, x_4, x_5);
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
x_164 = l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__5(x_160, x_162, x_163, x_4, x_5);
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
x_172 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__6(x_1, x_171, x_4, x_5);
x_173 = 7;
x_174 = x_173 <= x_3;
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_175 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_172);
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
x_180 = l_Std_PersistentHashMap_insertAux___main___rarg___closed__3;
x_181 = l_Array_iterateMAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__7(x_3, x_178, x_179, x_178, x_171, x_180);
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
lean_object* l_Std_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_18 = l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__5(x_5, x_17, x_7, x_2, x_3);
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
x_32 = l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__5(x_19, x_31, x_21, x_2, x_3);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_23);
return x_33;
}
}
}
lean_object* l___private_Lean_Meta_FunInfo_1__checkFunInfoCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_11 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__1(x_9, x_10);
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
x_22 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4(x_21, x_10, x_16);
lean_ctor_set(x_14, 1, x_22);
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
x_25 = lean_ctor_get(x_14, 2);
x_26 = lean_ctor_get(x_14, 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
lean_inc(x_16);
x_27 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4(x_24, x_10, x_16);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_26);
lean_ctor_set(x_13, 2, x_28);
return x_12;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
x_31 = lean_ctor_get(x_13, 3);
x_32 = lean_ctor_get(x_13, 4);
x_33 = lean_ctor_get(x_13, 5);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
x_34 = lean_ctor_get(x_14, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_14, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_14, 3);
lean_inc(x_37);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 x_38 = x_14;
} else {
 lean_dec_ref(x_14);
 x_38 = lean_box(0);
}
lean_inc(x_16);
x_39 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4(x_35, x_10, x_16);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 4, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_36);
lean_ctor_set(x_40, 3, x_37);
x_41 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_41, 0, x_29);
lean_ctor_set(x_41, 1, x_30);
lean_ctor_set(x_41, 2, x_40);
lean_ctor_set(x_41, 3, x_31);
lean_ctor_set(x_41, 4, x_32);
lean_ctor_set(x_41, 5, x_33);
lean_ctor_set(x_12, 1, x_41);
return x_12;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_42 = lean_ctor_get(x_12, 0);
lean_inc(x_42);
lean_dec(x_12);
x_43 = lean_ctor_get(x_13, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_13, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_13, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_13, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_13, 5);
lean_inc(x_47);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 lean_ctor_release(x_13, 4);
 lean_ctor_release(x_13, 5);
 x_48 = x_13;
} else {
 lean_dec_ref(x_13);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_14, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_14, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_14, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_14, 3);
lean_inc(x_52);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 x_53 = x_14;
} else {
 lean_dec_ref(x_14);
 x_53 = lean_box(0);
}
lean_inc(x_42);
x_54 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4(x_50, x_10, x_42);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 4, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_51);
lean_ctor_set(x_55, 3, x_52);
if (lean_is_scalar(x_48)) {
 x_56 = lean_alloc_ctor(0, 6, 0);
} else {
 x_56 = x_48;
}
lean_ctor_set(x_56, 0, x_43);
lean_ctor_set(x_56, 1, x_44);
lean_ctor_set(x_56, 2, x_55);
lean_ctor_set(x_56, 3, x_45);
lean_ctor_set(x_56, 4, x_46);
lean_ctor_set(x_56, 5, x_47);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_42);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_10);
x_58 = !lean_is_exclusive(x_12);
if (x_58 == 0)
{
return x_12;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_12, 0);
x_60 = lean_ctor_get(x_12, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_12);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_62 = lean_ctor_get(x_11, 0);
lean_inc(x_62);
lean_dec(x_11);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_5);
return x_63;
}
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Array_iterateMAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__7(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Std_PersistentHashMap_insertAux___main___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__5(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l___private_Lean_Meta_FunInfo_2__whenHasVar___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_FunInfo_2__whenHasVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_FunInfo_2__whenHasVar___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_FunInfo_2__whenHasVar___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_FunInfo_2__whenHasVar___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_indexOfAux___main___at___private_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
uint8_t l_Array_contains___at___private_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__3(x_1, x_2, x_1, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Lean_Meta_FunInfo_3__collectDepsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_indexOfAux___main___at___private_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__1(x_1, x_2, x_4);
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
x_7 = l_Array_contains___at___private_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__2(x_3, x_6);
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
x_12 = l___private_Lean_Meta_FunInfo_3__collectDepsAux___main(x_1, x_9, x_3);
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
x_17 = l___private_Lean_Meta_FunInfo_3__collectDepsAux___main(x_1, x_14, x_3);
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
x_22 = l___private_Lean_Meta_FunInfo_3__collectDepsAux___main(x_1, x_19, x_3);
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
x_28 = l___private_Lean_Meta_FunInfo_3__collectDepsAux___main(x_1, x_24, x_3);
x_29 = l___private_Lean_Meta_FunInfo_3__collectDepsAux___main(x_1, x_25, x_28);
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
lean_object* l_Array_indexOfAux___main___at___private_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_indexOfAux___main___at___private_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_contains___at___private_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at___private_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Meta_FunInfo_3__collectDepsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_FunInfo_3__collectDepsAux___main(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Meta_FunInfo_3__collectDepsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_FunInfo_3__collectDepsAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Lean_Meta_FunInfo_3__collectDepsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_FunInfo_3__collectDepsAux(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at___private_Lean_Meta_FunInfo_4__collectDeps___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Array_qsortAux___main___at___private_Lean_Meta_FunInfo_4__collectDeps___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_24 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at___private_Lean_Meta_FunInfo_4__collectDeps___spec__2(x_3, x_19, x_17, x_2, x_2);
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
x_27 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at___private_Lean_Meta_FunInfo_4__collectDeps___spec__2(x_3, x_26, x_25, x_2, x_2);
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
x_32 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at___private_Lean_Meta_FunInfo_4__collectDeps___spec__2(x_3, x_30, x_28, x_2, x_2);
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
x_35 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at___private_Lean_Meta_FunInfo_4__collectDeps___spec__2(x_3, x_34, x_33, x_2, x_2);
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
x_8 = l_Array_qsortAux___main___at___private_Lean_Meta_FunInfo_4__collectDeps___spec__1(x_6, x_2, x_5);
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
lean_object* l___private_Lean_Meta_FunInfo_4__collectDeps(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Array_empty___closed__1;
x_4 = l___private_Lean_Meta_FunInfo_3__collectDepsAux___main(x_1, x_2, x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_5, x_6);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_qsortAux___main___at___private_Lean_Meta_FunInfo_4__collectDeps___spec__1(x_4, x_8, x_7);
lean_dec(x_7);
return x_9;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at___private_Lean_Meta_FunInfo_4__collectDeps___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at___private_Lean_Meta_FunInfo_4__collectDeps___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_qsortAux___main___at___private_Lean_Meta_FunInfo_4__collectDeps___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsortAux___main___at___private_Lean_Meta_FunInfo_4__collectDeps___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Meta_FunInfo_4__collectDeps___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_FunInfo_4__collectDeps(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_FunInfo_5__updateHasFwdDeps___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
x_12 = lean_ctor_get_uint8(x_10, sizeof(void*)*1 + 1);
x_13 = lean_ctor_get_uint8(x_10, sizeof(void*)*1 + 2);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
if (x_13 == 0)
{
uint8_t x_17; 
x_17 = l_Array_contains___at___private_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__2(x_1, x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
x_18 = x_10;
x_19 = lean_array_fset(x_9, x_2, x_18);
lean_dec(x_2);
x_2 = x_16;
x_3 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_10, 0);
lean_dec(x_22);
x_23 = 1;
lean_ctor_set_uint8(x_10, sizeof(void*)*1 + 2, x_23);
x_24 = x_10;
x_25 = lean_array_fset(x_9, x_2, x_24);
lean_dec(x_2);
x_2 = x_16;
x_3 = x_25;
goto _start;
}
else
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_10);
x_27 = 1;
x_28 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_11);
lean_ctor_set_uint8(x_28, sizeof(void*)*1 + 1, x_12);
lean_ctor_set_uint8(x_28, sizeof(void*)*1 + 2, x_27);
x_29 = x_28;
x_30 = lean_array_fset(x_9, x_2, x_29);
lean_dec(x_2);
x_2 = x_16;
x_3 = x_30;
goto _start;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_14);
x_32 = x_10;
x_33 = lean_array_fset(x_9, x_2, x_32);
lean_dec(x_2);
x_2 = x_16;
x_3 = x_33;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Meta_FunInfo_5__updateHasFwdDeps(lean_object* x_1, lean_object* x_2) {
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
x_6 = x_1;
x_7 = l_Array_umapMAux___main___at___private_Lean_Meta_FunInfo_5__updateHasFwdDeps___spec__1(x_2, x_4, x_6);
x_8 = x_7;
return x_8;
}
else
{
return x_1;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_FunInfo_5__updateHasFwdDeps___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_FunInfo_5__updateHasFwdDeps___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Meta_FunInfo_5__updateHasFwdDeps___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_FunInfo_5__updateHasFwdDeps(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_19 = l___private_Lean_Meta_FunInfo_4__collectDeps(x_1, x_18);
lean_dec(x_18);
x_20 = l___private_Lean_Meta_FunInfo_5__updateHasFwdDeps(x_4, x_19);
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
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = l_Nat_foldMAux___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__1(x_1, x_2, x_2, x_10, x_6, x_7);
lean_dec(x_2);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l___private_Lean_Meta_FunInfo_4__collectDeps(x_1, x_3);
x_15 = l___private_Lean_Meta_FunInfo_5__updateHasFwdDeps(x_13, x_14);
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
x_19 = l___private_Lean_Meta_FunInfo_4__collectDeps(x_1, x_3);
x_20 = l___private_Lean_Meta_FunInfo_5__updateHasFwdDeps(x_17, x_19);
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
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_31);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_39 = x_32;
} else {
 lean_dec_ref(x_32);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_33, 0);
lean_inc(x_40);
lean_dec(x_33);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_5, x_41);
lean_dec(x_5);
x_43 = !lean_is_exclusive(x_38);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_38, 2);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_98; uint8_t x_99; 
x_46 = lean_ctor_get(x_44, 2);
x_98 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_44, 2, x_98);
x_99 = !lean_is_exclusive(x_6);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_6, 2);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_40);
lean_ctor_set(x_101, 1, x_27);
x_102 = lean_array_push(x_100, x_101);
lean_ctor_set(x_6, 2, x_102);
x_103 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4(x_1, x_2, x_3, x_4, x_42, x_6, x_38);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_104);
x_47 = x_106;
x_48 = x_105;
goto block_97;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_103, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_103, 1);
lean_inc(x_108);
lean_dec(x_103);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_107);
x_47 = x_109;
x_48 = x_108;
goto block_97;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_110 = lean_ctor_get(x_6, 0);
x_111 = lean_ctor_get(x_6, 1);
x_112 = lean_ctor_get(x_6, 2);
x_113 = lean_ctor_get(x_6, 3);
x_114 = lean_ctor_get(x_6, 4);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_6);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_40);
lean_ctor_set(x_115, 1, x_27);
x_116 = lean_array_push(x_112, x_115);
x_117 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_117, 0, x_110);
lean_ctor_set(x_117, 1, x_111);
lean_ctor_set(x_117, 2, x_116);
lean_ctor_set(x_117, 3, x_113);
lean_ctor_set(x_117, 4, x_114);
x_118 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4(x_1, x_2, x_3, x_4, x_42, x_117, x_38);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_119);
x_47 = x_121;
x_48 = x_120;
goto block_97;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_118, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_118, 1);
lean_inc(x_123);
lean_dec(x_118);
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_122);
x_47 = x_124;
x_48 = x_123;
goto block_97;
}
}
block_97:
{
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_48, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec(x_47);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_48, 2);
lean_dec(x_52);
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_49, 2);
lean_dec(x_54);
lean_ctor_set(x_49, 2, x_46);
if (lean_is_scalar(x_39)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_39;
 lean_ctor_set_tag(x_55, 1);
}
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_48);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_49, 0);
x_57 = lean_ctor_get(x_49, 1);
x_58 = lean_ctor_get(x_49, 3);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_49);
x_59 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_59, 2, x_46);
lean_ctor_set(x_59, 3, x_58);
lean_ctor_set(x_48, 2, x_59);
if (lean_is_scalar(x_39)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_39;
 lean_ctor_set_tag(x_60, 1);
}
lean_ctor_set(x_60, 0, x_50);
lean_ctor_set(x_60, 1, x_48);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_61 = lean_ctor_get(x_48, 0);
x_62 = lean_ctor_get(x_48, 1);
x_63 = lean_ctor_get(x_48, 3);
x_64 = lean_ctor_get(x_48, 4);
x_65 = lean_ctor_get(x_48, 5);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_48);
x_66 = lean_ctor_get(x_49, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_49, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_49, 3);
lean_inc(x_68);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 lean_ctor_release(x_49, 2);
 lean_ctor_release(x_49, 3);
 x_69 = x_49;
} else {
 lean_dec_ref(x_49);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 4, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_67);
lean_ctor_set(x_70, 2, x_46);
lean_ctor_set(x_70, 3, x_68);
x_71 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_71, 0, x_61);
lean_ctor_set(x_71, 1, x_62);
lean_ctor_set(x_71, 2, x_70);
lean_ctor_set(x_71, 3, x_63);
lean_ctor_set(x_71, 4, x_64);
lean_ctor_set(x_71, 5, x_65);
if (lean_is_scalar(x_39)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_39;
 lean_ctor_set_tag(x_72, 1);
}
lean_ctor_set(x_72, 0, x_50);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = lean_ctor_get(x_48, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_47, 0);
lean_inc(x_74);
lean_dec(x_47);
x_75 = !lean_is_exclusive(x_48);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_48, 2);
lean_dec(x_76);
x_77 = !lean_is_exclusive(x_73);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_73, 2);
lean_dec(x_78);
lean_ctor_set(x_73, 2, x_46);
if (lean_is_scalar(x_39)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_39;
}
lean_ctor_set(x_79, 0, x_74);
lean_ctor_set(x_79, 1, x_48);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_73, 0);
x_81 = lean_ctor_get(x_73, 1);
x_82 = lean_ctor_get(x_73, 3);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_73);
x_83 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
lean_ctor_set(x_83, 2, x_46);
lean_ctor_set(x_83, 3, x_82);
lean_ctor_set(x_48, 2, x_83);
if (lean_is_scalar(x_39)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_39;
}
lean_ctor_set(x_84, 0, x_74);
lean_ctor_set(x_84, 1, x_48);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_85 = lean_ctor_get(x_48, 0);
x_86 = lean_ctor_get(x_48, 1);
x_87 = lean_ctor_get(x_48, 3);
x_88 = lean_ctor_get(x_48, 4);
x_89 = lean_ctor_get(x_48, 5);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_48);
x_90 = lean_ctor_get(x_73, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_73, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_73, 3);
lean_inc(x_92);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 lean_ctor_release(x_73, 3);
 x_93 = x_73;
} else {
 lean_dec_ref(x_73);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 4, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_90);
lean_ctor_set(x_94, 1, x_91);
lean_ctor_set(x_94, 2, x_46);
lean_ctor_set(x_94, 3, x_92);
x_95 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_95, 0, x_85);
lean_ctor_set(x_95, 1, x_86);
lean_ctor_set(x_95, 2, x_94);
lean_ctor_set(x_95, 3, x_87);
lean_ctor_set(x_95, 4, x_88);
lean_ctor_set(x_95, 5, x_89);
if (lean_is_scalar(x_39)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_39;
}
lean_ctor_set(x_96, 0, x_74);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_125 = lean_ctor_get(x_44, 0);
x_126 = lean_ctor_get(x_44, 1);
x_127 = lean_ctor_get(x_44, 2);
x_128 = lean_ctor_get(x_44, 3);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_44);
x_162 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_163 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_163, 0, x_125);
lean_ctor_set(x_163, 1, x_126);
lean_ctor_set(x_163, 2, x_162);
lean_ctor_set(x_163, 3, x_128);
lean_ctor_set(x_38, 2, x_163);
x_164 = lean_ctor_get(x_6, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_6, 1);
lean_inc(x_165);
x_166 = lean_ctor_get(x_6, 2);
lean_inc(x_166);
x_167 = lean_ctor_get(x_6, 3);
lean_inc(x_167);
x_168 = lean_ctor_get(x_6, 4);
lean_inc(x_168);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_169 = x_6;
} else {
 lean_dec_ref(x_6);
 x_169 = lean_box(0);
}
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_40);
lean_ctor_set(x_170, 1, x_27);
x_171 = lean_array_push(x_166, x_170);
if (lean_is_scalar(x_169)) {
 x_172 = lean_alloc_ctor(0, 5, 0);
} else {
 x_172 = x_169;
}
lean_ctor_set(x_172, 0, x_164);
lean_ctor_set(x_172, 1, x_165);
lean_ctor_set(x_172, 2, x_171);
lean_ctor_set(x_172, 3, x_167);
lean_ctor_set(x_172, 4, x_168);
x_173 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4(x_1, x_2, x_3, x_4, x_42, x_172, x_38);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_176, 0, x_174);
x_129 = x_176;
x_130 = x_175;
goto block_161;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_173, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_173, 1);
lean_inc(x_178);
lean_dec(x_173);
x_179 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_179, 0, x_177);
x_129 = x_179;
x_130 = x_178;
goto block_161;
}
block_161:
{
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_131 = lean_ctor_get(x_130, 2);
lean_inc(x_131);
x_132 = lean_ctor_get(x_129, 0);
lean_inc(x_132);
lean_dec(x_129);
x_133 = lean_ctor_get(x_130, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_130, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_130, 3);
lean_inc(x_135);
x_136 = lean_ctor_get(x_130, 4);
lean_inc(x_136);
x_137 = lean_ctor_get(x_130, 5);
lean_inc(x_137);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 lean_ctor_release(x_130, 2);
 lean_ctor_release(x_130, 3);
 lean_ctor_release(x_130, 4);
 lean_ctor_release(x_130, 5);
 x_138 = x_130;
} else {
 lean_dec_ref(x_130);
 x_138 = lean_box(0);
}
x_139 = lean_ctor_get(x_131, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_131, 1);
lean_inc(x_140);
x_141 = lean_ctor_get(x_131, 3);
lean_inc(x_141);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 lean_ctor_release(x_131, 3);
 x_142 = x_131;
} else {
 lean_dec_ref(x_131);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(0, 4, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_139);
lean_ctor_set(x_143, 1, x_140);
lean_ctor_set(x_143, 2, x_127);
lean_ctor_set(x_143, 3, x_141);
if (lean_is_scalar(x_138)) {
 x_144 = lean_alloc_ctor(0, 6, 0);
} else {
 x_144 = x_138;
}
lean_ctor_set(x_144, 0, x_133);
lean_ctor_set(x_144, 1, x_134);
lean_ctor_set(x_144, 2, x_143);
lean_ctor_set(x_144, 3, x_135);
lean_ctor_set(x_144, 4, x_136);
lean_ctor_set(x_144, 5, x_137);
if (lean_is_scalar(x_39)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_39;
 lean_ctor_set_tag(x_145, 1);
}
lean_ctor_set(x_145, 0, x_132);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_146 = lean_ctor_get(x_130, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_129, 0);
lean_inc(x_147);
lean_dec(x_129);
x_148 = lean_ctor_get(x_130, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_130, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_130, 3);
lean_inc(x_150);
x_151 = lean_ctor_get(x_130, 4);
lean_inc(x_151);
x_152 = lean_ctor_get(x_130, 5);
lean_inc(x_152);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 lean_ctor_release(x_130, 2);
 lean_ctor_release(x_130, 3);
 lean_ctor_release(x_130, 4);
 lean_ctor_release(x_130, 5);
 x_153 = x_130;
} else {
 lean_dec_ref(x_130);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_146, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_146, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_146, 3);
lean_inc(x_156);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 lean_ctor_release(x_146, 2);
 lean_ctor_release(x_146, 3);
 x_157 = x_146;
} else {
 lean_dec_ref(x_146);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(0, 4, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_154);
lean_ctor_set(x_158, 1, x_155);
lean_ctor_set(x_158, 2, x_127);
lean_ctor_set(x_158, 3, x_156);
if (lean_is_scalar(x_153)) {
 x_159 = lean_alloc_ctor(0, 6, 0);
} else {
 x_159 = x_153;
}
lean_ctor_set(x_159, 0, x_148);
lean_ctor_set(x_159, 1, x_149);
lean_ctor_set(x_159, 2, x_158);
lean_ctor_set(x_159, 3, x_150);
lean_ctor_set(x_159, 4, x_151);
lean_ctor_set(x_159, 5, x_152);
if (lean_is_scalar(x_39)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_39;
}
lean_ctor_set(x_160, 0, x_147);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_180 = lean_ctor_get(x_38, 2);
x_181 = lean_ctor_get(x_38, 0);
x_182 = lean_ctor_get(x_38, 1);
x_183 = lean_ctor_get(x_38, 3);
x_184 = lean_ctor_get(x_38, 4);
x_185 = lean_ctor_get(x_38, 5);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_180);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_38);
x_186 = lean_ctor_get(x_180, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_180, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_180, 2);
lean_inc(x_188);
x_189 = lean_ctor_get(x_180, 3);
lean_inc(x_189);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 lean_ctor_release(x_180, 2);
 lean_ctor_release(x_180, 3);
 x_190 = x_180;
} else {
 lean_dec_ref(x_180);
 x_190 = lean_box(0);
}
x_224 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_190)) {
 x_225 = lean_alloc_ctor(0, 4, 0);
} else {
 x_225 = x_190;
}
lean_ctor_set(x_225, 0, x_186);
lean_ctor_set(x_225, 1, x_187);
lean_ctor_set(x_225, 2, x_224);
lean_ctor_set(x_225, 3, x_189);
x_226 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_226, 0, x_181);
lean_ctor_set(x_226, 1, x_182);
lean_ctor_set(x_226, 2, x_225);
lean_ctor_set(x_226, 3, x_183);
lean_ctor_set(x_226, 4, x_184);
lean_ctor_set(x_226, 5, x_185);
x_227 = lean_ctor_get(x_6, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_6, 1);
lean_inc(x_228);
x_229 = lean_ctor_get(x_6, 2);
lean_inc(x_229);
x_230 = lean_ctor_get(x_6, 3);
lean_inc(x_230);
x_231 = lean_ctor_get(x_6, 4);
lean_inc(x_231);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_232 = x_6;
} else {
 lean_dec_ref(x_6);
 x_232 = lean_box(0);
}
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_40);
lean_ctor_set(x_233, 1, x_27);
x_234 = lean_array_push(x_229, x_233);
if (lean_is_scalar(x_232)) {
 x_235 = lean_alloc_ctor(0, 5, 0);
} else {
 x_235 = x_232;
}
lean_ctor_set(x_235, 0, x_227);
lean_ctor_set(x_235, 1, x_228);
lean_ctor_set(x_235, 2, x_234);
lean_ctor_set(x_235, 3, x_230);
lean_ctor_set(x_235, 4, x_231);
x_236 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4(x_1, x_2, x_3, x_4, x_42, x_235, x_226);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec(x_236);
x_239 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_239, 0, x_237);
x_191 = x_239;
x_192 = x_238;
goto block_223;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_236, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_236, 1);
lean_inc(x_241);
lean_dec(x_236);
x_242 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_242, 0, x_240);
x_191 = x_242;
x_192 = x_241;
goto block_223;
}
block_223:
{
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_193 = lean_ctor_get(x_192, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_191, 0);
lean_inc(x_194);
lean_dec(x_191);
x_195 = lean_ctor_get(x_192, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_192, 1);
lean_inc(x_196);
x_197 = lean_ctor_get(x_192, 3);
lean_inc(x_197);
x_198 = lean_ctor_get(x_192, 4);
lean_inc(x_198);
x_199 = lean_ctor_get(x_192, 5);
lean_inc(x_199);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 lean_ctor_release(x_192, 2);
 lean_ctor_release(x_192, 3);
 lean_ctor_release(x_192, 4);
 lean_ctor_release(x_192, 5);
 x_200 = x_192;
} else {
 lean_dec_ref(x_192);
 x_200 = lean_box(0);
}
x_201 = lean_ctor_get(x_193, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_193, 1);
lean_inc(x_202);
x_203 = lean_ctor_get(x_193, 3);
lean_inc(x_203);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_204 = x_193;
} else {
 lean_dec_ref(x_193);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(0, 4, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_201);
lean_ctor_set(x_205, 1, x_202);
lean_ctor_set(x_205, 2, x_188);
lean_ctor_set(x_205, 3, x_203);
if (lean_is_scalar(x_200)) {
 x_206 = lean_alloc_ctor(0, 6, 0);
} else {
 x_206 = x_200;
}
lean_ctor_set(x_206, 0, x_195);
lean_ctor_set(x_206, 1, x_196);
lean_ctor_set(x_206, 2, x_205);
lean_ctor_set(x_206, 3, x_197);
lean_ctor_set(x_206, 4, x_198);
lean_ctor_set(x_206, 5, x_199);
if (lean_is_scalar(x_39)) {
 x_207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_207 = x_39;
 lean_ctor_set_tag(x_207, 1);
}
lean_ctor_set(x_207, 0, x_194);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_208 = lean_ctor_get(x_192, 2);
lean_inc(x_208);
x_209 = lean_ctor_get(x_191, 0);
lean_inc(x_209);
lean_dec(x_191);
x_210 = lean_ctor_get(x_192, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_192, 1);
lean_inc(x_211);
x_212 = lean_ctor_get(x_192, 3);
lean_inc(x_212);
x_213 = lean_ctor_get(x_192, 4);
lean_inc(x_213);
x_214 = lean_ctor_get(x_192, 5);
lean_inc(x_214);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 lean_ctor_release(x_192, 2);
 lean_ctor_release(x_192, 3);
 lean_ctor_release(x_192, 4);
 lean_ctor_release(x_192, 5);
 x_215 = x_192;
} else {
 lean_dec_ref(x_192);
 x_215 = lean_box(0);
}
x_216 = lean_ctor_get(x_208, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_208, 1);
lean_inc(x_217);
x_218 = lean_ctor_get(x_208, 3);
lean_inc(x_218);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 lean_ctor_release(x_208, 2);
 lean_ctor_release(x_208, 3);
 x_219 = x_208;
} else {
 lean_dec_ref(x_208);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(0, 4, 0);
} else {
 x_220 = x_219;
}
lean_ctor_set(x_220, 0, x_216);
lean_ctor_set(x_220, 1, x_217);
lean_ctor_set(x_220, 2, x_188);
lean_ctor_set(x_220, 3, x_218);
if (lean_is_scalar(x_215)) {
 x_221 = lean_alloc_ctor(0, 6, 0);
} else {
 x_221 = x_215;
}
lean_ctor_set(x_221, 0, x_210);
lean_ctor_set(x_221, 1, x_211);
lean_ctor_set(x_221, 2, x_220);
lean_ctor_set(x_221, 3, x_212);
lean_ctor_set(x_221, 4, x_213);
lean_ctor_set(x_221, 5, x_214);
if (lean_is_scalar(x_39)) {
 x_222 = lean_alloc_ctor(0, 2, 0);
} else {
 x_222 = x_39;
}
lean_ctor_set(x_222, 0, x_209);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
}
}
default: 
{
lean_object* x_243; lean_object* x_244; 
x_243 = lean_ctor_get(x_32, 1);
lean_inc(x_243);
lean_dec(x_32);
lean_inc(x_6);
x_244 = l_Lean_Meta_isClassExpensive___main(x_31, x_6, x_243);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_27);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = lean_unsigned_to_nat(1u);
x_248 = lean_nat_add(x_5, x_247);
lean_dec(x_5);
x_5 = x_248;
x_7 = x_246;
goto _start;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; 
x_250 = lean_ctor_get(x_244, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_251 = x_244;
} else {
 lean_dec_ref(x_244);
 x_251 = lean_box(0);
}
x_252 = lean_ctor_get(x_245, 0);
lean_inc(x_252);
lean_dec(x_245);
x_253 = lean_unsigned_to_nat(1u);
x_254 = lean_nat_add(x_5, x_253);
lean_dec(x_5);
x_255 = !lean_is_exclusive(x_250);
if (x_255 == 0)
{
lean_object* x_256; uint8_t x_257; 
x_256 = lean_ctor_get(x_250, 2);
x_257 = !lean_is_exclusive(x_256);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_310; uint8_t x_311; 
x_258 = lean_ctor_get(x_256, 2);
x_310 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_256, 2, x_310);
x_311 = !lean_is_exclusive(x_6);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_312 = lean_ctor_get(x_6, 2);
x_313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_313, 0, x_252);
lean_ctor_set(x_313, 1, x_27);
x_314 = lean_array_push(x_312, x_313);
lean_ctor_set(x_6, 2, x_314);
x_315 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4(x_1, x_2, x_3, x_4, x_254, x_6, x_250);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
x_318 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_318, 0, x_316);
x_259 = x_318;
x_260 = x_317;
goto block_309;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_319 = lean_ctor_get(x_315, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_315, 1);
lean_inc(x_320);
lean_dec(x_315);
x_321 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_321, 0, x_319);
x_259 = x_321;
x_260 = x_320;
goto block_309;
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_322 = lean_ctor_get(x_6, 0);
x_323 = lean_ctor_get(x_6, 1);
x_324 = lean_ctor_get(x_6, 2);
x_325 = lean_ctor_get(x_6, 3);
x_326 = lean_ctor_get(x_6, 4);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_6);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_252);
lean_ctor_set(x_327, 1, x_27);
x_328 = lean_array_push(x_324, x_327);
x_329 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_329, 0, x_322);
lean_ctor_set(x_329, 1, x_323);
lean_ctor_set(x_329, 2, x_328);
lean_ctor_set(x_329, 3, x_325);
lean_ctor_set(x_329, 4, x_326);
x_330 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4(x_1, x_2, x_3, x_4, x_254, x_329, x_250);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
lean_dec(x_330);
x_333 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_333, 0, x_331);
x_259 = x_333;
x_260 = x_332;
goto block_309;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_330, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_330, 1);
lean_inc(x_335);
lean_dec(x_330);
x_336 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_336, 0, x_334);
x_259 = x_336;
x_260 = x_335;
goto block_309;
}
}
block_309:
{
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_261 = lean_ctor_get(x_260, 2);
lean_inc(x_261);
x_262 = lean_ctor_get(x_259, 0);
lean_inc(x_262);
lean_dec(x_259);
x_263 = !lean_is_exclusive(x_260);
if (x_263 == 0)
{
lean_object* x_264; uint8_t x_265; 
x_264 = lean_ctor_get(x_260, 2);
lean_dec(x_264);
x_265 = !lean_is_exclusive(x_261);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_261, 2);
lean_dec(x_266);
lean_ctor_set(x_261, 2, x_258);
if (lean_is_scalar(x_251)) {
 x_267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_267 = x_251;
 lean_ctor_set_tag(x_267, 1);
}
lean_ctor_set(x_267, 0, x_262);
lean_ctor_set(x_267, 1, x_260);
return x_267;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_268 = lean_ctor_get(x_261, 0);
x_269 = lean_ctor_get(x_261, 1);
x_270 = lean_ctor_get(x_261, 3);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_261);
x_271 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_271, 0, x_268);
lean_ctor_set(x_271, 1, x_269);
lean_ctor_set(x_271, 2, x_258);
lean_ctor_set(x_271, 3, x_270);
lean_ctor_set(x_260, 2, x_271);
if (lean_is_scalar(x_251)) {
 x_272 = lean_alloc_ctor(1, 2, 0);
} else {
 x_272 = x_251;
 lean_ctor_set_tag(x_272, 1);
}
lean_ctor_set(x_272, 0, x_262);
lean_ctor_set(x_272, 1, x_260);
return x_272;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_273 = lean_ctor_get(x_260, 0);
x_274 = lean_ctor_get(x_260, 1);
x_275 = lean_ctor_get(x_260, 3);
x_276 = lean_ctor_get(x_260, 4);
x_277 = lean_ctor_get(x_260, 5);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_260);
x_278 = lean_ctor_get(x_261, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_261, 1);
lean_inc(x_279);
x_280 = lean_ctor_get(x_261, 3);
lean_inc(x_280);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 lean_ctor_release(x_261, 2);
 lean_ctor_release(x_261, 3);
 x_281 = x_261;
} else {
 lean_dec_ref(x_261);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(0, 4, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_278);
lean_ctor_set(x_282, 1, x_279);
lean_ctor_set(x_282, 2, x_258);
lean_ctor_set(x_282, 3, x_280);
x_283 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_283, 0, x_273);
lean_ctor_set(x_283, 1, x_274);
lean_ctor_set(x_283, 2, x_282);
lean_ctor_set(x_283, 3, x_275);
lean_ctor_set(x_283, 4, x_276);
lean_ctor_set(x_283, 5, x_277);
if (lean_is_scalar(x_251)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_251;
 lean_ctor_set_tag(x_284, 1);
}
lean_ctor_set(x_284, 0, x_262);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
}
else
{
lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_285 = lean_ctor_get(x_260, 2);
lean_inc(x_285);
x_286 = lean_ctor_get(x_259, 0);
lean_inc(x_286);
lean_dec(x_259);
x_287 = !lean_is_exclusive(x_260);
if (x_287 == 0)
{
lean_object* x_288; uint8_t x_289; 
x_288 = lean_ctor_get(x_260, 2);
lean_dec(x_288);
x_289 = !lean_is_exclusive(x_285);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_285, 2);
lean_dec(x_290);
lean_ctor_set(x_285, 2, x_258);
if (lean_is_scalar(x_251)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_251;
}
lean_ctor_set(x_291, 0, x_286);
lean_ctor_set(x_291, 1, x_260);
return x_291;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_292 = lean_ctor_get(x_285, 0);
x_293 = lean_ctor_get(x_285, 1);
x_294 = lean_ctor_get(x_285, 3);
lean_inc(x_294);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_285);
x_295 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_295, 0, x_292);
lean_ctor_set(x_295, 1, x_293);
lean_ctor_set(x_295, 2, x_258);
lean_ctor_set(x_295, 3, x_294);
lean_ctor_set(x_260, 2, x_295);
if (lean_is_scalar(x_251)) {
 x_296 = lean_alloc_ctor(0, 2, 0);
} else {
 x_296 = x_251;
}
lean_ctor_set(x_296, 0, x_286);
lean_ctor_set(x_296, 1, x_260);
return x_296;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_297 = lean_ctor_get(x_260, 0);
x_298 = lean_ctor_get(x_260, 1);
x_299 = lean_ctor_get(x_260, 3);
x_300 = lean_ctor_get(x_260, 4);
x_301 = lean_ctor_get(x_260, 5);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_260);
x_302 = lean_ctor_get(x_285, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_285, 1);
lean_inc(x_303);
x_304 = lean_ctor_get(x_285, 3);
lean_inc(x_304);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 lean_ctor_release(x_285, 2);
 lean_ctor_release(x_285, 3);
 x_305 = x_285;
} else {
 lean_dec_ref(x_285);
 x_305 = lean_box(0);
}
if (lean_is_scalar(x_305)) {
 x_306 = lean_alloc_ctor(0, 4, 0);
} else {
 x_306 = x_305;
}
lean_ctor_set(x_306, 0, x_302);
lean_ctor_set(x_306, 1, x_303);
lean_ctor_set(x_306, 2, x_258);
lean_ctor_set(x_306, 3, x_304);
x_307 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_307, 0, x_297);
lean_ctor_set(x_307, 1, x_298);
lean_ctor_set(x_307, 2, x_306);
lean_ctor_set(x_307, 3, x_299);
lean_ctor_set(x_307, 4, x_300);
lean_ctor_set(x_307, 5, x_301);
if (lean_is_scalar(x_251)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_251;
}
lean_ctor_set(x_308, 0, x_286);
lean_ctor_set(x_308, 1, x_307);
return x_308;
}
}
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_337 = lean_ctor_get(x_256, 0);
x_338 = lean_ctor_get(x_256, 1);
x_339 = lean_ctor_get(x_256, 2);
x_340 = lean_ctor_get(x_256, 3);
lean_inc(x_340);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_256);
x_374 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_375 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_375, 0, x_337);
lean_ctor_set(x_375, 1, x_338);
lean_ctor_set(x_375, 2, x_374);
lean_ctor_set(x_375, 3, x_340);
lean_ctor_set(x_250, 2, x_375);
x_376 = lean_ctor_get(x_6, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_6, 1);
lean_inc(x_377);
x_378 = lean_ctor_get(x_6, 2);
lean_inc(x_378);
x_379 = lean_ctor_get(x_6, 3);
lean_inc(x_379);
x_380 = lean_ctor_get(x_6, 4);
lean_inc(x_380);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_381 = x_6;
} else {
 lean_dec_ref(x_6);
 x_381 = lean_box(0);
}
x_382 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_382, 0, x_252);
lean_ctor_set(x_382, 1, x_27);
x_383 = lean_array_push(x_378, x_382);
if (lean_is_scalar(x_381)) {
 x_384 = lean_alloc_ctor(0, 5, 0);
} else {
 x_384 = x_381;
}
lean_ctor_set(x_384, 0, x_376);
lean_ctor_set(x_384, 1, x_377);
lean_ctor_set(x_384, 2, x_383);
lean_ctor_set(x_384, 3, x_379);
lean_ctor_set(x_384, 4, x_380);
x_385 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4(x_1, x_2, x_3, x_4, x_254, x_384, x_250);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_385, 1);
lean_inc(x_387);
lean_dec(x_385);
x_388 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_388, 0, x_386);
x_341 = x_388;
x_342 = x_387;
goto block_373;
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_389 = lean_ctor_get(x_385, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_385, 1);
lean_inc(x_390);
lean_dec(x_385);
x_391 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_391, 0, x_389);
x_341 = x_391;
x_342 = x_390;
goto block_373;
}
block_373:
{
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_343 = lean_ctor_get(x_342, 2);
lean_inc(x_343);
x_344 = lean_ctor_get(x_341, 0);
lean_inc(x_344);
lean_dec(x_341);
x_345 = lean_ctor_get(x_342, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_342, 1);
lean_inc(x_346);
x_347 = lean_ctor_get(x_342, 3);
lean_inc(x_347);
x_348 = lean_ctor_get(x_342, 4);
lean_inc(x_348);
x_349 = lean_ctor_get(x_342, 5);
lean_inc(x_349);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 lean_ctor_release(x_342, 2);
 lean_ctor_release(x_342, 3);
 lean_ctor_release(x_342, 4);
 lean_ctor_release(x_342, 5);
 x_350 = x_342;
} else {
 lean_dec_ref(x_342);
 x_350 = lean_box(0);
}
x_351 = lean_ctor_get(x_343, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_343, 1);
lean_inc(x_352);
x_353 = lean_ctor_get(x_343, 3);
lean_inc(x_353);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 lean_ctor_release(x_343, 2);
 lean_ctor_release(x_343, 3);
 x_354 = x_343;
} else {
 lean_dec_ref(x_343);
 x_354 = lean_box(0);
}
if (lean_is_scalar(x_354)) {
 x_355 = lean_alloc_ctor(0, 4, 0);
} else {
 x_355 = x_354;
}
lean_ctor_set(x_355, 0, x_351);
lean_ctor_set(x_355, 1, x_352);
lean_ctor_set(x_355, 2, x_339);
lean_ctor_set(x_355, 3, x_353);
if (lean_is_scalar(x_350)) {
 x_356 = lean_alloc_ctor(0, 6, 0);
} else {
 x_356 = x_350;
}
lean_ctor_set(x_356, 0, x_345);
lean_ctor_set(x_356, 1, x_346);
lean_ctor_set(x_356, 2, x_355);
lean_ctor_set(x_356, 3, x_347);
lean_ctor_set(x_356, 4, x_348);
lean_ctor_set(x_356, 5, x_349);
if (lean_is_scalar(x_251)) {
 x_357 = lean_alloc_ctor(1, 2, 0);
} else {
 x_357 = x_251;
 lean_ctor_set_tag(x_357, 1);
}
lean_ctor_set(x_357, 0, x_344);
lean_ctor_set(x_357, 1, x_356);
return x_357;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_358 = lean_ctor_get(x_342, 2);
lean_inc(x_358);
x_359 = lean_ctor_get(x_341, 0);
lean_inc(x_359);
lean_dec(x_341);
x_360 = lean_ctor_get(x_342, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_342, 1);
lean_inc(x_361);
x_362 = lean_ctor_get(x_342, 3);
lean_inc(x_362);
x_363 = lean_ctor_get(x_342, 4);
lean_inc(x_363);
x_364 = lean_ctor_get(x_342, 5);
lean_inc(x_364);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 lean_ctor_release(x_342, 2);
 lean_ctor_release(x_342, 3);
 lean_ctor_release(x_342, 4);
 lean_ctor_release(x_342, 5);
 x_365 = x_342;
} else {
 lean_dec_ref(x_342);
 x_365 = lean_box(0);
}
x_366 = lean_ctor_get(x_358, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_358, 1);
lean_inc(x_367);
x_368 = lean_ctor_get(x_358, 3);
lean_inc(x_368);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 lean_ctor_release(x_358, 2);
 lean_ctor_release(x_358, 3);
 x_369 = x_358;
} else {
 lean_dec_ref(x_358);
 x_369 = lean_box(0);
}
if (lean_is_scalar(x_369)) {
 x_370 = lean_alloc_ctor(0, 4, 0);
} else {
 x_370 = x_369;
}
lean_ctor_set(x_370, 0, x_366);
lean_ctor_set(x_370, 1, x_367);
lean_ctor_set(x_370, 2, x_339);
lean_ctor_set(x_370, 3, x_368);
if (lean_is_scalar(x_365)) {
 x_371 = lean_alloc_ctor(0, 6, 0);
} else {
 x_371 = x_365;
}
lean_ctor_set(x_371, 0, x_360);
lean_ctor_set(x_371, 1, x_361);
lean_ctor_set(x_371, 2, x_370);
lean_ctor_set(x_371, 3, x_362);
lean_ctor_set(x_371, 4, x_363);
lean_ctor_set(x_371, 5, x_364);
if (lean_is_scalar(x_251)) {
 x_372 = lean_alloc_ctor(0, 2, 0);
} else {
 x_372 = x_251;
}
lean_ctor_set(x_372, 0, x_359);
lean_ctor_set(x_372, 1, x_371);
return x_372;
}
}
}
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_392 = lean_ctor_get(x_250, 2);
x_393 = lean_ctor_get(x_250, 0);
x_394 = lean_ctor_get(x_250, 1);
x_395 = lean_ctor_get(x_250, 3);
x_396 = lean_ctor_get(x_250, 4);
x_397 = lean_ctor_get(x_250, 5);
lean_inc(x_397);
lean_inc(x_396);
lean_inc(x_395);
lean_inc(x_392);
lean_inc(x_394);
lean_inc(x_393);
lean_dec(x_250);
x_398 = lean_ctor_get(x_392, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_392, 1);
lean_inc(x_399);
x_400 = lean_ctor_get(x_392, 2);
lean_inc(x_400);
x_401 = lean_ctor_get(x_392, 3);
lean_inc(x_401);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 lean_ctor_release(x_392, 2);
 lean_ctor_release(x_392, 3);
 x_402 = x_392;
} else {
 lean_dec_ref(x_392);
 x_402 = lean_box(0);
}
x_436 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_402)) {
 x_437 = lean_alloc_ctor(0, 4, 0);
} else {
 x_437 = x_402;
}
lean_ctor_set(x_437, 0, x_398);
lean_ctor_set(x_437, 1, x_399);
lean_ctor_set(x_437, 2, x_436);
lean_ctor_set(x_437, 3, x_401);
x_438 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_438, 0, x_393);
lean_ctor_set(x_438, 1, x_394);
lean_ctor_set(x_438, 2, x_437);
lean_ctor_set(x_438, 3, x_395);
lean_ctor_set(x_438, 4, x_396);
lean_ctor_set(x_438, 5, x_397);
x_439 = lean_ctor_get(x_6, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_6, 1);
lean_inc(x_440);
x_441 = lean_ctor_get(x_6, 2);
lean_inc(x_441);
x_442 = lean_ctor_get(x_6, 3);
lean_inc(x_442);
x_443 = lean_ctor_get(x_6, 4);
lean_inc(x_443);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_444 = x_6;
} else {
 lean_dec_ref(x_6);
 x_444 = lean_box(0);
}
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_252);
lean_ctor_set(x_445, 1, x_27);
x_446 = lean_array_push(x_441, x_445);
if (lean_is_scalar(x_444)) {
 x_447 = lean_alloc_ctor(0, 5, 0);
} else {
 x_447 = x_444;
}
lean_ctor_set(x_447, 0, x_439);
lean_ctor_set(x_447, 1, x_440);
lean_ctor_set(x_447, 2, x_446);
lean_ctor_set(x_447, 3, x_442);
lean_ctor_set(x_447, 4, x_443);
x_448 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4(x_1, x_2, x_3, x_4, x_254, x_447, x_438);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_448, 1);
lean_inc(x_450);
lean_dec(x_448);
x_451 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_451, 0, x_449);
x_403 = x_451;
x_404 = x_450;
goto block_435;
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_452 = lean_ctor_get(x_448, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_448, 1);
lean_inc(x_453);
lean_dec(x_448);
x_454 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_454, 0, x_452);
x_403 = x_454;
x_404 = x_453;
goto block_435;
}
block_435:
{
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_405 = lean_ctor_get(x_404, 2);
lean_inc(x_405);
x_406 = lean_ctor_get(x_403, 0);
lean_inc(x_406);
lean_dec(x_403);
x_407 = lean_ctor_get(x_404, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_404, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_404, 3);
lean_inc(x_409);
x_410 = lean_ctor_get(x_404, 4);
lean_inc(x_410);
x_411 = lean_ctor_get(x_404, 5);
lean_inc(x_411);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 lean_ctor_release(x_404, 2);
 lean_ctor_release(x_404, 3);
 lean_ctor_release(x_404, 4);
 lean_ctor_release(x_404, 5);
 x_412 = x_404;
} else {
 lean_dec_ref(x_404);
 x_412 = lean_box(0);
}
x_413 = lean_ctor_get(x_405, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_405, 1);
lean_inc(x_414);
x_415 = lean_ctor_get(x_405, 3);
lean_inc(x_415);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 lean_ctor_release(x_405, 2);
 lean_ctor_release(x_405, 3);
 x_416 = x_405;
} else {
 lean_dec_ref(x_405);
 x_416 = lean_box(0);
}
if (lean_is_scalar(x_416)) {
 x_417 = lean_alloc_ctor(0, 4, 0);
} else {
 x_417 = x_416;
}
lean_ctor_set(x_417, 0, x_413);
lean_ctor_set(x_417, 1, x_414);
lean_ctor_set(x_417, 2, x_400);
lean_ctor_set(x_417, 3, x_415);
if (lean_is_scalar(x_412)) {
 x_418 = lean_alloc_ctor(0, 6, 0);
} else {
 x_418 = x_412;
}
lean_ctor_set(x_418, 0, x_407);
lean_ctor_set(x_418, 1, x_408);
lean_ctor_set(x_418, 2, x_417);
lean_ctor_set(x_418, 3, x_409);
lean_ctor_set(x_418, 4, x_410);
lean_ctor_set(x_418, 5, x_411);
if (lean_is_scalar(x_251)) {
 x_419 = lean_alloc_ctor(1, 2, 0);
} else {
 x_419 = x_251;
 lean_ctor_set_tag(x_419, 1);
}
lean_ctor_set(x_419, 0, x_406);
lean_ctor_set(x_419, 1, x_418);
return x_419;
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_420 = lean_ctor_get(x_404, 2);
lean_inc(x_420);
x_421 = lean_ctor_get(x_403, 0);
lean_inc(x_421);
lean_dec(x_403);
x_422 = lean_ctor_get(x_404, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_404, 1);
lean_inc(x_423);
x_424 = lean_ctor_get(x_404, 3);
lean_inc(x_424);
x_425 = lean_ctor_get(x_404, 4);
lean_inc(x_425);
x_426 = lean_ctor_get(x_404, 5);
lean_inc(x_426);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 lean_ctor_release(x_404, 2);
 lean_ctor_release(x_404, 3);
 lean_ctor_release(x_404, 4);
 lean_ctor_release(x_404, 5);
 x_427 = x_404;
} else {
 lean_dec_ref(x_404);
 x_427 = lean_box(0);
}
x_428 = lean_ctor_get(x_420, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_420, 1);
lean_inc(x_429);
x_430 = lean_ctor_get(x_420, 3);
lean_inc(x_430);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 lean_ctor_release(x_420, 2);
 lean_ctor_release(x_420, 3);
 x_431 = x_420;
} else {
 lean_dec_ref(x_420);
 x_431 = lean_box(0);
}
if (lean_is_scalar(x_431)) {
 x_432 = lean_alloc_ctor(0, 4, 0);
} else {
 x_432 = x_431;
}
lean_ctor_set(x_432, 0, x_428);
lean_ctor_set(x_432, 1, x_429);
lean_ctor_set(x_432, 2, x_400);
lean_ctor_set(x_432, 3, x_430);
if (lean_is_scalar(x_427)) {
 x_433 = lean_alloc_ctor(0, 6, 0);
} else {
 x_433 = x_427;
}
lean_ctor_set(x_433, 0, x_422);
lean_ctor_set(x_433, 1, x_423);
lean_ctor_set(x_433, 2, x_432);
lean_ctor_set(x_433, 3, x_424);
lean_ctor_set(x_433, 4, x_425);
lean_ctor_set(x_433, 5, x_426);
if (lean_is_scalar(x_251)) {
 x_434 = lean_alloc_ctor(0, 2, 0);
} else {
 x_434 = x_251;
}
lean_ctor_set(x_434, 0, x_421);
lean_ctor_set(x_434, 1, x_433);
return x_434;
}
}
}
}
}
else
{
uint8_t x_455; 
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_455 = !lean_is_exclusive(x_244);
if (x_455 == 0)
{
return x_244;
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_456 = lean_ctor_get(x_244, 0);
x_457 = lean_ctor_get(x_244, 1);
lean_inc(x_457);
lean_inc(x_456);
lean_dec(x_244);
x_458 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_458, 0, x_456);
lean_ctor_set(x_458, 1, x_457);
return x_458;
}
}
}
}
}
else
{
uint8_t x_459; 
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_459 = !lean_is_exclusive(x_32);
if (x_459 == 0)
{
return x_32;
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_460 = lean_ctor_get(x_32, 0);
x_461 = lean_ctor_get(x_32, 1);
lean_inc(x_461);
lean_inc(x_460);
lean_dec(x_32);
x_462 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_462, 0, x_460);
lean_ctor_set(x_462, 1, x_461);
return x_462;
}
}
}
else
{
uint8_t x_463; 
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_463 = !lean_is_exclusive(x_28);
if (x_463 == 0)
{
return x_28;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_464 = lean_ctor_get(x_28, 0);
x_465 = lean_ctor_get(x_28, 1);
lean_inc(x_465);
lean_inc(x_464);
lean_dec(x_28);
x_466 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_466, 0, x_464);
lean_ctor_set(x_466, 1, x_465);
return x_466;
}
}
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_12 = l_Nat_foldMAux___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__1(x_1, x_2, x_2, x_11, x_8, x_9);
lean_dec(x_2);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l___private_Lean_Meta_FunInfo_4__collectDeps(x_1, x_3);
lean_dec(x_1);
x_16 = l___private_Lean_Meta_FunInfo_5__updateHasFwdDeps(x_14, x_15);
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
x_20 = l___private_Lean_Meta_FunInfo_4__collectDeps(x_1, x_3);
lean_dec(x_1);
x_21 = l___private_Lean_Meta_FunInfo_5__updateHasFwdDeps(x_18, x_20);
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
x_28 = l___private_Lean_Meta_Basic_4__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__3(x_4, x_5, x_6, x_1, x_2, x_7, x_8, x_9);
return x_28;
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5___lambda__1___boxed), 9, 6);
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_23);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_31 = x_24;
} else {
 lean_dec_ref(x_24);
 x_31 = lean_box(0);
}
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
lean_dec(x_25);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_10, x_33);
lean_dec(x_10);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_30, 2);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_90; uint8_t x_91; 
x_38 = lean_ctor_get(x_36, 2);
x_90 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_36, 2, x_90);
x_91 = !lean_is_exclusive(x_11);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_11, 2);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_32);
lean_ctor_set(x_93, 1, x_19);
x_94 = lean_array_push(x_92, x_93);
lean_ctor_set(x_11, 2, x_94);
x_95 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_34, x_11, x_30);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_96);
x_39 = x_98;
x_40 = x_97;
goto block_89;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_95, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_95, 1);
lean_inc(x_100);
lean_dec(x_95);
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_99);
x_39 = x_101;
x_40 = x_100;
goto block_89;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_102 = lean_ctor_get(x_11, 0);
x_103 = lean_ctor_get(x_11, 1);
x_104 = lean_ctor_get(x_11, 2);
x_105 = lean_ctor_get(x_11, 3);
x_106 = lean_ctor_get(x_11, 4);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_11);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_32);
lean_ctor_set(x_107, 1, x_19);
x_108 = lean_array_push(x_104, x_107);
x_109 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_109, 0, x_102);
lean_ctor_set(x_109, 1, x_103);
lean_ctor_set(x_109, 2, x_108);
lean_ctor_set(x_109, 3, x_105);
lean_ctor_set(x_109, 4, x_106);
x_110 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_34, x_109, x_30);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_111);
x_39 = x_113;
x_40 = x_112;
goto block_89;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_110, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_110, 1);
lean_inc(x_115);
lean_dec(x_110);
x_116 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_116, 0, x_114);
x_39 = x_116;
x_40 = x_115;
goto block_89;
}
}
block_89:
{
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_40, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
lean_dec(x_39);
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_40, 2);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_41, 2);
lean_dec(x_46);
lean_ctor_set(x_41, 2, x_38);
if (lean_is_scalar(x_31)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_31;
 lean_ctor_set_tag(x_47, 1);
}
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_40);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_41, 0);
x_49 = lean_ctor_get(x_41, 1);
x_50 = lean_ctor_get(x_41, 3);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_41);
x_51 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_38);
lean_ctor_set(x_51, 3, x_50);
lean_ctor_set(x_40, 2, x_51);
if (lean_is_scalar(x_31)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_31;
 lean_ctor_set_tag(x_52, 1);
}
lean_ctor_set(x_52, 0, x_42);
lean_ctor_set(x_52, 1, x_40);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_53 = lean_ctor_get(x_40, 0);
x_54 = lean_ctor_get(x_40, 1);
x_55 = lean_ctor_get(x_40, 3);
x_56 = lean_ctor_get(x_40, 4);
x_57 = lean_ctor_get(x_40, 5);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_40);
x_58 = lean_ctor_get(x_41, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_41, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_41, 3);
lean_inc(x_60);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 x_61 = x_41;
} else {
 lean_dec_ref(x_41);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 4, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_59);
lean_ctor_set(x_62, 2, x_38);
lean_ctor_set(x_62, 3, x_60);
x_63 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_63, 0, x_53);
lean_ctor_set(x_63, 1, x_54);
lean_ctor_set(x_63, 2, x_62);
lean_ctor_set(x_63, 3, x_55);
lean_ctor_set(x_63, 4, x_56);
lean_ctor_set(x_63, 5, x_57);
if (lean_is_scalar(x_31)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_31;
 lean_ctor_set_tag(x_64, 1);
}
lean_ctor_set(x_64, 0, x_42);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_40, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_39, 0);
lean_inc(x_66);
lean_dec(x_39);
x_67 = !lean_is_exclusive(x_40);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_40, 2);
lean_dec(x_68);
x_69 = !lean_is_exclusive(x_65);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_65, 2);
lean_dec(x_70);
lean_ctor_set(x_65, 2, x_38);
if (lean_is_scalar(x_31)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_31;
}
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_40);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_65, 0);
x_73 = lean_ctor_get(x_65, 1);
x_74 = lean_ctor_get(x_65, 3);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_65);
x_75 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
lean_ctor_set(x_75, 2, x_38);
lean_ctor_set(x_75, 3, x_74);
lean_ctor_set(x_40, 2, x_75);
if (lean_is_scalar(x_31)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_31;
}
lean_ctor_set(x_76, 0, x_66);
lean_ctor_set(x_76, 1, x_40);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_77 = lean_ctor_get(x_40, 0);
x_78 = lean_ctor_get(x_40, 1);
x_79 = lean_ctor_get(x_40, 3);
x_80 = lean_ctor_get(x_40, 4);
x_81 = lean_ctor_get(x_40, 5);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_40);
x_82 = lean_ctor_get(x_65, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_65, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_65, 3);
lean_inc(x_84);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 x_85 = x_65;
} else {
 lean_dec_ref(x_65);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(0, 4, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_82);
lean_ctor_set(x_86, 1, x_83);
lean_ctor_set(x_86, 2, x_38);
lean_ctor_set(x_86, 3, x_84);
x_87 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_87, 0, x_77);
lean_ctor_set(x_87, 1, x_78);
lean_ctor_set(x_87, 2, x_86);
lean_ctor_set(x_87, 3, x_79);
lean_ctor_set(x_87, 4, x_80);
lean_ctor_set(x_87, 5, x_81);
if (lean_is_scalar(x_31)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_31;
}
lean_ctor_set(x_88, 0, x_66);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_117 = lean_ctor_get(x_36, 0);
x_118 = lean_ctor_get(x_36, 1);
x_119 = lean_ctor_get(x_36, 2);
x_120 = lean_ctor_get(x_36, 3);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_36);
x_154 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_155 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_155, 0, x_117);
lean_ctor_set(x_155, 1, x_118);
lean_ctor_set(x_155, 2, x_154);
lean_ctor_set(x_155, 3, x_120);
lean_ctor_set(x_30, 2, x_155);
x_156 = lean_ctor_get(x_11, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_11, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_11, 2);
lean_inc(x_158);
x_159 = lean_ctor_get(x_11, 3);
lean_inc(x_159);
x_160 = lean_ctor_get(x_11, 4);
lean_inc(x_160);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 x_161 = x_11;
} else {
 lean_dec_ref(x_11);
 x_161 = lean_box(0);
}
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_32);
lean_ctor_set(x_162, 1, x_19);
x_163 = lean_array_push(x_158, x_162);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 5, 0);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_156);
lean_ctor_set(x_164, 1, x_157);
lean_ctor_set(x_164, 2, x_163);
lean_ctor_set(x_164, 3, x_159);
lean_ctor_set(x_164, 4, x_160);
x_165 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_34, x_164, x_30);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_168, 0, x_166);
x_121 = x_168;
x_122 = x_167;
goto block_153;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_165, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_165, 1);
lean_inc(x_170);
lean_dec(x_165);
x_171 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_171, 0, x_169);
x_121 = x_171;
x_122 = x_170;
goto block_153;
}
block_153:
{
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_123 = lean_ctor_get(x_122, 2);
lean_inc(x_123);
x_124 = lean_ctor_get(x_121, 0);
lean_inc(x_124);
lean_dec(x_121);
x_125 = lean_ctor_get(x_122, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_122, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_122, 3);
lean_inc(x_127);
x_128 = lean_ctor_get(x_122, 4);
lean_inc(x_128);
x_129 = lean_ctor_get(x_122, 5);
lean_inc(x_129);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 lean_ctor_release(x_122, 2);
 lean_ctor_release(x_122, 3);
 lean_ctor_release(x_122, 4);
 lean_ctor_release(x_122, 5);
 x_130 = x_122;
} else {
 lean_dec_ref(x_122);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_123, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_123, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_123, 3);
lean_inc(x_133);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 x_134 = x_123;
} else {
 lean_dec_ref(x_123);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(0, 4, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_131);
lean_ctor_set(x_135, 1, x_132);
lean_ctor_set(x_135, 2, x_119);
lean_ctor_set(x_135, 3, x_133);
if (lean_is_scalar(x_130)) {
 x_136 = lean_alloc_ctor(0, 6, 0);
} else {
 x_136 = x_130;
}
lean_ctor_set(x_136, 0, x_125);
lean_ctor_set(x_136, 1, x_126);
lean_ctor_set(x_136, 2, x_135);
lean_ctor_set(x_136, 3, x_127);
lean_ctor_set(x_136, 4, x_128);
lean_ctor_set(x_136, 5, x_129);
if (lean_is_scalar(x_31)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_31;
 lean_ctor_set_tag(x_137, 1);
}
lean_ctor_set(x_137, 0, x_124);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_138 = lean_ctor_get(x_122, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_121, 0);
lean_inc(x_139);
lean_dec(x_121);
x_140 = lean_ctor_get(x_122, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_122, 1);
lean_inc(x_141);
x_142 = lean_ctor_get(x_122, 3);
lean_inc(x_142);
x_143 = lean_ctor_get(x_122, 4);
lean_inc(x_143);
x_144 = lean_ctor_get(x_122, 5);
lean_inc(x_144);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 lean_ctor_release(x_122, 2);
 lean_ctor_release(x_122, 3);
 lean_ctor_release(x_122, 4);
 lean_ctor_release(x_122, 5);
 x_145 = x_122;
} else {
 lean_dec_ref(x_122);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_138, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_138, 1);
lean_inc(x_147);
x_148 = lean_ctor_get(x_138, 3);
lean_inc(x_148);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 lean_ctor_release(x_138, 2);
 lean_ctor_release(x_138, 3);
 x_149 = x_138;
} else {
 lean_dec_ref(x_138);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(0, 4, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_146);
lean_ctor_set(x_150, 1, x_147);
lean_ctor_set(x_150, 2, x_119);
lean_ctor_set(x_150, 3, x_148);
if (lean_is_scalar(x_145)) {
 x_151 = lean_alloc_ctor(0, 6, 0);
} else {
 x_151 = x_145;
}
lean_ctor_set(x_151, 0, x_140);
lean_ctor_set(x_151, 1, x_141);
lean_ctor_set(x_151, 2, x_150);
lean_ctor_set(x_151, 3, x_142);
lean_ctor_set(x_151, 4, x_143);
lean_ctor_set(x_151, 5, x_144);
if (lean_is_scalar(x_31)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_31;
}
lean_ctor_set(x_152, 0, x_139);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_172 = lean_ctor_get(x_30, 2);
x_173 = lean_ctor_get(x_30, 0);
x_174 = lean_ctor_get(x_30, 1);
x_175 = lean_ctor_get(x_30, 3);
x_176 = lean_ctor_get(x_30, 4);
x_177 = lean_ctor_get(x_30, 5);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_172);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_30);
x_178 = lean_ctor_get(x_172, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_172, 1);
lean_inc(x_179);
x_180 = lean_ctor_get(x_172, 2);
lean_inc(x_180);
x_181 = lean_ctor_get(x_172, 3);
lean_inc(x_181);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 lean_ctor_release(x_172, 2);
 lean_ctor_release(x_172, 3);
 x_182 = x_172;
} else {
 lean_dec_ref(x_172);
 x_182 = lean_box(0);
}
x_216 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_182)) {
 x_217 = lean_alloc_ctor(0, 4, 0);
} else {
 x_217 = x_182;
}
lean_ctor_set(x_217, 0, x_178);
lean_ctor_set(x_217, 1, x_179);
lean_ctor_set(x_217, 2, x_216);
lean_ctor_set(x_217, 3, x_181);
x_218 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_218, 0, x_173);
lean_ctor_set(x_218, 1, x_174);
lean_ctor_set(x_218, 2, x_217);
lean_ctor_set(x_218, 3, x_175);
lean_ctor_set(x_218, 4, x_176);
lean_ctor_set(x_218, 5, x_177);
x_219 = lean_ctor_get(x_11, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_11, 1);
lean_inc(x_220);
x_221 = lean_ctor_get(x_11, 2);
lean_inc(x_221);
x_222 = lean_ctor_get(x_11, 3);
lean_inc(x_222);
x_223 = lean_ctor_get(x_11, 4);
lean_inc(x_223);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 x_224 = x_11;
} else {
 lean_dec_ref(x_11);
 x_224 = lean_box(0);
}
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_32);
lean_ctor_set(x_225, 1, x_19);
x_226 = lean_array_push(x_221, x_225);
if (lean_is_scalar(x_224)) {
 x_227 = lean_alloc_ctor(0, 5, 0);
} else {
 x_227 = x_224;
}
lean_ctor_set(x_227, 0, x_219);
lean_ctor_set(x_227, 1, x_220);
lean_ctor_set(x_227, 2, x_226);
lean_ctor_set(x_227, 3, x_222);
lean_ctor_set(x_227, 4, x_223);
x_228 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_34, x_227, x_218);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
x_231 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_231, 0, x_229);
x_183 = x_231;
x_184 = x_230;
goto block_215;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_228, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_228, 1);
lean_inc(x_233);
lean_dec(x_228);
x_234 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_234, 0, x_232);
x_183 = x_234;
x_184 = x_233;
goto block_215;
}
block_215:
{
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_185 = lean_ctor_get(x_184, 2);
lean_inc(x_185);
x_186 = lean_ctor_get(x_183, 0);
lean_inc(x_186);
lean_dec(x_183);
x_187 = lean_ctor_get(x_184, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_184, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_184, 3);
lean_inc(x_189);
x_190 = lean_ctor_get(x_184, 4);
lean_inc(x_190);
x_191 = lean_ctor_get(x_184, 5);
lean_inc(x_191);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 lean_ctor_release(x_184, 2);
 lean_ctor_release(x_184, 3);
 lean_ctor_release(x_184, 4);
 lean_ctor_release(x_184, 5);
 x_192 = x_184;
} else {
 lean_dec_ref(x_184);
 x_192 = lean_box(0);
}
x_193 = lean_ctor_get(x_185, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_185, 1);
lean_inc(x_194);
x_195 = lean_ctor_get(x_185, 3);
lean_inc(x_195);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 lean_ctor_release(x_185, 2);
 lean_ctor_release(x_185, 3);
 x_196 = x_185;
} else {
 lean_dec_ref(x_185);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(0, 4, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_193);
lean_ctor_set(x_197, 1, x_194);
lean_ctor_set(x_197, 2, x_180);
lean_ctor_set(x_197, 3, x_195);
if (lean_is_scalar(x_192)) {
 x_198 = lean_alloc_ctor(0, 6, 0);
} else {
 x_198 = x_192;
}
lean_ctor_set(x_198, 0, x_187);
lean_ctor_set(x_198, 1, x_188);
lean_ctor_set(x_198, 2, x_197);
lean_ctor_set(x_198, 3, x_189);
lean_ctor_set(x_198, 4, x_190);
lean_ctor_set(x_198, 5, x_191);
if (lean_is_scalar(x_31)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_31;
 lean_ctor_set_tag(x_199, 1);
}
lean_ctor_set(x_199, 0, x_186);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_200 = lean_ctor_get(x_184, 2);
lean_inc(x_200);
x_201 = lean_ctor_get(x_183, 0);
lean_inc(x_201);
lean_dec(x_183);
x_202 = lean_ctor_get(x_184, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_184, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_184, 3);
lean_inc(x_204);
x_205 = lean_ctor_get(x_184, 4);
lean_inc(x_205);
x_206 = lean_ctor_get(x_184, 5);
lean_inc(x_206);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 lean_ctor_release(x_184, 2);
 lean_ctor_release(x_184, 3);
 lean_ctor_release(x_184, 4);
 lean_ctor_release(x_184, 5);
 x_207 = x_184;
} else {
 lean_dec_ref(x_184);
 x_207 = lean_box(0);
}
x_208 = lean_ctor_get(x_200, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_200, 1);
lean_inc(x_209);
x_210 = lean_ctor_get(x_200, 3);
lean_inc(x_210);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 lean_ctor_release(x_200, 2);
 lean_ctor_release(x_200, 3);
 x_211 = x_200;
} else {
 lean_dec_ref(x_200);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(0, 4, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_208);
lean_ctor_set(x_212, 1, x_209);
lean_ctor_set(x_212, 2, x_180);
lean_ctor_set(x_212, 3, x_210);
if (lean_is_scalar(x_207)) {
 x_213 = lean_alloc_ctor(0, 6, 0);
} else {
 x_213 = x_207;
}
lean_ctor_set(x_213, 0, x_202);
lean_ctor_set(x_213, 1, x_203);
lean_ctor_set(x_213, 2, x_212);
lean_ctor_set(x_213, 3, x_204);
lean_ctor_set(x_213, 4, x_205);
lean_ctor_set(x_213, 5, x_206);
if (lean_is_scalar(x_31)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_31;
}
lean_ctor_set(x_214, 0, x_201);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
}
}
default: 
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_24, 1);
lean_inc(x_235);
lean_dec(x_24);
lean_inc(x_11);
x_236 = l_Lean_Meta_isClassExpensive___main(x_23, x_11, x_235);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_19);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec(x_236);
x_239 = lean_unsigned_to_nat(1u);
x_240 = lean_nat_add(x_10, x_239);
lean_dec(x_10);
x_10 = x_240;
x_12 = x_238;
goto _start;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_242 = lean_ctor_get(x_236, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_243 = x_236;
} else {
 lean_dec_ref(x_236);
 x_243 = lean_box(0);
}
x_244 = lean_ctor_get(x_237, 0);
lean_inc(x_244);
lean_dec(x_237);
x_245 = lean_unsigned_to_nat(1u);
x_246 = lean_nat_add(x_10, x_245);
lean_dec(x_10);
x_247 = !lean_is_exclusive(x_242);
if (x_247 == 0)
{
lean_object* x_248; uint8_t x_249; 
x_248 = lean_ctor_get(x_242, 2);
x_249 = !lean_is_exclusive(x_248);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_302; uint8_t x_303; 
x_250 = lean_ctor_get(x_248, 2);
x_302 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_248, 2, x_302);
x_303 = !lean_is_exclusive(x_11);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_304 = lean_ctor_get(x_11, 2);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_244);
lean_ctor_set(x_305, 1, x_19);
x_306 = lean_array_push(x_304, x_305);
lean_ctor_set(x_11, 2, x_306);
x_307 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_246, x_11, x_242);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec(x_307);
x_310 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_310, 0, x_308);
x_251 = x_310;
x_252 = x_309;
goto block_301;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_307, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_307, 1);
lean_inc(x_312);
lean_dec(x_307);
x_313 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_313, 0, x_311);
x_251 = x_313;
x_252 = x_312;
goto block_301;
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_314 = lean_ctor_get(x_11, 0);
x_315 = lean_ctor_get(x_11, 1);
x_316 = lean_ctor_get(x_11, 2);
x_317 = lean_ctor_get(x_11, 3);
x_318 = lean_ctor_get(x_11, 4);
lean_inc(x_318);
lean_inc(x_317);
lean_inc(x_316);
lean_inc(x_315);
lean_inc(x_314);
lean_dec(x_11);
x_319 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_319, 0, x_244);
lean_ctor_set(x_319, 1, x_19);
x_320 = lean_array_push(x_316, x_319);
x_321 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_321, 0, x_314);
lean_ctor_set(x_321, 1, x_315);
lean_ctor_set(x_321, 2, x_320);
lean_ctor_set(x_321, 3, x_317);
lean_ctor_set(x_321, 4, x_318);
x_322 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_246, x_321, x_242);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_322, 1);
lean_inc(x_324);
lean_dec(x_322);
x_325 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_325, 0, x_323);
x_251 = x_325;
x_252 = x_324;
goto block_301;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_322, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_322, 1);
lean_inc(x_327);
lean_dec(x_322);
x_328 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_328, 0, x_326);
x_251 = x_328;
x_252 = x_327;
goto block_301;
}
}
block_301:
{
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_253; lean_object* x_254; uint8_t x_255; 
x_253 = lean_ctor_get(x_252, 2);
lean_inc(x_253);
x_254 = lean_ctor_get(x_251, 0);
lean_inc(x_254);
lean_dec(x_251);
x_255 = !lean_is_exclusive(x_252);
if (x_255 == 0)
{
lean_object* x_256; uint8_t x_257; 
x_256 = lean_ctor_get(x_252, 2);
lean_dec(x_256);
x_257 = !lean_is_exclusive(x_253);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; 
x_258 = lean_ctor_get(x_253, 2);
lean_dec(x_258);
lean_ctor_set(x_253, 2, x_250);
if (lean_is_scalar(x_243)) {
 x_259 = lean_alloc_ctor(1, 2, 0);
} else {
 x_259 = x_243;
 lean_ctor_set_tag(x_259, 1);
}
lean_ctor_set(x_259, 0, x_254);
lean_ctor_set(x_259, 1, x_252);
return x_259;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_260 = lean_ctor_get(x_253, 0);
x_261 = lean_ctor_get(x_253, 1);
x_262 = lean_ctor_get(x_253, 3);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_253);
x_263 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_263, 0, x_260);
lean_ctor_set(x_263, 1, x_261);
lean_ctor_set(x_263, 2, x_250);
lean_ctor_set(x_263, 3, x_262);
lean_ctor_set(x_252, 2, x_263);
if (lean_is_scalar(x_243)) {
 x_264 = lean_alloc_ctor(1, 2, 0);
} else {
 x_264 = x_243;
 lean_ctor_set_tag(x_264, 1);
}
lean_ctor_set(x_264, 0, x_254);
lean_ctor_set(x_264, 1, x_252);
return x_264;
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_265 = lean_ctor_get(x_252, 0);
x_266 = lean_ctor_get(x_252, 1);
x_267 = lean_ctor_get(x_252, 3);
x_268 = lean_ctor_get(x_252, 4);
x_269 = lean_ctor_get(x_252, 5);
lean_inc(x_269);
lean_inc(x_268);
lean_inc(x_267);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_252);
x_270 = lean_ctor_get(x_253, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_253, 1);
lean_inc(x_271);
x_272 = lean_ctor_get(x_253, 3);
lean_inc(x_272);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 lean_ctor_release(x_253, 2);
 lean_ctor_release(x_253, 3);
 x_273 = x_253;
} else {
 lean_dec_ref(x_253);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(0, 4, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_270);
lean_ctor_set(x_274, 1, x_271);
lean_ctor_set(x_274, 2, x_250);
lean_ctor_set(x_274, 3, x_272);
x_275 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_275, 0, x_265);
lean_ctor_set(x_275, 1, x_266);
lean_ctor_set(x_275, 2, x_274);
lean_ctor_set(x_275, 3, x_267);
lean_ctor_set(x_275, 4, x_268);
lean_ctor_set(x_275, 5, x_269);
if (lean_is_scalar(x_243)) {
 x_276 = lean_alloc_ctor(1, 2, 0);
} else {
 x_276 = x_243;
 lean_ctor_set_tag(x_276, 1);
}
lean_ctor_set(x_276, 0, x_254);
lean_ctor_set(x_276, 1, x_275);
return x_276;
}
}
else
{
lean_object* x_277; lean_object* x_278; uint8_t x_279; 
x_277 = lean_ctor_get(x_252, 2);
lean_inc(x_277);
x_278 = lean_ctor_get(x_251, 0);
lean_inc(x_278);
lean_dec(x_251);
x_279 = !lean_is_exclusive(x_252);
if (x_279 == 0)
{
lean_object* x_280; uint8_t x_281; 
x_280 = lean_ctor_get(x_252, 2);
lean_dec(x_280);
x_281 = !lean_is_exclusive(x_277);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; 
x_282 = lean_ctor_get(x_277, 2);
lean_dec(x_282);
lean_ctor_set(x_277, 2, x_250);
if (lean_is_scalar(x_243)) {
 x_283 = lean_alloc_ctor(0, 2, 0);
} else {
 x_283 = x_243;
}
lean_ctor_set(x_283, 0, x_278);
lean_ctor_set(x_283, 1, x_252);
return x_283;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_284 = lean_ctor_get(x_277, 0);
x_285 = lean_ctor_get(x_277, 1);
x_286 = lean_ctor_get(x_277, 3);
lean_inc(x_286);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_277);
x_287 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_287, 0, x_284);
lean_ctor_set(x_287, 1, x_285);
lean_ctor_set(x_287, 2, x_250);
lean_ctor_set(x_287, 3, x_286);
lean_ctor_set(x_252, 2, x_287);
if (lean_is_scalar(x_243)) {
 x_288 = lean_alloc_ctor(0, 2, 0);
} else {
 x_288 = x_243;
}
lean_ctor_set(x_288, 0, x_278);
lean_ctor_set(x_288, 1, x_252);
return x_288;
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_289 = lean_ctor_get(x_252, 0);
x_290 = lean_ctor_get(x_252, 1);
x_291 = lean_ctor_get(x_252, 3);
x_292 = lean_ctor_get(x_252, 4);
x_293 = lean_ctor_get(x_252, 5);
lean_inc(x_293);
lean_inc(x_292);
lean_inc(x_291);
lean_inc(x_290);
lean_inc(x_289);
lean_dec(x_252);
x_294 = lean_ctor_get(x_277, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_277, 1);
lean_inc(x_295);
x_296 = lean_ctor_get(x_277, 3);
lean_inc(x_296);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 lean_ctor_release(x_277, 2);
 lean_ctor_release(x_277, 3);
 x_297 = x_277;
} else {
 lean_dec_ref(x_277);
 x_297 = lean_box(0);
}
if (lean_is_scalar(x_297)) {
 x_298 = lean_alloc_ctor(0, 4, 0);
} else {
 x_298 = x_297;
}
lean_ctor_set(x_298, 0, x_294);
lean_ctor_set(x_298, 1, x_295);
lean_ctor_set(x_298, 2, x_250);
lean_ctor_set(x_298, 3, x_296);
x_299 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_299, 0, x_289);
lean_ctor_set(x_299, 1, x_290);
lean_ctor_set(x_299, 2, x_298);
lean_ctor_set(x_299, 3, x_291);
lean_ctor_set(x_299, 4, x_292);
lean_ctor_set(x_299, 5, x_293);
if (lean_is_scalar(x_243)) {
 x_300 = lean_alloc_ctor(0, 2, 0);
} else {
 x_300 = x_243;
}
lean_ctor_set(x_300, 0, x_278);
lean_ctor_set(x_300, 1, x_299);
return x_300;
}
}
}
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_329 = lean_ctor_get(x_248, 0);
x_330 = lean_ctor_get(x_248, 1);
x_331 = lean_ctor_get(x_248, 2);
x_332 = lean_ctor_get(x_248, 3);
lean_inc(x_332);
lean_inc(x_331);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_248);
x_366 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_367 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_367, 0, x_329);
lean_ctor_set(x_367, 1, x_330);
lean_ctor_set(x_367, 2, x_366);
lean_ctor_set(x_367, 3, x_332);
lean_ctor_set(x_242, 2, x_367);
x_368 = lean_ctor_get(x_11, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_11, 1);
lean_inc(x_369);
x_370 = lean_ctor_get(x_11, 2);
lean_inc(x_370);
x_371 = lean_ctor_get(x_11, 3);
lean_inc(x_371);
x_372 = lean_ctor_get(x_11, 4);
lean_inc(x_372);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 x_373 = x_11;
} else {
 lean_dec_ref(x_11);
 x_373 = lean_box(0);
}
x_374 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_374, 0, x_244);
lean_ctor_set(x_374, 1, x_19);
x_375 = lean_array_push(x_370, x_374);
if (lean_is_scalar(x_373)) {
 x_376 = lean_alloc_ctor(0, 5, 0);
} else {
 x_376 = x_373;
}
lean_ctor_set(x_376, 0, x_368);
lean_ctor_set(x_376, 1, x_369);
lean_ctor_set(x_376, 2, x_375);
lean_ctor_set(x_376, 3, x_371);
lean_ctor_set(x_376, 4, x_372);
x_377 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_246, x_376, x_242);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_377, 1);
lean_inc(x_379);
lean_dec(x_377);
x_380 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_380, 0, x_378);
x_333 = x_380;
x_334 = x_379;
goto block_365;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_381 = lean_ctor_get(x_377, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_377, 1);
lean_inc(x_382);
lean_dec(x_377);
x_383 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_383, 0, x_381);
x_333 = x_383;
x_334 = x_382;
goto block_365;
}
block_365:
{
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_335 = lean_ctor_get(x_334, 2);
lean_inc(x_335);
x_336 = lean_ctor_get(x_333, 0);
lean_inc(x_336);
lean_dec(x_333);
x_337 = lean_ctor_get(x_334, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_334, 1);
lean_inc(x_338);
x_339 = lean_ctor_get(x_334, 3);
lean_inc(x_339);
x_340 = lean_ctor_get(x_334, 4);
lean_inc(x_340);
x_341 = lean_ctor_get(x_334, 5);
lean_inc(x_341);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 lean_ctor_release(x_334, 2);
 lean_ctor_release(x_334, 3);
 lean_ctor_release(x_334, 4);
 lean_ctor_release(x_334, 5);
 x_342 = x_334;
} else {
 lean_dec_ref(x_334);
 x_342 = lean_box(0);
}
x_343 = lean_ctor_get(x_335, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_335, 1);
lean_inc(x_344);
x_345 = lean_ctor_get(x_335, 3);
lean_inc(x_345);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 lean_ctor_release(x_335, 2);
 lean_ctor_release(x_335, 3);
 x_346 = x_335;
} else {
 lean_dec_ref(x_335);
 x_346 = lean_box(0);
}
if (lean_is_scalar(x_346)) {
 x_347 = lean_alloc_ctor(0, 4, 0);
} else {
 x_347 = x_346;
}
lean_ctor_set(x_347, 0, x_343);
lean_ctor_set(x_347, 1, x_344);
lean_ctor_set(x_347, 2, x_331);
lean_ctor_set(x_347, 3, x_345);
if (lean_is_scalar(x_342)) {
 x_348 = lean_alloc_ctor(0, 6, 0);
} else {
 x_348 = x_342;
}
lean_ctor_set(x_348, 0, x_337);
lean_ctor_set(x_348, 1, x_338);
lean_ctor_set(x_348, 2, x_347);
lean_ctor_set(x_348, 3, x_339);
lean_ctor_set(x_348, 4, x_340);
lean_ctor_set(x_348, 5, x_341);
if (lean_is_scalar(x_243)) {
 x_349 = lean_alloc_ctor(1, 2, 0);
} else {
 x_349 = x_243;
 lean_ctor_set_tag(x_349, 1);
}
lean_ctor_set(x_349, 0, x_336);
lean_ctor_set(x_349, 1, x_348);
return x_349;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_350 = lean_ctor_get(x_334, 2);
lean_inc(x_350);
x_351 = lean_ctor_get(x_333, 0);
lean_inc(x_351);
lean_dec(x_333);
x_352 = lean_ctor_get(x_334, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_334, 1);
lean_inc(x_353);
x_354 = lean_ctor_get(x_334, 3);
lean_inc(x_354);
x_355 = lean_ctor_get(x_334, 4);
lean_inc(x_355);
x_356 = lean_ctor_get(x_334, 5);
lean_inc(x_356);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 lean_ctor_release(x_334, 2);
 lean_ctor_release(x_334, 3);
 lean_ctor_release(x_334, 4);
 lean_ctor_release(x_334, 5);
 x_357 = x_334;
} else {
 lean_dec_ref(x_334);
 x_357 = lean_box(0);
}
x_358 = lean_ctor_get(x_350, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_350, 1);
lean_inc(x_359);
x_360 = lean_ctor_get(x_350, 3);
lean_inc(x_360);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_361 = x_350;
} else {
 lean_dec_ref(x_350);
 x_361 = lean_box(0);
}
if (lean_is_scalar(x_361)) {
 x_362 = lean_alloc_ctor(0, 4, 0);
} else {
 x_362 = x_361;
}
lean_ctor_set(x_362, 0, x_358);
lean_ctor_set(x_362, 1, x_359);
lean_ctor_set(x_362, 2, x_331);
lean_ctor_set(x_362, 3, x_360);
if (lean_is_scalar(x_357)) {
 x_363 = lean_alloc_ctor(0, 6, 0);
} else {
 x_363 = x_357;
}
lean_ctor_set(x_363, 0, x_352);
lean_ctor_set(x_363, 1, x_353);
lean_ctor_set(x_363, 2, x_362);
lean_ctor_set(x_363, 3, x_354);
lean_ctor_set(x_363, 4, x_355);
lean_ctor_set(x_363, 5, x_356);
if (lean_is_scalar(x_243)) {
 x_364 = lean_alloc_ctor(0, 2, 0);
} else {
 x_364 = x_243;
}
lean_ctor_set(x_364, 0, x_351);
lean_ctor_set(x_364, 1, x_363);
return x_364;
}
}
}
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_384 = lean_ctor_get(x_242, 2);
x_385 = lean_ctor_get(x_242, 0);
x_386 = lean_ctor_get(x_242, 1);
x_387 = lean_ctor_get(x_242, 3);
x_388 = lean_ctor_get(x_242, 4);
x_389 = lean_ctor_get(x_242, 5);
lean_inc(x_389);
lean_inc(x_388);
lean_inc(x_387);
lean_inc(x_384);
lean_inc(x_386);
lean_inc(x_385);
lean_dec(x_242);
x_390 = lean_ctor_get(x_384, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_384, 1);
lean_inc(x_391);
x_392 = lean_ctor_get(x_384, 2);
lean_inc(x_392);
x_393 = lean_ctor_get(x_384, 3);
lean_inc(x_393);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 lean_ctor_release(x_384, 1);
 lean_ctor_release(x_384, 2);
 lean_ctor_release(x_384, 3);
 x_394 = x_384;
} else {
 lean_dec_ref(x_384);
 x_394 = lean_box(0);
}
x_428 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_394)) {
 x_429 = lean_alloc_ctor(0, 4, 0);
} else {
 x_429 = x_394;
}
lean_ctor_set(x_429, 0, x_390);
lean_ctor_set(x_429, 1, x_391);
lean_ctor_set(x_429, 2, x_428);
lean_ctor_set(x_429, 3, x_393);
x_430 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_430, 0, x_385);
lean_ctor_set(x_430, 1, x_386);
lean_ctor_set(x_430, 2, x_429);
lean_ctor_set(x_430, 3, x_387);
lean_ctor_set(x_430, 4, x_388);
lean_ctor_set(x_430, 5, x_389);
x_431 = lean_ctor_get(x_11, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_11, 1);
lean_inc(x_432);
x_433 = lean_ctor_get(x_11, 2);
lean_inc(x_433);
x_434 = lean_ctor_get(x_11, 3);
lean_inc(x_434);
x_435 = lean_ctor_get(x_11, 4);
lean_inc(x_435);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 x_436 = x_11;
} else {
 lean_dec_ref(x_11);
 x_436 = lean_box(0);
}
x_437 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_437, 0, x_244);
lean_ctor_set(x_437, 1, x_19);
x_438 = lean_array_push(x_433, x_437);
if (lean_is_scalar(x_436)) {
 x_439 = lean_alloc_ctor(0, 5, 0);
} else {
 x_439 = x_436;
}
lean_ctor_set(x_439, 0, x_431);
lean_ctor_set(x_439, 1, x_432);
lean_ctor_set(x_439, 2, x_438);
lean_ctor_set(x_439, 3, x_434);
lean_ctor_set(x_439, 4, x_435);
x_440 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_246, x_439, x_430);
if (lean_obj_tag(x_440) == 0)
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_440, 1);
lean_inc(x_442);
lean_dec(x_440);
x_443 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_443, 0, x_441);
x_395 = x_443;
x_396 = x_442;
goto block_427;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_444 = lean_ctor_get(x_440, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_440, 1);
lean_inc(x_445);
lean_dec(x_440);
x_446 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_446, 0, x_444);
x_395 = x_446;
x_396 = x_445;
goto block_427;
}
block_427:
{
if (lean_obj_tag(x_395) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_397 = lean_ctor_get(x_396, 2);
lean_inc(x_397);
x_398 = lean_ctor_get(x_395, 0);
lean_inc(x_398);
lean_dec(x_395);
x_399 = lean_ctor_get(x_396, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_396, 1);
lean_inc(x_400);
x_401 = lean_ctor_get(x_396, 3);
lean_inc(x_401);
x_402 = lean_ctor_get(x_396, 4);
lean_inc(x_402);
x_403 = lean_ctor_get(x_396, 5);
lean_inc(x_403);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 lean_ctor_release(x_396, 2);
 lean_ctor_release(x_396, 3);
 lean_ctor_release(x_396, 4);
 lean_ctor_release(x_396, 5);
 x_404 = x_396;
} else {
 lean_dec_ref(x_396);
 x_404 = lean_box(0);
}
x_405 = lean_ctor_get(x_397, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_397, 1);
lean_inc(x_406);
x_407 = lean_ctor_get(x_397, 3);
lean_inc(x_407);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 lean_ctor_release(x_397, 2);
 lean_ctor_release(x_397, 3);
 x_408 = x_397;
} else {
 lean_dec_ref(x_397);
 x_408 = lean_box(0);
}
if (lean_is_scalar(x_408)) {
 x_409 = lean_alloc_ctor(0, 4, 0);
} else {
 x_409 = x_408;
}
lean_ctor_set(x_409, 0, x_405);
lean_ctor_set(x_409, 1, x_406);
lean_ctor_set(x_409, 2, x_392);
lean_ctor_set(x_409, 3, x_407);
if (lean_is_scalar(x_404)) {
 x_410 = lean_alloc_ctor(0, 6, 0);
} else {
 x_410 = x_404;
}
lean_ctor_set(x_410, 0, x_399);
lean_ctor_set(x_410, 1, x_400);
lean_ctor_set(x_410, 2, x_409);
lean_ctor_set(x_410, 3, x_401);
lean_ctor_set(x_410, 4, x_402);
lean_ctor_set(x_410, 5, x_403);
if (lean_is_scalar(x_243)) {
 x_411 = lean_alloc_ctor(1, 2, 0);
} else {
 x_411 = x_243;
 lean_ctor_set_tag(x_411, 1);
}
lean_ctor_set(x_411, 0, x_398);
lean_ctor_set(x_411, 1, x_410);
return x_411;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_412 = lean_ctor_get(x_396, 2);
lean_inc(x_412);
x_413 = lean_ctor_get(x_395, 0);
lean_inc(x_413);
lean_dec(x_395);
x_414 = lean_ctor_get(x_396, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_396, 1);
lean_inc(x_415);
x_416 = lean_ctor_get(x_396, 3);
lean_inc(x_416);
x_417 = lean_ctor_get(x_396, 4);
lean_inc(x_417);
x_418 = lean_ctor_get(x_396, 5);
lean_inc(x_418);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 lean_ctor_release(x_396, 2);
 lean_ctor_release(x_396, 3);
 lean_ctor_release(x_396, 4);
 lean_ctor_release(x_396, 5);
 x_419 = x_396;
} else {
 lean_dec_ref(x_396);
 x_419 = lean_box(0);
}
x_420 = lean_ctor_get(x_412, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_412, 1);
lean_inc(x_421);
x_422 = lean_ctor_get(x_412, 3);
lean_inc(x_422);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 lean_ctor_release(x_412, 1);
 lean_ctor_release(x_412, 2);
 lean_ctor_release(x_412, 3);
 x_423 = x_412;
} else {
 lean_dec_ref(x_412);
 x_423 = lean_box(0);
}
if (lean_is_scalar(x_423)) {
 x_424 = lean_alloc_ctor(0, 4, 0);
} else {
 x_424 = x_423;
}
lean_ctor_set(x_424, 0, x_420);
lean_ctor_set(x_424, 1, x_421);
lean_ctor_set(x_424, 2, x_392);
lean_ctor_set(x_424, 3, x_422);
if (lean_is_scalar(x_419)) {
 x_425 = lean_alloc_ctor(0, 6, 0);
} else {
 x_425 = x_419;
}
lean_ctor_set(x_425, 0, x_414);
lean_ctor_set(x_425, 1, x_415);
lean_ctor_set(x_425, 2, x_424);
lean_ctor_set(x_425, 3, x_416);
lean_ctor_set(x_425, 4, x_417);
lean_ctor_set(x_425, 5, x_418);
if (lean_is_scalar(x_243)) {
 x_426 = lean_alloc_ctor(0, 2, 0);
} else {
 x_426 = x_243;
}
lean_ctor_set(x_426, 0, x_413);
lean_ctor_set(x_426, 1, x_425);
return x_426;
}
}
}
}
}
else
{
uint8_t x_447; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_447 = !lean_is_exclusive(x_236);
if (x_447 == 0)
{
return x_236;
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_448 = lean_ctor_get(x_236, 0);
x_449 = lean_ctor_get(x_236, 1);
lean_inc(x_449);
lean_inc(x_448);
lean_dec(x_236);
x_450 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_449);
return x_450;
}
}
}
}
}
else
{
uint8_t x_451; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_451 = !lean_is_exclusive(x_24);
if (x_451 == 0)
{
return x_24;
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_452 = lean_ctor_get(x_24, 0);
x_453 = lean_ctor_get(x_24, 1);
lean_inc(x_453);
lean_inc(x_452);
lean_dec(x_24);
x_454 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_454, 0, x_452);
lean_ctor_set(x_454, 1, x_453);
return x_454;
}
}
}
else
{
uint8_t x_455; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_455 = !lean_is_exclusive(x_20);
if (x_455 == 0)
{
return x_20;
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_456 = lean_ctor_get(x_20, 0);
x_457 = lean_ctor_get(x_20, 1);
lean_inc(x_457);
lean_inc(x_456);
lean_dec(x_20);
x_458 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_458, 0, x_456);
lean_ctor_set(x_458, 1, x_457);
return x_458;
}
}
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = l_Nat_foldMAux___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__1(x_1, x_2, x_2, x_10, x_6, x_7);
lean_dec(x_2);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l___private_Lean_Meta_FunInfo_4__collectDeps(x_1, x_3);
x_15 = l___private_Lean_Meta_FunInfo_5__updateHasFwdDeps(x_13, x_14);
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
x_19 = l___private_Lean_Meta_FunInfo_4__collectDeps(x_1, x_3);
x_20 = l___private_Lean_Meta_FunInfo_5__updateHasFwdDeps(x_17, x_19);
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
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_31);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_39 = x_32;
} else {
 lean_dec_ref(x_32);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_33, 0);
lean_inc(x_40);
lean_dec(x_33);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_5, x_41);
lean_dec(x_5);
x_43 = !lean_is_exclusive(x_38);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_38, 2);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_98; uint8_t x_99; 
x_46 = lean_ctor_get(x_44, 2);
x_98 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_44, 2, x_98);
x_99 = !lean_is_exclusive(x_6);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_6, 2);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_40);
lean_ctor_set(x_101, 1, x_27);
x_102 = lean_array_push(x_100, x_101);
lean_ctor_set(x_6, 2, x_102);
x_103 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6(x_1, x_2, x_3, x_4, x_42, x_6, x_38);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_104);
x_47 = x_106;
x_48 = x_105;
goto block_97;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_103, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_103, 1);
lean_inc(x_108);
lean_dec(x_103);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_107);
x_47 = x_109;
x_48 = x_108;
goto block_97;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_110 = lean_ctor_get(x_6, 0);
x_111 = lean_ctor_get(x_6, 1);
x_112 = lean_ctor_get(x_6, 2);
x_113 = lean_ctor_get(x_6, 3);
x_114 = lean_ctor_get(x_6, 4);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_6);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_40);
lean_ctor_set(x_115, 1, x_27);
x_116 = lean_array_push(x_112, x_115);
x_117 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_117, 0, x_110);
lean_ctor_set(x_117, 1, x_111);
lean_ctor_set(x_117, 2, x_116);
lean_ctor_set(x_117, 3, x_113);
lean_ctor_set(x_117, 4, x_114);
x_118 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6(x_1, x_2, x_3, x_4, x_42, x_117, x_38);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_119);
x_47 = x_121;
x_48 = x_120;
goto block_97;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_118, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_118, 1);
lean_inc(x_123);
lean_dec(x_118);
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_122);
x_47 = x_124;
x_48 = x_123;
goto block_97;
}
}
block_97:
{
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_48, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec(x_47);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_48, 2);
lean_dec(x_52);
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_49, 2);
lean_dec(x_54);
lean_ctor_set(x_49, 2, x_46);
if (lean_is_scalar(x_39)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_39;
 lean_ctor_set_tag(x_55, 1);
}
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_48);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_49, 0);
x_57 = lean_ctor_get(x_49, 1);
x_58 = lean_ctor_get(x_49, 3);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_49);
x_59 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_59, 2, x_46);
lean_ctor_set(x_59, 3, x_58);
lean_ctor_set(x_48, 2, x_59);
if (lean_is_scalar(x_39)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_39;
 lean_ctor_set_tag(x_60, 1);
}
lean_ctor_set(x_60, 0, x_50);
lean_ctor_set(x_60, 1, x_48);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_61 = lean_ctor_get(x_48, 0);
x_62 = lean_ctor_get(x_48, 1);
x_63 = lean_ctor_get(x_48, 3);
x_64 = lean_ctor_get(x_48, 4);
x_65 = lean_ctor_get(x_48, 5);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_48);
x_66 = lean_ctor_get(x_49, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_49, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_49, 3);
lean_inc(x_68);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 lean_ctor_release(x_49, 2);
 lean_ctor_release(x_49, 3);
 x_69 = x_49;
} else {
 lean_dec_ref(x_49);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 4, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_67);
lean_ctor_set(x_70, 2, x_46);
lean_ctor_set(x_70, 3, x_68);
x_71 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_71, 0, x_61);
lean_ctor_set(x_71, 1, x_62);
lean_ctor_set(x_71, 2, x_70);
lean_ctor_set(x_71, 3, x_63);
lean_ctor_set(x_71, 4, x_64);
lean_ctor_set(x_71, 5, x_65);
if (lean_is_scalar(x_39)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_39;
 lean_ctor_set_tag(x_72, 1);
}
lean_ctor_set(x_72, 0, x_50);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = lean_ctor_get(x_48, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_47, 0);
lean_inc(x_74);
lean_dec(x_47);
x_75 = !lean_is_exclusive(x_48);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_48, 2);
lean_dec(x_76);
x_77 = !lean_is_exclusive(x_73);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_73, 2);
lean_dec(x_78);
lean_ctor_set(x_73, 2, x_46);
if (lean_is_scalar(x_39)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_39;
}
lean_ctor_set(x_79, 0, x_74);
lean_ctor_set(x_79, 1, x_48);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_73, 0);
x_81 = lean_ctor_get(x_73, 1);
x_82 = lean_ctor_get(x_73, 3);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_73);
x_83 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
lean_ctor_set(x_83, 2, x_46);
lean_ctor_set(x_83, 3, x_82);
lean_ctor_set(x_48, 2, x_83);
if (lean_is_scalar(x_39)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_39;
}
lean_ctor_set(x_84, 0, x_74);
lean_ctor_set(x_84, 1, x_48);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_85 = lean_ctor_get(x_48, 0);
x_86 = lean_ctor_get(x_48, 1);
x_87 = lean_ctor_get(x_48, 3);
x_88 = lean_ctor_get(x_48, 4);
x_89 = lean_ctor_get(x_48, 5);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_48);
x_90 = lean_ctor_get(x_73, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_73, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_73, 3);
lean_inc(x_92);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 lean_ctor_release(x_73, 3);
 x_93 = x_73;
} else {
 lean_dec_ref(x_73);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 4, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_90);
lean_ctor_set(x_94, 1, x_91);
lean_ctor_set(x_94, 2, x_46);
lean_ctor_set(x_94, 3, x_92);
x_95 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_95, 0, x_85);
lean_ctor_set(x_95, 1, x_86);
lean_ctor_set(x_95, 2, x_94);
lean_ctor_set(x_95, 3, x_87);
lean_ctor_set(x_95, 4, x_88);
lean_ctor_set(x_95, 5, x_89);
if (lean_is_scalar(x_39)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_39;
}
lean_ctor_set(x_96, 0, x_74);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_125 = lean_ctor_get(x_44, 0);
x_126 = lean_ctor_get(x_44, 1);
x_127 = lean_ctor_get(x_44, 2);
x_128 = lean_ctor_get(x_44, 3);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_44);
x_162 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_163 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_163, 0, x_125);
lean_ctor_set(x_163, 1, x_126);
lean_ctor_set(x_163, 2, x_162);
lean_ctor_set(x_163, 3, x_128);
lean_ctor_set(x_38, 2, x_163);
x_164 = lean_ctor_get(x_6, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_6, 1);
lean_inc(x_165);
x_166 = lean_ctor_get(x_6, 2);
lean_inc(x_166);
x_167 = lean_ctor_get(x_6, 3);
lean_inc(x_167);
x_168 = lean_ctor_get(x_6, 4);
lean_inc(x_168);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_169 = x_6;
} else {
 lean_dec_ref(x_6);
 x_169 = lean_box(0);
}
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_40);
lean_ctor_set(x_170, 1, x_27);
x_171 = lean_array_push(x_166, x_170);
if (lean_is_scalar(x_169)) {
 x_172 = lean_alloc_ctor(0, 5, 0);
} else {
 x_172 = x_169;
}
lean_ctor_set(x_172, 0, x_164);
lean_ctor_set(x_172, 1, x_165);
lean_ctor_set(x_172, 2, x_171);
lean_ctor_set(x_172, 3, x_167);
lean_ctor_set(x_172, 4, x_168);
x_173 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6(x_1, x_2, x_3, x_4, x_42, x_172, x_38);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_176, 0, x_174);
x_129 = x_176;
x_130 = x_175;
goto block_161;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_173, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_173, 1);
lean_inc(x_178);
lean_dec(x_173);
x_179 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_179, 0, x_177);
x_129 = x_179;
x_130 = x_178;
goto block_161;
}
block_161:
{
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_131 = lean_ctor_get(x_130, 2);
lean_inc(x_131);
x_132 = lean_ctor_get(x_129, 0);
lean_inc(x_132);
lean_dec(x_129);
x_133 = lean_ctor_get(x_130, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_130, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_130, 3);
lean_inc(x_135);
x_136 = lean_ctor_get(x_130, 4);
lean_inc(x_136);
x_137 = lean_ctor_get(x_130, 5);
lean_inc(x_137);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 lean_ctor_release(x_130, 2);
 lean_ctor_release(x_130, 3);
 lean_ctor_release(x_130, 4);
 lean_ctor_release(x_130, 5);
 x_138 = x_130;
} else {
 lean_dec_ref(x_130);
 x_138 = lean_box(0);
}
x_139 = lean_ctor_get(x_131, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_131, 1);
lean_inc(x_140);
x_141 = lean_ctor_get(x_131, 3);
lean_inc(x_141);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 lean_ctor_release(x_131, 3);
 x_142 = x_131;
} else {
 lean_dec_ref(x_131);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(0, 4, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_139);
lean_ctor_set(x_143, 1, x_140);
lean_ctor_set(x_143, 2, x_127);
lean_ctor_set(x_143, 3, x_141);
if (lean_is_scalar(x_138)) {
 x_144 = lean_alloc_ctor(0, 6, 0);
} else {
 x_144 = x_138;
}
lean_ctor_set(x_144, 0, x_133);
lean_ctor_set(x_144, 1, x_134);
lean_ctor_set(x_144, 2, x_143);
lean_ctor_set(x_144, 3, x_135);
lean_ctor_set(x_144, 4, x_136);
lean_ctor_set(x_144, 5, x_137);
if (lean_is_scalar(x_39)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_39;
 lean_ctor_set_tag(x_145, 1);
}
lean_ctor_set(x_145, 0, x_132);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_146 = lean_ctor_get(x_130, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_129, 0);
lean_inc(x_147);
lean_dec(x_129);
x_148 = lean_ctor_get(x_130, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_130, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_130, 3);
lean_inc(x_150);
x_151 = lean_ctor_get(x_130, 4);
lean_inc(x_151);
x_152 = lean_ctor_get(x_130, 5);
lean_inc(x_152);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 lean_ctor_release(x_130, 2);
 lean_ctor_release(x_130, 3);
 lean_ctor_release(x_130, 4);
 lean_ctor_release(x_130, 5);
 x_153 = x_130;
} else {
 lean_dec_ref(x_130);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_146, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_146, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_146, 3);
lean_inc(x_156);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 lean_ctor_release(x_146, 2);
 lean_ctor_release(x_146, 3);
 x_157 = x_146;
} else {
 lean_dec_ref(x_146);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(0, 4, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_154);
lean_ctor_set(x_158, 1, x_155);
lean_ctor_set(x_158, 2, x_127);
lean_ctor_set(x_158, 3, x_156);
if (lean_is_scalar(x_153)) {
 x_159 = lean_alloc_ctor(0, 6, 0);
} else {
 x_159 = x_153;
}
lean_ctor_set(x_159, 0, x_148);
lean_ctor_set(x_159, 1, x_149);
lean_ctor_set(x_159, 2, x_158);
lean_ctor_set(x_159, 3, x_150);
lean_ctor_set(x_159, 4, x_151);
lean_ctor_set(x_159, 5, x_152);
if (lean_is_scalar(x_39)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_39;
}
lean_ctor_set(x_160, 0, x_147);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_180 = lean_ctor_get(x_38, 2);
x_181 = lean_ctor_get(x_38, 0);
x_182 = lean_ctor_get(x_38, 1);
x_183 = lean_ctor_get(x_38, 3);
x_184 = lean_ctor_get(x_38, 4);
x_185 = lean_ctor_get(x_38, 5);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_180);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_38);
x_186 = lean_ctor_get(x_180, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_180, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_180, 2);
lean_inc(x_188);
x_189 = lean_ctor_get(x_180, 3);
lean_inc(x_189);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 lean_ctor_release(x_180, 2);
 lean_ctor_release(x_180, 3);
 x_190 = x_180;
} else {
 lean_dec_ref(x_180);
 x_190 = lean_box(0);
}
x_224 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_190)) {
 x_225 = lean_alloc_ctor(0, 4, 0);
} else {
 x_225 = x_190;
}
lean_ctor_set(x_225, 0, x_186);
lean_ctor_set(x_225, 1, x_187);
lean_ctor_set(x_225, 2, x_224);
lean_ctor_set(x_225, 3, x_189);
x_226 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_226, 0, x_181);
lean_ctor_set(x_226, 1, x_182);
lean_ctor_set(x_226, 2, x_225);
lean_ctor_set(x_226, 3, x_183);
lean_ctor_set(x_226, 4, x_184);
lean_ctor_set(x_226, 5, x_185);
x_227 = lean_ctor_get(x_6, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_6, 1);
lean_inc(x_228);
x_229 = lean_ctor_get(x_6, 2);
lean_inc(x_229);
x_230 = lean_ctor_get(x_6, 3);
lean_inc(x_230);
x_231 = lean_ctor_get(x_6, 4);
lean_inc(x_231);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_232 = x_6;
} else {
 lean_dec_ref(x_6);
 x_232 = lean_box(0);
}
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_40);
lean_ctor_set(x_233, 1, x_27);
x_234 = lean_array_push(x_229, x_233);
if (lean_is_scalar(x_232)) {
 x_235 = lean_alloc_ctor(0, 5, 0);
} else {
 x_235 = x_232;
}
lean_ctor_set(x_235, 0, x_227);
lean_ctor_set(x_235, 1, x_228);
lean_ctor_set(x_235, 2, x_234);
lean_ctor_set(x_235, 3, x_230);
lean_ctor_set(x_235, 4, x_231);
x_236 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6(x_1, x_2, x_3, x_4, x_42, x_235, x_226);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec(x_236);
x_239 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_239, 0, x_237);
x_191 = x_239;
x_192 = x_238;
goto block_223;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_236, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_236, 1);
lean_inc(x_241);
lean_dec(x_236);
x_242 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_242, 0, x_240);
x_191 = x_242;
x_192 = x_241;
goto block_223;
}
block_223:
{
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_193 = lean_ctor_get(x_192, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_191, 0);
lean_inc(x_194);
lean_dec(x_191);
x_195 = lean_ctor_get(x_192, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_192, 1);
lean_inc(x_196);
x_197 = lean_ctor_get(x_192, 3);
lean_inc(x_197);
x_198 = lean_ctor_get(x_192, 4);
lean_inc(x_198);
x_199 = lean_ctor_get(x_192, 5);
lean_inc(x_199);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 lean_ctor_release(x_192, 2);
 lean_ctor_release(x_192, 3);
 lean_ctor_release(x_192, 4);
 lean_ctor_release(x_192, 5);
 x_200 = x_192;
} else {
 lean_dec_ref(x_192);
 x_200 = lean_box(0);
}
x_201 = lean_ctor_get(x_193, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_193, 1);
lean_inc(x_202);
x_203 = lean_ctor_get(x_193, 3);
lean_inc(x_203);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_204 = x_193;
} else {
 lean_dec_ref(x_193);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(0, 4, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_201);
lean_ctor_set(x_205, 1, x_202);
lean_ctor_set(x_205, 2, x_188);
lean_ctor_set(x_205, 3, x_203);
if (lean_is_scalar(x_200)) {
 x_206 = lean_alloc_ctor(0, 6, 0);
} else {
 x_206 = x_200;
}
lean_ctor_set(x_206, 0, x_195);
lean_ctor_set(x_206, 1, x_196);
lean_ctor_set(x_206, 2, x_205);
lean_ctor_set(x_206, 3, x_197);
lean_ctor_set(x_206, 4, x_198);
lean_ctor_set(x_206, 5, x_199);
if (lean_is_scalar(x_39)) {
 x_207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_207 = x_39;
 lean_ctor_set_tag(x_207, 1);
}
lean_ctor_set(x_207, 0, x_194);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_208 = lean_ctor_get(x_192, 2);
lean_inc(x_208);
x_209 = lean_ctor_get(x_191, 0);
lean_inc(x_209);
lean_dec(x_191);
x_210 = lean_ctor_get(x_192, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_192, 1);
lean_inc(x_211);
x_212 = lean_ctor_get(x_192, 3);
lean_inc(x_212);
x_213 = lean_ctor_get(x_192, 4);
lean_inc(x_213);
x_214 = lean_ctor_get(x_192, 5);
lean_inc(x_214);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 lean_ctor_release(x_192, 2);
 lean_ctor_release(x_192, 3);
 lean_ctor_release(x_192, 4);
 lean_ctor_release(x_192, 5);
 x_215 = x_192;
} else {
 lean_dec_ref(x_192);
 x_215 = lean_box(0);
}
x_216 = lean_ctor_get(x_208, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_208, 1);
lean_inc(x_217);
x_218 = lean_ctor_get(x_208, 3);
lean_inc(x_218);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 lean_ctor_release(x_208, 2);
 lean_ctor_release(x_208, 3);
 x_219 = x_208;
} else {
 lean_dec_ref(x_208);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(0, 4, 0);
} else {
 x_220 = x_219;
}
lean_ctor_set(x_220, 0, x_216);
lean_ctor_set(x_220, 1, x_217);
lean_ctor_set(x_220, 2, x_188);
lean_ctor_set(x_220, 3, x_218);
if (lean_is_scalar(x_215)) {
 x_221 = lean_alloc_ctor(0, 6, 0);
} else {
 x_221 = x_215;
}
lean_ctor_set(x_221, 0, x_210);
lean_ctor_set(x_221, 1, x_211);
lean_ctor_set(x_221, 2, x_220);
lean_ctor_set(x_221, 3, x_212);
lean_ctor_set(x_221, 4, x_213);
lean_ctor_set(x_221, 5, x_214);
if (lean_is_scalar(x_39)) {
 x_222 = lean_alloc_ctor(0, 2, 0);
} else {
 x_222 = x_39;
}
lean_ctor_set(x_222, 0, x_209);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
}
}
default: 
{
lean_object* x_243; lean_object* x_244; 
x_243 = lean_ctor_get(x_32, 1);
lean_inc(x_243);
lean_dec(x_32);
lean_inc(x_6);
x_244 = l_Lean_Meta_isClassExpensive___main(x_31, x_6, x_243);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_27);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = lean_unsigned_to_nat(1u);
x_248 = lean_nat_add(x_5, x_247);
lean_dec(x_5);
x_5 = x_248;
x_7 = x_246;
goto _start;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; 
x_250 = lean_ctor_get(x_244, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_251 = x_244;
} else {
 lean_dec_ref(x_244);
 x_251 = lean_box(0);
}
x_252 = lean_ctor_get(x_245, 0);
lean_inc(x_252);
lean_dec(x_245);
x_253 = lean_unsigned_to_nat(1u);
x_254 = lean_nat_add(x_5, x_253);
lean_dec(x_5);
x_255 = !lean_is_exclusive(x_250);
if (x_255 == 0)
{
lean_object* x_256; uint8_t x_257; 
x_256 = lean_ctor_get(x_250, 2);
x_257 = !lean_is_exclusive(x_256);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_310; uint8_t x_311; 
x_258 = lean_ctor_get(x_256, 2);
x_310 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_256, 2, x_310);
x_311 = !lean_is_exclusive(x_6);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_312 = lean_ctor_get(x_6, 2);
x_313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_313, 0, x_252);
lean_ctor_set(x_313, 1, x_27);
x_314 = lean_array_push(x_312, x_313);
lean_ctor_set(x_6, 2, x_314);
x_315 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6(x_1, x_2, x_3, x_4, x_254, x_6, x_250);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
x_318 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_318, 0, x_316);
x_259 = x_318;
x_260 = x_317;
goto block_309;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_319 = lean_ctor_get(x_315, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_315, 1);
lean_inc(x_320);
lean_dec(x_315);
x_321 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_321, 0, x_319);
x_259 = x_321;
x_260 = x_320;
goto block_309;
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_322 = lean_ctor_get(x_6, 0);
x_323 = lean_ctor_get(x_6, 1);
x_324 = lean_ctor_get(x_6, 2);
x_325 = lean_ctor_get(x_6, 3);
x_326 = lean_ctor_get(x_6, 4);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_6);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_252);
lean_ctor_set(x_327, 1, x_27);
x_328 = lean_array_push(x_324, x_327);
x_329 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_329, 0, x_322);
lean_ctor_set(x_329, 1, x_323);
lean_ctor_set(x_329, 2, x_328);
lean_ctor_set(x_329, 3, x_325);
lean_ctor_set(x_329, 4, x_326);
x_330 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6(x_1, x_2, x_3, x_4, x_254, x_329, x_250);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
lean_dec(x_330);
x_333 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_333, 0, x_331);
x_259 = x_333;
x_260 = x_332;
goto block_309;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_330, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_330, 1);
lean_inc(x_335);
lean_dec(x_330);
x_336 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_336, 0, x_334);
x_259 = x_336;
x_260 = x_335;
goto block_309;
}
}
block_309:
{
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_261 = lean_ctor_get(x_260, 2);
lean_inc(x_261);
x_262 = lean_ctor_get(x_259, 0);
lean_inc(x_262);
lean_dec(x_259);
x_263 = !lean_is_exclusive(x_260);
if (x_263 == 0)
{
lean_object* x_264; uint8_t x_265; 
x_264 = lean_ctor_get(x_260, 2);
lean_dec(x_264);
x_265 = !lean_is_exclusive(x_261);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_261, 2);
lean_dec(x_266);
lean_ctor_set(x_261, 2, x_258);
if (lean_is_scalar(x_251)) {
 x_267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_267 = x_251;
 lean_ctor_set_tag(x_267, 1);
}
lean_ctor_set(x_267, 0, x_262);
lean_ctor_set(x_267, 1, x_260);
return x_267;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_268 = lean_ctor_get(x_261, 0);
x_269 = lean_ctor_get(x_261, 1);
x_270 = lean_ctor_get(x_261, 3);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_261);
x_271 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_271, 0, x_268);
lean_ctor_set(x_271, 1, x_269);
lean_ctor_set(x_271, 2, x_258);
lean_ctor_set(x_271, 3, x_270);
lean_ctor_set(x_260, 2, x_271);
if (lean_is_scalar(x_251)) {
 x_272 = lean_alloc_ctor(1, 2, 0);
} else {
 x_272 = x_251;
 lean_ctor_set_tag(x_272, 1);
}
lean_ctor_set(x_272, 0, x_262);
lean_ctor_set(x_272, 1, x_260);
return x_272;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_273 = lean_ctor_get(x_260, 0);
x_274 = lean_ctor_get(x_260, 1);
x_275 = lean_ctor_get(x_260, 3);
x_276 = lean_ctor_get(x_260, 4);
x_277 = lean_ctor_get(x_260, 5);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_260);
x_278 = lean_ctor_get(x_261, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_261, 1);
lean_inc(x_279);
x_280 = lean_ctor_get(x_261, 3);
lean_inc(x_280);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 lean_ctor_release(x_261, 2);
 lean_ctor_release(x_261, 3);
 x_281 = x_261;
} else {
 lean_dec_ref(x_261);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(0, 4, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_278);
lean_ctor_set(x_282, 1, x_279);
lean_ctor_set(x_282, 2, x_258);
lean_ctor_set(x_282, 3, x_280);
x_283 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_283, 0, x_273);
lean_ctor_set(x_283, 1, x_274);
lean_ctor_set(x_283, 2, x_282);
lean_ctor_set(x_283, 3, x_275);
lean_ctor_set(x_283, 4, x_276);
lean_ctor_set(x_283, 5, x_277);
if (lean_is_scalar(x_251)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_251;
 lean_ctor_set_tag(x_284, 1);
}
lean_ctor_set(x_284, 0, x_262);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
}
else
{
lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_285 = lean_ctor_get(x_260, 2);
lean_inc(x_285);
x_286 = lean_ctor_get(x_259, 0);
lean_inc(x_286);
lean_dec(x_259);
x_287 = !lean_is_exclusive(x_260);
if (x_287 == 0)
{
lean_object* x_288; uint8_t x_289; 
x_288 = lean_ctor_get(x_260, 2);
lean_dec(x_288);
x_289 = !lean_is_exclusive(x_285);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_285, 2);
lean_dec(x_290);
lean_ctor_set(x_285, 2, x_258);
if (lean_is_scalar(x_251)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_251;
}
lean_ctor_set(x_291, 0, x_286);
lean_ctor_set(x_291, 1, x_260);
return x_291;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_292 = lean_ctor_get(x_285, 0);
x_293 = lean_ctor_get(x_285, 1);
x_294 = lean_ctor_get(x_285, 3);
lean_inc(x_294);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_285);
x_295 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_295, 0, x_292);
lean_ctor_set(x_295, 1, x_293);
lean_ctor_set(x_295, 2, x_258);
lean_ctor_set(x_295, 3, x_294);
lean_ctor_set(x_260, 2, x_295);
if (lean_is_scalar(x_251)) {
 x_296 = lean_alloc_ctor(0, 2, 0);
} else {
 x_296 = x_251;
}
lean_ctor_set(x_296, 0, x_286);
lean_ctor_set(x_296, 1, x_260);
return x_296;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_297 = lean_ctor_get(x_260, 0);
x_298 = lean_ctor_get(x_260, 1);
x_299 = lean_ctor_get(x_260, 3);
x_300 = lean_ctor_get(x_260, 4);
x_301 = lean_ctor_get(x_260, 5);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_260);
x_302 = lean_ctor_get(x_285, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_285, 1);
lean_inc(x_303);
x_304 = lean_ctor_get(x_285, 3);
lean_inc(x_304);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 lean_ctor_release(x_285, 2);
 lean_ctor_release(x_285, 3);
 x_305 = x_285;
} else {
 lean_dec_ref(x_285);
 x_305 = lean_box(0);
}
if (lean_is_scalar(x_305)) {
 x_306 = lean_alloc_ctor(0, 4, 0);
} else {
 x_306 = x_305;
}
lean_ctor_set(x_306, 0, x_302);
lean_ctor_set(x_306, 1, x_303);
lean_ctor_set(x_306, 2, x_258);
lean_ctor_set(x_306, 3, x_304);
x_307 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_307, 0, x_297);
lean_ctor_set(x_307, 1, x_298);
lean_ctor_set(x_307, 2, x_306);
lean_ctor_set(x_307, 3, x_299);
lean_ctor_set(x_307, 4, x_300);
lean_ctor_set(x_307, 5, x_301);
if (lean_is_scalar(x_251)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_251;
}
lean_ctor_set(x_308, 0, x_286);
lean_ctor_set(x_308, 1, x_307);
return x_308;
}
}
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_337 = lean_ctor_get(x_256, 0);
x_338 = lean_ctor_get(x_256, 1);
x_339 = lean_ctor_get(x_256, 2);
x_340 = lean_ctor_get(x_256, 3);
lean_inc(x_340);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_256);
x_374 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_375 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_375, 0, x_337);
lean_ctor_set(x_375, 1, x_338);
lean_ctor_set(x_375, 2, x_374);
lean_ctor_set(x_375, 3, x_340);
lean_ctor_set(x_250, 2, x_375);
x_376 = lean_ctor_get(x_6, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_6, 1);
lean_inc(x_377);
x_378 = lean_ctor_get(x_6, 2);
lean_inc(x_378);
x_379 = lean_ctor_get(x_6, 3);
lean_inc(x_379);
x_380 = lean_ctor_get(x_6, 4);
lean_inc(x_380);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_381 = x_6;
} else {
 lean_dec_ref(x_6);
 x_381 = lean_box(0);
}
x_382 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_382, 0, x_252);
lean_ctor_set(x_382, 1, x_27);
x_383 = lean_array_push(x_378, x_382);
if (lean_is_scalar(x_381)) {
 x_384 = lean_alloc_ctor(0, 5, 0);
} else {
 x_384 = x_381;
}
lean_ctor_set(x_384, 0, x_376);
lean_ctor_set(x_384, 1, x_377);
lean_ctor_set(x_384, 2, x_383);
lean_ctor_set(x_384, 3, x_379);
lean_ctor_set(x_384, 4, x_380);
x_385 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6(x_1, x_2, x_3, x_4, x_254, x_384, x_250);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_385, 1);
lean_inc(x_387);
lean_dec(x_385);
x_388 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_388, 0, x_386);
x_341 = x_388;
x_342 = x_387;
goto block_373;
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_389 = lean_ctor_get(x_385, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_385, 1);
lean_inc(x_390);
lean_dec(x_385);
x_391 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_391, 0, x_389);
x_341 = x_391;
x_342 = x_390;
goto block_373;
}
block_373:
{
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_343 = lean_ctor_get(x_342, 2);
lean_inc(x_343);
x_344 = lean_ctor_get(x_341, 0);
lean_inc(x_344);
lean_dec(x_341);
x_345 = lean_ctor_get(x_342, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_342, 1);
lean_inc(x_346);
x_347 = lean_ctor_get(x_342, 3);
lean_inc(x_347);
x_348 = lean_ctor_get(x_342, 4);
lean_inc(x_348);
x_349 = lean_ctor_get(x_342, 5);
lean_inc(x_349);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 lean_ctor_release(x_342, 2);
 lean_ctor_release(x_342, 3);
 lean_ctor_release(x_342, 4);
 lean_ctor_release(x_342, 5);
 x_350 = x_342;
} else {
 lean_dec_ref(x_342);
 x_350 = lean_box(0);
}
x_351 = lean_ctor_get(x_343, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_343, 1);
lean_inc(x_352);
x_353 = lean_ctor_get(x_343, 3);
lean_inc(x_353);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 lean_ctor_release(x_343, 2);
 lean_ctor_release(x_343, 3);
 x_354 = x_343;
} else {
 lean_dec_ref(x_343);
 x_354 = lean_box(0);
}
if (lean_is_scalar(x_354)) {
 x_355 = lean_alloc_ctor(0, 4, 0);
} else {
 x_355 = x_354;
}
lean_ctor_set(x_355, 0, x_351);
lean_ctor_set(x_355, 1, x_352);
lean_ctor_set(x_355, 2, x_339);
lean_ctor_set(x_355, 3, x_353);
if (lean_is_scalar(x_350)) {
 x_356 = lean_alloc_ctor(0, 6, 0);
} else {
 x_356 = x_350;
}
lean_ctor_set(x_356, 0, x_345);
lean_ctor_set(x_356, 1, x_346);
lean_ctor_set(x_356, 2, x_355);
lean_ctor_set(x_356, 3, x_347);
lean_ctor_set(x_356, 4, x_348);
lean_ctor_set(x_356, 5, x_349);
if (lean_is_scalar(x_251)) {
 x_357 = lean_alloc_ctor(1, 2, 0);
} else {
 x_357 = x_251;
 lean_ctor_set_tag(x_357, 1);
}
lean_ctor_set(x_357, 0, x_344);
lean_ctor_set(x_357, 1, x_356);
return x_357;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_358 = lean_ctor_get(x_342, 2);
lean_inc(x_358);
x_359 = lean_ctor_get(x_341, 0);
lean_inc(x_359);
lean_dec(x_341);
x_360 = lean_ctor_get(x_342, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_342, 1);
lean_inc(x_361);
x_362 = lean_ctor_get(x_342, 3);
lean_inc(x_362);
x_363 = lean_ctor_get(x_342, 4);
lean_inc(x_363);
x_364 = lean_ctor_get(x_342, 5);
lean_inc(x_364);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 lean_ctor_release(x_342, 2);
 lean_ctor_release(x_342, 3);
 lean_ctor_release(x_342, 4);
 lean_ctor_release(x_342, 5);
 x_365 = x_342;
} else {
 lean_dec_ref(x_342);
 x_365 = lean_box(0);
}
x_366 = lean_ctor_get(x_358, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_358, 1);
lean_inc(x_367);
x_368 = lean_ctor_get(x_358, 3);
lean_inc(x_368);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 lean_ctor_release(x_358, 2);
 lean_ctor_release(x_358, 3);
 x_369 = x_358;
} else {
 lean_dec_ref(x_358);
 x_369 = lean_box(0);
}
if (lean_is_scalar(x_369)) {
 x_370 = lean_alloc_ctor(0, 4, 0);
} else {
 x_370 = x_369;
}
lean_ctor_set(x_370, 0, x_366);
lean_ctor_set(x_370, 1, x_367);
lean_ctor_set(x_370, 2, x_339);
lean_ctor_set(x_370, 3, x_368);
if (lean_is_scalar(x_365)) {
 x_371 = lean_alloc_ctor(0, 6, 0);
} else {
 x_371 = x_365;
}
lean_ctor_set(x_371, 0, x_360);
lean_ctor_set(x_371, 1, x_361);
lean_ctor_set(x_371, 2, x_370);
lean_ctor_set(x_371, 3, x_362);
lean_ctor_set(x_371, 4, x_363);
lean_ctor_set(x_371, 5, x_364);
if (lean_is_scalar(x_251)) {
 x_372 = lean_alloc_ctor(0, 2, 0);
} else {
 x_372 = x_251;
}
lean_ctor_set(x_372, 0, x_359);
lean_ctor_set(x_372, 1, x_371);
return x_372;
}
}
}
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_392 = lean_ctor_get(x_250, 2);
x_393 = lean_ctor_get(x_250, 0);
x_394 = lean_ctor_get(x_250, 1);
x_395 = lean_ctor_get(x_250, 3);
x_396 = lean_ctor_get(x_250, 4);
x_397 = lean_ctor_get(x_250, 5);
lean_inc(x_397);
lean_inc(x_396);
lean_inc(x_395);
lean_inc(x_392);
lean_inc(x_394);
lean_inc(x_393);
lean_dec(x_250);
x_398 = lean_ctor_get(x_392, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_392, 1);
lean_inc(x_399);
x_400 = lean_ctor_get(x_392, 2);
lean_inc(x_400);
x_401 = lean_ctor_get(x_392, 3);
lean_inc(x_401);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 lean_ctor_release(x_392, 2);
 lean_ctor_release(x_392, 3);
 x_402 = x_392;
} else {
 lean_dec_ref(x_392);
 x_402 = lean_box(0);
}
x_436 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_402)) {
 x_437 = lean_alloc_ctor(0, 4, 0);
} else {
 x_437 = x_402;
}
lean_ctor_set(x_437, 0, x_398);
lean_ctor_set(x_437, 1, x_399);
lean_ctor_set(x_437, 2, x_436);
lean_ctor_set(x_437, 3, x_401);
x_438 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_438, 0, x_393);
lean_ctor_set(x_438, 1, x_394);
lean_ctor_set(x_438, 2, x_437);
lean_ctor_set(x_438, 3, x_395);
lean_ctor_set(x_438, 4, x_396);
lean_ctor_set(x_438, 5, x_397);
x_439 = lean_ctor_get(x_6, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_6, 1);
lean_inc(x_440);
x_441 = lean_ctor_get(x_6, 2);
lean_inc(x_441);
x_442 = lean_ctor_get(x_6, 3);
lean_inc(x_442);
x_443 = lean_ctor_get(x_6, 4);
lean_inc(x_443);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_444 = x_6;
} else {
 lean_dec_ref(x_6);
 x_444 = lean_box(0);
}
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_252);
lean_ctor_set(x_445, 1, x_27);
x_446 = lean_array_push(x_441, x_445);
if (lean_is_scalar(x_444)) {
 x_447 = lean_alloc_ctor(0, 5, 0);
} else {
 x_447 = x_444;
}
lean_ctor_set(x_447, 0, x_439);
lean_ctor_set(x_447, 1, x_440);
lean_ctor_set(x_447, 2, x_446);
lean_ctor_set(x_447, 3, x_442);
lean_ctor_set(x_447, 4, x_443);
x_448 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6(x_1, x_2, x_3, x_4, x_254, x_447, x_438);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_448, 1);
lean_inc(x_450);
lean_dec(x_448);
x_451 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_451, 0, x_449);
x_403 = x_451;
x_404 = x_450;
goto block_435;
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_452 = lean_ctor_get(x_448, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_448, 1);
lean_inc(x_453);
lean_dec(x_448);
x_454 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_454, 0, x_452);
x_403 = x_454;
x_404 = x_453;
goto block_435;
}
block_435:
{
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_405 = lean_ctor_get(x_404, 2);
lean_inc(x_405);
x_406 = lean_ctor_get(x_403, 0);
lean_inc(x_406);
lean_dec(x_403);
x_407 = lean_ctor_get(x_404, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_404, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_404, 3);
lean_inc(x_409);
x_410 = lean_ctor_get(x_404, 4);
lean_inc(x_410);
x_411 = lean_ctor_get(x_404, 5);
lean_inc(x_411);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 lean_ctor_release(x_404, 2);
 lean_ctor_release(x_404, 3);
 lean_ctor_release(x_404, 4);
 lean_ctor_release(x_404, 5);
 x_412 = x_404;
} else {
 lean_dec_ref(x_404);
 x_412 = lean_box(0);
}
x_413 = lean_ctor_get(x_405, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_405, 1);
lean_inc(x_414);
x_415 = lean_ctor_get(x_405, 3);
lean_inc(x_415);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 lean_ctor_release(x_405, 2);
 lean_ctor_release(x_405, 3);
 x_416 = x_405;
} else {
 lean_dec_ref(x_405);
 x_416 = lean_box(0);
}
if (lean_is_scalar(x_416)) {
 x_417 = lean_alloc_ctor(0, 4, 0);
} else {
 x_417 = x_416;
}
lean_ctor_set(x_417, 0, x_413);
lean_ctor_set(x_417, 1, x_414);
lean_ctor_set(x_417, 2, x_400);
lean_ctor_set(x_417, 3, x_415);
if (lean_is_scalar(x_412)) {
 x_418 = lean_alloc_ctor(0, 6, 0);
} else {
 x_418 = x_412;
}
lean_ctor_set(x_418, 0, x_407);
lean_ctor_set(x_418, 1, x_408);
lean_ctor_set(x_418, 2, x_417);
lean_ctor_set(x_418, 3, x_409);
lean_ctor_set(x_418, 4, x_410);
lean_ctor_set(x_418, 5, x_411);
if (lean_is_scalar(x_251)) {
 x_419 = lean_alloc_ctor(1, 2, 0);
} else {
 x_419 = x_251;
 lean_ctor_set_tag(x_419, 1);
}
lean_ctor_set(x_419, 0, x_406);
lean_ctor_set(x_419, 1, x_418);
return x_419;
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_420 = lean_ctor_get(x_404, 2);
lean_inc(x_420);
x_421 = lean_ctor_get(x_403, 0);
lean_inc(x_421);
lean_dec(x_403);
x_422 = lean_ctor_get(x_404, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_404, 1);
lean_inc(x_423);
x_424 = lean_ctor_get(x_404, 3);
lean_inc(x_424);
x_425 = lean_ctor_get(x_404, 4);
lean_inc(x_425);
x_426 = lean_ctor_get(x_404, 5);
lean_inc(x_426);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 lean_ctor_release(x_404, 2);
 lean_ctor_release(x_404, 3);
 lean_ctor_release(x_404, 4);
 lean_ctor_release(x_404, 5);
 x_427 = x_404;
} else {
 lean_dec_ref(x_404);
 x_427 = lean_box(0);
}
x_428 = lean_ctor_get(x_420, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_420, 1);
lean_inc(x_429);
x_430 = lean_ctor_get(x_420, 3);
lean_inc(x_430);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 lean_ctor_release(x_420, 2);
 lean_ctor_release(x_420, 3);
 x_431 = x_420;
} else {
 lean_dec_ref(x_420);
 x_431 = lean_box(0);
}
if (lean_is_scalar(x_431)) {
 x_432 = lean_alloc_ctor(0, 4, 0);
} else {
 x_432 = x_431;
}
lean_ctor_set(x_432, 0, x_428);
lean_ctor_set(x_432, 1, x_429);
lean_ctor_set(x_432, 2, x_400);
lean_ctor_set(x_432, 3, x_430);
if (lean_is_scalar(x_427)) {
 x_433 = lean_alloc_ctor(0, 6, 0);
} else {
 x_433 = x_427;
}
lean_ctor_set(x_433, 0, x_422);
lean_ctor_set(x_433, 1, x_423);
lean_ctor_set(x_433, 2, x_432);
lean_ctor_set(x_433, 3, x_424);
lean_ctor_set(x_433, 4, x_425);
lean_ctor_set(x_433, 5, x_426);
if (lean_is_scalar(x_251)) {
 x_434 = lean_alloc_ctor(0, 2, 0);
} else {
 x_434 = x_251;
}
lean_ctor_set(x_434, 0, x_421);
lean_ctor_set(x_434, 1, x_433);
return x_434;
}
}
}
}
}
else
{
uint8_t x_455; 
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_455 = !lean_is_exclusive(x_244);
if (x_455 == 0)
{
return x_244;
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_456 = lean_ctor_get(x_244, 0);
x_457 = lean_ctor_get(x_244, 1);
lean_inc(x_457);
lean_inc(x_456);
lean_dec(x_244);
x_458 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_458, 0, x_456);
lean_ctor_set(x_458, 1, x_457);
return x_458;
}
}
}
}
}
else
{
uint8_t x_459; 
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_459 = !lean_is_exclusive(x_32);
if (x_459 == 0)
{
return x_32;
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_460 = lean_ctor_get(x_32, 0);
x_461 = lean_ctor_get(x_32, 1);
lean_inc(x_461);
lean_inc(x_460);
lean_dec(x_32);
x_462 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_462, 0, x_460);
lean_ctor_set(x_462, 1, x_461);
return x_462;
}
}
}
else
{
uint8_t x_463; 
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_463 = !lean_is_exclusive(x_28);
if (x_463 == 0)
{
return x_28;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_464 = lean_ctor_get(x_28, 0);
x_465 = lean_ctor_get(x_28, 1);
lean_inc(x_465);
lean_inc(x_464);
lean_dec(x_28);
x_466 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_466, 0, x_464);
lean_ctor_set(x_466, 1, x_465);
return x_466;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_4__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
if (lean_obj_tag(x_6) == 7)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint64_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_6, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_6, 2);
lean_inc(x_26);
x_27 = lean_ctor_get_uint64(x_6, sizeof(void*)*3);
lean_dec(x_6);
x_28 = lean_array_get_size(x_4);
x_29 = lean_expr_instantiate_rev_range(x_25, x_5, x_28, x_4);
lean_dec(x_28);
lean_dec(x_25);
x_30 = l_Lean_Meta_mkFreshId___rarg(x_8);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = (uint8_t)((x_27 << 24) >> 61);
lean_inc(x_31);
x_34 = lean_local_ctx_mk_local_decl(x_3, x_31, x_24, x_29, x_33);
x_35 = l_Lean_mkFVar(x_31);
x_36 = lean_array_push(x_4, x_35);
x_3 = x_34;
x_4 = x_36;
x_6 = x_26;
x_8 = x_32;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint64_t x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_38 = lean_ctor_get(x_6, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_6, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_6, 2);
lean_inc(x_40);
x_41 = lean_ctor_get_uint64(x_6, sizeof(void*)*3);
x_42 = lean_ctor_get(x_2, 0);
lean_inc(x_42);
x_43 = lean_array_get_size(x_4);
x_44 = lean_nat_dec_lt(x_43, x_42);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_2);
x_45 = lean_expr_instantiate_rev_range(x_6, x_5, x_43, x_4);
lean_dec(x_6);
x_46 = !lean_is_exclusive(x_7);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_7, 1);
lean_dec(x_47);
lean_ctor_set(x_7, 1, x_3);
x_48 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6(x_4, x_43, x_45, x_4, x_5, x_7, x_8);
lean_dec(x_45);
lean_dec(x_4);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_7, 0);
x_50 = lean_ctor_get(x_7, 2);
x_51 = lean_ctor_get(x_7, 3);
x_52 = lean_ctor_get(x_7, 4);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_7);
x_53 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_3);
lean_ctor_set(x_53, 2, x_50);
lean_ctor_set(x_53, 3, x_51);
lean_ctor_set(x_53, 4, x_52);
x_54 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6(x_4, x_43, x_45, x_4, x_5, x_53, x_8);
lean_dec(x_45);
lean_dec(x_4);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_6);
x_55 = lean_expr_instantiate_rev_range(x_39, x_5, x_43, x_4);
lean_dec(x_43);
lean_dec(x_39);
x_56 = l_Lean_Meta_mkFreshId___rarg(x_8);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = (uint8_t)((x_41 << 24) >> 61);
lean_inc(x_57);
x_60 = lean_local_ctx_mk_local_decl(x_3, x_57, x_38, x_55, x_59);
x_61 = l_Lean_mkFVar(x_57);
x_62 = lean_array_push(x_4, x_61);
x_3 = x_60;
x_4 = x_62;
x_6 = x_40;
x_8 = x_58;
goto _start;
}
}
}
else
{
lean_object* x_64; 
x_64 = lean_box(0);
x_9 = x_64;
goto block_23;
}
block_23:
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
x_14 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4(x_4, x_10, x_11, x_4, x_5, x_7, x_8);
lean_dec(x_11);
lean_dec(x_4);
return x_14;
}
else
{
lean_object* x_15; 
lean_inc(x_5);
lean_inc(x_4);
x_15 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_11, x_4, x_5, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 2);
x_18 = lean_ctor_get(x_7, 3);
x_19 = lean_ctor_get(x_7, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
lean_inc(x_3);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_3);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
if (x_1 == 0)
{
lean_object* x_21; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_21 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4(x_4, x_10, x_11, x_4, x_5, x_20, x_8);
lean_dec(x_11);
lean_dec(x_4);
return x_21;
}
else
{
lean_object* x_22; 
lean_inc(x_5);
lean_inc(x_4);
x_22 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_11, x_4, x_5, x_20, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_22;
}
}
}
}
}
lean_object* _init_l___private_Lean_Meta_Basic_5__forallTelescopeReducingAux___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Basic_5__forallTelescopeReducingAux___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = l___private_Lean_Meta_Basic_5__forallTelescopeReducingAux___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__2___closed__1;
x_11 = l_Nat_foldMAux___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__1(x_9, x_10, x_10, x_9, x_3, x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l___private_Lean_Meta_FunInfo_4__collectDeps(x_9, x_1);
lean_dec(x_1);
x_15 = l___private_Lean_Meta_FunInfo_5__updateHasFwdDeps(x_13, x_14);
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
x_19 = l___private_Lean_Meta_FunInfo_4__collectDeps(x_9, x_1);
lean_dec(x_1);
x_20 = l___private_Lean_Meta_FunInfo_5__updateHasFwdDeps(x_17, x_19);
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
x_31 = l___private_Lean_Meta_Basic_4__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__3(x_28, x_2, x_27, x_29, x_30, x_6, x_3, x_7);
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
lean_object* l___private_Lean_Meta_FunInfo_6__getFunInfoAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 4);
lean_inc(x_9);
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 6);
x_13 = lean_ctor_get(x_4, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_2);
lean_inc(x_1);
x_15 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_12);
x_16 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__1(x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_inc(x_3);
x_17 = l_Lean_Meta_inferType(x_1, x_3, x_4);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_3, 4);
lean_dec(x_19);
x_20 = lean_ctor_get(x_3, 3);
lean_dec(x_20);
x_21 = lean_ctor_get(x_3, 2);
lean_dec(x_21);
x_22 = lean_ctor_get(x_3, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_3, 0);
lean_dec(x_23);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec(x_17);
x_26 = 1;
lean_ctor_set_uint8(x_5, sizeof(void*)*1 + 6, x_26);
x_27 = l___private_Lean_Meta_Basic_5__forallTelescopeReducingAux___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__2(x_24, x_2, x_3, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 2);
lean_inc(x_29);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_28, 2);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
x_37 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4(x_36, x_15, x_31);
lean_ctor_set(x_29, 1, x_37);
return x_27;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_29, 1);
x_40 = lean_ctor_get(x_29, 2);
x_41 = lean_ctor_get(x_29, 3);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_29);
lean_inc(x_31);
x_42 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4(x_39, x_15, x_31);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set(x_43, 3, x_41);
lean_ctor_set(x_28, 2, x_43);
return x_27;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_44 = lean_ctor_get(x_28, 0);
x_45 = lean_ctor_get(x_28, 1);
x_46 = lean_ctor_get(x_28, 3);
x_47 = lean_ctor_get(x_28, 4);
x_48 = lean_ctor_get(x_28, 5);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_28);
x_49 = lean_ctor_get(x_29, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_29, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_29, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_29, 3);
lean_inc(x_52);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 lean_ctor_release(x_29, 2);
 lean_ctor_release(x_29, 3);
 x_53 = x_29;
} else {
 lean_dec_ref(x_29);
 x_53 = lean_box(0);
}
lean_inc(x_31);
x_54 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4(x_50, x_15, x_31);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 4, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_51);
lean_ctor_set(x_55, 3, x_52);
x_56 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_56, 0, x_44);
lean_ctor_set(x_56, 1, x_45);
lean_ctor_set(x_56, 2, x_55);
lean_ctor_set(x_56, 3, x_46);
lean_ctor_set(x_56, 4, x_47);
lean_ctor_set(x_56, 5, x_48);
lean_ctor_set(x_27, 1, x_56);
return x_27;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_57 = lean_ctor_get(x_27, 0);
lean_inc(x_57);
lean_dec(x_27);
x_58 = lean_ctor_get(x_28, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_28, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_28, 3);
lean_inc(x_60);
x_61 = lean_ctor_get(x_28, 4);
lean_inc(x_61);
x_62 = lean_ctor_get(x_28, 5);
lean_inc(x_62);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 lean_ctor_release(x_28, 3);
 lean_ctor_release(x_28, 4);
 lean_ctor_release(x_28, 5);
 x_63 = x_28;
} else {
 lean_dec_ref(x_28);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_29, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_29, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_29, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_29, 3);
lean_inc(x_67);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 lean_ctor_release(x_29, 2);
 lean_ctor_release(x_29, 3);
 x_68 = x_29;
} else {
 lean_dec_ref(x_29);
 x_68 = lean_box(0);
}
lean_inc(x_57);
x_69 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4(x_65, x_15, x_57);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 4, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_70, 2, x_66);
lean_ctor_set(x_70, 3, x_67);
if (lean_is_scalar(x_63)) {
 x_71 = lean_alloc_ctor(0, 6, 0);
} else {
 x_71 = x_63;
}
lean_ctor_set(x_71, 0, x_58);
lean_ctor_set(x_71, 1, x_59);
lean_ctor_set(x_71, 2, x_70);
lean_ctor_set(x_71, 3, x_60);
lean_ctor_set(x_71, 4, x_61);
lean_ctor_set(x_71, 5, x_62);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_57);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
else
{
uint8_t x_73; 
lean_dec(x_15);
x_73 = !lean_is_exclusive(x_27);
if (x_73 == 0)
{
return x_27;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_27, 0);
x_75 = lean_ctor_get(x_27, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_27);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_free_object(x_3);
lean_dec(x_15);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_77 = !lean_is_exclusive(x_17);
if (x_77 == 0)
{
return x_17;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_17, 0);
x_79 = lean_ctor_get(x_17, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_17);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_17, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_17, 1);
lean_inc(x_82);
lean_dec(x_17);
x_83 = 1;
lean_ctor_set_uint8(x_5, sizeof(void*)*1 + 6, x_83);
x_84 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_84, 0, x_5);
lean_ctor_set(x_84, 1, x_6);
lean_ctor_set(x_84, 2, x_7);
lean_ctor_set(x_84, 3, x_8);
lean_ctor_set(x_84, 4, x_9);
x_85 = l___private_Lean_Meta_Basic_5__forallTelescopeReducingAux___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__2(x_81, x_2, x_84, x_82);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_86, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_85, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_89 = x_85;
} else {
 lean_dec_ref(x_85);
 x_89 = lean_box(0);
}
x_90 = lean_ctor_get(x_86, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_86, 3);
lean_inc(x_92);
x_93 = lean_ctor_get(x_86, 4);
lean_inc(x_93);
x_94 = lean_ctor_get(x_86, 5);
lean_inc(x_94);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 lean_ctor_release(x_86, 2);
 lean_ctor_release(x_86, 3);
 lean_ctor_release(x_86, 4);
 lean_ctor_release(x_86, 5);
 x_95 = x_86;
} else {
 lean_dec_ref(x_86);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get(x_87, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_87, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_87, 2);
lean_inc(x_98);
x_99 = lean_ctor_get(x_87, 3);
lean_inc(x_99);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 lean_ctor_release(x_87, 2);
 lean_ctor_release(x_87, 3);
 x_100 = x_87;
} else {
 lean_dec_ref(x_87);
 x_100 = lean_box(0);
}
lean_inc(x_88);
x_101 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4(x_97, x_15, x_88);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(0, 4, 0);
} else {
 x_102 = x_100;
}
lean_ctor_set(x_102, 0, x_96);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set(x_102, 2, x_98);
lean_ctor_set(x_102, 3, x_99);
if (lean_is_scalar(x_95)) {
 x_103 = lean_alloc_ctor(0, 6, 0);
} else {
 x_103 = x_95;
}
lean_ctor_set(x_103, 0, x_90);
lean_ctor_set(x_103, 1, x_91);
lean_ctor_set(x_103, 2, x_102);
lean_ctor_set(x_103, 3, x_92);
lean_ctor_set(x_103, 4, x_93);
lean_ctor_set(x_103, 5, x_94);
if (lean_is_scalar(x_89)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_89;
}
lean_ctor_set(x_104, 0, x_88);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_15);
x_105 = lean_ctor_get(x_85, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_85, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_107 = x_85;
} else {
 lean_dec_ref(x_85);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_15);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_109 = lean_ctor_get(x_17, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_17, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_111 = x_17;
} else {
 lean_dec_ref(x_17);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_15);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_113 = lean_ctor_get(x_16, 0);
lean_inc(x_113);
lean_dec(x_16);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_4);
return x_114;
}
}
else
{
lean_object* x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_115 = lean_ctor_get(x_5, 0);
x_116 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_117 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_118 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 2);
x_119 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 3);
x_120 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 4);
x_121 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 5);
x_122 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 6);
lean_inc(x_115);
lean_dec(x_5);
x_123 = lean_ctor_get(x_4, 2);
lean_inc(x_123);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec(x_123);
lean_inc(x_2);
lean_inc(x_1);
x_125 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_125, 0, x_1);
lean_ctor_set(x_125, 1, x_2);
lean_ctor_set_uint8(x_125, sizeof(void*)*2, x_122);
x_126 = l_Std_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__1(x_124, x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; 
lean_inc(x_3);
x_127 = l_Lean_Meta_inferType(x_1, x_3, x_4);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 x_128 = x_3;
} else {
 lean_dec_ref(x_3);
 x_128 = lean_box(0);
}
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
x_131 = 1;
x_132 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_132, 0, x_115);
lean_ctor_set_uint8(x_132, sizeof(void*)*1, x_116);
lean_ctor_set_uint8(x_132, sizeof(void*)*1 + 1, x_117);
lean_ctor_set_uint8(x_132, sizeof(void*)*1 + 2, x_118);
lean_ctor_set_uint8(x_132, sizeof(void*)*1 + 3, x_119);
lean_ctor_set_uint8(x_132, sizeof(void*)*1 + 4, x_120);
lean_ctor_set_uint8(x_132, sizeof(void*)*1 + 5, x_121);
lean_ctor_set_uint8(x_132, sizeof(void*)*1 + 6, x_131);
if (lean_is_scalar(x_128)) {
 x_133 = lean_alloc_ctor(0, 5, 0);
} else {
 x_133 = x_128;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_6);
lean_ctor_set(x_133, 2, x_7);
lean_ctor_set(x_133, 3, x_8);
lean_ctor_set(x_133, 4, x_9);
x_134 = l___private_Lean_Meta_Basic_5__forallTelescopeReducingAux___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__2(x_129, x_2, x_133, x_130);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_135, 2);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 0);
lean_inc(x_137);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_138 = x_134;
} else {
 lean_dec_ref(x_134);
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
x_147 = lean_ctor_get(x_136, 2);
lean_inc(x_147);
x_148 = lean_ctor_get(x_136, 3);
lean_inc(x_148);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 lean_ctor_release(x_136, 2);
 lean_ctor_release(x_136, 3);
 x_149 = x_136;
} else {
 lean_dec_ref(x_136);
 x_149 = lean_box(0);
}
lean_inc(x_137);
x_150 = l_Std_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_1__checkFunInfoCache___spec__4(x_146, x_125, x_137);
if (lean_is_scalar(x_149)) {
 x_151 = lean_alloc_ctor(0, 4, 0);
} else {
 x_151 = x_149;
}
lean_ctor_set(x_151, 0, x_145);
lean_ctor_set(x_151, 1, x_150);
lean_ctor_set(x_151, 2, x_147);
lean_ctor_set(x_151, 3, x_148);
if (lean_is_scalar(x_144)) {
 x_152 = lean_alloc_ctor(0, 6, 0);
} else {
 x_152 = x_144;
}
lean_ctor_set(x_152, 0, x_139);
lean_ctor_set(x_152, 1, x_140);
lean_ctor_set(x_152, 2, x_151);
lean_ctor_set(x_152, 3, x_141);
lean_ctor_set(x_152, 4, x_142);
lean_ctor_set(x_152, 5, x_143);
if (lean_is_scalar(x_138)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_138;
}
lean_ctor_set(x_153, 0, x_137);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_125);
x_154 = lean_ctor_get(x_134, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_134, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_156 = x_134;
} else {
 lean_dec_ref(x_134);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_128);
lean_dec(x_125);
lean_dec(x_115);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_158 = lean_ctor_get(x_127, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_127, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_160 = x_127;
} else {
 lean_dec_ref(x_127);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_125);
lean_dec(x_115);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_162 = lean_ctor_get(x_126, 0);
lean_inc(x_162);
lean_dec(x_126);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_4);
return x_163;
}
}
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_foldMAux___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5___lambda__1(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__5(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Basic_4__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l___private_Lean_Meta_Basic_4__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__3(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Meta_getFunInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l___private_Lean_Meta_FunInfo_6__getFunInfoAux(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = l___private_Lean_Meta_FunInfo_6__getFunInfoAux(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Basic(lean_object*);
lean_object* initialize_Lean_Meta_InferType(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_FunInfo(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
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
l___private_Lean_Meta_Basic_5__forallTelescopeReducingAux___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__2___closed__1 = _init_l___private_Lean_Meta_Basic_5__forallTelescopeReducingAux___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Basic_5__forallTelescopeReducingAux___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__2___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
