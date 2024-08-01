// Lean compiler output
// Module: Lean.Meta.FunInfo
// Imports: Lean.Meta.Basic Lean.Meta.InferType
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__6(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_qpartition___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__1(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static size_t l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2___closed__1;
uint64_t l_Lean_Meta_TransparencyMode_hash(uint8_t);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_getOutParamPositions_x3f(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___rarg(lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__3(lean_object*, lean_object*, size_t, size_t);
lean_object* l_ReaderT_instApplicativeOfMonad___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
lean_object* l_Lean_Meta_getTransparency(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity___boxed(lean_object*);
lean_object* l_instMonadControlTOfPure___rarg(lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__1___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar(lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_366_(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT lean_object* l_Array_indexOfAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadCoreM;
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5___closed__1;
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT uint8_t l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__2(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_indexOfAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__1___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_404_(uint8_t, uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
static lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__1;
static size_t l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2(lean_object*, size_t, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_366_(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2___closed__2;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_366_(x_3, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_free_object(x_1);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
lean_free_object(x_1);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_usize_shift_right(x_2, x_6);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = 5;
x_22 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2___closed__2;
x_23 = lean_usize_land(x_2, x_22);
x_24 = lean_usize_to_nat(x_23);
x_25 = lean_box(2);
x_26 = lean_array_get(x_25, x_20, x_24);
lean_dec(x_24);
lean_dec(x_20);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_366_(x_3, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
return x_31;
}
}
case 1:
{
lean_object* x_32; size_t x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_usize_shift_right(x_2, x_21);
x_1 = x_32;
x_2 = x_33;
goto _start;
}
default: 
{
lean_object* x_35; 
x_35 = lean_box(0);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__3(x_36, x_37, lean_box(0), x_38, x_3);
lean_dec(x_37);
lean_dec(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; 
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_Lean_Meta_TransparencyMode_hash(x_3);
x_7 = l_Lean_Expr_hash(x_4);
if (lean_obj_tag(x_5) == 0)
{
uint64_t x_8; uint64_t x_9; uint64_t x_10; size_t x_11; lean_object* x_12; 
x_8 = 11;
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = lean_uint64_mix_hash(x_6, x_9);
x_11 = lean_uint64_to_usize(x_10);
x_12 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2(x_1, x_11, x_2);
return x_12;
}
else
{
lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_uint64_of_nat(x_13);
x_15 = 13;
x_16 = lean_uint64_mix_hash(x_14, x_15);
x_17 = lean_uint64_mix_hash(x_7, x_16);
x_18 = lean_uint64_mix_hash(x_6, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2(x_1, x_19, x_2);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__6(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; uint64_t x_20; uint64_t x_21; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = 1;
x_12 = lean_usize_sub(x_1, x_11);
x_13 = 5;
x_14 = lean_usize_mul(x_13, x_12);
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
uint64_t x_22; uint64_t x_23; uint64_t x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_22 = 11;
x_23 = lean_uint64_mix_hash(x_21, x_22);
x_24 = lean_uint64_mix_hash(x_20, x_23);
x_25 = lean_uint64_to_usize(x_24);
x_26 = lean_usize_shift_right(x_25, x_14);
x_27 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(x_6, x_26, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_16;
x_6 = x_27;
goto _start;
}
else
{
lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; size_t x_35; size_t x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_19, 0);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_uint64_of_nat(x_29);
lean_dec(x_29);
x_31 = 13;
x_32 = lean_uint64_mix_hash(x_30, x_31);
x_33 = lean_uint64_mix_hash(x_21, x_32);
x_34 = lean_uint64_mix_hash(x_20, x_33);
x_35 = lean_uint64_to_usize(x_34);
x_36 = lean_usize_shift_right(x_35, x_14);
x_37 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(x_6, x_36, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_16;
x_6 = x_37;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_366_(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2___closed__2;
x_11 = lean_usize_land(x_2, x_10);
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
x_16 = lean_box(0);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_366_(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_366_(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_9);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = lean_usize_shift_right(x_2, x_9);
x_42 = lean_usize_add(x_3, x_8);
x_43 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2___closed__2;
x_52 = lean_usize_land(x_2, x_51);
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(0);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_366_(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = lean_usize_shift_right(x_2, x_50);
x_74 = lean_usize_add(x_3, x_49);
x_75 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_1);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; size_t x_85; uint8_t x_86; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__7(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = lean_usize_dec_le(x_85, x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
x_88 = lean_unsigned_to_nat(4u);
x_89 = lean_nat_dec_lt(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5___closed__1;
x_93 = l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__6(x_3, x_90, x_91, lean_box(0), x_83, x_92);
lean_dec(x_91);
lean_dec(x_90);
return x_93;
}
else
{
return x_84;
}
}
else
{
return x_84;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; uint8_t x_100; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__7(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = lean_usize_dec_le(x_99, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
x_102 = lean_unsigned_to_nat(4u);
x_103 = lean_nat_dec_lt(x_101, x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec(x_98);
x_106 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5___closed__1;
x_107 = l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__6(x_3, x_104, x_105, lean_box(0), x_97, x_106);
lean_dec(x_105);
lean_dec(x_104);
return x_107;
}
else
{
return x_98;
}
}
else
{
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; 
x_4 = 1;
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = l_Lean_Meta_TransparencyMode_hash(x_5);
x_9 = l_Lean_Expr_hash(x_6);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint64_t x_10; uint64_t x_11; uint64_t x_12; size_t x_13; lean_object* x_14; 
x_10 = 11;
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_12 = lean_uint64_mix_hash(x_8, x_11);
x_13 = lean_uint64_to_usize(x_12);
x_14 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(x_1, x_13, x_4, x_2, x_3);
return x_14;
}
else
{
lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; size_t x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_uint64_of_nat(x_15);
lean_dec(x_15);
x_17 = 13;
x_18 = lean_uint64_mix_hash(x_16, x_17);
x_19 = lean_uint64_mix_hash(x_9, x_18);
x_20 = lean_uint64_mix_hash(x_8, x_19);
x_21 = lean_uint64_to_usize(x_20);
x_22 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(x_1, x_21, x_4, x_2, x_3);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Lean_Meta_getTransparency(x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_5, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_2);
x_19 = lean_unbox(x_10);
lean_dec(x_10);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_19);
x_20 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__1(x_17, x_18);
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
x_32 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(x_31, x_18, x_22);
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
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_38 = lean_ctor_get(x_26, 0);
x_39 = lean_ctor_get(x_26, 2);
x_40 = lean_ctor_get(x_26, 3);
x_41 = lean_ctor_get(x_26, 4);
x_42 = lean_ctor_get(x_26, 5);
x_43 = lean_ctor_get(x_26, 6);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_44);
lean_inc(x_38);
lean_dec(x_26);
lean_inc(x_22);
x_45 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(x_44, x_18, x_22);
x_46 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_39);
lean_ctor_set(x_46, 3, x_40);
lean_ctor_set(x_46, 4, x_41);
lean_ctor_set(x_46, 5, x_42);
lean_ctor_set(x_46, 6, x_43);
lean_ctor_set(x_25, 1, x_46);
x_47 = lean_st_ref_set(x_5, x_25, x_27);
lean_dec(x_5);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_22);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_51 = lean_ctor_get(x_25, 0);
x_52 = lean_ctor_get(x_25, 2);
x_53 = lean_ctor_get(x_25, 3);
x_54 = lean_ctor_get(x_25, 4);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_25);
x_55 = lean_ctor_get(x_26, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_26, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_26, 3);
lean_inc(x_57);
x_58 = lean_ctor_get(x_26, 4);
lean_inc(x_58);
x_59 = lean_ctor_get(x_26, 5);
lean_inc(x_59);
x_60 = lean_ctor_get(x_26, 6);
lean_inc(x_60);
x_61 = lean_ctor_get(x_26, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 lean_ctor_release(x_26, 3);
 lean_ctor_release(x_26, 4);
 lean_ctor_release(x_26, 5);
 lean_ctor_release(x_26, 6);
 x_62 = x_26;
} else {
 lean_dec_ref(x_26);
 x_62 = lean_box(0);
}
lean_inc(x_22);
x_63 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(x_61, x_18, x_22);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 7, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_55);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_56);
lean_ctor_set(x_64, 3, x_57);
lean_ctor_set(x_64, 4, x_58);
lean_ctor_set(x_64, 5, x_59);
lean_ctor_set(x_64, 6, x_60);
x_65 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_65, 0, x_51);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_52);
lean_ctor_set(x_65, 3, x_53);
lean_ctor_set(x_65, 4, x_54);
x_66 = lean_st_ref_set(x_5, x_65, x_27);
lean_dec(x_5);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_22);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_dec(x_18);
lean_dec(x_5);
x_70 = !lean_is_exclusive(x_21);
if (x_70 == 0)
{
return x_21;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_21, 0);
x_72 = lean_ctor_get(x_21, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_21);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_74 = lean_ctor_get(x_20, 0);
lean_inc(x_74);
lean_dec(x_20);
lean_ctor_set(x_12, 0, x_74);
return x_12;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; 
x_75 = lean_ctor_get(x_12, 0);
x_76 = lean_ctor_get(x_12, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_12);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_79, 0, x_1);
lean_ctor_set(x_79, 1, x_2);
x_80 = lean_unbox(x_10);
lean_dec(x_10);
lean_ctor_set_uint8(x_79, sizeof(void*)*2, x_80);
x_81 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__1(x_78, x_79);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
lean_inc(x_5);
x_82 = lean_apply_5(x_3, x_4, x_5, x_6, x_7, x_76);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_st_ref_take(x_5, x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_89 = lean_ctor_get(x_86, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_86, 2);
lean_inc(x_90);
x_91 = lean_ctor_get(x_86, 3);
lean_inc(x_91);
x_92 = lean_ctor_get(x_86, 4);
lean_inc(x_92);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 lean_ctor_release(x_86, 2);
 lean_ctor_release(x_86, 3);
 lean_ctor_release(x_86, 4);
 x_93 = x_86;
} else {
 lean_dec_ref(x_86);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get(x_87, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_87, 2);
lean_inc(x_95);
x_96 = lean_ctor_get(x_87, 3);
lean_inc(x_96);
x_97 = lean_ctor_get(x_87, 4);
lean_inc(x_97);
x_98 = lean_ctor_get(x_87, 5);
lean_inc(x_98);
x_99 = lean_ctor_get(x_87, 6);
lean_inc(x_99);
x_100 = lean_ctor_get(x_87, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 lean_ctor_release(x_87, 2);
 lean_ctor_release(x_87, 3);
 lean_ctor_release(x_87, 4);
 lean_ctor_release(x_87, 5);
 lean_ctor_release(x_87, 6);
 x_101 = x_87;
} else {
 lean_dec_ref(x_87);
 x_101 = lean_box(0);
}
lean_inc(x_83);
x_102 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(x_100, x_79, x_83);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 7, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_94);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set(x_103, 2, x_95);
lean_ctor_set(x_103, 3, x_96);
lean_ctor_set(x_103, 4, x_97);
lean_ctor_set(x_103, 5, x_98);
lean_ctor_set(x_103, 6, x_99);
if (lean_is_scalar(x_93)) {
 x_104 = lean_alloc_ctor(0, 5, 0);
} else {
 x_104 = x_93;
}
lean_ctor_set(x_104, 0, x_89);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set(x_104, 2, x_90);
lean_ctor_set(x_104, 3, x_91);
lean_ctor_set(x_104, 4, x_92);
x_105 = lean_st_ref_set(x_5, x_104, x_88);
lean_dec(x_5);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_107 = x_105;
} else {
 lean_dec_ref(x_105);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_83);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_79);
lean_dec(x_5);
x_109 = lean_ctor_get(x_82, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_82, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_111 = x_82;
} else {
 lean_dec_ref(x_82);
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
else
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_79);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_113 = lean_ctor_get(x_81, 0);
lean_inc(x_113);
lean_dec(x_81);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_76);
return x_114;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__6(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_indexOfAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_nat_dec_eq(x_6, x_1);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
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
LEAN_EXPORT uint8_t l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(lean_object* x_1, lean_object* x_2) {
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
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__3(x_2, x_1, x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Array_indexOfAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_indexOfAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_decLt___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1___closed__1;
lean_inc(x_2);
x_6 = l_Array_qpartition___rarg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__1;
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
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_12 = lean_array_fget(x_3, x_5);
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
x_14 = lean_ctor_get_uint8(x_12, sizeof(void*)*1 + 1);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_12, sizeof(void*)*1 + 2);
x_17 = lean_ctor_get_uint8(x_12, sizeof(void*)*1 + 3);
x_18 = lean_ctor_get_uint8(x_12, sizeof(void*)*1 + 4);
x_19 = lean_ctor_get_uint8(x_12, sizeof(void*)*1 + 5);
x_20 = lean_nat_add(x_5, x_10);
if (x_14 == 0)
{
uint8_t x_21; 
x_21 = l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(x_2, x_5);
lean_dec(x_5);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_15);
x_22 = lean_array_push(x_7, x_12);
x_4 = x_11;
x_5 = x_20;
x_6 = lean_box(0);
x_7 = x_22;
goto _start;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_12, 0);
lean_dec(x_25);
x_26 = 1;
lean_ctor_set_uint8(x_12, sizeof(void*)*1 + 1, x_26);
x_27 = lean_array_push(x_7, x_12);
x_4 = x_11;
x_5 = x_20;
x_6 = lean_box(0);
x_7 = x_27;
goto _start;
}
else
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_12);
x_29 = 1;
x_30 = lean_alloc_ctor(0, 1, 6);
lean_ctor_set(x_30, 0, x_15);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_13);
lean_ctor_set_uint8(x_30, sizeof(void*)*1 + 1, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*1 + 2, x_16);
lean_ctor_set_uint8(x_30, sizeof(void*)*1 + 3, x_17);
lean_ctor_set_uint8(x_30, sizeof(void*)*1 + 4, x_18);
lean_ctor_set_uint8(x_30, sizeof(void*)*1 + 5, x_19);
x_31 = lean_array_push(x_7, x_30);
x_4 = x_11;
x_5 = x_20;
x_6 = lean_box(0);
x_7 = x_31;
goto _start;
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_15);
lean_dec(x_5);
x_33 = lean_array_push(x_7, x_12);
x_4 = x_11;
x_5 = x_20;
x_6 = lean_box(0);
x_7 = x_33;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_7, x_6);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_5, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_113; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_5, x_18);
lean_dec(x_5);
x_26 = lean_ctor_get(x_9, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_28 = x_9;
} else {
 lean_dec_ref(x_9);
 x_28 = lean_box(0);
}
x_113 = l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(x_2, x_6);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_28);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_26);
lean_ctor_set(x_114, 1, x_27);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_20 = x_115;
x_21 = x_14;
goto block_25;
}
else
{
uint8_t x_116; 
x_116 = lean_nat_dec_lt(x_6, x_4);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = l_Lean_instInhabitedExpr;
x_118 = l_outOfBounds___rarg(x_117);
x_29 = x_118;
goto block_112;
}
else
{
lean_object* x_119; 
x_119 = lean_array_fget(x_3, x_6);
x_29 = x_119;
goto block_112;
}
}
block_25:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_5 = x_19;
x_6 = x_23;
x_9 = x_22;
x_14 = x_21;
goto _start;
}
block_112:
{
lean_object* x_30; 
x_30 = l_Array_indexOfAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__1(x_1, x_29, x_16);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_29);
if (lean_is_scalar(x_28)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_28;
}
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_27);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_20 = x_32;
x_21 = x_14;
goto block_25;
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_29);
x_35 = lean_infer_type(x_29, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_38 = lean_whnf(x_36, x_10, x_11, x_12, x_13, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Expr_isForall(x_39);
lean_dec(x_39);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_34);
lean_dec(x_29);
if (lean_is_scalar(x_28)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_28;
}
lean_ctor_set(x_42, 0, x_26);
lean_ctor_set(x_42, 1, x_27);
lean_ctor_set(x_30, 0, x_42);
x_20 = x_30;
x_21 = x_40;
goto block_25;
}
else
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_array_get_size(x_27);
x_44 = lean_nat_dec_lt(x_34, x_43);
lean_dec(x_43);
x_45 = l_Lean_Expr_fvarId_x21(x_29);
lean_dec(x_29);
x_46 = lean_box(0);
x_47 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_26, x_45, x_46);
if (x_44 == 0)
{
lean_object* x_48; 
lean_dec(x_34);
if (lean_is_scalar(x_28)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_28;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_27);
lean_ctor_set(x_30, 0, x_48);
x_20 = x_30;
x_21 = x_40;
goto block_25;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_array_fget(x_27, x_34);
x_50 = lean_array_fset(x_27, x_34, x_46);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_52 = 1;
lean_ctor_set_uint8(x_49, sizeof(void*)*1 + 4, x_52);
x_53 = lean_array_fset(x_50, x_34, x_49);
lean_dec(x_34);
if (lean_is_scalar(x_28)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_28;
}
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_30, 0, x_54);
x_20 = x_30;
x_21 = x_40;
goto block_25;
}
else
{
uint8_t x_55; uint8_t x_56; lean_object* x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_55 = lean_ctor_get_uint8(x_49, sizeof(void*)*1);
x_56 = lean_ctor_get_uint8(x_49, sizeof(void*)*1 + 1);
x_57 = lean_ctor_get(x_49, 0);
x_58 = lean_ctor_get_uint8(x_49, sizeof(void*)*1 + 2);
x_59 = lean_ctor_get_uint8(x_49, sizeof(void*)*1 + 3);
x_60 = lean_ctor_get_uint8(x_49, sizeof(void*)*1 + 5);
lean_inc(x_57);
lean_dec(x_49);
x_61 = 1;
x_62 = lean_alloc_ctor(0, 1, 6);
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_55);
lean_ctor_set_uint8(x_62, sizeof(void*)*1 + 1, x_56);
lean_ctor_set_uint8(x_62, sizeof(void*)*1 + 2, x_58);
lean_ctor_set_uint8(x_62, sizeof(void*)*1 + 3, x_59);
lean_ctor_set_uint8(x_62, sizeof(void*)*1 + 4, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*1 + 5, x_60);
x_63 = lean_array_fset(x_50, x_34, x_62);
lean_dec(x_34);
if (lean_is_scalar(x_28)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_28;
}
lean_ctor_set(x_64, 0, x_47);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_30, 0, x_64);
x_20 = x_30;
x_21 = x_40;
goto block_25;
}
}
}
}
else
{
uint8_t x_65; 
lean_free_object(x_30);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_65 = !lean_is_exclusive(x_38);
if (x_65 == 0)
{
return x_38;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_38, 0);
x_67 = lean_ctor_get(x_38, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_38);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_free_object(x_30);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_69 = !lean_is_exclusive(x_35);
if (x_69 == 0)
{
return x_35;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_35, 0);
x_71 = lean_ctor_get(x_35, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_35);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_30, 0);
lean_inc(x_73);
lean_dec(x_30);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_29);
x_74 = lean_infer_type(x_29, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_77 = lean_whnf(x_75, x_10, x_11, x_12, x_13, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_Expr_isForall(x_78);
lean_dec(x_78);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_73);
lean_dec(x_29);
if (lean_is_scalar(x_28)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_28;
}
lean_ctor_set(x_81, 0, x_26);
lean_ctor_set(x_81, 1, x_27);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_20 = x_82;
x_21 = x_79;
goto block_25;
}
else
{
lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_83 = lean_array_get_size(x_27);
x_84 = lean_nat_dec_lt(x_73, x_83);
lean_dec(x_83);
x_85 = l_Lean_Expr_fvarId_x21(x_29);
lean_dec(x_29);
x_86 = lean_box(0);
x_87 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_26, x_85, x_86);
if (x_84 == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_73);
if (lean_is_scalar(x_28)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_28;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_27);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_20 = x_89;
x_21 = x_79;
goto block_25;
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_93; lean_object* x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_90 = lean_array_fget(x_27, x_73);
x_91 = lean_array_fset(x_27, x_73, x_86);
x_92 = lean_ctor_get_uint8(x_90, sizeof(void*)*1);
x_93 = lean_ctor_get_uint8(x_90, sizeof(void*)*1 + 1);
x_94 = lean_ctor_get(x_90, 0);
lean_inc(x_94);
x_95 = lean_ctor_get_uint8(x_90, sizeof(void*)*1 + 2);
x_96 = lean_ctor_get_uint8(x_90, sizeof(void*)*1 + 3);
x_97 = lean_ctor_get_uint8(x_90, sizeof(void*)*1 + 5);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 x_98 = x_90;
} else {
 lean_dec_ref(x_90);
 x_98 = lean_box(0);
}
x_99 = 1;
if (lean_is_scalar(x_98)) {
 x_100 = lean_alloc_ctor(0, 1, 6);
} else {
 x_100 = x_98;
}
lean_ctor_set(x_100, 0, x_94);
lean_ctor_set_uint8(x_100, sizeof(void*)*1, x_92);
lean_ctor_set_uint8(x_100, sizeof(void*)*1 + 1, x_93);
lean_ctor_set_uint8(x_100, sizeof(void*)*1 + 2, x_95);
lean_ctor_set_uint8(x_100, sizeof(void*)*1 + 3, x_96);
lean_ctor_set_uint8(x_100, sizeof(void*)*1 + 4, x_99);
lean_ctor_set_uint8(x_100, sizeof(void*)*1 + 5, x_97);
x_101 = lean_array_fset(x_91, x_73, x_100);
lean_dec(x_73);
if (lean_is_scalar(x_28)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_28;
}
lean_ctor_set(x_102, 0, x_87);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_20 = x_103;
x_21 = x_79;
goto block_25;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_73);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_104 = lean_ctor_get(x_77, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_77, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_106 = x_77;
} else {
 lean_dec_ref(x_77);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_73);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_108 = lean_ctor_get(x_74, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_74, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_110 = x_74;
} else {
 lean_dec_ref(x_74);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
}
}
}
else
{
lean_object* x_120; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_9);
lean_ctor_set(x_120, 1, x_14);
return x_120;
}
}
else
{
lean_object* x_121; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_9);
lean_ctor_set(x_121, 1, x_14);
return x_121;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Decidable", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___closed__2;
x_9 = l_Lean_Expr_isAppOf(x_2, x_8);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_isFVar(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Expr_fvarId_x21(x_2);
x_6 = l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(x_1, x_5);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = 1;
return x_8;
}
}
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_7, x_6);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_5, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_184; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_5, x_18);
lean_dec(x_5);
x_26 = lean_ctor_get(x_9, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_28 = x_9;
} else {
 lean_dec_ref(x_9);
 x_28 = lean_box(0);
}
x_184 = lean_nat_dec_lt(x_6, x_4);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; 
x_185 = l_Lean_instInhabitedExpr;
x_186 = l_outOfBounds___rarg(x_185);
x_29 = x_186;
goto block_183;
}
else
{
lean_object* x_187; 
x_187 = lean_array_fget(x_2, x_6);
x_29 = x_187;
goto block_183;
}
block_25:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_5 = x_19;
x_6 = x_23;
x_9 = x_22;
x_14 = x_21;
goto _start;
}
block_183:
{
lean_object* x_30; 
lean_inc(x_10);
x_30 = l_Lean_Meta_getFVarLocalDecl(x_29, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_152; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_LocalDecl_type(x_31);
x_34 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(x_2, x_33);
x_35 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(x_27, x_34);
lean_dec(x_27);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_33);
x_152 = l_Lean_Meta_isProp(x_33, x_10, x_11, x_12, x_13, x_32);
if (lean_obj_tag(x_26) == 0)
{
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; uint8_t x_156; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = 0;
x_156 = lean_unbox(x_153);
lean_dec(x_153);
x_36 = x_155;
x_37 = x_156;
x_38 = x_154;
goto block_151;
}
else
{
uint8_t x_157; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_157 = !lean_is_exclusive(x_152);
if (x_157 == 0)
{
return x_152;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_152, 0);
x_159 = lean_ctor_get(x_152, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_152);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
else
{
lean_object* x_161; lean_object* x_162; 
lean_inc(x_26);
x_161 = lean_alloc_closure((void*)(l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__2___boxed), 2, 1);
lean_closure_set(x_161, 0, x_26);
x_162 = lean_find_expr(x_161, x_33);
lean_dec(x_161);
if (lean_obj_tag(x_162) == 0)
{
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; uint8_t x_166; 
x_163 = lean_ctor_get(x_152, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_152, 1);
lean_inc(x_164);
lean_dec(x_152);
x_165 = 0;
x_166 = lean_unbox(x_163);
lean_dec(x_163);
x_36 = x_165;
x_37 = x_166;
x_38 = x_164;
goto block_151;
}
else
{
uint8_t x_167; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_167 = !lean_is_exclusive(x_152);
if (x_167 == 0)
{
return x_152;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_152, 0);
x_169 = lean_ctor_get(x_152, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_152);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
else
{
lean_dec(x_162);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; uint8_t x_174; 
x_171 = lean_ctor_get(x_152, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_152, 1);
lean_inc(x_172);
lean_dec(x_152);
x_173 = 1;
x_174 = lean_unbox(x_171);
lean_dec(x_171);
x_36 = x_173;
x_37 = x_174;
x_38 = x_172;
goto block_151;
}
else
{
uint8_t x_175; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_175 = !lean_is_exclusive(x_152);
if (x_175 == 0)
{
return x_152;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_152, 0);
x_177 = lean_ctor_get(x_152, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_152);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
}
block_151:
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_39 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__1;
x_40 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_33);
x_41 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_33, x_39, x_40, x_10, x_11, x_12, x_13, x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_LocalDecl_binderInfo(x_31);
lean_dec(x_31);
x_45 = lean_alloc_ctor(0, 1, 6);
lean_ctor_set(x_45, 0, x_34);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*1 + 1, x_40);
lean_ctor_set_uint8(x_45, sizeof(void*)*1 + 2, x_37);
x_46 = lean_unbox(x_42);
lean_dec(x_42);
lean_ctor_set_uint8(x_45, sizeof(void*)*1 + 3, x_46);
lean_ctor_set_uint8(x_45, sizeof(void*)*1 + 4, x_40);
lean_ctor_set_uint8(x_45, sizeof(void*)*1 + 5, x_36);
x_47 = lean_array_push(x_35, x_45);
x_48 = 3;
x_49 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_404_(x_44, x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_33);
if (lean_is_scalar(x_28)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_28;
}
lean_ctor_set(x_50, 0, x_26);
lean_ctor_set(x_50, 1, x_47);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_20 = x_51;
x_21 = x_43;
goto block_25;
}
else
{
lean_object* x_52; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_33);
x_52 = l_Lean_Meta_isClass_x3f(x_33, x_10, x_11, x_12, x_13, x_43);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_33);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
if (lean_is_scalar(x_28)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_28;
}
lean_ctor_set(x_55, 0, x_26);
lean_ctor_set(x_55, 1, x_47);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_20 = x_56;
x_21 = x_54;
goto block_25;
}
else
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
lean_dec(x_52);
x_58 = !lean_is_exclusive(x_53);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_53, 0);
x_60 = lean_st_ref_get(x_13, x_57);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_getOutParamPositions_x3f(x_63, x_59);
lean_dec(x_59);
lean_dec(x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
lean_dec(x_33);
if (lean_is_scalar(x_28)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_28;
}
lean_ctor_set(x_65, 0, x_26);
lean_ctor_set(x_65, 1, x_47);
lean_ctor_set(x_53, 0, x_65);
x_20 = x_53;
x_21 = x_62;
goto block_25;
}
else
{
uint8_t x_66; 
lean_free_object(x_53);
x_66 = !lean_is_exclusive(x_64);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_64, 0);
x_68 = l_Array_isEmpty___rarg(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_33, x_16);
x_70 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__2;
lean_inc(x_69);
x_71 = lean_mk_array(x_69, x_70);
x_72 = lean_nat_sub(x_69, x_18);
lean_dec(x_69);
x_73 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_33, x_71, x_72);
x_74 = lean_array_get_size(x_73);
if (lean_is_scalar(x_28)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_28;
}
lean_ctor_set(x_75, 0, x_26);
lean_ctor_set(x_75, 1, x_47);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_74);
x_76 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1(x_2, x_67, x_73, x_74, x_74, x_16, x_74, x_18, x_75, x_10, x_11, x_12, x_13, x_62);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_67);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = !lean_is_exclusive(x_77);
if (x_79 == 0)
{
lean_ctor_set(x_64, 0, x_77);
x_20 = x_64;
x_21 = x_78;
goto block_25;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_77, 0);
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_77);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_64, 0, x_82);
x_20 = x_64;
x_21 = x_78;
goto block_25;
}
}
else
{
uint8_t x_83; 
lean_free_object(x_64);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_83 = !lean_is_exclusive(x_76);
if (x_83 == 0)
{
return x_76;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_76, 0);
x_85 = lean_ctor_get(x_76, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_76);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; 
lean_dec(x_67);
lean_dec(x_33);
if (lean_is_scalar(x_28)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_28;
}
lean_ctor_set(x_87, 0, x_26);
lean_ctor_set(x_87, 1, x_47);
lean_ctor_set(x_64, 0, x_87);
x_20 = x_64;
x_21 = x_62;
goto block_25;
}
}
else
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_64, 0);
lean_inc(x_88);
lean_dec(x_64);
x_89 = l_Array_isEmpty___rarg(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_90 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_33, x_16);
x_91 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__2;
lean_inc(x_90);
x_92 = lean_mk_array(x_90, x_91);
x_93 = lean_nat_sub(x_90, x_18);
lean_dec(x_90);
x_94 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_33, x_92, x_93);
x_95 = lean_array_get_size(x_94);
if (lean_is_scalar(x_28)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_28;
}
lean_ctor_set(x_96, 0, x_26);
lean_ctor_set(x_96, 1, x_47);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_95);
x_97 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1(x_2, x_88, x_94, x_95, x_95, x_16, x_95, x_18, x_96, x_10, x_11, x_12, x_13, x_62);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_88);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_102 = x_98;
} else {
 lean_dec_ref(x_98);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_20 = x_104;
x_21 = x_99;
goto block_25;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_105 = lean_ctor_get(x_97, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_97, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_107 = x_97;
} else {
 lean_dec_ref(x_97);
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
lean_object* x_109; lean_object* x_110; 
lean_dec(x_88);
lean_dec(x_33);
if (lean_is_scalar(x_28)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_28;
}
lean_ctor_set(x_109, 0, x_26);
lean_ctor_set(x_109, 1, x_47);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
x_20 = x_110;
x_21 = x_62;
goto block_25;
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_53, 0);
lean_inc(x_111);
lean_dec(x_53);
x_112 = lean_st_ref_get(x_13, x_57);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
lean_dec(x_113);
x_116 = l_Lean_getOutParamPositions_x3f(x_115, x_111);
lean_dec(x_111);
lean_dec(x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_33);
if (lean_is_scalar(x_28)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_28;
}
lean_ctor_set(x_117, 0, x_26);
lean_ctor_set(x_117, 1, x_47);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_117);
x_20 = x_118;
x_21 = x_114;
goto block_25;
}
else
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_119 = lean_ctor_get(x_116, 0);
lean_inc(x_119);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_120 = x_116;
} else {
 lean_dec_ref(x_116);
 x_120 = lean_box(0);
}
x_121 = l_Array_isEmpty___rarg(x_119);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_122 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_33, x_16);
x_123 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__2;
lean_inc(x_122);
x_124 = lean_mk_array(x_122, x_123);
x_125 = lean_nat_sub(x_122, x_18);
lean_dec(x_122);
x_126 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_33, x_124, x_125);
x_127 = lean_array_get_size(x_126);
if (lean_is_scalar(x_28)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_28;
}
lean_ctor_set(x_128, 0, x_26);
lean_ctor_set(x_128, 1, x_47);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_127);
x_129 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1(x_2, x_119, x_126, x_127, x_127, x_16, x_127, x_18, x_128, x_10, x_11, x_12, x_13, x_114);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_119);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_134 = x_130;
} else {
 lean_dec_ref(x_130);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
if (lean_is_scalar(x_120)) {
 x_136 = lean_alloc_ctor(1, 1, 0);
} else {
 x_136 = x_120;
}
lean_ctor_set(x_136, 0, x_135);
x_20 = x_136;
x_21 = x_131;
goto block_25;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_120);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_137 = lean_ctor_get(x_129, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_129, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_139 = x_129;
} else {
 lean_dec_ref(x_129);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_119);
lean_dec(x_33);
if (lean_is_scalar(x_28)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_28;
}
lean_ctor_set(x_141, 0, x_26);
lean_ctor_set(x_141, 1, x_47);
if (lean_is_scalar(x_120)) {
 x_142 = lean_alloc_ctor(1, 1, 0);
} else {
 x_142 = x_120;
}
lean_ctor_set(x_142, 0, x_141);
x_20 = x_142;
x_21 = x_114;
goto block_25;
}
}
}
}
}
else
{
uint8_t x_143; 
lean_dec(x_47);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_143 = !lean_is_exclusive(x_52);
if (x_143 == 0)
{
return x_52;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_52, 0);
x_145 = lean_ctor_get(x_52, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_52);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
}
else
{
uint8_t x_147; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_147 = !lean_is_exclusive(x_41);
if (x_147 == 0)
{
return x_41;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_41, 0);
x_149 = lean_ctor_get(x_41, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_41);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
}
else
{
uint8_t x_179; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_179 = !lean_is_exclusive(x_30);
if (x_179 == 0)
{
return x_30;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_30, 0);
x_181 = lean_ctor_get(x_30, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_30);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
}
}
else
{
lean_object* x_188; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_9);
lean_ctor_set(x_188, 1, x_14);
return x_188;
}
}
else
{
lean_object* x_189; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_9);
lean_ctor_set(x_189, 1, x_14);
return x_189;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_6, x_5);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_4, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_183; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_4, x_17);
lean_dec(x_4);
x_25 = lean_ctor_get(x_8, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_27 = x_8;
} else {
 lean_dec_ref(x_8);
 x_27 = lean_box(0);
}
x_183 = lean_nat_dec_lt(x_5, x_3);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; 
x_184 = l_Lean_instInhabitedExpr;
x_185 = l_outOfBounds___rarg(x_184);
x_28 = x_185;
goto block_182;
}
else
{
lean_object* x_186; 
x_186 = lean_array_fget(x_2, x_5);
x_28 = x_186;
goto block_182;
}
block_24:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_18;
x_5 = x_22;
x_8 = x_21;
x_13 = x_20;
goto _start;
}
block_182:
{
lean_object* x_29; 
lean_inc(x_9);
x_29 = l_Lean_Meta_getFVarLocalDecl(x_28, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_151; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_LocalDecl_type(x_30);
x_33 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(x_2, x_32);
x_34 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(x_26, x_33);
lean_dec(x_26);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_32);
x_151 = l_Lean_Meta_isProp(x_32, x_9, x_10, x_11, x_12, x_31);
if (lean_obj_tag(x_25) == 0)
{
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; uint8_t x_155; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = 0;
x_155 = lean_unbox(x_152);
lean_dec(x_152);
x_35 = x_154;
x_36 = x_155;
x_37 = x_153;
goto block_150;
}
else
{
uint8_t x_156; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_156 = !lean_is_exclusive(x_151);
if (x_156 == 0)
{
return x_151;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_151, 0);
x_158 = lean_ctor_get(x_151, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_151);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
else
{
lean_object* x_160; lean_object* x_161; 
lean_inc(x_25);
x_160 = lean_alloc_closure((void*)(l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__2___boxed), 2, 1);
lean_closure_set(x_160, 0, x_25);
x_161 = lean_find_expr(x_160, x_32);
lean_dec(x_160);
if (lean_obj_tag(x_161) == 0)
{
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_162; lean_object* x_163; uint8_t x_164; uint8_t x_165; 
x_162 = lean_ctor_get(x_151, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_151, 1);
lean_inc(x_163);
lean_dec(x_151);
x_164 = 0;
x_165 = lean_unbox(x_162);
lean_dec(x_162);
x_35 = x_164;
x_36 = x_165;
x_37 = x_163;
goto block_150;
}
else
{
uint8_t x_166; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_166 = !lean_is_exclusive(x_151);
if (x_166 == 0)
{
return x_151;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_151, 0);
x_168 = lean_ctor_get(x_151, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_151);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
else
{
lean_dec(x_161);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; uint8_t x_173; 
x_170 = lean_ctor_get(x_151, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_151, 1);
lean_inc(x_171);
lean_dec(x_151);
x_172 = 1;
x_173 = lean_unbox(x_170);
lean_dec(x_170);
x_35 = x_172;
x_36 = x_173;
x_37 = x_171;
goto block_150;
}
else
{
uint8_t x_174; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_174 = !lean_is_exclusive(x_151);
if (x_174 == 0)
{
return x_151;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_151, 0);
x_176 = lean_ctor_get(x_151, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_151);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
}
block_150:
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_38 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__1;
x_39 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_32);
x_40 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_32, x_38, x_39, x_9, x_10, x_11, x_12, x_37);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_LocalDecl_binderInfo(x_30);
lean_dec(x_30);
x_44 = lean_alloc_ctor(0, 1, 6);
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*1 + 1, x_39);
lean_ctor_set_uint8(x_44, sizeof(void*)*1 + 2, x_36);
x_45 = lean_unbox(x_41);
lean_dec(x_41);
lean_ctor_set_uint8(x_44, sizeof(void*)*1 + 3, x_45);
lean_ctor_set_uint8(x_44, sizeof(void*)*1 + 4, x_39);
lean_ctor_set_uint8(x_44, sizeof(void*)*1 + 5, x_35);
x_46 = lean_array_push(x_34, x_44);
x_47 = 3;
x_48 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_404_(x_43, x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_32);
if (lean_is_scalar(x_27)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_27;
}
lean_ctor_set(x_49, 0, x_25);
lean_ctor_set(x_49, 1, x_46);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_19 = x_50;
x_20 = x_42;
goto block_24;
}
else
{
lean_object* x_51; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_32);
x_51 = l_Lean_Meta_isClass_x3f(x_32, x_9, x_10, x_11, x_12, x_42);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_32);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
if (lean_is_scalar(x_27)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_27;
}
lean_ctor_set(x_54, 0, x_25);
lean_ctor_set(x_54, 1, x_46);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_19 = x_55;
x_20 = x_53;
goto block_24;
}
else
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_dec(x_51);
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_52, 0);
x_59 = lean_st_ref_get(x_12, x_56);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_getOutParamPositions_x3f(x_62, x_58);
lean_dec(x_58);
lean_dec(x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
lean_dec(x_32);
if (lean_is_scalar(x_27)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_27;
}
lean_ctor_set(x_64, 0, x_25);
lean_ctor_set(x_64, 1, x_46);
lean_ctor_set(x_52, 0, x_64);
x_19 = x_52;
x_20 = x_61;
goto block_24;
}
else
{
uint8_t x_65; 
lean_free_object(x_52);
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_63, 0);
x_67 = l_Array_isEmpty___rarg(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_68 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_32, x_15);
x_69 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__2;
lean_inc(x_68);
x_70 = lean_mk_array(x_68, x_69);
x_71 = lean_nat_sub(x_68, x_17);
lean_dec(x_68);
x_72 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_32, x_70, x_71);
x_73 = lean_array_get_size(x_72);
if (lean_is_scalar(x_27)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_27;
}
lean_ctor_set(x_74, 0, x_25);
lean_ctor_set(x_74, 1, x_46);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_73);
x_75 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1(x_2, x_66, x_72, x_73, x_73, x_15, x_73, x_17, x_74, x_9, x_10, x_11, x_12, x_61);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_66);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = !lean_is_exclusive(x_76);
if (x_78 == 0)
{
lean_ctor_set(x_63, 0, x_76);
x_19 = x_63;
x_20 = x_77;
goto block_24;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_76, 0);
x_80 = lean_ctor_get(x_76, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_76);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set(x_63, 0, x_81);
x_19 = x_63;
x_20 = x_77;
goto block_24;
}
}
else
{
uint8_t x_82; 
lean_free_object(x_63);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_82 = !lean_is_exclusive(x_75);
if (x_82 == 0)
{
return x_75;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_75, 0);
x_84 = lean_ctor_get(x_75, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_75);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; 
lean_dec(x_66);
lean_dec(x_32);
if (lean_is_scalar(x_27)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_27;
}
lean_ctor_set(x_86, 0, x_25);
lean_ctor_set(x_86, 1, x_46);
lean_ctor_set(x_63, 0, x_86);
x_19 = x_63;
x_20 = x_61;
goto block_24;
}
}
else
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_63, 0);
lean_inc(x_87);
lean_dec(x_63);
x_88 = l_Array_isEmpty___rarg(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_89 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_32, x_15);
x_90 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__2;
lean_inc(x_89);
x_91 = lean_mk_array(x_89, x_90);
x_92 = lean_nat_sub(x_89, x_17);
lean_dec(x_89);
x_93 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_32, x_91, x_92);
x_94 = lean_array_get_size(x_93);
if (lean_is_scalar(x_27)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_27;
}
lean_ctor_set(x_95, 0, x_25);
lean_ctor_set(x_95, 1, x_46);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_94);
x_96 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1(x_2, x_87, x_93, x_94, x_94, x_15, x_94, x_17, x_95, x_9, x_10, x_11, x_12, x_61);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_87);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_101 = x_97;
} else {
 lean_dec_ref(x_97);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_19 = x_103;
x_20 = x_98;
goto block_24;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_104 = lean_ctor_get(x_96, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_96, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_106 = x_96;
} else {
 lean_dec_ref(x_96);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_87);
lean_dec(x_32);
if (lean_is_scalar(x_27)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_27;
}
lean_ctor_set(x_108, 0, x_25);
lean_ctor_set(x_108, 1, x_46);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_19 = x_109;
x_20 = x_61;
goto block_24;
}
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_110 = lean_ctor_get(x_52, 0);
lean_inc(x_110);
lean_dec(x_52);
x_111 = lean_st_ref_get(x_12, x_56);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l_Lean_getOutParamPositions_x3f(x_114, x_110);
lean_dec(x_110);
lean_dec(x_114);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_32);
if (lean_is_scalar(x_27)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_27;
}
lean_ctor_set(x_116, 0, x_25);
lean_ctor_set(x_116, 1, x_46);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_19 = x_117;
x_20 = x_113;
goto block_24;
}
else
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_118 = lean_ctor_get(x_115, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 x_119 = x_115;
} else {
 lean_dec_ref(x_115);
 x_119 = lean_box(0);
}
x_120 = l_Array_isEmpty___rarg(x_118);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_121 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_32, x_15);
x_122 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__2;
lean_inc(x_121);
x_123 = lean_mk_array(x_121, x_122);
x_124 = lean_nat_sub(x_121, x_17);
lean_dec(x_121);
x_125 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_32, x_123, x_124);
x_126 = lean_array_get_size(x_125);
if (lean_is_scalar(x_27)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_27;
}
lean_ctor_set(x_127, 0, x_25);
lean_ctor_set(x_127, 1, x_46);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_126);
x_128 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1(x_2, x_118, x_125, x_126, x_126, x_15, x_126, x_17, x_127, x_9, x_10, x_11, x_12, x_113);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_118);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_133 = x_129;
} else {
 lean_dec_ref(x_129);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
if (lean_is_scalar(x_119)) {
 x_135 = lean_alloc_ctor(1, 1, 0);
} else {
 x_135 = x_119;
}
lean_ctor_set(x_135, 0, x_134);
x_19 = x_135;
x_20 = x_130;
goto block_24;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_119);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_136 = lean_ctor_get(x_128, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_128, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_138 = x_128;
} else {
 lean_dec_ref(x_128);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_118);
lean_dec(x_32);
if (lean_is_scalar(x_27)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_27;
}
lean_ctor_set(x_140, 0, x_25);
lean_ctor_set(x_140, 1, x_46);
if (lean_is_scalar(x_119)) {
 x_141 = lean_alloc_ctor(1, 1, 0);
} else {
 x_141 = x_119;
}
lean_ctor_set(x_141, 0, x_140);
x_19 = x_141;
x_20 = x_113;
goto block_24;
}
}
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_46);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_142 = !lean_is_exclusive(x_51);
if (x_142 == 0)
{
return x_51;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_51, 0);
x_144 = lean_ctor_get(x_51, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_51);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
}
else
{
uint8_t x_146; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_146 = !lean_is_exclusive(x_40);
if (x_146 == 0)
{
return x_40;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_40, 0);
x_148 = lean_ctor_get(x_40, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_40);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
}
else
{
uint8_t x_178; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_178 = !lean_is_exclusive(x_29);
if (x_178 == 0)
{
return x_29;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_29, 0);
x_180 = lean_ctor_get(x_29, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_29);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
}
}
else
{
lean_object* x_187; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_8);
lean_ctor_set(x_187, 1, x_13);
return x_187;
}
}
else
{
lean_object* x_188; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_8);
lean_ctor_set(x_188, 1, x_13);
return x_188;
}
}
}
static lean_object* _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1___closed__1;
lean_inc(x_9);
x_13 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__4(x_1, x_2, x_9, x_9, x_10, x_9, x_11, x_12, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_15, 1);
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(x_2, x_3);
x_20 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(x_17, x_19);
lean_dec(x_17);
lean_ctor_set(x_15, 1, x_19);
lean_ctor_set(x_15, 0, x_20);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(x_2, x_3);
x_23 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(x_21, x_22);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_13, 0, x_24);
return x_13;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
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
x_29 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(x_2, x_3);
x_30 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(x_27, x_29);
lean_dec(x_27);
if (lean_is_scalar(x_28)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_28;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_13);
if (x_33 == 0)
{
return x_13;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_13, 0);
x_35 = lean_ctor_get(x_13, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_13);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__1;
x_2 = l_ReaderT_instApplicativeOfMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__2;
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l_instMonadControlTOfPure___rarg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = l_Lean_Meta_getTransparency(x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_4, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_2);
lean_inc(x_1);
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
x_18 = lean_unbox(x_9);
lean_dec(x_9);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_18);
x_19 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__1(x_16, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_free_object(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_20 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__3;
x_24 = lean_alloc_closure((void*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1___boxed), 8, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = !lean_is_exclusive(x_3);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_3, 0);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
uint8_t x_28; uint8_t x_29; lean_object* x_30; 
x_28 = 1;
lean_ctor_set_uint8(x_26, 9, x_28);
x_29 = 0;
lean_inc(x_4);
x_30 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg(x_21, x_2, x_24, x_29, x_3, x_4, x_5, x_6, x_22);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_st_ref_take(x_4, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_34, 1);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_31);
x_41 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(x_40, x_17, x_31);
lean_ctor_set(x_35, 1, x_41);
x_42 = lean_st_ref_set(x_4, x_34, x_36);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
lean_ctor_set(x_42, 0, x_31);
return x_42;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_31);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_47 = lean_ctor_get(x_35, 0);
x_48 = lean_ctor_get(x_35, 2);
x_49 = lean_ctor_get(x_35, 3);
x_50 = lean_ctor_get(x_35, 4);
x_51 = lean_ctor_get(x_35, 5);
x_52 = lean_ctor_get(x_35, 6);
x_53 = lean_ctor_get(x_35, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_53);
lean_inc(x_47);
lean_dec(x_35);
lean_inc(x_31);
x_54 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(x_53, x_17, x_31);
x_55 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_48);
lean_ctor_set(x_55, 3, x_49);
lean_ctor_set(x_55, 4, x_50);
lean_ctor_set(x_55, 5, x_51);
lean_ctor_set(x_55, 6, x_52);
lean_ctor_set(x_34, 1, x_55);
x_56 = lean_st_ref_set(x_4, x_34, x_36);
lean_dec(x_4);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_31);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_60 = lean_ctor_get(x_34, 0);
x_61 = lean_ctor_get(x_34, 2);
x_62 = lean_ctor_get(x_34, 3);
x_63 = lean_ctor_get(x_34, 4);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_34);
x_64 = lean_ctor_get(x_35, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_35, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_35, 3);
lean_inc(x_66);
x_67 = lean_ctor_get(x_35, 4);
lean_inc(x_67);
x_68 = lean_ctor_get(x_35, 5);
lean_inc(x_68);
x_69 = lean_ctor_get(x_35, 6);
lean_inc(x_69);
x_70 = lean_ctor_get(x_35, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 lean_ctor_release(x_35, 2);
 lean_ctor_release(x_35, 3);
 lean_ctor_release(x_35, 4);
 lean_ctor_release(x_35, 5);
 lean_ctor_release(x_35, 6);
 x_71 = x_35;
} else {
 lean_dec_ref(x_35);
 x_71 = lean_box(0);
}
lean_inc(x_31);
x_72 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(x_70, x_17, x_31);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 7, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_64);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_65);
lean_ctor_set(x_73, 3, x_66);
lean_ctor_set(x_73, 4, x_67);
lean_ctor_set(x_73, 5, x_68);
lean_ctor_set(x_73, 6, x_69);
x_74 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_74, 0, x_60);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_74, 2, x_61);
lean_ctor_set(x_74, 3, x_62);
lean_ctor_set(x_74, 4, x_63);
x_75 = lean_st_ref_set(x_4, x_74, x_36);
lean_dec(x_4);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_31);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
uint8_t x_79; 
lean_dec(x_17);
lean_dec(x_4);
x_79 = !lean_is_exclusive(x_30);
if (x_79 == 0)
{
return x_30;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_30, 0);
x_81 = lean_ctor_get(x_30, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_30);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; 
x_83 = lean_ctor_get_uint8(x_26, 0);
x_84 = lean_ctor_get_uint8(x_26, 1);
x_85 = lean_ctor_get_uint8(x_26, 2);
x_86 = lean_ctor_get_uint8(x_26, 3);
x_87 = lean_ctor_get_uint8(x_26, 4);
x_88 = lean_ctor_get_uint8(x_26, 5);
x_89 = lean_ctor_get_uint8(x_26, 6);
x_90 = lean_ctor_get_uint8(x_26, 7);
x_91 = lean_ctor_get_uint8(x_26, 8);
x_92 = lean_ctor_get_uint8(x_26, 10);
x_93 = lean_ctor_get_uint8(x_26, 11);
x_94 = lean_ctor_get_uint8(x_26, 12);
lean_dec(x_26);
x_95 = 1;
x_96 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_96, 0, x_83);
lean_ctor_set_uint8(x_96, 1, x_84);
lean_ctor_set_uint8(x_96, 2, x_85);
lean_ctor_set_uint8(x_96, 3, x_86);
lean_ctor_set_uint8(x_96, 4, x_87);
lean_ctor_set_uint8(x_96, 5, x_88);
lean_ctor_set_uint8(x_96, 6, x_89);
lean_ctor_set_uint8(x_96, 7, x_90);
lean_ctor_set_uint8(x_96, 8, x_91);
lean_ctor_set_uint8(x_96, 9, x_95);
lean_ctor_set_uint8(x_96, 10, x_92);
lean_ctor_set_uint8(x_96, 11, x_93);
lean_ctor_set_uint8(x_96, 12, x_94);
lean_ctor_set(x_3, 0, x_96);
x_97 = 0;
lean_inc(x_4);
x_98 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg(x_21, x_2, x_24, x_97, x_3, x_4, x_5, x_6, x_22);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_st_ref_take(x_4, x_100);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
x_105 = lean_ctor_get(x_102, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_102, 2);
lean_inc(x_106);
x_107 = lean_ctor_get(x_102, 3);
lean_inc(x_107);
x_108 = lean_ctor_get(x_102, 4);
lean_inc(x_108);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 lean_ctor_release(x_102, 2);
 lean_ctor_release(x_102, 3);
 lean_ctor_release(x_102, 4);
 x_109 = x_102;
} else {
 lean_dec_ref(x_102);
 x_109 = lean_box(0);
}
x_110 = lean_ctor_get(x_103, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_103, 2);
lean_inc(x_111);
x_112 = lean_ctor_get(x_103, 3);
lean_inc(x_112);
x_113 = lean_ctor_get(x_103, 4);
lean_inc(x_113);
x_114 = lean_ctor_get(x_103, 5);
lean_inc(x_114);
x_115 = lean_ctor_get(x_103, 6);
lean_inc(x_115);
x_116 = lean_ctor_get(x_103, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 lean_ctor_release(x_103, 2);
 lean_ctor_release(x_103, 3);
 lean_ctor_release(x_103, 4);
 lean_ctor_release(x_103, 5);
 lean_ctor_release(x_103, 6);
 x_117 = x_103;
} else {
 lean_dec_ref(x_103);
 x_117 = lean_box(0);
}
lean_inc(x_99);
x_118 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(x_116, x_17, x_99);
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 7, 0);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_110);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_119, 2, x_111);
lean_ctor_set(x_119, 3, x_112);
lean_ctor_set(x_119, 4, x_113);
lean_ctor_set(x_119, 5, x_114);
lean_ctor_set(x_119, 6, x_115);
if (lean_is_scalar(x_109)) {
 x_120 = lean_alloc_ctor(0, 5, 0);
} else {
 x_120 = x_109;
}
lean_ctor_set(x_120, 0, x_105);
lean_ctor_set(x_120, 1, x_119);
lean_ctor_set(x_120, 2, x_106);
lean_ctor_set(x_120, 3, x_107);
lean_ctor_set(x_120, 4, x_108);
x_121 = lean_st_ref_set(x_4, x_120, x_104);
lean_dec(x_4);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_123 = x_121;
} else {
 lean_dec_ref(x_121);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_99);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_17);
lean_dec(x_4);
x_125 = lean_ctor_get(x_98, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_98, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_127 = x_98;
} else {
 lean_dec_ref(x_98);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; uint8_t x_136; uint8_t x_137; uint8_t x_138; uint8_t x_139; uint8_t x_140; uint8_t x_141; uint8_t x_142; uint8_t x_143; uint8_t x_144; uint8_t x_145; uint8_t x_146; uint8_t x_147; uint8_t x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; 
x_129 = lean_ctor_get(x_3, 0);
x_130 = lean_ctor_get(x_3, 1);
x_131 = lean_ctor_get(x_3, 2);
x_132 = lean_ctor_get(x_3, 3);
x_133 = lean_ctor_get(x_3, 4);
x_134 = lean_ctor_get(x_3, 5);
x_135 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_136 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_3);
x_137 = lean_ctor_get_uint8(x_129, 0);
x_138 = lean_ctor_get_uint8(x_129, 1);
x_139 = lean_ctor_get_uint8(x_129, 2);
x_140 = lean_ctor_get_uint8(x_129, 3);
x_141 = lean_ctor_get_uint8(x_129, 4);
x_142 = lean_ctor_get_uint8(x_129, 5);
x_143 = lean_ctor_get_uint8(x_129, 6);
x_144 = lean_ctor_get_uint8(x_129, 7);
x_145 = lean_ctor_get_uint8(x_129, 8);
x_146 = lean_ctor_get_uint8(x_129, 10);
x_147 = lean_ctor_get_uint8(x_129, 11);
x_148 = lean_ctor_get_uint8(x_129, 12);
if (lean_is_exclusive(x_129)) {
 x_149 = x_129;
} else {
 lean_dec_ref(x_129);
 x_149 = lean_box(0);
}
x_150 = 1;
if (lean_is_scalar(x_149)) {
 x_151 = lean_alloc_ctor(0, 0, 13);
} else {
 x_151 = x_149;
}
lean_ctor_set_uint8(x_151, 0, x_137);
lean_ctor_set_uint8(x_151, 1, x_138);
lean_ctor_set_uint8(x_151, 2, x_139);
lean_ctor_set_uint8(x_151, 3, x_140);
lean_ctor_set_uint8(x_151, 4, x_141);
lean_ctor_set_uint8(x_151, 5, x_142);
lean_ctor_set_uint8(x_151, 6, x_143);
lean_ctor_set_uint8(x_151, 7, x_144);
lean_ctor_set_uint8(x_151, 8, x_145);
lean_ctor_set_uint8(x_151, 9, x_150);
lean_ctor_set_uint8(x_151, 10, x_146);
lean_ctor_set_uint8(x_151, 11, x_147);
lean_ctor_set_uint8(x_151, 12, x_148);
x_152 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_130);
lean_ctor_set(x_152, 2, x_131);
lean_ctor_set(x_152, 3, x_132);
lean_ctor_set(x_152, 4, x_133);
lean_ctor_set(x_152, 5, x_134);
lean_ctor_set_uint8(x_152, sizeof(void*)*6, x_135);
lean_ctor_set_uint8(x_152, sizeof(void*)*6 + 1, x_136);
x_153 = 0;
lean_inc(x_4);
x_154 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg(x_21, x_2, x_24, x_153, x_152, x_4, x_5, x_6, x_22);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_st_ref_take(x_4, x_156);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_157, 1);
lean_inc(x_160);
lean_dec(x_157);
x_161 = lean_ctor_get(x_158, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_158, 2);
lean_inc(x_162);
x_163 = lean_ctor_get(x_158, 3);
lean_inc(x_163);
x_164 = lean_ctor_get(x_158, 4);
lean_inc(x_164);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_165 = x_158;
} else {
 lean_dec_ref(x_158);
 x_165 = lean_box(0);
}
x_166 = lean_ctor_get(x_159, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_159, 2);
lean_inc(x_167);
x_168 = lean_ctor_get(x_159, 3);
lean_inc(x_168);
x_169 = lean_ctor_get(x_159, 4);
lean_inc(x_169);
x_170 = lean_ctor_get(x_159, 5);
lean_inc(x_170);
x_171 = lean_ctor_get(x_159, 6);
lean_inc(x_171);
x_172 = lean_ctor_get(x_159, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 lean_ctor_release(x_159, 2);
 lean_ctor_release(x_159, 3);
 lean_ctor_release(x_159, 4);
 lean_ctor_release(x_159, 5);
 lean_ctor_release(x_159, 6);
 x_173 = x_159;
} else {
 lean_dec_ref(x_159);
 x_173 = lean_box(0);
}
lean_inc(x_155);
x_174 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(x_172, x_17, x_155);
if (lean_is_scalar(x_173)) {
 x_175 = lean_alloc_ctor(0, 7, 0);
} else {
 x_175 = x_173;
}
lean_ctor_set(x_175, 0, x_166);
lean_ctor_set(x_175, 1, x_174);
lean_ctor_set(x_175, 2, x_167);
lean_ctor_set(x_175, 3, x_168);
lean_ctor_set(x_175, 4, x_169);
lean_ctor_set(x_175, 5, x_170);
lean_ctor_set(x_175, 6, x_171);
if (lean_is_scalar(x_165)) {
 x_176 = lean_alloc_ctor(0, 5, 0);
} else {
 x_176 = x_165;
}
lean_ctor_set(x_176, 0, x_161);
lean_ctor_set(x_176, 1, x_175);
lean_ctor_set(x_176, 2, x_162);
lean_ctor_set(x_176, 3, x_163);
lean_ctor_set(x_176, 4, x_164);
x_177 = lean_st_ref_set(x_4, x_176, x_160);
lean_dec(x_4);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_179 = x_177;
} else {
 lean_dec_ref(x_177);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_155);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_17);
lean_dec(x_4);
x_181 = lean_ctor_get(x_154, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_154, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_183 = x_154;
} else {
 lean_dec_ref(x_154);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
}
}
else
{
uint8_t x_185; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_185 = !lean_is_exclusive(x_20);
if (x_185 == 0)
{
return x_20;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_20, 0);
x_187 = lean_ctor_get(x_20, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_20);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
else
{
lean_object* x_189; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_189 = lean_ctor_get(x_19, 0);
lean_inc(x_189);
lean_dec(x_19);
lean_ctor_set(x_11, 0, x_189);
return x_11;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; 
x_190 = lean_ctor_get(x_11, 0);
x_191 = lean_ctor_get(x_11, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_11);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec(x_192);
lean_inc(x_2);
lean_inc(x_1);
x_194 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_194, 0, x_1);
lean_ctor_set(x_194, 1, x_2);
x_195 = lean_unbox(x_9);
lean_dec(x_9);
lean_ctor_set_uint8(x_194, sizeof(void*)*2, x_195);
x_196 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__1(x_193, x_194);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_197 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_191);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; uint8_t x_209; lean_object* x_210; uint8_t x_211; uint8_t x_212; uint8_t x_213; uint8_t x_214; uint8_t x_215; uint8_t x_216; uint8_t x_217; uint8_t x_218; uint8_t x_219; uint8_t x_220; uint8_t x_221; uint8_t x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; lean_object* x_228; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__3;
x_201 = lean_alloc_closure((void*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1___boxed), 8, 1);
lean_closure_set(x_201, 0, x_200);
x_202 = lean_ctor_get(x_3, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_3, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_3, 2);
lean_inc(x_204);
x_205 = lean_ctor_get(x_3, 3);
lean_inc(x_205);
x_206 = lean_ctor_get(x_3, 4);
lean_inc(x_206);
x_207 = lean_ctor_get(x_3, 5);
lean_inc(x_207);
x_208 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_209 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 x_210 = x_3;
} else {
 lean_dec_ref(x_3);
 x_210 = lean_box(0);
}
x_211 = lean_ctor_get_uint8(x_202, 0);
x_212 = lean_ctor_get_uint8(x_202, 1);
x_213 = lean_ctor_get_uint8(x_202, 2);
x_214 = lean_ctor_get_uint8(x_202, 3);
x_215 = lean_ctor_get_uint8(x_202, 4);
x_216 = lean_ctor_get_uint8(x_202, 5);
x_217 = lean_ctor_get_uint8(x_202, 6);
x_218 = lean_ctor_get_uint8(x_202, 7);
x_219 = lean_ctor_get_uint8(x_202, 8);
x_220 = lean_ctor_get_uint8(x_202, 10);
x_221 = lean_ctor_get_uint8(x_202, 11);
x_222 = lean_ctor_get_uint8(x_202, 12);
if (lean_is_exclusive(x_202)) {
 x_223 = x_202;
} else {
 lean_dec_ref(x_202);
 x_223 = lean_box(0);
}
x_224 = 1;
if (lean_is_scalar(x_223)) {
 x_225 = lean_alloc_ctor(0, 0, 13);
} else {
 x_225 = x_223;
}
lean_ctor_set_uint8(x_225, 0, x_211);
lean_ctor_set_uint8(x_225, 1, x_212);
lean_ctor_set_uint8(x_225, 2, x_213);
lean_ctor_set_uint8(x_225, 3, x_214);
lean_ctor_set_uint8(x_225, 4, x_215);
lean_ctor_set_uint8(x_225, 5, x_216);
lean_ctor_set_uint8(x_225, 6, x_217);
lean_ctor_set_uint8(x_225, 7, x_218);
lean_ctor_set_uint8(x_225, 8, x_219);
lean_ctor_set_uint8(x_225, 9, x_224);
lean_ctor_set_uint8(x_225, 10, x_220);
lean_ctor_set_uint8(x_225, 11, x_221);
lean_ctor_set_uint8(x_225, 12, x_222);
if (lean_is_scalar(x_210)) {
 x_226 = lean_alloc_ctor(0, 6, 2);
} else {
 x_226 = x_210;
}
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_203);
lean_ctor_set(x_226, 2, x_204);
lean_ctor_set(x_226, 3, x_205);
lean_ctor_set(x_226, 4, x_206);
lean_ctor_set(x_226, 5, x_207);
lean_ctor_set_uint8(x_226, sizeof(void*)*6, x_208);
lean_ctor_set_uint8(x_226, sizeof(void*)*6 + 1, x_209);
x_227 = 0;
lean_inc(x_4);
x_228 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg(x_198, x_2, x_201, x_227, x_226, x_4, x_5, x_6, x_199);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
x_231 = lean_st_ref_take(x_4, x_230);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_232, 1);
lean_inc(x_233);
x_234 = lean_ctor_get(x_231, 1);
lean_inc(x_234);
lean_dec(x_231);
x_235 = lean_ctor_get(x_232, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_232, 2);
lean_inc(x_236);
x_237 = lean_ctor_get(x_232, 3);
lean_inc(x_237);
x_238 = lean_ctor_get(x_232, 4);
lean_inc(x_238);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 lean_ctor_release(x_232, 2);
 lean_ctor_release(x_232, 3);
 lean_ctor_release(x_232, 4);
 x_239 = x_232;
} else {
 lean_dec_ref(x_232);
 x_239 = lean_box(0);
}
x_240 = lean_ctor_get(x_233, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_233, 2);
lean_inc(x_241);
x_242 = lean_ctor_get(x_233, 3);
lean_inc(x_242);
x_243 = lean_ctor_get(x_233, 4);
lean_inc(x_243);
x_244 = lean_ctor_get(x_233, 5);
lean_inc(x_244);
x_245 = lean_ctor_get(x_233, 6);
lean_inc(x_245);
x_246 = lean_ctor_get(x_233, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 lean_ctor_release(x_233, 2);
 lean_ctor_release(x_233, 3);
 lean_ctor_release(x_233, 4);
 lean_ctor_release(x_233, 5);
 lean_ctor_release(x_233, 6);
 x_247 = x_233;
} else {
 lean_dec_ref(x_233);
 x_247 = lean_box(0);
}
lean_inc(x_229);
x_248 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(x_246, x_194, x_229);
if (lean_is_scalar(x_247)) {
 x_249 = lean_alloc_ctor(0, 7, 0);
} else {
 x_249 = x_247;
}
lean_ctor_set(x_249, 0, x_240);
lean_ctor_set(x_249, 1, x_248);
lean_ctor_set(x_249, 2, x_241);
lean_ctor_set(x_249, 3, x_242);
lean_ctor_set(x_249, 4, x_243);
lean_ctor_set(x_249, 5, x_244);
lean_ctor_set(x_249, 6, x_245);
if (lean_is_scalar(x_239)) {
 x_250 = lean_alloc_ctor(0, 5, 0);
} else {
 x_250 = x_239;
}
lean_ctor_set(x_250, 0, x_235);
lean_ctor_set(x_250, 1, x_249);
lean_ctor_set(x_250, 2, x_236);
lean_ctor_set(x_250, 3, x_237);
lean_ctor_set(x_250, 4, x_238);
x_251 = lean_st_ref_set(x_4, x_250, x_234);
lean_dec(x_4);
x_252 = lean_ctor_get(x_251, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_253 = x_251;
} else {
 lean_dec_ref(x_251);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_229);
lean_ctor_set(x_254, 1, x_252);
return x_254;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_194);
lean_dec(x_4);
x_255 = lean_ctor_get(x_228, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_228, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_257 = x_228;
} else {
 lean_dec_ref(x_228);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(1, 2, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_255);
lean_ctor_set(x_258, 1, x_256);
return x_258;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_194);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_259 = lean_ctor_get(x_197, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_197, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_261 = x_197;
} else {
 lean_dec_ref(x_197);
 x_261 = lean_box(0);
}
if (lean_is_scalar(x_261)) {
 x_262 = lean_alloc_ctor(1, 2, 0);
} else {
 x_262 = x_261;
}
lean_ctor_set(x_262, 0, x_259);
lean_ctor_set(x_262, 1, x_260);
return x_262;
}
}
else
{
lean_object* x_263; lean_object* x_264; 
lean_dec(x_194);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_263 = lean_ctor_get(x_196, 0);
lean_inc(x_263);
lean_dec(x_196);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_191);
return x_264;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_array_get_size(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_FunInfo_getArity(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_FunInfo(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2___closed__1 = _init_l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2___closed__1();
l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2___closed__2 = _init_l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2___closed__2();
l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5___closed__1);
l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1___closed__1 = _init_l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1___closed__1();
lean_mark_persistent(l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1___closed__1);
l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__1 = _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__1();
lean_mark_persistent(l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__1);
l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___closed__1 = _init_l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___closed__1);
l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___closed__2 = _init_l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___closed__2);
l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__1 = _init_l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__1);
l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__2 = _init_l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__2);
l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1___closed__1 = _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1___closed__1);
l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__1 = _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__1();
lean_mark_persistent(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__1);
l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__2 = _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__2();
lean_mark_persistent(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__2);
l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__3 = _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__3();
lean_mark_persistent(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
