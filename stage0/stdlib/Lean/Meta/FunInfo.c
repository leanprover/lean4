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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_qpartition___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__1(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_mkInfoCacheKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__3(lean_object*, lean_object*);
uint8_t l_Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_1371_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static size_t l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_getOutParamPositions_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__1___boxed(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__4;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__1(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__2;
lean_object* l_ReaderT_instApplicativeOfMonad___rarg(lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__1;
LEAN_EXPORT lean_object* l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_FunInfo_getArity___boxed(lean_object*);
lean_object* l_instMonadControlTOfPure___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__3;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__1___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar(lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
static lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__1;
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadCoreM;
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__4(lean_object*, lean_object*, size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5___closed__1;
uint8_t l_Lean_Expr_hasFVar(lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__2___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___closed__2;
static lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__1;
static size_t l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2(lean_object*, size_t, lean_object*);
uint8_t l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(uint8_t, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
x_10 = l_Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_1371_(x_5, x_9);
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
x_14 = l_Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_1371_(x_3, x_12);
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
x_29 = l_Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_1371_(x_3, x_27);
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
uint64_t x_3; lean_object* x_4; lean_object* x_5; uint64_t x_6; 
x_3 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_Lean_Expr_hash(x_4);
if (lean_obj_tag(x_5) == 0)
{
uint64_t x_7; uint64_t x_8; uint64_t x_9; size_t x_10; lean_object* x_11; 
x_7 = 11;
x_8 = lean_uint64_mix_hash(x_6, x_7);
x_9 = lean_uint64_mix_hash(x_3, x_8);
x_10 = lean_uint64_to_usize(x_9);
x_11 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2(x_1, x_10, x_2);
return x_11;
}
else
{
lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_uint64_of_nat(x_12);
x_14 = 13;
x_15 = lean_uint64_mix_hash(x_13, x_14);
x_16 = lean_uint64_mix_hash(x_6, x_15);
x_17 = lean_uint64_mix_hash(x_3, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2(x_1, x_18, x_2);
return x_19;
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
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; uint64_t x_20; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = 1;
x_12 = lean_usize_sub(x_1, x_11);
x_13 = 5;
x_14 = lean_usize_mul(x_13, x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_5, x_15);
lean_dec(x_5);
x_17 = lean_ctor_get_uint64(x_9, sizeof(void*)*2);
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
x_20 = l_Lean_Expr_hash(x_18);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_21 = 11;
x_22 = lean_uint64_mix_hash(x_20, x_21);
x_23 = lean_uint64_mix_hash(x_17, x_22);
x_24 = lean_uint64_to_usize(x_23);
x_25 = lean_usize_shift_right(x_24, x_14);
x_26 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(x_6, x_25, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_16;
x_6 = x_26;
goto _start;
}
else
{
lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; size_t x_34; size_t x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_uint64_of_nat(x_28);
lean_dec(x_28);
x_30 = 13;
x_31 = lean_uint64_mix_hash(x_29, x_30);
x_32 = lean_uint64_mix_hash(x_20, x_31);
x_33 = lean_uint64_mix_hash(x_17, x_32);
x_34 = lean_uint64_to_usize(x_33);
x_35 = lean_usize_shift_right(x_34, x_14);
x_36 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(x_6, x_35, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_16;
x_6 = x_36;
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
x_18 = l_Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_1371_(x_3, x_17);
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
x_21 = l_Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_1371_(x_4, x_19);
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
x_28 = l_Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_1371_(x_4, x_26);
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
x_63 = l_Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_1371_(x_4, x_60);
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
size_t x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; 
x_4 = 1;
x_5 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = l_Lean_Expr_hash(x_6);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; lean_object* x_13; 
x_9 = 11;
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = lean_uint64_mix_hash(x_5, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(x_1, x_12, x_4, x_2, x_3);
return x_13;
}
else
{
lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; size_t x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_uint64_of_nat(x_14);
lean_dec(x_14);
x_16 = 13;
x_17 = lean_uint64_mix_hash(x_15, x_16);
x_18 = lean_uint64_mix_hash(x_8, x_17);
x_19 = lean_uint64_mix_hash(x_5, x_18);
x_20 = lean_uint64_to_usize(x_19);
x_21 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(x_1, x_20, x_4, x_2, x_3);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Lean_Meta_mkInfoCacheKey(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_5, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__1(x_17, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_free_object(x_12);
lean_inc(x_5);
x_19 = lean_apply_5(x_3, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_st_ref_take(x_5, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_23, 1);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_20);
x_30 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(x_29, x_10, x_20);
lean_ctor_set(x_24, 1, x_30);
x_31 = lean_st_ref_set(x_5, x_23, x_25);
lean_dec(x_5);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_20);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_20);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_36 = lean_ctor_get(x_24, 0);
x_37 = lean_ctor_get(x_24, 2);
x_38 = lean_ctor_get(x_24, 3);
x_39 = lean_ctor_get(x_24, 4);
x_40 = lean_ctor_get(x_24, 5);
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_41);
lean_inc(x_36);
lean_dec(x_24);
lean_inc(x_20);
x_42 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(x_41, x_10, x_20);
x_43 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_37);
lean_ctor_set(x_43, 3, x_38);
lean_ctor_set(x_43, 4, x_39);
lean_ctor_set(x_43, 5, x_40);
lean_ctor_set(x_23, 1, x_43);
x_44 = lean_st_ref_set(x_5, x_23, x_25);
lean_dec(x_5);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_20);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_48 = lean_ctor_get(x_23, 0);
x_49 = lean_ctor_get(x_23, 2);
x_50 = lean_ctor_get(x_23, 3);
x_51 = lean_ctor_get(x_23, 4);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_23);
x_52 = lean_ctor_get(x_24, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_24, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_24, 3);
lean_inc(x_54);
x_55 = lean_ctor_get(x_24, 4);
lean_inc(x_55);
x_56 = lean_ctor_get(x_24, 5);
lean_inc(x_56);
x_57 = lean_ctor_get(x_24, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 lean_ctor_release(x_24, 3);
 lean_ctor_release(x_24, 4);
 lean_ctor_release(x_24, 5);
 x_58 = x_24;
} else {
 lean_dec_ref(x_24);
 x_58 = lean_box(0);
}
lean_inc(x_20);
x_59 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(x_57, x_10, x_20);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 6, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_52);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_60, 2, x_53);
lean_ctor_set(x_60, 3, x_54);
lean_ctor_set(x_60, 4, x_55);
lean_ctor_set(x_60, 5, x_56);
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_48);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_61, 2, x_49);
lean_ctor_set(x_61, 3, x_50);
lean_ctor_set(x_61, 4, x_51);
x_62 = lean_st_ref_set(x_5, x_61, x_25);
lean_dec(x_5);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_20);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_dec(x_10);
lean_dec(x_5);
x_66 = !lean_is_exclusive(x_19);
if (x_66 == 0)
{
return x_19;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_19, 0);
x_68 = lean_ctor_get(x_19, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_19);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_70 = lean_ctor_get(x_18, 0);
lean_inc(x_70);
lean_dec(x_18);
lean_ctor_set(x_12, 0, x_70);
return x_12;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_12, 0);
x_72 = lean_ctor_get(x_12, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_12);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__1(x_74, x_10);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
lean_inc(x_5);
x_76 = lean_apply_5(x_3, x_4, x_5, x_6, x_7, x_72);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_st_ref_take(x_5, x_78);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_ctor_get(x_80, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_80, 2);
lean_inc(x_84);
x_85 = lean_ctor_get(x_80, 3);
lean_inc(x_85);
x_86 = lean_ctor_get(x_80, 4);
lean_inc(x_86);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 lean_ctor_release(x_80, 2);
 lean_ctor_release(x_80, 3);
 lean_ctor_release(x_80, 4);
 x_87 = x_80;
} else {
 lean_dec_ref(x_80);
 x_87 = lean_box(0);
}
x_88 = lean_ctor_get(x_81, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_81, 2);
lean_inc(x_89);
x_90 = lean_ctor_get(x_81, 3);
lean_inc(x_90);
x_91 = lean_ctor_get(x_81, 4);
lean_inc(x_91);
x_92 = lean_ctor_get(x_81, 5);
lean_inc(x_92);
x_93 = lean_ctor_get(x_81, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 lean_ctor_release(x_81, 2);
 lean_ctor_release(x_81, 3);
 lean_ctor_release(x_81, 4);
 lean_ctor_release(x_81, 5);
 x_94 = x_81;
} else {
 lean_dec_ref(x_81);
 x_94 = lean_box(0);
}
lean_inc(x_77);
x_95 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(x_93, x_10, x_77);
if (lean_is_scalar(x_94)) {
 x_96 = lean_alloc_ctor(0, 6, 0);
} else {
 x_96 = x_94;
}
lean_ctor_set(x_96, 0, x_88);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_96, 2, x_89);
lean_ctor_set(x_96, 3, x_90);
lean_ctor_set(x_96, 4, x_91);
lean_ctor_set(x_96, 5, x_92);
if (lean_is_scalar(x_87)) {
 x_97 = lean_alloc_ctor(0, 5, 0);
} else {
 x_97 = x_87;
}
lean_ctor_set(x_97, 0, x_83);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_97, 2, x_84);
lean_ctor_set(x_97, 3, x_85);
lean_ctor_set(x_97, 4, x_86);
x_98 = lean_st_ref_set(x_5, x_97, x_82);
lean_dec(x_5);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_77);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_10);
lean_dec(x_5);
x_102 = lean_ctor_get(x_76, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_76, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_104 = x_76;
} else {
 lean_dec_ref(x_76);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_106 = lean_ctor_get(x_75, 0);
lean_inc(x_106);
lean_dec(x_75);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_72);
return x_107;
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
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_idxOfAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
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
LEAN_EXPORT uint8_t l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__4(x_2, x_1, x_7, x_8);
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
lean_object* x_4; 
x_4 = l_Array_idxOf_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__1(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
return x_3;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__3(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_push(x_3, x_5);
return x_7;
}
else
{
lean_dec(x_5);
return x_3;
}
}
}
case 5:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l_Lean_Expr_hasFVar(x_2);
if (x_10 == 0)
{
return x_3;
}
else
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(x_1, x_8, x_3);
x_2 = x_9;
x_3 = x_11;
goto _start;
}
}
case 6:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
x_15 = l_Lean_Expr_hasFVar(x_2);
if (x_15 == 0)
{
return x_3;
}
else
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(x_1, x_13, x_3);
x_2 = x_14;
x_3 = x_16;
goto _start;
}
}
case 7:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_2, 2);
x_20 = l_Lean_Expr_hasFVar(x_2);
if (x_20 == 0)
{
return x_3;
}
else
{
lean_object* x_21; 
x_21 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(x_1, x_18, x_3);
x_2 = x_19;
x_3 = x_21;
goto _start;
}
}
case 8:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
x_25 = lean_ctor_get(x_2, 3);
x_26 = l_Lean_Expr_hasFVar(x_2);
if (x_26 == 0)
{
return x_3;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(x_1, x_23, x_3);
x_28 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(x_1, x_24, x_27);
x_2 = x_25;
x_3 = x_28;
goto _start;
}
}
case 10:
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_2, 1);
x_2 = x_30;
goto _start;
}
case 11:
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_2, 2);
x_2 = x_32;
goto _start;
}
default: 
{
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_idxOfAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_idxOf_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__4(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__3(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_3, x_4);
if (x_8 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1___closed__1;
lean_inc(x_3);
x_10 = l_Array_qpartition___rarg(x_1, x_2, x_9, x_3, x_4, lean_box(0), lean_box(0), lean_box(0));
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_nat_dec_le(x_4, x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1(x_1, x_12, x_3, x_11, lean_box(0), lean_box(0), lean_box(0));
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_11, x_15);
lean_dec(x_11);
x_2 = x_14;
x_3 = x_16;
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_3);
return x_12;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___closed__1;
x_4 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(x_1, x_2, x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_5, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_8, x_7);
if (x_10 == 0)
{
lean_object* x_11; 
lean_inc(x_7);
x_11 = l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1(x_5, x_4, x_7, x_7, lean_box(0), lean_box(0), lean_box(0));
lean_dec(x_7);
lean_dec(x_5);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1(x_5, x_4, x_8, x_7, lean_box(0), lean_box(0), lean_box(0));
lean_dec(x_7);
lean_dec(x_5);
return x_12;
}
}
else
{
lean_dec(x_7);
lean_dec(x_5);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_21 = l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__3(x_2, x_5);
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
x_8 = l_Array_mapFinIdxM_map___at___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___spec__1(x_1, x_2, x_1, x_6, x_4, lean_box(0), x_7);
return x_8;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_mapFinIdxM_map___at___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_nat_dec_lt(x_7, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_25; 
x_25 = !lean_is_exclusive(x_6);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_6, 0);
x_27 = lean_ctor_get(x_6, 1);
x_28 = l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__3(x_3, x_7);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_6);
x_18 = x_29;
x_19 = x_14;
goto block_24;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_array_fget(x_4, x_7);
x_31 = l_Array_idxOf_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__1(x_1, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
lean_dec(x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_6);
x_18 = x_32;
x_19 = x_14;
goto block_24;
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_30);
x_35 = lean_infer_type(x_30, x_10, x_11, x_12, x_13, x_14);
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
lean_dec(x_34);
lean_dec(x_30);
lean_ctor_set(x_31, 0, x_6);
x_18 = x_31;
x_19 = x_40;
goto block_24;
}
else
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_array_get_size(x_27);
x_43 = lean_nat_dec_lt(x_34, x_42);
lean_dec(x_42);
x_44 = l_Lean_Expr_fvarId_x21(x_30);
lean_dec(x_30);
x_45 = lean_box(0);
x_46 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_26, x_44, x_45);
if (x_43 == 0)
{
lean_dec(x_34);
lean_ctor_set(x_6, 0, x_46);
lean_ctor_set(x_31, 0, x_6);
x_18 = x_31;
x_19 = x_40;
goto block_24;
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_array_fget(x_27, x_34);
x_48 = lean_array_fset(x_27, x_34, x_45);
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
uint8_t x_50; lean_object* x_51; 
x_50 = 1;
lean_ctor_set_uint8(x_47, sizeof(void*)*1 + 4, x_50);
x_51 = lean_array_fset(x_48, x_34, x_47);
lean_dec(x_34);
lean_ctor_set(x_6, 1, x_51);
lean_ctor_set(x_6, 0, x_46);
lean_ctor_set(x_31, 0, x_6);
x_18 = x_31;
x_19 = x_40;
goto block_24;
}
else
{
uint8_t x_52; uint8_t x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get_uint8(x_47, sizeof(void*)*1);
x_53 = lean_ctor_get_uint8(x_47, sizeof(void*)*1 + 1);
x_54 = lean_ctor_get(x_47, 0);
x_55 = lean_ctor_get_uint8(x_47, sizeof(void*)*1 + 2);
x_56 = lean_ctor_get_uint8(x_47, sizeof(void*)*1 + 3);
x_57 = lean_ctor_get_uint8(x_47, sizeof(void*)*1 + 5);
lean_inc(x_54);
lean_dec(x_47);
x_58 = 1;
x_59 = lean_alloc_ctor(0, 1, 6);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_52);
lean_ctor_set_uint8(x_59, sizeof(void*)*1 + 1, x_53);
lean_ctor_set_uint8(x_59, sizeof(void*)*1 + 2, x_55);
lean_ctor_set_uint8(x_59, sizeof(void*)*1 + 3, x_56);
lean_ctor_set_uint8(x_59, sizeof(void*)*1 + 4, x_58);
lean_ctor_set_uint8(x_59, sizeof(void*)*1 + 5, x_57);
x_60 = lean_array_fset(x_48, x_34, x_59);
lean_dec(x_34);
lean_ctor_set(x_6, 1, x_60);
lean_ctor_set(x_6, 0, x_46);
lean_ctor_set(x_31, 0, x_6);
x_18 = x_31;
x_19 = x_40;
goto block_24;
}
}
}
}
else
{
uint8_t x_61; 
lean_free_object(x_31);
lean_dec(x_34);
lean_dec(x_30);
lean_free_object(x_6);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_61 = !lean_is_exclusive(x_38);
if (x_61 == 0)
{
return x_38;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_38, 0);
x_63 = lean_ctor_get(x_38, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_38);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_free_object(x_31);
lean_dec(x_34);
lean_dec(x_30);
lean_free_object(x_6);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_65 = !lean_is_exclusive(x_35);
if (x_65 == 0)
{
return x_35;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_35, 0);
x_67 = lean_ctor_get(x_35, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_35);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_31, 0);
lean_inc(x_69);
lean_dec(x_31);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_30);
x_70 = lean_infer_type(x_30, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_73 = lean_whnf(x_71, x_10, x_11, x_12, x_13, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Expr_isForall(x_74);
lean_dec(x_74);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_69);
lean_dec(x_30);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_6);
x_18 = x_77;
x_19 = x_75;
goto block_24;
}
else
{
lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_array_get_size(x_27);
x_79 = lean_nat_dec_lt(x_69, x_78);
lean_dec(x_78);
x_80 = l_Lean_Expr_fvarId_x21(x_30);
lean_dec(x_30);
x_81 = lean_box(0);
x_82 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_26, x_80, x_81);
if (x_79 == 0)
{
lean_object* x_83; 
lean_dec(x_69);
lean_ctor_set(x_6, 0, x_82);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_6);
x_18 = x_83;
x_19 = x_75;
goto block_24;
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_87; lean_object* x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_84 = lean_array_fget(x_27, x_69);
x_85 = lean_array_fset(x_27, x_69, x_81);
x_86 = lean_ctor_get_uint8(x_84, sizeof(void*)*1);
x_87 = lean_ctor_get_uint8(x_84, sizeof(void*)*1 + 1);
x_88 = lean_ctor_get(x_84, 0);
lean_inc(x_88);
x_89 = lean_ctor_get_uint8(x_84, sizeof(void*)*1 + 2);
x_90 = lean_ctor_get_uint8(x_84, sizeof(void*)*1 + 3);
x_91 = lean_ctor_get_uint8(x_84, sizeof(void*)*1 + 5);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 x_92 = x_84;
} else {
 lean_dec_ref(x_84);
 x_92 = lean_box(0);
}
x_93 = 1;
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 1, 6);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_88);
lean_ctor_set_uint8(x_94, sizeof(void*)*1, x_86);
lean_ctor_set_uint8(x_94, sizeof(void*)*1 + 1, x_87);
lean_ctor_set_uint8(x_94, sizeof(void*)*1 + 2, x_89);
lean_ctor_set_uint8(x_94, sizeof(void*)*1 + 3, x_90);
lean_ctor_set_uint8(x_94, sizeof(void*)*1 + 4, x_93);
lean_ctor_set_uint8(x_94, sizeof(void*)*1 + 5, x_91);
x_95 = lean_array_fset(x_85, x_69, x_94);
lean_dec(x_69);
lean_ctor_set(x_6, 1, x_95);
lean_ctor_set(x_6, 0, x_82);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_6);
x_18 = x_96;
x_19 = x_75;
goto block_24;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_69);
lean_dec(x_30);
lean_free_object(x_6);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_97 = lean_ctor_get(x_73, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_73, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_99 = x_73;
} else {
 lean_dec_ref(x_73);
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
lean_dec(x_69);
lean_dec(x_30);
lean_free_object(x_6);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_101 = lean_ctor_get(x_70, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_70, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_103 = x_70;
} else {
 lean_dec_ref(x_70);
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
}
}
else
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_105 = lean_ctor_get(x_6, 0);
x_106 = lean_ctor_get(x_6, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_6);
x_107 = l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__3(x_3, x_7);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_18 = x_109;
x_19 = x_14;
goto block_24;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_array_fget(x_4, x_7);
x_111 = l_Array_idxOf_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__1(x_1, x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_105);
lean_ctor_set(x_112, 1, x_106);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_18 = x_113;
x_19 = x_14;
goto block_24;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_111, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 x_115 = x_111;
} else {
 lean_dec_ref(x_111);
 x_115 = lean_box(0);
}
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_110);
x_116 = lean_infer_type(x_110, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_119 = lean_whnf(x_117, x_10, x_11, x_12, x_13, x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = l_Lean_Expr_isForall(x_120);
lean_dec(x_120);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_114);
lean_dec(x_110);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_105);
lean_ctor_set(x_123, 1, x_106);
if (lean_is_scalar(x_115)) {
 x_124 = lean_alloc_ctor(1, 1, 0);
} else {
 x_124 = x_115;
}
lean_ctor_set(x_124, 0, x_123);
x_18 = x_124;
x_19 = x_121;
goto block_24;
}
else
{
lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_array_get_size(x_106);
x_126 = lean_nat_dec_lt(x_114, x_125);
lean_dec(x_125);
x_127 = l_Lean_Expr_fvarId_x21(x_110);
lean_dec(x_110);
x_128 = lean_box(0);
x_129 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_105, x_127, x_128);
if (x_126 == 0)
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_114);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_106);
if (lean_is_scalar(x_115)) {
 x_131 = lean_alloc_ctor(1, 1, 0);
} else {
 x_131 = x_115;
}
lean_ctor_set(x_131, 0, x_130);
x_18 = x_131;
x_19 = x_121;
goto block_24;
}
else
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; uint8_t x_135; lean_object* x_136; uint8_t x_137; uint8_t x_138; uint8_t x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_132 = lean_array_fget(x_106, x_114);
x_133 = lean_array_fset(x_106, x_114, x_128);
x_134 = lean_ctor_get_uint8(x_132, sizeof(void*)*1);
x_135 = lean_ctor_get_uint8(x_132, sizeof(void*)*1 + 1);
x_136 = lean_ctor_get(x_132, 0);
lean_inc(x_136);
x_137 = lean_ctor_get_uint8(x_132, sizeof(void*)*1 + 2);
x_138 = lean_ctor_get_uint8(x_132, sizeof(void*)*1 + 3);
x_139 = lean_ctor_get_uint8(x_132, sizeof(void*)*1 + 5);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 x_140 = x_132;
} else {
 lean_dec_ref(x_132);
 x_140 = lean_box(0);
}
x_141 = 1;
if (lean_is_scalar(x_140)) {
 x_142 = lean_alloc_ctor(0, 1, 6);
} else {
 x_142 = x_140;
}
lean_ctor_set(x_142, 0, x_136);
lean_ctor_set_uint8(x_142, sizeof(void*)*1, x_134);
lean_ctor_set_uint8(x_142, sizeof(void*)*1 + 1, x_135);
lean_ctor_set_uint8(x_142, sizeof(void*)*1 + 2, x_137);
lean_ctor_set_uint8(x_142, sizeof(void*)*1 + 3, x_138);
lean_ctor_set_uint8(x_142, sizeof(void*)*1 + 4, x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*1 + 5, x_139);
x_143 = lean_array_fset(x_133, x_114, x_142);
lean_dec(x_114);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_129);
lean_ctor_set(x_144, 1, x_143);
if (lean_is_scalar(x_115)) {
 x_145 = lean_alloc_ctor(1, 1, 0);
} else {
 x_145 = x_115;
}
lean_ctor_set(x_145, 0, x_144);
x_18 = x_145;
x_19 = x_121;
goto block_24;
}
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_110);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_146 = lean_ctor_get(x_119, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_119, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_148 = x_119;
} else {
 lean_dec_ref(x_119);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_110);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_150 = lean_ctor_get(x_116, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_116, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_152 = x_116;
} else {
 lean_dec_ref(x_116);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
}
}
block_24:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_5, 2);
x_22 = lean_nat_add(x_7, x_21);
lean_dec(x_7);
x_6 = x_20;
x_7 = x_22;
x_8 = lean_box(0);
x_9 = lean_box(0);
x_14 = x_19;
goto _start;
}
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
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Decidable", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___closed__2;
x_9 = l_Lean_Expr_isAppOf(x_2, x_8);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__2(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_nat_dec_lt(x_6, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_5, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_26 = x_5;
} else {
 lean_dec_ref(x_5);
 x_26 = lean_box(0);
}
x_27 = lean_array_fget(x_2, x_6);
lean_inc(x_9);
x_28 = l_Lean_Meta_getFVarLocalDecl(x_27, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; lean_object* x_159; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_LocalDecl_type(x_29);
x_32 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(x_2, x_31);
x_33 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(x_25, x_32);
lean_dec(x_25);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_31);
x_159 = l_Lean_Meta_isProp(x_31, x_9, x_10, x_11, x_12, x_30);
if (lean_obj_tag(x_24) == 0)
{
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; uint8_t x_162; uint8_t x_163; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = 0;
x_163 = lean_unbox(x_160);
lean_dec(x_160);
x_34 = x_162;
x_35 = x_163;
x_36 = x_161;
goto block_158;
}
else
{
uint8_t x_164; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
x_164 = !lean_is_exclusive(x_159);
if (x_164 == 0)
{
return x_159;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_159, 0);
x_166 = lean_ctor_get(x_159, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_159);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
else
{
lean_object* x_168; lean_object* x_169; 
lean_inc(x_24);
x_168 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__2___boxed), 2, 1);
lean_closure_set(x_168, 0, x_24);
x_169 = lean_find_expr(x_168, x_31);
lean_dec(x_168);
if (lean_obj_tag(x_169) == 0)
{
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; uint8_t x_173; 
x_170 = lean_ctor_get(x_159, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_159, 1);
lean_inc(x_171);
lean_dec(x_159);
x_172 = 0;
x_173 = lean_unbox(x_170);
lean_dec(x_170);
x_34 = x_172;
x_35 = x_173;
x_36 = x_171;
goto block_158;
}
else
{
uint8_t x_174; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
x_174 = !lean_is_exclusive(x_159);
if (x_174 == 0)
{
return x_159;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_159, 0);
x_176 = lean_ctor_get(x_159, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_159);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
else
{
lean_dec(x_169);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; uint8_t x_181; 
x_178 = lean_ctor_get(x_159, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_159, 1);
lean_inc(x_179);
lean_dec(x_159);
x_180 = 1;
x_181 = lean_unbox(x_178);
lean_dec(x_178);
x_34 = x_180;
x_35 = x_181;
x_36 = x_179;
goto block_158;
}
else
{
uint8_t x_182; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
x_182 = !lean_is_exclusive(x_159);
if (x_182 == 0)
{
return x_159;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_159, 0);
x_184 = lean_ctor_get(x_159, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_159);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
}
}
block_158:
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_37 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__1;
x_38 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_31);
x_39 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_31, x_37, x_38, x_9, x_10, x_11, x_12, x_36);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_LocalDecl_binderInfo(x_29);
x_43 = lean_alloc_ctor(0, 1, 6);
lean_ctor_set(x_43, 0, x_32);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*1 + 1, x_38);
lean_ctor_set_uint8(x_43, sizeof(void*)*1 + 2, x_35);
x_44 = lean_unbox(x_40);
lean_dec(x_40);
lean_ctor_set_uint8(x_43, sizeof(void*)*1 + 3, x_44);
lean_ctor_set_uint8(x_43, sizeof(void*)*1 + 4, x_38);
lean_ctor_set_uint8(x_43, sizeof(void*)*1 + 5, x_34);
x_45 = lean_array_push(x_33, x_43);
x_46 = 3;
x_47 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_42, x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_31);
lean_dec(x_29);
if (lean_is_scalar(x_26)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_26;
}
lean_ctor_set(x_48, 0, x_24);
lean_ctor_set(x_48, 1, x_45);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_17 = x_49;
x_18 = x_41;
goto block_23;
}
else
{
lean_object* x_50; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_31);
x_50 = l_Lean_Meta_isClass_x3f(x_31, x_9, x_10, x_11, x_12, x_41);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_31);
lean_dec(x_29);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
if (lean_is_scalar(x_26)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_26;
}
lean_ctor_set(x_53, 0, x_24);
lean_ctor_set(x_53, 1, x_45);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_17 = x_54;
x_18 = x_52;
goto block_23;
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_dec(x_50);
x_56 = !lean_is_exclusive(x_51);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_51, 0);
x_58 = lean_st_ref_get(x_12, x_55);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_getOutParamPositions_x3f(x_61, x_57);
lean_dec(x_57);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
lean_dec(x_31);
lean_dec(x_29);
if (lean_is_scalar(x_26)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_26;
}
lean_ctor_set(x_63, 0, x_24);
lean_ctor_set(x_63, 1, x_45);
lean_ctor_set(x_51, 0, x_63);
x_17 = x_51;
x_18 = x_60;
goto block_23;
}
else
{
uint8_t x_64; 
lean_free_object(x_51);
x_64 = !lean_is_exclusive(x_62);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_62, 0);
x_66 = l_Array_isEmpty___rarg(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_67 = lean_unsigned_to_nat(0u);
x_68 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_31, x_67);
x_69 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__2;
lean_inc(x_68);
x_70 = lean_mk_array(x_68, x_69);
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_sub(x_68, x_71);
lean_dec(x_68);
x_73 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_31, x_70, x_72);
x_74 = lean_array_get_size(x_73);
x_75 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_75, 0, x_67);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set(x_75, 2, x_71);
if (lean_is_scalar(x_26)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_26;
}
lean_ctor_set(x_76, 0, x_24);
lean_ctor_set(x_76, 1, x_45);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_77 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1(x_2, x_29, x_65, x_73, x_75, x_76, x_67, lean_box(0), lean_box(0), x_9, x_10, x_11, x_12, x_60);
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_65);
lean_dec(x_29);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = !lean_is_exclusive(x_78);
if (x_80 == 0)
{
lean_ctor_set(x_62, 0, x_78);
x_17 = x_62;
x_18 = x_79;
goto block_23;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_78, 0);
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_78);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set(x_62, 0, x_83);
x_17 = x_62;
x_18 = x_79;
goto block_23;
}
}
else
{
uint8_t x_84; 
lean_free_object(x_62);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
x_84 = !lean_is_exclusive(x_77);
if (x_84 == 0)
{
return x_77;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_77, 0);
x_86 = lean_ctor_get(x_77, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_77);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; 
lean_dec(x_65);
lean_dec(x_31);
lean_dec(x_29);
if (lean_is_scalar(x_26)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_26;
}
lean_ctor_set(x_88, 0, x_24);
lean_ctor_set(x_88, 1, x_45);
lean_ctor_set(x_62, 0, x_88);
x_17 = x_62;
x_18 = x_60;
goto block_23;
}
}
else
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_62, 0);
lean_inc(x_89);
lean_dec(x_62);
x_90 = l_Array_isEmpty___rarg(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_91 = lean_unsigned_to_nat(0u);
x_92 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_31, x_91);
x_93 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__2;
lean_inc(x_92);
x_94 = lean_mk_array(x_92, x_93);
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_nat_sub(x_92, x_95);
lean_dec(x_92);
x_97 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_31, x_94, x_96);
x_98 = lean_array_get_size(x_97);
x_99 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_99, 0, x_91);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set(x_99, 2, x_95);
if (lean_is_scalar(x_26)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_26;
}
lean_ctor_set(x_100, 0, x_24);
lean_ctor_set(x_100, 1, x_45);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_101 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1(x_2, x_29, x_89, x_97, x_99, x_100, x_91, lean_box(0), lean_box(0), x_9, x_10, x_11, x_12, x_60);
lean_dec(x_99);
lean_dec(x_97);
lean_dec(x_89);
lean_dec(x_29);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_ctor_get(x_102, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_106 = x_102;
} else {
 lean_dec_ref(x_102);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_17 = x_108;
x_18 = x_103;
goto block_23;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
x_109 = lean_ctor_get(x_101, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_101, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_111 = x_101;
} else {
 lean_dec_ref(x_101);
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
lean_dec(x_89);
lean_dec(x_31);
lean_dec(x_29);
if (lean_is_scalar(x_26)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_26;
}
lean_ctor_set(x_113, 0, x_24);
lean_ctor_set(x_113, 1, x_45);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_17 = x_114;
x_18 = x_60;
goto block_23;
}
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_115 = lean_ctor_get(x_51, 0);
lean_inc(x_115);
lean_dec(x_51);
x_116 = lean_st_ref_get(x_12, x_55);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
lean_dec(x_117);
x_120 = l_Lean_getOutParamPositions_x3f(x_119, x_115);
lean_dec(x_115);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_31);
lean_dec(x_29);
if (lean_is_scalar(x_26)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_26;
}
lean_ctor_set(x_121, 0, x_24);
lean_ctor_set(x_121, 1, x_45);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_17 = x_122;
x_18 = x_118;
goto block_23;
}
else
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_120, 0);
lean_inc(x_123);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 x_124 = x_120;
} else {
 lean_dec_ref(x_120);
 x_124 = lean_box(0);
}
x_125 = l_Array_isEmpty___rarg(x_123);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_126 = lean_unsigned_to_nat(0u);
x_127 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_31, x_126);
x_128 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__2;
lean_inc(x_127);
x_129 = lean_mk_array(x_127, x_128);
x_130 = lean_unsigned_to_nat(1u);
x_131 = lean_nat_sub(x_127, x_130);
lean_dec(x_127);
x_132 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_31, x_129, x_131);
x_133 = lean_array_get_size(x_132);
x_134 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_134, 0, x_126);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set(x_134, 2, x_130);
if (lean_is_scalar(x_26)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_26;
}
lean_ctor_set(x_135, 0, x_24);
lean_ctor_set(x_135, 1, x_45);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_136 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1(x_2, x_29, x_123, x_132, x_134, x_135, x_126, lean_box(0), lean_box(0), x_9, x_10, x_11, x_12, x_118);
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_123);
lean_dec(x_29);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_141 = x_137;
} else {
 lean_dec_ref(x_137);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
if (lean_is_scalar(x_124)) {
 x_143 = lean_alloc_ctor(1, 1, 0);
} else {
 x_143 = x_124;
}
lean_ctor_set(x_143, 0, x_142);
x_17 = x_143;
x_18 = x_138;
goto block_23;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_124);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
x_144 = lean_ctor_get(x_136, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_136, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_146 = x_136;
} else {
 lean_dec_ref(x_136);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_123);
lean_dec(x_31);
lean_dec(x_29);
if (lean_is_scalar(x_26)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_26;
}
lean_ctor_set(x_148, 0, x_24);
lean_ctor_set(x_148, 1, x_45);
if (lean_is_scalar(x_124)) {
 x_149 = lean_alloc_ctor(1, 1, 0);
} else {
 x_149 = x_124;
}
lean_ctor_set(x_149, 0, x_148);
x_17 = x_149;
x_18 = x_118;
goto block_23;
}
}
}
}
}
else
{
uint8_t x_150; 
lean_dec(x_45);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
x_150 = !lean_is_exclusive(x_50);
if (x_150 == 0)
{
return x_50;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_50, 0);
x_152 = lean_ctor_get(x_50, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_50);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
}
else
{
uint8_t x_154; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
x_154 = !lean_is_exclusive(x_39);
if (x_154 == 0)
{
return x_39;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_39, 0);
x_156 = lean_ctor_get(x_39, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_39);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
}
else
{
uint8_t x_186; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
x_186 = !lean_is_exclusive(x_28);
if (x_186 == 0)
{
return x_28;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_28, 0);
x_188 = lean_ctor_get(x_28, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_28);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
block_23:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_4, 2);
x_21 = lean_nat_add(x_6, x_20);
lean_dec(x_6);
x_5 = x_19;
x_6 = x_21;
x_7 = lean_box(0);
x_8 = lean_box(0);
x_13 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_nat_dec_lt(x_5, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_4, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_25 = x_4;
} else {
 lean_dec_ref(x_4);
 x_25 = lean_box(0);
}
x_26 = lean_array_fget(x_2, x_5);
lean_inc(x_8);
x_27 = l_Lean_Meta_getFVarLocalDecl(x_26, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_158; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_LocalDecl_type(x_28);
x_31 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(x_2, x_30);
x_32 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(x_24, x_31);
lean_dec(x_24);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_30);
x_158 = l_Lean_Meta_isProp(x_30, x_8, x_9, x_10, x_11, x_29);
if (lean_obj_tag(x_23) == 0)
{
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; uint8_t x_161; uint8_t x_162; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = 0;
x_162 = lean_unbox(x_159);
lean_dec(x_159);
x_33 = x_161;
x_34 = x_162;
x_35 = x_160;
goto block_157;
}
else
{
uint8_t x_163; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_163 = !lean_is_exclusive(x_158);
if (x_163 == 0)
{
return x_158;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_158, 0);
x_165 = lean_ctor_get(x_158, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_158);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; 
lean_inc(x_23);
x_167 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__2___boxed), 2, 1);
lean_closure_set(x_167, 0, x_23);
x_168 = lean_find_expr(x_167, x_30);
lean_dec(x_167);
if (lean_obj_tag(x_168) == 0)
{
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; uint8_t x_172; 
x_169 = lean_ctor_get(x_158, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_158, 1);
lean_inc(x_170);
lean_dec(x_158);
x_171 = 0;
x_172 = lean_unbox(x_169);
lean_dec(x_169);
x_33 = x_171;
x_34 = x_172;
x_35 = x_170;
goto block_157;
}
else
{
uint8_t x_173; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_173 = !lean_is_exclusive(x_158);
if (x_173 == 0)
{
return x_158;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_158, 0);
x_175 = lean_ctor_get(x_158, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_158);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
else
{
lean_dec(x_168);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; uint8_t x_180; 
x_177 = lean_ctor_get(x_158, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_158, 1);
lean_inc(x_178);
lean_dec(x_158);
x_179 = 1;
x_180 = lean_unbox(x_177);
lean_dec(x_177);
x_33 = x_179;
x_34 = x_180;
x_35 = x_178;
goto block_157;
}
else
{
uint8_t x_181; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_181 = !lean_is_exclusive(x_158);
if (x_181 == 0)
{
return x_158;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_158, 0);
x_183 = lean_ctor_get(x_158, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_158);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
}
block_157:
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_36 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__1;
x_37 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_30);
x_38 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_30, x_36, x_37, x_8, x_9, x_10, x_11, x_35);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_LocalDecl_binderInfo(x_28);
x_42 = lean_alloc_ctor(0, 1, 6);
lean_ctor_set(x_42, 0, x_31);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*1 + 1, x_37);
lean_ctor_set_uint8(x_42, sizeof(void*)*1 + 2, x_34);
x_43 = lean_unbox(x_39);
lean_dec(x_39);
lean_ctor_set_uint8(x_42, sizeof(void*)*1 + 3, x_43);
lean_ctor_set_uint8(x_42, sizeof(void*)*1 + 4, x_37);
lean_ctor_set_uint8(x_42, sizeof(void*)*1 + 5, x_33);
x_44 = lean_array_push(x_32, x_42);
x_45 = 3;
x_46 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_41, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_30);
lean_dec(x_28);
if (lean_is_scalar(x_25)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_25;
}
lean_ctor_set(x_47, 0, x_23);
lean_ctor_set(x_47, 1, x_44);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_16 = x_48;
x_17 = x_40;
goto block_22;
}
else
{
lean_object* x_49; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_30);
x_49 = l_Lean_Meta_isClass_x3f(x_30, x_8, x_9, x_10, x_11, x_40);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_30);
lean_dec(x_28);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
if (lean_is_scalar(x_25)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_25;
}
lean_ctor_set(x_52, 0, x_23);
lean_ctor_set(x_52, 1, x_44);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_16 = x_53;
x_17 = x_51;
goto block_22;
}
else
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_dec(x_49);
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_st_ref_get(x_11, x_54);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_getOutParamPositions_x3f(x_60, x_56);
lean_dec(x_56);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
lean_dec(x_30);
lean_dec(x_28);
if (lean_is_scalar(x_25)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_25;
}
lean_ctor_set(x_62, 0, x_23);
lean_ctor_set(x_62, 1, x_44);
lean_ctor_set(x_50, 0, x_62);
x_16 = x_50;
x_17 = x_59;
goto block_22;
}
else
{
uint8_t x_63; 
lean_free_object(x_50);
x_63 = !lean_is_exclusive(x_61);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_61, 0);
x_65 = l_Array_isEmpty___rarg(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_66 = lean_unsigned_to_nat(0u);
x_67 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_30, x_66);
x_68 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__2;
lean_inc(x_67);
x_69 = lean_mk_array(x_67, x_68);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_sub(x_67, x_70);
lean_dec(x_67);
x_72 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_30, x_69, x_71);
x_73 = lean_array_get_size(x_72);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_66);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_74, 2, x_70);
if (lean_is_scalar(x_25)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_25;
}
lean_ctor_set(x_75, 0, x_23);
lean_ctor_set(x_75, 1, x_44);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_76 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1(x_2, x_28, x_64, x_72, x_74, x_75, x_66, lean_box(0), lean_box(0), x_8, x_9, x_10, x_11, x_59);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_64);
lean_dec(x_28);
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
lean_ctor_set(x_61, 0, x_77);
x_16 = x_61;
x_17 = x_78;
goto block_22;
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
lean_ctor_set(x_61, 0, x_82);
x_16 = x_61;
x_17 = x_78;
goto block_22;
}
}
else
{
uint8_t x_83; 
lean_free_object(x_61);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
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
lean_dec(x_64);
lean_dec(x_30);
lean_dec(x_28);
if (lean_is_scalar(x_25)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_25;
}
lean_ctor_set(x_87, 0, x_23);
lean_ctor_set(x_87, 1, x_44);
lean_ctor_set(x_61, 0, x_87);
x_16 = x_61;
x_17 = x_59;
goto block_22;
}
}
else
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_61, 0);
lean_inc(x_88);
lean_dec(x_61);
x_89 = l_Array_isEmpty___rarg(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_90 = lean_unsigned_to_nat(0u);
x_91 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_30, x_90);
x_92 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__2;
lean_inc(x_91);
x_93 = lean_mk_array(x_91, x_92);
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_sub(x_91, x_94);
lean_dec(x_91);
x_96 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_30, x_93, x_95);
x_97 = lean_array_get_size(x_96);
x_98 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_98, 0, x_90);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set(x_98, 2, x_94);
if (lean_is_scalar(x_25)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_25;
}
lean_ctor_set(x_99, 0, x_23);
lean_ctor_set(x_99, 1, x_44);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_100 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1(x_2, x_28, x_88, x_96, x_98, x_99, x_90, lean_box(0), lean_box(0), x_8, x_9, x_10, x_11, x_59);
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_88);
lean_dec(x_28);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_105 = x_101;
} else {
 lean_dec_ref(x_101);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_16 = x_107;
x_17 = x_102;
goto block_22;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_108 = lean_ctor_get(x_100, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_100, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_110 = x_100;
} else {
 lean_dec_ref(x_100);
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
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_88);
lean_dec(x_30);
lean_dec(x_28);
if (lean_is_scalar(x_25)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_25;
}
lean_ctor_set(x_112, 0, x_23);
lean_ctor_set(x_112, 1, x_44);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_16 = x_113;
x_17 = x_59;
goto block_22;
}
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_114 = lean_ctor_get(x_50, 0);
lean_inc(x_114);
lean_dec(x_50);
x_115 = lean_st_ref_get(x_11, x_54);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_ctor_get(x_116, 0);
lean_inc(x_118);
lean_dec(x_116);
x_119 = l_Lean_getOutParamPositions_x3f(x_118, x_114);
lean_dec(x_114);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_30);
lean_dec(x_28);
if (lean_is_scalar(x_25)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_25;
}
lean_ctor_set(x_120, 0, x_23);
lean_ctor_set(x_120, 1, x_44);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_16 = x_121;
x_17 = x_117;
goto block_22;
}
else
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_122 = lean_ctor_get(x_119, 0);
lean_inc(x_122);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 x_123 = x_119;
} else {
 lean_dec_ref(x_119);
 x_123 = lean_box(0);
}
x_124 = l_Array_isEmpty___rarg(x_122);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_125 = lean_unsigned_to_nat(0u);
x_126 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_30, x_125);
x_127 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__2;
lean_inc(x_126);
x_128 = lean_mk_array(x_126, x_127);
x_129 = lean_unsigned_to_nat(1u);
x_130 = lean_nat_sub(x_126, x_129);
lean_dec(x_126);
x_131 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_30, x_128, x_130);
x_132 = lean_array_get_size(x_131);
x_133 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_133, 0, x_125);
lean_ctor_set(x_133, 1, x_132);
lean_ctor_set(x_133, 2, x_129);
if (lean_is_scalar(x_25)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_25;
}
lean_ctor_set(x_134, 0, x_23);
lean_ctor_set(x_134, 1, x_44);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_135 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1(x_2, x_28, x_122, x_131, x_133, x_134, x_125, lean_box(0), lean_box(0), x_8, x_9, x_10, x_11, x_117);
lean_dec(x_133);
lean_dec(x_131);
lean_dec(x_122);
lean_dec(x_28);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_ctor_get(x_136, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_140 = x_136;
} else {
 lean_dec_ref(x_136);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_139);
if (lean_is_scalar(x_123)) {
 x_142 = lean_alloc_ctor(1, 1, 0);
} else {
 x_142 = x_123;
}
lean_ctor_set(x_142, 0, x_141);
x_16 = x_142;
x_17 = x_137;
goto block_22;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_123);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_143 = lean_ctor_get(x_135, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_135, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_145 = x_135;
} else {
 lean_dec_ref(x_135);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_122);
lean_dec(x_30);
lean_dec(x_28);
if (lean_is_scalar(x_25)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_25;
}
lean_ctor_set(x_147, 0, x_23);
lean_ctor_set(x_147, 1, x_44);
if (lean_is_scalar(x_123)) {
 x_148 = lean_alloc_ctor(1, 1, 0);
} else {
 x_148 = x_123;
}
lean_ctor_set(x_148, 0, x_147);
x_16 = x_148;
x_17 = x_117;
goto block_22;
}
}
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_44);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_149 = !lean_is_exclusive(x_49);
if (x_149 == 0)
{
return x_49;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_49, 0);
x_151 = lean_ctor_get(x_49, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_49);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
}
else
{
uint8_t x_153; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_153 = !lean_is_exclusive(x_38);
if (x_153 == 0)
{
return x_38;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_38, 0);
x_155 = lean_ctor_get(x_38, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_38);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
}
else
{
uint8_t x_185; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_185 = !lean_is_exclusive(x_27);
if (x_185 == 0)
{
return x_27;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_27, 0);
x_187 = lean_ctor_get(x_27, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_27);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
block_22:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_3, 2);
x_20 = lean_nat_add(x_5, x_19);
lean_dec(x_5);
x_4 = x_18;
x_5 = x_20;
x_6 = lean_box(0);
x_7 = lean_box(0);
x_12 = x_17;
goto _start;
}
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
x_13 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1___closed__1;
x_14 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__4(x_1, x_2, x_12, x_13, x_10, lean_box(0), lean_box(0), x_4, x_5, x_6, x_7, x_8);
lean_dec(x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_16, 1);
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(x_2, x_3);
x_21 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(x_18, x_20);
lean_dec(x_18);
lean_ctor_set(x_16, 1, x_20);
lean_ctor_set(x_16, 0, x_21);
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(x_2, x_3);
x_24 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(x_22, x_23);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
x_30 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(x_2, x_3);
x_31 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(x_28, x_30);
lean_dec(x_28);
if (lean_is_scalar(x_29)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_29;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_14);
if (x_34 == 0)
{
return x_14;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_14, 0);
x_36 = lean_ctor_get(x_14, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_14);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
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
static uint64_t _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__4() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 1;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_58; uint8_t x_59; 
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Lean_Meta_mkInfoCacheKey(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_58 = lean_st_ref_get(x_4, x_10);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__1(x_63, x_9);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
lean_free_object(x_58);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_65 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_61);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__3;
x_69 = lean_alloc_closure((void*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1___boxed), 8, 1);
lean_closure_set(x_69, 0, x_68);
x_70 = !lean_is_exclusive(x_3);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_3, 0);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
uint64_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; 
x_73 = lean_ctor_get_uint64(x_3, sizeof(void*)*7);
x_74 = lean_ctor_get_uint8(x_71, 9);
x_75 = 1;
x_76 = l_Lean_Meta_TransparencyMode_lt(x_74, x_75);
x_77 = 2;
x_78 = lean_uint64_shift_right(x_73, x_77);
x_79 = lean_uint64_shift_left(x_78, x_77);
if (x_76 == 0)
{
uint64_t x_80; uint64_t x_81; uint8_t x_82; lean_object* x_83; 
x_80 = l_Lean_Meta_TransparencyMode_toUInt64(x_74);
x_81 = lean_uint64_lor(x_79, x_80);
lean_ctor_set_uint64(x_3, sizeof(void*)*7, x_81);
x_82 = 0;
lean_inc(x_4);
x_83 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg(x_66, x_2, x_69, x_82, x_3, x_4, x_5, x_6, x_67);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_11 = x_84;
x_12 = x_85;
goto block_57;
}
else
{
uint8_t x_86; 
lean_dec(x_9);
lean_dec(x_4);
x_86 = !lean_is_exclusive(x_83);
if (x_86 == 0)
{
return x_83;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_83, 0);
x_88 = lean_ctor_get(x_83, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_83);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint64_t x_90; uint64_t x_91; uint8_t x_92; lean_object* x_93; 
lean_ctor_set_uint8(x_71, 9, x_75);
x_90 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__4;
x_91 = lean_uint64_lor(x_79, x_90);
lean_ctor_set_uint64(x_3, sizeof(void*)*7, x_91);
x_92 = 0;
lean_inc(x_4);
x_93 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg(x_66, x_2, x_69, x_92, x_3, x_4, x_5, x_6, x_67);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_11 = x_94;
x_12 = x_95;
goto block_57;
}
else
{
uint8_t x_96; 
lean_dec(x_9);
lean_dec(x_4);
x_96 = !lean_is_exclusive(x_93);
if (x_96 == 0)
{
return x_93;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_93, 0);
x_98 = lean_ctor_get(x_93, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_93);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
else
{
uint64_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint64_t x_121; uint64_t x_122; uint64_t x_123; 
x_100 = lean_ctor_get_uint64(x_3, sizeof(void*)*7);
x_101 = lean_ctor_get_uint8(x_71, 0);
x_102 = lean_ctor_get_uint8(x_71, 1);
x_103 = lean_ctor_get_uint8(x_71, 2);
x_104 = lean_ctor_get_uint8(x_71, 3);
x_105 = lean_ctor_get_uint8(x_71, 4);
x_106 = lean_ctor_get_uint8(x_71, 5);
x_107 = lean_ctor_get_uint8(x_71, 6);
x_108 = lean_ctor_get_uint8(x_71, 7);
x_109 = lean_ctor_get_uint8(x_71, 8);
x_110 = lean_ctor_get_uint8(x_71, 9);
x_111 = lean_ctor_get_uint8(x_71, 10);
x_112 = lean_ctor_get_uint8(x_71, 11);
x_113 = lean_ctor_get_uint8(x_71, 12);
x_114 = lean_ctor_get_uint8(x_71, 13);
x_115 = lean_ctor_get_uint8(x_71, 14);
x_116 = lean_ctor_get_uint8(x_71, 15);
x_117 = lean_ctor_get_uint8(x_71, 16);
x_118 = lean_ctor_get_uint8(x_71, 17);
lean_dec(x_71);
x_119 = 1;
x_120 = l_Lean_Meta_TransparencyMode_lt(x_110, x_119);
x_121 = 2;
x_122 = lean_uint64_shift_right(x_100, x_121);
x_123 = lean_uint64_shift_left(x_122, x_121);
if (x_120 == 0)
{
lean_object* x_124; uint64_t x_125; uint64_t x_126; uint8_t x_127; lean_object* x_128; 
x_124 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_124, 0, x_101);
lean_ctor_set_uint8(x_124, 1, x_102);
lean_ctor_set_uint8(x_124, 2, x_103);
lean_ctor_set_uint8(x_124, 3, x_104);
lean_ctor_set_uint8(x_124, 4, x_105);
lean_ctor_set_uint8(x_124, 5, x_106);
lean_ctor_set_uint8(x_124, 6, x_107);
lean_ctor_set_uint8(x_124, 7, x_108);
lean_ctor_set_uint8(x_124, 8, x_109);
lean_ctor_set_uint8(x_124, 9, x_110);
lean_ctor_set_uint8(x_124, 10, x_111);
lean_ctor_set_uint8(x_124, 11, x_112);
lean_ctor_set_uint8(x_124, 12, x_113);
lean_ctor_set_uint8(x_124, 13, x_114);
lean_ctor_set_uint8(x_124, 14, x_115);
lean_ctor_set_uint8(x_124, 15, x_116);
lean_ctor_set_uint8(x_124, 16, x_117);
lean_ctor_set_uint8(x_124, 17, x_118);
x_125 = l_Lean_Meta_TransparencyMode_toUInt64(x_110);
x_126 = lean_uint64_lor(x_123, x_125);
lean_ctor_set(x_3, 0, x_124);
lean_ctor_set_uint64(x_3, sizeof(void*)*7, x_126);
x_127 = 0;
lean_inc(x_4);
x_128 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg(x_66, x_2, x_69, x_127, x_3, x_4, x_5, x_6, x_67);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_11 = x_129;
x_12 = x_130;
goto block_57;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_9);
lean_dec(x_4);
x_131 = lean_ctor_get(x_128, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_128, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_133 = x_128;
} else {
 lean_dec_ref(x_128);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
else
{
lean_object* x_135; uint64_t x_136; uint64_t x_137; uint8_t x_138; lean_object* x_139; 
x_135 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_135, 0, x_101);
lean_ctor_set_uint8(x_135, 1, x_102);
lean_ctor_set_uint8(x_135, 2, x_103);
lean_ctor_set_uint8(x_135, 3, x_104);
lean_ctor_set_uint8(x_135, 4, x_105);
lean_ctor_set_uint8(x_135, 5, x_106);
lean_ctor_set_uint8(x_135, 6, x_107);
lean_ctor_set_uint8(x_135, 7, x_108);
lean_ctor_set_uint8(x_135, 8, x_109);
lean_ctor_set_uint8(x_135, 9, x_119);
lean_ctor_set_uint8(x_135, 10, x_111);
lean_ctor_set_uint8(x_135, 11, x_112);
lean_ctor_set_uint8(x_135, 12, x_113);
lean_ctor_set_uint8(x_135, 13, x_114);
lean_ctor_set_uint8(x_135, 14, x_115);
lean_ctor_set_uint8(x_135, 15, x_116);
lean_ctor_set_uint8(x_135, 16, x_117);
lean_ctor_set_uint8(x_135, 17, x_118);
x_136 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__4;
x_137 = lean_uint64_lor(x_123, x_136);
lean_ctor_set(x_3, 0, x_135);
lean_ctor_set_uint64(x_3, sizeof(void*)*7, x_137);
x_138 = 0;
lean_inc(x_4);
x_139 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg(x_66, x_2, x_69, x_138, x_3, x_4, x_5, x_6, x_67);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_11 = x_140;
x_12 = x_141;
goto block_57;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_9);
lean_dec(x_4);
x_142 = lean_ctor_get(x_139, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_139, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_144 = x_139;
} else {
 lean_dec_ref(x_139);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
}
}
else
{
lean_object* x_146; uint64_t x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; uint8_t x_156; uint8_t x_157; uint8_t x_158; uint8_t x_159; uint8_t x_160; uint8_t x_161; uint8_t x_162; uint8_t x_163; uint8_t x_164; uint8_t x_165; uint8_t x_166; uint8_t x_167; uint8_t x_168; uint8_t x_169; uint8_t x_170; uint8_t x_171; uint8_t x_172; uint8_t x_173; uint8_t x_174; lean_object* x_175; uint8_t x_176; uint8_t x_177; uint64_t x_178; uint64_t x_179; uint64_t x_180; 
x_146 = lean_ctor_get(x_3, 0);
x_147 = lean_ctor_get_uint64(x_3, sizeof(void*)*7);
x_148 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_149 = lean_ctor_get(x_3, 1);
x_150 = lean_ctor_get(x_3, 2);
x_151 = lean_ctor_get(x_3, 3);
x_152 = lean_ctor_get(x_3, 4);
x_153 = lean_ctor_get(x_3, 5);
x_154 = lean_ctor_get(x_3, 6);
x_155 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_156 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_146);
lean_dec(x_3);
x_157 = lean_ctor_get_uint8(x_146, 0);
x_158 = lean_ctor_get_uint8(x_146, 1);
x_159 = lean_ctor_get_uint8(x_146, 2);
x_160 = lean_ctor_get_uint8(x_146, 3);
x_161 = lean_ctor_get_uint8(x_146, 4);
x_162 = lean_ctor_get_uint8(x_146, 5);
x_163 = lean_ctor_get_uint8(x_146, 6);
x_164 = lean_ctor_get_uint8(x_146, 7);
x_165 = lean_ctor_get_uint8(x_146, 8);
x_166 = lean_ctor_get_uint8(x_146, 9);
x_167 = lean_ctor_get_uint8(x_146, 10);
x_168 = lean_ctor_get_uint8(x_146, 11);
x_169 = lean_ctor_get_uint8(x_146, 12);
x_170 = lean_ctor_get_uint8(x_146, 13);
x_171 = lean_ctor_get_uint8(x_146, 14);
x_172 = lean_ctor_get_uint8(x_146, 15);
x_173 = lean_ctor_get_uint8(x_146, 16);
x_174 = lean_ctor_get_uint8(x_146, 17);
if (lean_is_exclusive(x_146)) {
 x_175 = x_146;
} else {
 lean_dec_ref(x_146);
 x_175 = lean_box(0);
}
x_176 = 1;
x_177 = l_Lean_Meta_TransparencyMode_lt(x_166, x_176);
x_178 = 2;
x_179 = lean_uint64_shift_right(x_147, x_178);
x_180 = lean_uint64_shift_left(x_179, x_178);
if (x_177 == 0)
{
lean_object* x_181; uint64_t x_182; uint64_t x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; 
if (lean_is_scalar(x_175)) {
 x_181 = lean_alloc_ctor(0, 0, 18);
} else {
 x_181 = x_175;
}
lean_ctor_set_uint8(x_181, 0, x_157);
lean_ctor_set_uint8(x_181, 1, x_158);
lean_ctor_set_uint8(x_181, 2, x_159);
lean_ctor_set_uint8(x_181, 3, x_160);
lean_ctor_set_uint8(x_181, 4, x_161);
lean_ctor_set_uint8(x_181, 5, x_162);
lean_ctor_set_uint8(x_181, 6, x_163);
lean_ctor_set_uint8(x_181, 7, x_164);
lean_ctor_set_uint8(x_181, 8, x_165);
lean_ctor_set_uint8(x_181, 9, x_166);
lean_ctor_set_uint8(x_181, 10, x_167);
lean_ctor_set_uint8(x_181, 11, x_168);
lean_ctor_set_uint8(x_181, 12, x_169);
lean_ctor_set_uint8(x_181, 13, x_170);
lean_ctor_set_uint8(x_181, 14, x_171);
lean_ctor_set_uint8(x_181, 15, x_172);
lean_ctor_set_uint8(x_181, 16, x_173);
lean_ctor_set_uint8(x_181, 17, x_174);
x_182 = l_Lean_Meta_TransparencyMode_toUInt64(x_166);
x_183 = lean_uint64_lor(x_180, x_182);
x_184 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_149);
lean_ctor_set(x_184, 2, x_150);
lean_ctor_set(x_184, 3, x_151);
lean_ctor_set(x_184, 4, x_152);
lean_ctor_set(x_184, 5, x_153);
lean_ctor_set(x_184, 6, x_154);
lean_ctor_set_uint64(x_184, sizeof(void*)*7, x_183);
lean_ctor_set_uint8(x_184, sizeof(void*)*7 + 8, x_148);
lean_ctor_set_uint8(x_184, sizeof(void*)*7 + 9, x_155);
lean_ctor_set_uint8(x_184, sizeof(void*)*7 + 10, x_156);
x_185 = 0;
lean_inc(x_4);
x_186 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg(x_66, x_2, x_69, x_185, x_184, x_4, x_5, x_6, x_67);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_11 = x_187;
x_12 = x_188;
goto block_57;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_9);
lean_dec(x_4);
x_189 = lean_ctor_get(x_186, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_186, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_191 = x_186;
} else {
 lean_dec_ref(x_186);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(1, 2, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_190);
return x_192;
}
}
else
{
lean_object* x_193; uint64_t x_194; uint64_t x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; 
if (lean_is_scalar(x_175)) {
 x_193 = lean_alloc_ctor(0, 0, 18);
} else {
 x_193 = x_175;
}
lean_ctor_set_uint8(x_193, 0, x_157);
lean_ctor_set_uint8(x_193, 1, x_158);
lean_ctor_set_uint8(x_193, 2, x_159);
lean_ctor_set_uint8(x_193, 3, x_160);
lean_ctor_set_uint8(x_193, 4, x_161);
lean_ctor_set_uint8(x_193, 5, x_162);
lean_ctor_set_uint8(x_193, 6, x_163);
lean_ctor_set_uint8(x_193, 7, x_164);
lean_ctor_set_uint8(x_193, 8, x_165);
lean_ctor_set_uint8(x_193, 9, x_176);
lean_ctor_set_uint8(x_193, 10, x_167);
lean_ctor_set_uint8(x_193, 11, x_168);
lean_ctor_set_uint8(x_193, 12, x_169);
lean_ctor_set_uint8(x_193, 13, x_170);
lean_ctor_set_uint8(x_193, 14, x_171);
lean_ctor_set_uint8(x_193, 15, x_172);
lean_ctor_set_uint8(x_193, 16, x_173);
lean_ctor_set_uint8(x_193, 17, x_174);
x_194 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__4;
x_195 = lean_uint64_lor(x_180, x_194);
x_196 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set(x_196, 1, x_149);
lean_ctor_set(x_196, 2, x_150);
lean_ctor_set(x_196, 3, x_151);
lean_ctor_set(x_196, 4, x_152);
lean_ctor_set(x_196, 5, x_153);
lean_ctor_set(x_196, 6, x_154);
lean_ctor_set_uint64(x_196, sizeof(void*)*7, x_195);
lean_ctor_set_uint8(x_196, sizeof(void*)*7 + 8, x_148);
lean_ctor_set_uint8(x_196, sizeof(void*)*7 + 9, x_155);
lean_ctor_set_uint8(x_196, sizeof(void*)*7 + 10, x_156);
x_197 = 0;
lean_inc(x_4);
x_198 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg(x_66, x_2, x_69, x_197, x_196, x_4, x_5, x_6, x_67);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_11 = x_199;
x_12 = x_200;
goto block_57;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_9);
lean_dec(x_4);
x_201 = lean_ctor_get(x_198, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_198, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_203 = x_198;
} else {
 lean_dec_ref(x_198);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
}
}
}
else
{
uint8_t x_205; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_205 = !lean_is_exclusive(x_65);
if (x_205 == 0)
{
return x_65;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_65, 0);
x_207 = lean_ctor_get(x_65, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_65);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
else
{
lean_object* x_209; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_209 = lean_ctor_get(x_64, 0);
lean_inc(x_209);
lean_dec(x_64);
lean_ctor_set(x_58, 0, x_209);
return x_58;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_210 = lean_ctor_get(x_58, 0);
x_211 = lean_ctor_get(x_58, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_58);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
lean_dec(x_212);
x_214 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__1(x_213, x_9);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_215 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_211);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint64_t x_221; uint8_t x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; uint8_t x_230; lean_object* x_231; uint8_t x_232; uint8_t x_233; uint8_t x_234; uint8_t x_235; uint8_t x_236; uint8_t x_237; uint8_t x_238; uint8_t x_239; uint8_t x_240; uint8_t x_241; uint8_t x_242; uint8_t x_243; uint8_t x_244; uint8_t x_245; uint8_t x_246; uint8_t x_247; uint8_t x_248; uint8_t x_249; lean_object* x_250; uint8_t x_251; uint8_t x_252; uint64_t x_253; uint64_t x_254; uint64_t x_255; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_218 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__3;
x_219 = lean_alloc_closure((void*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1___boxed), 8, 1);
lean_closure_set(x_219, 0, x_218);
x_220 = lean_ctor_get(x_3, 0);
lean_inc(x_220);
x_221 = lean_ctor_get_uint64(x_3, sizeof(void*)*7);
x_222 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_223 = lean_ctor_get(x_3, 1);
lean_inc(x_223);
x_224 = lean_ctor_get(x_3, 2);
lean_inc(x_224);
x_225 = lean_ctor_get(x_3, 3);
lean_inc(x_225);
x_226 = lean_ctor_get(x_3, 4);
lean_inc(x_226);
x_227 = lean_ctor_get(x_3, 5);
lean_inc(x_227);
x_228 = lean_ctor_get(x_3, 6);
lean_inc(x_228);
x_229 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_230 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 x_231 = x_3;
} else {
 lean_dec_ref(x_3);
 x_231 = lean_box(0);
}
x_232 = lean_ctor_get_uint8(x_220, 0);
x_233 = lean_ctor_get_uint8(x_220, 1);
x_234 = lean_ctor_get_uint8(x_220, 2);
x_235 = lean_ctor_get_uint8(x_220, 3);
x_236 = lean_ctor_get_uint8(x_220, 4);
x_237 = lean_ctor_get_uint8(x_220, 5);
x_238 = lean_ctor_get_uint8(x_220, 6);
x_239 = lean_ctor_get_uint8(x_220, 7);
x_240 = lean_ctor_get_uint8(x_220, 8);
x_241 = lean_ctor_get_uint8(x_220, 9);
x_242 = lean_ctor_get_uint8(x_220, 10);
x_243 = lean_ctor_get_uint8(x_220, 11);
x_244 = lean_ctor_get_uint8(x_220, 12);
x_245 = lean_ctor_get_uint8(x_220, 13);
x_246 = lean_ctor_get_uint8(x_220, 14);
x_247 = lean_ctor_get_uint8(x_220, 15);
x_248 = lean_ctor_get_uint8(x_220, 16);
x_249 = lean_ctor_get_uint8(x_220, 17);
if (lean_is_exclusive(x_220)) {
 x_250 = x_220;
} else {
 lean_dec_ref(x_220);
 x_250 = lean_box(0);
}
x_251 = 1;
x_252 = l_Lean_Meta_TransparencyMode_lt(x_241, x_251);
x_253 = 2;
x_254 = lean_uint64_shift_right(x_221, x_253);
x_255 = lean_uint64_shift_left(x_254, x_253);
if (x_252 == 0)
{
lean_object* x_256; uint64_t x_257; uint64_t x_258; lean_object* x_259; uint8_t x_260; lean_object* x_261; 
if (lean_is_scalar(x_250)) {
 x_256 = lean_alloc_ctor(0, 0, 18);
} else {
 x_256 = x_250;
}
lean_ctor_set_uint8(x_256, 0, x_232);
lean_ctor_set_uint8(x_256, 1, x_233);
lean_ctor_set_uint8(x_256, 2, x_234);
lean_ctor_set_uint8(x_256, 3, x_235);
lean_ctor_set_uint8(x_256, 4, x_236);
lean_ctor_set_uint8(x_256, 5, x_237);
lean_ctor_set_uint8(x_256, 6, x_238);
lean_ctor_set_uint8(x_256, 7, x_239);
lean_ctor_set_uint8(x_256, 8, x_240);
lean_ctor_set_uint8(x_256, 9, x_241);
lean_ctor_set_uint8(x_256, 10, x_242);
lean_ctor_set_uint8(x_256, 11, x_243);
lean_ctor_set_uint8(x_256, 12, x_244);
lean_ctor_set_uint8(x_256, 13, x_245);
lean_ctor_set_uint8(x_256, 14, x_246);
lean_ctor_set_uint8(x_256, 15, x_247);
lean_ctor_set_uint8(x_256, 16, x_248);
lean_ctor_set_uint8(x_256, 17, x_249);
x_257 = l_Lean_Meta_TransparencyMode_toUInt64(x_241);
x_258 = lean_uint64_lor(x_255, x_257);
if (lean_is_scalar(x_231)) {
 x_259 = lean_alloc_ctor(0, 7, 11);
} else {
 x_259 = x_231;
}
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_223);
lean_ctor_set(x_259, 2, x_224);
lean_ctor_set(x_259, 3, x_225);
lean_ctor_set(x_259, 4, x_226);
lean_ctor_set(x_259, 5, x_227);
lean_ctor_set(x_259, 6, x_228);
lean_ctor_set_uint64(x_259, sizeof(void*)*7, x_258);
lean_ctor_set_uint8(x_259, sizeof(void*)*7 + 8, x_222);
lean_ctor_set_uint8(x_259, sizeof(void*)*7 + 9, x_229);
lean_ctor_set_uint8(x_259, sizeof(void*)*7 + 10, x_230);
x_260 = 0;
lean_inc(x_4);
x_261 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg(x_216, x_2, x_219, x_260, x_259, x_4, x_5, x_6, x_217);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_11 = x_262;
x_12 = x_263;
goto block_57;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_9);
lean_dec(x_4);
x_264 = lean_ctor_get(x_261, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_261, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_266 = x_261;
} else {
 lean_dec_ref(x_261);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_264);
lean_ctor_set(x_267, 1, x_265);
return x_267;
}
}
else
{
lean_object* x_268; uint64_t x_269; uint64_t x_270; lean_object* x_271; uint8_t x_272; lean_object* x_273; 
if (lean_is_scalar(x_250)) {
 x_268 = lean_alloc_ctor(0, 0, 18);
} else {
 x_268 = x_250;
}
lean_ctor_set_uint8(x_268, 0, x_232);
lean_ctor_set_uint8(x_268, 1, x_233);
lean_ctor_set_uint8(x_268, 2, x_234);
lean_ctor_set_uint8(x_268, 3, x_235);
lean_ctor_set_uint8(x_268, 4, x_236);
lean_ctor_set_uint8(x_268, 5, x_237);
lean_ctor_set_uint8(x_268, 6, x_238);
lean_ctor_set_uint8(x_268, 7, x_239);
lean_ctor_set_uint8(x_268, 8, x_240);
lean_ctor_set_uint8(x_268, 9, x_251);
lean_ctor_set_uint8(x_268, 10, x_242);
lean_ctor_set_uint8(x_268, 11, x_243);
lean_ctor_set_uint8(x_268, 12, x_244);
lean_ctor_set_uint8(x_268, 13, x_245);
lean_ctor_set_uint8(x_268, 14, x_246);
lean_ctor_set_uint8(x_268, 15, x_247);
lean_ctor_set_uint8(x_268, 16, x_248);
lean_ctor_set_uint8(x_268, 17, x_249);
x_269 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__4;
x_270 = lean_uint64_lor(x_255, x_269);
if (lean_is_scalar(x_231)) {
 x_271 = lean_alloc_ctor(0, 7, 11);
} else {
 x_271 = x_231;
}
lean_ctor_set(x_271, 0, x_268);
lean_ctor_set(x_271, 1, x_223);
lean_ctor_set(x_271, 2, x_224);
lean_ctor_set(x_271, 3, x_225);
lean_ctor_set(x_271, 4, x_226);
lean_ctor_set(x_271, 5, x_227);
lean_ctor_set(x_271, 6, x_228);
lean_ctor_set_uint64(x_271, sizeof(void*)*7, x_270);
lean_ctor_set_uint8(x_271, sizeof(void*)*7 + 8, x_222);
lean_ctor_set_uint8(x_271, sizeof(void*)*7 + 9, x_229);
lean_ctor_set_uint8(x_271, sizeof(void*)*7 + 10, x_230);
x_272 = 0;
lean_inc(x_4);
x_273 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg(x_216, x_2, x_219, x_272, x_271, x_4, x_5, x_6, x_217);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec(x_273);
x_11 = x_274;
x_12 = x_275;
goto block_57;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_9);
lean_dec(x_4);
x_276 = lean_ctor_get(x_273, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_273, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_278 = x_273;
} else {
 lean_dec_ref(x_273);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(1, 2, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_276);
lean_ctor_set(x_279, 1, x_277);
return x_279;
}
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_280 = lean_ctor_get(x_215, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_215, 1);
lean_inc(x_281);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_282 = x_215;
} else {
 lean_dec_ref(x_215);
 x_282 = lean_box(0);
}
if (lean_is_scalar(x_282)) {
 x_283 = lean_alloc_ctor(1, 2, 0);
} else {
 x_283 = x_282;
}
lean_ctor_set(x_283, 0, x_280);
lean_ctor_set(x_283, 1, x_281);
return x_283;
}
}
else
{
lean_object* x_284; lean_object* x_285; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_284 = lean_ctor_get(x_214, 0);
lean_inc(x_284);
lean_dec(x_214);
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_211);
return x_285;
}
}
block_57:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_st_ref_take(x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_14, 1);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_11);
x_21 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(x_20, x_9, x_11);
lean_ctor_set(x_15, 1, x_21);
x_22 = lean_st_ref_set(x_4, x_14, x_16);
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_11);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_11);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 2);
x_29 = lean_ctor_get(x_15, 3);
x_30 = lean_ctor_get(x_15, 4);
x_31 = lean_ctor_get(x_15, 5);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_32);
lean_inc(x_27);
lean_dec(x_15);
lean_inc(x_11);
x_33 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(x_32, x_9, x_11);
x_34 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_28);
lean_ctor_set(x_34, 3, x_29);
lean_ctor_set(x_34, 4, x_30);
lean_ctor_set(x_34, 5, x_31);
lean_ctor_set(x_14, 1, x_34);
x_35 = lean_st_ref_set(x_4, x_14, x_16);
lean_dec(x_4);
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
lean_ctor_set(x_38, 0, x_11);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_39 = lean_ctor_get(x_14, 0);
x_40 = lean_ctor_get(x_14, 2);
x_41 = lean_ctor_get(x_14, 3);
x_42 = lean_ctor_get(x_14, 4);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_14);
x_43 = lean_ctor_get(x_15, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_15, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_15, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_15, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_15, 5);
lean_inc(x_47);
x_48 = lean_ctor_get(x_15, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 lean_ctor_release(x_15, 3);
 lean_ctor_release(x_15, 4);
 lean_ctor_release(x_15, 5);
 x_49 = x_15;
} else {
 lean_dec_ref(x_15);
 x_49 = lean_box(0);
}
lean_inc(x_11);
x_50 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(x_48, x_9, x_11);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 6, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_44);
lean_ctor_set(x_51, 3, x_45);
lean_ctor_set(x_51, 4, x_46);
lean_ctor_set(x_51, 5, x_47);
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_39);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_40);
lean_ctor_set(x_52, 3, x_41);
lean_ctor_set(x_52, 4, x_42);
x_53 = lean_st_ref_set(x_4, x_52, x_16);
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
lean_ctor_set(x_56, 0, x_11);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
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
l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___closed__1 = _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___closed__1);
l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___closed__2 = _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___closed__2();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___closed__2);
l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__1 = _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__1();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__1);
l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__2 = _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__2();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__2);
l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1___closed__1 = _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1___closed__1);
l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__1 = _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__1();
lean_mark_persistent(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__1);
l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__2 = _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__2();
lean_mark_persistent(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__2);
l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__3 = _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__3();
lean_mark_persistent(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__3);
l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__4 = _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__4();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
