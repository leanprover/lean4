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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__6(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
uint8_t l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_359_(lean_object*, lean_object*);
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
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeReaderT___rarg(lean_object*);
size_t lean_usize_of_nat(lean_object*);
static size_t l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2___closed__1;
uint64_t l_Lean_Meta_TransparencyMode_hash(uint8_t);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_getOutParamPositions_x3f(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__3(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
lean_object* l_Lean_Meta_getTransparency(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__5(lean_object*);
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
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__1___closed__2;
lean_object* l_Lean_Expr_FindImpl_findUnsafe_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlT__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_whenHasVar(lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(uint8_t, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT lean_object* l_Array_indexOfAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadCoreM;
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4___closed__1;
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
static lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__1;
static size_t l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2(lean_object*, size_t, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_359_(x_5, x_9);
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
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_359_(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_usize_shift_right(x_2, x_5);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__3(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = l_Lean_Meta_TransparencyMode_hash(x_4);
x_8 = l_Lean_Expr_hash(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; lean_object* x_13; 
x_9 = 11;
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = lean_uint64_mix_hash(x_7, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2(x_3, x_12, x_2);
lean_dec(x_2);
return x_13;
}
else
{
lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; size_t x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_uint64_of_nat(x_14);
lean_dec(x_14);
x_16 = 13;
x_17 = lean_uint64_mix_hash(x_15, x_16);
x_18 = lean_uint64_mix_hash(x_8, x_17);
x_19 = lean_uint64_mix_hash(x_7, x_18);
x_20 = lean_uint64_to_usize(x_19);
x_21 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__2(x_3, x_20, x_2);
lean_dec(x_2);
return x_21;
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
x_18 = l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_359_(x_3, x_17);
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
x_21 = l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_359_(x_4, x_19);
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
x_28 = l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_359_(x_4, x_26);
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
x_63 = l___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_359_(x_4, x_60);
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
static lean_object* _init_l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; 
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
uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; lean_object* x_19; 
x_15 = 11;
x_16 = lean_uint64_mix_hash(x_14, x_15);
x_17 = lean_uint64_mix_hash(x_13, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(x_5, x_18, x_7, x_2, x_3);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_19);
return x_1;
}
else
{
lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; size_t x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_uint64_of_nat(x_20);
lean_dec(x_20);
x_22 = 13;
x_23 = lean_uint64_mix_hash(x_21, x_22);
x_24 = lean_uint64_mix_hash(x_14, x_23);
x_25 = lean_uint64_mix_hash(x_13, x_24);
x_26 = lean_uint64_to_usize(x_25);
x_27 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(x_5, x_26, x_7, x_2, x_3);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_27);
return x_1;
}
}
else
{
lean_object* x_28; lean_object* x_29; size_t x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; uint64_t x_36; uint64_t x_37; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_1);
x_30 = 1;
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_29, x_31);
lean_dec(x_29);
x_33 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
x_36 = l_Lean_Meta_TransparencyMode_hash(x_33);
x_37 = l_Lean_Expr_hash(x_34);
lean_dec(x_34);
if (lean_obj_tag(x_35) == 0)
{
uint64_t x_38; uint64_t x_39; uint64_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_38 = 11;
x_39 = lean_uint64_mix_hash(x_37, x_38);
x_40 = lean_uint64_mix_hash(x_36, x_39);
x_41 = lean_uint64_to_usize(x_40);
x_42 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(x_28, x_41, x_30, x_2, x_3);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_32);
return x_43;
}
else
{
lean_object* x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; size_t x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_35, 0);
lean_inc(x_44);
lean_dec(x_35);
x_45 = lean_uint64_of_nat(x_44);
lean_dec(x_44);
x_46 = 13;
x_47 = lean_uint64_mix_hash(x_45, x_46);
x_48 = lean_uint64_mix_hash(x_37, x_47);
x_49 = lean_uint64_mix_hash(x_36, x_48);
x_50 = lean_uint64_to_usize(x_49);
x_51 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__5(x_28, x_50, x_30, x_2, x_3);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_32);
return x_52;
}
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
lean_inc(x_18);
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
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_51 = lean_ctor_get(x_25, 0);
x_52 = lean_ctor_get(x_25, 2);
x_53 = lean_ctor_get(x_25, 3);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_25);
x_54 = lean_ctor_get(x_26, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_26, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_26, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_26, 4);
lean_inc(x_57);
x_58 = lean_ctor_get(x_26, 5);
lean_inc(x_58);
x_59 = lean_ctor_get(x_26, 6);
lean_inc(x_59);
x_60 = lean_ctor_get(x_26, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 lean_ctor_release(x_26, 3);
 lean_ctor_release(x_26, 4);
 lean_ctor_release(x_26, 5);
 lean_ctor_release(x_26, 6);
 x_61 = x_26;
} else {
 lean_dec_ref(x_26);
 x_61 = lean_box(0);
}
lean_inc(x_22);
x_62 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(x_60, x_18, x_22);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 7, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_54);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_55);
lean_ctor_set(x_63, 3, x_56);
lean_ctor_set(x_63, 4, x_57);
lean_ctor_set(x_63, 5, x_58);
lean_ctor_set(x_63, 6, x_59);
x_64 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_64, 0, x_51);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_52);
lean_ctor_set(x_64, 3, x_53);
x_65 = lean_st_ref_set(x_5, x_64, x_27);
lean_dec(x_5);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_22);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_18);
lean_dec(x_5);
x_69 = !lean_is_exclusive(x_21);
if (x_69 == 0)
{
return x_21;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_21, 0);
x_71 = lean_ctor_get(x_21, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_21);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_73 = lean_ctor_get(x_20, 0);
lean_inc(x_73);
lean_dec(x_20);
lean_ctor_set(x_12, 0, x_73);
return x_12;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; 
x_74 = lean_ctor_get(x_12, 0);
x_75 = lean_ctor_get(x_12, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_12);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_2);
x_79 = lean_unbox(x_10);
lean_dec(x_10);
lean_ctor_set_uint8(x_78, sizeof(void*)*2, x_79);
lean_inc(x_78);
x_80 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__1(x_77, x_78);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
lean_inc(x_5);
x_81 = lean_apply_5(x_3, x_4, x_5, x_6, x_7, x_75);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_st_ref_take(x_5, x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec(x_84);
x_88 = lean_ctor_get(x_85, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_85, 2);
lean_inc(x_89);
x_90 = lean_ctor_get(x_85, 3);
lean_inc(x_90);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 lean_ctor_release(x_85, 2);
 lean_ctor_release(x_85, 3);
 x_91 = x_85;
} else {
 lean_dec_ref(x_85);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_86, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_86, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_86, 3);
lean_inc(x_94);
x_95 = lean_ctor_get(x_86, 4);
lean_inc(x_95);
x_96 = lean_ctor_get(x_86, 5);
lean_inc(x_96);
x_97 = lean_ctor_get(x_86, 6);
lean_inc(x_97);
x_98 = lean_ctor_get(x_86, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 lean_ctor_release(x_86, 2);
 lean_ctor_release(x_86, 3);
 lean_ctor_release(x_86, 4);
 lean_ctor_release(x_86, 5);
 lean_ctor_release(x_86, 6);
 x_99 = x_86;
} else {
 lean_dec_ref(x_86);
 x_99 = lean_box(0);
}
lean_inc(x_82);
x_100 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(x_98, x_78, x_82);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 7, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_92);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_101, 2, x_93);
lean_ctor_set(x_101, 3, x_94);
lean_ctor_set(x_101, 4, x_95);
lean_ctor_set(x_101, 5, x_96);
lean_ctor_set(x_101, 6, x_97);
if (lean_is_scalar(x_91)) {
 x_102 = lean_alloc_ctor(0, 4, 0);
} else {
 x_102 = x_91;
}
lean_ctor_set(x_102, 0, x_88);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set(x_102, 2, x_89);
lean_ctor_set(x_102, 3, x_90);
x_103 = lean_st_ref_set(x_5, x_102, x_87);
lean_dec(x_5);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_82);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_78);
lean_dec(x_5);
x_107 = lean_ctor_get(x_81, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_81, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_109 = x_81;
} else {
 lean_dec_ref(x_81);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_78);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_111 = lean_ctor_get(x_80, 0);
lean_inc(x_111);
lean_dec(x_80);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_75);
return x_112;
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
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_77; 
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
x_77 = l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(x_2, x_6);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_28);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_26);
lean_ctor_set(x_78, 1, x_27);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_20 = x_79;
x_21 = x_14;
goto block_25;
}
else
{
uint8_t x_80; 
x_80 = lean_nat_dec_lt(x_6, x_4);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = l_Lean_instInhabitedExpr;
x_82 = l___private_Init_Util_0__outOfBounds___rarg(x_81);
x_29 = x_82;
goto block_76;
}
else
{
lean_object* x_83; 
x_83 = lean_array_fget(x_3, x_6);
x_29 = x_83;
goto block_76;
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
block_76:
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
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_29);
x_34 = lean_infer_type(x_29, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_37 = lean_whnf(x_35, x_10, x_11, x_12, x_13, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Expr_isForall(x_38);
lean_dec(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_33);
lean_dec(x_29);
if (lean_is_scalar(x_28)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_28;
}
lean_ctor_set(x_41, 0, x_26);
lean_ctor_set(x_41, 1, x_27);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_20 = x_42;
x_21 = x_39;
goto block_25;
}
else
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_array_get_size(x_27);
x_44 = lean_nat_dec_lt(x_33, x_43);
lean_dec(x_43);
x_45 = l_Lean_Expr_fvarId_x21(x_29);
x_46 = lean_box(0);
x_47 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_26, x_45, x_46);
if (x_44 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_33);
if (lean_is_scalar(x_28)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_28;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_27);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_20 = x_49;
x_21 = x_39;
goto block_25;
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_array_fget(x_27, x_33);
x_51 = lean_array_fset(x_27, x_33, x_46);
x_52 = !lean_is_exclusive(x_50);
if (x_52 == 0)
{
uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = 1;
lean_ctor_set_uint8(x_50, sizeof(void*)*1 + 4, x_53);
x_54 = lean_array_fset(x_51, x_33, x_50);
lean_dec(x_33);
if (lean_is_scalar(x_28)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_28;
}
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_20 = x_56;
x_21 = x_39;
goto block_25;
}
else
{
uint8_t x_57; uint8_t x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_57 = lean_ctor_get_uint8(x_50, sizeof(void*)*1);
x_58 = lean_ctor_get_uint8(x_50, sizeof(void*)*1 + 1);
x_59 = lean_ctor_get(x_50, 0);
x_60 = lean_ctor_get_uint8(x_50, sizeof(void*)*1 + 2);
x_61 = lean_ctor_get_uint8(x_50, sizeof(void*)*1 + 3);
x_62 = lean_ctor_get_uint8(x_50, sizeof(void*)*1 + 5);
lean_inc(x_59);
lean_dec(x_50);
x_63 = 1;
x_64 = lean_alloc_ctor(0, 1, 6);
lean_ctor_set(x_64, 0, x_59);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_57);
lean_ctor_set_uint8(x_64, sizeof(void*)*1 + 1, x_58);
lean_ctor_set_uint8(x_64, sizeof(void*)*1 + 2, x_60);
lean_ctor_set_uint8(x_64, sizeof(void*)*1 + 3, x_61);
lean_ctor_set_uint8(x_64, sizeof(void*)*1 + 4, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*1 + 5, x_62);
x_65 = lean_array_fset(x_51, x_33, x_64);
lean_dec(x_33);
if (lean_is_scalar(x_28)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_28;
}
lean_ctor_set(x_66, 0, x_47);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_20 = x_67;
x_21 = x_39;
goto block_25;
}
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_33);
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
x_68 = !lean_is_exclusive(x_37);
if (x_68 == 0)
{
return x_37;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_37, 0);
x_70 = lean_ctor_get(x_37, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_37);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_33);
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
x_72 = !lean_is_exclusive(x_34);
if (x_72 == 0)
{
return x_34;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_34, 0);
x_74 = lean_ctor_get(x_34, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_34);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
}
else
{
lean_object* x_84; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_9);
lean_ctor_set(x_84, 1, x_14);
return x_84;
}
}
else
{
lean_object* x_85; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_9);
lean_ctor_set(x_85, 1, x_14);
return x_85;
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
x_1 = lean_mk_string_from_bytes("Decidable", 9);
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
lean_dec(x_2);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_127; 
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
x_127 = lean_nat_dec_lt(x_6, x_4);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = l_Lean_instInhabitedExpr;
x_129 = l___private_Init_Util_0__outOfBounds___rarg(x_128);
x_29 = x_129;
goto block_126;
}
else
{
lean_object* x_130; 
x_130 = lean_array_fget(x_2, x_6);
x_29 = x_130;
goto block_126;
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
block_126:
{
lean_object* x_30; 
lean_inc(x_10);
x_30 = l_Lean_Meta_getFVarLocalDecl(x_29, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_95; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_LocalDecl_type(x_31);
lean_inc(x_33);
lean_inc(x_2);
x_34 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(x_2, x_33);
x_35 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(x_27, x_34);
lean_dec(x_27);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_33);
x_95 = l_Lean_Meta_isProp(x_33, x_10, x_11, x_12, x_13, x_32);
if (lean_obj_tag(x_26) == 0)
{
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; uint8_t x_99; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = 0;
x_99 = lean_unbox(x_96);
lean_dec(x_96);
x_36 = x_98;
x_37 = x_99;
x_38 = x_97;
goto block_94;
}
else
{
uint8_t x_100; 
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
lean_dec(x_2);
x_100 = !lean_is_exclusive(x_95);
if (x_100 == 0)
{
return x_95;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_95, 0);
x_102 = lean_ctor_get(x_95, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_95);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_inc(x_26);
x_104 = lean_alloc_closure((void*)(l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__2___boxed), 2, 1);
lean_closure_set(x_104, 0, x_26);
lean_inc(x_33);
x_105 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_104, x_33);
if (lean_obj_tag(x_105) == 0)
{
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; uint8_t x_109; 
x_106 = lean_ctor_get(x_95, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_95, 1);
lean_inc(x_107);
lean_dec(x_95);
x_108 = 0;
x_109 = lean_unbox(x_106);
lean_dec(x_106);
x_36 = x_108;
x_37 = x_109;
x_38 = x_107;
goto block_94;
}
else
{
uint8_t x_110; 
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
lean_dec(x_2);
x_110 = !lean_is_exclusive(x_95);
if (x_110 == 0)
{
return x_95;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_95, 0);
x_112 = lean_ctor_get(x_95, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_95);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
lean_dec(x_105);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_117; 
x_114 = lean_ctor_get(x_95, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_95, 1);
lean_inc(x_115);
lean_dec(x_95);
x_116 = 1;
x_117 = lean_unbox(x_114);
lean_dec(x_114);
x_36 = x_116;
x_37 = x_117;
x_38 = x_115;
goto block_94;
}
else
{
uint8_t x_118; 
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
lean_dec(x_2);
x_118 = !lean_is_exclusive(x_95);
if (x_118 == 0)
{
return x_95;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_95, 0);
x_120 = lean_ctor_get(x_95, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_95);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
block_94:
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_33);
x_40 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_33, x_39, x_10, x_11, x_12, x_13, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_LocalDecl_binderInfo(x_31);
lean_dec(x_31);
x_44 = 0;
x_45 = lean_alloc_ctor(0, 1, 6);
lean_ctor_set(x_45, 0, x_34);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*1 + 1, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*1 + 2, x_37);
x_46 = lean_unbox(x_41);
lean_dec(x_41);
lean_ctor_set_uint8(x_45, sizeof(void*)*1 + 3, x_46);
lean_ctor_set_uint8(x_45, sizeof(void*)*1 + 4, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*1 + 5, x_36);
x_47 = lean_array_push(x_35, x_45);
x_48 = 3;
x_49 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_43, x_48);
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
x_21 = x_42;
goto block_25;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_33);
x_52 = l_Lean_Meta_isClass_x3f(x_33, x_10, x_11, x_12, x_13, x_42);
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
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
lean_dec(x_52);
x_58 = lean_ctor_get(x_53, 0);
lean_inc(x_58);
lean_dec(x_53);
x_59 = lean_st_ref_get(x_13, x_57);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_getOutParamPositions_x3f(x_62, x_58);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_33);
if (lean_is_scalar(x_28)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_28;
}
lean_ctor_set(x_64, 0, x_26);
lean_ctor_set(x_64, 1, x_47);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_20 = x_65;
x_21 = x_61;
goto block_25;
}
else
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_63, 0);
lean_inc(x_66);
lean_dec(x_63);
x_67 = l_Array_isEmpty___rarg(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_68 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_33, x_16);
x_69 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__2;
lean_inc(x_68);
x_70 = lean_mk_array(x_68, x_69);
x_71 = lean_nat_sub(x_68, x_18);
lean_dec(x_68);
x_72 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_33, x_70, x_71);
x_73 = lean_array_get_size(x_72);
if (lean_is_scalar(x_28)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_28;
}
lean_ctor_set(x_74, 0, x_26);
lean_ctor_set(x_74, 1, x_47);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_73);
x_75 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1(x_2, x_66, x_72, x_73, x_73, x_16, x_73, x_18, x_74, x_10, x_11, x_12, x_13, x_61);
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
lean_object* x_79; 
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_76);
x_20 = x_79;
x_21 = x_77;
goto block_25;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_76, 0);
x_81 = lean_ctor_get(x_76, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_76);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_20 = x_83;
x_21 = x_77;
goto block_25;
}
}
else
{
uint8_t x_84; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_2);
x_84 = !lean_is_exclusive(x_75);
if (x_84 == 0)
{
return x_75;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_75, 0);
x_86 = lean_ctor_get(x_75, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_75);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_66);
lean_dec(x_33);
if (lean_is_scalar(x_28)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_28;
}
lean_ctor_set(x_88, 0, x_26);
lean_ctor_set(x_88, 1, x_47);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_20 = x_89;
x_21 = x_61;
goto block_25;
}
}
}
}
}
else
{
uint8_t x_90; 
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
lean_dec(x_2);
x_90 = !lean_is_exclusive(x_40);
if (x_90 == 0)
{
return x_40;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_40, 0);
x_92 = lean_ctor_get(x_40, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_40);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_2);
x_122 = !lean_is_exclusive(x_30);
if (x_122 == 0)
{
return x_30;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_30, 0);
x_124 = lean_ctor_get(x_30, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_30);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
}
else
{
lean_object* x_131; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_9);
lean_ctor_set(x_131, 1, x_14);
return x_131;
}
}
else
{
lean_object* x_132; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_9);
lean_ctor_set(x_132, 1, x_14);
return x_132;
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_126; 
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
x_126 = lean_nat_dec_lt(x_5, x_3);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = l_Lean_instInhabitedExpr;
x_128 = l___private_Init_Util_0__outOfBounds___rarg(x_127);
x_28 = x_128;
goto block_125;
}
else
{
lean_object* x_129; 
x_129 = lean_array_fget(x_2, x_5);
x_28 = x_129;
goto block_125;
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
block_125:
{
lean_object* x_29; 
lean_inc(x_9);
x_29 = l_Lean_Meta_getFVarLocalDecl(x_28, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_94; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_LocalDecl_type(x_30);
lean_inc(x_32);
lean_inc(x_2);
x_33 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(x_2, x_32);
x_34 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(x_26, x_33);
lean_dec(x_26);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_32);
x_94 = l_Lean_Meta_isProp(x_32, x_9, x_10, x_11, x_12, x_31);
if (lean_obj_tag(x_25) == 0)
{
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_98; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = 0;
x_98 = lean_unbox(x_95);
lean_dec(x_95);
x_35 = x_97;
x_36 = x_98;
x_37 = x_96;
goto block_93;
}
else
{
uint8_t x_99; 
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
lean_dec(x_2);
x_99 = !lean_is_exclusive(x_94);
if (x_99 == 0)
{
return x_94;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_94, 0);
x_101 = lean_ctor_get(x_94, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_94);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; 
lean_inc(x_25);
x_103 = lean_alloc_closure((void*)(l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___lambda__2___boxed), 2, 1);
lean_closure_set(x_103, 0, x_25);
lean_inc(x_32);
x_104 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_103, x_32);
if (lean_obj_tag(x_104) == 0)
{
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_108; 
x_105 = lean_ctor_get(x_94, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_94, 1);
lean_inc(x_106);
lean_dec(x_94);
x_107 = 0;
x_108 = lean_unbox(x_105);
lean_dec(x_105);
x_35 = x_107;
x_36 = x_108;
x_37 = x_106;
goto block_93;
}
else
{
uint8_t x_109; 
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
lean_dec(x_2);
x_109 = !lean_is_exclusive(x_94);
if (x_109 == 0)
{
return x_94;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_94, 0);
x_111 = lean_ctor_get(x_94, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_94);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
lean_dec(x_104);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; uint8_t x_116; 
x_113 = lean_ctor_get(x_94, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_94, 1);
lean_inc(x_114);
lean_dec(x_94);
x_115 = 1;
x_116 = lean_unbox(x_113);
lean_dec(x_113);
x_35 = x_115;
x_36 = x_116;
x_37 = x_114;
goto block_93;
}
else
{
uint8_t x_117; 
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
lean_dec(x_2);
x_117 = !lean_is_exclusive(x_94);
if (x_117 == 0)
{
return x_94;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_94, 0);
x_119 = lean_ctor_get(x_94, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_94);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
}
block_93:
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_32);
x_39 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_32, x_38, x_9, x_10, x_11, x_12, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_LocalDecl_binderInfo(x_30);
lean_dec(x_30);
x_43 = 0;
x_44 = lean_alloc_ctor(0, 1, 6);
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*1 + 1, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*1 + 2, x_36);
x_45 = lean_unbox(x_40);
lean_dec(x_40);
lean_ctor_set_uint8(x_44, sizeof(void*)*1 + 3, x_45);
lean_ctor_set_uint8(x_44, sizeof(void*)*1 + 4, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*1 + 5, x_35);
x_46 = lean_array_push(x_34, x_44);
x_47 = 3;
x_48 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_42, x_47);
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
x_20 = x_41;
goto block_24;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_32);
x_51 = l_Lean_Meta_isClass_x3f(x_32, x_9, x_10, x_11, x_12, x_41);
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
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_dec(x_51);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
lean_dec(x_52);
x_58 = lean_st_ref_get(x_12, x_56);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_getOutParamPositions_x3f(x_61, x_57);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_32);
if (lean_is_scalar(x_27)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_27;
}
lean_ctor_set(x_63, 0, x_25);
lean_ctor_set(x_63, 1, x_46);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_19 = x_64;
x_20 = x_60;
goto block_24;
}
else
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_65);
lean_dec(x_62);
x_66 = l_Array_isEmpty___rarg(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_67 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_32, x_15);
x_68 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___closed__2;
lean_inc(x_67);
x_69 = lean_mk_array(x_67, x_68);
x_70 = lean_nat_sub(x_67, x_17);
lean_dec(x_67);
x_71 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_32, x_69, x_70);
x_72 = lean_array_get_size(x_71);
if (lean_is_scalar(x_27)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_27;
}
lean_ctor_set(x_73, 0, x_25);
lean_ctor_set(x_73, 1, x_46);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_72);
x_74 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__1(x_2, x_65, x_71, x_72, x_72, x_15, x_72, x_17, x_73, x_9, x_10, x_11, x_12, x_60);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_65);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = !lean_is_exclusive(x_75);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_75);
x_19 = x_78;
x_20 = x_76;
goto block_24;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_75, 0);
x_80 = lean_ctor_get(x_75, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_75);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_19 = x_82;
x_20 = x_76;
goto block_24;
}
}
else
{
uint8_t x_83; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_74);
if (x_83 == 0)
{
return x_74;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_74, 0);
x_85 = lean_ctor_get(x_74, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_74);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_65);
lean_dec(x_32);
if (lean_is_scalar(x_27)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_27;
}
lean_ctor_set(x_87, 0, x_25);
lean_ctor_set(x_87, 1, x_46);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_19 = x_88;
x_20 = x_60;
goto block_24;
}
}
}
}
}
else
{
uint8_t x_89; 
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
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_39);
if (x_89 == 0)
{
return x_39;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_39, 0);
x_91 = lean_ctor_get(x_39, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_39);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
x_121 = !lean_is_exclusive(x_29);
if (x_121 == 0)
{
return x_29;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_29, 0);
x_123 = lean_ctor_get(x_29, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_29);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
else
{
lean_object* x_130; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_8);
lean_ctor_set(x_130, 1, x_13);
return x_130;
}
}
else
{
lean_object* x_131; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_8);
lean_ctor_set(x_131, 1, x_13);
return x_131;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__5___rarg), 8, 0);
return x_2;
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
lean_inc(x_2);
x_13 = l_Std_Range_forIn_loop___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__3___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__4(x_1, x_2, x_9, x_9, x_10, x_9, x_11, x_12, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(x_2, x_3);
x_18 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(x_16, x_17);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps(x_2, x_3);
x_24 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_updateHasFwdDeps(x_22, x_23);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_13);
if (x_27 == 0)
{
return x_13;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_13, 0);
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_13);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__1;
x_2 = l_ReaderT_instApplicativeReaderT___rarg(x_1);
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
x_3 = l_instMonadControlT__1___rarg(x_2);
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
lean_inc(x_17);
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
uint8_t x_28; lean_object* x_29; 
x_28 = 1;
lean_ctor_set_uint8(x_26, 9, x_28);
lean_inc(x_4);
x_29 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__5___rarg(x_21, x_2, x_24, x_3, x_4, x_5, x_6, x_22);
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
x_40 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(x_39, x_17, x_30);
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
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_46 = lean_ctor_get(x_34, 0);
x_47 = lean_ctor_get(x_34, 2);
x_48 = lean_ctor_get(x_34, 3);
x_49 = lean_ctor_get(x_34, 4);
x_50 = lean_ctor_get(x_34, 5);
x_51 = lean_ctor_get(x_34, 6);
x_52 = lean_ctor_get(x_34, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_52);
lean_inc(x_46);
lean_dec(x_34);
lean_inc(x_30);
x_53 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(x_52, x_17, x_30);
x_54 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_54, 0, x_46);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_47);
lean_ctor_set(x_54, 3, x_48);
lean_ctor_set(x_54, 4, x_49);
lean_ctor_set(x_54, 5, x_50);
lean_ctor_set(x_54, 6, x_51);
lean_ctor_set(x_33, 1, x_54);
x_55 = lean_st_ref_set(x_4, x_33, x_35);
lean_dec(x_4);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_30);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_59 = lean_ctor_get(x_33, 0);
x_60 = lean_ctor_get(x_33, 2);
x_61 = lean_ctor_get(x_33, 3);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_33);
x_62 = lean_ctor_get(x_34, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_34, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_34, 3);
lean_inc(x_64);
x_65 = lean_ctor_get(x_34, 4);
lean_inc(x_65);
x_66 = lean_ctor_get(x_34, 5);
lean_inc(x_66);
x_67 = lean_ctor_get(x_34, 6);
lean_inc(x_67);
x_68 = lean_ctor_get(x_34, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 lean_ctor_release(x_34, 3);
 lean_ctor_release(x_34, 4);
 lean_ctor_release(x_34, 5);
 lean_ctor_release(x_34, 6);
 x_69 = x_34;
} else {
 lean_dec_ref(x_34);
 x_69 = lean_box(0);
}
lean_inc(x_30);
x_70 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(x_68, x_17, x_30);
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 7, 0);
} else {
 x_71 = x_69;
}
lean_ctor_set(x_71, 0, x_62);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_63);
lean_ctor_set(x_71, 3, x_64);
lean_ctor_set(x_71, 4, x_65);
lean_ctor_set(x_71, 5, x_66);
lean_ctor_set(x_71, 6, x_67);
x_72 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_72, 0, x_59);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_72, 2, x_60);
lean_ctor_set(x_72, 3, x_61);
x_73 = lean_st_ref_set(x_4, x_72, x_35);
lean_dec(x_4);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_75 = x_73;
} else {
 lean_dec_ref(x_73);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_30);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_17);
lean_dec(x_4);
x_77 = !lean_is_exclusive(x_29);
if (x_77 == 0)
{
return x_29;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_29, 0);
x_79 = lean_ctor_get(x_29, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_29);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; 
x_81 = lean_ctor_get_uint8(x_26, 0);
x_82 = lean_ctor_get_uint8(x_26, 1);
x_83 = lean_ctor_get_uint8(x_26, 2);
x_84 = lean_ctor_get_uint8(x_26, 3);
x_85 = lean_ctor_get_uint8(x_26, 4);
x_86 = lean_ctor_get_uint8(x_26, 5);
x_87 = lean_ctor_get_uint8(x_26, 6);
x_88 = lean_ctor_get_uint8(x_26, 7);
x_89 = lean_ctor_get_uint8(x_26, 8);
x_90 = lean_ctor_get_uint8(x_26, 10);
x_91 = lean_ctor_get_uint8(x_26, 11);
lean_dec(x_26);
x_92 = 1;
x_93 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_93, 0, x_81);
lean_ctor_set_uint8(x_93, 1, x_82);
lean_ctor_set_uint8(x_93, 2, x_83);
lean_ctor_set_uint8(x_93, 3, x_84);
lean_ctor_set_uint8(x_93, 4, x_85);
lean_ctor_set_uint8(x_93, 5, x_86);
lean_ctor_set_uint8(x_93, 6, x_87);
lean_ctor_set_uint8(x_93, 7, x_88);
lean_ctor_set_uint8(x_93, 8, x_89);
lean_ctor_set_uint8(x_93, 9, x_92);
lean_ctor_set_uint8(x_93, 10, x_90);
lean_ctor_set_uint8(x_93, 11, x_91);
lean_ctor_set(x_3, 0, x_93);
lean_inc(x_4);
x_94 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__5___rarg(x_21, x_2, x_24, x_3, x_4, x_5, x_6, x_22);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_st_ref_take(x_4, x_96);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = lean_ctor_get(x_98, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_98, 2);
lean_inc(x_102);
x_103 = lean_ctor_get(x_98, 3);
lean_inc(x_103);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 lean_ctor_release(x_98, 2);
 lean_ctor_release(x_98, 3);
 x_104 = x_98;
} else {
 lean_dec_ref(x_98);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get(x_99, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_99, 2);
lean_inc(x_106);
x_107 = lean_ctor_get(x_99, 3);
lean_inc(x_107);
x_108 = lean_ctor_get(x_99, 4);
lean_inc(x_108);
x_109 = lean_ctor_get(x_99, 5);
lean_inc(x_109);
x_110 = lean_ctor_get(x_99, 6);
lean_inc(x_110);
x_111 = lean_ctor_get(x_99, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 lean_ctor_release(x_99, 2);
 lean_ctor_release(x_99, 3);
 lean_ctor_release(x_99, 4);
 lean_ctor_release(x_99, 5);
 lean_ctor_release(x_99, 6);
 x_112 = x_99;
} else {
 lean_dec_ref(x_99);
 x_112 = lean_box(0);
}
lean_inc(x_95);
x_113 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(x_111, x_17, x_95);
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(0, 7, 0);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_105);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set(x_114, 2, x_106);
lean_ctor_set(x_114, 3, x_107);
lean_ctor_set(x_114, 4, x_108);
lean_ctor_set(x_114, 5, x_109);
lean_ctor_set(x_114, 6, x_110);
if (lean_is_scalar(x_104)) {
 x_115 = lean_alloc_ctor(0, 4, 0);
} else {
 x_115 = x_104;
}
lean_ctor_set(x_115, 0, x_101);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_115, 2, x_102);
lean_ctor_set(x_115, 3, x_103);
x_116 = lean_st_ref_set(x_4, x_115, x_100);
lean_dec(x_4);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_95);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_17);
lean_dec(x_4);
x_120 = lean_ctor_get(x_94, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_94, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_122 = x_94;
} else {
 lean_dec_ref(x_94);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; uint8_t x_131; uint8_t x_132; uint8_t x_133; uint8_t x_134; uint8_t x_135; uint8_t x_136; uint8_t x_137; uint8_t x_138; uint8_t x_139; uint8_t x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_124 = lean_ctor_get(x_3, 0);
x_125 = lean_ctor_get(x_3, 1);
x_126 = lean_ctor_get(x_3, 2);
x_127 = lean_ctor_get(x_3, 3);
x_128 = lean_ctor_get(x_3, 4);
x_129 = lean_ctor_get(x_3, 5);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_3);
x_130 = lean_ctor_get_uint8(x_124, 0);
x_131 = lean_ctor_get_uint8(x_124, 1);
x_132 = lean_ctor_get_uint8(x_124, 2);
x_133 = lean_ctor_get_uint8(x_124, 3);
x_134 = lean_ctor_get_uint8(x_124, 4);
x_135 = lean_ctor_get_uint8(x_124, 5);
x_136 = lean_ctor_get_uint8(x_124, 6);
x_137 = lean_ctor_get_uint8(x_124, 7);
x_138 = lean_ctor_get_uint8(x_124, 8);
x_139 = lean_ctor_get_uint8(x_124, 10);
x_140 = lean_ctor_get_uint8(x_124, 11);
if (lean_is_exclusive(x_124)) {
 x_141 = x_124;
} else {
 lean_dec_ref(x_124);
 x_141 = lean_box(0);
}
x_142 = 1;
if (lean_is_scalar(x_141)) {
 x_143 = lean_alloc_ctor(0, 0, 12);
} else {
 x_143 = x_141;
}
lean_ctor_set_uint8(x_143, 0, x_130);
lean_ctor_set_uint8(x_143, 1, x_131);
lean_ctor_set_uint8(x_143, 2, x_132);
lean_ctor_set_uint8(x_143, 3, x_133);
lean_ctor_set_uint8(x_143, 4, x_134);
lean_ctor_set_uint8(x_143, 5, x_135);
lean_ctor_set_uint8(x_143, 6, x_136);
lean_ctor_set_uint8(x_143, 7, x_137);
lean_ctor_set_uint8(x_143, 8, x_138);
lean_ctor_set_uint8(x_143, 9, x_142);
lean_ctor_set_uint8(x_143, 10, x_139);
lean_ctor_set_uint8(x_143, 11, x_140);
x_144 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_125);
lean_ctor_set(x_144, 2, x_126);
lean_ctor_set(x_144, 3, x_127);
lean_ctor_set(x_144, 4, x_128);
lean_ctor_set(x_144, 5, x_129);
lean_inc(x_4);
x_145 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__5___rarg(x_21, x_2, x_24, x_144, x_4, x_5, x_6, x_22);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_st_ref_take(x_4, x_147);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
x_151 = lean_ctor_get(x_148, 1);
lean_inc(x_151);
lean_dec(x_148);
x_152 = lean_ctor_get(x_149, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_149, 2);
lean_inc(x_153);
x_154 = lean_ctor_get(x_149, 3);
lean_inc(x_154);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 lean_ctor_release(x_149, 2);
 lean_ctor_release(x_149, 3);
 x_155 = x_149;
} else {
 lean_dec_ref(x_149);
 x_155 = lean_box(0);
}
x_156 = lean_ctor_get(x_150, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_150, 2);
lean_inc(x_157);
x_158 = lean_ctor_get(x_150, 3);
lean_inc(x_158);
x_159 = lean_ctor_get(x_150, 4);
lean_inc(x_159);
x_160 = lean_ctor_get(x_150, 5);
lean_inc(x_160);
x_161 = lean_ctor_get(x_150, 6);
lean_inc(x_161);
x_162 = lean_ctor_get(x_150, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 lean_ctor_release(x_150, 2);
 lean_ctor_release(x_150, 3);
 lean_ctor_release(x_150, 4);
 lean_ctor_release(x_150, 5);
 lean_ctor_release(x_150, 6);
 x_163 = x_150;
} else {
 lean_dec_ref(x_150);
 x_163 = lean_box(0);
}
lean_inc(x_146);
x_164 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(x_162, x_17, x_146);
if (lean_is_scalar(x_163)) {
 x_165 = lean_alloc_ctor(0, 7, 0);
} else {
 x_165 = x_163;
}
lean_ctor_set(x_165, 0, x_156);
lean_ctor_set(x_165, 1, x_164);
lean_ctor_set(x_165, 2, x_157);
lean_ctor_set(x_165, 3, x_158);
lean_ctor_set(x_165, 4, x_159);
lean_ctor_set(x_165, 5, x_160);
lean_ctor_set(x_165, 6, x_161);
if (lean_is_scalar(x_155)) {
 x_166 = lean_alloc_ctor(0, 4, 0);
} else {
 x_166 = x_155;
}
lean_ctor_set(x_166, 0, x_152);
lean_ctor_set(x_166, 1, x_165);
lean_ctor_set(x_166, 2, x_153);
lean_ctor_set(x_166, 3, x_154);
x_167 = lean_st_ref_set(x_4, x_166, x_151);
lean_dec(x_4);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_169 = x_167;
} else {
 lean_dec_ref(x_167);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_146);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_17);
lean_dec(x_4);
x_171 = lean_ctor_get(x_145, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_145, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_173 = x_145;
} else {
 lean_dec_ref(x_145);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_175 = !lean_is_exclusive(x_20);
if (x_175 == 0)
{
return x_20;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_20, 0);
x_177 = lean_ctor_get(x_20, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_20);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
else
{
lean_object* x_179; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_179 = lean_ctor_get(x_19, 0);
lean_inc(x_179);
lean_dec(x_19);
lean_ctor_set(x_11, 0, x_179);
return x_11;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; 
x_180 = lean_ctor_get(x_11, 0);
x_181 = lean_ctor_get(x_11, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_11);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
lean_dec(x_182);
lean_inc(x_2);
lean_inc(x_1);
x_184 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_184, 0, x_1);
lean_ctor_set(x_184, 1, x_2);
x_185 = lean_unbox(x_9);
lean_dec(x_9);
lean_ctor_set_uint8(x_184, sizeof(void*)*2, x_185);
lean_inc(x_184);
x_186 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__1(x_183, x_184);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_187 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_181);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; uint8_t x_200; uint8_t x_201; uint8_t x_202; uint8_t x_203; uint8_t x_204; uint8_t x_205; uint8_t x_206; uint8_t x_207; uint8_t x_208; uint8_t x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___closed__3;
x_191 = lean_alloc_closure((void*)(l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1___boxed), 8, 1);
lean_closure_set(x_191, 0, x_190);
x_192 = lean_ctor_get(x_3, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_3, 1);
lean_inc(x_193);
x_194 = lean_ctor_get(x_3, 2);
lean_inc(x_194);
x_195 = lean_ctor_get(x_3, 3);
lean_inc(x_195);
x_196 = lean_ctor_get(x_3, 4);
lean_inc(x_196);
x_197 = lean_ctor_get(x_3, 5);
lean_inc(x_197);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 x_198 = x_3;
} else {
 lean_dec_ref(x_3);
 x_198 = lean_box(0);
}
x_199 = lean_ctor_get_uint8(x_192, 0);
x_200 = lean_ctor_get_uint8(x_192, 1);
x_201 = lean_ctor_get_uint8(x_192, 2);
x_202 = lean_ctor_get_uint8(x_192, 3);
x_203 = lean_ctor_get_uint8(x_192, 4);
x_204 = lean_ctor_get_uint8(x_192, 5);
x_205 = lean_ctor_get_uint8(x_192, 6);
x_206 = lean_ctor_get_uint8(x_192, 7);
x_207 = lean_ctor_get_uint8(x_192, 8);
x_208 = lean_ctor_get_uint8(x_192, 10);
x_209 = lean_ctor_get_uint8(x_192, 11);
if (lean_is_exclusive(x_192)) {
 x_210 = x_192;
} else {
 lean_dec_ref(x_192);
 x_210 = lean_box(0);
}
x_211 = 1;
if (lean_is_scalar(x_210)) {
 x_212 = lean_alloc_ctor(0, 0, 12);
} else {
 x_212 = x_210;
}
lean_ctor_set_uint8(x_212, 0, x_199);
lean_ctor_set_uint8(x_212, 1, x_200);
lean_ctor_set_uint8(x_212, 2, x_201);
lean_ctor_set_uint8(x_212, 3, x_202);
lean_ctor_set_uint8(x_212, 4, x_203);
lean_ctor_set_uint8(x_212, 5, x_204);
lean_ctor_set_uint8(x_212, 6, x_205);
lean_ctor_set_uint8(x_212, 7, x_206);
lean_ctor_set_uint8(x_212, 8, x_207);
lean_ctor_set_uint8(x_212, 9, x_211);
lean_ctor_set_uint8(x_212, 10, x_208);
lean_ctor_set_uint8(x_212, 11, x_209);
if (lean_is_scalar(x_198)) {
 x_213 = lean_alloc_ctor(0, 6, 0);
} else {
 x_213 = x_198;
}
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_193);
lean_ctor_set(x_213, 2, x_194);
lean_ctor_set(x_213, 3, x_195);
lean_ctor_set(x_213, 4, x_196);
lean_ctor_set(x_213, 5, x_197);
lean_inc(x_4);
x_214 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__5___rarg(x_188, x_2, x_191, x_213, x_4, x_5, x_6, x_189);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_st_ref_take(x_4, x_216);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
x_220 = lean_ctor_get(x_217, 1);
lean_inc(x_220);
lean_dec(x_217);
x_221 = lean_ctor_get(x_218, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_218, 2);
lean_inc(x_222);
x_223 = lean_ctor_get(x_218, 3);
lean_inc(x_223);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 lean_ctor_release(x_218, 2);
 lean_ctor_release(x_218, 3);
 x_224 = x_218;
} else {
 lean_dec_ref(x_218);
 x_224 = lean_box(0);
}
x_225 = lean_ctor_get(x_219, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_219, 2);
lean_inc(x_226);
x_227 = lean_ctor_get(x_219, 3);
lean_inc(x_227);
x_228 = lean_ctor_get(x_219, 4);
lean_inc(x_228);
x_229 = lean_ctor_get(x_219, 5);
lean_inc(x_229);
x_230 = lean_ctor_get(x_219, 6);
lean_inc(x_230);
x_231 = lean_ctor_get(x_219, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 lean_ctor_release(x_219, 2);
 lean_ctor_release(x_219, 3);
 lean_ctor_release(x_219, 4);
 lean_ctor_release(x_219, 5);
 lean_ctor_release(x_219, 6);
 x_232 = x_219;
} else {
 lean_dec_ref(x_219);
 x_232 = lean_box(0);
}
lean_inc(x_215);
x_233 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4(x_231, x_184, x_215);
if (lean_is_scalar(x_232)) {
 x_234 = lean_alloc_ctor(0, 7, 0);
} else {
 x_234 = x_232;
}
lean_ctor_set(x_234, 0, x_225);
lean_ctor_set(x_234, 1, x_233);
lean_ctor_set(x_234, 2, x_226);
lean_ctor_set(x_234, 3, x_227);
lean_ctor_set(x_234, 4, x_228);
lean_ctor_set(x_234, 5, x_229);
lean_ctor_set(x_234, 6, x_230);
if (lean_is_scalar(x_224)) {
 x_235 = lean_alloc_ctor(0, 4, 0);
} else {
 x_235 = x_224;
}
lean_ctor_set(x_235, 0, x_221);
lean_ctor_set(x_235, 1, x_234);
lean_ctor_set(x_235, 2, x_222);
lean_ctor_set(x_235, 3, x_223);
x_236 = lean_st_ref_set(x_4, x_235, x_220);
lean_dec(x_4);
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_238 = x_236;
} else {
 lean_dec_ref(x_236);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_215);
lean_ctor_set(x_239, 1, x_237);
return x_239;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_184);
lean_dec(x_4);
x_240 = lean_ctor_get(x_214, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_214, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_242 = x_214;
} else {
 lean_dec_ref(x_214);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(1, 2, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_241);
return x_243;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_184);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_244 = lean_ctor_get(x_187, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_187, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_246 = x_187;
} else {
 lean_dec_ref(x_187);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(1, 2, 0);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_244);
lean_ctor_set(x_247, 1, x_245);
return x_247;
}
}
else
{
lean_object* x_248; lean_object* x_249; 
lean_dec(x_184);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_248 = lean_ctor_get(x_186, 0);
lean_inc(x_248);
lean_dec(x_186);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_181);
return x_249;
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
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_FunInfo(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4___closed__1 = _init_l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_FunInfo_0__Lean_Meta_checkFunInfoCache___spec__4___closed__1);
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
