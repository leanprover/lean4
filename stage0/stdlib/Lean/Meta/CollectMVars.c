// Lean compiler output
// Module: Lean.Meta.CollectMVars
// Imports: Lean.Util.CollectMVars Lean.Meta.Basic
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_go___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_getMVarDependencies_go___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_getMVarDependencies_addMVars___spec__7(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVarsAtDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_collectMVarsAtDecl___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_MVarId_getMVarDependencies_addMVars___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_collectMVarsAtDecl___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_collectMVarsAtDecl___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_go___spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_getMVarDependencies_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getMVars___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsAtDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsNoDelayed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__2;
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_getMVarDependencies_go___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__4;
LEAN_EXPORT lean_object* l_Lean_MVarId_getMVarDependencies___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getMVars___closed__5;
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_getMVarDependencies_addMVars___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
static lean_object* l_Lean_Meta_getMVars___closed__4;
uint8_t l_Lean_PersistentHashMap_contains___at_Lean_MVarId_isDelayedAssigned___spec__1(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at_Lean_Meta_collectMVars___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_getMVarDependencies_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_addMVars___spec__6(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_getMVarDependencies_go___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getMVarDependencies_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at_Lean_MVarId_getMVarDependencies_go___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_go___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_getMVarDependencies_go___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getMVarDependencies_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getMVarDependencies_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getMVars___closed__2;
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at_Lean_MVarId_getMVarDependencies_addMVars___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at_Lean_MVarId_getMVarDependencies_go___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at_Lean_MVarId_getMVarDependencies_addMVars___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_Lean_Meta_collectMVarsAtDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_MVarId_getMVarDependencies_addMVars___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_go___spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_collectMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_go___spec__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_Lean_Meta_collectMVarsAtDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1984_(lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___at_Lean_MVarId_isAssigned___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_collectMVars___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at_Lean_Meta_getMVarsNoDelayed___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_MVarId_getMVarDependencies_addMVars___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getMVarDependencies_addMVars(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsAtDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_addMVars___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_CollectMVars_visit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at_Lean_Meta_collectMVars___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at_Lean_Meta_getMVarsNoDelayed___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getMVarDependencies_addMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getMVarDependencies_go___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_collectMVars___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_getMVarsNoDelayed___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_collectMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_collectMVarsAtDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_collectMVarsAtDecl___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getMVarDependencies(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_getMVarDependencies_go___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_collectMVarsAtDecl___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_MVarId_getMVarDependencies_addMVars___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_MVarId_getMVarDependencies_addMVars___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at_Lean_MVarId_getMVarDependencies_go___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__1;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVarsAtDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_go___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__6;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_getMVarsNoDelayed___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_go___spec__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getMVars___closed__1;
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at_Lean_MVarId_getMVarDependencies_go___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_getMVarDependencies_go___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_collectMVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_10 = lean_st_ref_get(x_4, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_instantiateMVarsCore(x_13, x_1);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_take(x_4, x_12);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
lean_ctor_set(x_18, 0, x_16);
x_22 = lean_st_ref_set(x_4, x_18, x_19);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_15);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_18, 1);
x_28 = lean_ctor_get(x_18, 2);
x_29 = lean_ctor_get(x_18, 3);
x_30 = lean_ctor_get(x_18, 4);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_16);
lean_ctor_set(x_31, 1, x_27);
lean_ctor_set(x_31, 2, x_28);
lean_ctor_set(x_31, 3, x_29);
lean_ctor_set(x_31, 4, x_30);
x_32 = lean_st_ref_set(x_4, x_31, x_19);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_15);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at_Lean_Meta_collectMVars___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_4, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(x_11, x_1);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(x_15, x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_collectMVars___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_array_uget(x_13, x_3);
x_15 = l_Lean_getDelayedMVarAssignment_x3f___at_Lean_Meta_collectMVars___spec__2(x_14, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_20 = lean_box(0);
x_3 = x_19;
x_4 = x_20;
x_10 = x_17;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Expr_mvar___override(x_24);
x_26 = l_Lean_Meta_collectMVars(x_25, x_5, x_6, x_7, x_8, x_9, x_22);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = 1;
x_29 = lean_usize_add(x_3, x_28);
x_30 = lean_box(0);
x_3 = x_29;
x_4 = x_30;
x_10 = x_27;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; lean_object* x_24; size_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_8 = l_Lean_instantiateMVars___at_Lean_Meta_collectMVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_2, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = lean_array_get_size(x_14);
lean_dec(x_14);
x_16 = l_Lean_CollectMVars_visit(x_9, x_12);
lean_inc(x_16);
x_17 = lean_st_ref_set(x_2, x_16, x_13);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_array_get_size(x_19);
x_21 = l_Array_toSubarray___rarg(x_19, x_15, x_20);
x_22 = lean_ctor_get(x_21, 2);
lean_inc(x_22);
x_23 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
x_25 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_collectMVars___spec__3(x_21, x_23, x_25, x_26, x_2, x_3, x_4, x_5, x_6, x_18);
lean_dec(x_21);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_collectMVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_instantiateMVars___at_Lean_Meta_collectMVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at_Lean_Meta_collectMVars___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getDelayedMVarAssignment_x3f___at_Lean_Meta_collectMVars___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_collectMVars___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_collectMVars___spec__3(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_collectMVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_getMVars___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_getMVars___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_getMVars___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_getMVars___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_getMVars___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_getMVars___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_getMVars___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_getMVars___closed__3;
x_2 = l_Lean_Meta_getMVars___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = l_Lean_Meta_getMVars___closed__5;
x_8 = lean_st_mk_ref(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_collectMVars(x_1, x_9, x_2, x_3, x_4, x_5, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_9, x_12);
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getMVars(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at_Lean_Meta_getMVarsNoDelayed___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_3, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 8);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_PersistentHashMap_contains___at_Lean_MVarId_isDelayedAssigned___spec__1(x_11, x_1);
x_13 = lean_box(x_12);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_16, 8);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_PersistentHashMap_contains___at_Lean_MVarId_isDelayedAssigned___spec__1(x_17, x_1);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_getMVarsNoDelayed___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = l_Lean_MVarId_isDelayedAssigned___at_Lean_Meta_getMVarsNoDelayed___spec__1(x_11, x_5, x_6, x_7, x_8, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_array_push(x_4, x_11);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_2 = x_18;
x_4 = x_16;
x_9 = x_15;
goto _start;
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; 
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_2 = x_22;
x_9 = x_20;
goto _start;
}
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_9);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Meta_getMVars(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_array_get_size(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_9);
x_14 = l_Lean_Meta_getMVars___closed__4;
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_11, x_11);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_9);
x_16 = l_Lean_Meta_getMVars___closed__4;
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_7);
x_17 = 0;
x_18 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_19 = l_Lean_Meta_getMVars___closed__4;
x_20 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_getMVarsNoDelayed___spec__2(x_9, x_17, x_18, x_19, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_9);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_23 = lean_array_get_size(x_21);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_lt(x_24, x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_21);
x_26 = l_Lean_Meta_getMVars___closed__4;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = lean_nat_dec_le(x_23, x_23);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_23);
lean_dec(x_21);
x_29 = l_Lean_Meta_getMVars___closed__4;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_22);
return x_30;
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; 
x_31 = 0;
x_32 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_33 = l_Lean_Meta_getMVars___closed__4;
x_34 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_getMVarsNoDelayed___spec__2(x_21, x_31, x_32, x_33, x_2, x_3, x_4, x_5, x_22);
lean_dec(x_21);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at_Lean_Meta_getMVarsNoDelayed___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_isDelayedAssigned___at_Lean_Meta_getMVarsNoDelayed___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_getMVarsNoDelayed___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_getMVarsNoDelayed___spec__2(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsNoDelayed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getMVarsNoDelayed(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_collectMVarsAtDecl___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Meta_collectMVars(x_13, x_3, x_4, x_5, x_6, x_7, x_8);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = l_Lean_Meta_collectMVars(x_16, x_3, x_4, x_5, x_6, x_7, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_1 = x_18;
x_2 = x_11;
x_8 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_collectMVarsAtDecl___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_collectMVars(x_12, x_3, x_4, x_5, x_6, x_7, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_1 = x_14;
x_2 = x_11;
x_8 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_collectMVarsAtDecl___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = l_Lean_Meta_collectMVars(x_12, x_3, x_4, x_5, x_6, x_7, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_10, 2);
lean_inc(x_16);
lean_dec(x_10);
x_17 = l_List_foldlM___at_Lean_Meta_collectMVarsAtDecl___spec__3(x_14, x_16, x_3, x_4, x_5, x_6, x_7, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_1 = x_18;
x_2 = x_11;
x_8 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_Lean_Meta_collectMVarsAtDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Meta_collectMVars(x_11, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
case 4:
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
case 5:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_List_foldlM___at_Lean_Meta_collectMVarsAtDecl___spec__2(x_2, x_14, x_3, x_4, x_5, x_6, x_7, x_8);
return x_15;
}
case 6:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_List_foldlM___at_Lean_Meta_collectMVarsAtDecl___spec__4(x_2, x_16, x_3, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
default: 
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 2);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Meta_collectMVars(x_21, x_3, x_4, x_5, x_6, x_7, x_8);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Meta_collectMVars(x_20, x_3, x_4, x_5, x_6, x_7, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVarsAtDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l_Lean_Declaration_foldExprM___at_Lean_Meta_collectMVarsAtDecl___spec__1(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_collectMVarsAtDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_foldlM___at_Lean_Meta_collectMVarsAtDecl___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_collectMVarsAtDecl___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_foldlM___at_Lean_Meta_collectMVarsAtDecl___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_collectMVarsAtDecl___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_foldlM___at_Lean_Meta_collectMVarsAtDecl___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_Lean_Meta_collectMVarsAtDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Declaration_foldExprM___at_Lean_Meta_collectMVarsAtDecl___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectMVarsAtDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_collectMVarsAtDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsAtDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_7 = l_Lean_Meta_getMVars___closed__5;
x_8 = lean_st_mk_ref(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = l_Lean_Declaration_foldExprM___at_Lean_Meta_collectMVarsAtDecl___spec__1(x_1, x_11, x_9, x_2, x_3, x_4, x_5, x_10);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_9, x_13);
lean_dec(x_9);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMVarsAtDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getMVarsAtDecl(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_MVarId_getMVarDependencies_addMVars___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_MVarId_getMVarDependencies_addMVars___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1984_(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1984_(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_MVarId_getMVarDependencies_addMVars___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_MVarId_getMVarDependencies_addMVars___spec__4(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_MVarId_getMVarDependencies_addMVars___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_MVarId_getMVarDependencies_addMVars___spec__3(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at_Lean_MVarId_getMVarDependencies_addMVars___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_4, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 8);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_PersistentHashMap_contains___at_Lean_MVarId_isDelayedAssigned___spec__1(x_12, x_1);
x_14 = lean_box(x_13);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 8);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_PersistentHashMap_contains___at_Lean_MVarId_isDelayedAssigned___spec__1(x_18, x_1);
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_addMVars___spec__6(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_6, x_5);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_array_uget(x_4, x_6);
if (x_1 == 0)
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_97 = l_Lean_MVarId_isDelayedAssigned___at_Lean_MVarId_getMVarDependencies_addMVars___spec__5(x_16, x_8, x_9, x_10, x_11, x_12, x_13);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_unbox(x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = 1;
x_17 = x_101;
x_18 = x_100;
goto block_96;
}
else
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_ctor_get(x_97, 1);
lean_inc(x_102);
lean_dec(x_97);
x_103 = 0;
x_17 = x_103;
x_18 = x_102;
goto block_96;
}
}
else
{
x_17 = x_1;
x_18 = x_13;
goto block_96;
}
block_96:
{
if (x_17 == 0)
{
size_t x_19; size_t x_20; 
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_6, x_19);
x_6 = x_20;
x_13 = x_18;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_7);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; uint8_t x_39; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
x_25 = lean_array_get_size(x_24);
x_26 = l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1984_(x_16);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_24, x_37);
x_39 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_MVarId_getMVarDependencies_addMVars___spec__1(x_16, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_23, x_40);
lean_dec(x_23);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_16);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_38);
x_44 = lean_array_uset(x_24, x_37, x_43);
x_45 = lean_unsigned_to_nat(4u);
x_46 = lean_nat_mul(x_41, x_45);
x_47 = lean_unsigned_to_nat(3u);
x_48 = lean_nat_div(x_46, x_47);
lean_dec(x_46);
x_49 = lean_array_get_size(x_44);
x_50 = lean_nat_dec_le(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; size_t x_52; 
x_51 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_MVarId_getMVarDependencies_addMVars___spec__2(x_44);
lean_ctor_set(x_7, 1, x_51);
lean_ctor_set(x_7, 0, x_41);
x_52 = lean_usize_add(x_6, x_35);
x_6 = x_52;
x_13 = x_18;
goto _start;
}
else
{
size_t x_54; 
lean_ctor_set(x_7, 1, x_44);
lean_ctor_set(x_7, 0, x_41);
x_54 = lean_usize_add(x_6, x_35);
x_6 = x_54;
x_13 = x_18;
goto _start;
}
}
else
{
size_t x_56; 
lean_dec(x_38);
lean_dec(x_16);
x_56 = lean_usize_add(x_6, x_35);
x_6 = x_56;
x_13 = x_18;
goto _start;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; size_t x_68; size_t x_69; size_t x_70; size_t x_71; size_t x_72; lean_object* x_73; uint8_t x_74; 
x_58 = lean_ctor_get(x_7, 0);
x_59 = lean_ctor_get(x_7, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_7);
x_60 = lean_array_get_size(x_59);
x_61 = l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1984_(x_16);
x_62 = 32;
x_63 = lean_uint64_shift_right(x_61, x_62);
x_64 = lean_uint64_xor(x_61, x_63);
x_65 = 16;
x_66 = lean_uint64_shift_right(x_64, x_65);
x_67 = lean_uint64_xor(x_64, x_66);
x_68 = lean_uint64_to_usize(x_67);
x_69 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_70 = 1;
x_71 = lean_usize_sub(x_69, x_70);
x_72 = lean_usize_land(x_68, x_71);
x_73 = lean_array_uget(x_59, x_72);
x_74 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_MVarId_getMVarDependencies_addMVars___spec__1(x_16, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_add(x_58, x_75);
lean_dec(x_58);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_78, 0, x_16);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set(x_78, 2, x_73);
x_79 = lean_array_uset(x_59, x_72, x_78);
x_80 = lean_unsigned_to_nat(4u);
x_81 = lean_nat_mul(x_76, x_80);
x_82 = lean_unsigned_to_nat(3u);
x_83 = lean_nat_div(x_81, x_82);
lean_dec(x_81);
x_84 = lean_array_get_size(x_79);
x_85 = lean_nat_dec_le(x_83, x_84);
lean_dec(x_84);
lean_dec(x_83);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; size_t x_88; 
x_86 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_MVarId_getMVarDependencies_addMVars___spec__2(x_79);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_76);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_usize_add(x_6, x_70);
x_6 = x_88;
x_7 = x_87;
x_13 = x_18;
goto _start;
}
else
{
lean_object* x_90; size_t x_91; 
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_76);
lean_ctor_set(x_90, 1, x_79);
x_91 = lean_usize_add(x_6, x_70);
x_6 = x_91;
x_7 = x_90;
x_13 = x_18;
goto _start;
}
}
else
{
lean_object* x_93; size_t x_94; 
lean_dec(x_73);
lean_dec(x_16);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_58);
lean_ctor_set(x_93, 1, x_59);
x_94 = lean_usize_add(x_6, x_70);
x_6 = x_94;
x_7 = x_93;
x_13 = x_18;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_getMVarDependencies_addMVars___spec__7(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_13 = lean_array_uget(x_2, x_3);
lean_inc(x_9);
x_14 = l_Lean_MVarId_getMVarDependencies_go(x_1, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_5 = x_15;
x_11 = x_16;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_9);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; 
lean_dec(x_9);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getMVarDependencies_addMVars(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_9 = l_Lean_Meta_getMVars(x_2, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_getMVars___closed__3;
x_16 = lean_st_ref_set(x_3, x_15, x_14);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = lean_array_size(x_10);
x_20 = 0;
x_21 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_addMVars___spec__6(x_1, x_10, x_18, x_10, x_19, x_20, x_13, x_3, x_4, x_5, x_6, x_7, x_17);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_st_ref_set(x_3, x_22, x_23);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_24, 1);
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_array_get_size(x_10);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_nat_dec_lt(x_29, x_28);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_6);
x_31 = lean_box(0);
lean_ctor_set(x_24, 0, x_31);
return x_24;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_28, x_28);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_6);
x_33 = lean_box(0);
lean_ctor_set(x_24, 0, x_33);
return x_24;
}
else
{
size_t x_34; lean_object* x_35; lean_object* x_36; 
lean_free_object(x_24);
x_34 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_35 = lean_box(0);
x_36 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_getMVarDependencies_addMVars___spec__7(x_1, x_10, x_20, x_34, x_35, x_3, x_4, x_5, x_6, x_7, x_26);
lean_dec(x_10);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_24, 1);
lean_inc(x_37);
lean_dec(x_24);
x_38 = lean_array_get_size(x_10);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_nat_dec_lt(x_39, x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_38);
lean_dec(x_10);
lean_dec(x_6);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_38, x_38);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_38);
lean_dec(x_10);
lean_dec(x_6);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_37);
return x_45;
}
else
{
size_t x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_47 = lean_box(0);
x_48 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_getMVarDependencies_addMVars___spec__7(x_1, x_10, x_20, x_46, x_47, x_3, x_4, x_5, x_6, x_7, x_37);
lean_dec(x_10);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_go___spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_8, x_7);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_array_uget(x_6, x_8);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_9, 1);
x_21 = lean_ctor_get(x_9, 0);
lean_dec(x_21);
lean_inc(x_13);
lean_inc(x_20);
x_22 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_getMVarDependencies_go___spec__2(x_1, x_2, x_18, x_20, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_13);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_9, 0, x_26);
lean_ctor_set(x_22, 0, x_9);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_9, 0, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_9);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
lean_dec(x_20);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
lean_dec(x_23);
lean_inc(x_5);
lean_ctor_set(x_9, 1, x_31);
lean_ctor_set(x_9, 0, x_5);
x_32 = 1;
x_33 = lean_usize_add(x_8, x_32);
x_8 = x_33;
x_15 = x_30;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_9);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_5);
x_35 = !lean_is_exclusive(x_22);
if (x_35 == 0)
{
return x_22;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_22, 0);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_22);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_9, 1);
lean_inc(x_39);
lean_dec(x_9);
lean_inc(x_13);
lean_inc(x_39);
x_40 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_getMVarDependencies_go___spec__2(x_1, x_2, x_18, x_39, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_18);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_13);
lean_dec(x_5);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_39);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; 
lean_dec(x_39);
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
lean_dec(x_40);
x_48 = lean_ctor_get(x_41, 0);
lean_inc(x_48);
lean_dec(x_41);
lean_inc(x_5);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_5);
lean_ctor_set(x_49, 1, x_48);
x_50 = 1;
x_51 = lean_usize_add(x_8, x_50);
x_8 = x_51;
x_9 = x_49;
x_15 = x_47;
goto _start;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_39);
lean_dec(x_13);
lean_dec(x_5);
x_53 = lean_ctor_get(x_40, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_40, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_55 = x_40;
} else {
 lean_dec_ref(x_40);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_go___spec__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_go___spec__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_7, x_6);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_array_uget(x_5, x_7);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_19 = x_8;
} else {
 lean_dec_ref(x_8);
 x_19 = lean_box(0);
}
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_18);
x_20 = x_28;
x_21 = x_14;
goto block_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_18);
x_29 = lean_ctor_get(x_17, 0);
lean_inc(x_29);
lean_dec(x_17);
x_30 = l_Lean_LocalDecl_type(x_29);
lean_inc(x_12);
x_31 = l_Lean_MVarId_getMVarDependencies_addMVars(x_1, x_30, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_LocalDecl_value_x3f(x_29);
lean_dec(x_29);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_go___spec__4___closed__1;
x_20 = x_34;
x_21 = x_32;
goto block_27;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_12);
x_36 = l_Lean_MVarId_getMVarDependencies_addMVars(x_1, x_35, x_9, x_10, x_11, x_12, x_13, x_32);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_go___spec__4___closed__1;
x_20 = x_38;
x_21 = x_37;
goto block_27;
}
else
{
uint8_t x_39; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_36);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_31);
if (x_43 == 0)
{
return x_31;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_31, 0);
x_45 = lean_ctor_get(x_31, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_31);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
block_27:
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_4);
if (lean_is_scalar(x_19)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_19;
}
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_22);
x_24 = 1;
x_25 = lean_usize_add(x_7, x_24);
x_7 = x_25;
x_8 = x_23;
x_14 = x_21;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_getMVarDependencies_go___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_getMVarDependencies_go___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_box(0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
x_15 = lean_array_size(x_11);
x_16 = 0;
lean_inc(x_8);
x_17 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_go___spec__3(x_1, x_2, x_11, x_12, x_13, x_11, x_15, x_16, x_14, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_box(0);
x_23 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_getMVarDependencies_go___spec__2___lambda__1(x_21, x_22, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_8);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_18);
lean_dec(x_8);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_26);
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_8);
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_3, 0);
x_35 = lean_box(0);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_4);
x_38 = lean_array_size(x_34);
x_39 = 0;
lean_inc(x_8);
x_40 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_go___spec__4(x_1, x_34, x_35, x_36, x_34, x_38, x_39, x_37, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_box(0);
x_46 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_getMVarDependencies_go___spec__2___lambda__1(x_44, x_45, x_5, x_6, x_7, x_8, x_9, x_43);
lean_dec(x_8);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_41);
lean_dec(x_8);
x_47 = !lean_is_exclusive(x_40);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_40, 0);
lean_dec(x_48);
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_49);
return x_40;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
lean_dec(x_40);
x_51 = lean_ctor_get(x_42, 0);
lean_inc(x_51);
lean_dec(x_42);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_8);
x_53 = !lean_is_exclusive(x_40);
if (x_53 == 0)
{
return x_40;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_40, 0);
x_55 = lean_ctor_get(x_40, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_40);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_go___spec__5(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_7, x_6);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_array_uget(x_5, x_7);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_19 = x_8;
} else {
 lean_dec_ref(x_8);
 x_19 = lean_box(0);
}
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_18);
x_20 = x_28;
x_21 = x_14;
goto block_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_18);
x_29 = lean_ctor_get(x_17, 0);
lean_inc(x_29);
lean_dec(x_17);
x_30 = l_Lean_LocalDecl_type(x_29);
lean_inc(x_12);
x_31 = l_Lean_MVarId_getMVarDependencies_addMVars(x_1, x_30, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_LocalDecl_value_x3f(x_29);
lean_dec(x_29);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_go___spec__4___closed__1;
x_20 = x_34;
x_21 = x_32;
goto block_27;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_12);
x_36 = l_Lean_MVarId_getMVarDependencies_addMVars(x_1, x_35, x_9, x_10, x_11, x_12, x_13, x_32);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_go___spec__4___closed__1;
x_20 = x_38;
x_21 = x_37;
goto block_27;
}
else
{
uint8_t x_39; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_36);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_31);
if (x_43 == 0)
{
return x_31;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_31, 0);
x_45 = lean_ctor_get(x_31, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_31);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
block_27:
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_4);
if (lean_is_scalar(x_19)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_19;
}
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_22);
x_24 = 1;
x_25 = lean_usize_add(x_7, x_24);
x_7 = x_25;
x_8 = x_23;
x_14 = x_21;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_getMVarDependencies_go___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_getMVarDependencies_go___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_inc(x_3);
x_11 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_getMVarDependencies_go___spec__2(x_1, x_3, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_7);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_box(0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
x_25 = lean_array_size(x_22);
x_26 = 0;
x_27 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_go___spec__5(x_1, x_21, x_22, x_23, x_22, x_25, x_26, x_24, x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_27, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
lean_ctor_set(x_27, 0, x_32);
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_28);
x_36 = !lean_is_exclusive(x_27);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_27, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_38);
return x_27;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_27, 1);
lean_inc(x_39);
lean_dec(x_27);
x_40 = lean_ctor_get(x_29, 0);
lean_inc(x_40);
lean_dec(x_29);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_27);
if (x_42 == 0)
{
return x_27;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_27, 0);
x_44 = lean_ctor_get(x_27, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_27);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_7);
x_46 = !lean_is_exclusive(x_11);
if (x_46 == 0)
{
return x_11;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_11, 0);
x_48 = lean_ctor_get(x_11, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_11);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at_Lean_MVarId_getMVarDependencies_go___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_4, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(x_11, x_1);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(x_15, x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at_Lean_MVarId_getMVarDependencies_go___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_4, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 7);
lean_inc(x_12);
x_13 = l_Lean_PersistentHashMap_contains___at_Lean_MVarId_isAssigned___spec__1(x_12, x_1);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 8);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_PersistentHashMap_contains___at_Lean_MVarId_isDelayedAssigned___spec__1(x_14, x_1);
x_16 = lean_box(x_15);
lean_ctor_set(x_8, 0, x_16);
return x_8;
}
else
{
uint8_t x_17; lean_object* x_18; 
lean_dec(x_11);
x_17 = 1;
x_18 = lean_box(x_17);
lean_ctor_set(x_8, 0, x_18);
return x_8;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_21, 7);
lean_inc(x_22);
x_23 = l_Lean_PersistentHashMap_contains___at_Lean_MVarId_isAssigned___spec__1(x_22, x_1);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_21, 8);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_Lean_PersistentHashMap_contains___at_Lean_MVarId_isDelayedAssigned___spec__1(x_24, x_1);
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_20);
return x_27;
}
else
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_21);
x_28 = 1;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_20);
return x_30;
}
}
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("runtime", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__1;
x_2 = l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__3;
x_2 = l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__5;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__6;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getMVarDependencies_go___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_getMVarDependencies_go(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getMVarDependencies_go(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 4);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 5);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 6);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 7);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 8);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 9);
lean_inc(x_18);
x_19 = lean_ctor_get(x_6, 10);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_6, sizeof(void*)*12);
x_21 = lean_ctor_get(x_6, 11);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_6, sizeof(void*)*12 + 1);
x_23 = lean_nat_dec_eq(x_12, x_13);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_6);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_25 = lean_ctor_get(x_6, 11);
lean_dec(x_25);
x_26 = lean_ctor_get(x_6, 10);
lean_dec(x_26);
x_27 = lean_ctor_get(x_6, 9);
lean_dec(x_27);
x_28 = lean_ctor_get(x_6, 8);
lean_dec(x_28);
x_29 = lean_ctor_get(x_6, 7);
lean_dec(x_29);
x_30 = lean_ctor_get(x_6, 6);
lean_dec(x_30);
x_31 = lean_ctor_get(x_6, 5);
lean_dec(x_31);
x_32 = lean_ctor_get(x_6, 4);
lean_dec(x_32);
x_33 = lean_ctor_get(x_6, 3);
lean_dec(x_33);
x_34 = lean_ctor_get(x_6, 2);
lean_dec(x_34);
x_35 = lean_ctor_get(x_6, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_6, 0);
lean_dec(x_36);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_12, x_37);
lean_dec(x_12);
lean_ctor_set(x_6, 3, x_38);
lean_inc(x_2);
x_39 = l_Lean_MVarId_getDecl(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 2);
lean_inc(x_42);
lean_inc(x_6);
x_43 = l_Lean_MVarId_getMVarDependencies_addMVars(x_1, x_42, x_3, x_4, x_5, x_6, x_7, x_41);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_dec(x_40);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_box(0);
lean_inc(x_6);
x_48 = l_Lean_PersistentArray_forIn___at_Lean_MVarId_getMVarDependencies_go___spec__1(x_1, x_46, x_47, x_3, x_4, x_5, x_6, x_7, x_44);
lean_dec(x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lean_getDelayedMVarAssignment_x3f___at_Lean_MVarId_getMVarDependencies_go___spec__6(x_2, x_3, x_4, x_5, x_6, x_7, x_49);
lean_dec(x_2);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
lean_dec(x_6);
x_52 = !lean_is_exclusive(x_50);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_50, 0);
lean_dec(x_53);
lean_ctor_set(x_50, 0, x_47);
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_dec(x_50);
x_57 = lean_ctor_get(x_51, 0);
lean_inc(x_57);
lean_dec(x_51);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_142 = l_Lean_MVarId_isAssignedOrDelayedAssigned___at_Lean_MVarId_getMVarDependencies_go___spec__7(x_58, x_3, x_4, x_5, x_6, x_7, x_56);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_unbox(x_143);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; uint8_t x_146; 
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
x_146 = 1;
x_59 = x_146;
x_60 = x_145;
goto block_141;
}
else
{
lean_object* x_147; uint8_t x_148; 
x_147 = lean_ctor_get(x_142, 1);
lean_inc(x_147);
lean_dec(x_142);
x_148 = 0;
x_59 = x_148;
x_60 = x_147;
goto block_141;
}
block_141:
{
if (x_59 == 0)
{
x_2 = x_58;
x_8 = x_60;
goto _start;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = lean_st_ref_take(x_3, x_60);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint64_t x_69; uint64_t x_70; uint64_t x_71; uint64_t x_72; uint64_t x_73; uint64_t x_74; uint64_t x_75; size_t x_76; size_t x_77; size_t x_78; size_t x_79; size_t x_80; lean_object* x_81; uint8_t x_82; 
x_66 = lean_ctor_get(x_63, 0);
x_67 = lean_ctor_get(x_63, 1);
x_68 = lean_array_get_size(x_67);
x_69 = l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1984_(x_58);
x_70 = 32;
x_71 = lean_uint64_shift_right(x_69, x_70);
x_72 = lean_uint64_xor(x_69, x_71);
x_73 = 16;
x_74 = lean_uint64_shift_right(x_72, x_73);
x_75 = lean_uint64_xor(x_72, x_74);
x_76 = lean_uint64_to_usize(x_75);
x_77 = lean_usize_of_nat(x_68);
lean_dec(x_68);
x_78 = 1;
x_79 = lean_usize_sub(x_77, x_78);
x_80 = lean_usize_land(x_76, x_79);
x_81 = lean_array_uget(x_67, x_80);
x_82 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_MVarId_getMVarDependencies_addMVars___spec__1(x_58, x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_83 = lean_nat_add(x_66, x_37);
lean_dec(x_66);
lean_inc(x_58);
x_84 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_84, 0, x_58);
lean_ctor_set(x_84, 1, x_47);
lean_ctor_set(x_84, 2, x_81);
x_85 = lean_array_uset(x_67, x_80, x_84);
x_86 = lean_unsigned_to_nat(4u);
x_87 = lean_nat_mul(x_83, x_86);
x_88 = lean_unsigned_to_nat(3u);
x_89 = lean_nat_div(x_87, x_88);
lean_dec(x_87);
x_90 = lean_array_get_size(x_85);
x_91 = lean_nat_dec_le(x_89, x_90);
lean_dec(x_90);
lean_dec(x_89);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_MVarId_getMVarDependencies_addMVars___spec__2(x_85);
lean_ctor_set(x_63, 1, x_92);
lean_ctor_set(x_63, 0, x_83);
x_93 = lean_st_ref_set(x_3, x_63, x_64);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_2 = x_58;
x_8 = x_94;
goto _start;
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_ctor_set(x_63, 1, x_85);
lean_ctor_set(x_63, 0, x_83);
x_96 = lean_st_ref_set(x_3, x_63, x_64);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_2 = x_58;
x_8 = x_97;
goto _start;
}
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_81);
x_99 = lean_st_ref_set(x_3, x_63, x_64);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_2 = x_58;
x_8 = x_100;
goto _start;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint64_t x_105; uint64_t x_106; uint64_t x_107; uint64_t x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; size_t x_112; size_t x_113; size_t x_114; size_t x_115; size_t x_116; lean_object* x_117; uint8_t x_118; 
x_102 = lean_ctor_get(x_63, 0);
x_103 = lean_ctor_get(x_63, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_63);
x_104 = lean_array_get_size(x_103);
x_105 = l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1984_(x_58);
x_106 = 32;
x_107 = lean_uint64_shift_right(x_105, x_106);
x_108 = lean_uint64_xor(x_105, x_107);
x_109 = 16;
x_110 = lean_uint64_shift_right(x_108, x_109);
x_111 = lean_uint64_xor(x_108, x_110);
x_112 = lean_uint64_to_usize(x_111);
x_113 = lean_usize_of_nat(x_104);
lean_dec(x_104);
x_114 = 1;
x_115 = lean_usize_sub(x_113, x_114);
x_116 = lean_usize_land(x_112, x_115);
x_117 = lean_array_uget(x_103, x_116);
x_118 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_MVarId_getMVarDependencies_addMVars___spec__1(x_58, x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_119 = lean_nat_add(x_102, x_37);
lean_dec(x_102);
lean_inc(x_58);
x_120 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_120, 0, x_58);
lean_ctor_set(x_120, 1, x_47);
lean_ctor_set(x_120, 2, x_117);
x_121 = lean_array_uset(x_103, x_116, x_120);
x_122 = lean_unsigned_to_nat(4u);
x_123 = lean_nat_mul(x_119, x_122);
x_124 = lean_unsigned_to_nat(3u);
x_125 = lean_nat_div(x_123, x_124);
lean_dec(x_123);
x_126 = lean_array_get_size(x_121);
x_127 = lean_nat_dec_le(x_125, x_126);
lean_dec(x_126);
lean_dec(x_125);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_MVarId_getMVarDependencies_addMVars___spec__2(x_121);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_119);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_st_ref_set(x_3, x_129, x_64);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_2 = x_58;
x_8 = x_131;
goto _start;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_119);
lean_ctor_set(x_133, 1, x_121);
x_134 = lean_st_ref_set(x_3, x_133, x_64);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec(x_134);
x_2 = x_58;
x_8 = x_135;
goto _start;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_117);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_102);
lean_ctor_set(x_137, 1, x_103);
x_138 = lean_st_ref_set(x_3, x_137, x_64);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
x_2 = x_58;
x_8 = x_139;
goto _start;
}
}
}
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_6);
lean_dec(x_2);
x_149 = !lean_is_exclusive(x_48);
if (x_149 == 0)
{
return x_48;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_48, 0);
x_151 = lean_ctor_get(x_48, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_48);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
else
{
uint8_t x_153; 
lean_dec(x_40);
lean_dec(x_6);
lean_dec(x_2);
x_153 = !lean_is_exclusive(x_43);
if (x_153 == 0)
{
return x_43;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_43, 0);
x_155 = lean_ctor_get(x_43, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_43);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_6);
lean_dec(x_2);
x_157 = !lean_is_exclusive(x_39);
if (x_157 == 0)
{
return x_39;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_39, 0);
x_159 = lean_ctor_get(x_39, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_39);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_6);
x_161 = lean_unsigned_to_nat(1u);
x_162 = lean_nat_add(x_12, x_161);
lean_dec(x_12);
x_163 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_163, 0, x_9);
lean_ctor_set(x_163, 1, x_10);
lean_ctor_set(x_163, 2, x_11);
lean_ctor_set(x_163, 3, x_162);
lean_ctor_set(x_163, 4, x_13);
lean_ctor_set(x_163, 5, x_14);
lean_ctor_set(x_163, 6, x_15);
lean_ctor_set(x_163, 7, x_16);
lean_ctor_set(x_163, 8, x_17);
lean_ctor_set(x_163, 9, x_18);
lean_ctor_set(x_163, 10, x_19);
lean_ctor_set(x_163, 11, x_21);
lean_ctor_set_uint8(x_163, sizeof(void*)*12, x_20);
lean_ctor_set_uint8(x_163, sizeof(void*)*12 + 1, x_22);
lean_inc(x_2);
x_164 = l_Lean_MVarId_getDecl(x_2, x_4, x_5, x_163, x_7, x_8);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = lean_ctor_get(x_165, 2);
lean_inc(x_167);
lean_inc(x_163);
x_168 = l_Lean_MVarId_getMVarDependencies_addMVars(x_1, x_167, x_3, x_4, x_5, x_163, x_7, x_166);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
lean_dec(x_168);
x_170 = lean_ctor_get(x_165, 1);
lean_inc(x_170);
lean_dec(x_165);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec(x_170);
x_172 = lean_box(0);
lean_inc(x_163);
x_173 = l_Lean_PersistentArray_forIn___at_Lean_MVarId_getMVarDependencies_go___spec__1(x_1, x_171, x_172, x_3, x_4, x_5, x_163, x_7, x_169);
lean_dec(x_171);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
lean_dec(x_173);
x_175 = l_Lean_getDelayedMVarAssignment_x3f___at_Lean_MVarId_getMVarDependencies_go___spec__6(x_2, x_3, x_4, x_5, x_163, x_7, x_174);
lean_dec(x_2);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_163);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_178 = x_175;
} else {
 lean_dec_ref(x_175);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_172);
lean_ctor_set(x_179, 1, x_177);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; lean_object* x_184; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_180 = lean_ctor_get(x_175, 1);
lean_inc(x_180);
lean_dec(x_175);
x_181 = lean_ctor_get(x_176, 0);
lean_inc(x_181);
lean_dec(x_176);
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
lean_dec(x_181);
x_230 = l_Lean_MVarId_isAssignedOrDelayedAssigned___at_Lean_MVarId_getMVarDependencies_go___spec__7(x_182, x_3, x_4, x_5, x_163, x_7, x_180);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_unbox(x_231);
lean_dec(x_231);
if (x_232 == 0)
{
lean_object* x_233; uint8_t x_234; 
x_233 = lean_ctor_get(x_230, 1);
lean_inc(x_233);
lean_dec(x_230);
x_234 = 1;
x_183 = x_234;
x_184 = x_233;
goto block_229;
}
else
{
lean_object* x_235; uint8_t x_236; 
x_235 = lean_ctor_get(x_230, 1);
lean_inc(x_235);
lean_dec(x_230);
x_236 = 0;
x_183 = x_236;
x_184 = x_235;
goto block_229;
}
block_229:
{
if (x_183 == 0)
{
x_2 = x_182;
x_6 = x_163;
x_8 = x_184;
goto _start;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint64_t x_193; uint64_t x_194; uint64_t x_195; uint64_t x_196; uint64_t x_197; uint64_t x_198; uint64_t x_199; size_t x_200; size_t x_201; size_t x_202; size_t x_203; size_t x_204; lean_object* x_205; uint8_t x_206; 
x_186 = lean_st_ref_take(x_3, x_184);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = lean_ctor_get(x_187, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_191 = x_187;
} else {
 lean_dec_ref(x_187);
 x_191 = lean_box(0);
}
x_192 = lean_array_get_size(x_190);
x_193 = l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1984_(x_182);
x_194 = 32;
x_195 = lean_uint64_shift_right(x_193, x_194);
x_196 = lean_uint64_xor(x_193, x_195);
x_197 = 16;
x_198 = lean_uint64_shift_right(x_196, x_197);
x_199 = lean_uint64_xor(x_196, x_198);
x_200 = lean_uint64_to_usize(x_199);
x_201 = lean_usize_of_nat(x_192);
lean_dec(x_192);
x_202 = 1;
x_203 = lean_usize_sub(x_201, x_202);
x_204 = lean_usize_land(x_200, x_203);
x_205 = lean_array_uget(x_190, x_204);
x_206 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_MVarId_getMVarDependencies_addMVars___spec__1(x_182, x_205);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; 
x_207 = lean_nat_add(x_189, x_161);
lean_dec(x_189);
lean_inc(x_182);
x_208 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_208, 0, x_182);
lean_ctor_set(x_208, 1, x_172);
lean_ctor_set(x_208, 2, x_205);
x_209 = lean_array_uset(x_190, x_204, x_208);
x_210 = lean_unsigned_to_nat(4u);
x_211 = lean_nat_mul(x_207, x_210);
x_212 = lean_unsigned_to_nat(3u);
x_213 = lean_nat_div(x_211, x_212);
lean_dec(x_211);
x_214 = lean_array_get_size(x_209);
x_215 = lean_nat_dec_le(x_213, x_214);
lean_dec(x_214);
lean_dec(x_213);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_216 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_MVarId_getMVarDependencies_addMVars___spec__2(x_209);
if (lean_is_scalar(x_191)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_191;
}
lean_ctor_set(x_217, 0, x_207);
lean_ctor_set(x_217, 1, x_216);
x_218 = lean_st_ref_set(x_3, x_217, x_188);
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
lean_dec(x_218);
x_2 = x_182;
x_6 = x_163;
x_8 = x_219;
goto _start;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
if (lean_is_scalar(x_191)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_191;
}
lean_ctor_set(x_221, 0, x_207);
lean_ctor_set(x_221, 1, x_209);
x_222 = lean_st_ref_set(x_3, x_221, x_188);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_dec(x_222);
x_2 = x_182;
x_6 = x_163;
x_8 = x_223;
goto _start;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_205);
if (lean_is_scalar(x_191)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_191;
}
lean_ctor_set(x_225, 0, x_189);
lean_ctor_set(x_225, 1, x_190);
x_226 = lean_st_ref_set(x_3, x_225, x_188);
x_227 = lean_ctor_get(x_226, 1);
lean_inc(x_227);
lean_dec(x_226);
x_2 = x_182;
x_6 = x_163;
x_8 = x_227;
goto _start;
}
}
}
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_163);
lean_dec(x_2);
x_237 = lean_ctor_get(x_173, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_173, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_239 = x_173;
} else {
 lean_dec_ref(x_173);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_237);
lean_ctor_set(x_240, 1, x_238);
return x_240;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_165);
lean_dec(x_163);
lean_dec(x_2);
x_241 = lean_ctor_get(x_168, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_168, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_243 = x_168;
} else {
 lean_dec_ref(x_168);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(1, 2, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_242);
return x_244;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_163);
lean_dec(x_2);
x_245 = lean_ctor_get(x_164, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_164, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_247 = x_164;
} else {
 lean_dec_ref(x_164);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
}
}
else
{
lean_object* x_249; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_249 = l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8(x_14, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
return x_249;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_MVarId_getMVarDependencies_addMVars___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_MVarId_getMVarDependencies_addMVars___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at_Lean_MVarId_getMVarDependencies_addMVars___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_isDelayedAssigned___at_Lean_MVarId_getMVarDependencies_addMVars___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_addMVars___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_addMVars___spec__6(x_14, x_2, x_3, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_getMVarDependencies_addMVars___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_getMVarDependencies_addMVars___spec__7(x_12, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getMVarDependencies_addMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_MVarId_getMVarDependencies_addMVars(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_go___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_1);
lean_dec(x_1);
x_17 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_18 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_19 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_go___spec__3(x_16, x_2, x_3, x_4, x_5, x_6, x_17, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_go___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_1);
lean_dec(x_1);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_18 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_go___spec__4(x_15, x_2, x_3, x_4, x_5, x_16, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_getMVarDependencies_go___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_getMVarDependencies_go___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_getMVarDependencies_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_getMVarDependencies_go___spec__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_go___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_1);
lean_dec(x_1);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_18 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_go___spec__5(x_15, x_2, x_3, x_4, x_5, x_16, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_getMVarDependencies_go___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PersistentArray_forIn___at_Lean_MVarId_getMVarDependencies_go___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_getMVarDependencies_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_PersistentArray_forIn___at_Lean_MVarId_getMVarDependencies_go___spec__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at_Lean_MVarId_getMVarDependencies_go___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getDelayedMVarAssignment_x3f___at_Lean_MVarId_getMVarDependencies_go___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignedOrDelayedAssigned___at_Lean_MVarId_getMVarDependencies_go___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_isAssignedOrDelayedAssigned___at_Lean_MVarId_getMVarDependencies_go___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getMVarDependencies_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_MVarId_getMVarDependencies_go___lambda__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getMVarDependencies_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_MVarId_getMVarDependencies_go(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getMVarDependencies(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_Meta_getMVars___closed__3;
x_9 = lean_st_mk_ref(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_MVarId_getMVarDependencies_go(x_2, x_1, x_10, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_10, x_13);
lean_dec(x_10);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_10);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getMVarDependencies___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_MVarId_getMVarDependencies(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* initialize_Lean_Util_CollectMVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_CollectMVars(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_CollectMVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_getMVars___closed__1 = _init_l_Lean_Meta_getMVars___closed__1();
lean_mark_persistent(l_Lean_Meta_getMVars___closed__1);
l_Lean_Meta_getMVars___closed__2 = _init_l_Lean_Meta_getMVars___closed__2();
lean_mark_persistent(l_Lean_Meta_getMVars___closed__2);
l_Lean_Meta_getMVars___closed__3 = _init_l_Lean_Meta_getMVars___closed__3();
lean_mark_persistent(l_Lean_Meta_getMVars___closed__3);
l_Lean_Meta_getMVars___closed__4 = _init_l_Lean_Meta_getMVars___closed__4();
lean_mark_persistent(l_Lean_Meta_getMVars___closed__4);
l_Lean_Meta_getMVars___closed__5 = _init_l_Lean_Meta_getMVars___closed__5();
lean_mark_persistent(l_Lean_Meta_getMVars___closed__5);
l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_go___spec__4___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_go___spec__4___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_getMVarDependencies_go___spec__4___closed__1);
l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__1);
l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__2);
l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__3 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__3();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__3);
l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__4 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__4();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__4);
l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__5 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__5();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__5);
l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__6 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__6();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_MVarId_getMVarDependencies_go___spec__8___closed__6);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
