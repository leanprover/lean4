// Lean compiler output
// Module: Lean.Meta.GeneralizeVars
// Imports: Lean.Meta.Basic Lean.Util.CollectFVars
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
static lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_getFVarSetToGeneralize_spec__7(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_getFVarSetToGeneralize_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__6;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
static lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__5;
lean_object* l_Lean_CollectFVars_main(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Meta_sortFVarIds___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___Lean_Meta_getFVarsToGeneralize_spec__0(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__0(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__1(uint8_t, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 4);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1___redArg(x_1, x_5, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_ctor_get(x_7, 0);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
x_16 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_4, x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_inc(x_4);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_15);
lean_ctor_set(x_7, 0, x_4);
x_17 = l_Lean_FVarIdSet_insert(x_14, x_4);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 0, x_17);
x_1 = x_9;
x_2 = x_6;
x_3 = x_11;
goto _start;
}
else
{
lean_free_object(x_7);
lean_dec(x_4);
x_1 = x_9;
x_2 = x_6;
x_3 = x_11;
goto _start;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_4, x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_inc(x_4);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_21);
lean_ctor_set(x_7, 0, x_4);
x_23 = l_Lean_FVarIdSet_insert(x_20, x_4);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_7);
x_1 = x_24;
x_2 = x_6;
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_26; 
lean_free_object(x_7);
lean_dec(x_4);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_21);
x_1 = x_26;
x_2 = x_6;
x_3 = x_11;
goto _start;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_dec(x_7);
x_29 = lean_ctor_get(x_9, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_31 = x_9;
} else {
 lean_dec_ref(x_9);
 x_31 = lean_box(0);
}
x_32 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_4, x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_inc(x_4);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_30);
x_34 = l_Lean_FVarIdSet_insert(x_29, x_4);
if (lean_is_scalar(x_31)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_31;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_1 = x_35;
x_2 = x_6;
x_3 = x_28;
goto _start;
}
else
{
lean_object* x_37; 
lean_dec(x_4);
if (lean_is_scalar(x_31)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_31;
}
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_30);
x_1 = x_37;
x_2 = x_6;
x_3 = x_28;
goto _start;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_1);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_3);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1___redArg(x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 4);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1___redArg(x_1, x_9, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
x_20 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_8, x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_inc(x_8);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_19);
lean_ctor_set(x_11, 0, x_8);
x_21 = l_Lean_FVarIdSet_insert(x_18, x_8);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 0, x_21);
x_22 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1___redArg(x_13, x_10, x_15);
return x_22;
}
else
{
lean_object* x_23; 
lean_free_object(x_11);
lean_dec(x_8);
x_23 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1___redArg(x_13, x_10, x_15);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_8, x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc(x_8);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_25);
lean_ctor_set(x_11, 0, x_8);
x_27 = l_Lean_FVarIdSet_insert(x_24, x_8);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_11);
x_29 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1___redArg(x_28, x_10, x_15);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_free_object(x_11);
lean_dec(x_8);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
x_31 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1___redArg(x_30, x_10, x_15);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_11, 1);
lean_inc(x_32);
lean_dec(x_11);
x_33 = lean_ctor_get(x_13, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_35 = x_13;
} else {
 lean_dec_ref(x_13);
 x_35 = lean_box(0);
}
x_36 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_8, x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_inc(x_8);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_8);
lean_ctor_set(x_37, 1, x_34);
x_38 = l_Lean_FVarIdSet_insert(x_33, x_8);
if (lean_is_scalar(x_35)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_35;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1___redArg(x_39, x_10, x_32);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_8);
if (lean_is_scalar(x_35)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_35;
}
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_41, 1, x_34);
x_42 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1___redArg(x_41, x_10, x_32);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_7);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3___redArg(x_1, x_3, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__5;
x_2 = lean_box(1);
x_3 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_33; 
lean_inc_ref(x_4);
x_33 = l_Lean_FVarId_getDecl___redArg(x_1, x_4, x_6, x_7, x_8);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_50; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_50 = lean_ctor_get(x_34, 3);
lean_inc_ref(x_50);
x_36 = x_50;
goto block_49;
block_49:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_37 = l_Lean_instantiateMVars___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3___redArg(x_36, x_5, x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec_ref(x_37);
x_40 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__6;
x_41 = l_Lean_CollectFVars_main(x_38, x_40);
x_42 = 0;
x_43 = l_Lean_LocalDecl_value_x3f(x_34, x_42);
lean_dec(x_34);
if (lean_obj_tag(x_43) == 0)
{
x_20 = x_41;
x_21 = x_4;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = x_39;
goto block_32;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = l_Lean_instantiateMVars___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3___redArg(x_44, x_5, x_39);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec_ref(x_45);
x_48 = l_Lean_CollectFVars_main(x_46, x_41);
x_20 = x_48;
x_21 = x_4;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = x_47;
goto block_32;
}
}
}
else
{
uint8_t x_51; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_33);
if (x_51 == 0)
{
return x_33;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_33, 0);
x_53 = lean_ctor_get(x_33, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_33);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
block_19:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
lean_ctor_set(x_9, 1, x_12);
lean_ctor_set(x_9, 0, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
}
block_32:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec_ref(x_20);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_2);
x_28 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1(x_27, x_26, x_21, x_22, x_23, x_24, x_25);
lean_dec_ref(x_21);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_9 = x_31;
x_10 = x_30;
goto block_19;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; 
lean_dec_ref(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_9, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_9);
x_12 = l_Lean_FVarIdSet_insert(x_2, x_9);
lean_inc_ref(x_3);
x_13 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit(x_9, x_10, x_12, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_1 = x_16;
x_2 = x_17;
x_7 = x_15;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec_ref(x_3);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_dec(x_9);
x_1 = x_10;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkGeneralizationForbiddenSet_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_3, x_2);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_4, 1);
x_21 = lean_array_uget(x_1, x_3);
x_22 = l_Lean_Expr_isFVar(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_23 = lean_infer_type(x_21, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = l_Lean_instantiateMVars___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3___redArg(x_24, x_6, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = l_Lean_CollectFVars_main(x_27, x_19);
lean_ctor_set(x_4, 0, x_29);
x_10 = x_4;
x_11 = x_28;
goto block_15;
}
else
{
uint8_t x_30; 
lean_free_object(x_4);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_23);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Lean_Expr_fvarId_x21(x_21);
lean_dec_ref(x_21);
x_35 = lean_array_push(x_20, x_34);
lean_ctor_set(x_4, 1, x_35);
x_10 = x_4;
x_11 = x_9;
goto block_15;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_4, 0);
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_4);
x_38 = lean_array_uget(x_1, x_3);
x_39 = l_Lean_Expr_isFVar(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_40 = lean_infer_type(x_38, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
x_43 = l_Lean_instantiateMVars___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3___redArg(x_41, x_6, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = l_Lean_CollectFVars_main(x_44, x_36);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_37);
x_10 = x_47;
x_11 = x_45;
goto block_15;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_48 = lean_ctor_get(x_40, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_40, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_50 = x_40;
} else {
 lean_dec_ref(x_40);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = l_Lean_Expr_fvarId_x21(x_38);
lean_dec_ref(x_38);
x_53 = lean_array_push(x_37, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_36);
lean_ctor_set(x_54, 1, x_53);
x_10 = x_54;
x_11 = x_9;
goto block_15;
}
}
}
block_15:
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
x_4 = x_10;
x_9 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_3, x_2);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_4, 1);
x_21 = lean_array_uget(x_1, x_3);
x_22 = l_Lean_Expr_isFVar(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_23 = lean_infer_type(x_21, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = l_Lean_instantiateMVars___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3___redArg(x_24, x_6, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = l_Lean_CollectFVars_main(x_27, x_19);
lean_ctor_set(x_4, 0, x_29);
x_10 = x_4;
x_11 = x_28;
goto block_15;
}
else
{
uint8_t x_30; 
lean_free_object(x_4);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_23);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Lean_Expr_fvarId_x21(x_21);
lean_dec_ref(x_21);
x_35 = lean_array_push(x_20, x_34);
lean_ctor_set(x_4, 1, x_35);
x_10 = x_4;
x_11 = x_9;
goto block_15;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_4, 0);
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_4);
x_38 = lean_array_uget(x_1, x_3);
x_39 = l_Lean_Expr_isFVar(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_40 = lean_infer_type(x_38, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
x_43 = l_Lean_instantiateMVars___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3___redArg(x_41, x_6, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = l_Lean_CollectFVars_main(x_44, x_36);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_37);
x_10 = x_47;
x_11 = x_45;
goto block_15;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_48 = lean_ctor_get(x_40, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_40, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_50 = x_40;
} else {
 lean_dec_ref(x_40);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = l_Lean_Expr_fvarId_x21(x_38);
lean_dec_ref(x_38);
x_53 = lean_array_push(x_37, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_36);
lean_ctor_set(x_54, 1, x_53);
x_10 = x_54;
x_11 = x_9;
goto block_15;
}
}
}
block_15:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0_spec__0(x_1, x_2, x_13, x_10, x_5, x_6, x_7, x_8, x_11);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_8 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
x_9 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__5;
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_2);
lean_ctor_set(x_10, 2, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_array_size(x_1);
x_13 = 0;
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0(x_1, x_12, x_13, x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec_ref(x_14);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_array_to_list(x_18);
x_21 = l_Lean_Meta_mkGeneralizationForbiddenSet_loop(x_20, x_19, x_3, x_4, x_5, x_6, x_17);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkGeneralizationForbiddenSet(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_7, x_6);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
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
x_19 = lean_array_uget(x_5, x_7);
lean_inc(x_17);
x_20 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(x_1, x_2, x_3, x_19, x_17, x_9, x_10, x_11, x_12, x_13);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_8, 0, x_24);
lean_ctor_set(x_20, 0, x_8);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_8, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_8);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
lean_dec(x_17);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec_ref(x_20);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec_ref(x_21);
lean_inc(x_4);
lean_ctor_set(x_8, 1, x_29);
lean_ctor_set(x_8, 0, x_4);
x_30 = 1;
x_31 = lean_usize_add(x_7, x_30);
x_7 = x_31;
x_13 = x_28;
goto _start;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_8, 1);
lean_inc(x_33);
lean_dec(x_8);
x_34 = lean_array_uget(x_5, x_7);
lean_inc(x_33);
x_35 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(x_1, x_2, x_3, x_34, x_33, x_9, x_10, x_11, x_12, x_13);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_4);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_33);
if (lean_is_scalar(x_38)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_38;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; 
lean_dec(x_33);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_dec_ref(x_35);
x_43 = lean_ctor_get(x_36, 0);
lean_inc(x_43);
lean_dec_ref(x_36);
lean_inc(x_4);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_43);
x_45 = 1;
x_46 = lean_usize_add(x_7, x_45);
x_7 = x_46;
x_8 = x_44;
x_13 = x_42;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_6, x_5);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_20 = x_7;
} else {
 lean_dec_ref(x_7);
 x_20 = lean_box(0);
}
x_21 = lean_array_uget(x_4, x_6);
if (lean_obj_tag(x_21) == 0)
{
lean_dec(x_20);
x_10 = x_19;
x_11 = x_9;
goto block_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_138; uint8_t x_139; lean_object* x_205; uint8_t x_206; lean_object* x_209; lean_object* x_216; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_25 = x_19;
} else {
 lean_dec_ref(x_19);
 x_25 = lean_box(0);
}
lean_inc(x_24);
x_117 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_117, 0, x_24);
x_216 = lean_ctor_get(x_22, 1);
lean_inc(x_216);
x_209 = x_216;
goto block_215;
block_27:
{
lean_object* x_26; 
if (lean_is_scalar(x_25)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_25;
}
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
x_10 = x_26;
x_11 = x_9;
goto block_16;
}
block_35:
{
if (x_29 == 0)
{
lean_object* x_31; 
lean_dec(x_28);
if (lean_is_scalar(x_20)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_20;
}
lean_ctor_set(x_31, 0, x_23);
lean_ctor_set(x_31, 1, x_24);
x_10 = x_31;
x_11 = x_30;
goto block_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_inc(x_28);
x_32 = l_Lean_FVarIdSet_insert(x_23, x_28);
x_33 = l_Lean_FVarIdSet_insert(x_24, x_28);
if (lean_is_scalar(x_20)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_20;
}
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_10 = x_34;
x_11 = x_30;
goto block_16;
}
}
block_54:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_st_ref_take(x_8, x_36);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_41, 0);
lean_dec(x_44);
lean_ctor_set(x_41, 0, x_39);
x_45 = lean_st_ref_set(x_8, x_41, x_42);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec_ref(x_45);
x_28 = x_37;
x_29 = x_38;
x_30 = x_46;
goto block_35;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_41, 1);
x_48 = lean_ctor_get(x_41, 2);
x_49 = lean_ctor_get(x_41, 3);
x_50 = lean_ctor_get(x_41, 4);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_41);
x_51 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_51, 0, x_39);
lean_ctor_set(x_51, 1, x_47);
lean_ctor_set(x_51, 2, x_48);
lean_ctor_set(x_51, 3, x_49);
lean_ctor_set(x_51, 4, x_50);
x_52 = lean_st_ref_set(x_8, x_51, x_42);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec_ref(x_52);
x_28 = x_37;
x_29 = x_38;
x_30 = x_53;
goto block_35;
}
}
block_62:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
lean_dec_ref(x_57);
x_60 = lean_ctor_get(x_58, 1);
lean_inc_ref(x_60);
lean_dec(x_58);
x_61 = lean_unbox(x_59);
lean_dec(x_59);
x_36 = x_55;
x_37 = x_56;
x_38 = x_61;
x_39 = x_60;
goto block_54;
}
block_82:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc_ref(x_67);
lean_dec_ref(x_66);
x_68 = lean_st_ref_take(x_8, x_63);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec_ref(x_68);
x_71 = !lean_is_exclusive(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_69, 0);
lean_dec(x_72);
lean_ctor_set(x_69, 0, x_67);
x_73 = lean_st_ref_set(x_8, x_69, x_70);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec_ref(x_73);
x_28 = x_64;
x_29 = x_65;
x_30 = x_74;
goto block_35;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_75 = lean_ctor_get(x_69, 1);
x_76 = lean_ctor_get(x_69, 2);
x_77 = lean_ctor_get(x_69, 3);
x_78 = lean_ctor_get(x_69, 4);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_69);
x_79 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_79, 0, x_67);
lean_ctor_set(x_79, 1, x_75);
lean_ctor_set(x_79, 2, x_76);
lean_ctor_set(x_79, 3, x_77);
lean_ctor_set(x_79, 4, x_78);
x_80 = lean_st_ref_set(x_8, x_79, x_70);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec_ref(x_80);
x_28 = x_64;
x_29 = x_65;
x_30 = x_81;
goto block_35;
}
}
block_89:
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec_ref(x_85);
x_88 = lean_unbox(x_86);
lean_dec(x_86);
x_63 = x_83;
x_64 = x_84;
x_65 = x_88;
x_66 = x_87;
goto block_82;
}
block_108:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_94 = lean_st_ref_take(x_8, x_90);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec_ref(x_94);
x_97 = !lean_is_exclusive(x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_95, 0);
lean_dec(x_98);
lean_ctor_set(x_95, 0, x_93);
x_99 = lean_st_ref_set(x_8, x_95, x_96);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec_ref(x_99);
x_28 = x_91;
x_29 = x_92;
x_30 = x_100;
goto block_35;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_101 = lean_ctor_get(x_95, 1);
x_102 = lean_ctor_get(x_95, 2);
x_103 = lean_ctor_get(x_95, 3);
x_104 = lean_ctor_get(x_95, 4);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_95);
x_105 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_105, 0, x_93);
lean_ctor_set(x_105, 1, x_101);
lean_ctor_set(x_105, 2, x_102);
lean_ctor_set(x_105, 3, x_103);
lean_ctor_set(x_105, 4, x_104);
x_106 = lean_st_ref_set(x_8, x_105, x_96);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec_ref(x_106);
x_28 = x_91;
x_29 = x_92;
x_30 = x_107;
goto block_35;
}
}
block_116:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
lean_dec_ref(x_111);
x_114 = lean_ctor_get(x_112, 1);
lean_inc_ref(x_114);
lean_dec(x_112);
x_115 = lean_unbox(x_113);
lean_dec(x_113);
x_90 = x_109;
x_91 = x_110;
x_92 = x_115;
x_93 = x_114;
goto block_108;
}
block_128:
{
if (x_122 == 0)
{
uint8_t x_124; 
x_124 = l_Lean_Expr_hasFVar(x_121);
if (x_124 == 0)
{
uint8_t x_125; 
x_125 = l_Lean_Expr_hasMVar(x_121);
if (x_125 == 0)
{
lean_dec_ref(x_121);
lean_dec_ref(x_119);
lean_dec_ref(x_117);
x_63 = x_118;
x_64 = x_120;
x_65 = x_125;
x_66 = x_123;
goto block_82;
}
else
{
lean_object* x_126; 
x_126 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_117, x_119, x_121, x_123);
x_83 = x_118;
x_84 = x_120;
x_85 = x_126;
goto block_89;
}
}
else
{
lean_object* x_127; 
x_127 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_117, x_119, x_121, x_123);
x_83 = x_118;
x_84 = x_120;
x_85 = x_127;
goto block_89;
}
}
else
{
lean_dec_ref(x_121);
lean_dec_ref(x_119);
lean_dec_ref(x_117);
x_63 = x_118;
x_64 = x_120;
x_65 = x_122;
x_66 = x_123;
goto block_82;
}
}
block_137:
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec_ref(x_133);
x_136 = lean_unbox(x_134);
lean_dec(x_134);
x_118 = x_129;
x_119 = x_130;
x_120 = x_131;
x_121 = x_132;
x_122 = x_136;
x_123 = x_135;
goto block_128;
}
block_204:
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_box(x_139);
x_141 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_141, 0, x_140);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_142 = lean_ctor_get(x_22, 3);
lean_inc_ref(x_142);
lean_dec_ref(x_22);
x_143 = lean_st_ref_get(x_8, x_9);
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_145 = lean_ctor_get(x_143, 0);
x_146 = lean_ctor_get(x_143, 1);
x_147 = lean_ctor_get(x_145, 0);
lean_inc_ref(x_147);
lean_dec(x_145);
x_148 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
lean_inc_ref(x_147);
lean_ctor_set(x_143, 1, x_147);
lean_ctor_set(x_143, 0, x_148);
x_149 = l_Lean_Expr_hasFVar(x_142);
if (x_149 == 0)
{
uint8_t x_150; 
x_150 = l_Lean_Expr_hasMVar(x_142);
if (x_150 == 0)
{
lean_dec_ref(x_143);
lean_dec_ref(x_142);
lean_dec_ref(x_141);
lean_dec_ref(x_117);
x_36 = x_146;
x_37 = x_138;
x_38 = x_150;
x_39 = x_147;
goto block_54;
}
else
{
lean_object* x_151; 
lean_dec_ref(x_147);
x_151 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_117, x_141, x_142, x_143);
x_55 = x_146;
x_56 = x_138;
x_57 = x_151;
goto block_62;
}
}
else
{
lean_object* x_152; 
lean_dec_ref(x_147);
x_152 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_117, x_141, x_142, x_143);
x_55 = x_146;
x_56 = x_138;
x_57 = x_152;
goto block_62;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_153 = lean_ctor_get(x_143, 0);
x_154 = lean_ctor_get(x_143, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_143);
x_155 = lean_ctor_get(x_153, 0);
lean_inc_ref(x_155);
lean_dec(x_153);
x_156 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
lean_inc_ref(x_155);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
x_158 = l_Lean_Expr_hasFVar(x_142);
if (x_158 == 0)
{
uint8_t x_159; 
x_159 = l_Lean_Expr_hasMVar(x_142);
if (x_159 == 0)
{
lean_dec_ref(x_157);
lean_dec_ref(x_142);
lean_dec_ref(x_141);
lean_dec_ref(x_117);
x_36 = x_154;
x_37 = x_138;
x_38 = x_159;
x_39 = x_155;
goto block_54;
}
else
{
lean_object* x_160; 
lean_dec_ref(x_155);
x_160 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_117, x_141, x_142, x_157);
x_55 = x_154;
x_56 = x_138;
x_57 = x_160;
goto block_62;
}
}
else
{
lean_object* x_161; 
lean_dec_ref(x_155);
x_161 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_117, x_141, x_142, x_157);
x_55 = x_154;
x_56 = x_138;
x_57 = x_161;
goto block_62;
}
}
}
else
{
uint8_t x_162; 
x_162 = lean_ctor_get_uint8(x_22, sizeof(void*)*5);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_163 = lean_ctor_get(x_22, 3);
lean_inc_ref(x_163);
x_164 = lean_ctor_get(x_22, 4);
lean_inc_ref(x_164);
lean_dec_ref(x_22);
x_165 = lean_st_ref_get(x_8, x_9);
x_166 = !lean_is_exclusive(x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_167 = lean_ctor_get(x_165, 0);
x_168 = lean_ctor_get(x_165, 1);
x_169 = lean_ctor_get(x_167, 0);
lean_inc_ref(x_169);
lean_dec(x_167);
x_170 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
lean_ctor_set(x_165, 1, x_169);
lean_ctor_set(x_165, 0, x_170);
x_171 = l_Lean_Expr_hasFVar(x_163);
if (x_171 == 0)
{
uint8_t x_172; 
x_172 = l_Lean_Expr_hasMVar(x_163);
if (x_172 == 0)
{
lean_dec_ref(x_163);
x_118 = x_168;
x_119 = x_141;
x_120 = x_138;
x_121 = x_164;
x_122 = x_172;
x_123 = x_165;
goto block_128;
}
else
{
lean_object* x_173; 
lean_inc_ref(x_141);
lean_inc_ref(x_117);
x_173 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_117, x_141, x_163, x_165);
x_129 = x_168;
x_130 = x_141;
x_131 = x_138;
x_132 = x_164;
x_133 = x_173;
goto block_137;
}
}
else
{
lean_object* x_174; 
lean_inc_ref(x_141);
lean_inc_ref(x_117);
x_174 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_117, x_141, x_163, x_165);
x_129 = x_168;
x_130 = x_141;
x_131 = x_138;
x_132 = x_164;
x_133 = x_174;
goto block_137;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_175 = lean_ctor_get(x_165, 0);
x_176 = lean_ctor_get(x_165, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_165);
x_177 = lean_ctor_get(x_175, 0);
lean_inc_ref(x_177);
lean_dec(x_175);
x_178 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_177);
x_180 = l_Lean_Expr_hasFVar(x_163);
if (x_180 == 0)
{
uint8_t x_181; 
x_181 = l_Lean_Expr_hasMVar(x_163);
if (x_181 == 0)
{
lean_dec_ref(x_163);
x_118 = x_176;
x_119 = x_141;
x_120 = x_138;
x_121 = x_164;
x_122 = x_181;
x_123 = x_179;
goto block_128;
}
else
{
lean_object* x_182; 
lean_inc_ref(x_141);
lean_inc_ref(x_117);
x_182 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_117, x_141, x_163, x_179);
x_129 = x_176;
x_130 = x_141;
x_131 = x_138;
x_132 = x_164;
x_133 = x_182;
goto block_137;
}
}
else
{
lean_object* x_183; 
lean_inc_ref(x_141);
lean_inc_ref(x_117);
x_183 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_117, x_141, x_163, x_179);
x_129 = x_176;
x_130 = x_141;
x_131 = x_138;
x_132 = x_164;
x_133 = x_183;
goto block_137;
}
}
}
else
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_184 = lean_ctor_get(x_22, 3);
lean_inc_ref(x_184);
lean_dec_ref(x_22);
x_185 = lean_st_ref_get(x_8, x_9);
x_186 = !lean_is_exclusive(x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_187 = lean_ctor_get(x_185, 0);
x_188 = lean_ctor_get(x_185, 1);
x_189 = lean_ctor_get(x_187, 0);
lean_inc_ref(x_189);
lean_dec(x_187);
x_190 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
lean_inc_ref(x_189);
lean_ctor_set(x_185, 1, x_189);
lean_ctor_set(x_185, 0, x_190);
x_191 = l_Lean_Expr_hasFVar(x_184);
if (x_191 == 0)
{
uint8_t x_192; 
x_192 = l_Lean_Expr_hasMVar(x_184);
if (x_192 == 0)
{
lean_dec_ref(x_185);
lean_dec_ref(x_184);
lean_dec_ref(x_141);
lean_dec_ref(x_117);
x_90 = x_188;
x_91 = x_138;
x_92 = x_192;
x_93 = x_189;
goto block_108;
}
else
{
lean_object* x_193; 
lean_dec_ref(x_189);
x_193 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_117, x_141, x_184, x_185);
x_109 = x_188;
x_110 = x_138;
x_111 = x_193;
goto block_116;
}
}
else
{
lean_object* x_194; 
lean_dec_ref(x_189);
x_194 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_117, x_141, x_184, x_185);
x_109 = x_188;
x_110 = x_138;
x_111 = x_194;
goto block_116;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_195 = lean_ctor_get(x_185, 0);
x_196 = lean_ctor_get(x_185, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_185);
x_197 = lean_ctor_get(x_195, 0);
lean_inc_ref(x_197);
lean_dec(x_195);
x_198 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
lean_inc_ref(x_197);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_197);
x_200 = l_Lean_Expr_hasFVar(x_184);
if (x_200 == 0)
{
uint8_t x_201; 
x_201 = l_Lean_Expr_hasMVar(x_184);
if (x_201 == 0)
{
lean_dec_ref(x_199);
lean_dec_ref(x_184);
lean_dec_ref(x_141);
lean_dec_ref(x_117);
x_90 = x_196;
x_91 = x_138;
x_92 = x_201;
x_93 = x_197;
goto block_108;
}
else
{
lean_object* x_202; 
lean_dec_ref(x_197);
x_202 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_117, x_141, x_184, x_199);
x_109 = x_196;
x_110 = x_138;
x_111 = x_202;
goto block_116;
}
}
else
{
lean_object* x_203; 
lean_dec_ref(x_197);
x_203 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_117, x_141, x_184, x_199);
x_109 = x_196;
x_110 = x_138;
x_111 = x_203;
goto block_116;
}
}
}
}
}
block_208:
{
if (x_206 == 0)
{
if (x_2 == 0)
{
lean_dec(x_25);
x_138 = x_205;
x_139 = x_2;
goto block_204;
}
else
{
uint8_t x_207; 
x_207 = l_Lean_LocalDecl_isLet(x_22, x_206);
if (x_207 == 0)
{
lean_dec(x_25);
x_138 = x_205;
x_139 = x_207;
goto block_204;
}
else
{
lean_dec(x_205);
lean_dec_ref(x_117);
lean_dec(x_22);
lean_dec(x_20);
goto block_27;
}
}
}
else
{
lean_dec(x_205);
lean_dec_ref(x_117);
lean_dec(x_22);
lean_dec(x_20);
goto block_27;
}
}
block_215:
{
uint8_t x_210; 
x_210 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_209, x_3);
if (x_210 == 0)
{
uint8_t x_211; 
x_211 = l_Lean_LocalDecl_isAuxDecl(x_22);
if (x_211 == 0)
{
uint8_t x_212; uint8_t x_213; 
x_212 = l_Lean_LocalDecl_binderInfo(x_22);
x_213 = l_Lean_BinderInfo_isInstImplicit(x_212);
x_205 = x_209;
x_206 = x_213;
goto block_208;
}
else
{
x_205 = x_209;
x_206 = x_211;
goto block_208;
}
}
else
{
lean_object* x_214; 
lean_dec(x_209);
lean_dec_ref(x_117);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_20);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_23);
lean_ctor_set(x_214, 1, x_24);
x_10 = x_214;
x_11 = x_9;
goto block_16;
}
}
}
}
block_16:
{
lean_object* x_12; size_t x_13; size_t x_14; 
lean_inc(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_10);
x_13 = 1;
x_14 = lean_usize_add(x_6, x_13);
x_6 = x_14;
x_7 = x_12;
x_9 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_20; 
x_20 = lean_usize_dec_lt(x_6, x_5);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_3);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_23 = x_7;
} else {
 lean_dec_ref(x_7);
 x_23 = lean_box(0);
}
x_24 = lean_array_uget(x_4, x_6);
if (lean_obj_tag(x_24) == 0)
{
lean_dec(x_23);
x_13 = x_22;
x_14 = x_12;
goto block_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_141; uint8_t x_142; lean_object* x_208; uint8_t x_209; lean_object* x_212; lean_object* x_219; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_28 = x_22;
} else {
 lean_dec_ref(x_22);
 x_28 = lean_box(0);
}
lean_inc(x_27);
x_120 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_120, 0, x_27);
x_219 = lean_ctor_get(x_25, 1);
lean_inc(x_219);
x_212 = x_219;
goto block_218;
block_30:
{
lean_object* x_29; 
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
x_13 = x_29;
x_14 = x_12;
goto block_19;
}
block_38:
{
if (x_32 == 0)
{
lean_object* x_34; 
lean_dec(x_31);
if (lean_is_scalar(x_23)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_23;
}
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_27);
x_13 = x_34;
x_14 = x_33;
goto block_19;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_inc(x_31);
x_35 = l_Lean_FVarIdSet_insert(x_26, x_31);
x_36 = l_Lean_FVarIdSet_insert(x_27, x_31);
if (lean_is_scalar(x_23)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_23;
}
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_13 = x_37;
x_14 = x_33;
goto block_19;
}
}
block_57:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_st_ref_take(x_9, x_39);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_44, 0);
lean_dec(x_47);
lean_ctor_set(x_44, 0, x_42);
x_48 = lean_st_ref_set(x_9, x_44, x_45);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec_ref(x_48);
x_31 = x_40;
x_32 = x_41;
x_33 = x_49;
goto block_38;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_44, 1);
x_51 = lean_ctor_get(x_44, 2);
x_52 = lean_ctor_get(x_44, 3);
x_53 = lean_ctor_get(x_44, 4);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_44);
x_54 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_54, 0, x_42);
lean_ctor_set(x_54, 1, x_50);
lean_ctor_set(x_54, 2, x_51);
lean_ctor_set(x_54, 3, x_52);
lean_ctor_set(x_54, 4, x_53);
x_55 = lean_st_ref_set(x_9, x_54, x_45);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec_ref(x_55);
x_31 = x_40;
x_32 = x_41;
x_33 = x_56;
goto block_38;
}
}
block_65:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec_ref(x_60);
x_63 = lean_ctor_get(x_61, 1);
lean_inc_ref(x_63);
lean_dec(x_61);
x_64 = lean_unbox(x_62);
lean_dec(x_62);
x_39 = x_58;
x_40 = x_59;
x_41 = x_64;
x_42 = x_63;
goto block_57;
}
block_85:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc_ref(x_70);
lean_dec_ref(x_69);
x_71 = lean_st_ref_take(x_9, x_66);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec_ref(x_71);
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_72, 0);
lean_dec(x_75);
lean_ctor_set(x_72, 0, x_70);
x_76 = lean_st_ref_set(x_9, x_72, x_73);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec_ref(x_76);
x_31 = x_67;
x_32 = x_68;
x_33 = x_77;
goto block_38;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_78 = lean_ctor_get(x_72, 1);
x_79 = lean_ctor_get(x_72, 2);
x_80 = lean_ctor_get(x_72, 3);
x_81 = lean_ctor_get(x_72, 4);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_72);
x_82 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_82, 0, x_70);
lean_ctor_set(x_82, 1, x_78);
lean_ctor_set(x_82, 2, x_79);
lean_ctor_set(x_82, 3, x_80);
lean_ctor_set(x_82, 4, x_81);
x_83 = lean_st_ref_set(x_9, x_82, x_73);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec_ref(x_83);
x_31 = x_67;
x_32 = x_68;
x_33 = x_84;
goto block_38;
}
}
block_92:
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec_ref(x_88);
x_91 = lean_unbox(x_89);
lean_dec(x_89);
x_66 = x_86;
x_67 = x_87;
x_68 = x_91;
x_69 = x_90;
goto block_85;
}
block_111:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_97 = lean_st_ref_take(x_9, x_94);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec_ref(x_97);
x_100 = !lean_is_exclusive(x_98);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_98, 0);
lean_dec(x_101);
lean_ctor_set(x_98, 0, x_96);
x_102 = lean_st_ref_set(x_9, x_98, x_99);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec_ref(x_102);
x_31 = x_93;
x_32 = x_95;
x_33 = x_103;
goto block_38;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = lean_ctor_get(x_98, 1);
x_105 = lean_ctor_get(x_98, 2);
x_106 = lean_ctor_get(x_98, 3);
x_107 = lean_ctor_get(x_98, 4);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_98);
x_108 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_108, 0, x_96);
lean_ctor_set(x_108, 1, x_104);
lean_ctor_set(x_108, 2, x_105);
lean_ctor_set(x_108, 3, x_106);
lean_ctor_set(x_108, 4, x_107);
x_109 = lean_st_ref_set(x_9, x_108, x_99);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec_ref(x_109);
x_31 = x_93;
x_32 = x_95;
x_33 = x_110;
goto block_38;
}
}
block_119:
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
lean_dec_ref(x_114);
x_117 = lean_ctor_get(x_115, 1);
lean_inc_ref(x_117);
lean_dec(x_115);
x_118 = lean_unbox(x_116);
lean_dec(x_116);
x_93 = x_112;
x_94 = x_113;
x_95 = x_118;
x_96 = x_117;
goto block_111;
}
block_131:
{
if (x_125 == 0)
{
uint8_t x_127; 
x_127 = l_Lean_Expr_hasFVar(x_124);
if (x_127 == 0)
{
uint8_t x_128; 
x_128 = l_Lean_Expr_hasMVar(x_124);
if (x_128 == 0)
{
lean_dec_ref(x_124);
lean_dec_ref(x_122);
lean_dec_ref(x_120);
x_66 = x_121;
x_67 = x_123;
x_68 = x_128;
x_69 = x_126;
goto block_85;
}
else
{
lean_object* x_129; 
x_129 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_120, x_122, x_124, x_126);
x_86 = x_121;
x_87 = x_123;
x_88 = x_129;
goto block_92;
}
}
else
{
lean_object* x_130; 
x_130 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_120, x_122, x_124, x_126);
x_86 = x_121;
x_87 = x_123;
x_88 = x_130;
goto block_92;
}
}
else
{
lean_dec_ref(x_124);
lean_dec_ref(x_122);
lean_dec_ref(x_120);
x_66 = x_121;
x_67 = x_123;
x_68 = x_125;
x_69 = x_126;
goto block_85;
}
}
block_140:
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec_ref(x_136);
x_139 = lean_unbox(x_137);
lean_dec(x_137);
x_121 = x_132;
x_122 = x_133;
x_123 = x_134;
x_124 = x_135;
x_125 = x_139;
x_126 = x_138;
goto block_131;
}
block_207:
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_box(x_142);
x_144 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_144, 0, x_143);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_145 = lean_ctor_get(x_25, 3);
lean_inc_ref(x_145);
lean_dec_ref(x_25);
x_146 = lean_st_ref_get(x_9, x_12);
x_147 = !lean_is_exclusive(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_148 = lean_ctor_get(x_146, 0);
x_149 = lean_ctor_get(x_146, 1);
x_150 = lean_ctor_get(x_148, 0);
lean_inc_ref(x_150);
lean_dec(x_148);
x_151 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
lean_inc_ref(x_150);
lean_ctor_set(x_146, 1, x_150);
lean_ctor_set(x_146, 0, x_151);
x_152 = l_Lean_Expr_hasFVar(x_145);
if (x_152 == 0)
{
uint8_t x_153; 
x_153 = l_Lean_Expr_hasMVar(x_145);
if (x_153 == 0)
{
lean_dec_ref(x_146);
lean_dec_ref(x_145);
lean_dec_ref(x_144);
lean_dec_ref(x_120);
x_39 = x_149;
x_40 = x_141;
x_41 = x_153;
x_42 = x_150;
goto block_57;
}
else
{
lean_object* x_154; 
lean_dec_ref(x_150);
x_154 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_120, x_144, x_145, x_146);
x_58 = x_149;
x_59 = x_141;
x_60 = x_154;
goto block_65;
}
}
else
{
lean_object* x_155; 
lean_dec_ref(x_150);
x_155 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_120, x_144, x_145, x_146);
x_58 = x_149;
x_59 = x_141;
x_60 = x_155;
goto block_65;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_156 = lean_ctor_get(x_146, 0);
x_157 = lean_ctor_get(x_146, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_146);
x_158 = lean_ctor_get(x_156, 0);
lean_inc_ref(x_158);
lean_dec(x_156);
x_159 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
lean_inc_ref(x_158);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
x_161 = l_Lean_Expr_hasFVar(x_145);
if (x_161 == 0)
{
uint8_t x_162; 
x_162 = l_Lean_Expr_hasMVar(x_145);
if (x_162 == 0)
{
lean_dec_ref(x_160);
lean_dec_ref(x_145);
lean_dec_ref(x_144);
lean_dec_ref(x_120);
x_39 = x_157;
x_40 = x_141;
x_41 = x_162;
x_42 = x_158;
goto block_57;
}
else
{
lean_object* x_163; 
lean_dec_ref(x_158);
x_163 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_120, x_144, x_145, x_160);
x_58 = x_157;
x_59 = x_141;
x_60 = x_163;
goto block_65;
}
}
else
{
lean_object* x_164; 
lean_dec_ref(x_158);
x_164 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_120, x_144, x_145, x_160);
x_58 = x_157;
x_59 = x_141;
x_60 = x_164;
goto block_65;
}
}
}
else
{
uint8_t x_165; 
x_165 = lean_ctor_get_uint8(x_25, sizeof(void*)*5);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_166 = lean_ctor_get(x_25, 3);
lean_inc_ref(x_166);
x_167 = lean_ctor_get(x_25, 4);
lean_inc_ref(x_167);
lean_dec_ref(x_25);
x_168 = lean_st_ref_get(x_9, x_12);
x_169 = !lean_is_exclusive(x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_170 = lean_ctor_get(x_168, 0);
x_171 = lean_ctor_get(x_168, 1);
x_172 = lean_ctor_get(x_170, 0);
lean_inc_ref(x_172);
lean_dec(x_170);
x_173 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
lean_ctor_set(x_168, 1, x_172);
lean_ctor_set(x_168, 0, x_173);
x_174 = l_Lean_Expr_hasFVar(x_166);
if (x_174 == 0)
{
uint8_t x_175; 
x_175 = l_Lean_Expr_hasMVar(x_166);
if (x_175 == 0)
{
lean_dec_ref(x_166);
x_121 = x_171;
x_122 = x_144;
x_123 = x_141;
x_124 = x_167;
x_125 = x_175;
x_126 = x_168;
goto block_131;
}
else
{
lean_object* x_176; 
lean_inc_ref(x_144);
lean_inc_ref(x_120);
x_176 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_120, x_144, x_166, x_168);
x_132 = x_171;
x_133 = x_144;
x_134 = x_141;
x_135 = x_167;
x_136 = x_176;
goto block_140;
}
}
else
{
lean_object* x_177; 
lean_inc_ref(x_144);
lean_inc_ref(x_120);
x_177 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_120, x_144, x_166, x_168);
x_132 = x_171;
x_133 = x_144;
x_134 = x_141;
x_135 = x_167;
x_136 = x_177;
goto block_140;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_178 = lean_ctor_get(x_168, 0);
x_179 = lean_ctor_get(x_168, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_168);
x_180 = lean_ctor_get(x_178, 0);
lean_inc_ref(x_180);
lean_dec(x_178);
x_181 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_180);
x_183 = l_Lean_Expr_hasFVar(x_166);
if (x_183 == 0)
{
uint8_t x_184; 
x_184 = l_Lean_Expr_hasMVar(x_166);
if (x_184 == 0)
{
lean_dec_ref(x_166);
x_121 = x_179;
x_122 = x_144;
x_123 = x_141;
x_124 = x_167;
x_125 = x_184;
x_126 = x_182;
goto block_131;
}
else
{
lean_object* x_185; 
lean_inc_ref(x_144);
lean_inc_ref(x_120);
x_185 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_120, x_144, x_166, x_182);
x_132 = x_179;
x_133 = x_144;
x_134 = x_141;
x_135 = x_167;
x_136 = x_185;
goto block_140;
}
}
else
{
lean_object* x_186; 
lean_inc_ref(x_144);
lean_inc_ref(x_120);
x_186 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_120, x_144, x_166, x_182);
x_132 = x_179;
x_133 = x_144;
x_134 = x_141;
x_135 = x_167;
x_136 = x_186;
goto block_140;
}
}
}
else
{
lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_187 = lean_ctor_get(x_25, 3);
lean_inc_ref(x_187);
lean_dec_ref(x_25);
x_188 = lean_st_ref_get(x_9, x_12);
x_189 = !lean_is_exclusive(x_188);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_190 = lean_ctor_get(x_188, 0);
x_191 = lean_ctor_get(x_188, 1);
x_192 = lean_ctor_get(x_190, 0);
lean_inc_ref(x_192);
lean_dec(x_190);
x_193 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
lean_inc_ref(x_192);
lean_ctor_set(x_188, 1, x_192);
lean_ctor_set(x_188, 0, x_193);
x_194 = l_Lean_Expr_hasFVar(x_187);
if (x_194 == 0)
{
uint8_t x_195; 
x_195 = l_Lean_Expr_hasMVar(x_187);
if (x_195 == 0)
{
lean_dec_ref(x_188);
lean_dec_ref(x_187);
lean_dec_ref(x_144);
lean_dec_ref(x_120);
x_93 = x_141;
x_94 = x_191;
x_95 = x_195;
x_96 = x_192;
goto block_111;
}
else
{
lean_object* x_196; 
lean_dec_ref(x_192);
x_196 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_120, x_144, x_187, x_188);
x_112 = x_141;
x_113 = x_191;
x_114 = x_196;
goto block_119;
}
}
else
{
lean_object* x_197; 
lean_dec_ref(x_192);
x_197 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_120, x_144, x_187, x_188);
x_112 = x_141;
x_113 = x_191;
x_114 = x_197;
goto block_119;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_198 = lean_ctor_get(x_188, 0);
x_199 = lean_ctor_get(x_188, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_188);
x_200 = lean_ctor_get(x_198, 0);
lean_inc_ref(x_200);
lean_dec(x_198);
x_201 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
lean_inc_ref(x_200);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_200);
x_203 = l_Lean_Expr_hasFVar(x_187);
if (x_203 == 0)
{
uint8_t x_204; 
x_204 = l_Lean_Expr_hasMVar(x_187);
if (x_204 == 0)
{
lean_dec_ref(x_202);
lean_dec_ref(x_187);
lean_dec_ref(x_144);
lean_dec_ref(x_120);
x_93 = x_141;
x_94 = x_199;
x_95 = x_204;
x_96 = x_200;
goto block_111;
}
else
{
lean_object* x_205; 
lean_dec_ref(x_200);
x_205 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_120, x_144, x_187, x_202);
x_112 = x_141;
x_113 = x_199;
x_114 = x_205;
goto block_119;
}
}
else
{
lean_object* x_206; 
lean_dec_ref(x_200);
x_206 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_120, x_144, x_187, x_202);
x_112 = x_141;
x_113 = x_199;
x_114 = x_206;
goto block_119;
}
}
}
}
}
block_211:
{
if (x_209 == 0)
{
if (x_1 == 0)
{
lean_dec(x_28);
x_141 = x_208;
x_142 = x_1;
goto block_207;
}
else
{
uint8_t x_210; 
x_210 = l_Lean_LocalDecl_isLet(x_25, x_209);
if (x_210 == 0)
{
lean_dec(x_28);
x_141 = x_208;
x_142 = x_210;
goto block_207;
}
else
{
lean_dec(x_208);
lean_dec_ref(x_120);
lean_dec(x_25);
lean_dec(x_23);
goto block_30;
}
}
}
else
{
lean_dec(x_208);
lean_dec_ref(x_120);
lean_dec(x_25);
lean_dec(x_23);
goto block_30;
}
}
block_218:
{
uint8_t x_213; 
x_213 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_212, x_2);
if (x_213 == 0)
{
uint8_t x_214; 
x_214 = l_Lean_LocalDecl_isAuxDecl(x_25);
if (x_214 == 0)
{
uint8_t x_215; uint8_t x_216; 
x_215 = l_Lean_LocalDecl_binderInfo(x_25);
x_216 = l_Lean_BinderInfo_isInstImplicit(x_215);
x_208 = x_212;
x_209 = x_216;
goto block_211;
}
else
{
x_208 = x_212;
x_209 = x_214;
goto block_211;
}
}
else
{
lean_object* x_217; 
lean_dec(x_212);
lean_dec_ref(x_120);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_23);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_26);
lean_ctor_set(x_217, 1, x_27);
x_13 = x_217;
x_14 = x_12;
goto block_19;
}
}
}
}
block_19:
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
lean_inc(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_13);
x_16 = 1;
x_17 = lean_usize_add(x_6, x_16);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg(x_3, x_1, x_2, x_4, x_5, x_17, x_15, x_9, x_14);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
x_15 = lean_array_size(x_12);
x_16 = 0;
x_17 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_13, x_12, x_15, x_16, x_14, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_12);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_22);
lean_ctor_set(x_17, 0, x_4);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_18);
lean_free_object(x_4);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_17, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
lean_dec_ref(x_19);
lean_ctor_set(x_17, 0, x_28);
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_dec(x_17);
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
lean_dec_ref(x_19);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_4, 0);
lean_inc(x_32);
lean_dec(x_4);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_5);
x_35 = lean_array_size(x_32);
x_36 = 0;
x_37 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_33, x_32, x_35, x_36, x_34, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_32);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_41 = x_37;
} else {
 lean_dec_ref(x_37);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_38);
x_45 = lean_ctor_get(x_37, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_46 = x_37;
} else {
 lean_dec_ref(x_37);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_39, 0);
lean_inc(x_47);
lean_dec_ref(x_39);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_4);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_ctor_get(x_4, 0);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_5);
x_53 = lean_array_size(x_50);
x_54 = 0;
x_55 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(x_1, x_2, x_51, x_50, x_53, x_54, x_52, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_50);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_55);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_55, 0);
lean_dec(x_59);
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
lean_dec(x_56);
lean_ctor_set(x_4, 0, x_60);
lean_ctor_set(x_55, 0, x_4);
return x_55;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_dec(x_55);
x_62 = lean_ctor_get(x_56, 1);
lean_inc(x_62);
lean_dec(x_56);
lean_ctor_set(x_4, 0, x_62);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_4);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_56);
lean_free_object(x_4);
x_64 = !lean_is_exclusive(x_55);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_55, 0);
lean_dec(x_65);
x_66 = lean_ctor_get(x_57, 0);
lean_inc(x_66);
lean_dec_ref(x_57);
lean_ctor_set(x_55, 0, x_66);
return x_55;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_55, 1);
lean_inc(x_67);
lean_dec(x_55);
x_68 = lean_ctor_get(x_57, 0);
lean_inc(x_68);
lean_dec_ref(x_57);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_70 = lean_ctor_get(x_4, 0);
lean_inc(x_70);
lean_dec(x_4);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_5);
x_73 = lean_array_size(x_70);
x_74 = 0;
x_75 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(x_1, x_2, x_71, x_70, x_73, x_74, x_72, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_70);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_79 = x_75;
} else {
 lean_dec_ref(x_75);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_76, 1);
lean_inc(x_80);
lean_dec(x_76);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
if (lean_is_scalar(x_79)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_79;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_78);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_76);
x_83 = lean_ctor_get(x_75, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_84 = x_75;
} else {
 lean_dec_ref(x_75);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_77, 0);
lean_inc(x_85);
lean_dec_ref(x_77);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
return x_86;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_6, x_5);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_20 = x_7;
} else {
 lean_dec_ref(x_7);
 x_20 = lean_box(0);
}
x_21 = lean_array_uget(x_4, x_6);
if (lean_obj_tag(x_21) == 0)
{
lean_dec(x_20);
x_10 = x_19;
x_11 = x_9;
goto block_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_138; uint8_t x_139; lean_object* x_205; uint8_t x_206; lean_object* x_209; lean_object* x_216; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_25 = x_19;
} else {
 lean_dec_ref(x_19);
 x_25 = lean_box(0);
}
lean_inc(x_24);
x_117 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_117, 0, x_24);
x_216 = lean_ctor_get(x_22, 1);
lean_inc(x_216);
x_209 = x_216;
goto block_215;
block_27:
{
lean_object* x_26; 
if (lean_is_scalar(x_25)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_25;
}
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
x_10 = x_26;
x_11 = x_9;
goto block_16;
}
block_35:
{
if (x_29 == 0)
{
lean_object* x_31; 
lean_dec(x_28);
if (lean_is_scalar(x_20)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_20;
}
lean_ctor_set(x_31, 0, x_23);
lean_ctor_set(x_31, 1, x_24);
x_10 = x_31;
x_11 = x_30;
goto block_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_inc(x_28);
x_32 = l_Lean_FVarIdSet_insert(x_23, x_28);
x_33 = l_Lean_FVarIdSet_insert(x_24, x_28);
if (lean_is_scalar(x_20)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_20;
}
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_10 = x_34;
x_11 = x_30;
goto block_16;
}
}
block_54:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_st_ref_take(x_8, x_36);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_41, 0);
lean_dec(x_44);
lean_ctor_set(x_41, 0, x_39);
x_45 = lean_st_ref_set(x_8, x_41, x_42);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec_ref(x_45);
x_28 = x_37;
x_29 = x_38;
x_30 = x_46;
goto block_35;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_41, 1);
x_48 = lean_ctor_get(x_41, 2);
x_49 = lean_ctor_get(x_41, 3);
x_50 = lean_ctor_get(x_41, 4);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_41);
x_51 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_51, 0, x_39);
lean_ctor_set(x_51, 1, x_47);
lean_ctor_set(x_51, 2, x_48);
lean_ctor_set(x_51, 3, x_49);
lean_ctor_set(x_51, 4, x_50);
x_52 = lean_st_ref_set(x_8, x_51, x_42);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec_ref(x_52);
x_28 = x_37;
x_29 = x_38;
x_30 = x_53;
goto block_35;
}
}
block_62:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
lean_dec_ref(x_57);
x_60 = lean_ctor_get(x_58, 1);
lean_inc_ref(x_60);
lean_dec(x_58);
x_61 = lean_unbox(x_59);
lean_dec(x_59);
x_36 = x_55;
x_37 = x_56;
x_38 = x_61;
x_39 = x_60;
goto block_54;
}
block_82:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc_ref(x_67);
lean_dec_ref(x_66);
x_68 = lean_st_ref_take(x_8, x_63);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec_ref(x_68);
x_71 = !lean_is_exclusive(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_69, 0);
lean_dec(x_72);
lean_ctor_set(x_69, 0, x_67);
x_73 = lean_st_ref_set(x_8, x_69, x_70);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec_ref(x_73);
x_28 = x_64;
x_29 = x_65;
x_30 = x_74;
goto block_35;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_75 = lean_ctor_get(x_69, 1);
x_76 = lean_ctor_get(x_69, 2);
x_77 = lean_ctor_get(x_69, 3);
x_78 = lean_ctor_get(x_69, 4);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_69);
x_79 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_79, 0, x_67);
lean_ctor_set(x_79, 1, x_75);
lean_ctor_set(x_79, 2, x_76);
lean_ctor_set(x_79, 3, x_77);
lean_ctor_set(x_79, 4, x_78);
x_80 = lean_st_ref_set(x_8, x_79, x_70);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec_ref(x_80);
x_28 = x_64;
x_29 = x_65;
x_30 = x_81;
goto block_35;
}
}
block_89:
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec_ref(x_85);
x_88 = lean_unbox(x_86);
lean_dec(x_86);
x_63 = x_83;
x_64 = x_84;
x_65 = x_88;
x_66 = x_87;
goto block_82;
}
block_108:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_94 = lean_st_ref_take(x_8, x_90);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec_ref(x_94);
x_97 = !lean_is_exclusive(x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_95, 0);
lean_dec(x_98);
lean_ctor_set(x_95, 0, x_93);
x_99 = lean_st_ref_set(x_8, x_95, x_96);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec_ref(x_99);
x_28 = x_91;
x_29 = x_92;
x_30 = x_100;
goto block_35;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_101 = lean_ctor_get(x_95, 1);
x_102 = lean_ctor_get(x_95, 2);
x_103 = lean_ctor_get(x_95, 3);
x_104 = lean_ctor_get(x_95, 4);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_95);
x_105 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_105, 0, x_93);
lean_ctor_set(x_105, 1, x_101);
lean_ctor_set(x_105, 2, x_102);
lean_ctor_set(x_105, 3, x_103);
lean_ctor_set(x_105, 4, x_104);
x_106 = lean_st_ref_set(x_8, x_105, x_96);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec_ref(x_106);
x_28 = x_91;
x_29 = x_92;
x_30 = x_107;
goto block_35;
}
}
block_116:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
lean_dec_ref(x_111);
x_114 = lean_ctor_get(x_112, 1);
lean_inc_ref(x_114);
lean_dec(x_112);
x_115 = lean_unbox(x_113);
lean_dec(x_113);
x_90 = x_109;
x_91 = x_110;
x_92 = x_115;
x_93 = x_114;
goto block_108;
}
block_128:
{
if (x_122 == 0)
{
uint8_t x_124; 
x_124 = l_Lean_Expr_hasFVar(x_121);
if (x_124 == 0)
{
uint8_t x_125; 
x_125 = l_Lean_Expr_hasMVar(x_121);
if (x_125 == 0)
{
lean_dec_ref(x_121);
lean_dec_ref(x_120);
lean_dec_ref(x_117);
x_63 = x_118;
x_64 = x_119;
x_65 = x_125;
x_66 = x_123;
goto block_82;
}
else
{
lean_object* x_126; 
x_126 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_117, x_120, x_121, x_123);
x_83 = x_118;
x_84 = x_119;
x_85 = x_126;
goto block_89;
}
}
else
{
lean_object* x_127; 
x_127 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_117, x_120, x_121, x_123);
x_83 = x_118;
x_84 = x_119;
x_85 = x_127;
goto block_89;
}
}
else
{
lean_dec_ref(x_121);
lean_dec_ref(x_120);
lean_dec_ref(x_117);
x_63 = x_118;
x_64 = x_119;
x_65 = x_122;
x_66 = x_123;
goto block_82;
}
}
block_137:
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec_ref(x_133);
x_136 = lean_unbox(x_134);
lean_dec(x_134);
x_118 = x_129;
x_119 = x_130;
x_120 = x_131;
x_121 = x_132;
x_122 = x_136;
x_123 = x_135;
goto block_128;
}
block_204:
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_box(x_139);
x_141 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_141, 0, x_140);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_142 = lean_ctor_get(x_22, 3);
lean_inc_ref(x_142);
lean_dec_ref(x_22);
x_143 = lean_st_ref_get(x_8, x_9);
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_145 = lean_ctor_get(x_143, 0);
x_146 = lean_ctor_get(x_143, 1);
x_147 = lean_ctor_get(x_145, 0);
lean_inc_ref(x_147);
lean_dec(x_145);
x_148 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
lean_inc_ref(x_147);
lean_ctor_set(x_143, 1, x_147);
lean_ctor_set(x_143, 0, x_148);
x_149 = l_Lean_Expr_hasFVar(x_142);
if (x_149 == 0)
{
uint8_t x_150; 
x_150 = l_Lean_Expr_hasMVar(x_142);
if (x_150 == 0)
{
lean_dec_ref(x_143);
lean_dec_ref(x_142);
lean_dec_ref(x_141);
lean_dec_ref(x_117);
x_36 = x_146;
x_37 = x_138;
x_38 = x_150;
x_39 = x_147;
goto block_54;
}
else
{
lean_object* x_151; 
lean_dec_ref(x_147);
x_151 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_117, x_141, x_142, x_143);
x_55 = x_146;
x_56 = x_138;
x_57 = x_151;
goto block_62;
}
}
else
{
lean_object* x_152; 
lean_dec_ref(x_147);
x_152 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_117, x_141, x_142, x_143);
x_55 = x_146;
x_56 = x_138;
x_57 = x_152;
goto block_62;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_153 = lean_ctor_get(x_143, 0);
x_154 = lean_ctor_get(x_143, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_143);
x_155 = lean_ctor_get(x_153, 0);
lean_inc_ref(x_155);
lean_dec(x_153);
x_156 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
lean_inc_ref(x_155);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
x_158 = l_Lean_Expr_hasFVar(x_142);
if (x_158 == 0)
{
uint8_t x_159; 
x_159 = l_Lean_Expr_hasMVar(x_142);
if (x_159 == 0)
{
lean_dec_ref(x_157);
lean_dec_ref(x_142);
lean_dec_ref(x_141);
lean_dec_ref(x_117);
x_36 = x_154;
x_37 = x_138;
x_38 = x_159;
x_39 = x_155;
goto block_54;
}
else
{
lean_object* x_160; 
lean_dec_ref(x_155);
x_160 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_117, x_141, x_142, x_157);
x_55 = x_154;
x_56 = x_138;
x_57 = x_160;
goto block_62;
}
}
else
{
lean_object* x_161; 
lean_dec_ref(x_155);
x_161 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_117, x_141, x_142, x_157);
x_55 = x_154;
x_56 = x_138;
x_57 = x_161;
goto block_62;
}
}
}
else
{
uint8_t x_162; 
x_162 = lean_ctor_get_uint8(x_22, sizeof(void*)*5);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_163 = lean_ctor_get(x_22, 3);
lean_inc_ref(x_163);
x_164 = lean_ctor_get(x_22, 4);
lean_inc_ref(x_164);
lean_dec_ref(x_22);
x_165 = lean_st_ref_get(x_8, x_9);
x_166 = !lean_is_exclusive(x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_167 = lean_ctor_get(x_165, 0);
x_168 = lean_ctor_get(x_165, 1);
x_169 = lean_ctor_get(x_167, 0);
lean_inc_ref(x_169);
lean_dec(x_167);
x_170 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
lean_ctor_set(x_165, 1, x_169);
lean_ctor_set(x_165, 0, x_170);
x_171 = l_Lean_Expr_hasFVar(x_163);
if (x_171 == 0)
{
uint8_t x_172; 
x_172 = l_Lean_Expr_hasMVar(x_163);
if (x_172 == 0)
{
lean_dec_ref(x_163);
x_118 = x_168;
x_119 = x_138;
x_120 = x_141;
x_121 = x_164;
x_122 = x_172;
x_123 = x_165;
goto block_128;
}
else
{
lean_object* x_173; 
lean_inc_ref(x_141);
lean_inc_ref(x_117);
x_173 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_117, x_141, x_163, x_165);
x_129 = x_168;
x_130 = x_138;
x_131 = x_141;
x_132 = x_164;
x_133 = x_173;
goto block_137;
}
}
else
{
lean_object* x_174; 
lean_inc_ref(x_141);
lean_inc_ref(x_117);
x_174 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_117, x_141, x_163, x_165);
x_129 = x_168;
x_130 = x_138;
x_131 = x_141;
x_132 = x_164;
x_133 = x_174;
goto block_137;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_175 = lean_ctor_get(x_165, 0);
x_176 = lean_ctor_get(x_165, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_165);
x_177 = lean_ctor_get(x_175, 0);
lean_inc_ref(x_177);
lean_dec(x_175);
x_178 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_177);
x_180 = l_Lean_Expr_hasFVar(x_163);
if (x_180 == 0)
{
uint8_t x_181; 
x_181 = l_Lean_Expr_hasMVar(x_163);
if (x_181 == 0)
{
lean_dec_ref(x_163);
x_118 = x_176;
x_119 = x_138;
x_120 = x_141;
x_121 = x_164;
x_122 = x_181;
x_123 = x_179;
goto block_128;
}
else
{
lean_object* x_182; 
lean_inc_ref(x_141);
lean_inc_ref(x_117);
x_182 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_117, x_141, x_163, x_179);
x_129 = x_176;
x_130 = x_138;
x_131 = x_141;
x_132 = x_164;
x_133 = x_182;
goto block_137;
}
}
else
{
lean_object* x_183; 
lean_inc_ref(x_141);
lean_inc_ref(x_117);
x_183 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_117, x_141, x_163, x_179);
x_129 = x_176;
x_130 = x_138;
x_131 = x_141;
x_132 = x_164;
x_133 = x_183;
goto block_137;
}
}
}
else
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_184 = lean_ctor_get(x_22, 3);
lean_inc_ref(x_184);
lean_dec_ref(x_22);
x_185 = lean_st_ref_get(x_8, x_9);
x_186 = !lean_is_exclusive(x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_187 = lean_ctor_get(x_185, 0);
x_188 = lean_ctor_get(x_185, 1);
x_189 = lean_ctor_get(x_187, 0);
lean_inc_ref(x_189);
lean_dec(x_187);
x_190 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
lean_inc_ref(x_189);
lean_ctor_set(x_185, 1, x_189);
lean_ctor_set(x_185, 0, x_190);
x_191 = l_Lean_Expr_hasFVar(x_184);
if (x_191 == 0)
{
uint8_t x_192; 
x_192 = l_Lean_Expr_hasMVar(x_184);
if (x_192 == 0)
{
lean_dec_ref(x_185);
lean_dec_ref(x_184);
lean_dec_ref(x_141);
lean_dec_ref(x_117);
x_90 = x_188;
x_91 = x_138;
x_92 = x_192;
x_93 = x_189;
goto block_108;
}
else
{
lean_object* x_193; 
lean_dec_ref(x_189);
x_193 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_117, x_141, x_184, x_185);
x_109 = x_188;
x_110 = x_138;
x_111 = x_193;
goto block_116;
}
}
else
{
lean_object* x_194; 
lean_dec_ref(x_189);
x_194 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_117, x_141, x_184, x_185);
x_109 = x_188;
x_110 = x_138;
x_111 = x_194;
goto block_116;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_195 = lean_ctor_get(x_185, 0);
x_196 = lean_ctor_get(x_185, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_185);
x_197 = lean_ctor_get(x_195, 0);
lean_inc_ref(x_197);
lean_dec(x_195);
x_198 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
lean_inc_ref(x_197);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_197);
x_200 = l_Lean_Expr_hasFVar(x_184);
if (x_200 == 0)
{
uint8_t x_201; 
x_201 = l_Lean_Expr_hasMVar(x_184);
if (x_201 == 0)
{
lean_dec_ref(x_199);
lean_dec_ref(x_184);
lean_dec_ref(x_141);
lean_dec_ref(x_117);
x_90 = x_196;
x_91 = x_138;
x_92 = x_201;
x_93 = x_197;
goto block_108;
}
else
{
lean_object* x_202; 
lean_dec_ref(x_197);
x_202 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_117, x_141, x_184, x_199);
x_109 = x_196;
x_110 = x_138;
x_111 = x_202;
goto block_116;
}
}
else
{
lean_object* x_203; 
lean_dec_ref(x_197);
x_203 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_117, x_141, x_184, x_199);
x_109 = x_196;
x_110 = x_138;
x_111 = x_203;
goto block_116;
}
}
}
}
}
block_208:
{
if (x_206 == 0)
{
if (x_2 == 0)
{
lean_dec(x_25);
x_138 = x_205;
x_139 = x_2;
goto block_204;
}
else
{
uint8_t x_207; 
x_207 = l_Lean_LocalDecl_isLet(x_22, x_206);
if (x_207 == 0)
{
lean_dec(x_25);
x_138 = x_205;
x_139 = x_207;
goto block_204;
}
else
{
lean_dec(x_205);
lean_dec_ref(x_117);
lean_dec(x_22);
lean_dec(x_20);
goto block_27;
}
}
}
else
{
lean_dec(x_205);
lean_dec_ref(x_117);
lean_dec(x_22);
lean_dec(x_20);
goto block_27;
}
}
block_215:
{
uint8_t x_210; 
x_210 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_209, x_3);
if (x_210 == 0)
{
uint8_t x_211; 
x_211 = l_Lean_LocalDecl_isAuxDecl(x_22);
if (x_211 == 0)
{
uint8_t x_212; uint8_t x_213; 
x_212 = l_Lean_LocalDecl_binderInfo(x_22);
x_213 = l_Lean_BinderInfo_isInstImplicit(x_212);
x_205 = x_209;
x_206 = x_213;
goto block_208;
}
else
{
x_205 = x_209;
x_206 = x_211;
goto block_208;
}
}
else
{
lean_object* x_214; 
lean_dec(x_209);
lean_dec_ref(x_117);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_20);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_23);
lean_ctor_set(x_214, 1, x_24);
x_10 = x_214;
x_11 = x_9;
goto block_16;
}
}
}
}
block_16:
{
lean_object* x_12; size_t x_13; size_t x_14; 
lean_inc(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_10);
x_13 = 1;
x_14 = lean_usize_add(x_6, x_13);
x_6 = x_14;
x_7 = x_12;
x_9 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_20; 
x_20 = lean_usize_dec_lt(x_6, x_5);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_3);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_23 = x_7;
} else {
 lean_dec_ref(x_7);
 x_23 = lean_box(0);
}
x_24 = lean_array_uget(x_4, x_6);
if (lean_obj_tag(x_24) == 0)
{
lean_dec(x_23);
x_13 = x_22;
x_14 = x_12;
goto block_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_141; uint8_t x_142; lean_object* x_208; uint8_t x_209; lean_object* x_212; lean_object* x_219; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_28 = x_22;
} else {
 lean_dec_ref(x_22);
 x_28 = lean_box(0);
}
lean_inc(x_27);
x_120 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_120, 0, x_27);
x_219 = lean_ctor_get(x_25, 1);
lean_inc(x_219);
x_212 = x_219;
goto block_218;
block_30:
{
lean_object* x_29; 
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
x_13 = x_29;
x_14 = x_12;
goto block_19;
}
block_38:
{
if (x_32 == 0)
{
lean_object* x_34; 
lean_dec(x_31);
if (lean_is_scalar(x_23)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_23;
}
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_27);
x_13 = x_34;
x_14 = x_33;
goto block_19;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_inc(x_31);
x_35 = l_Lean_FVarIdSet_insert(x_26, x_31);
x_36 = l_Lean_FVarIdSet_insert(x_27, x_31);
if (lean_is_scalar(x_23)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_23;
}
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_13 = x_37;
x_14 = x_33;
goto block_19;
}
}
block_57:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_st_ref_take(x_9, x_40);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_44, 0);
lean_dec(x_47);
lean_ctor_set(x_44, 0, x_42);
x_48 = lean_st_ref_set(x_9, x_44, x_45);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec_ref(x_48);
x_31 = x_39;
x_32 = x_41;
x_33 = x_49;
goto block_38;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_44, 1);
x_51 = lean_ctor_get(x_44, 2);
x_52 = lean_ctor_get(x_44, 3);
x_53 = lean_ctor_get(x_44, 4);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_44);
x_54 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_54, 0, x_42);
lean_ctor_set(x_54, 1, x_50);
lean_ctor_set(x_54, 2, x_51);
lean_ctor_set(x_54, 3, x_52);
lean_ctor_set(x_54, 4, x_53);
x_55 = lean_st_ref_set(x_9, x_54, x_45);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec_ref(x_55);
x_31 = x_39;
x_32 = x_41;
x_33 = x_56;
goto block_38;
}
}
block_65:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec_ref(x_60);
x_63 = lean_ctor_get(x_61, 1);
lean_inc_ref(x_63);
lean_dec(x_61);
x_64 = lean_unbox(x_62);
lean_dec(x_62);
x_39 = x_59;
x_40 = x_58;
x_41 = x_64;
x_42 = x_63;
goto block_57;
}
block_85:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc_ref(x_70);
lean_dec_ref(x_69);
x_71 = lean_st_ref_take(x_9, x_66);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec_ref(x_71);
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_72, 0);
lean_dec(x_75);
lean_ctor_set(x_72, 0, x_70);
x_76 = lean_st_ref_set(x_9, x_72, x_73);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec_ref(x_76);
x_31 = x_67;
x_32 = x_68;
x_33 = x_77;
goto block_38;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_78 = lean_ctor_get(x_72, 1);
x_79 = lean_ctor_get(x_72, 2);
x_80 = lean_ctor_get(x_72, 3);
x_81 = lean_ctor_get(x_72, 4);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_72);
x_82 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_82, 0, x_70);
lean_ctor_set(x_82, 1, x_78);
lean_ctor_set(x_82, 2, x_79);
lean_ctor_set(x_82, 3, x_80);
lean_ctor_set(x_82, 4, x_81);
x_83 = lean_st_ref_set(x_9, x_82, x_73);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec_ref(x_83);
x_31 = x_67;
x_32 = x_68;
x_33 = x_84;
goto block_38;
}
}
block_92:
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec_ref(x_88);
x_91 = lean_unbox(x_89);
lean_dec(x_89);
x_66 = x_86;
x_67 = x_87;
x_68 = x_91;
x_69 = x_90;
goto block_85;
}
block_111:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_97 = lean_st_ref_take(x_9, x_94);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec_ref(x_97);
x_100 = !lean_is_exclusive(x_98);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_98, 0);
lean_dec(x_101);
lean_ctor_set(x_98, 0, x_96);
x_102 = lean_st_ref_set(x_9, x_98, x_99);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec_ref(x_102);
x_31 = x_93;
x_32 = x_95;
x_33 = x_103;
goto block_38;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = lean_ctor_get(x_98, 1);
x_105 = lean_ctor_get(x_98, 2);
x_106 = lean_ctor_get(x_98, 3);
x_107 = lean_ctor_get(x_98, 4);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_98);
x_108 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_108, 0, x_96);
lean_ctor_set(x_108, 1, x_104);
lean_ctor_set(x_108, 2, x_105);
lean_ctor_set(x_108, 3, x_106);
lean_ctor_set(x_108, 4, x_107);
x_109 = lean_st_ref_set(x_9, x_108, x_99);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec_ref(x_109);
x_31 = x_93;
x_32 = x_95;
x_33 = x_110;
goto block_38;
}
}
block_119:
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
lean_dec_ref(x_114);
x_117 = lean_ctor_get(x_115, 1);
lean_inc_ref(x_117);
lean_dec(x_115);
x_118 = lean_unbox(x_116);
lean_dec(x_116);
x_93 = x_112;
x_94 = x_113;
x_95 = x_118;
x_96 = x_117;
goto block_111;
}
block_131:
{
if (x_125 == 0)
{
uint8_t x_127; 
x_127 = l_Lean_Expr_hasFVar(x_123);
if (x_127 == 0)
{
uint8_t x_128; 
x_128 = l_Lean_Expr_hasMVar(x_123);
if (x_128 == 0)
{
lean_dec_ref(x_124);
lean_dec_ref(x_123);
lean_dec_ref(x_120);
x_66 = x_121;
x_67 = x_122;
x_68 = x_128;
x_69 = x_126;
goto block_85;
}
else
{
lean_object* x_129; 
x_129 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_120, x_124, x_123, x_126);
x_86 = x_121;
x_87 = x_122;
x_88 = x_129;
goto block_92;
}
}
else
{
lean_object* x_130; 
x_130 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_120, x_124, x_123, x_126);
x_86 = x_121;
x_87 = x_122;
x_88 = x_130;
goto block_92;
}
}
else
{
lean_dec_ref(x_124);
lean_dec_ref(x_123);
lean_dec_ref(x_120);
x_66 = x_121;
x_67 = x_122;
x_68 = x_125;
x_69 = x_126;
goto block_85;
}
}
block_140:
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec_ref(x_136);
x_139 = lean_unbox(x_137);
lean_dec(x_137);
x_121 = x_132;
x_122 = x_133;
x_123 = x_134;
x_124 = x_135;
x_125 = x_139;
x_126 = x_138;
goto block_131;
}
block_207:
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_box(x_142);
x_144 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_144, 0, x_143);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_145 = lean_ctor_get(x_25, 3);
lean_inc_ref(x_145);
lean_dec_ref(x_25);
x_146 = lean_st_ref_get(x_9, x_12);
x_147 = !lean_is_exclusive(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_148 = lean_ctor_get(x_146, 0);
x_149 = lean_ctor_get(x_146, 1);
x_150 = lean_ctor_get(x_148, 0);
lean_inc_ref(x_150);
lean_dec(x_148);
x_151 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
lean_inc_ref(x_150);
lean_ctor_set(x_146, 1, x_150);
lean_ctor_set(x_146, 0, x_151);
x_152 = l_Lean_Expr_hasFVar(x_145);
if (x_152 == 0)
{
uint8_t x_153; 
x_153 = l_Lean_Expr_hasMVar(x_145);
if (x_153 == 0)
{
lean_dec_ref(x_146);
lean_dec_ref(x_145);
lean_dec_ref(x_144);
lean_dec_ref(x_120);
x_39 = x_141;
x_40 = x_149;
x_41 = x_153;
x_42 = x_150;
goto block_57;
}
else
{
lean_object* x_154; 
lean_dec_ref(x_150);
x_154 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_120, x_144, x_145, x_146);
x_58 = x_149;
x_59 = x_141;
x_60 = x_154;
goto block_65;
}
}
else
{
lean_object* x_155; 
lean_dec_ref(x_150);
x_155 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_120, x_144, x_145, x_146);
x_58 = x_149;
x_59 = x_141;
x_60 = x_155;
goto block_65;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_156 = lean_ctor_get(x_146, 0);
x_157 = lean_ctor_get(x_146, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_146);
x_158 = lean_ctor_get(x_156, 0);
lean_inc_ref(x_158);
lean_dec(x_156);
x_159 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
lean_inc_ref(x_158);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
x_161 = l_Lean_Expr_hasFVar(x_145);
if (x_161 == 0)
{
uint8_t x_162; 
x_162 = l_Lean_Expr_hasMVar(x_145);
if (x_162 == 0)
{
lean_dec_ref(x_160);
lean_dec_ref(x_145);
lean_dec_ref(x_144);
lean_dec_ref(x_120);
x_39 = x_141;
x_40 = x_157;
x_41 = x_162;
x_42 = x_158;
goto block_57;
}
else
{
lean_object* x_163; 
lean_dec_ref(x_158);
x_163 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_120, x_144, x_145, x_160);
x_58 = x_157;
x_59 = x_141;
x_60 = x_163;
goto block_65;
}
}
else
{
lean_object* x_164; 
lean_dec_ref(x_158);
x_164 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_120, x_144, x_145, x_160);
x_58 = x_157;
x_59 = x_141;
x_60 = x_164;
goto block_65;
}
}
}
else
{
uint8_t x_165; 
x_165 = lean_ctor_get_uint8(x_25, sizeof(void*)*5);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_166 = lean_ctor_get(x_25, 3);
lean_inc_ref(x_166);
x_167 = lean_ctor_get(x_25, 4);
lean_inc_ref(x_167);
lean_dec_ref(x_25);
x_168 = lean_st_ref_get(x_9, x_12);
x_169 = !lean_is_exclusive(x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_170 = lean_ctor_get(x_168, 0);
x_171 = lean_ctor_get(x_168, 1);
x_172 = lean_ctor_get(x_170, 0);
lean_inc_ref(x_172);
lean_dec(x_170);
x_173 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
lean_ctor_set(x_168, 1, x_172);
lean_ctor_set(x_168, 0, x_173);
x_174 = l_Lean_Expr_hasFVar(x_166);
if (x_174 == 0)
{
uint8_t x_175; 
x_175 = l_Lean_Expr_hasMVar(x_166);
if (x_175 == 0)
{
lean_dec_ref(x_166);
x_121 = x_171;
x_122 = x_141;
x_123 = x_167;
x_124 = x_144;
x_125 = x_175;
x_126 = x_168;
goto block_131;
}
else
{
lean_object* x_176; 
lean_inc_ref(x_144);
lean_inc_ref(x_120);
x_176 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_120, x_144, x_166, x_168);
x_132 = x_171;
x_133 = x_141;
x_134 = x_167;
x_135 = x_144;
x_136 = x_176;
goto block_140;
}
}
else
{
lean_object* x_177; 
lean_inc_ref(x_144);
lean_inc_ref(x_120);
x_177 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_120, x_144, x_166, x_168);
x_132 = x_171;
x_133 = x_141;
x_134 = x_167;
x_135 = x_144;
x_136 = x_177;
goto block_140;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_178 = lean_ctor_get(x_168, 0);
x_179 = lean_ctor_get(x_168, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_168);
x_180 = lean_ctor_get(x_178, 0);
lean_inc_ref(x_180);
lean_dec(x_178);
x_181 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_180);
x_183 = l_Lean_Expr_hasFVar(x_166);
if (x_183 == 0)
{
uint8_t x_184; 
x_184 = l_Lean_Expr_hasMVar(x_166);
if (x_184 == 0)
{
lean_dec_ref(x_166);
x_121 = x_179;
x_122 = x_141;
x_123 = x_167;
x_124 = x_144;
x_125 = x_184;
x_126 = x_182;
goto block_131;
}
else
{
lean_object* x_185; 
lean_inc_ref(x_144);
lean_inc_ref(x_120);
x_185 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_120, x_144, x_166, x_182);
x_132 = x_179;
x_133 = x_141;
x_134 = x_167;
x_135 = x_144;
x_136 = x_185;
goto block_140;
}
}
else
{
lean_object* x_186; 
lean_inc_ref(x_144);
lean_inc_ref(x_120);
x_186 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_120, x_144, x_166, x_182);
x_132 = x_179;
x_133 = x_141;
x_134 = x_167;
x_135 = x_144;
x_136 = x_186;
goto block_140;
}
}
}
else
{
lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_187 = lean_ctor_get(x_25, 3);
lean_inc_ref(x_187);
lean_dec_ref(x_25);
x_188 = lean_st_ref_get(x_9, x_12);
x_189 = !lean_is_exclusive(x_188);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_190 = lean_ctor_get(x_188, 0);
x_191 = lean_ctor_get(x_188, 1);
x_192 = lean_ctor_get(x_190, 0);
lean_inc_ref(x_192);
lean_dec(x_190);
x_193 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
lean_inc_ref(x_192);
lean_ctor_set(x_188, 1, x_192);
lean_ctor_set(x_188, 0, x_193);
x_194 = l_Lean_Expr_hasFVar(x_187);
if (x_194 == 0)
{
uint8_t x_195; 
x_195 = l_Lean_Expr_hasMVar(x_187);
if (x_195 == 0)
{
lean_dec_ref(x_188);
lean_dec_ref(x_187);
lean_dec_ref(x_144);
lean_dec_ref(x_120);
x_93 = x_141;
x_94 = x_191;
x_95 = x_195;
x_96 = x_192;
goto block_111;
}
else
{
lean_object* x_196; 
lean_dec_ref(x_192);
x_196 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_120, x_144, x_187, x_188);
x_112 = x_141;
x_113 = x_191;
x_114 = x_196;
goto block_119;
}
}
else
{
lean_object* x_197; 
lean_dec_ref(x_192);
x_197 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_120, x_144, x_187, x_188);
x_112 = x_141;
x_113 = x_191;
x_114 = x_197;
goto block_119;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_198 = lean_ctor_get(x_188, 0);
x_199 = lean_ctor_get(x_188, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_188);
x_200 = lean_ctor_get(x_198, 0);
lean_inc_ref(x_200);
lean_dec(x_198);
x_201 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
lean_inc_ref(x_200);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_200);
x_203 = l_Lean_Expr_hasFVar(x_187);
if (x_203 == 0)
{
uint8_t x_204; 
x_204 = l_Lean_Expr_hasMVar(x_187);
if (x_204 == 0)
{
lean_dec_ref(x_202);
lean_dec_ref(x_187);
lean_dec_ref(x_144);
lean_dec_ref(x_120);
x_93 = x_141;
x_94 = x_199;
x_95 = x_204;
x_96 = x_200;
goto block_111;
}
else
{
lean_object* x_205; 
lean_dec_ref(x_200);
x_205 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_120, x_144, x_187, x_202);
x_112 = x_141;
x_113 = x_199;
x_114 = x_205;
goto block_119;
}
}
else
{
lean_object* x_206; 
lean_dec_ref(x_200);
x_206 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_120, x_144, x_187, x_202);
x_112 = x_141;
x_113 = x_199;
x_114 = x_206;
goto block_119;
}
}
}
}
}
block_211:
{
if (x_209 == 0)
{
if (x_1 == 0)
{
lean_dec(x_28);
x_141 = x_208;
x_142 = x_1;
goto block_207;
}
else
{
uint8_t x_210; 
x_210 = l_Lean_LocalDecl_isLet(x_25, x_209);
if (x_210 == 0)
{
lean_dec(x_28);
x_141 = x_208;
x_142 = x_210;
goto block_207;
}
else
{
lean_dec(x_208);
lean_dec_ref(x_120);
lean_dec(x_25);
lean_dec(x_23);
goto block_30;
}
}
}
else
{
lean_dec(x_208);
lean_dec_ref(x_120);
lean_dec(x_25);
lean_dec(x_23);
goto block_30;
}
}
block_218:
{
uint8_t x_213; 
x_213 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_212, x_2);
if (x_213 == 0)
{
uint8_t x_214; 
x_214 = l_Lean_LocalDecl_isAuxDecl(x_25);
if (x_214 == 0)
{
uint8_t x_215; uint8_t x_216; 
x_215 = l_Lean_LocalDecl_binderInfo(x_25);
x_216 = l_Lean_BinderInfo_isInstImplicit(x_215);
x_208 = x_212;
x_209 = x_216;
goto block_211;
}
else
{
x_208 = x_212;
x_209 = x_214;
goto block_211;
}
}
else
{
lean_object* x_217; 
lean_dec(x_212);
lean_dec_ref(x_120);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_23);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_26);
lean_ctor_set(x_217, 1, x_27);
x_13 = x_217;
x_14 = x_12;
goto block_19;
}
}
}
}
block_19:
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
lean_inc(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_13);
x_16 = 1;
x_17 = lean_usize_add(x_6, x_16);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4___redArg(x_3, x_1, x_2, x_4, x_5, x_17, x_15, x_9, x_14);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_3);
lean_inc_ref(x_4);
x_12 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(x_1, x_2, x_4, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec_ref(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec_ref(x_13);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec_ref(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec_ref(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec_ref(x_13);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_array_size(x_11);
x_25 = 0;
x_26 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4(x_1, x_2, x_22, x_11, x_24, x_25, x_23, x_5, x_6, x_7, x_8, x_20);
lean_dec_ref(x_11);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
lean_ctor_set(x_26, 0, x_31);
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_27);
x_35 = !lean_is_exclusive(x_26);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_26, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
lean_dec_ref(x_28);
lean_ctor_set(x_26, 0, x_37);
return x_26;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_dec(x_26);
x_39 = lean_ctor_get(x_28, 0);
lean_inc(x_39);
lean_dec_ref(x_28);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_getFVarSetToGeneralize_spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = l_Lean_Expr_isFVar(x_11);
if (x_12 == 0)
{
lean_dec_ref(x_11);
x_5 = x_4;
goto block_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Expr_fvarId_x21(x_11);
lean_dec_ref(x_11);
x_14 = l_Lean_FVarIdSet_insert(x_4, x_13);
x_5 = x_14;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_9 = lean_box(1);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_array_get_size(x_1);
x_25 = lean_nat_dec_lt(x_23, x_24);
if (x_25 == 0)
{
lean_dec(x_24);
x_10 = x_9;
goto block_22;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_24, x_24);
if (x_26 == 0)
{
lean_dec(x_24);
x_10 = x_9;
goto block_22;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
x_27 = 0;
x_28 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_29 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_getFVarSetToGeneralize_spec__7(x_1, x_27, x_28, x_9);
x_10 = x_29;
goto block_22;
}
}
block_22:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_10);
x_14 = l_Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0(x_3, x_2, x_12, x_13, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_4);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 0);
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
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_1);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__0(x_14, x_2, x_3, x_4, x_5, x_15, x_16, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_2);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg(x_1, x_10, x_3, x_4, x_11, x_12, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_2);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1(x_1, x_13, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_1);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(x_13, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_2);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4___redArg(x_1, x_10, x_3, x_4, x_11, x_12, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_2);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4(x_1, x_13, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_1);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4(x_13, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
x_11 = l_Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_getFVarSetToGeneralize_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_getFVarSetToGeneralize_spec__7(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_getFVarSetToGeneralize(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 3);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 4);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(x_1, x_4);
x_7 = lean_array_push(x_6, x_3);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___Lean_Meta_getFVarsToGeneralize_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_9 = l_Lean_Meta_mkGeneralizationForbiddenSet(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
lean_inc_ref(x_4);
x_12 = l_Lean_Meta_getFVarSetToGeneralize(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
x_15 = x_20;
goto block_19;
}
else
{
lean_object* x_21; 
x_21 = lean_unsigned_to_nat(0u);
x_15 = x_21;
goto block_19;
}
block_19:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_mk_empty_array_with_capacity(x_15);
lean_dec(x_15);
x_17 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(x_16, x_13);
x_18 = l_Lean_Meta_sortFVarIds___redArg(x_17, x_4, x_14);
return x_18;
}
}
else
{
uint8_t x_22; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_22 = !lean_is_exclusive(x_9);
if (x_22 == 0)
{
return x_9;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_getFVarsToGeneralize(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_10;
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_CollectFVars(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_GeneralizeVars(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectFVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0 = _init_l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0();
lean_mark_persistent(l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0);
l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1 = _init_l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1();
lean_mark_persistent(l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2 = _init_l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2();
lean_mark_persistent(l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2);
l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3 = _init_l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3();
lean_mark_persistent(l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3);
l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4 = _init_l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4();
lean_mark_persistent(l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4);
l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__5 = _init_l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__5();
lean_mark_persistent(l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__5);
l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__6 = _init_l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__6();
lean_mark_persistent(l_Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__6);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
