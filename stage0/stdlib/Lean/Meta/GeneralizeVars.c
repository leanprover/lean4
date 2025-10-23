// Lean compiler output
// Module: Lean.Meta.GeneralizeVars
// Imports: public import Lean.Meta.Basic public import Lean.Util.CollectFVars
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__6;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
static lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Meta_getFVarSetToGeneralize_spec__7(lean_object*, size_t, size_t, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2;
uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Meta_getFVarSetToGeneralize_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Meta_sortFVarIds___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___Lean_Meta_getFVarsToGeneralize_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__1(uint8_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1___redArg(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1___redArg(x_1, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_4, x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_inc(x_4);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_FVarIdSet_insert(x_11, x_4);
lean_ctor_set(x_9, 1, x_14);
lean_ctor_set(x_9, 0, x_15);
x_1 = x_9;
x_2 = x_6;
goto _start;
}
else
{
lean_dec(x_4);
x_1 = x_9;
x_2 = x_6;
goto _start;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_4, x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc(x_4);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_FVarIdSet_insert(x_18, x_4);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_1 = x_23;
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_25; 
lean_dec(x_4);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_19);
x_1 = x_25;
x_2 = x_6;
goto _start;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_1);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1___redArg(x_1, x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1___redArg(x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_8, x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_8);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_FVarIdSet_insert(x_15, x_8);
lean_ctor_set(x_13, 1, x_18);
lean_ctor_set(x_13, 0, x_19);
x_20 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1___redArg(x_13, x_10);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_8);
x_21 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1___redArg(x_13, x_10);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_8, x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_inc(x_8);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_8);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_FVarIdSet_insert(x_22, x_8);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1___redArg(x_27, x_10);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_23);
x_30 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1___redArg(x_29, x_10);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_1);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3___redArg(x_1, x_3);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__5;
x_2 = lean_box(1);
x_3 = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_32; 
lean_inc_ref(x_4);
x_32 = l_Lean_FVarId_getDecl___redArg(x_1, x_4, x_6, x_7);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = l_Lean_LocalDecl_type(x_33);
x_35 = l_Lean_instantiateMVars___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3___redArg(x_34, x_5);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__6;
x_38 = l_Lean_collectFVars(x_37, x_36);
x_39 = 0;
x_40 = l_Lean_LocalDecl_value_x3f(x_33, x_39);
lean_dec(x_33);
if (lean_obj_tag(x_40) == 0)
{
x_20 = x_38;
x_21 = x_4;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = lean_box(0);
goto block_31;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = l_Lean_instantiateMVars___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3___redArg(x_41, x_5);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = l_Lean_collectFVars(x_38, x_43);
x_20 = x_44;
x_21 = x_4;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = lean_box(0);
goto block_31;
}
}
else
{
uint8_t x_45; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_32);
if (x_45 == 0)
{
return x_32;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_32, 0);
lean_inc(x_46);
lean_dec(x_32);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
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
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_9);
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
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
block_31:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec_ref(x_20);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_2);
x_28 = l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1(x_27, x_26, x_21, x_22, x_23, x_24);
lean_dec_ref(x_21);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_9 = x_30;
x_10 = lean_box(0);
goto block_19;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; 
lean_dec_ref(x_3);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_2);
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
x_11 = l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_9, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_9);
x_12 = l_Lean_FVarIdSet_insert(x_2, x_9);
lean_inc_ref(x_3);
x_13 = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit(x_9, x_10, x_12, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_1 = x_15;
x_2 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec_ref(x_3);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_4);
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
x_23 = lean_infer_type(x_21, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = l_Lean_instantiateMVars___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3___redArg(x_24, x_6);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = l_Lean_collectFVars(x_19, x_26);
lean_ctor_set(x_4, 0, x_27);
x_10 = x_4;
x_11 = lean_box(0);
goto block_15;
}
else
{
uint8_t x_28; 
lean_free_object(x_4);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_Expr_fvarId_x21(x_21);
lean_dec_ref(x_21);
x_32 = lean_array_push(x_20, x_31);
lean_ctor_set(x_4, 1, x_32);
x_10 = x_4;
x_11 = lean_box(0);
goto block_15;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_4, 0);
x_34 = lean_ctor_get(x_4, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_4);
x_35 = lean_array_uget(x_1, x_3);
x_36 = l_Lean_Expr_isFVar(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_37 = lean_infer_type(x_35, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = l_Lean_instantiateMVars___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3___redArg(x_38, x_6);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = l_Lean_collectFVars(x_33, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_34);
x_10 = x_42;
x_11 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_44 = x_37;
} else {
 lean_dec_ref(x_37);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 1, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = l_Lean_Expr_fvarId_x21(x_35);
lean_dec_ref(x_35);
x_47 = lean_array_push(x_34, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_33);
lean_ctor_set(x_48, 1, x_47);
x_10 = x_48;
x_11 = lean_box(0);
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
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_4);
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
x_23 = lean_infer_type(x_21, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = l_Lean_instantiateMVars___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3___redArg(x_24, x_6);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = l_Lean_collectFVars(x_19, x_26);
lean_ctor_set(x_4, 0, x_27);
x_10 = x_4;
x_11 = lean_box(0);
goto block_15;
}
else
{
uint8_t x_28; 
lean_free_object(x_4);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_Expr_fvarId_x21(x_21);
lean_dec_ref(x_21);
x_32 = lean_array_push(x_20, x_31);
lean_ctor_set(x_4, 1, x_32);
x_10 = x_4;
x_11 = lean_box(0);
goto block_15;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_4, 0);
x_34 = lean_ctor_get(x_4, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_4);
x_35 = lean_array_uget(x_1, x_3);
x_36 = l_Lean_Expr_isFVar(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_37 = lean_infer_type(x_35, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = l_Lean_instantiateMVars___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__3___redArg(x_38, x_6);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = l_Lean_collectFVars(x_33, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_34);
x_10 = x_42;
x_11 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_44 = x_37;
} else {
 lean_dec_ref(x_37);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 1, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = l_Lean_Expr_fvarId_x21(x_35);
lean_dec_ref(x_35);
x_47 = lean_array_push(x_34, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_33);
lean_ctor_set(x_48, 1, x_47);
x_10 = x_48;
x_11 = lean_box(0);
goto block_15;
}
}
}
block_15:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0_spec__0(x_1, x_2, x_13, x_10, x_5, x_6, x_7, x_8);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_8 = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
x_9 = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__5;
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
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0(x_1, x_12, x_13, x_11, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_array_to_list(x_17);
x_20 = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop(x_19, x_18, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkGeneralizationForbiddenSet(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_7, x_6);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_4);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_8);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_8, 1);
x_18 = lean_ctor_get(x_8, 0);
lean_dec(x_18);
x_19 = lean_array_uget(x_5, x_7);
lean_inc(x_17);
x_20 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(x_1, x_2, x_3, x_19, x_17, x_9, x_10, x_11, x_12);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec(x_4);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_8, 0, x_23);
lean_ctor_set(x_20, 0, x_8);
return x_20;
}
else
{
lean_object* x_24; size_t x_25; size_t x_26; 
lean_free_object(x_20);
lean_dec(x_17);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec_ref(x_22);
lean_inc(x_4);
lean_ctor_set(x_8, 1, x_24);
lean_ctor_set(x_8, 0, x_4);
x_25 = 1;
x_26 = lean_usize_add(x_7, x_25);
x_7 = x_26;
goto _start;
}
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_4);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_8, 0, x_29);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_8);
return x_30;
}
else
{
lean_object* x_31; size_t x_32; size_t x_33; 
lean_dec(x_17);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec_ref(x_28);
lean_inc(x_4);
lean_ctor_set(x_8, 1, x_31);
lean_ctor_set(x_8, 0, x_4);
x_32 = 1;
x_33 = lean_usize_add(x_7, x_32);
x_7 = x_33;
goto _start;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
lean_dec(x_8);
x_36 = lean_array_uget(x_5, x_7);
lean_inc(x_35);
x_37 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(x_1, x_2, x_3, x_36, x_35, x_9, x_10, x_11, x_12);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_4);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_35);
if (lean_is_scalar(x_39)) {
 x_42 = lean_alloc_ctor(0, 1, 0);
} else {
 x_42 = x_39;
}
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; 
lean_dec(x_39);
lean_dec(x_35);
x_43 = lean_ctor_get(x_38, 0);
lean_inc(x_43);
lean_dec_ref(x_38);
lean_inc(x_4);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_43);
x_45 = 1;
x_46 = lean_usize_add(x_7, x_45);
x_7 = x_46;
x_8 = x_44;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_6, x_5);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_7);
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
x_11 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_50; lean_object* x_51; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_72; lean_object* x_73; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_92; lean_object* x_93; uint8_t x_99; 
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
x_28 = l_Lean_LocalDecl_fvarId(x_22);
x_99 = l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_28, x_3);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_119; uint8_t x_152; uint8_t x_155; 
lean_inc(x_24);
x_100 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_100, 0, x_24);
x_155 = l_Lean_LocalDecl_isAuxDecl(x_22);
if (x_155 == 0)
{
uint8_t x_156; uint8_t x_157; 
x_156 = l_Lean_LocalDecl_binderInfo(x_22);
x_157 = l_Lean_BinderInfo_isInstImplicit(x_156);
x_152 = x_157;
goto block_154;
}
else
{
x_152 = x_155;
goto block_154;
}
block_110:
{
if (x_104 == 0)
{
uint8_t x_106; 
x_106 = l_Lean_Expr_hasFVar(x_101);
if (x_106 == 0)
{
uint8_t x_107; 
x_107 = l_Lean_Expr_hasMVar(x_101);
if (x_107 == 0)
{
lean_dec_ref(x_102);
lean_dec_ref(x_101);
lean_dec_ref(x_100);
x_57 = lean_box(0);
x_58 = x_107;
x_59 = x_105;
goto block_71;
}
else
{
lean_object* x_108; 
x_108 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_100, x_102, x_101, x_105);
x_72 = lean_box(0);
x_73 = x_108;
goto block_77;
}
}
else
{
lean_object* x_109; 
x_109 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_100, x_102, x_101, x_105);
x_72 = lean_box(0);
x_73 = x_109;
goto block_77;
}
}
else
{
lean_dec_ref(x_102);
lean_dec_ref(x_101);
lean_dec_ref(x_100);
x_57 = lean_box(0);
x_58 = x_104;
x_59 = x_105;
goto block_71;
}
}
block_118:
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec_ref(x_114);
x_117 = lean_unbox(x_115);
lean_dec(x_115);
x_101 = x_111;
x_102 = x_112;
x_103 = lean_box(0);
x_104 = x_117;
x_105 = x_116;
goto block_110;
}
block_151:
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_box(x_119);
x_121 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_121, 0, x_120);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_122 = lean_ctor_get(x_22, 3);
lean_inc_ref(x_122);
lean_dec_ref(x_22);
x_123 = lean_st_ref_get(x_8);
x_124 = lean_ctor_get(x_123, 0);
lean_inc_ref(x_124);
lean_dec_ref(x_123);
x_125 = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
lean_inc_ref(x_124);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
x_127 = l_Lean_Expr_hasFVar(x_122);
if (x_127 == 0)
{
uint8_t x_128; 
x_128 = l_Lean_Expr_hasMVar(x_122);
if (x_128 == 0)
{
lean_dec_ref(x_126);
lean_dec_ref(x_122);
lean_dec_ref(x_121);
lean_dec_ref(x_100);
x_36 = lean_box(0);
x_37 = x_128;
x_38 = x_124;
goto block_49;
}
else
{
lean_object* x_129; 
lean_dec_ref(x_124);
x_129 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_100, x_121, x_122, x_126);
x_50 = lean_box(0);
x_51 = x_129;
goto block_56;
}
}
else
{
lean_object* x_130; 
lean_dec_ref(x_124);
x_130 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_100, x_121, x_122, x_126);
x_50 = lean_box(0);
x_51 = x_130;
goto block_56;
}
}
else
{
uint8_t x_131; 
x_131 = lean_ctor_get_uint8(x_22, sizeof(void*)*5);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_132 = lean_ctor_get(x_22, 3);
lean_inc_ref(x_132);
x_133 = lean_ctor_get(x_22, 4);
lean_inc_ref(x_133);
lean_dec_ref(x_22);
x_134 = lean_st_ref_get(x_8);
x_135 = lean_ctor_get(x_134, 0);
lean_inc_ref(x_135);
lean_dec_ref(x_134);
x_136 = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
x_138 = l_Lean_Expr_hasFVar(x_132);
if (x_138 == 0)
{
uint8_t x_139; 
x_139 = l_Lean_Expr_hasMVar(x_132);
if (x_139 == 0)
{
lean_dec_ref(x_132);
x_101 = x_133;
x_102 = x_121;
x_103 = lean_box(0);
x_104 = x_139;
x_105 = x_137;
goto block_110;
}
else
{
lean_object* x_140; 
lean_inc_ref(x_121);
lean_inc_ref(x_100);
x_140 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_100, x_121, x_132, x_137);
x_111 = x_133;
x_112 = x_121;
x_113 = lean_box(0);
x_114 = x_140;
goto block_118;
}
}
else
{
lean_object* x_141; 
lean_inc_ref(x_121);
lean_inc_ref(x_100);
x_141 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_100, x_121, x_132, x_137);
x_111 = x_133;
x_112 = x_121;
x_113 = lean_box(0);
x_114 = x_141;
goto block_118;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_142 = lean_ctor_get(x_22, 3);
lean_inc_ref(x_142);
lean_dec_ref(x_22);
x_143 = lean_st_ref_get(x_8);
x_144 = lean_ctor_get(x_143, 0);
lean_inc_ref(x_144);
lean_dec_ref(x_143);
x_145 = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
lean_inc_ref(x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
x_147 = l_Lean_Expr_hasFVar(x_142);
if (x_147 == 0)
{
uint8_t x_148; 
x_148 = l_Lean_Expr_hasMVar(x_142);
if (x_148 == 0)
{
lean_dec_ref(x_146);
lean_dec_ref(x_142);
lean_dec_ref(x_121);
lean_dec_ref(x_100);
x_78 = lean_box(0);
x_79 = x_148;
x_80 = x_144;
goto block_91;
}
else
{
lean_object* x_149; 
lean_dec_ref(x_144);
x_149 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_100, x_121, x_142, x_146);
x_92 = lean_box(0);
x_93 = x_149;
goto block_98;
}
}
else
{
lean_object* x_150; 
lean_dec_ref(x_144);
x_150 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_100, x_121, x_142, x_146);
x_92 = lean_box(0);
x_93 = x_150;
goto block_98;
}
}
}
}
block_154:
{
if (x_152 == 0)
{
if (x_2 == 0)
{
lean_dec(x_25);
x_119 = x_2;
goto block_151;
}
else
{
uint8_t x_153; 
x_153 = l_Lean_LocalDecl_isLet(x_22, x_152);
if (x_153 == 0)
{
lean_dec(x_25);
x_119 = x_153;
goto block_151;
}
else
{
lean_dec_ref(x_100);
lean_dec(x_28);
lean_dec(x_22);
lean_dec(x_20);
goto block_27;
}
}
}
else
{
lean_dec_ref(x_100);
lean_dec(x_28);
lean_dec(x_22);
lean_dec(x_20);
goto block_27;
}
}
}
else
{
lean_object* x_158; 
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_20);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_23);
lean_ctor_set(x_158, 1, x_24);
x_10 = x_158;
x_11 = lean_box(0);
goto block_16;
}
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
x_11 = lean_box(0);
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
x_11 = lean_box(0);
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
x_11 = lean_box(0);
goto block_16;
}
}
block_49:
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_st_ref_take(x_8);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_38);
x_42 = lean_st_ref_set(x_8, x_39);
x_29 = x_37;
x_30 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_39, 1);
x_44 = lean_ctor_get(x_39, 2);
x_45 = lean_ctor_get(x_39, 3);
x_46 = lean_ctor_get(x_39, 4);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_39);
x_47 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_43);
lean_ctor_set(x_47, 2, x_44);
lean_ctor_set(x_47, 3, x_45);
lean_ctor_set(x_47, 4, x_46);
x_48 = lean_st_ref_set(x_8, x_47);
x_29 = x_37;
x_30 = lean_box(0);
goto block_35;
}
}
block_56:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
lean_dec_ref(x_51);
x_54 = lean_ctor_get(x_52, 1);
lean_inc_ref(x_54);
lean_dec(x_52);
x_55 = lean_unbox(x_53);
lean_dec(x_53);
x_36 = lean_box(0);
x_37 = x_55;
x_38 = x_54;
goto block_49;
}
block_71:
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_59, 1);
lean_inc_ref(x_60);
lean_dec_ref(x_59);
x_61 = lean_st_ref_take(x_8);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_61, 0);
lean_dec(x_63);
lean_ctor_set(x_61, 0, x_60);
x_64 = lean_st_ref_set(x_8, x_61);
x_29 = x_58;
x_30 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_61, 1);
x_66 = lean_ctor_get(x_61, 2);
x_67 = lean_ctor_get(x_61, 3);
x_68 = lean_ctor_get(x_61, 4);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_61);
x_69 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_69, 0, x_60);
lean_ctor_set(x_69, 1, x_65);
lean_ctor_set(x_69, 2, x_66);
lean_ctor_set(x_69, 3, x_67);
lean_ctor_set(x_69, 4, x_68);
x_70 = lean_st_ref_set(x_8, x_69);
x_29 = x_58;
x_30 = lean_box(0);
goto block_35;
}
}
block_77:
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec_ref(x_73);
x_76 = lean_unbox(x_74);
lean_dec(x_74);
x_57 = lean_box(0);
x_58 = x_76;
x_59 = x_75;
goto block_71;
}
block_91:
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_st_ref_take(x_8);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_81, 0);
lean_dec(x_83);
lean_ctor_set(x_81, 0, x_80);
x_84 = lean_st_ref_set(x_8, x_81);
x_29 = x_79;
x_30 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_85 = lean_ctor_get(x_81, 1);
x_86 = lean_ctor_get(x_81, 2);
x_87 = lean_ctor_get(x_81, 3);
x_88 = lean_ctor_get(x_81, 4);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_81);
x_89 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_89, 0, x_80);
lean_ctor_set(x_89, 1, x_85);
lean_ctor_set(x_89, 2, x_86);
lean_ctor_set(x_89, 3, x_87);
lean_ctor_set(x_89, 4, x_88);
x_90 = lean_st_ref_set(x_8, x_89);
x_29 = x_79;
x_30 = lean_box(0);
goto block_35;
}
}
block_98:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
lean_dec_ref(x_93);
x_96 = lean_ctor_get(x_94, 1);
lean_inc_ref(x_96);
lean_dec(x_94);
x_97 = lean_unbox(x_95);
lean_dec(x_95);
x_78 = lean_box(0);
x_79 = x_97;
x_80 = x_96;
goto block_91;
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
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_20; 
x_20 = lean_usize_dec_lt(x_6, x_5);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_3);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_7);
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
x_14 = lean_box(0);
goto block_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_53; lean_object* x_54; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_75; lean_object* x_76; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_95; lean_object* x_96; uint8_t x_102; 
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
x_31 = l_Lean_LocalDecl_fvarId(x_25);
x_102 = l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_31, x_2);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_122; uint8_t x_155; uint8_t x_158; 
lean_inc(x_27);
x_103 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_103, 0, x_27);
x_158 = l_Lean_LocalDecl_isAuxDecl(x_25);
if (x_158 == 0)
{
uint8_t x_159; uint8_t x_160; 
x_159 = l_Lean_LocalDecl_binderInfo(x_25);
x_160 = l_Lean_BinderInfo_isInstImplicit(x_159);
x_155 = x_160;
goto block_157;
}
else
{
x_155 = x_158;
goto block_157;
}
block_113:
{
if (x_107 == 0)
{
uint8_t x_109; 
x_109 = l_Lean_Expr_hasFVar(x_106);
if (x_109 == 0)
{
uint8_t x_110; 
x_110 = l_Lean_Expr_hasMVar(x_106);
if (x_110 == 0)
{
lean_dec_ref(x_106);
lean_dec_ref(x_104);
lean_dec_ref(x_103);
x_60 = lean_box(0);
x_61 = x_110;
x_62 = x_108;
goto block_74;
}
else
{
lean_object* x_111; 
x_111 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_103, x_104, x_106, x_108);
x_75 = lean_box(0);
x_76 = x_111;
goto block_80;
}
}
else
{
lean_object* x_112; 
x_112 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_103, x_104, x_106, x_108);
x_75 = lean_box(0);
x_76 = x_112;
goto block_80;
}
}
else
{
lean_dec_ref(x_106);
lean_dec_ref(x_104);
lean_dec_ref(x_103);
x_60 = lean_box(0);
x_61 = x_107;
x_62 = x_108;
goto block_74;
}
}
block_121:
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec_ref(x_117);
x_120 = lean_unbox(x_118);
lean_dec(x_118);
x_104 = x_114;
x_105 = lean_box(0);
x_106 = x_116;
x_107 = x_120;
x_108 = x_119;
goto block_113;
}
block_154:
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_box(x_122);
x_124 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_124, 0, x_123);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_125 = lean_ctor_get(x_25, 3);
lean_inc_ref(x_125);
lean_dec_ref(x_25);
x_126 = lean_st_ref_get(x_9);
x_127 = lean_ctor_get(x_126, 0);
lean_inc_ref(x_127);
lean_dec_ref(x_126);
x_128 = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
lean_inc_ref(x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
x_130 = l_Lean_Expr_hasFVar(x_125);
if (x_130 == 0)
{
uint8_t x_131; 
x_131 = l_Lean_Expr_hasMVar(x_125);
if (x_131 == 0)
{
lean_dec_ref(x_129);
lean_dec_ref(x_125);
lean_dec_ref(x_124);
lean_dec_ref(x_103);
x_39 = lean_box(0);
x_40 = x_131;
x_41 = x_127;
goto block_52;
}
else
{
lean_object* x_132; 
lean_dec_ref(x_127);
x_132 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_103, x_124, x_125, x_129);
x_53 = lean_box(0);
x_54 = x_132;
goto block_59;
}
}
else
{
lean_object* x_133; 
lean_dec_ref(x_127);
x_133 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_103, x_124, x_125, x_129);
x_53 = lean_box(0);
x_54 = x_133;
goto block_59;
}
}
else
{
uint8_t x_134; 
x_134 = lean_ctor_get_uint8(x_25, sizeof(void*)*5);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_135 = lean_ctor_get(x_25, 3);
lean_inc_ref(x_135);
x_136 = lean_ctor_get(x_25, 4);
lean_inc_ref(x_136);
lean_dec_ref(x_25);
x_137 = lean_st_ref_get(x_9);
x_138 = lean_ctor_get(x_137, 0);
lean_inc_ref(x_138);
lean_dec_ref(x_137);
x_139 = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
x_141 = l_Lean_Expr_hasFVar(x_135);
if (x_141 == 0)
{
uint8_t x_142; 
x_142 = l_Lean_Expr_hasMVar(x_135);
if (x_142 == 0)
{
lean_dec_ref(x_135);
x_104 = x_124;
x_105 = lean_box(0);
x_106 = x_136;
x_107 = x_142;
x_108 = x_140;
goto block_113;
}
else
{
lean_object* x_143; 
lean_inc_ref(x_124);
lean_inc_ref(x_103);
x_143 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_103, x_124, x_135, x_140);
x_114 = x_124;
x_115 = lean_box(0);
x_116 = x_136;
x_117 = x_143;
goto block_121;
}
}
else
{
lean_object* x_144; 
lean_inc_ref(x_124);
lean_inc_ref(x_103);
x_144 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_103, x_124, x_135, x_140);
x_114 = x_124;
x_115 = lean_box(0);
x_116 = x_136;
x_117 = x_144;
goto block_121;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_145 = lean_ctor_get(x_25, 3);
lean_inc_ref(x_145);
lean_dec_ref(x_25);
x_146 = lean_st_ref_get(x_9);
x_147 = lean_ctor_get(x_146, 0);
lean_inc_ref(x_147);
lean_dec_ref(x_146);
x_148 = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
lean_inc_ref(x_147);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_147);
x_150 = l_Lean_Expr_hasFVar(x_145);
if (x_150 == 0)
{
uint8_t x_151; 
x_151 = l_Lean_Expr_hasMVar(x_145);
if (x_151 == 0)
{
lean_dec_ref(x_149);
lean_dec_ref(x_145);
lean_dec_ref(x_124);
lean_dec_ref(x_103);
x_81 = lean_box(0);
x_82 = x_151;
x_83 = x_147;
goto block_94;
}
else
{
lean_object* x_152; 
lean_dec_ref(x_147);
x_152 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_103, x_124, x_145, x_149);
x_95 = lean_box(0);
x_96 = x_152;
goto block_101;
}
}
else
{
lean_object* x_153; 
lean_dec_ref(x_147);
x_153 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_103, x_124, x_145, x_149);
x_95 = lean_box(0);
x_96 = x_153;
goto block_101;
}
}
}
}
block_157:
{
if (x_155 == 0)
{
if (x_1 == 0)
{
lean_dec(x_28);
x_122 = x_1;
goto block_154;
}
else
{
uint8_t x_156; 
x_156 = l_Lean_LocalDecl_isLet(x_25, x_155);
if (x_156 == 0)
{
lean_dec(x_28);
x_122 = x_156;
goto block_154;
}
else
{
lean_dec_ref(x_103);
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_23);
goto block_30;
}
}
}
else
{
lean_dec_ref(x_103);
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_23);
goto block_30;
}
}
}
else
{
lean_object* x_161; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_23);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_26);
lean_ctor_set(x_161, 1, x_27);
x_13 = x_161;
x_14 = lean_box(0);
goto block_19;
}
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
x_14 = lean_box(0);
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
x_14 = lean_box(0);
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
x_14 = lean_box(0);
goto block_19;
}
}
block_52:
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_st_ref_take(x_9);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
lean_ctor_set(x_42, 0, x_41);
x_45 = lean_st_ref_set(x_9, x_42);
x_32 = x_40;
x_33 = lean_box(0);
goto block_38;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_42, 1);
x_47 = lean_ctor_get(x_42, 2);
x_48 = lean_ctor_get(x_42, 3);
x_49 = lean_ctor_get(x_42, 4);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_42);
x_50 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_50, 0, x_41);
lean_ctor_set(x_50, 1, x_46);
lean_ctor_set(x_50, 2, x_47);
lean_ctor_set(x_50, 3, x_48);
lean_ctor_set(x_50, 4, x_49);
x_51 = lean_st_ref_set(x_9, x_50);
x_32 = x_40;
x_33 = lean_box(0);
goto block_38;
}
}
block_59:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec_ref(x_54);
x_57 = lean_ctor_get(x_55, 1);
lean_inc_ref(x_57);
lean_dec(x_55);
x_58 = lean_unbox(x_56);
lean_dec(x_56);
x_39 = lean_box(0);
x_40 = x_58;
x_41 = x_57;
goto block_52;
}
block_74:
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_63);
lean_dec_ref(x_62);
x_64 = lean_st_ref_take(x_9);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
lean_ctor_set(x_64, 0, x_63);
x_67 = lean_st_ref_set(x_9, x_64);
x_32 = x_61;
x_33 = lean_box(0);
goto block_38;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_64, 1);
x_69 = lean_ctor_get(x_64, 2);
x_70 = lean_ctor_get(x_64, 3);
x_71 = lean_ctor_get(x_64, 4);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_64);
x_72 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_72, 0, x_63);
lean_ctor_set(x_72, 1, x_68);
lean_ctor_set(x_72, 2, x_69);
lean_ctor_set(x_72, 3, x_70);
lean_ctor_set(x_72, 4, x_71);
x_73 = lean_st_ref_set(x_9, x_72);
x_32 = x_61;
x_33 = lean_box(0);
goto block_38;
}
}
block_80:
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec_ref(x_76);
x_79 = lean_unbox(x_77);
lean_dec(x_77);
x_60 = lean_box(0);
x_61 = x_79;
x_62 = x_78;
goto block_74;
}
block_94:
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_st_ref_take(x_9);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_84, 0);
lean_dec(x_86);
lean_ctor_set(x_84, 0, x_83);
x_87 = lean_st_ref_set(x_9, x_84);
x_32 = x_82;
x_33 = lean_box(0);
goto block_38;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_88 = lean_ctor_get(x_84, 1);
x_89 = lean_ctor_get(x_84, 2);
x_90 = lean_ctor_get(x_84, 3);
x_91 = lean_ctor_get(x_84, 4);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_84);
x_92 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_92, 0, x_83);
lean_ctor_set(x_92, 1, x_88);
lean_ctor_set(x_92, 2, x_89);
lean_ctor_set(x_92, 3, x_90);
lean_ctor_set(x_92, 4, x_91);
x_93 = lean_st_ref_set(x_9, x_92);
x_32 = x_82;
x_33 = lean_box(0);
goto block_38;
}
}
block_101:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec_ref(x_96);
x_99 = lean_ctor_get(x_97, 1);
lean_inc_ref(x_99);
lean_dec(x_97);
x_100 = lean_unbox(x_98);
lean_dec(x_98);
x_81 = lean_box(0);
x_82 = x_100;
x_83 = x_99;
goto block_94;
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
x_18 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg(x_3, x_1, x_2, x_4, x_5, x_17, x_15, x_9);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
x_15 = lean_array_size(x_12);
x_16 = 0;
x_17 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_13, x_12, x_15, x_16, x_14, x_6, x_7, x_8, x_9);
lean_dec_ref(x_12);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_19, 0);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_21);
lean_ctor_set(x_17, 0, x_4);
return x_17;
}
else
{
lean_object* x_22; 
lean_inc_ref(x_20);
lean_dec(x_19);
lean_free_object(x_4);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec_ref(x_20);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_ctor_get(x_23, 0);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_25);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_4);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_inc_ref(x_24);
lean_dec(x_23);
lean_free_object(x_4);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec_ref(x_24);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_4, 0);
lean_inc(x_29);
lean_dec(x_4);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_5);
x_32 = lean_array_size(x_29);
x_33 = 0;
x_34 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_30, x_29, x_32, x_33, x_31, x_6, x_7, x_8, x_9);
lean_dec_ref(x_29);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_ctor_get(x_35, 0);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
if (lean_is_scalar(x_36)) {
 x_40 = lean_alloc_ctor(0, 1, 0);
} else {
 x_40 = x_36;
}
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_inc_ref(x_37);
lean_dec(x_35);
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
lean_dec_ref(x_37);
if (lean_is_scalar(x_36)) {
 x_42 = lean_alloc_ctor(0, 1, 0);
} else {
 x_42 = x_36;
}
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_4);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; lean_object* x_49; uint8_t x_50; 
x_44 = lean_ctor_get(x_4, 0);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_size(x_44);
x_48 = 0;
x_49 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(x_1, x_2, x_45, x_44, x_47, x_48, x_46, x_6, x_7, x_8, x_9);
lean_dec_ref(x_44);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_ctor_get(x_51, 0);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_ctor_set(x_4, 0, x_53);
lean_ctor_set(x_49, 0, x_4);
return x_49;
}
else
{
lean_object* x_54; 
lean_inc_ref(x_52);
lean_dec(x_51);
lean_free_object(x_4);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec_ref(x_52);
lean_ctor_set(x_49, 0, x_54);
return x_49;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_49, 0);
lean_inc(x_55);
lean_dec(x_49);
x_56 = lean_ctor_get(x_55, 0);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_ctor_set(x_4, 0, x_57);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_4);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_inc_ref(x_56);
lean_dec(x_55);
lean_free_object(x_4);
x_59 = lean_ctor_get(x_56, 0);
lean_inc(x_59);
lean_dec_ref(x_56);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; size_t x_64; size_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_61 = lean_ctor_get(x_4, 0);
lean_inc(x_61);
lean_dec(x_4);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_5);
x_64 = lean_array_size(x_61);
x_65 = 0;
x_66 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(x_1, x_2, x_62, x_61, x_64, x_65, x_63, x_6, x_7, x_8, x_9);
lean_dec_ref(x_61);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
x_69 = lean_ctor_get(x_67, 0);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
if (lean_is_scalar(x_68)) {
 x_72 = lean_alloc_ctor(0, 1, 0);
} else {
 x_72 = x_68;
}
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_inc_ref(x_69);
lean_dec(x_67);
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
lean_dec_ref(x_69);
if (lean_is_scalar(x_68)) {
 x_74 = lean_alloc_ctor(0, 1, 0);
} else {
 x_74 = x_68;
}
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_6, x_5);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_7);
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
x_11 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_50; lean_object* x_51; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_72; lean_object* x_73; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_92; lean_object* x_93; uint8_t x_99; 
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
x_28 = l_Lean_LocalDecl_fvarId(x_22);
x_99 = l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_28, x_3);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_119; uint8_t x_152; uint8_t x_155; 
lean_inc(x_24);
x_100 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_100, 0, x_24);
x_155 = l_Lean_LocalDecl_isAuxDecl(x_22);
if (x_155 == 0)
{
uint8_t x_156; uint8_t x_157; 
x_156 = l_Lean_LocalDecl_binderInfo(x_22);
x_157 = l_Lean_BinderInfo_isInstImplicit(x_156);
x_152 = x_157;
goto block_154;
}
else
{
x_152 = x_155;
goto block_154;
}
block_110:
{
if (x_104 == 0)
{
uint8_t x_106; 
x_106 = l_Lean_Expr_hasFVar(x_102);
if (x_106 == 0)
{
uint8_t x_107; 
x_107 = l_Lean_Expr_hasMVar(x_102);
if (x_107 == 0)
{
lean_dec_ref(x_103);
lean_dec_ref(x_102);
lean_dec_ref(x_100);
x_57 = lean_box(0);
x_58 = x_107;
x_59 = x_105;
goto block_71;
}
else
{
lean_object* x_108; 
x_108 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_100, x_103, x_102, x_105);
x_72 = lean_box(0);
x_73 = x_108;
goto block_77;
}
}
else
{
lean_object* x_109; 
x_109 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_100, x_103, x_102, x_105);
x_72 = lean_box(0);
x_73 = x_109;
goto block_77;
}
}
else
{
lean_dec_ref(x_103);
lean_dec_ref(x_102);
lean_dec_ref(x_100);
x_57 = lean_box(0);
x_58 = x_104;
x_59 = x_105;
goto block_71;
}
}
block_118:
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec_ref(x_114);
x_117 = lean_unbox(x_115);
lean_dec(x_115);
x_101 = lean_box(0);
x_102 = x_112;
x_103 = x_113;
x_104 = x_117;
x_105 = x_116;
goto block_110;
}
block_151:
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_box(x_119);
x_121 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_121, 0, x_120);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_122 = lean_ctor_get(x_22, 3);
lean_inc_ref(x_122);
lean_dec_ref(x_22);
x_123 = lean_st_ref_get(x_8);
x_124 = lean_ctor_get(x_123, 0);
lean_inc_ref(x_124);
lean_dec_ref(x_123);
x_125 = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
lean_inc_ref(x_124);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
x_127 = l_Lean_Expr_hasFVar(x_122);
if (x_127 == 0)
{
uint8_t x_128; 
x_128 = l_Lean_Expr_hasMVar(x_122);
if (x_128 == 0)
{
lean_dec_ref(x_126);
lean_dec_ref(x_122);
lean_dec_ref(x_121);
lean_dec_ref(x_100);
x_36 = lean_box(0);
x_37 = x_128;
x_38 = x_124;
goto block_49;
}
else
{
lean_object* x_129; 
lean_dec_ref(x_124);
x_129 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_100, x_121, x_122, x_126);
x_50 = lean_box(0);
x_51 = x_129;
goto block_56;
}
}
else
{
lean_object* x_130; 
lean_dec_ref(x_124);
x_130 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_100, x_121, x_122, x_126);
x_50 = lean_box(0);
x_51 = x_130;
goto block_56;
}
}
else
{
uint8_t x_131; 
x_131 = lean_ctor_get_uint8(x_22, sizeof(void*)*5);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_132 = lean_ctor_get(x_22, 3);
lean_inc_ref(x_132);
x_133 = lean_ctor_get(x_22, 4);
lean_inc_ref(x_133);
lean_dec_ref(x_22);
x_134 = lean_st_ref_get(x_8);
x_135 = lean_ctor_get(x_134, 0);
lean_inc_ref(x_135);
lean_dec_ref(x_134);
x_136 = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
x_138 = l_Lean_Expr_hasFVar(x_132);
if (x_138 == 0)
{
uint8_t x_139; 
x_139 = l_Lean_Expr_hasMVar(x_132);
if (x_139 == 0)
{
lean_dec_ref(x_132);
x_101 = lean_box(0);
x_102 = x_133;
x_103 = x_121;
x_104 = x_139;
x_105 = x_137;
goto block_110;
}
else
{
lean_object* x_140; 
lean_inc_ref(x_121);
lean_inc_ref(x_100);
x_140 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_100, x_121, x_132, x_137);
x_111 = lean_box(0);
x_112 = x_133;
x_113 = x_121;
x_114 = x_140;
goto block_118;
}
}
else
{
lean_object* x_141; 
lean_inc_ref(x_121);
lean_inc_ref(x_100);
x_141 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_100, x_121, x_132, x_137);
x_111 = lean_box(0);
x_112 = x_133;
x_113 = x_121;
x_114 = x_141;
goto block_118;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_142 = lean_ctor_get(x_22, 3);
lean_inc_ref(x_142);
lean_dec_ref(x_22);
x_143 = lean_st_ref_get(x_8);
x_144 = lean_ctor_get(x_143, 0);
lean_inc_ref(x_144);
lean_dec_ref(x_143);
x_145 = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
lean_inc_ref(x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
x_147 = l_Lean_Expr_hasFVar(x_142);
if (x_147 == 0)
{
uint8_t x_148; 
x_148 = l_Lean_Expr_hasMVar(x_142);
if (x_148 == 0)
{
lean_dec_ref(x_146);
lean_dec_ref(x_142);
lean_dec_ref(x_121);
lean_dec_ref(x_100);
x_78 = lean_box(0);
x_79 = x_148;
x_80 = x_144;
goto block_91;
}
else
{
lean_object* x_149; 
lean_dec_ref(x_144);
x_149 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_100, x_121, x_142, x_146);
x_92 = lean_box(0);
x_93 = x_149;
goto block_98;
}
}
else
{
lean_object* x_150; 
lean_dec_ref(x_144);
x_150 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_100, x_121, x_142, x_146);
x_92 = lean_box(0);
x_93 = x_150;
goto block_98;
}
}
}
}
block_154:
{
if (x_152 == 0)
{
if (x_2 == 0)
{
lean_dec(x_25);
x_119 = x_2;
goto block_151;
}
else
{
uint8_t x_153; 
x_153 = l_Lean_LocalDecl_isLet(x_22, x_152);
if (x_153 == 0)
{
lean_dec(x_25);
x_119 = x_153;
goto block_151;
}
else
{
lean_dec_ref(x_100);
lean_dec(x_28);
lean_dec(x_22);
lean_dec(x_20);
goto block_27;
}
}
}
else
{
lean_dec_ref(x_100);
lean_dec(x_28);
lean_dec(x_22);
lean_dec(x_20);
goto block_27;
}
}
}
else
{
lean_object* x_158; 
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_20);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_23);
lean_ctor_set(x_158, 1, x_24);
x_10 = x_158;
x_11 = lean_box(0);
goto block_16;
}
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
x_11 = lean_box(0);
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
x_11 = lean_box(0);
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
x_11 = lean_box(0);
goto block_16;
}
}
block_49:
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_st_ref_take(x_8);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_38);
x_42 = lean_st_ref_set(x_8, x_39);
x_29 = x_37;
x_30 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_39, 1);
x_44 = lean_ctor_get(x_39, 2);
x_45 = lean_ctor_get(x_39, 3);
x_46 = lean_ctor_get(x_39, 4);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_39);
x_47 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_43);
lean_ctor_set(x_47, 2, x_44);
lean_ctor_set(x_47, 3, x_45);
lean_ctor_set(x_47, 4, x_46);
x_48 = lean_st_ref_set(x_8, x_47);
x_29 = x_37;
x_30 = lean_box(0);
goto block_35;
}
}
block_56:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
lean_dec_ref(x_51);
x_54 = lean_ctor_get(x_52, 1);
lean_inc_ref(x_54);
lean_dec(x_52);
x_55 = lean_unbox(x_53);
lean_dec(x_53);
x_36 = lean_box(0);
x_37 = x_55;
x_38 = x_54;
goto block_49;
}
block_71:
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_59, 1);
lean_inc_ref(x_60);
lean_dec_ref(x_59);
x_61 = lean_st_ref_take(x_8);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_61, 0);
lean_dec(x_63);
lean_ctor_set(x_61, 0, x_60);
x_64 = lean_st_ref_set(x_8, x_61);
x_29 = x_58;
x_30 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_61, 1);
x_66 = lean_ctor_get(x_61, 2);
x_67 = lean_ctor_get(x_61, 3);
x_68 = lean_ctor_get(x_61, 4);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_61);
x_69 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_69, 0, x_60);
lean_ctor_set(x_69, 1, x_65);
lean_ctor_set(x_69, 2, x_66);
lean_ctor_set(x_69, 3, x_67);
lean_ctor_set(x_69, 4, x_68);
x_70 = lean_st_ref_set(x_8, x_69);
x_29 = x_58;
x_30 = lean_box(0);
goto block_35;
}
}
block_77:
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec_ref(x_73);
x_76 = lean_unbox(x_74);
lean_dec(x_74);
x_57 = lean_box(0);
x_58 = x_76;
x_59 = x_75;
goto block_71;
}
block_91:
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_st_ref_take(x_8);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_81, 0);
lean_dec(x_83);
lean_ctor_set(x_81, 0, x_80);
x_84 = lean_st_ref_set(x_8, x_81);
x_29 = x_79;
x_30 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_85 = lean_ctor_get(x_81, 1);
x_86 = lean_ctor_get(x_81, 2);
x_87 = lean_ctor_get(x_81, 3);
x_88 = lean_ctor_get(x_81, 4);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_81);
x_89 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_89, 0, x_80);
lean_ctor_set(x_89, 1, x_85);
lean_ctor_set(x_89, 2, x_86);
lean_ctor_set(x_89, 3, x_87);
lean_ctor_set(x_89, 4, x_88);
x_90 = lean_st_ref_set(x_8, x_89);
x_29 = x_79;
x_30 = lean_box(0);
goto block_35;
}
}
block_98:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
lean_dec_ref(x_93);
x_96 = lean_ctor_get(x_94, 1);
lean_inc_ref(x_96);
lean_dec(x_94);
x_97 = lean_unbox(x_95);
lean_dec(x_95);
x_78 = lean_box(0);
x_79 = x_97;
x_80 = x_96;
goto block_91;
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
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_20; 
x_20 = lean_usize_dec_lt(x_6, x_5);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_3);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_7);
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
x_14 = lean_box(0);
goto block_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_53; lean_object* x_54; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_75; lean_object* x_76; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_95; lean_object* x_96; uint8_t x_102; 
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
x_31 = l_Lean_LocalDecl_fvarId(x_25);
x_102 = l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_31, x_2);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_122; uint8_t x_155; uint8_t x_158; 
lean_inc(x_27);
x_103 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_103, 0, x_27);
x_158 = l_Lean_LocalDecl_isAuxDecl(x_25);
if (x_158 == 0)
{
uint8_t x_159; uint8_t x_160; 
x_159 = l_Lean_LocalDecl_binderInfo(x_25);
x_160 = l_Lean_BinderInfo_isInstImplicit(x_159);
x_155 = x_160;
goto block_157;
}
else
{
x_155 = x_158;
goto block_157;
}
block_113:
{
if (x_107 == 0)
{
uint8_t x_109; 
x_109 = l_Lean_Expr_hasFVar(x_105);
if (x_109 == 0)
{
uint8_t x_110; 
x_110 = l_Lean_Expr_hasMVar(x_105);
if (x_110 == 0)
{
lean_dec_ref(x_105);
lean_dec_ref(x_104);
lean_dec_ref(x_103);
x_60 = lean_box(0);
x_61 = x_110;
x_62 = x_108;
goto block_74;
}
else
{
lean_object* x_111; 
x_111 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_103, x_104, x_105, x_108);
x_75 = lean_box(0);
x_76 = x_111;
goto block_80;
}
}
else
{
lean_object* x_112; 
x_112 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_103, x_104, x_105, x_108);
x_75 = lean_box(0);
x_76 = x_112;
goto block_80;
}
}
else
{
lean_dec_ref(x_105);
lean_dec_ref(x_104);
lean_dec_ref(x_103);
x_60 = lean_box(0);
x_61 = x_107;
x_62 = x_108;
goto block_74;
}
}
block_121:
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec_ref(x_117);
x_120 = lean_unbox(x_118);
lean_dec(x_118);
x_104 = x_114;
x_105 = x_115;
x_106 = lean_box(0);
x_107 = x_120;
x_108 = x_119;
goto block_113;
}
block_154:
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_box(x_122);
x_124 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_124, 0, x_123);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_125 = lean_ctor_get(x_25, 3);
lean_inc_ref(x_125);
lean_dec_ref(x_25);
x_126 = lean_st_ref_get(x_9);
x_127 = lean_ctor_get(x_126, 0);
lean_inc_ref(x_127);
lean_dec_ref(x_126);
x_128 = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
lean_inc_ref(x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
x_130 = l_Lean_Expr_hasFVar(x_125);
if (x_130 == 0)
{
uint8_t x_131; 
x_131 = l_Lean_Expr_hasMVar(x_125);
if (x_131 == 0)
{
lean_dec_ref(x_129);
lean_dec_ref(x_125);
lean_dec_ref(x_124);
lean_dec_ref(x_103);
x_39 = lean_box(0);
x_40 = x_131;
x_41 = x_127;
goto block_52;
}
else
{
lean_object* x_132; 
lean_dec_ref(x_127);
x_132 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_103, x_124, x_125, x_129);
x_53 = lean_box(0);
x_54 = x_132;
goto block_59;
}
}
else
{
lean_object* x_133; 
lean_dec_ref(x_127);
x_133 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_103, x_124, x_125, x_129);
x_53 = lean_box(0);
x_54 = x_133;
goto block_59;
}
}
else
{
uint8_t x_134; 
x_134 = lean_ctor_get_uint8(x_25, sizeof(void*)*5);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_135 = lean_ctor_get(x_25, 3);
lean_inc_ref(x_135);
x_136 = lean_ctor_get(x_25, 4);
lean_inc_ref(x_136);
lean_dec_ref(x_25);
x_137 = lean_st_ref_get(x_9);
x_138 = lean_ctor_get(x_137, 0);
lean_inc_ref(x_138);
lean_dec_ref(x_137);
x_139 = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
x_141 = l_Lean_Expr_hasFVar(x_135);
if (x_141 == 0)
{
uint8_t x_142; 
x_142 = l_Lean_Expr_hasMVar(x_135);
if (x_142 == 0)
{
lean_dec_ref(x_135);
x_104 = x_124;
x_105 = x_136;
x_106 = lean_box(0);
x_107 = x_142;
x_108 = x_140;
goto block_113;
}
else
{
lean_object* x_143; 
lean_inc_ref(x_124);
lean_inc_ref(x_103);
x_143 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_103, x_124, x_135, x_140);
x_114 = x_124;
x_115 = x_136;
x_116 = lean_box(0);
x_117 = x_143;
goto block_121;
}
}
else
{
lean_object* x_144; 
lean_inc_ref(x_124);
lean_inc_ref(x_103);
x_144 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_103, x_124, x_135, x_140);
x_114 = x_124;
x_115 = x_136;
x_116 = lean_box(0);
x_117 = x_144;
goto block_121;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_145 = lean_ctor_get(x_25, 3);
lean_inc_ref(x_145);
lean_dec_ref(x_25);
x_146 = lean_st_ref_get(x_9);
x_147 = lean_ctor_get(x_146, 0);
lean_inc_ref(x_147);
lean_dec_ref(x_146);
x_148 = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
lean_inc_ref(x_147);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_147);
x_150 = l_Lean_Expr_hasFVar(x_145);
if (x_150 == 0)
{
uint8_t x_151; 
x_151 = l_Lean_Expr_hasMVar(x_145);
if (x_151 == 0)
{
lean_dec_ref(x_149);
lean_dec_ref(x_145);
lean_dec_ref(x_124);
lean_dec_ref(x_103);
x_81 = lean_box(0);
x_82 = x_151;
x_83 = x_147;
goto block_94;
}
else
{
lean_object* x_152; 
lean_dec_ref(x_147);
x_152 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_103, x_124, x_145, x_149);
x_95 = lean_box(0);
x_96 = x_152;
goto block_101;
}
}
else
{
lean_object* x_153; 
lean_dec_ref(x_147);
x_153 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_103, x_124, x_145, x_149);
x_95 = lean_box(0);
x_96 = x_153;
goto block_101;
}
}
}
}
block_157:
{
if (x_155 == 0)
{
if (x_1 == 0)
{
lean_dec(x_28);
x_122 = x_1;
goto block_154;
}
else
{
uint8_t x_156; 
x_156 = l_Lean_LocalDecl_isLet(x_25, x_155);
if (x_156 == 0)
{
lean_dec(x_28);
x_122 = x_156;
goto block_154;
}
else
{
lean_dec_ref(x_103);
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_23);
goto block_30;
}
}
}
else
{
lean_dec_ref(x_103);
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_23);
goto block_30;
}
}
}
else
{
lean_object* x_161; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_23);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_26);
lean_ctor_set(x_161, 1, x_27);
x_13 = x_161;
x_14 = lean_box(0);
goto block_19;
}
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
x_14 = lean_box(0);
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
x_14 = lean_box(0);
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
x_14 = lean_box(0);
goto block_19;
}
}
block_52:
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_st_ref_take(x_9);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
lean_ctor_set(x_42, 0, x_41);
x_45 = lean_st_ref_set(x_9, x_42);
x_32 = x_40;
x_33 = lean_box(0);
goto block_38;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_42, 1);
x_47 = lean_ctor_get(x_42, 2);
x_48 = lean_ctor_get(x_42, 3);
x_49 = lean_ctor_get(x_42, 4);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_42);
x_50 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_50, 0, x_41);
lean_ctor_set(x_50, 1, x_46);
lean_ctor_set(x_50, 2, x_47);
lean_ctor_set(x_50, 3, x_48);
lean_ctor_set(x_50, 4, x_49);
x_51 = lean_st_ref_set(x_9, x_50);
x_32 = x_40;
x_33 = lean_box(0);
goto block_38;
}
}
block_59:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec_ref(x_54);
x_57 = lean_ctor_get(x_55, 1);
lean_inc_ref(x_57);
lean_dec(x_55);
x_58 = lean_unbox(x_56);
lean_dec(x_56);
x_39 = lean_box(0);
x_40 = x_58;
x_41 = x_57;
goto block_52;
}
block_74:
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_63);
lean_dec_ref(x_62);
x_64 = lean_st_ref_take(x_9);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
lean_ctor_set(x_64, 0, x_63);
x_67 = lean_st_ref_set(x_9, x_64);
x_32 = x_61;
x_33 = lean_box(0);
goto block_38;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_64, 1);
x_69 = lean_ctor_get(x_64, 2);
x_70 = lean_ctor_get(x_64, 3);
x_71 = lean_ctor_get(x_64, 4);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_64);
x_72 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_72, 0, x_63);
lean_ctor_set(x_72, 1, x_68);
lean_ctor_set(x_72, 2, x_69);
lean_ctor_set(x_72, 3, x_70);
lean_ctor_set(x_72, 4, x_71);
x_73 = lean_st_ref_set(x_9, x_72);
x_32 = x_61;
x_33 = lean_box(0);
goto block_38;
}
}
block_80:
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec_ref(x_76);
x_79 = lean_unbox(x_77);
lean_dec(x_77);
x_60 = lean_box(0);
x_61 = x_79;
x_62 = x_78;
goto block_74;
}
block_94:
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_st_ref_take(x_9);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_84, 0);
lean_dec(x_86);
lean_ctor_set(x_84, 0, x_83);
x_87 = lean_st_ref_set(x_9, x_84);
x_32 = x_82;
x_33 = lean_box(0);
goto block_38;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_88 = lean_ctor_get(x_84, 1);
x_89 = lean_ctor_get(x_84, 2);
x_90 = lean_ctor_get(x_84, 3);
x_91 = lean_ctor_get(x_84, 4);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_84);
x_92 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_92, 0, x_83);
lean_ctor_set(x_92, 1, x_88);
lean_ctor_set(x_92, 2, x_89);
lean_ctor_set(x_92, 3, x_90);
lean_ctor_set(x_92, 4, x_91);
x_93 = lean_st_ref_set(x_9, x_92);
x_32 = x_82;
x_33 = lean_box(0);
goto block_38;
}
}
block_101:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec_ref(x_96);
x_99 = lean_ctor_get(x_97, 1);
lean_inc_ref(x_99);
lean_dec(x_97);
x_100 = lean_unbox(x_98);
lean_dec(x_98);
x_81 = lean_box(0);
x_82 = x_100;
x_83 = x_99;
goto block_94;
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
x_18 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4___redArg(x_3, x_1, x_2, x_4, x_5, x_17, x_15, x_9);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_3);
lean_inc_ref(x_4);
x_12 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(x_1, x_2, x_4, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_4);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec_ref(x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
lean_free_object(x_12);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_array_size(x_11);
x_20 = 0;
x_21 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4(x_1, x_2, x_17, x_11, x_19, x_20, x_18, x_5, x_6, x_7, x_8);
lean_dec_ref(x_11);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_23, 0);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; 
lean_inc_ref(x_24);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec_ref(x_24);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_ctor_get(x_27, 0);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_inc_ref(x_28);
lean_dec(x_27);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec_ref(x_28);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_12, 0);
lean_inc(x_33);
lean_dec(x_12);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec_ref(x_11);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec_ref(x_33);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_array_size(x_11);
x_40 = 0;
x_41 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4(x_1, x_2, x_37, x_11, x_39, x_40, x_38, x_5, x_6, x_7, x_8);
lean_dec_ref(x_11);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_42, 0);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 1, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_inc_ref(x_44);
lean_dec(x_42);
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
lean_dec_ref(x_44);
if (lean_is_scalar(x_43)) {
 x_48 = lean_alloc_ctor(0, 1, 0);
} else {
 x_48 = x_43;
}
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Meta_getFVarSetToGeneralize_spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_9 = lean_box(1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get_size(x_1);
x_24 = lean_nat_dec_lt(x_22, x_23);
if (x_24 == 0)
{
lean_dec(x_23);
x_10 = x_9;
goto block_21;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_23, x_23);
if (x_25 == 0)
{
lean_dec(x_23);
x_10 = x_9;
goto block_21;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_28 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Meta_getFVarSetToGeneralize_spec__7(x_1, x_26, x_27, x_9);
x_10 = x_28;
goto block_21;
}
}
block_21:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_4, 2);
x_12 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_10);
x_14 = l_Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0(x_3, x_2, x_12, x_13, x_4, x_5, x_6, x_7);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_1);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_17 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__0(x_14, x_2, x_3, x_4, x_5, x_15, x_16, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_2);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg(x_1, x_10, x_3, x_4, x_11, x_12, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_2);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1(x_1, x_13, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_1);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(x_13, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11);
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
x_12 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_2);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4___redArg(x_1, x_10, x_3, x_4, x_11, x_12, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_2);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4(x_1, x_13, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_1);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4(x_13, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11);
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
x_11 = l_Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Meta_getFVarSetToGeneralize_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Meta_getFVarSetToGeneralize_spec__7(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_getFVarSetToGeneralize(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_9 = l_Lean_Meta_mkGeneralizationForbiddenSet(x_1, x_2, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
lean_inc_ref(x_4);
x_11 = l_Lean_Meta_getFVarSetToGeneralize(x_1, x_10, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
x_13 = x_18;
goto block_17;
}
else
{
lean_object* x_19; 
x_19 = lean_unsigned_to_nat(0u);
x_13 = x_19;
goto block_17;
}
block_17:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_mk_empty_array_with_capacity(x_13);
lean_dec(x_13);
x_15 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(x_14, x_12);
x_16 = l_Lean_Meta_sortFVarIds___redArg(x_15, x_4);
return x_16;
}
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_20 = !lean_is_exclusive(x_9);
if (x_20 == 0)
{
return x_9;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_9, 0);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_getFVarsToGeneralize(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
lean_dec_ref(x_1);
return x_10;
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Util_CollectFVars(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_GeneralizeVars(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0 = _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0();
lean_mark_persistent(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0);
l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1 = _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1();
lean_mark_persistent(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2 = _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2();
lean_mark_persistent(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2);
l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3 = _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3();
lean_mark_persistent(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3);
l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4 = _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4();
lean_mark_persistent(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4);
l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__5 = _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__5();
lean_mark_persistent(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__5);
l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__6 = _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__6();
lean_mark_persistent(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__6);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
