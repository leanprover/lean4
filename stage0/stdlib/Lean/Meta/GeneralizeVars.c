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
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0;
static lean_once_cell_t l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2 = (const lean_object*)&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(lean_object*, size_t, size_t, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_sortFVarIds___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_24; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = lean_ctor_get(x_11, 1);
x_13 = lean_ctor_get(x_11, 2);
x_14 = lean_ctor_get(x_11, 3);
x_15 = lean_ctor_get(x_11, 4);
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_11, 0);
lean_dec(x_25);
x_16 = x_11;
x_17 = x_24;
goto block_23;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_18; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_10);
x_18 = x_16;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_12);
lean_ctor_set(x_22, 2, x_13);
lean_ctor_set(x_22, 3, x_14);
lean_ctor_set(x_22, 4, x_15);
x_18 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_st_ref_set(x_2, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_9);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(x_1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(x_1, x_3);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_26; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 4);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(x_1, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get(x_9, 1);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
x_12 = x_9;
x_13 = x_26;
goto block_25;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = x_26;
goto block_25;
}
block_25:
{
uint8_t x_14; 
x_14 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_4, x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_4);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_10);
x_16 = l_Lean_FVarIdSet_insert(x_11, x_4);
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_16);
lean_ctor_set(x_12, 0, x_15);
x_17 = x_12;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
x_17 = x_20;
goto block_19;
}
block_19:
{
x_1 = x_17;
x_2 = x_6;
goto _start;
}
}
else
{
lean_object* x_21; 
lean_dec(x_4);
if (x_13 == 0)
{
x_21 = x_12;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_11);
x_21 = x_24;
goto block_23;
}
block_23:
{
x_1 = x_21;
x_2 = x_6;
goto _start;
}
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2));
x_2 = lean_box(1);
x_3 = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
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
lean_object* x_9; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_32; 
lean_inc_ref(x_4);
x_32 = l_Lean_FVarId_getDecl___redArg(x_1, x_4, x_6, x_7);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = l_Lean_LocalDecl_type(x_33);
x_35 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(x_34, x_5);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3);
x_38 = l_Lean_collectFVars(x_37, x_36);
x_39 = 0;
x_40 = l_Lean_LocalDecl_value_x3f(x_33, x_39);
lean_dec(x_33);
if (lean_obj_tag(x_40) == 1)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(x_41, x_5);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = l_Lean_collectFVars(x_38, x_43);
x_21 = x_44;
x_22 = x_4;
x_23 = x_5;
x_24 = x_6;
x_25 = x_7;
goto block_31;
}
else
{
lean_dec(x_40);
x_21 = x_38;
x_22 = x_4;
x_23 = x_5;
x_24 = x_6;
x_25 = x_7;
goto block_31;
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_52; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = lean_ctor_get(x_32, 0);
x_52 = !lean_is_exclusive(x_32);
if (x_52 == 0)
{
x_46 = x_32;
x_47 = x_52;
goto block_51;
}
else
{
lean_inc(x_45);
lean_dec(x_32);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
block_20:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_19; 
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get(x_9, 1);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
x_12 = x_9;
x_13 = x_19;
goto block_18;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; 
if (x_13 == 0)
{
x_14 = x_12;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_11);
x_14 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
block_31:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_22);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec_ref(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_3);
x_28 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(x_27, x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_9 = x_30;
goto block_20;
}
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
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(x_1, x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
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
x_11 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_9, x_2);
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
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec_ref(x_3);
x_18 = lean_ctor_get(x_13, 0);
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
x_19 = x_13;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_3, x_2);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_53; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
x_53 = !lean_is_exclusive(x_4);
if (x_53 == 0)
{
x_19 = x_4;
x_20 = x_53;
goto block_52;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_19 = lean_box(0);
x_20 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_array_uget_borrowed(x_1, x_3);
x_22 = l_Lean_Expr_isFVar(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_21);
x_23 = lean_infer_type(x_21, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(x_24, x_6);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = l_Lean_collectFVars(x_17, x_26);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_27);
x_28 = x_19;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_18);
x_28 = x_30;
goto block_29;
}
block_29:
{
x_10 = x_28;
goto block_14;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
lean_del_object(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_31 = lean_ctor_get(x_25, 0);
x_38 = !lean_is_exclusive(x_25);
if (x_38 == 0)
{
x_32 = x_25;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_del_object(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_39 = lean_ctor_get(x_23, 0);
x_46 = !lean_is_exclusive(x_23);
if (x_46 == 0)
{
x_40 = x_23;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_23);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = l_Lean_Expr_fvarId_x21(x_21);
x_48 = lean_array_push(x_18, x_47);
if (x_20 == 0)
{
lean_ctor_set(x_19, 1, x_48);
x_49 = x_19;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_17);
lean_ctor_set(x_51, 1, x_48);
x_49 = x_51;
goto block_50;
}
block_50:
{
x_10 = x_49;
goto block_14;
}
}
}
}
block_14:
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
x_4 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_8 = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
x_9 = ((lean_object*)(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2));
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
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0(x_1, x_12, x_13, x_11, x_3, x_4, x_5, x_6);
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
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_21 = lean_ctor_get(x_14, 0);
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
x_22 = x_14;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_5, x_4);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_170; 
x_11 = lean_ctor_get(x_6, 1);
x_170 = !lean_is_exclusive(x_6);
if (x_170 == 0)
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_6, 0);
lean_dec(x_171);
x_12 = x_6;
x_13 = x_170;
goto block_169;
}
else
{
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_box(0);
x_13 = x_170;
goto block_169;
}
block_169:
{
lean_object* x_14; lean_object* x_15; lean_object* x_23; 
x_14 = lean_box(0);
x_23 = lean_array_uget_borrowed(x_3, x_5);
if (lean_obj_tag(x_23) == 0)
{
x_15 = x_11;
goto block_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_168; 
x_24 = lean_ctor_get(x_23, 0);
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
x_168 = !lean_is_exclusive(x_11);
if (x_168 == 0)
{
x_27 = x_11;
x_28 = x_168;
goto block_167;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_11);
x_27 = lean_box(0);
x_28 = x_168;
goto block_167;
}
block_167:
{
lean_object* x_33; uint8_t x_34; uint8_t x_40; lean_object* x_41; lean_object* x_57; uint8_t x_63; lean_object* x_64; lean_object* x_81; uint8_t x_86; lean_object* x_87; lean_object* x_103; uint8_t x_109; 
x_33 = l_Lean_LocalDecl_fvarId(x_24);
x_109 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_33, x_2);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_127; uint8_t x_160; uint8_t x_163; 
lean_inc(x_25);
x_110 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_110, 0, x_25);
x_163 = l_Lean_LocalDecl_isAuxDecl(x_24);
if (x_163 == 0)
{
uint8_t x_164; uint8_t x_165; 
x_164 = l_Lean_LocalDecl_binderInfo(x_24);
x_165 = l_Lean_BinderInfo_isInstImplicit(x_164);
x_160 = x_165;
goto block_162;
}
else
{
x_160 = x_163;
goto block_162;
}
block_119:
{
if (x_113 == 0)
{
uint8_t x_115; 
x_115 = l_Lean_Expr_hasFVar(x_112);
if (x_115 == 0)
{
uint8_t x_116; 
x_116 = l_Lean_Expr_hasMVar(x_112);
if (x_116 == 0)
{
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
x_63 = x_116;
x_64 = x_114;
goto block_80;
}
else
{
lean_object* x_117; 
x_117 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_111, x_112, x_114);
x_81 = x_117;
goto block_85;
}
}
else
{
lean_object* x_118; 
x_118 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_111, x_112, x_114);
x_81 = x_118;
goto block_85;
}
}
else
{
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
x_63 = x_113;
x_64 = x_114;
goto block_80;
}
}
block_126:
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec_ref(x_122);
x_125 = lean_unbox(x_123);
lean_dec(x_123);
x_111 = x_121;
x_112 = x_120;
x_113 = x_125;
x_114 = x_124;
goto block_119;
}
block_159:
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_box(x_127);
x_129 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(x_129, 0, x_128);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_130 = lean_ctor_get(x_24, 3);
x_131 = lean_st_ref_get(x_7);
x_132 = lean_ctor_get(x_131, 0);
lean_inc_ref(x_132);
lean_dec(x_131);
x_133 = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
lean_inc_ref(x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_132);
x_135 = l_Lean_Expr_hasFVar(x_130);
if (x_135 == 0)
{
uint8_t x_136; 
x_136 = l_Lean_Expr_hasMVar(x_130);
if (x_136 == 0)
{
lean_dec_ref(x_134);
lean_dec_ref(x_129);
lean_dec_ref(x_110);
x_40 = x_136;
x_41 = x_132;
goto block_56;
}
else
{
lean_object* x_137; 
lean_dec_ref(x_132);
lean_inc_ref(x_130);
x_137 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_129, x_130, x_134);
x_57 = x_137;
goto block_62;
}
}
else
{
lean_object* x_138; 
lean_dec_ref(x_132);
lean_inc_ref(x_130);
x_138 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_129, x_130, x_134);
x_57 = x_138;
goto block_62;
}
}
else
{
uint8_t x_139; 
x_139 = lean_ctor_get_uint8(x_24, sizeof(void*)*5);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_140 = lean_ctor_get(x_24, 3);
x_141 = lean_ctor_get(x_24, 4);
x_142 = lean_st_ref_get(x_7);
x_143 = lean_ctor_get(x_142, 0);
lean_inc_ref(x_143);
lean_dec(x_142);
x_144 = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_143);
x_146 = l_Lean_Expr_hasFVar(x_140);
if (x_146 == 0)
{
uint8_t x_147; 
x_147 = l_Lean_Expr_hasMVar(x_140);
if (x_147 == 0)
{
lean_inc_ref(x_141);
x_111 = x_129;
x_112 = x_141;
x_113 = x_147;
x_114 = x_145;
goto block_119;
}
else
{
lean_object* x_148; 
lean_inc_ref(x_140);
lean_inc_ref(x_129);
lean_inc_ref(x_110);
x_148 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_129, x_140, x_145);
lean_inc_ref(x_141);
x_120 = x_141;
x_121 = x_129;
x_122 = x_148;
goto block_126;
}
}
else
{
lean_object* x_149; 
lean_inc_ref(x_140);
lean_inc_ref(x_129);
lean_inc_ref(x_110);
x_149 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_129, x_140, x_145);
lean_inc_ref(x_141);
x_120 = x_141;
x_121 = x_129;
x_122 = x_149;
goto block_126;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_150 = lean_ctor_get(x_24, 3);
x_151 = lean_st_ref_get(x_7);
x_152 = lean_ctor_get(x_151, 0);
lean_inc_ref(x_152);
lean_dec(x_151);
x_153 = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
lean_inc_ref(x_152);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_152);
x_155 = l_Lean_Expr_hasFVar(x_150);
if (x_155 == 0)
{
uint8_t x_156; 
x_156 = l_Lean_Expr_hasMVar(x_150);
if (x_156 == 0)
{
lean_dec_ref(x_154);
lean_dec_ref(x_129);
lean_dec_ref(x_110);
x_86 = x_156;
x_87 = x_152;
goto block_102;
}
else
{
lean_object* x_157; 
lean_dec_ref(x_152);
lean_inc_ref(x_150);
x_157 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_129, x_150, x_154);
x_103 = x_157;
goto block_108;
}
}
else
{
lean_object* x_158; 
lean_dec_ref(x_152);
lean_inc_ref(x_150);
x_158 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_129, x_150, x_154);
x_103 = x_158;
goto block_108;
}
}
}
}
block_162:
{
if (x_160 == 0)
{
if (x_1 == 0)
{
lean_del_object(x_27);
x_127 = x_1;
goto block_159;
}
else
{
uint8_t x_161; 
x_161 = l_Lean_LocalDecl_isLet(x_24, x_160);
if (x_161 == 0)
{
lean_del_object(x_27);
x_127 = x_161;
goto block_159;
}
else
{
lean_dec_ref(x_110);
lean_dec(x_33);
goto block_32;
}
}
}
else
{
lean_dec_ref(x_110);
lean_dec(x_33);
goto block_32;
}
}
}
else
{
lean_object* x_166; 
lean_dec(x_33);
lean_del_object(x_27);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_25);
lean_ctor_set(x_166, 1, x_26);
x_15 = x_166;
goto block_22;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
x_15 = x_29;
goto block_22;
}
}
block_39:
{
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_26);
x_15 = x_35;
goto block_22;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_inc(x_33);
x_36 = l_Lean_FVarIdSet_insert(x_26, x_33);
x_37 = l_Lean_FVarIdSet_insert(x_25, x_33);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_15 = x_38;
goto block_22;
}
}
block_56:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_54; 
x_42 = lean_st_ref_take(x_7);
x_43 = lean_ctor_get(x_42, 1);
x_44 = lean_ctor_get(x_42, 2);
x_45 = lean_ctor_get(x_42, 3);
x_46 = lean_ctor_get(x_42, 4);
x_54 = !lean_is_exclusive(x_42);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_42, 0);
lean_dec(x_55);
x_47 = x_42;
x_48 = x_54;
goto block_53;
}
else
{
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_42);
x_47 = lean_box(0);
x_48 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_49; 
if (x_48 == 0)
{
lean_ctor_set(x_47, 0, x_41);
x_49 = x_47;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_41);
lean_ctor_set(x_52, 1, x_43);
lean_ctor_set(x_52, 2, x_44);
lean_ctor_set(x_52, 3, x_45);
lean_ctor_set(x_52, 4, x_46);
x_49 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_50; 
x_50 = lean_st_ref_set(x_7, x_49);
x_34 = x_40;
goto block_39;
}
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
x_40 = x_61;
x_41 = x_60;
goto block_56;
}
block_80:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_78; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc_ref(x_65);
lean_dec_ref(x_64);
x_66 = lean_st_ref_take(x_7);
x_67 = lean_ctor_get(x_66, 1);
x_68 = lean_ctor_get(x_66, 2);
x_69 = lean_ctor_get(x_66, 3);
x_70 = lean_ctor_get(x_66, 4);
x_78 = !lean_is_exclusive(x_66);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_66, 0);
lean_dec(x_79);
x_71 = x_66;
x_72 = x_78;
goto block_77;
}
else
{
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_66);
x_71 = lean_box(0);
x_72 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_73; 
if (x_72 == 0)
{
lean_ctor_set(x_71, 0, x_65);
x_73 = x_71;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_76, 0, x_65);
lean_ctor_set(x_76, 1, x_67);
lean_ctor_set(x_76, 2, x_68);
lean_ctor_set(x_76, 3, x_69);
lean_ctor_set(x_76, 4, x_70);
x_73 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_74; 
x_74 = lean_st_ref_set(x_7, x_73);
x_34 = x_63;
goto block_39;
}
}
}
block_85:
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec_ref(x_81);
x_84 = lean_unbox(x_82);
lean_dec(x_82);
x_63 = x_84;
x_64 = x_83;
goto block_80;
}
block_102:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_100; 
x_88 = lean_st_ref_take(x_7);
x_89 = lean_ctor_get(x_88, 1);
x_90 = lean_ctor_get(x_88, 2);
x_91 = lean_ctor_get(x_88, 3);
x_92 = lean_ctor_get(x_88, 4);
x_100 = !lean_is_exclusive(x_88);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_88, 0);
lean_dec(x_101);
x_93 = x_88;
x_94 = x_100;
goto block_99;
}
else
{
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_88);
x_93 = lean_box(0);
x_94 = x_100;
goto block_99;
}
block_99:
{
lean_object* x_95; 
if (x_94 == 0)
{
lean_ctor_set(x_93, 0, x_87);
x_95 = x_93;
goto block_97;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_98, 0, x_87);
lean_ctor_set(x_98, 1, x_89);
lean_ctor_set(x_98, 2, x_90);
lean_ctor_set(x_98, 3, x_91);
lean_ctor_set(x_98, 4, x_92);
x_95 = x_98;
goto block_97;
}
block_97:
{
lean_object* x_96; 
x_96 = lean_st_ref_set(x_7, x_95);
x_34 = x_86;
goto block_39;
}
}
}
block_108:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec_ref(x_103);
x_106 = lean_ctor_get(x_104, 1);
lean_inc_ref(x_106);
lean_dec(x_104);
x_107 = lean_unbox(x_105);
lean_dec(x_105);
x_86 = x_107;
x_87 = x_106;
goto block_102;
}
}
}
block_22:
{
lean_object* x_16; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_15);
lean_ctor_set(x_12, 0, x_14);
x_16 = x_12;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_15);
x_16 = x_21;
goto block_20;
}
block_20:
{
size_t x_17; size_t x_18; 
x_17 = 1;
x_18 = lean_usize_add(x_5, x_17);
x_5 = x_18;
x_6 = x_16;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_1);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(x_9, x_2, x_3, x_10, x_11, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_173; 
x_14 = lean_ctor_get(x_6, 1);
x_173 = !lean_is_exclusive(x_6);
if (x_173 == 0)
{
lean_object* x_174; 
x_174 = lean_ctor_get(x_6, 0);
lean_dec(x_174);
x_15 = x_6;
x_16 = x_173;
goto block_172;
}
else
{
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = x_173;
goto block_172;
}
block_172:
{
lean_object* x_17; lean_object* x_18; lean_object* x_26; 
x_17 = lean_box(0);
x_26 = lean_array_uget_borrowed(x_3, x_5);
if (lean_obj_tag(x_26) == 0)
{
x_18 = x_14;
goto block_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_171; 
x_27 = lean_ctor_get(x_26, 0);
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
x_171 = !lean_is_exclusive(x_14);
if (x_171 == 0)
{
x_30 = x_14;
x_31 = x_171;
goto block_170;
}
else
{
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_box(0);
x_31 = x_171;
goto block_170;
}
block_170:
{
lean_object* x_36; uint8_t x_37; uint8_t x_43; lean_object* x_44; lean_object* x_60; uint8_t x_66; lean_object* x_67; lean_object* x_84; uint8_t x_89; lean_object* x_90; lean_object* x_106; uint8_t x_112; 
x_36 = l_Lean_LocalDecl_fvarId(x_27);
x_112 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_36, x_2);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_130; uint8_t x_163; uint8_t x_166; 
lean_inc(x_28);
x_113 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_113, 0, x_28);
x_166 = l_Lean_LocalDecl_isAuxDecl(x_27);
if (x_166 == 0)
{
uint8_t x_167; uint8_t x_168; 
x_167 = l_Lean_LocalDecl_binderInfo(x_27);
x_168 = l_Lean_BinderInfo_isInstImplicit(x_167);
x_163 = x_168;
goto block_165;
}
else
{
x_163 = x_166;
goto block_165;
}
block_122:
{
if (x_116 == 0)
{
uint8_t x_118; 
x_118 = l_Lean_Expr_hasFVar(x_115);
if (x_118 == 0)
{
uint8_t x_119; 
x_119 = l_Lean_Expr_hasMVar(x_115);
if (x_119 == 0)
{
lean_dec_ref(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
x_66 = x_119;
x_67 = x_117;
goto block_83;
}
else
{
lean_object* x_120; 
x_120 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_114, x_115, x_117);
x_84 = x_120;
goto block_88;
}
}
else
{
lean_object* x_121; 
x_121 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_114, x_115, x_117);
x_84 = x_121;
goto block_88;
}
}
else
{
lean_dec_ref(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
x_66 = x_116;
x_67 = x_117;
goto block_83;
}
}
block_129:
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec_ref(x_125);
x_128 = lean_unbox(x_126);
lean_dec(x_126);
x_114 = x_123;
x_115 = x_124;
x_116 = x_128;
x_117 = x_127;
goto block_122;
}
block_162:
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_box(x_130);
x_132 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(x_132, 0, x_131);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_133 = lean_ctor_get(x_27, 3);
x_134 = lean_st_ref_get(x_8);
x_135 = lean_ctor_get(x_134, 0);
lean_inc_ref(x_135);
lean_dec(x_134);
x_136 = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
lean_inc_ref(x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
x_138 = l_Lean_Expr_hasFVar(x_133);
if (x_138 == 0)
{
uint8_t x_139; 
x_139 = l_Lean_Expr_hasMVar(x_133);
if (x_139 == 0)
{
lean_dec_ref(x_137);
lean_dec_ref(x_132);
lean_dec_ref(x_113);
x_43 = x_139;
x_44 = x_135;
goto block_59;
}
else
{
lean_object* x_140; 
lean_dec_ref(x_135);
lean_inc_ref(x_133);
x_140 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_132, x_133, x_137);
x_60 = x_140;
goto block_65;
}
}
else
{
lean_object* x_141; 
lean_dec_ref(x_135);
lean_inc_ref(x_133);
x_141 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_132, x_133, x_137);
x_60 = x_141;
goto block_65;
}
}
else
{
uint8_t x_142; 
x_142 = lean_ctor_get_uint8(x_27, sizeof(void*)*5);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_143 = lean_ctor_get(x_27, 3);
x_144 = lean_ctor_get(x_27, 4);
x_145 = lean_st_ref_get(x_8);
x_146 = lean_ctor_get(x_145, 0);
lean_inc_ref(x_146);
lean_dec(x_145);
x_147 = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
x_149 = l_Lean_Expr_hasFVar(x_143);
if (x_149 == 0)
{
uint8_t x_150; 
x_150 = l_Lean_Expr_hasMVar(x_143);
if (x_150 == 0)
{
lean_inc_ref(x_144);
x_114 = x_132;
x_115 = x_144;
x_116 = x_150;
x_117 = x_148;
goto block_122;
}
else
{
lean_object* x_151; 
lean_inc_ref(x_143);
lean_inc_ref(x_132);
lean_inc_ref(x_113);
x_151 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_132, x_143, x_148);
lean_inc_ref(x_144);
x_123 = x_132;
x_124 = x_144;
x_125 = x_151;
goto block_129;
}
}
else
{
lean_object* x_152; 
lean_inc_ref(x_143);
lean_inc_ref(x_132);
lean_inc_ref(x_113);
x_152 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_132, x_143, x_148);
lean_inc_ref(x_144);
x_123 = x_132;
x_124 = x_144;
x_125 = x_152;
goto block_129;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_153 = lean_ctor_get(x_27, 3);
x_154 = lean_st_ref_get(x_8);
x_155 = lean_ctor_get(x_154, 0);
lean_inc_ref(x_155);
lean_dec(x_154);
x_156 = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
lean_inc_ref(x_155);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
x_158 = l_Lean_Expr_hasFVar(x_153);
if (x_158 == 0)
{
uint8_t x_159; 
x_159 = l_Lean_Expr_hasMVar(x_153);
if (x_159 == 0)
{
lean_dec_ref(x_157);
lean_dec_ref(x_132);
lean_dec_ref(x_113);
x_89 = x_159;
x_90 = x_155;
goto block_105;
}
else
{
lean_object* x_160; 
lean_dec_ref(x_155);
lean_inc_ref(x_153);
x_160 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_132, x_153, x_157);
x_106 = x_160;
goto block_111;
}
}
else
{
lean_object* x_161; 
lean_dec_ref(x_155);
lean_inc_ref(x_153);
x_161 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_132, x_153, x_157);
x_106 = x_161;
goto block_111;
}
}
}
}
block_165:
{
if (x_163 == 0)
{
if (x_1 == 0)
{
lean_del_object(x_30);
x_130 = x_1;
goto block_162;
}
else
{
uint8_t x_164; 
x_164 = l_Lean_LocalDecl_isLet(x_27, x_163);
if (x_164 == 0)
{
lean_del_object(x_30);
x_130 = x_164;
goto block_162;
}
else
{
lean_dec_ref(x_113);
lean_dec(x_36);
goto block_35;
}
}
}
else
{
lean_dec_ref(x_113);
lean_dec(x_36);
goto block_35;
}
}
}
else
{
lean_object* x_169; 
lean_dec(x_36);
lean_del_object(x_30);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_28);
lean_ctor_set(x_169, 1, x_29);
x_18 = x_169;
goto block_25;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
x_18 = x_32;
goto block_25;
}
}
block_42:
{
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_28);
lean_ctor_set(x_38, 1, x_29);
x_18 = x_38;
goto block_25;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_inc(x_36);
x_39 = l_Lean_FVarIdSet_insert(x_29, x_36);
x_40 = l_Lean_FVarIdSet_insert(x_28, x_36);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_18 = x_41;
goto block_25;
}
}
block_59:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_57; 
x_45 = lean_st_ref_take(x_8);
x_46 = lean_ctor_get(x_45, 1);
x_47 = lean_ctor_get(x_45, 2);
x_48 = lean_ctor_get(x_45, 3);
x_49 = lean_ctor_get(x_45, 4);
x_57 = !lean_is_exclusive(x_45);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_45, 0);
lean_dec(x_58);
x_50 = x_45;
x_51 = x_57;
goto block_56;
}
else
{
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_45);
x_50 = lean_box(0);
x_51 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_52; 
if (x_51 == 0)
{
lean_ctor_set(x_50, 0, x_44);
x_52 = x_50;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_55, 0, x_44);
lean_ctor_set(x_55, 1, x_46);
lean_ctor_set(x_55, 2, x_47);
lean_ctor_set(x_55, 3, x_48);
lean_ctor_set(x_55, 4, x_49);
x_52 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_53; 
x_53 = lean_st_ref_set(x_8, x_52);
x_37 = x_43;
goto block_42;
}
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
x_43 = x_64;
x_44 = x_63;
goto block_59;
}
block_83:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_81; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc_ref(x_68);
lean_dec_ref(x_67);
x_69 = lean_st_ref_take(x_8);
x_70 = lean_ctor_get(x_69, 1);
x_71 = lean_ctor_get(x_69, 2);
x_72 = lean_ctor_get(x_69, 3);
x_73 = lean_ctor_get(x_69, 4);
x_81 = !lean_is_exclusive(x_69);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_69, 0);
lean_dec(x_82);
x_74 = x_69;
x_75 = x_81;
goto block_80;
}
else
{
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_69);
x_74 = lean_box(0);
x_75 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_76; 
if (x_75 == 0)
{
lean_ctor_set(x_74, 0, x_68);
x_76 = x_74;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_79, 0, x_68);
lean_ctor_set(x_79, 1, x_70);
lean_ctor_set(x_79, 2, x_71);
lean_ctor_set(x_79, 3, x_72);
lean_ctor_set(x_79, 4, x_73);
x_76 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_77; 
x_77 = lean_st_ref_set(x_8, x_76);
x_37 = x_66;
goto block_42;
}
}
}
block_88:
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec_ref(x_84);
x_87 = lean_unbox(x_85);
lean_dec(x_85);
x_66 = x_87;
x_67 = x_86;
goto block_83;
}
block_105:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_103; 
x_91 = lean_st_ref_take(x_8);
x_92 = lean_ctor_get(x_91, 1);
x_93 = lean_ctor_get(x_91, 2);
x_94 = lean_ctor_get(x_91, 3);
x_95 = lean_ctor_get(x_91, 4);
x_103 = !lean_is_exclusive(x_91);
if (x_103 == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_91, 0);
lean_dec(x_104);
x_96 = x_91;
x_97 = x_103;
goto block_102;
}
else
{
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_91);
x_96 = lean_box(0);
x_97 = x_103;
goto block_102;
}
block_102:
{
lean_object* x_98; 
if (x_97 == 0)
{
lean_ctor_set(x_96, 0, x_90);
x_98 = x_96;
goto block_100;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_101, 0, x_90);
lean_ctor_set(x_101, 1, x_92);
lean_ctor_set(x_101, 2, x_93);
lean_ctor_set(x_101, 3, x_94);
lean_ctor_set(x_101, 4, x_95);
x_98 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_99; 
x_99 = lean_st_ref_set(x_8, x_98);
x_37 = x_89;
goto block_42;
}
}
}
block_111:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
lean_dec_ref(x_106);
x_109 = lean_ctor_get(x_107, 1);
lean_inc_ref(x_109);
lean_dec(x_107);
x_110 = lean_unbox(x_108);
lean_dec(x_108);
x_89 = x_110;
x_90 = x_109;
goto block_105;
}
}
}
block_25:
{
lean_object* x_19; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 1, x_18);
lean_ctor_set(x_15, 0, x_17);
x_19 = x_15;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_18);
x_19 = x_24;
goto block_23;
}
block_23:
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = 1;
x_21 = lean_usize_add(x_5, x_20);
x_22 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(x_1, x_2, x_3, x_4, x_21, x_19, x_8);
return x_22;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1(x_12, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_5, x_4);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_170; 
x_11 = lean_ctor_get(x_6, 1);
x_170 = !lean_is_exclusive(x_6);
if (x_170 == 0)
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_6, 0);
lean_dec(x_171);
x_12 = x_6;
x_13 = x_170;
goto block_169;
}
else
{
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_box(0);
x_13 = x_170;
goto block_169;
}
block_169:
{
lean_object* x_14; lean_object* x_15; lean_object* x_23; 
x_14 = lean_box(0);
x_23 = lean_array_uget_borrowed(x_3, x_5);
if (lean_obj_tag(x_23) == 0)
{
x_15 = x_11;
goto block_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_168; 
x_24 = lean_ctor_get(x_23, 0);
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
x_168 = !lean_is_exclusive(x_11);
if (x_168 == 0)
{
x_27 = x_11;
x_28 = x_168;
goto block_167;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_11);
x_27 = lean_box(0);
x_28 = x_168;
goto block_167;
}
block_167:
{
lean_object* x_33; uint8_t x_34; uint8_t x_40; lean_object* x_41; lean_object* x_57; uint8_t x_63; lean_object* x_64; lean_object* x_81; uint8_t x_86; lean_object* x_87; lean_object* x_103; uint8_t x_109; 
x_33 = l_Lean_LocalDecl_fvarId(x_24);
x_109 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_33, x_2);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_127; uint8_t x_160; uint8_t x_163; 
lean_inc(x_25);
x_110 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_110, 0, x_25);
x_163 = l_Lean_LocalDecl_isAuxDecl(x_24);
if (x_163 == 0)
{
uint8_t x_164; uint8_t x_165; 
x_164 = l_Lean_LocalDecl_binderInfo(x_24);
x_165 = l_Lean_BinderInfo_isInstImplicit(x_164);
x_160 = x_165;
goto block_162;
}
else
{
x_160 = x_163;
goto block_162;
}
block_119:
{
if (x_113 == 0)
{
uint8_t x_115; 
x_115 = l_Lean_Expr_hasFVar(x_112);
if (x_115 == 0)
{
uint8_t x_116; 
x_116 = l_Lean_Expr_hasMVar(x_112);
if (x_116 == 0)
{
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
x_63 = x_116;
x_64 = x_114;
goto block_80;
}
else
{
lean_object* x_117; 
x_117 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_111, x_112, x_114);
x_81 = x_117;
goto block_85;
}
}
else
{
lean_object* x_118; 
x_118 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_111, x_112, x_114);
x_81 = x_118;
goto block_85;
}
}
else
{
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
x_63 = x_113;
x_64 = x_114;
goto block_80;
}
}
block_126:
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec_ref(x_122);
x_125 = lean_unbox(x_123);
lean_dec(x_123);
x_111 = x_120;
x_112 = x_121;
x_113 = x_125;
x_114 = x_124;
goto block_119;
}
block_159:
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_box(x_127);
x_129 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(x_129, 0, x_128);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_130 = lean_ctor_get(x_24, 3);
x_131 = lean_st_ref_get(x_7);
x_132 = lean_ctor_get(x_131, 0);
lean_inc_ref(x_132);
lean_dec(x_131);
x_133 = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
lean_inc_ref(x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_132);
x_135 = l_Lean_Expr_hasFVar(x_130);
if (x_135 == 0)
{
uint8_t x_136; 
x_136 = l_Lean_Expr_hasMVar(x_130);
if (x_136 == 0)
{
lean_dec_ref(x_134);
lean_dec_ref(x_129);
lean_dec_ref(x_110);
x_40 = x_136;
x_41 = x_132;
goto block_56;
}
else
{
lean_object* x_137; 
lean_dec_ref(x_132);
lean_inc_ref(x_130);
x_137 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_129, x_130, x_134);
x_57 = x_137;
goto block_62;
}
}
else
{
lean_object* x_138; 
lean_dec_ref(x_132);
lean_inc_ref(x_130);
x_138 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_129, x_130, x_134);
x_57 = x_138;
goto block_62;
}
}
else
{
uint8_t x_139; 
x_139 = lean_ctor_get_uint8(x_24, sizeof(void*)*5);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_140 = lean_ctor_get(x_24, 3);
x_141 = lean_ctor_get(x_24, 4);
x_142 = lean_st_ref_get(x_7);
x_143 = lean_ctor_get(x_142, 0);
lean_inc_ref(x_143);
lean_dec(x_142);
x_144 = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_143);
x_146 = l_Lean_Expr_hasFVar(x_140);
if (x_146 == 0)
{
uint8_t x_147; 
x_147 = l_Lean_Expr_hasMVar(x_140);
if (x_147 == 0)
{
lean_inc_ref(x_141);
x_111 = x_129;
x_112 = x_141;
x_113 = x_147;
x_114 = x_145;
goto block_119;
}
else
{
lean_object* x_148; 
lean_inc_ref(x_140);
lean_inc_ref(x_129);
lean_inc_ref(x_110);
x_148 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_129, x_140, x_145);
lean_inc_ref(x_141);
x_120 = x_129;
x_121 = x_141;
x_122 = x_148;
goto block_126;
}
}
else
{
lean_object* x_149; 
lean_inc_ref(x_140);
lean_inc_ref(x_129);
lean_inc_ref(x_110);
x_149 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_129, x_140, x_145);
lean_inc_ref(x_141);
x_120 = x_129;
x_121 = x_141;
x_122 = x_149;
goto block_126;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_150 = lean_ctor_get(x_24, 3);
x_151 = lean_st_ref_get(x_7);
x_152 = lean_ctor_get(x_151, 0);
lean_inc_ref(x_152);
lean_dec(x_151);
x_153 = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
lean_inc_ref(x_152);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_152);
x_155 = l_Lean_Expr_hasFVar(x_150);
if (x_155 == 0)
{
uint8_t x_156; 
x_156 = l_Lean_Expr_hasMVar(x_150);
if (x_156 == 0)
{
lean_dec_ref(x_154);
lean_dec_ref(x_129);
lean_dec_ref(x_110);
x_86 = x_156;
x_87 = x_152;
goto block_102;
}
else
{
lean_object* x_157; 
lean_dec_ref(x_152);
lean_inc_ref(x_150);
x_157 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_129, x_150, x_154);
x_103 = x_157;
goto block_108;
}
}
else
{
lean_object* x_158; 
lean_dec_ref(x_152);
lean_inc_ref(x_150);
x_158 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_129, x_150, x_154);
x_103 = x_158;
goto block_108;
}
}
}
}
block_162:
{
if (x_160 == 0)
{
if (x_1 == 0)
{
lean_del_object(x_27);
x_127 = x_1;
goto block_159;
}
else
{
uint8_t x_161; 
x_161 = l_Lean_LocalDecl_isLet(x_24, x_160);
if (x_161 == 0)
{
lean_del_object(x_27);
x_127 = x_161;
goto block_159;
}
else
{
lean_dec_ref(x_110);
lean_dec(x_33);
goto block_32;
}
}
}
else
{
lean_dec_ref(x_110);
lean_dec(x_33);
goto block_32;
}
}
}
else
{
lean_object* x_166; 
lean_dec(x_33);
lean_del_object(x_27);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_25);
lean_ctor_set(x_166, 1, x_26);
x_15 = x_166;
goto block_22;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
x_15 = x_29;
goto block_22;
}
}
block_39:
{
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_26);
x_15 = x_35;
goto block_22;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_inc(x_33);
x_36 = l_Lean_FVarIdSet_insert(x_26, x_33);
x_37 = l_Lean_FVarIdSet_insert(x_25, x_33);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_15 = x_38;
goto block_22;
}
}
block_56:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_54; 
x_42 = lean_st_ref_take(x_7);
x_43 = lean_ctor_get(x_42, 1);
x_44 = lean_ctor_get(x_42, 2);
x_45 = lean_ctor_get(x_42, 3);
x_46 = lean_ctor_get(x_42, 4);
x_54 = !lean_is_exclusive(x_42);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_42, 0);
lean_dec(x_55);
x_47 = x_42;
x_48 = x_54;
goto block_53;
}
else
{
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_42);
x_47 = lean_box(0);
x_48 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_49; 
if (x_48 == 0)
{
lean_ctor_set(x_47, 0, x_41);
x_49 = x_47;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_41);
lean_ctor_set(x_52, 1, x_43);
lean_ctor_set(x_52, 2, x_44);
lean_ctor_set(x_52, 3, x_45);
lean_ctor_set(x_52, 4, x_46);
x_49 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_50; 
x_50 = lean_st_ref_set(x_7, x_49);
x_34 = x_40;
goto block_39;
}
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
x_40 = x_61;
x_41 = x_60;
goto block_56;
}
block_80:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_78; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc_ref(x_65);
lean_dec_ref(x_64);
x_66 = lean_st_ref_take(x_7);
x_67 = lean_ctor_get(x_66, 1);
x_68 = lean_ctor_get(x_66, 2);
x_69 = lean_ctor_get(x_66, 3);
x_70 = lean_ctor_get(x_66, 4);
x_78 = !lean_is_exclusive(x_66);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_66, 0);
lean_dec(x_79);
x_71 = x_66;
x_72 = x_78;
goto block_77;
}
else
{
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_66);
x_71 = lean_box(0);
x_72 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_73; 
if (x_72 == 0)
{
lean_ctor_set(x_71, 0, x_65);
x_73 = x_71;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_76, 0, x_65);
lean_ctor_set(x_76, 1, x_67);
lean_ctor_set(x_76, 2, x_68);
lean_ctor_set(x_76, 3, x_69);
lean_ctor_set(x_76, 4, x_70);
x_73 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_74; 
x_74 = lean_st_ref_set(x_7, x_73);
x_34 = x_63;
goto block_39;
}
}
}
block_85:
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec_ref(x_81);
x_84 = lean_unbox(x_82);
lean_dec(x_82);
x_63 = x_84;
x_64 = x_83;
goto block_80;
}
block_102:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_100; 
x_88 = lean_st_ref_take(x_7);
x_89 = lean_ctor_get(x_88, 1);
x_90 = lean_ctor_get(x_88, 2);
x_91 = lean_ctor_get(x_88, 3);
x_92 = lean_ctor_get(x_88, 4);
x_100 = !lean_is_exclusive(x_88);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_88, 0);
lean_dec(x_101);
x_93 = x_88;
x_94 = x_100;
goto block_99;
}
else
{
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_88);
x_93 = lean_box(0);
x_94 = x_100;
goto block_99;
}
block_99:
{
lean_object* x_95; 
if (x_94 == 0)
{
lean_ctor_set(x_93, 0, x_87);
x_95 = x_93;
goto block_97;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_98, 0, x_87);
lean_ctor_set(x_98, 1, x_89);
lean_ctor_set(x_98, 2, x_90);
lean_ctor_set(x_98, 3, x_91);
lean_ctor_set(x_98, 4, x_92);
x_95 = x_98;
goto block_97;
}
block_97:
{
lean_object* x_96; 
x_96 = lean_st_ref_set(x_7, x_95);
x_34 = x_86;
goto block_39;
}
}
}
block_108:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec_ref(x_103);
x_106 = lean_ctor_get(x_104, 1);
lean_inc_ref(x_106);
lean_dec(x_104);
x_107 = lean_unbox(x_105);
lean_dec(x_105);
x_86 = x_107;
x_87 = x_106;
goto block_102;
}
}
}
block_22:
{
lean_object* x_16; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_15);
lean_ctor_set(x_12, 0, x_14);
x_16 = x_12;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_15);
x_16 = x_21;
goto block_20;
}
block_20:
{
size_t x_17; size_t x_18; 
x_17 = 1;
x_18 = lean_usize_add(x_5, x_17);
x_5 = x_18;
x_6 = x_16;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_1);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(x_9, x_2, x_3, x_10, x_11, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_173; 
x_14 = lean_ctor_get(x_6, 1);
x_173 = !lean_is_exclusive(x_6);
if (x_173 == 0)
{
lean_object* x_174; 
x_174 = lean_ctor_get(x_6, 0);
lean_dec(x_174);
x_15 = x_6;
x_16 = x_173;
goto block_172;
}
else
{
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = x_173;
goto block_172;
}
block_172:
{
lean_object* x_17; lean_object* x_18; lean_object* x_26; 
x_17 = lean_box(0);
x_26 = lean_array_uget_borrowed(x_3, x_5);
if (lean_obj_tag(x_26) == 0)
{
x_18 = x_14;
goto block_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_171; 
x_27 = lean_ctor_get(x_26, 0);
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
x_171 = !lean_is_exclusive(x_14);
if (x_171 == 0)
{
x_30 = x_14;
x_31 = x_171;
goto block_170;
}
else
{
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_box(0);
x_31 = x_171;
goto block_170;
}
block_170:
{
lean_object* x_36; uint8_t x_37; uint8_t x_43; lean_object* x_44; lean_object* x_60; uint8_t x_66; lean_object* x_67; lean_object* x_84; uint8_t x_89; lean_object* x_90; lean_object* x_106; uint8_t x_112; 
x_36 = l_Lean_LocalDecl_fvarId(x_27);
x_112 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_36, x_2);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_130; uint8_t x_163; uint8_t x_166; 
lean_inc(x_28);
x_113 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_113, 0, x_28);
x_166 = l_Lean_LocalDecl_isAuxDecl(x_27);
if (x_166 == 0)
{
uint8_t x_167; uint8_t x_168; 
x_167 = l_Lean_LocalDecl_binderInfo(x_27);
x_168 = l_Lean_BinderInfo_isInstImplicit(x_167);
x_163 = x_168;
goto block_165;
}
else
{
x_163 = x_166;
goto block_165;
}
block_122:
{
if (x_116 == 0)
{
uint8_t x_118; 
x_118 = l_Lean_Expr_hasFVar(x_114);
if (x_118 == 0)
{
uint8_t x_119; 
x_119 = l_Lean_Expr_hasMVar(x_114);
if (x_119 == 0)
{
lean_dec_ref(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
x_66 = x_119;
x_67 = x_117;
goto block_83;
}
else
{
lean_object* x_120; 
x_120 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_115, x_114, x_117);
x_84 = x_120;
goto block_88;
}
}
else
{
lean_object* x_121; 
x_121 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_115, x_114, x_117);
x_84 = x_121;
goto block_88;
}
}
else
{
lean_dec_ref(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
x_66 = x_116;
x_67 = x_117;
goto block_83;
}
}
block_129:
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec_ref(x_125);
x_128 = lean_unbox(x_126);
lean_dec(x_126);
x_114 = x_123;
x_115 = x_124;
x_116 = x_128;
x_117 = x_127;
goto block_122;
}
block_162:
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_box(x_130);
x_132 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(x_132, 0, x_131);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_133 = lean_ctor_get(x_27, 3);
x_134 = lean_st_ref_get(x_8);
x_135 = lean_ctor_get(x_134, 0);
lean_inc_ref(x_135);
lean_dec(x_134);
x_136 = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
lean_inc_ref(x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
x_138 = l_Lean_Expr_hasFVar(x_133);
if (x_138 == 0)
{
uint8_t x_139; 
x_139 = l_Lean_Expr_hasMVar(x_133);
if (x_139 == 0)
{
lean_dec_ref(x_137);
lean_dec_ref(x_132);
lean_dec_ref(x_113);
x_43 = x_139;
x_44 = x_135;
goto block_59;
}
else
{
lean_object* x_140; 
lean_dec_ref(x_135);
lean_inc_ref(x_133);
x_140 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_132, x_133, x_137);
x_60 = x_140;
goto block_65;
}
}
else
{
lean_object* x_141; 
lean_dec_ref(x_135);
lean_inc_ref(x_133);
x_141 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_132, x_133, x_137);
x_60 = x_141;
goto block_65;
}
}
else
{
uint8_t x_142; 
x_142 = lean_ctor_get_uint8(x_27, sizeof(void*)*5);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_143 = lean_ctor_get(x_27, 3);
x_144 = lean_ctor_get(x_27, 4);
x_145 = lean_st_ref_get(x_8);
x_146 = lean_ctor_get(x_145, 0);
lean_inc_ref(x_146);
lean_dec(x_145);
x_147 = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
x_149 = l_Lean_Expr_hasFVar(x_143);
if (x_149 == 0)
{
uint8_t x_150; 
x_150 = l_Lean_Expr_hasMVar(x_143);
if (x_150 == 0)
{
lean_inc_ref(x_144);
x_114 = x_144;
x_115 = x_132;
x_116 = x_150;
x_117 = x_148;
goto block_122;
}
else
{
lean_object* x_151; 
lean_inc_ref(x_143);
lean_inc_ref(x_132);
lean_inc_ref(x_113);
x_151 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_132, x_143, x_148);
lean_inc_ref(x_144);
x_123 = x_144;
x_124 = x_132;
x_125 = x_151;
goto block_129;
}
}
else
{
lean_object* x_152; 
lean_inc_ref(x_143);
lean_inc_ref(x_132);
lean_inc_ref(x_113);
x_152 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_132, x_143, x_148);
lean_inc_ref(x_144);
x_123 = x_144;
x_124 = x_132;
x_125 = x_152;
goto block_129;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_153 = lean_ctor_get(x_27, 3);
x_154 = lean_st_ref_get(x_8);
x_155 = lean_ctor_get(x_154, 0);
lean_inc_ref(x_155);
lean_dec(x_154);
x_156 = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
lean_inc_ref(x_155);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
x_158 = l_Lean_Expr_hasFVar(x_153);
if (x_158 == 0)
{
uint8_t x_159; 
x_159 = l_Lean_Expr_hasMVar(x_153);
if (x_159 == 0)
{
lean_dec_ref(x_157);
lean_dec_ref(x_132);
lean_dec_ref(x_113);
x_89 = x_159;
x_90 = x_155;
goto block_105;
}
else
{
lean_object* x_160; 
lean_dec_ref(x_155);
lean_inc_ref(x_153);
x_160 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_132, x_153, x_157);
x_106 = x_160;
goto block_111;
}
}
else
{
lean_object* x_161; 
lean_dec_ref(x_155);
lean_inc_ref(x_153);
x_161 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_132, x_153, x_157);
x_106 = x_161;
goto block_111;
}
}
}
}
block_165:
{
if (x_163 == 0)
{
if (x_1 == 0)
{
lean_del_object(x_30);
x_130 = x_1;
goto block_162;
}
else
{
uint8_t x_164; 
x_164 = l_Lean_LocalDecl_isLet(x_27, x_163);
if (x_164 == 0)
{
lean_del_object(x_30);
x_130 = x_164;
goto block_162;
}
else
{
lean_dec_ref(x_113);
lean_dec(x_36);
goto block_35;
}
}
}
else
{
lean_dec_ref(x_113);
lean_dec(x_36);
goto block_35;
}
}
}
else
{
lean_object* x_169; 
lean_dec(x_36);
lean_del_object(x_30);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_28);
lean_ctor_set(x_169, 1, x_29);
x_18 = x_169;
goto block_25;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
x_18 = x_32;
goto block_25;
}
}
block_42:
{
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_28);
lean_ctor_set(x_38, 1, x_29);
x_18 = x_38;
goto block_25;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_inc(x_36);
x_39 = l_Lean_FVarIdSet_insert(x_29, x_36);
x_40 = l_Lean_FVarIdSet_insert(x_28, x_36);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_18 = x_41;
goto block_25;
}
}
block_59:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_57; 
x_45 = lean_st_ref_take(x_8);
x_46 = lean_ctor_get(x_45, 1);
x_47 = lean_ctor_get(x_45, 2);
x_48 = lean_ctor_get(x_45, 3);
x_49 = lean_ctor_get(x_45, 4);
x_57 = !lean_is_exclusive(x_45);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_45, 0);
lean_dec(x_58);
x_50 = x_45;
x_51 = x_57;
goto block_56;
}
else
{
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_45);
x_50 = lean_box(0);
x_51 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_52; 
if (x_51 == 0)
{
lean_ctor_set(x_50, 0, x_44);
x_52 = x_50;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_55, 0, x_44);
lean_ctor_set(x_55, 1, x_46);
lean_ctor_set(x_55, 2, x_47);
lean_ctor_set(x_55, 3, x_48);
lean_ctor_set(x_55, 4, x_49);
x_52 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_53; 
x_53 = lean_st_ref_set(x_8, x_52);
x_37 = x_43;
goto block_42;
}
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
x_43 = x_64;
x_44 = x_63;
goto block_59;
}
block_83:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_81; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc_ref(x_68);
lean_dec_ref(x_67);
x_69 = lean_st_ref_take(x_8);
x_70 = lean_ctor_get(x_69, 1);
x_71 = lean_ctor_get(x_69, 2);
x_72 = lean_ctor_get(x_69, 3);
x_73 = lean_ctor_get(x_69, 4);
x_81 = !lean_is_exclusive(x_69);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_69, 0);
lean_dec(x_82);
x_74 = x_69;
x_75 = x_81;
goto block_80;
}
else
{
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_69);
x_74 = lean_box(0);
x_75 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_76; 
if (x_75 == 0)
{
lean_ctor_set(x_74, 0, x_68);
x_76 = x_74;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_79, 0, x_68);
lean_ctor_set(x_79, 1, x_70);
lean_ctor_set(x_79, 2, x_71);
lean_ctor_set(x_79, 3, x_72);
lean_ctor_set(x_79, 4, x_73);
x_76 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_77; 
x_77 = lean_st_ref_set(x_8, x_76);
x_37 = x_66;
goto block_42;
}
}
}
block_88:
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec_ref(x_84);
x_87 = lean_unbox(x_85);
lean_dec(x_85);
x_66 = x_87;
x_67 = x_86;
goto block_83;
}
block_105:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_103; 
x_91 = lean_st_ref_take(x_8);
x_92 = lean_ctor_get(x_91, 1);
x_93 = lean_ctor_get(x_91, 2);
x_94 = lean_ctor_get(x_91, 3);
x_95 = lean_ctor_get(x_91, 4);
x_103 = !lean_is_exclusive(x_91);
if (x_103 == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_91, 0);
lean_dec(x_104);
x_96 = x_91;
x_97 = x_103;
goto block_102;
}
else
{
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_91);
x_96 = lean_box(0);
x_97 = x_103;
goto block_102;
}
block_102:
{
lean_object* x_98; 
if (x_97 == 0)
{
lean_ctor_set(x_96, 0, x_90);
x_98 = x_96;
goto block_100;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_101, 0, x_90);
lean_ctor_set(x_101, 1, x_92);
lean_ctor_set(x_101, 2, x_93);
lean_ctor_set(x_101, 3, x_94);
lean_ctor_set(x_101, 4, x_95);
x_98 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_99; 
x_99 = lean_st_ref_set(x_8, x_98);
x_37 = x_89;
goto block_42;
}
}
}
block_111:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
lean_dec_ref(x_106);
x_109 = lean_ctor_get(x_107, 1);
lean_inc_ref(x_109);
lean_dec(x_107);
x_110 = lean_unbox(x_108);
lean_dec(x_108);
x_89 = x_110;
x_90 = x_109;
goto block_105;
}
}
}
block_25:
{
lean_object* x_19; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 1, x_18);
lean_ctor_set(x_15, 0, x_17);
x_19 = x_15;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_18);
x_19 = x_24;
goto block_23;
}
block_23:
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = 1;
x_21 = lean_usize_add(x_5, x_20);
x_22 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(x_1, x_2, x_3, x_4, x_21, x_19, x_8);
return x_22;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2(x_12, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_45; 
x_11 = lean_ctor_get(x_4, 0);
x_45 = !lean_is_exclusive(x_4);
if (x_45 == 0)
{
x_12 = x_4;
x_13 = x_45;
goto block_44;
}
else
{
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_box(0);
x_13 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
x_16 = lean_array_size(x_11);
x_17 = 0;
x_18 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_11, x_16, x_17, x_15, x_6, x_7, x_8, x_9);
lean_dec_ref(x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_35; 
x_19 = lean_ctor_get(x_18, 0);
x_35 = !lean_is_exclusive(x_18);
if (x_35 == 0)
{
x_20 = x_18;
x_21 = x_35;
goto block_34;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_19, 0);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_23);
x_24 = x_12;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_23);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_24);
x_25 = x_20;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_inc_ref(x_22);
lean_dec(x_19);
lean_del_object(x_12);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec_ref(x_22);
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_30);
x_31 = x_20;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_43; 
lean_del_object(x_12);
x_36 = lean_ctor_get(x_18, 0);
x_43 = !lean_is_exclusive(x_18);
if (x_43 == 0)
{
x_37 = x_18;
x_38 = x_43;
goto block_42;
}
else
{
lean_inc(x_36);
lean_dec(x_18);
x_37 = lean_box(0);
x_38 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_39; 
if (x_38 == 0)
{
x_39 = x_37;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_36);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_80; 
x_46 = lean_ctor_get(x_4, 0);
x_80 = !lean_is_exclusive(x_4);
if (x_80 == 0)
{
x_47 = x_4;
x_48 = x_80;
goto block_79;
}
else
{
lean_inc(x_46);
lean_dec(x_4);
x_47 = lean_box(0);
x_48 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; lean_object* x_53; 
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_5);
x_51 = lean_array_size(x_46);
x_52 = 0;
x_53 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2(x_1, x_2, x_46, x_51, x_52, x_50, x_6, x_7, x_8, x_9);
lean_dec_ref(x_46);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_70; 
x_54 = lean_ctor_get(x_53, 0);
x_70 = !lean_is_exclusive(x_53);
if (x_70 == 0)
{
x_55 = x_53;
x_56 = x_70;
goto block_69;
}
else
{
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_box(0);
x_56 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_54, 0);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
if (x_48 == 0)
{
lean_ctor_set(x_47, 0, x_58);
x_59 = x_47;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_58);
x_59 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_60; 
if (x_56 == 0)
{
lean_ctor_set(x_55, 0, x_59);
x_60 = x_55;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_59);
x_60 = x_62;
goto block_61;
}
block_61:
{
return x_60;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_inc_ref(x_57);
lean_dec(x_54);
lean_del_object(x_47);
x_65 = lean_ctor_get(x_57, 0);
lean_inc(x_65);
lean_dec_ref(x_57);
if (x_56 == 0)
{
lean_ctor_set(x_55, 0, x_65);
x_66 = x_55;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_65);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_78; 
lean_del_object(x_47);
x_71 = lean_ctor_get(x_53, 0);
x_78 = !lean_is_exclusive(x_53);
if (x_78 == 0)
{
x_72 = x_53;
x_73 = x_78;
goto block_77;
}
else
{
lean_inc(x_71);
lean_dec(x_53);
x_72 = lean_box(0);
x_73 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_74; 
if (x_73 == 0)
{
x_74 = x_72;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_71);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_7);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_49; 
x_15 = lean_ctor_get(x_7, 1);
x_49 = !lean_is_exclusive(x_7);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_7, 0);
lean_dec(x_50);
x_16 = x_7;
x_17 = x_49;
goto block_48;
}
else
{
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_box(0);
x_17 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_uget_borrowed(x_4, x_6);
lean_inc(x_15);
lean_inc(x_18);
x_19 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(x_1, x_2, x_3, x_18, x_15, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_39; 
x_20 = lean_ctor_get(x_19, 0);
x_39 = !lean_is_exclusive(x_19);
if (x_39 == 0)
{
x_21 = x_19;
x_22 = x_39;
goto block_38;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_39;
goto block_38;
}
block_38:
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_20);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_23);
x_24 = x_16;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_15);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_24);
x_25 = x_21;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_del_object(x_21);
lean_dec(x_15);
x_30 = lean_ctor_get(x_20, 0);
lean_inc(x_30);
lean_dec_ref(x_20);
x_31 = lean_box(0);
if (x_17 == 0)
{
lean_ctor_set(x_16, 1, x_30);
lean_ctor_set(x_16, 0, x_31);
x_32 = x_16;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_30);
x_32 = x_37;
goto block_36;
}
block_36:
{
size_t x_33; size_t x_34; 
x_33 = 1;
x_34 = lean_usize_add(x_6, x_33);
x_6 = x_34;
x_7 = x_32;
goto _start;
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_47; 
lean_del_object(x_16);
lean_dec(x_15);
x_40 = lean_ctor_get(x_19, 0);
x_47 = !lean_is_exclusive(x_19);
if (x_47 == 0)
{
x_41 = x_19;
x_42 = x_47;
goto block_46;
}
else
{
lean_inc(x_40);
lean_dec(x_19);
x_41 = lean_box(0);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_42 == 0)
{
x_43 = x_41;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_40);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_1);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(x_13, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_3);
lean_inc_ref(x_4);
x_12 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(x_1, x_2, x_4, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_4);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_49; 
x_13 = lean_ctor_get(x_12, 0);
x_49 = !lean_is_exclusive(x_12);
if (x_49 == 0)
{
x_14 = x_12;
x_15 = x_49;
goto block_48;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_49;
goto block_48;
}
block_48:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_11);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec_ref(x_13);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_16);
x_17 = x_14;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
lean_del_object(x_14);
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
lean_dec_ref(x_13);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_array_size(x_11);
x_24 = 0;
x_25 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1(x_1, x_2, x_11, x_23, x_24, x_22, x_5, x_6, x_7, x_8);
lean_dec_ref(x_11);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_39; 
x_26 = lean_ctor_get(x_25, 0);
x_39 = !lean_is_exclusive(x_25);
if (x_39 == 0)
{
x_27 = x_25;
x_28 = x_39;
goto block_38;
}
else
{
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_26, 0);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_30);
x_31 = x_27;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_inc_ref(x_29);
lean_dec(x_26);
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
lean_dec_ref(x_29);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_34);
x_35 = x_27;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_47; 
x_40 = lean_ctor_get(x_25, 0);
x_47 = !lean_is_exclusive(x_25);
if (x_47 == 0)
{
x_41 = x_25;
x_42 = x_47;
goto block_46;
}
else
{
lean_inc(x_40);
lean_dec(x_25);
x_41 = lean_box(0);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_42 == 0)
{
x_43 = x_41;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_40);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_57; 
lean_dec_ref(x_11);
x_50 = lean_ctor_get(x_12, 0);
x_57 = !lean_is_exclusive(x_12);
if (x_57 == 0)
{
x_51 = x_12;
x_52 = x_57;
goto block_56;
}
else
{
lean_inc(x_50);
lean_dec(x_12);
x_51 = lean_box(0);
x_52 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_53; 
if (x_52 == 0)
{
x_53 = x_51;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_50);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
x_11 = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_uget_borrowed(x_1, x_2);
x_12 = l_Lean_Expr_isFVar(x_11);
if (x_12 == 0)
{
x_5 = x_4;
goto block_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Expr_fvarId_x21(x_11);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_9 = lean_box(1);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_array_get_size(x_1);
x_35 = lean_nat_dec_lt(x_33, x_34);
if (x_35 == 0)
{
x_10 = x_9;
goto block_32;
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_34, x_34);
if (x_36 == 0)
{
if (x_35 == 0)
{
x_10 = x_9;
goto block_32;
}
else
{
size_t x_37; size_t x_38; lean_object* x_39; 
x_37 = 0;
x_38 = lean_usize_of_nat(x_34);
x_39 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(x_1, x_37, x_38, x_9);
x_10 = x_39;
goto block_32;
}
}
else
{
size_t x_40; size_t x_41; lean_object* x_42; 
x_40 = 0;
x_41 = lean_usize_of_nat(x_34);
x_42 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(x_1, x_40, x_41, x_9);
x_10 = x_42;
goto block_32;
}
}
block_32:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 2);
x_12 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_9);
x_14 = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0(x_3, x_2, x_12, x_13, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_23; 
x_15 = lean_ctor_get(x_14, 0);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
x_16 = x_14;
x_17 = x_23;
goto block_22;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_18);
x_19 = x_16;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_31; 
x_24 = lean_ctor_get(x_14, 0);
x_31 = !lean_is_exclusive(x_14);
if (x_31 == 0)
{
x_25 = x_14;
x_26 = x_31;
goto block_30;
}
else
{
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4(x_12, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4(x_12, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(x_1, x_4);
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
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
lean_inc_ref(x_4);
x_11 = l_Lean_Meta_getFVarSetToGeneralize(x_1, x_10, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
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
x_15 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(x_14, x_12);
x_16 = l_Lean_Meta_sortFVarIds___redArg(x_15, x_4);
return x_16;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_27; 
lean_dec_ref(x_4);
x_20 = lean_ctor_get(x_11, 0);
x_27 = !lean_is_exclusive(x_11);
if (x_27 == 0)
{
x_21 = x_11;
x_22 = x_27;
goto block_26;
}
else
{
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_35; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_28 = lean_ctor_get(x_9, 0);
x_35 = !lean_is_exclusive(x_9);
if (x_35 == 0)
{
x_29 = x_9;
x_30 = x_35;
goto block_34;
}
else
{
lean_inc(x_28);
lean_dec(x_9);
x_29 = lean_box(0);
x_30 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_31; 
if (x_30 == 0)
{
x_31 = x_29;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_28);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(x_1, x_2);
return x_3;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_CollectFVars(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_GeneralizeVars(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectFVars(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_GeneralizeVars(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Util_CollectFVars(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_GeneralizeVars(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectFVars(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_GeneralizeVars(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_GeneralizeVars(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_GeneralizeVars(builtin);
}
#ifdef __cplusplus
}
#endif
