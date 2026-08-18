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
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_sortFVarIds___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0;
static lean_once_cell_t l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
static lean_once_cell_t l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2;
static const lean_array_object l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3 = (const lean_object*)&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; 
v___x_5_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5_, 0, v_e_1_);
return v___x_5_;
}
else
{
lean_object* v___x_6_; lean_object* v_mctx_7_; lean_object* v___x_8_; lean_object* v_fst_9_; lean_object* v_snd_10_; lean_object* v___x_11_; lean_object* v_cache_12_; lean_object* v_zetaDeltaFVarIds_13_; lean_object* v_postponed_14_; lean_object* v_diag_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v___x_6_ = lean_st_ref_get(v___y_2_);
v_mctx_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc_ref(v_mctx_7_);
lean_dec(v___x_6_);
v___x_8_ = l_Lean_instantiateMVarsCore(v_mctx_7_, v_e_1_);
v_fst_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_fst_9_);
v_snd_10_ = lean_ctor_get(v___x_8_, 1);
lean_inc(v_snd_10_);
lean_dec_ref(v___x_8_);
v___x_11_ = lean_st_ref_take(v___y_2_);
v_cache_12_ = lean_ctor_get(v___x_11_, 1);
v_zetaDeltaFVarIds_13_ = lean_ctor_get(v___x_11_, 2);
v_postponed_14_ = lean_ctor_get(v___x_11_, 3);
v_diag_15_ = lean_ctor_get(v___x_11_, 4);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_24_ == 0)
{
lean_object* v_unused_25_; 
v_unused_25_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_25_);
v___x_17_ = v___x_11_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_diag_15_);
lean_inc(v_postponed_14_);
lean_inc(v_zetaDeltaFVarIds_13_);
lean_inc(v_cache_12_);
lean_dec(v___x_11_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_20_; 
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v_snd_10_);
v___x_20_ = v___x_17_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_snd_10_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v_cache_12_);
lean_ctor_set(v_reuseFailAlloc_23_, 2, v_zetaDeltaFVarIds_13_);
lean_ctor_set(v_reuseFailAlloc_23_, 3, v_postponed_14_);
lean_ctor_set(v_reuseFailAlloc_23_, 4, v_diag_15_);
v___x_20_ = v_reuseFailAlloc_23_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_st_ref_put(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg___boxed(lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(v_e_26_, v___y_27_);
lean_dec(v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2(lean_object* v_e_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(v_e_30_, v___y_32_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___boxed(lean_object* v_e_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2(v_e_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
return v_res_43_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(lean_object* v_k_44_, lean_object* v_t_45_){
_start:
{
if (lean_obj_tag(v_t_45_) == 0)
{
lean_object* v_k_46_; lean_object* v_l_47_; lean_object* v_r_48_; uint8_t v___x_49_; 
v_k_46_ = lean_ctor_get(v_t_45_, 1);
v_l_47_ = lean_ctor_get(v_t_45_, 3);
v_r_48_ = lean_ctor_get(v_t_45_, 4);
v___x_49_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_44_, v_k_46_);
switch(v___x_49_)
{
case 0:
{
v_t_45_ = v_l_47_;
goto _start;
}
case 1:
{
uint8_t v___x_51_; 
v___x_51_ = 1;
return v___x_51_;
}
default: 
{
v_t_45_ = v_r_48_;
goto _start;
}
}
}
else
{
uint8_t v___x_53_; 
v___x_53_ = 0;
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg___boxed(lean_object* v_k_54_, lean_object* v_t_55_){
_start:
{
uint8_t v_res_56_; lean_object* v_r_57_; 
v_res_56_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v_k_54_, v_t_55_);
lean_dec(v_t_55_);
lean_dec(v_k_54_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(lean_object* v_init_58_, lean_object* v_x_59_){
_start:
{
if (lean_obj_tag(v_x_59_) == 0)
{
lean_object* v_k_61_; lean_object* v_l_62_; lean_object* v_r_63_; lean_object* v___x_64_; lean_object* v_a_65_; lean_object* v_a_66_; lean_object* v_fst_67_; lean_object* v_snd_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_83_; 
v_k_61_ = lean_ctor_get(v_x_59_, 1);
lean_inc(v_k_61_);
v_l_62_ = lean_ctor_get(v_x_59_, 3);
lean_inc(v_l_62_);
v_r_63_ = lean_ctor_get(v_x_59_, 4);
lean_inc(v_r_63_);
lean_dec_ref_known(v_x_59_, 5);
v___x_64_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(v_init_58_, v_l_62_);
v_a_65_ = lean_ctor_get(v___x_64_, 0);
lean_inc(v_a_65_);
lean_dec_ref(v___x_64_);
v_a_66_ = lean_ctor_get(v_a_65_, 0);
lean_inc(v_a_66_);
lean_dec(v_a_65_);
v_fst_67_ = lean_ctor_get(v_a_66_, 0);
v_snd_68_ = lean_ctor_get(v_a_66_, 1);
v_isSharedCheck_83_ = !lean_is_exclusive(v_a_66_);
if (v_isSharedCheck_83_ == 0)
{
v___x_70_ = v_a_66_;
v_isShared_71_ = v_isSharedCheck_83_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_snd_68_);
lean_inc(v_fst_67_);
lean_dec(v_a_66_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_83_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
uint8_t v___x_72_; 
v___x_72_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v_k_61_, v_snd_68_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_76_; 
lean_inc(v_k_61_);
v___x_73_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_73_, 0, v_k_61_);
lean_ctor_set(v___x_73_, 1, v_fst_67_);
v___x_74_ = l_Lean_FVarIdSet_insert(v_snd_68_, v_k_61_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 1, v___x_74_);
lean_ctor_set(v___x_70_, 0, v___x_73_);
v___x_76_ = v___x_70_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_73_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v___x_74_);
v___x_76_ = v_reuseFailAlloc_78_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
v_init_58_ = v___x_76_;
v_x_59_ = v_r_63_;
goto _start;
}
}
else
{
lean_object* v___x_80_; 
lean_dec(v_k_61_);
if (v_isShared_71_ == 0)
{
v___x_80_ = v___x_70_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_fst_67_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v_snd_68_);
v___x_80_ = v_reuseFailAlloc_82_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
v_init_58_ = v___x_80_;
v_x_59_ = v_r_63_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_84_, 0, v_init_58_);
v___x_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
return v___x_85_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg___boxed(lean_object* v_init_86_, lean_object* v_x_87_, lean_object* v___y_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(v_init_86_, v_x_87_);
return v_res_89_;
}
}
static lean_object* _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0(void){
_start:
{
lean_object* v_cellCount_90_; lean_object* v___x_91_; 
v_cellCount_90_ = lean_unsigned_to_nat(16u);
v___x_91_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_90_);
return v___x_91_;
}
}
static lean_object* _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1(void){
_start:
{
lean_object* v_cellCount_92_; lean_object* v___x_93_; 
v_cellCount_92_ = lean_unsigned_to_nat(16u);
v___x_93_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_92_);
return v___x_93_;
}
}
static lean_object* _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_94_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_95_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0);
v___x_96_ = lean_unsigned_to_nat(0u);
v___x_97_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v___x_95_);
lean_ctor_set(v___x_97_, 2, v___x_94_);
return v___x_97_;
}
}
static lean_object* _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_100_ = ((lean_object*)(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3));
v___x_101_ = lean_box(1);
v___x_102_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2);
v___x_103_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v___x_101_);
lean_ctor_set(v___x_103_, 2, v___x_100_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit(lean_object* v_fvarId_104_, lean_object* v_todo_105_, lean_object* v_s_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
lean_object* v_a_113_; lean_object* v_s_x27_125_; lean_object* v___y_126_; lean_object* v___y_127_; lean_object* v___y_128_; lean_object* v___y_129_; lean_object* v___x_135_; 
v___x_135_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_104_, v_a_107_, v_a_109_, v_a_110_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v_a_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v_a_139_; lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; lean_object* v___x_143_; 
v_a_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_a_136_);
lean_dec_ref_known(v___x_135_, 1);
v___x_137_ = l_Lean_LocalDecl_type(v_a_136_);
v___x_138_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(v___x_137_, v_a_108_);
v_a_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_a_139_);
lean_dec_ref(v___x_138_);
v___x_140_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__4);
v___x_141_ = l_Lean_collectFVars(v___x_140_, v_a_139_);
v___x_142_ = 0;
v___x_143_ = l_Lean_LocalDecl_value_x3f(v_a_136_, v___x_142_);
lean_dec(v_a_136_);
if (lean_obj_tag(v___x_143_) == 1)
{
lean_object* v_val_144_; lean_object* v___x_145_; lean_object* v_a_146_; lean_object* v___x_147_; 
v_val_144_ = lean_ctor_get(v___x_143_, 0);
lean_inc(v_val_144_);
lean_dec_ref_known(v___x_143_, 1);
v___x_145_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(v_val_144_, v_a_108_);
v_a_146_ = lean_ctor_get(v___x_145_, 0);
lean_inc(v_a_146_);
lean_dec_ref(v___x_145_);
v___x_147_ = l_Lean_collectFVars(v___x_141_, v_a_146_);
v_s_x27_125_ = v___x_147_;
v___y_126_ = v_a_107_;
v___y_127_ = v_a_108_;
v___y_128_ = v_a_109_;
v___y_129_ = v_a_110_;
goto v___jp_124_;
}
else
{
lean_dec(v___x_143_);
v_s_x27_125_ = v___x_141_;
v___y_126_ = v_a_107_;
v___y_127_ = v_a_108_;
v___y_128_ = v_a_109_;
v___y_129_ = v_a_110_;
goto v___jp_124_;
}
}
else
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
lean_dec(v_s_106_);
lean_dec(v_todo_105_);
v_a_148_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_155_ == 0)
{
v___x_150_ = v___x_135_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___x_135_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_a_148_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
v___jp_112_:
{
lean_object* v_fst_114_; lean_object* v_snd_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_123_; 
v_fst_114_ = lean_ctor_get(v_a_113_, 0);
v_snd_115_ = lean_ctor_get(v_a_113_, 1);
v_isSharedCheck_123_ = !lean_is_exclusive(v_a_113_);
if (v_isSharedCheck_123_ == 0)
{
v___x_117_ = v_a_113_;
v_isShared_118_ = v_isSharedCheck_123_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_snd_115_);
lean_inc(v_fst_114_);
lean_dec(v_a_113_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_123_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_120_; 
if (v_isShared_118_ == 0)
{
v___x_120_ = v___x_117_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_fst_114_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v_snd_115_);
v___x_120_ = v_reuseFailAlloc_122_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
lean_object* v___x_121_; 
v___x_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
return v___x_121_;
}
}
}
v___jp_124_:
{
lean_object* v_fvarSet_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v_a_133_; lean_object* v_a_134_; 
v_fvarSet_130_ = lean_ctor_get(v_s_x27_125_, 1);
lean_inc(v_fvarSet_130_);
lean_dec_ref(v_s_x27_125_);
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v_todo_105_);
lean_ctor_set(v___x_131_, 1, v_s_106_);
v___x_132_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(v___x_131_, v_fvarSet_130_);
v_a_133_ = lean_ctor_get(v___x_132_, 0);
lean_inc(v_a_133_);
lean_dec_ref(v___x_132_);
v_a_134_ = lean_ctor_get(v_a_133_, 0);
lean_inc(v_a_134_);
lean_dec(v_a_133_);
v_a_113_ = v_a_134_;
goto v___jp_112_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___boxed(lean_object* v_fvarId_156_, lean_object* v_todo_157_, lean_object* v_s_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit(v_fvarId_156_, v_todo_157_, v_s_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
return v_res_164_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0(lean_object* v_00_u03b2_165_, lean_object* v_k_166_, lean_object* v_t_167_){
_start:
{
uint8_t v___x_168_; 
v___x_168_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v_k_166_, v_t_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___boxed(lean_object* v_00_u03b2_169_, lean_object* v_k_170_, lean_object* v_t_171_){
_start:
{
uint8_t v_res_172_; lean_object* v_r_173_; 
v_res_172_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0(v_00_u03b2_169_, v_k_170_, v_t_171_);
lean_dec(v_t_171_);
lean_dec(v_k_170_);
v_r_173_ = lean_box(v_res_172_);
return v_r_173_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1(lean_object* v_init_174_, lean_object* v_x_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(v_init_174_, v_x_175_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___boxed(lean_object* v_init_182_, lean_object* v_x_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1(v_init_182_, v_x_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop(lean_object* v_todo_190_, lean_object* v_s_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
if (lean_obj_tag(v_todo_190_) == 0)
{
lean_object* v___x_197_; 
v___x_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_197_, 0, v_s_191_);
return v___x_197_;
}
else
{
lean_object* v_head_198_; lean_object* v_tail_199_; uint8_t v___x_200_; 
v_head_198_ = lean_ctor_get(v_todo_190_, 0);
lean_inc(v_head_198_);
v_tail_199_ = lean_ctor_get(v_todo_190_, 1);
lean_inc(v_tail_199_);
lean_dec_ref_known(v_todo_190_, 2);
v___x_200_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v_head_198_, v_s_191_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; 
lean_inc(v_head_198_);
v___x_201_ = l_Lean_FVarIdSet_insert(v_s_191_, v_head_198_);
v___x_202_ = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit(v_head_198_, v_tail_199_, v___x_201_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_203_; lean_object* v_fst_204_; lean_object* v_snd_205_; 
v_a_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_a_203_);
lean_dec_ref_known(v___x_202_, 1);
v_fst_204_ = lean_ctor_get(v_a_203_, 0);
lean_inc(v_fst_204_);
v_snd_205_ = lean_ctor_get(v_a_203_, 1);
lean_inc(v_snd_205_);
lean_dec(v_a_203_);
v_todo_190_ = v_fst_204_;
v_s_191_ = v_snd_205_;
goto _start;
}
else
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_214_; 
v_a_207_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_214_ == 0)
{
v___x_209_ = v___x_202_;
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_202_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_a_207_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
else
{
lean_dec(v_head_198_);
v_todo_190_ = v_tail_199_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop___boxed(lean_object* v_todo_216_, lean_object* v_s_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop(v_todo_216_, v_s_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0(lean_object* v_as_224_, size_t v_sz_225_, size_t v_i_226_, lean_object* v_b_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_a_234_; uint8_t v___x_238_; 
v___x_238_ = lean_usize_dec_lt(v_i_226_, v_sz_225_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; 
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v_b_227_);
return v___x_239_;
}
else
{
lean_object* v_fst_240_; lean_object* v_snd_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_276_; 
v_fst_240_ = lean_ctor_get(v_b_227_, 0);
v_snd_241_ = lean_ctor_get(v_b_227_, 1);
v_isSharedCheck_276_ = !lean_is_exclusive(v_b_227_);
if (v_isSharedCheck_276_ == 0)
{
v___x_243_ = v_b_227_;
v_isShared_244_ = v_isSharedCheck_276_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_snd_241_);
lean_inc(v_fst_240_);
lean_dec(v_b_227_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_276_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v_a_245_; uint8_t v___x_246_; 
v_a_245_ = lean_array_uget_borrowed(v_as_224_, v_i_226_);
v___x_246_ = l_Lean_Expr_isFVar(v_a_245_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; 
lean_inc(v___y_231_);
lean_inc_ref(v___y_230_);
lean_inc(v___y_229_);
lean_inc_ref(v___y_228_);
lean_inc(v_a_245_);
v___x_247_ = lean_infer_type(v_a_245_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v_a_248_; lean_object* v___x_249_; 
v_a_248_ = lean_ctor_get(v___x_247_, 0);
lean_inc(v_a_248_);
lean_dec_ref_known(v___x_247_, 1);
v___x_249_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(v_a_248_, v___y_229_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v___x_251_; lean_object* v___x_253_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_a_250_);
lean_dec_ref_known(v___x_249_, 1);
v___x_251_ = l_Lean_collectFVars(v_fst_240_, v_a_250_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v___x_251_);
v___x_253_ = v___x_243_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_snd_241_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
v_a_234_ = v___x_253_;
goto v___jp_233_;
}
}
else
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
lean_del_object(v___x_243_);
lean_dec(v_snd_241_);
lean_dec(v_fst_240_);
v_a_255_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_249_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_249_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
else
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
lean_del_object(v___x_243_);
lean_dec(v_snd_241_);
lean_dec(v_fst_240_);
v_a_263_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_247_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_247_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
else
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_271_ = l_Lean_Expr_fvarId_x21(v_a_245_);
v___x_272_ = lean_array_push(v_snd_241_, v___x_271_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 1, v___x_272_);
v___x_274_ = v___x_243_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_fst_240_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v___x_272_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
v_a_234_ = v___x_274_;
goto v___jp_233_;
}
}
}
}
v___jp_233_:
{
size_t v___x_235_; size_t v___x_236_; 
v___x_235_ = ((size_t)1ULL);
v___x_236_ = lean_usize_add(v_i_226_, v___x_235_);
v_i_226_ = v___x_236_;
v_b_227_ = v_a_234_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0___boxed(lean_object* v_as_277_, lean_object* v_sz_278_, lean_object* v_i_279_, lean_object* v_b_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
size_t v_sz_boxed_286_; size_t v_i_boxed_287_; lean_object* v_res_288_; 
v_sz_boxed_286_ = lean_unbox_usize(v_sz_278_);
lean_dec(v_sz_278_);
v_i_boxed_287_ = lean_unbox_usize(v_i_279_);
lean_dec(v_i_279_);
v_res_288_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0(v_as_277_, v_sz_boxed_286_, v_i_boxed_287_, v_b_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec_ref(v_as_277_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet(lean_object* v_targets_289_, lean_object* v_forbidden_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
lean_object* v___x_296_; lean_object* v_todo_297_; lean_object* v_s_298_; lean_object* v___x_299_; size_t v_sz_300_; size_t v___x_301_; lean_object* v___x_302_; 
v___x_296_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2);
v_todo_297_ = ((lean_object*)(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3));
v_s_298_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_s_298_, 0, v___x_296_);
lean_ctor_set(v_s_298_, 1, v_forbidden_290_);
lean_ctor_set(v_s_298_, 2, v_todo_297_);
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v_s_298_);
lean_ctor_set(v___x_299_, 1, v_todo_297_);
v_sz_300_ = lean_array_size(v_targets_289_);
v___x_301_ = ((size_t)0ULL);
v___x_302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0(v_targets_289_, v_sz_300_, v___x_301_, v___x_299_, v_a_291_, v_a_292_, v_a_293_, v_a_294_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v_fst_304_; lean_object* v_snd_305_; lean_object* v_fvarSet_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_a_303_);
lean_dec_ref_known(v___x_302_, 1);
v_fst_304_ = lean_ctor_get(v_a_303_, 0);
lean_inc(v_fst_304_);
v_snd_305_ = lean_ctor_get(v_a_303_, 1);
lean_inc(v_snd_305_);
lean_dec(v_a_303_);
v_fvarSet_306_ = lean_ctor_get(v_fst_304_, 1);
lean_inc(v_fvarSet_306_);
lean_dec(v_fst_304_);
v___x_307_ = lean_array_to_list(v_snd_305_);
v___x_308_ = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop(v___x_307_, v_fvarSet_306_, v_a_291_, v_a_292_, v_a_293_, v_a_294_);
return v___x_308_;
}
else
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
v_a_309_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_316_ == 0)
{
v___x_311_ = v___x_302_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_302_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_309_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet___boxed(lean_object* v_targets_317_, lean_object* v_forbidden_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_Meta_mkGeneralizationForbiddenSet(v_targets_317_, v_forbidden_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec_ref(v_targets_317_);
return v_res_324_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1(uint8_t v___y_325_, lean_object* v_x_326_){
_start:
{
return v___y_325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed(lean_object* v___y_327_, lean_object* v_x_328_){
_start:
{
uint8_t v___y_9894__boxed_329_; uint8_t v_res_330_; lean_object* v_r_331_; 
v___y_9894__boxed_329_ = lean_unbox(v___y_327_);
v_res_330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1(v___y_9894__boxed_329_, v_x_328_);
lean_dec(v_x_328_);
v_r_331_ = lean_box(v_res_330_);
return v_r_331_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0(lean_object* v_fst_332_, lean_object* v_x_333_){
_start:
{
uint8_t v___x_334_; 
v___x_334_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v_x_333_, v_fst_332_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed(lean_object* v_fst_335_, lean_object* v_x_336_){
_start:
{
uint8_t v_res_337_; lean_object* v_r_338_; 
v_res_337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0(v_fst_335_, v_x_336_);
lean_dec(v_x_336_);
lean_dec(v_fst_335_);
v_r_338_ = lean_box(v_res_337_);
return v_r_338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(uint8_t v_ignoreLetDecls_339_, lean_object* v_forbidden_340_, lean_object* v_as_341_, size_t v_sz_342_, size_t v_i_343_, lean_object* v_b_344_, lean_object* v___y_345_){
_start:
{
uint8_t v___x_347_; 
v___x_347_ = lean_usize_dec_lt(v_i_343_, v_sz_342_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; 
v___x_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_348_, 0, v_b_344_);
return v___x_348_;
}
else
{
lean_object* v_snd_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_508_; 
v_snd_349_ = lean_ctor_get(v_b_344_, 1);
v_isSharedCheck_508_ = !lean_is_exclusive(v_b_344_);
if (v_isSharedCheck_508_ == 0)
{
lean_object* v_unused_509_; 
v_unused_509_ = lean_ctor_get(v_b_344_, 0);
lean_dec(v_unused_509_);
v___x_351_ = v_b_344_;
v_isShared_352_ = v_isSharedCheck_508_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_snd_349_);
lean_dec(v_b_344_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_508_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_353_; lean_object* v_a_355_; lean_object* v_a_362_; 
v___x_353_ = lean_box(0);
v_a_362_ = lean_array_uget_borrowed(v_as_341_, v_i_343_);
if (lean_obj_tag(v_a_362_) == 0)
{
v_a_355_ = v_snd_349_;
goto v___jp_354_;
}
else
{
lean_object* v_val_363_; lean_object* v_fst_364_; lean_object* v_snd_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_507_; 
v_val_363_ = lean_ctor_get(v_a_362_, 0);
v_fst_364_ = lean_ctor_get(v_snd_349_, 0);
v_snd_365_ = lean_ctor_get(v_snd_349_, 1);
v_isSharedCheck_507_ = !lean_is_exclusive(v_snd_349_);
if (v_isSharedCheck_507_ == 0)
{
v___x_367_ = v_snd_349_;
v_isShared_368_ = v_isSharedCheck_507_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_snd_365_);
lean_inc(v_fst_364_);
lean_dec(v_snd_349_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_507_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_373_; uint8_t v_a_375_; uint8_t v_fst_381_; lean_object* v_mctx_382_; lean_object* v___y_398_; uint8_t v_fst_404_; lean_object* v_snd_405_; lean_object* v___y_422_; uint8_t v_fst_427_; lean_object* v_mctx_428_; lean_object* v___y_444_; uint8_t v___x_449_; 
v___x_373_ = l_Lean_LocalDecl_fvarId(v_val_363_);
v___x_449_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v___x_373_, v_forbidden_340_);
if (v___x_449_ == 0)
{
lean_object* v___f_450_; lean_object* v___y_452_; lean_object* v___y_453_; uint8_t v_fst_454_; lean_object* v_snd_455_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___y_463_; uint8_t v___y_468_; uint8_t v___y_501_; uint8_t v___x_503_; 
lean_inc(v_fst_364_);
v___f_450_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_450_, 0, v_fst_364_);
v___x_503_ = l_Lean_LocalDecl_isAuxDecl(v_val_363_);
if (v___x_503_ == 0)
{
uint8_t v___x_504_; uint8_t v___x_505_; 
v___x_504_ = l_Lean_LocalDecl_binderInfo(v_val_363_);
v___x_505_ = l_Lean_BinderInfo_isInstImplicit(v___x_504_);
v___y_501_ = v___x_505_;
goto v___jp_500_;
}
else
{
v___y_501_ = v___x_503_;
goto v___jp_500_;
}
v___jp_451_:
{
if (v_fst_454_ == 0)
{
uint8_t v___x_456_; 
v___x_456_ = l_Lean_Expr_hasFVar(v___y_453_);
if (v___x_456_ == 0)
{
uint8_t v___x_457_; 
v___x_457_ = l_Lean_Expr_hasMVar(v___y_453_);
if (v___x_457_ == 0)
{
lean_dec_ref(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec_ref(v___f_450_);
v_fst_404_ = v___x_457_;
v_snd_405_ = v_snd_455_;
goto v___jp_403_;
}
else
{
lean_object* v___x_458_; 
v___x_458_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_450_, v___y_452_, v___y_453_, v_snd_455_);
v___y_422_ = v___x_458_;
goto v___jp_421_;
}
}
else
{
lean_object* v___x_459_; 
v___x_459_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_450_, v___y_452_, v___y_453_, v_snd_455_);
v___y_422_ = v___x_459_;
goto v___jp_421_;
}
}
else
{
lean_dec_ref(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec_ref(v___f_450_);
v_fst_404_ = v_fst_454_;
v_snd_405_ = v_snd_455_;
goto v___jp_403_;
}
}
v___jp_460_:
{
lean_object* v_fst_464_; lean_object* v_snd_465_; uint8_t v___x_466_; 
v_fst_464_ = lean_ctor_get(v___y_463_, 0);
lean_inc(v_fst_464_);
v_snd_465_ = lean_ctor_get(v___y_463_, 1);
lean_inc(v_snd_465_);
lean_dec_ref(v___y_463_);
v___x_466_ = lean_unbox(v_fst_464_);
lean_dec(v_fst_464_);
v___y_452_ = v___y_461_;
v___y_453_ = v___y_462_;
v_fst_454_ = v___x_466_;
v_snd_455_ = v_snd_465_;
goto v___jp_451_;
}
v___jp_467_:
{
lean_object* v___x_469_; lean_object* v___f_470_; 
v___x_469_ = lean_box(v___y_468_);
v___f_470_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(v___f_470_, 0, v___x_469_);
if (lean_obj_tag(v_val_363_) == 0)
{
lean_object* v_type_471_; lean_object* v___x_472_; lean_object* v_mctx_473_; lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v_type_471_ = lean_ctor_get(v_val_363_, 3);
v___x_472_ = lean_st_ref_get(v___y_345_);
v_mctx_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc_ref_n(v_mctx_473_, 2);
lean_dec(v___x_472_);
v___x_474_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2);
v___x_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
lean_ctor_set(v___x_475_, 1, v_mctx_473_);
v___x_476_ = l_Lean_Expr_hasFVar(v_type_471_);
if (v___x_476_ == 0)
{
uint8_t v___x_477_; 
v___x_477_ = l_Lean_Expr_hasMVar(v_type_471_);
if (v___x_477_ == 0)
{
lean_dec_ref_known(v___x_475_, 2);
lean_dec_ref(v___f_470_);
lean_dec_ref(v___f_450_);
v_fst_381_ = v___x_477_;
v_mctx_382_ = v_mctx_473_;
goto v___jp_380_;
}
else
{
lean_object* v___x_478_; 
lean_dec_ref(v_mctx_473_);
lean_inc_ref(v_type_471_);
v___x_478_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_450_, v___f_470_, v_type_471_, v___x_475_);
v___y_398_ = v___x_478_;
goto v___jp_397_;
}
}
else
{
lean_object* v___x_479_; 
lean_dec_ref(v_mctx_473_);
lean_inc_ref(v_type_471_);
v___x_479_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_450_, v___f_470_, v_type_471_, v___x_475_);
v___y_398_ = v___x_479_;
goto v___jp_397_;
}
}
else
{
uint8_t v_nondep_480_; 
v_nondep_480_ = lean_ctor_get_uint8(v_val_363_, sizeof(void*)*5);
if (v_nondep_480_ == 0)
{
lean_object* v_type_481_; lean_object* v_value_482_; lean_object* v___x_483_; lean_object* v_mctx_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v_type_481_ = lean_ctor_get(v_val_363_, 3);
v_value_482_ = lean_ctor_get(v_val_363_, 4);
v___x_483_ = lean_st_ref_get(v___y_345_);
v_mctx_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc_ref(v_mctx_484_);
lean_dec(v___x_483_);
v___x_485_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2);
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v_mctx_484_);
v___x_487_ = l_Lean_Expr_hasFVar(v_type_481_);
if (v___x_487_ == 0)
{
uint8_t v___x_488_; 
v___x_488_ = l_Lean_Expr_hasMVar(v_type_481_);
if (v___x_488_ == 0)
{
lean_inc_ref(v_value_482_);
v___y_452_ = v___f_470_;
v___y_453_ = v_value_482_;
v_fst_454_ = v___x_488_;
v_snd_455_ = v___x_486_;
goto v___jp_451_;
}
else
{
lean_object* v___x_489_; 
lean_inc_ref(v_type_481_);
lean_inc_ref(v___f_470_);
lean_inc_ref(v___f_450_);
v___x_489_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_450_, v___f_470_, v_type_481_, v___x_486_);
lean_inc_ref(v_value_482_);
v___y_461_ = v___f_470_;
v___y_462_ = v_value_482_;
v___y_463_ = v___x_489_;
goto v___jp_460_;
}
}
else
{
lean_object* v___x_490_; 
lean_inc_ref(v_type_481_);
lean_inc_ref(v___f_470_);
lean_inc_ref(v___f_450_);
v___x_490_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_450_, v___f_470_, v_type_481_, v___x_486_);
lean_inc_ref(v_value_482_);
v___y_461_ = v___f_470_;
v___y_462_ = v_value_482_;
v___y_463_ = v___x_490_;
goto v___jp_460_;
}
}
else
{
lean_object* v_type_491_; lean_object* v___x_492_; lean_object* v_mctx_493_; lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v_type_491_ = lean_ctor_get(v_val_363_, 3);
v___x_492_ = lean_st_ref_get(v___y_345_);
v_mctx_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc_ref_n(v_mctx_493_, 2);
lean_dec(v___x_492_);
v___x_494_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2);
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v_mctx_493_);
v___x_496_ = l_Lean_Expr_hasFVar(v_type_491_);
if (v___x_496_ == 0)
{
uint8_t v___x_497_; 
v___x_497_ = l_Lean_Expr_hasMVar(v_type_491_);
if (v___x_497_ == 0)
{
lean_dec_ref_known(v___x_495_, 2);
lean_dec_ref(v___f_470_);
lean_dec_ref(v___f_450_);
v_fst_427_ = v___x_497_;
v_mctx_428_ = v_mctx_493_;
goto v___jp_426_;
}
else
{
lean_object* v___x_498_; 
lean_dec_ref(v_mctx_493_);
lean_inc_ref(v_type_491_);
v___x_498_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_450_, v___f_470_, v_type_491_, v___x_495_);
v___y_444_ = v___x_498_;
goto v___jp_443_;
}
}
else
{
lean_object* v___x_499_; 
lean_dec_ref(v_mctx_493_);
lean_inc_ref(v_type_491_);
v___x_499_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_450_, v___f_470_, v_type_491_, v___x_495_);
v___y_444_ = v___x_499_;
goto v___jp_443_;
}
}
}
}
v___jp_500_:
{
if (v___y_501_ == 0)
{
if (v_ignoreLetDecls_339_ == 0)
{
lean_del_object(v___x_367_);
v___y_468_ = v_ignoreLetDecls_339_;
goto v___jp_467_;
}
else
{
uint8_t v___x_502_; 
v___x_502_ = l_Lean_LocalDecl_isLet(v_val_363_, v___y_501_);
if (v___x_502_ == 0)
{
lean_del_object(v___x_367_);
v___y_468_ = v___x_502_;
goto v___jp_467_;
}
else
{
lean_dec_ref(v___f_450_);
lean_dec(v___x_373_);
goto v___jp_369_;
}
}
}
else
{
lean_dec_ref(v___f_450_);
lean_dec(v___x_373_);
goto v___jp_369_;
}
}
}
else
{
lean_object* v___x_506_; 
lean_dec(v___x_373_);
lean_del_object(v___x_367_);
v___x_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_506_, 0, v_fst_364_);
lean_ctor_set(v___x_506_, 1, v_snd_365_);
v_a_355_ = v___x_506_;
goto v___jp_354_;
}
v___jp_369_:
{
lean_object* v___x_371_; 
if (v_isShared_368_ == 0)
{
v___x_371_ = v___x_367_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_fst_364_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_snd_365_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
v_a_355_ = v___x_371_;
goto v___jp_354_;
}
}
v___jp_374_:
{
if (v_a_375_ == 0)
{
lean_object* v___x_376_; 
lean_dec(v___x_373_);
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v_fst_364_);
lean_ctor_set(v___x_376_, 1, v_snd_365_);
v_a_355_ = v___x_376_;
goto v___jp_354_;
}
else
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
lean_inc(v___x_373_);
v___x_377_ = l_Lean_FVarIdSet_insert(v_snd_365_, v___x_373_);
v___x_378_ = l_Lean_FVarIdSet_insert(v_fst_364_, v___x_373_);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set(v___x_379_, 1, v___x_377_);
v_a_355_ = v___x_379_;
goto v___jp_354_;
}
}
v___jp_380_:
{
lean_object* v___x_383_; lean_object* v_cache_384_; lean_object* v_zetaDeltaFVarIds_385_; lean_object* v_postponed_386_; lean_object* v_diag_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_395_; 
v___x_383_ = lean_st_ref_take(v___y_345_);
v_cache_384_ = lean_ctor_get(v___x_383_, 1);
v_zetaDeltaFVarIds_385_ = lean_ctor_get(v___x_383_, 2);
v_postponed_386_ = lean_ctor_get(v___x_383_, 3);
v_diag_387_ = lean_ctor_get(v___x_383_, 4);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_395_ == 0)
{
lean_object* v_unused_396_; 
v_unused_396_ = lean_ctor_get(v___x_383_, 0);
lean_dec(v_unused_396_);
v___x_389_ = v___x_383_;
v_isShared_390_ = v_isSharedCheck_395_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_diag_387_);
lean_inc(v_postponed_386_);
lean_inc(v_zetaDeltaFVarIds_385_);
lean_inc(v_cache_384_);
lean_dec(v___x_383_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_395_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v_mctx_382_);
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_mctx_382_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_cache_384_);
lean_ctor_set(v_reuseFailAlloc_394_, 2, v_zetaDeltaFVarIds_385_);
lean_ctor_set(v_reuseFailAlloc_394_, 3, v_postponed_386_);
lean_ctor_set(v_reuseFailAlloc_394_, 4, v_diag_387_);
v___x_392_ = v_reuseFailAlloc_394_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_393_; 
v___x_393_ = lean_st_ref_put(v___y_345_, v___x_392_);
v_a_375_ = v_fst_381_;
goto v___jp_374_;
}
}
}
v___jp_397_:
{
lean_object* v_snd_399_; lean_object* v_fst_400_; lean_object* v_mctx_401_; uint8_t v___x_402_; 
v_snd_399_ = lean_ctor_get(v___y_398_, 1);
lean_inc(v_snd_399_);
v_fst_400_ = lean_ctor_get(v___y_398_, 0);
lean_inc(v_fst_400_);
lean_dec_ref(v___y_398_);
v_mctx_401_ = lean_ctor_get(v_snd_399_, 1);
lean_inc_ref(v_mctx_401_);
lean_dec(v_snd_399_);
v___x_402_ = lean_unbox(v_fst_400_);
lean_dec(v_fst_400_);
v_fst_381_ = v___x_402_;
v_mctx_382_ = v_mctx_401_;
goto v___jp_380_;
}
v___jp_403_:
{
lean_object* v_mctx_406_; lean_object* v___x_407_; lean_object* v_cache_408_; lean_object* v_zetaDeltaFVarIds_409_; lean_object* v_postponed_410_; lean_object* v_diag_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_419_; 
v_mctx_406_ = lean_ctor_get(v_snd_405_, 1);
lean_inc_ref(v_mctx_406_);
lean_dec_ref(v_snd_405_);
v___x_407_ = lean_st_ref_take(v___y_345_);
v_cache_408_ = lean_ctor_get(v___x_407_, 1);
v_zetaDeltaFVarIds_409_ = lean_ctor_get(v___x_407_, 2);
v_postponed_410_ = lean_ctor_get(v___x_407_, 3);
v_diag_411_ = lean_ctor_get(v___x_407_, 4);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_419_ == 0)
{
lean_object* v_unused_420_; 
v_unused_420_ = lean_ctor_get(v___x_407_, 0);
lean_dec(v_unused_420_);
v___x_413_ = v___x_407_;
v_isShared_414_ = v_isSharedCheck_419_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_diag_411_);
lean_inc(v_postponed_410_);
lean_inc(v_zetaDeltaFVarIds_409_);
lean_inc(v_cache_408_);
lean_dec(v___x_407_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_419_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v_mctx_406_);
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_mctx_406_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_cache_408_);
lean_ctor_set(v_reuseFailAlloc_418_, 2, v_zetaDeltaFVarIds_409_);
lean_ctor_set(v_reuseFailAlloc_418_, 3, v_postponed_410_);
lean_ctor_set(v_reuseFailAlloc_418_, 4, v_diag_411_);
v___x_416_ = v_reuseFailAlloc_418_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_417_; 
v___x_417_ = lean_st_ref_put(v___y_345_, v___x_416_);
v_a_375_ = v_fst_404_;
goto v___jp_374_;
}
}
}
v___jp_421_:
{
lean_object* v_fst_423_; lean_object* v_snd_424_; uint8_t v___x_425_; 
v_fst_423_ = lean_ctor_get(v___y_422_, 0);
lean_inc(v_fst_423_);
v_snd_424_ = lean_ctor_get(v___y_422_, 1);
lean_inc(v_snd_424_);
lean_dec_ref(v___y_422_);
v___x_425_ = lean_unbox(v_fst_423_);
lean_dec(v_fst_423_);
v_fst_404_ = v___x_425_;
v_snd_405_ = v_snd_424_;
goto v___jp_403_;
}
v___jp_426_:
{
lean_object* v___x_429_; lean_object* v_cache_430_; lean_object* v_zetaDeltaFVarIds_431_; lean_object* v_postponed_432_; lean_object* v_diag_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_441_; 
v___x_429_ = lean_st_ref_take(v___y_345_);
v_cache_430_ = lean_ctor_get(v___x_429_, 1);
v_zetaDeltaFVarIds_431_ = lean_ctor_get(v___x_429_, 2);
v_postponed_432_ = lean_ctor_get(v___x_429_, 3);
v_diag_433_ = lean_ctor_get(v___x_429_, 4);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_441_ == 0)
{
lean_object* v_unused_442_; 
v_unused_442_ = lean_ctor_get(v___x_429_, 0);
lean_dec(v_unused_442_);
v___x_435_ = v___x_429_;
v_isShared_436_ = v_isSharedCheck_441_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_diag_433_);
lean_inc(v_postponed_432_);
lean_inc(v_zetaDeltaFVarIds_431_);
lean_inc(v_cache_430_);
lean_dec(v___x_429_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_441_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v_mctx_428_);
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_mctx_428_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_cache_430_);
lean_ctor_set(v_reuseFailAlloc_440_, 2, v_zetaDeltaFVarIds_431_);
lean_ctor_set(v_reuseFailAlloc_440_, 3, v_postponed_432_);
lean_ctor_set(v_reuseFailAlloc_440_, 4, v_diag_433_);
v___x_438_ = v_reuseFailAlloc_440_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_439_; 
v___x_439_ = lean_st_ref_put(v___y_345_, v___x_438_);
v_a_375_ = v_fst_427_;
goto v___jp_374_;
}
}
}
v___jp_443_:
{
lean_object* v_snd_445_; lean_object* v_fst_446_; lean_object* v_mctx_447_; uint8_t v___x_448_; 
v_snd_445_ = lean_ctor_get(v___y_444_, 1);
lean_inc(v_snd_445_);
v_fst_446_ = lean_ctor_get(v___y_444_, 0);
lean_inc(v_fst_446_);
lean_dec_ref(v___y_444_);
v_mctx_447_ = lean_ctor_get(v_snd_445_, 1);
lean_inc_ref(v_mctx_447_);
lean_dec(v_snd_445_);
v___x_448_ = lean_unbox(v_fst_446_);
lean_dec(v_fst_446_);
v_fst_427_ = v___x_448_;
v_mctx_428_ = v_mctx_447_;
goto v___jp_426_;
}
}
}
v___jp_354_:
{
lean_object* v___x_357_; 
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 1, v_a_355_);
lean_ctor_set(v___x_351_, 0, v___x_353_);
v___x_357_ = v___x_351_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_353_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_a_355_);
v___x_357_ = v_reuseFailAlloc_361_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
size_t v___x_358_; size_t v___x_359_; 
v___x_358_ = ((size_t)1ULL);
v___x_359_ = lean_usize_add(v_i_343_, v___x_358_);
v_i_343_ = v___x_359_;
v_b_344_ = v___x_357_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ignoreLetDecls_510_, lean_object* v_forbidden_511_, lean_object* v_as_512_, lean_object* v_sz_513_, lean_object* v_i_514_, lean_object* v_b_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_518_; size_t v_sz_boxed_519_; size_t v_i_boxed_520_; lean_object* v_res_521_; 
v_ignoreLetDecls_boxed_518_ = lean_unbox(v_ignoreLetDecls_510_);
v_sz_boxed_519_ = lean_unbox_usize(v_sz_513_);
lean_dec(v_sz_513_);
v_i_boxed_520_ = lean_unbox_usize(v_i_514_);
lean_dec(v_i_514_);
v_res_521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(v_ignoreLetDecls_boxed_518_, v_forbidden_511_, v_as_512_, v_sz_boxed_519_, v_i_boxed_520_, v_b_515_, v___y_516_);
lean_dec(v___y_516_);
lean_dec_ref(v_as_512_);
lean_dec(v_forbidden_511_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1(uint8_t v_ignoreLetDecls_522_, lean_object* v_forbidden_523_, lean_object* v_as_524_, size_t v_sz_525_, size_t v_i_526_, lean_object* v_b_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
uint8_t v___x_533_; 
v___x_533_ = lean_usize_dec_lt(v_i_526_, v_sz_525_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; 
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v_b_527_);
return v___x_534_;
}
else
{
lean_object* v_snd_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_694_; 
v_snd_535_ = lean_ctor_get(v_b_527_, 1);
v_isSharedCheck_694_ = !lean_is_exclusive(v_b_527_);
if (v_isSharedCheck_694_ == 0)
{
lean_object* v_unused_695_; 
v_unused_695_ = lean_ctor_get(v_b_527_, 0);
lean_dec(v_unused_695_);
v___x_537_ = v_b_527_;
v_isShared_538_ = v_isSharedCheck_694_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_snd_535_);
lean_dec(v_b_527_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_694_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_539_; lean_object* v_a_541_; lean_object* v_a_548_; 
v___x_539_ = lean_box(0);
v_a_548_ = lean_array_uget_borrowed(v_as_524_, v_i_526_);
if (lean_obj_tag(v_a_548_) == 0)
{
v_a_541_ = v_snd_535_;
goto v___jp_540_;
}
else
{
lean_object* v_val_549_; lean_object* v_fst_550_; lean_object* v_snd_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_693_; 
v_val_549_ = lean_ctor_get(v_a_548_, 0);
v_fst_550_ = lean_ctor_get(v_snd_535_, 0);
v_snd_551_ = lean_ctor_get(v_snd_535_, 1);
v_isSharedCheck_693_ = !lean_is_exclusive(v_snd_535_);
if (v_isSharedCheck_693_ == 0)
{
v___x_553_ = v_snd_535_;
v_isShared_554_ = v_isSharedCheck_693_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_snd_551_);
lean_inc(v_fst_550_);
lean_dec(v_snd_535_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_693_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_559_; uint8_t v_a_561_; uint8_t v_fst_567_; lean_object* v_mctx_568_; lean_object* v___y_584_; uint8_t v_fst_590_; lean_object* v_snd_591_; lean_object* v___y_608_; uint8_t v_fst_613_; lean_object* v_mctx_614_; lean_object* v___y_630_; uint8_t v___x_635_; 
v___x_559_ = l_Lean_LocalDecl_fvarId(v_val_549_);
v___x_635_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v___x_559_, v_forbidden_523_);
if (v___x_635_ == 0)
{
lean_object* v___f_636_; lean_object* v___y_638_; lean_object* v___y_639_; uint8_t v_fst_640_; lean_object* v_snd_641_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; uint8_t v___y_654_; uint8_t v___y_687_; uint8_t v___x_689_; 
lean_inc(v_fst_550_);
v___f_636_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_636_, 0, v_fst_550_);
v___x_689_ = l_Lean_LocalDecl_isAuxDecl(v_val_549_);
if (v___x_689_ == 0)
{
uint8_t v___x_690_; uint8_t v___x_691_; 
v___x_690_ = l_Lean_LocalDecl_binderInfo(v_val_549_);
v___x_691_ = l_Lean_BinderInfo_isInstImplicit(v___x_690_);
v___y_687_ = v___x_691_;
goto v___jp_686_;
}
else
{
v___y_687_ = v___x_689_;
goto v___jp_686_;
}
v___jp_637_:
{
if (v_fst_640_ == 0)
{
uint8_t v___x_642_; 
v___x_642_ = l_Lean_Expr_hasFVar(v___y_638_);
if (v___x_642_ == 0)
{
uint8_t v___x_643_; 
v___x_643_ = l_Lean_Expr_hasMVar(v___y_638_);
if (v___x_643_ == 0)
{
lean_dec_ref(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec_ref(v___f_636_);
v_fst_590_ = v___x_643_;
v_snd_591_ = v_snd_641_;
goto v___jp_589_;
}
else
{
lean_object* v___x_644_; 
v___x_644_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_636_, v___y_639_, v___y_638_, v_snd_641_);
v___y_608_ = v___x_644_;
goto v___jp_607_;
}
}
else
{
lean_object* v___x_645_; 
v___x_645_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_636_, v___y_639_, v___y_638_, v_snd_641_);
v___y_608_ = v___x_645_;
goto v___jp_607_;
}
}
else
{
lean_dec_ref(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec_ref(v___f_636_);
v_fst_590_ = v_fst_640_;
v_snd_591_ = v_snd_641_;
goto v___jp_589_;
}
}
v___jp_646_:
{
lean_object* v_fst_650_; lean_object* v_snd_651_; uint8_t v___x_652_; 
v_fst_650_ = lean_ctor_get(v___y_649_, 0);
lean_inc(v_fst_650_);
v_snd_651_ = lean_ctor_get(v___y_649_, 1);
lean_inc(v_snd_651_);
lean_dec_ref(v___y_649_);
v___x_652_ = lean_unbox(v_fst_650_);
lean_dec(v_fst_650_);
v___y_638_ = v___y_647_;
v___y_639_ = v___y_648_;
v_fst_640_ = v___x_652_;
v_snd_641_ = v_snd_651_;
goto v___jp_637_;
}
v___jp_653_:
{
lean_object* v___x_655_; lean_object* v___f_656_; 
v___x_655_ = lean_box(v___y_654_);
v___f_656_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(v___f_656_, 0, v___x_655_);
if (lean_obj_tag(v_val_549_) == 0)
{
lean_object* v_type_657_; lean_object* v___x_658_; lean_object* v_mctx_659_; lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v_type_657_ = lean_ctor_get(v_val_549_, 3);
v___x_658_ = lean_st_ref_get(v___y_529_);
v_mctx_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc_ref_n(v_mctx_659_, 2);
lean_dec(v___x_658_);
v___x_660_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2);
v___x_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
lean_ctor_set(v___x_661_, 1, v_mctx_659_);
v___x_662_ = l_Lean_Expr_hasFVar(v_type_657_);
if (v___x_662_ == 0)
{
uint8_t v___x_663_; 
v___x_663_ = l_Lean_Expr_hasMVar(v_type_657_);
if (v___x_663_ == 0)
{
lean_dec_ref_known(v___x_661_, 2);
lean_dec_ref(v___f_656_);
lean_dec_ref(v___f_636_);
v_fst_567_ = v___x_663_;
v_mctx_568_ = v_mctx_659_;
goto v___jp_566_;
}
else
{
lean_object* v___x_664_; 
lean_dec_ref(v_mctx_659_);
lean_inc_ref(v_type_657_);
v___x_664_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_636_, v___f_656_, v_type_657_, v___x_661_);
v___y_584_ = v___x_664_;
goto v___jp_583_;
}
}
else
{
lean_object* v___x_665_; 
lean_dec_ref(v_mctx_659_);
lean_inc_ref(v_type_657_);
v___x_665_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_636_, v___f_656_, v_type_657_, v___x_661_);
v___y_584_ = v___x_665_;
goto v___jp_583_;
}
}
else
{
uint8_t v_nondep_666_; 
v_nondep_666_ = lean_ctor_get_uint8(v_val_549_, sizeof(void*)*5);
if (v_nondep_666_ == 0)
{
lean_object* v_type_667_; lean_object* v_value_668_; lean_object* v___x_669_; lean_object* v_mctx_670_; lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v_type_667_ = lean_ctor_get(v_val_549_, 3);
v_value_668_ = lean_ctor_get(v_val_549_, 4);
v___x_669_ = lean_st_ref_get(v___y_529_);
v_mctx_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc_ref(v_mctx_670_);
lean_dec(v___x_669_);
v___x_671_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2);
v___x_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set(v___x_672_, 1, v_mctx_670_);
v___x_673_ = l_Lean_Expr_hasFVar(v_type_667_);
if (v___x_673_ == 0)
{
uint8_t v___x_674_; 
v___x_674_ = l_Lean_Expr_hasMVar(v_type_667_);
if (v___x_674_ == 0)
{
lean_inc_ref(v_value_668_);
v___y_638_ = v_value_668_;
v___y_639_ = v___f_656_;
v_fst_640_ = v___x_674_;
v_snd_641_ = v___x_672_;
goto v___jp_637_;
}
else
{
lean_object* v___x_675_; 
lean_inc_ref(v_type_667_);
lean_inc_ref(v___f_656_);
lean_inc_ref(v___f_636_);
v___x_675_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_636_, v___f_656_, v_type_667_, v___x_672_);
lean_inc_ref(v_value_668_);
v___y_647_ = v_value_668_;
v___y_648_ = v___f_656_;
v___y_649_ = v___x_675_;
goto v___jp_646_;
}
}
else
{
lean_object* v___x_676_; 
lean_inc_ref(v_type_667_);
lean_inc_ref(v___f_656_);
lean_inc_ref(v___f_636_);
v___x_676_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_636_, v___f_656_, v_type_667_, v___x_672_);
lean_inc_ref(v_value_668_);
v___y_647_ = v_value_668_;
v___y_648_ = v___f_656_;
v___y_649_ = v___x_676_;
goto v___jp_646_;
}
}
else
{
lean_object* v_type_677_; lean_object* v___x_678_; lean_object* v_mctx_679_; lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v_type_677_ = lean_ctor_get(v_val_549_, 3);
v___x_678_ = lean_st_ref_get(v___y_529_);
v_mctx_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc_ref_n(v_mctx_679_, 2);
lean_dec(v___x_678_);
v___x_680_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2);
v___x_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
lean_ctor_set(v___x_681_, 1, v_mctx_679_);
v___x_682_ = l_Lean_Expr_hasFVar(v_type_677_);
if (v___x_682_ == 0)
{
uint8_t v___x_683_; 
v___x_683_ = l_Lean_Expr_hasMVar(v_type_677_);
if (v___x_683_ == 0)
{
lean_dec_ref_known(v___x_681_, 2);
lean_dec_ref(v___f_656_);
lean_dec_ref(v___f_636_);
v_fst_613_ = v___x_683_;
v_mctx_614_ = v_mctx_679_;
goto v___jp_612_;
}
else
{
lean_object* v___x_684_; 
lean_dec_ref(v_mctx_679_);
lean_inc_ref(v_type_677_);
v___x_684_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_636_, v___f_656_, v_type_677_, v___x_681_);
v___y_630_ = v___x_684_;
goto v___jp_629_;
}
}
else
{
lean_object* v___x_685_; 
lean_dec_ref(v_mctx_679_);
lean_inc_ref(v_type_677_);
v___x_685_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_636_, v___f_656_, v_type_677_, v___x_681_);
v___y_630_ = v___x_685_;
goto v___jp_629_;
}
}
}
}
v___jp_686_:
{
if (v___y_687_ == 0)
{
if (v_ignoreLetDecls_522_ == 0)
{
lean_del_object(v___x_553_);
v___y_654_ = v_ignoreLetDecls_522_;
goto v___jp_653_;
}
else
{
uint8_t v___x_688_; 
v___x_688_ = l_Lean_LocalDecl_isLet(v_val_549_, v___y_687_);
if (v___x_688_ == 0)
{
lean_del_object(v___x_553_);
v___y_654_ = v___x_688_;
goto v___jp_653_;
}
else
{
lean_dec_ref(v___f_636_);
lean_dec(v___x_559_);
goto v___jp_555_;
}
}
}
else
{
lean_dec_ref(v___f_636_);
lean_dec(v___x_559_);
goto v___jp_555_;
}
}
}
else
{
lean_object* v___x_692_; 
lean_dec(v___x_559_);
lean_del_object(v___x_553_);
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v_fst_550_);
lean_ctor_set(v___x_692_, 1, v_snd_551_);
v_a_541_ = v___x_692_;
goto v___jp_540_;
}
v___jp_555_:
{
lean_object* v___x_557_; 
if (v_isShared_554_ == 0)
{
v___x_557_ = v___x_553_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_fst_550_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_snd_551_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
v_a_541_ = v___x_557_;
goto v___jp_540_;
}
}
v___jp_560_:
{
if (v_a_561_ == 0)
{
lean_object* v___x_562_; 
lean_dec(v___x_559_);
v___x_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_562_, 0, v_fst_550_);
lean_ctor_set(v___x_562_, 1, v_snd_551_);
v_a_541_ = v___x_562_;
goto v___jp_540_;
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
lean_inc(v___x_559_);
v___x_563_ = l_Lean_FVarIdSet_insert(v_snd_551_, v___x_559_);
v___x_564_ = l_Lean_FVarIdSet_insert(v_fst_550_, v___x_559_);
v___x_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
lean_ctor_set(v___x_565_, 1, v___x_563_);
v_a_541_ = v___x_565_;
goto v___jp_540_;
}
}
v___jp_566_:
{
lean_object* v___x_569_; lean_object* v_cache_570_; lean_object* v_zetaDeltaFVarIds_571_; lean_object* v_postponed_572_; lean_object* v_diag_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_581_; 
v___x_569_ = lean_st_ref_take(v___y_529_);
v_cache_570_ = lean_ctor_get(v___x_569_, 1);
v_zetaDeltaFVarIds_571_ = lean_ctor_get(v___x_569_, 2);
v_postponed_572_ = lean_ctor_get(v___x_569_, 3);
v_diag_573_ = lean_ctor_get(v___x_569_, 4);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_581_ == 0)
{
lean_object* v_unused_582_; 
v_unused_582_ = lean_ctor_get(v___x_569_, 0);
lean_dec(v_unused_582_);
v___x_575_ = v___x_569_;
v_isShared_576_ = v_isSharedCheck_581_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_diag_573_);
lean_inc(v_postponed_572_);
lean_inc(v_zetaDeltaFVarIds_571_);
lean_inc(v_cache_570_);
lean_dec(v___x_569_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_581_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v_mctx_568_);
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_mctx_568_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v_cache_570_);
lean_ctor_set(v_reuseFailAlloc_580_, 2, v_zetaDeltaFVarIds_571_);
lean_ctor_set(v_reuseFailAlloc_580_, 3, v_postponed_572_);
lean_ctor_set(v_reuseFailAlloc_580_, 4, v_diag_573_);
v___x_578_ = v_reuseFailAlloc_580_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
lean_object* v___x_579_; 
v___x_579_ = lean_st_ref_put(v___y_529_, v___x_578_);
v_a_561_ = v_fst_567_;
goto v___jp_560_;
}
}
}
v___jp_583_:
{
lean_object* v_snd_585_; lean_object* v_fst_586_; lean_object* v_mctx_587_; uint8_t v___x_588_; 
v_snd_585_ = lean_ctor_get(v___y_584_, 1);
lean_inc(v_snd_585_);
v_fst_586_ = lean_ctor_get(v___y_584_, 0);
lean_inc(v_fst_586_);
lean_dec_ref(v___y_584_);
v_mctx_587_ = lean_ctor_get(v_snd_585_, 1);
lean_inc_ref(v_mctx_587_);
lean_dec(v_snd_585_);
v___x_588_ = lean_unbox(v_fst_586_);
lean_dec(v_fst_586_);
v_fst_567_ = v___x_588_;
v_mctx_568_ = v_mctx_587_;
goto v___jp_566_;
}
v___jp_589_:
{
lean_object* v_mctx_592_; lean_object* v___x_593_; lean_object* v_cache_594_; lean_object* v_zetaDeltaFVarIds_595_; lean_object* v_postponed_596_; lean_object* v_diag_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_605_; 
v_mctx_592_ = lean_ctor_get(v_snd_591_, 1);
lean_inc_ref(v_mctx_592_);
lean_dec_ref(v_snd_591_);
v___x_593_ = lean_st_ref_take(v___y_529_);
v_cache_594_ = lean_ctor_get(v___x_593_, 1);
v_zetaDeltaFVarIds_595_ = lean_ctor_get(v___x_593_, 2);
v_postponed_596_ = lean_ctor_get(v___x_593_, 3);
v_diag_597_ = lean_ctor_get(v___x_593_, 4);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_605_ == 0)
{
lean_object* v_unused_606_; 
v_unused_606_ = lean_ctor_get(v___x_593_, 0);
lean_dec(v_unused_606_);
v___x_599_ = v___x_593_;
v_isShared_600_ = v_isSharedCheck_605_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_diag_597_);
lean_inc(v_postponed_596_);
lean_inc(v_zetaDeltaFVarIds_595_);
lean_inc(v_cache_594_);
lean_dec(v___x_593_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_605_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v_mctx_592_);
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_mctx_592_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_cache_594_);
lean_ctor_set(v_reuseFailAlloc_604_, 2, v_zetaDeltaFVarIds_595_);
lean_ctor_set(v_reuseFailAlloc_604_, 3, v_postponed_596_);
lean_ctor_set(v_reuseFailAlloc_604_, 4, v_diag_597_);
v___x_602_ = v_reuseFailAlloc_604_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_object* v___x_603_; 
v___x_603_ = lean_st_ref_put(v___y_529_, v___x_602_);
v_a_561_ = v_fst_590_;
goto v___jp_560_;
}
}
}
v___jp_607_:
{
lean_object* v_fst_609_; lean_object* v_snd_610_; uint8_t v___x_611_; 
v_fst_609_ = lean_ctor_get(v___y_608_, 0);
lean_inc(v_fst_609_);
v_snd_610_ = lean_ctor_get(v___y_608_, 1);
lean_inc(v_snd_610_);
lean_dec_ref(v___y_608_);
v___x_611_ = lean_unbox(v_fst_609_);
lean_dec(v_fst_609_);
v_fst_590_ = v___x_611_;
v_snd_591_ = v_snd_610_;
goto v___jp_589_;
}
v___jp_612_:
{
lean_object* v___x_615_; lean_object* v_cache_616_; lean_object* v_zetaDeltaFVarIds_617_; lean_object* v_postponed_618_; lean_object* v_diag_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_627_; 
v___x_615_ = lean_st_ref_take(v___y_529_);
v_cache_616_ = lean_ctor_get(v___x_615_, 1);
v_zetaDeltaFVarIds_617_ = lean_ctor_get(v___x_615_, 2);
v_postponed_618_ = lean_ctor_get(v___x_615_, 3);
v_diag_619_ = lean_ctor_get(v___x_615_, 4);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; 
v_unused_628_ = lean_ctor_get(v___x_615_, 0);
lean_dec(v_unused_628_);
v___x_621_ = v___x_615_;
v_isShared_622_ = v_isSharedCheck_627_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_diag_619_);
lean_inc(v_postponed_618_);
lean_inc(v_zetaDeltaFVarIds_617_);
lean_inc(v_cache_616_);
lean_dec(v___x_615_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_627_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v_mctx_614_);
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_mctx_614_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_cache_616_);
lean_ctor_set(v_reuseFailAlloc_626_, 2, v_zetaDeltaFVarIds_617_);
lean_ctor_set(v_reuseFailAlloc_626_, 3, v_postponed_618_);
lean_ctor_set(v_reuseFailAlloc_626_, 4, v_diag_619_);
v___x_624_ = v_reuseFailAlloc_626_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_625_; 
v___x_625_ = lean_st_ref_put(v___y_529_, v___x_624_);
v_a_561_ = v_fst_613_;
goto v___jp_560_;
}
}
}
v___jp_629_:
{
lean_object* v_snd_631_; lean_object* v_fst_632_; lean_object* v_mctx_633_; uint8_t v___x_634_; 
v_snd_631_ = lean_ctor_get(v___y_630_, 1);
lean_inc(v_snd_631_);
v_fst_632_ = lean_ctor_get(v___y_630_, 0);
lean_inc(v_fst_632_);
lean_dec_ref(v___y_630_);
v_mctx_633_ = lean_ctor_get(v_snd_631_, 1);
lean_inc_ref(v_mctx_633_);
lean_dec(v_snd_631_);
v___x_634_ = lean_unbox(v_fst_632_);
lean_dec(v_fst_632_);
v_fst_613_ = v___x_634_;
v_mctx_614_ = v_mctx_633_;
goto v___jp_612_;
}
}
}
v___jp_540_:
{
lean_object* v___x_543_; 
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 1, v_a_541_);
lean_ctor_set(v___x_537_, 0, v___x_539_);
v___x_543_ = v___x_537_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v_a_541_);
v___x_543_ = v_reuseFailAlloc_547_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
size_t v___x_544_; size_t v___x_545_; lean_object* v___x_546_; 
v___x_544_ = ((size_t)1ULL);
v___x_545_ = lean_usize_add(v_i_526_, v___x_544_);
v___x_546_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(v_ignoreLetDecls_522_, v_forbidden_523_, v_as_524_, v_sz_525_, v___x_545_, v___x_543_, v___y_529_);
return v___x_546_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___boxed(lean_object* v_ignoreLetDecls_696_, lean_object* v_forbidden_697_, lean_object* v_as_698_, lean_object* v_sz_699_, lean_object* v_i_700_, lean_object* v_b_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_707_; size_t v_sz_boxed_708_; size_t v_i_boxed_709_; lean_object* v_res_710_; 
v_ignoreLetDecls_boxed_707_ = lean_unbox(v_ignoreLetDecls_696_);
v_sz_boxed_708_ = lean_unbox_usize(v_sz_699_);
lean_dec(v_sz_699_);
v_i_boxed_709_ = lean_unbox_usize(v_i_700_);
lean_dec(v_i_700_);
v_res_710_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1(v_ignoreLetDecls_boxed_707_, v_forbidden_697_, v_as_698_, v_sz_boxed_708_, v_i_boxed_709_, v_b_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec_ref(v_as_698_);
lean_dec(v_forbidden_697_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(uint8_t v_ignoreLetDecls_711_, lean_object* v_forbidden_712_, lean_object* v_as_713_, size_t v_sz_714_, size_t v_i_715_, lean_object* v_b_716_, lean_object* v___y_717_){
_start:
{
uint8_t v___x_719_; 
v___x_719_ = lean_usize_dec_lt(v_i_715_, v_sz_714_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; 
v___x_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_720_, 0, v_b_716_);
return v___x_720_;
}
else
{
lean_object* v_snd_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_880_; 
v_snd_721_ = lean_ctor_get(v_b_716_, 1);
v_isSharedCheck_880_ = !lean_is_exclusive(v_b_716_);
if (v_isSharedCheck_880_ == 0)
{
lean_object* v_unused_881_; 
v_unused_881_ = lean_ctor_get(v_b_716_, 0);
lean_dec(v_unused_881_);
v___x_723_ = v_b_716_;
v_isShared_724_ = v_isSharedCheck_880_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_snd_721_);
lean_dec(v_b_716_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_880_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_725_; lean_object* v_a_727_; lean_object* v_a_734_; 
v___x_725_ = lean_box(0);
v_a_734_ = lean_array_uget_borrowed(v_as_713_, v_i_715_);
if (lean_obj_tag(v_a_734_) == 0)
{
v_a_727_ = v_snd_721_;
goto v___jp_726_;
}
else
{
lean_object* v_val_735_; lean_object* v_fst_736_; lean_object* v_snd_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_879_; 
v_val_735_ = lean_ctor_get(v_a_734_, 0);
v_fst_736_ = lean_ctor_get(v_snd_721_, 0);
v_snd_737_ = lean_ctor_get(v_snd_721_, 1);
v_isSharedCheck_879_ = !lean_is_exclusive(v_snd_721_);
if (v_isSharedCheck_879_ == 0)
{
v___x_739_ = v_snd_721_;
v_isShared_740_ = v_isSharedCheck_879_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_snd_737_);
lean_inc(v_fst_736_);
lean_dec(v_snd_721_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_879_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_745_; uint8_t v_a_747_; uint8_t v_fst_753_; lean_object* v_mctx_754_; lean_object* v___y_770_; uint8_t v_fst_776_; lean_object* v_snd_777_; lean_object* v___y_794_; uint8_t v_fst_799_; lean_object* v_mctx_800_; lean_object* v___y_816_; uint8_t v___x_821_; 
v___x_745_ = l_Lean_LocalDecl_fvarId(v_val_735_);
v___x_821_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v___x_745_, v_forbidden_712_);
if (v___x_821_ == 0)
{
lean_object* v___f_822_; lean_object* v___y_824_; lean_object* v___y_825_; uint8_t v_fst_826_; lean_object* v_snd_827_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; uint8_t v___y_840_; uint8_t v___y_873_; uint8_t v___x_875_; 
lean_inc(v_fst_736_);
v___f_822_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_822_, 0, v_fst_736_);
v___x_875_ = l_Lean_LocalDecl_isAuxDecl(v_val_735_);
if (v___x_875_ == 0)
{
uint8_t v___x_876_; uint8_t v___x_877_; 
v___x_876_ = l_Lean_LocalDecl_binderInfo(v_val_735_);
v___x_877_ = l_Lean_BinderInfo_isInstImplicit(v___x_876_);
v___y_873_ = v___x_877_;
goto v___jp_872_;
}
else
{
v___y_873_ = v___x_875_;
goto v___jp_872_;
}
v___jp_823_:
{
if (v_fst_826_ == 0)
{
uint8_t v___x_828_; 
v___x_828_ = l_Lean_Expr_hasFVar(v___y_825_);
if (v___x_828_ == 0)
{
uint8_t v___x_829_; 
v___x_829_ = l_Lean_Expr_hasMVar(v___y_825_);
if (v___x_829_ == 0)
{
lean_dec_ref(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec_ref(v___f_822_);
v_fst_776_ = v___x_829_;
v_snd_777_ = v_snd_827_;
goto v___jp_775_;
}
else
{
lean_object* v___x_830_; 
v___x_830_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_822_, v___y_824_, v___y_825_, v_snd_827_);
v___y_794_ = v___x_830_;
goto v___jp_793_;
}
}
else
{
lean_object* v___x_831_; 
v___x_831_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_822_, v___y_824_, v___y_825_, v_snd_827_);
v___y_794_ = v___x_831_;
goto v___jp_793_;
}
}
else
{
lean_dec_ref(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec_ref(v___f_822_);
v_fst_776_ = v_fst_826_;
v_snd_777_ = v_snd_827_;
goto v___jp_775_;
}
}
v___jp_832_:
{
lean_object* v_fst_836_; lean_object* v_snd_837_; uint8_t v___x_838_; 
v_fst_836_ = lean_ctor_get(v___y_835_, 0);
lean_inc(v_fst_836_);
v_snd_837_ = lean_ctor_get(v___y_835_, 1);
lean_inc(v_snd_837_);
lean_dec_ref(v___y_835_);
v___x_838_ = lean_unbox(v_fst_836_);
lean_dec(v_fst_836_);
v___y_824_ = v___y_833_;
v___y_825_ = v___y_834_;
v_fst_826_ = v___x_838_;
v_snd_827_ = v_snd_837_;
goto v___jp_823_;
}
v___jp_839_:
{
lean_object* v___x_841_; lean_object* v___f_842_; 
v___x_841_ = lean_box(v___y_840_);
v___f_842_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(v___f_842_, 0, v___x_841_);
if (lean_obj_tag(v_val_735_) == 0)
{
lean_object* v_type_843_; lean_object* v___x_844_; lean_object* v_mctx_845_; lean_object* v___x_846_; lean_object* v___x_847_; uint8_t v___x_848_; 
v_type_843_ = lean_ctor_get(v_val_735_, 3);
v___x_844_ = lean_st_ref_get(v___y_717_);
v_mctx_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc_ref_n(v_mctx_845_, 2);
lean_dec(v___x_844_);
v___x_846_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2);
v___x_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
lean_ctor_set(v___x_847_, 1, v_mctx_845_);
v___x_848_ = l_Lean_Expr_hasFVar(v_type_843_);
if (v___x_848_ == 0)
{
uint8_t v___x_849_; 
v___x_849_ = l_Lean_Expr_hasMVar(v_type_843_);
if (v___x_849_ == 0)
{
lean_dec_ref_known(v___x_847_, 2);
lean_dec_ref(v___f_842_);
lean_dec_ref(v___f_822_);
v_fst_753_ = v___x_849_;
v_mctx_754_ = v_mctx_845_;
goto v___jp_752_;
}
else
{
lean_object* v___x_850_; 
lean_dec_ref(v_mctx_845_);
lean_inc_ref(v_type_843_);
v___x_850_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_822_, v___f_842_, v_type_843_, v___x_847_);
v___y_770_ = v___x_850_;
goto v___jp_769_;
}
}
else
{
lean_object* v___x_851_; 
lean_dec_ref(v_mctx_845_);
lean_inc_ref(v_type_843_);
v___x_851_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_822_, v___f_842_, v_type_843_, v___x_847_);
v___y_770_ = v___x_851_;
goto v___jp_769_;
}
}
else
{
uint8_t v_nondep_852_; 
v_nondep_852_ = lean_ctor_get_uint8(v_val_735_, sizeof(void*)*5);
if (v_nondep_852_ == 0)
{
lean_object* v_type_853_; lean_object* v_value_854_; lean_object* v___x_855_; lean_object* v_mctx_856_; lean_object* v___x_857_; lean_object* v___x_858_; uint8_t v___x_859_; 
v_type_853_ = lean_ctor_get(v_val_735_, 3);
v_value_854_ = lean_ctor_get(v_val_735_, 4);
v___x_855_ = lean_st_ref_get(v___y_717_);
v_mctx_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc_ref(v_mctx_856_);
lean_dec(v___x_855_);
v___x_857_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2);
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
lean_ctor_set(v___x_858_, 1, v_mctx_856_);
v___x_859_ = l_Lean_Expr_hasFVar(v_type_853_);
if (v___x_859_ == 0)
{
uint8_t v___x_860_; 
v___x_860_ = l_Lean_Expr_hasMVar(v_type_853_);
if (v___x_860_ == 0)
{
lean_inc_ref(v_value_854_);
v___y_824_ = v___f_842_;
v___y_825_ = v_value_854_;
v_fst_826_ = v___x_860_;
v_snd_827_ = v___x_858_;
goto v___jp_823_;
}
else
{
lean_object* v___x_861_; 
lean_inc_ref(v_type_853_);
lean_inc_ref(v___f_842_);
lean_inc_ref(v___f_822_);
v___x_861_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_822_, v___f_842_, v_type_853_, v___x_858_);
lean_inc_ref(v_value_854_);
v___y_833_ = v___f_842_;
v___y_834_ = v_value_854_;
v___y_835_ = v___x_861_;
goto v___jp_832_;
}
}
else
{
lean_object* v___x_862_; 
lean_inc_ref(v_type_853_);
lean_inc_ref(v___f_842_);
lean_inc_ref(v___f_822_);
v___x_862_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_822_, v___f_842_, v_type_853_, v___x_858_);
lean_inc_ref(v_value_854_);
v___y_833_ = v___f_842_;
v___y_834_ = v_value_854_;
v___y_835_ = v___x_862_;
goto v___jp_832_;
}
}
else
{
lean_object* v_type_863_; lean_object* v___x_864_; lean_object* v_mctx_865_; lean_object* v___x_866_; lean_object* v___x_867_; uint8_t v___x_868_; 
v_type_863_ = lean_ctor_get(v_val_735_, 3);
v___x_864_ = lean_st_ref_get(v___y_717_);
v_mctx_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc_ref_n(v_mctx_865_, 2);
lean_dec(v___x_864_);
v___x_866_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2);
v___x_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
lean_ctor_set(v___x_867_, 1, v_mctx_865_);
v___x_868_ = l_Lean_Expr_hasFVar(v_type_863_);
if (v___x_868_ == 0)
{
uint8_t v___x_869_; 
v___x_869_ = l_Lean_Expr_hasMVar(v_type_863_);
if (v___x_869_ == 0)
{
lean_dec_ref_known(v___x_867_, 2);
lean_dec_ref(v___f_842_);
lean_dec_ref(v___f_822_);
v_fst_799_ = v___x_869_;
v_mctx_800_ = v_mctx_865_;
goto v___jp_798_;
}
else
{
lean_object* v___x_870_; 
lean_dec_ref(v_mctx_865_);
lean_inc_ref(v_type_863_);
v___x_870_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_822_, v___f_842_, v_type_863_, v___x_867_);
v___y_816_ = v___x_870_;
goto v___jp_815_;
}
}
else
{
lean_object* v___x_871_; 
lean_dec_ref(v_mctx_865_);
lean_inc_ref(v_type_863_);
v___x_871_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_822_, v___f_842_, v_type_863_, v___x_867_);
v___y_816_ = v___x_871_;
goto v___jp_815_;
}
}
}
}
v___jp_872_:
{
if (v___y_873_ == 0)
{
if (v_ignoreLetDecls_711_ == 0)
{
lean_del_object(v___x_739_);
v___y_840_ = v_ignoreLetDecls_711_;
goto v___jp_839_;
}
else
{
uint8_t v___x_874_; 
v___x_874_ = l_Lean_LocalDecl_isLet(v_val_735_, v___y_873_);
if (v___x_874_ == 0)
{
lean_del_object(v___x_739_);
v___y_840_ = v___x_874_;
goto v___jp_839_;
}
else
{
lean_dec_ref(v___f_822_);
lean_dec(v___x_745_);
goto v___jp_741_;
}
}
}
else
{
lean_dec_ref(v___f_822_);
lean_dec(v___x_745_);
goto v___jp_741_;
}
}
}
else
{
lean_object* v___x_878_; 
lean_dec(v___x_745_);
lean_del_object(v___x_739_);
v___x_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_878_, 0, v_fst_736_);
lean_ctor_set(v___x_878_, 1, v_snd_737_);
v_a_727_ = v___x_878_;
goto v___jp_726_;
}
v___jp_741_:
{
lean_object* v___x_743_; 
if (v_isShared_740_ == 0)
{
v___x_743_ = v___x_739_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_fst_736_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_snd_737_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
v_a_727_ = v___x_743_;
goto v___jp_726_;
}
}
v___jp_746_:
{
if (v_a_747_ == 0)
{
lean_object* v___x_748_; 
lean_dec(v___x_745_);
v___x_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_748_, 0, v_fst_736_);
lean_ctor_set(v___x_748_, 1, v_snd_737_);
v_a_727_ = v___x_748_;
goto v___jp_726_;
}
else
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
lean_inc(v___x_745_);
v___x_749_ = l_Lean_FVarIdSet_insert(v_snd_737_, v___x_745_);
v___x_750_ = l_Lean_FVarIdSet_insert(v_fst_736_, v___x_745_);
v___x_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
lean_ctor_set(v___x_751_, 1, v___x_749_);
v_a_727_ = v___x_751_;
goto v___jp_726_;
}
}
v___jp_752_:
{
lean_object* v___x_755_; lean_object* v_cache_756_; lean_object* v_zetaDeltaFVarIds_757_; lean_object* v_postponed_758_; lean_object* v_diag_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_767_; 
v___x_755_ = lean_st_ref_take(v___y_717_);
v_cache_756_ = lean_ctor_get(v___x_755_, 1);
v_zetaDeltaFVarIds_757_ = lean_ctor_get(v___x_755_, 2);
v_postponed_758_ = lean_ctor_get(v___x_755_, 3);
v_diag_759_ = lean_ctor_get(v___x_755_, 4);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_767_ == 0)
{
lean_object* v_unused_768_; 
v_unused_768_ = lean_ctor_get(v___x_755_, 0);
lean_dec(v_unused_768_);
v___x_761_ = v___x_755_;
v_isShared_762_ = v_isSharedCheck_767_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_diag_759_);
lean_inc(v_postponed_758_);
lean_inc(v_zetaDeltaFVarIds_757_);
lean_inc(v_cache_756_);
lean_dec(v___x_755_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_767_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v_mctx_754_);
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_mctx_754_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v_cache_756_);
lean_ctor_set(v_reuseFailAlloc_766_, 2, v_zetaDeltaFVarIds_757_);
lean_ctor_set(v_reuseFailAlloc_766_, 3, v_postponed_758_);
lean_ctor_set(v_reuseFailAlloc_766_, 4, v_diag_759_);
v___x_764_ = v_reuseFailAlloc_766_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
lean_object* v___x_765_; 
v___x_765_ = lean_st_ref_put(v___y_717_, v___x_764_);
v_a_747_ = v_fst_753_;
goto v___jp_746_;
}
}
}
v___jp_769_:
{
lean_object* v_snd_771_; lean_object* v_fst_772_; lean_object* v_mctx_773_; uint8_t v___x_774_; 
v_snd_771_ = lean_ctor_get(v___y_770_, 1);
lean_inc(v_snd_771_);
v_fst_772_ = lean_ctor_get(v___y_770_, 0);
lean_inc(v_fst_772_);
lean_dec_ref(v___y_770_);
v_mctx_773_ = lean_ctor_get(v_snd_771_, 1);
lean_inc_ref(v_mctx_773_);
lean_dec(v_snd_771_);
v___x_774_ = lean_unbox(v_fst_772_);
lean_dec(v_fst_772_);
v_fst_753_ = v___x_774_;
v_mctx_754_ = v_mctx_773_;
goto v___jp_752_;
}
v___jp_775_:
{
lean_object* v_mctx_778_; lean_object* v___x_779_; lean_object* v_cache_780_; lean_object* v_zetaDeltaFVarIds_781_; lean_object* v_postponed_782_; lean_object* v_diag_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_791_; 
v_mctx_778_ = lean_ctor_get(v_snd_777_, 1);
lean_inc_ref(v_mctx_778_);
lean_dec_ref(v_snd_777_);
v___x_779_ = lean_st_ref_take(v___y_717_);
v_cache_780_ = lean_ctor_get(v___x_779_, 1);
v_zetaDeltaFVarIds_781_ = lean_ctor_get(v___x_779_, 2);
v_postponed_782_ = lean_ctor_get(v___x_779_, 3);
v_diag_783_ = lean_ctor_get(v___x_779_, 4);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; 
v_unused_792_ = lean_ctor_get(v___x_779_, 0);
lean_dec(v_unused_792_);
v___x_785_ = v___x_779_;
v_isShared_786_ = v_isSharedCheck_791_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_diag_783_);
lean_inc(v_postponed_782_);
lean_inc(v_zetaDeltaFVarIds_781_);
lean_inc(v_cache_780_);
lean_dec(v___x_779_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_791_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v_mctx_778_);
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_mctx_778_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_cache_780_);
lean_ctor_set(v_reuseFailAlloc_790_, 2, v_zetaDeltaFVarIds_781_);
lean_ctor_set(v_reuseFailAlloc_790_, 3, v_postponed_782_);
lean_ctor_set(v_reuseFailAlloc_790_, 4, v_diag_783_);
v___x_788_ = v_reuseFailAlloc_790_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_789_; 
v___x_789_ = lean_st_ref_put(v___y_717_, v___x_788_);
v_a_747_ = v_fst_776_;
goto v___jp_746_;
}
}
}
v___jp_793_:
{
lean_object* v_fst_795_; lean_object* v_snd_796_; uint8_t v___x_797_; 
v_fst_795_ = lean_ctor_get(v___y_794_, 0);
lean_inc(v_fst_795_);
v_snd_796_ = lean_ctor_get(v___y_794_, 1);
lean_inc(v_snd_796_);
lean_dec_ref(v___y_794_);
v___x_797_ = lean_unbox(v_fst_795_);
lean_dec(v_fst_795_);
v_fst_776_ = v___x_797_;
v_snd_777_ = v_snd_796_;
goto v___jp_775_;
}
v___jp_798_:
{
lean_object* v___x_801_; lean_object* v_cache_802_; lean_object* v_zetaDeltaFVarIds_803_; lean_object* v_postponed_804_; lean_object* v_diag_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_813_; 
v___x_801_ = lean_st_ref_take(v___y_717_);
v_cache_802_ = lean_ctor_get(v___x_801_, 1);
v_zetaDeltaFVarIds_803_ = lean_ctor_get(v___x_801_, 2);
v_postponed_804_ = lean_ctor_get(v___x_801_, 3);
v_diag_805_ = lean_ctor_get(v___x_801_, 4);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_813_ == 0)
{
lean_object* v_unused_814_; 
v_unused_814_ = lean_ctor_get(v___x_801_, 0);
lean_dec(v_unused_814_);
v___x_807_ = v___x_801_;
v_isShared_808_ = v_isSharedCheck_813_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_diag_805_);
lean_inc(v_postponed_804_);
lean_inc(v_zetaDeltaFVarIds_803_);
lean_inc(v_cache_802_);
lean_dec(v___x_801_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_813_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v_mctx_800_);
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_mctx_800_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_cache_802_);
lean_ctor_set(v_reuseFailAlloc_812_, 2, v_zetaDeltaFVarIds_803_);
lean_ctor_set(v_reuseFailAlloc_812_, 3, v_postponed_804_);
lean_ctor_set(v_reuseFailAlloc_812_, 4, v_diag_805_);
v___x_810_ = v_reuseFailAlloc_812_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_811_; 
v___x_811_ = lean_st_ref_put(v___y_717_, v___x_810_);
v_a_747_ = v_fst_799_;
goto v___jp_746_;
}
}
}
v___jp_815_:
{
lean_object* v_snd_817_; lean_object* v_fst_818_; lean_object* v_mctx_819_; uint8_t v___x_820_; 
v_snd_817_ = lean_ctor_get(v___y_816_, 1);
lean_inc(v_snd_817_);
v_fst_818_ = lean_ctor_get(v___y_816_, 0);
lean_inc(v_fst_818_);
lean_dec_ref(v___y_816_);
v_mctx_819_ = lean_ctor_get(v_snd_817_, 1);
lean_inc_ref(v_mctx_819_);
lean_dec(v_snd_817_);
v___x_820_ = lean_unbox(v_fst_818_);
lean_dec(v_fst_818_);
v_fst_799_ = v___x_820_;
v_mctx_800_ = v_mctx_819_;
goto v___jp_798_;
}
}
}
v___jp_726_:
{
lean_object* v___x_729_; 
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 1, v_a_727_);
lean_ctor_set(v___x_723_, 0, v___x_725_);
v___x_729_ = v___x_723_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_a_727_);
v___x_729_ = v_reuseFailAlloc_733_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
size_t v___x_730_; size_t v___x_731_; 
v___x_730_ = ((size_t)1ULL);
v___x_731_ = lean_usize_add(v_i_715_, v___x_730_);
v_i_715_ = v___x_731_;
v_b_716_ = v___x_729_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_ignoreLetDecls_882_, lean_object* v_forbidden_883_, lean_object* v_as_884_, lean_object* v_sz_885_, lean_object* v_i_886_, lean_object* v_b_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_890_; size_t v_sz_boxed_891_; size_t v_i_boxed_892_; lean_object* v_res_893_; 
v_ignoreLetDecls_boxed_890_ = lean_unbox(v_ignoreLetDecls_882_);
v_sz_boxed_891_ = lean_unbox_usize(v_sz_885_);
lean_dec(v_sz_885_);
v_i_boxed_892_ = lean_unbox_usize(v_i_886_);
lean_dec(v_i_886_);
v_res_893_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(v_ignoreLetDecls_boxed_890_, v_forbidden_883_, v_as_884_, v_sz_boxed_891_, v_i_boxed_892_, v_b_887_, v___y_888_);
lean_dec(v___y_888_);
lean_dec_ref(v_as_884_);
lean_dec(v_forbidden_883_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2(uint8_t v_ignoreLetDecls_894_, lean_object* v_forbidden_895_, lean_object* v_as_896_, size_t v_sz_897_, size_t v_i_898_, lean_object* v_b_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
uint8_t v___x_905_; 
v___x_905_ = lean_usize_dec_lt(v_i_898_, v_sz_897_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; 
v___x_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_906_, 0, v_b_899_);
return v___x_906_;
}
else
{
lean_object* v_snd_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_1066_; 
v_snd_907_ = lean_ctor_get(v_b_899_, 1);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_b_899_);
if (v_isSharedCheck_1066_ == 0)
{
lean_object* v_unused_1067_; 
v_unused_1067_ = lean_ctor_get(v_b_899_, 0);
lean_dec(v_unused_1067_);
v___x_909_ = v_b_899_;
v_isShared_910_ = v_isSharedCheck_1066_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_snd_907_);
lean_dec(v_b_899_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_1066_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_911_; lean_object* v_a_913_; lean_object* v_a_920_; 
v___x_911_ = lean_box(0);
v_a_920_ = lean_array_uget_borrowed(v_as_896_, v_i_898_);
if (lean_obj_tag(v_a_920_) == 0)
{
v_a_913_ = v_snd_907_;
goto v___jp_912_;
}
else
{
lean_object* v_val_921_; lean_object* v_fst_922_; lean_object* v_snd_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_1065_; 
v_val_921_ = lean_ctor_get(v_a_920_, 0);
v_fst_922_ = lean_ctor_get(v_snd_907_, 0);
v_snd_923_ = lean_ctor_get(v_snd_907_, 1);
v_isSharedCheck_1065_ = !lean_is_exclusive(v_snd_907_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_925_ = v_snd_907_;
v_isShared_926_ = v_isSharedCheck_1065_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_snd_923_);
lean_inc(v_fst_922_);
lean_dec(v_snd_907_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_1065_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_931_; uint8_t v_a_933_; uint8_t v_fst_939_; lean_object* v_mctx_940_; lean_object* v___y_956_; uint8_t v_fst_962_; lean_object* v_snd_963_; lean_object* v___y_980_; uint8_t v_fst_985_; lean_object* v_mctx_986_; lean_object* v___y_1002_; uint8_t v___x_1007_; 
v___x_931_ = l_Lean_LocalDecl_fvarId(v_val_921_);
v___x_1007_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v___x_931_, v_forbidden_895_);
if (v___x_1007_ == 0)
{
lean_object* v___f_1008_; lean_object* v___y_1010_; lean_object* v___y_1011_; uint8_t v_fst_1012_; lean_object* v_snd_1013_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; uint8_t v___y_1026_; uint8_t v___y_1059_; uint8_t v___x_1061_; 
lean_inc(v_fst_922_);
v___f_1008_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1008_, 0, v_fst_922_);
v___x_1061_ = l_Lean_LocalDecl_isAuxDecl(v_val_921_);
if (v___x_1061_ == 0)
{
uint8_t v___x_1062_; uint8_t v___x_1063_; 
v___x_1062_ = l_Lean_LocalDecl_binderInfo(v_val_921_);
v___x_1063_ = l_Lean_BinderInfo_isInstImplicit(v___x_1062_);
v___y_1059_ = v___x_1063_;
goto v___jp_1058_;
}
else
{
v___y_1059_ = v___x_1061_;
goto v___jp_1058_;
}
v___jp_1009_:
{
if (v_fst_1012_ == 0)
{
uint8_t v___x_1014_; 
v___x_1014_ = l_Lean_Expr_hasFVar(v___y_1010_);
if (v___x_1014_ == 0)
{
uint8_t v___x_1015_; 
v___x_1015_ = l_Lean_Expr_hasMVar(v___y_1010_);
if (v___x_1015_ == 0)
{
lean_dec_ref(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec_ref(v___f_1008_);
v_fst_962_ = v___x_1015_;
v_snd_963_ = v_snd_1013_;
goto v___jp_961_;
}
else
{
lean_object* v___x_1016_; 
v___x_1016_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1008_, v___y_1011_, v___y_1010_, v_snd_1013_);
v___y_980_ = v___x_1016_;
goto v___jp_979_;
}
}
else
{
lean_object* v___x_1017_; 
v___x_1017_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1008_, v___y_1011_, v___y_1010_, v_snd_1013_);
v___y_980_ = v___x_1017_;
goto v___jp_979_;
}
}
else
{
lean_dec_ref(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec_ref(v___f_1008_);
v_fst_962_ = v_fst_1012_;
v_snd_963_ = v_snd_1013_;
goto v___jp_961_;
}
}
v___jp_1018_:
{
lean_object* v_fst_1022_; lean_object* v_snd_1023_; uint8_t v___x_1024_; 
v_fst_1022_ = lean_ctor_get(v___y_1021_, 0);
lean_inc(v_fst_1022_);
v_snd_1023_ = lean_ctor_get(v___y_1021_, 1);
lean_inc(v_snd_1023_);
lean_dec_ref(v___y_1021_);
v___x_1024_ = lean_unbox(v_fst_1022_);
lean_dec(v_fst_1022_);
v___y_1010_ = v___y_1019_;
v___y_1011_ = v___y_1020_;
v_fst_1012_ = v___x_1024_;
v_snd_1013_ = v_snd_1023_;
goto v___jp_1009_;
}
v___jp_1025_:
{
lean_object* v___x_1027_; lean_object* v___f_1028_; 
v___x_1027_ = lean_box(v___y_1026_);
v___f_1028_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1028_, 0, v___x_1027_);
if (lean_obj_tag(v_val_921_) == 0)
{
lean_object* v_type_1029_; lean_object* v___x_1030_; lean_object* v_mctx_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v_type_1029_ = lean_ctor_get(v_val_921_, 3);
v___x_1030_ = lean_st_ref_get(v___y_901_);
v_mctx_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc_ref_n(v_mctx_1031_, 2);
lean_dec(v___x_1030_);
v___x_1032_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2);
v___x_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
lean_ctor_set(v___x_1033_, 1, v_mctx_1031_);
v___x_1034_ = l_Lean_Expr_hasFVar(v_type_1029_);
if (v___x_1034_ == 0)
{
uint8_t v___x_1035_; 
v___x_1035_ = l_Lean_Expr_hasMVar(v_type_1029_);
if (v___x_1035_ == 0)
{
lean_dec_ref_known(v___x_1033_, 2);
lean_dec_ref(v___f_1028_);
lean_dec_ref(v___f_1008_);
v_fst_939_ = v___x_1035_;
v_mctx_940_ = v_mctx_1031_;
goto v___jp_938_;
}
else
{
lean_object* v___x_1036_; 
lean_dec_ref(v_mctx_1031_);
lean_inc_ref(v_type_1029_);
v___x_1036_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1008_, v___f_1028_, v_type_1029_, v___x_1033_);
v___y_956_ = v___x_1036_;
goto v___jp_955_;
}
}
else
{
lean_object* v___x_1037_; 
lean_dec_ref(v_mctx_1031_);
lean_inc_ref(v_type_1029_);
v___x_1037_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1008_, v___f_1028_, v_type_1029_, v___x_1033_);
v___y_956_ = v___x_1037_;
goto v___jp_955_;
}
}
else
{
uint8_t v_nondep_1038_; 
v_nondep_1038_ = lean_ctor_get_uint8(v_val_921_, sizeof(void*)*5);
if (v_nondep_1038_ == 0)
{
lean_object* v_type_1039_; lean_object* v_value_1040_; lean_object* v___x_1041_; lean_object* v_mctx_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v_type_1039_ = lean_ctor_get(v_val_921_, 3);
v_value_1040_ = lean_ctor_get(v_val_921_, 4);
v___x_1041_ = lean_st_ref_get(v___y_901_);
v_mctx_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc_ref(v_mctx_1042_);
lean_dec(v___x_1041_);
v___x_1043_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2);
v___x_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
lean_ctor_set(v___x_1044_, 1, v_mctx_1042_);
v___x_1045_ = l_Lean_Expr_hasFVar(v_type_1039_);
if (v___x_1045_ == 0)
{
uint8_t v___x_1046_; 
v___x_1046_ = l_Lean_Expr_hasMVar(v_type_1039_);
if (v___x_1046_ == 0)
{
lean_inc_ref(v_value_1040_);
v___y_1010_ = v_value_1040_;
v___y_1011_ = v___f_1028_;
v_fst_1012_ = v___x_1046_;
v_snd_1013_ = v___x_1044_;
goto v___jp_1009_;
}
else
{
lean_object* v___x_1047_; 
lean_inc_ref(v_type_1039_);
lean_inc_ref(v___f_1028_);
lean_inc_ref(v___f_1008_);
v___x_1047_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1008_, v___f_1028_, v_type_1039_, v___x_1044_);
lean_inc_ref(v_value_1040_);
v___y_1019_ = v_value_1040_;
v___y_1020_ = v___f_1028_;
v___y_1021_ = v___x_1047_;
goto v___jp_1018_;
}
}
else
{
lean_object* v___x_1048_; 
lean_inc_ref(v_type_1039_);
lean_inc_ref(v___f_1028_);
lean_inc_ref(v___f_1008_);
v___x_1048_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1008_, v___f_1028_, v_type_1039_, v___x_1044_);
lean_inc_ref(v_value_1040_);
v___y_1019_ = v_value_1040_;
v___y_1020_ = v___f_1028_;
v___y_1021_ = v___x_1048_;
goto v___jp_1018_;
}
}
else
{
lean_object* v_type_1049_; lean_object* v___x_1050_; lean_object* v_mctx_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v_type_1049_ = lean_ctor_get(v_val_921_, 3);
v___x_1050_ = lean_st_ref_get(v___y_901_);
v_mctx_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc_ref_n(v_mctx_1051_, 2);
lean_dec(v___x_1050_);
v___x_1052_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2);
v___x_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
lean_ctor_set(v___x_1053_, 1, v_mctx_1051_);
v___x_1054_ = l_Lean_Expr_hasFVar(v_type_1049_);
if (v___x_1054_ == 0)
{
uint8_t v___x_1055_; 
v___x_1055_ = l_Lean_Expr_hasMVar(v_type_1049_);
if (v___x_1055_ == 0)
{
lean_dec_ref_known(v___x_1053_, 2);
lean_dec_ref(v___f_1028_);
lean_dec_ref(v___f_1008_);
v_fst_985_ = v___x_1055_;
v_mctx_986_ = v_mctx_1051_;
goto v___jp_984_;
}
else
{
lean_object* v___x_1056_; 
lean_dec_ref(v_mctx_1051_);
lean_inc_ref(v_type_1049_);
v___x_1056_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1008_, v___f_1028_, v_type_1049_, v___x_1053_);
v___y_1002_ = v___x_1056_;
goto v___jp_1001_;
}
}
else
{
lean_object* v___x_1057_; 
lean_dec_ref(v_mctx_1051_);
lean_inc_ref(v_type_1049_);
v___x_1057_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1008_, v___f_1028_, v_type_1049_, v___x_1053_);
v___y_1002_ = v___x_1057_;
goto v___jp_1001_;
}
}
}
}
v___jp_1058_:
{
if (v___y_1059_ == 0)
{
if (v_ignoreLetDecls_894_ == 0)
{
lean_del_object(v___x_925_);
v___y_1026_ = v_ignoreLetDecls_894_;
goto v___jp_1025_;
}
else
{
uint8_t v___x_1060_; 
v___x_1060_ = l_Lean_LocalDecl_isLet(v_val_921_, v___y_1059_);
if (v___x_1060_ == 0)
{
lean_del_object(v___x_925_);
v___y_1026_ = v___x_1060_;
goto v___jp_1025_;
}
else
{
lean_dec_ref(v___f_1008_);
lean_dec(v___x_931_);
goto v___jp_927_;
}
}
}
else
{
lean_dec_ref(v___f_1008_);
lean_dec(v___x_931_);
goto v___jp_927_;
}
}
}
else
{
lean_object* v___x_1064_; 
lean_dec(v___x_931_);
lean_del_object(v___x_925_);
v___x_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1064_, 0, v_fst_922_);
lean_ctor_set(v___x_1064_, 1, v_snd_923_);
v_a_913_ = v___x_1064_;
goto v___jp_912_;
}
v___jp_927_:
{
lean_object* v___x_929_; 
if (v_isShared_926_ == 0)
{
v___x_929_ = v___x_925_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_fst_922_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v_snd_923_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
v_a_913_ = v___x_929_;
goto v___jp_912_;
}
}
v___jp_932_:
{
if (v_a_933_ == 0)
{
lean_object* v___x_934_; 
lean_dec(v___x_931_);
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v_fst_922_);
lean_ctor_set(v___x_934_, 1, v_snd_923_);
v_a_913_ = v___x_934_;
goto v___jp_912_;
}
else
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
lean_inc(v___x_931_);
v___x_935_ = l_Lean_FVarIdSet_insert(v_snd_923_, v___x_931_);
v___x_936_ = l_Lean_FVarIdSet_insert(v_fst_922_, v___x_931_);
v___x_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
lean_ctor_set(v___x_937_, 1, v___x_935_);
v_a_913_ = v___x_937_;
goto v___jp_912_;
}
}
v___jp_938_:
{
lean_object* v___x_941_; lean_object* v_cache_942_; lean_object* v_zetaDeltaFVarIds_943_; lean_object* v_postponed_944_; lean_object* v_diag_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_953_; 
v___x_941_ = lean_st_ref_take(v___y_901_);
v_cache_942_ = lean_ctor_get(v___x_941_, 1);
v_zetaDeltaFVarIds_943_ = lean_ctor_get(v___x_941_, 2);
v_postponed_944_ = lean_ctor_get(v___x_941_, 3);
v_diag_945_ = lean_ctor_get(v___x_941_, 4);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_953_ == 0)
{
lean_object* v_unused_954_; 
v_unused_954_ = lean_ctor_get(v___x_941_, 0);
lean_dec(v_unused_954_);
v___x_947_ = v___x_941_;
v_isShared_948_ = v_isSharedCheck_953_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_diag_945_);
lean_inc(v_postponed_944_);
lean_inc(v_zetaDeltaFVarIds_943_);
lean_inc(v_cache_942_);
lean_dec(v___x_941_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_953_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 0, v_mctx_940_);
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_mctx_940_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_cache_942_);
lean_ctor_set(v_reuseFailAlloc_952_, 2, v_zetaDeltaFVarIds_943_);
lean_ctor_set(v_reuseFailAlloc_952_, 3, v_postponed_944_);
lean_ctor_set(v_reuseFailAlloc_952_, 4, v_diag_945_);
v___x_950_ = v_reuseFailAlloc_952_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_951_; 
v___x_951_ = lean_st_ref_put(v___y_901_, v___x_950_);
v_a_933_ = v_fst_939_;
goto v___jp_932_;
}
}
}
v___jp_955_:
{
lean_object* v_snd_957_; lean_object* v_fst_958_; lean_object* v_mctx_959_; uint8_t v___x_960_; 
v_snd_957_ = lean_ctor_get(v___y_956_, 1);
lean_inc(v_snd_957_);
v_fst_958_ = lean_ctor_get(v___y_956_, 0);
lean_inc(v_fst_958_);
lean_dec_ref(v___y_956_);
v_mctx_959_ = lean_ctor_get(v_snd_957_, 1);
lean_inc_ref(v_mctx_959_);
lean_dec(v_snd_957_);
v___x_960_ = lean_unbox(v_fst_958_);
lean_dec(v_fst_958_);
v_fst_939_ = v___x_960_;
v_mctx_940_ = v_mctx_959_;
goto v___jp_938_;
}
v___jp_961_:
{
lean_object* v_mctx_964_; lean_object* v___x_965_; lean_object* v_cache_966_; lean_object* v_zetaDeltaFVarIds_967_; lean_object* v_postponed_968_; lean_object* v_diag_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_977_; 
v_mctx_964_ = lean_ctor_get(v_snd_963_, 1);
lean_inc_ref(v_mctx_964_);
lean_dec_ref(v_snd_963_);
v___x_965_ = lean_st_ref_take(v___y_901_);
v_cache_966_ = lean_ctor_get(v___x_965_, 1);
v_zetaDeltaFVarIds_967_ = lean_ctor_get(v___x_965_, 2);
v_postponed_968_ = lean_ctor_get(v___x_965_, 3);
v_diag_969_ = lean_ctor_get(v___x_965_, 4);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_977_ == 0)
{
lean_object* v_unused_978_; 
v_unused_978_ = lean_ctor_get(v___x_965_, 0);
lean_dec(v_unused_978_);
v___x_971_ = v___x_965_;
v_isShared_972_ = v_isSharedCheck_977_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_diag_969_);
lean_inc(v_postponed_968_);
lean_inc(v_zetaDeltaFVarIds_967_);
lean_inc(v_cache_966_);
lean_dec(v___x_965_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_977_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v_mctx_964_);
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_mctx_964_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_cache_966_);
lean_ctor_set(v_reuseFailAlloc_976_, 2, v_zetaDeltaFVarIds_967_);
lean_ctor_set(v_reuseFailAlloc_976_, 3, v_postponed_968_);
lean_ctor_set(v_reuseFailAlloc_976_, 4, v_diag_969_);
v___x_974_ = v_reuseFailAlloc_976_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_object* v___x_975_; 
v___x_975_ = lean_st_ref_put(v___y_901_, v___x_974_);
v_a_933_ = v_fst_962_;
goto v___jp_932_;
}
}
}
v___jp_979_:
{
lean_object* v_fst_981_; lean_object* v_snd_982_; uint8_t v___x_983_; 
v_fst_981_ = lean_ctor_get(v___y_980_, 0);
lean_inc(v_fst_981_);
v_snd_982_ = lean_ctor_get(v___y_980_, 1);
lean_inc(v_snd_982_);
lean_dec_ref(v___y_980_);
v___x_983_ = lean_unbox(v_fst_981_);
lean_dec(v_fst_981_);
v_fst_962_ = v___x_983_;
v_snd_963_ = v_snd_982_;
goto v___jp_961_;
}
v___jp_984_:
{
lean_object* v___x_987_; lean_object* v_cache_988_; lean_object* v_zetaDeltaFVarIds_989_; lean_object* v_postponed_990_; lean_object* v_diag_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_999_; 
v___x_987_ = lean_st_ref_take(v___y_901_);
v_cache_988_ = lean_ctor_get(v___x_987_, 1);
v_zetaDeltaFVarIds_989_ = lean_ctor_get(v___x_987_, 2);
v_postponed_990_ = lean_ctor_get(v___x_987_, 3);
v_diag_991_ = lean_ctor_get(v___x_987_, 4);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_999_ == 0)
{
lean_object* v_unused_1000_; 
v_unused_1000_ = lean_ctor_get(v___x_987_, 0);
lean_dec(v_unused_1000_);
v___x_993_ = v___x_987_;
v_isShared_994_ = v_isSharedCheck_999_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_diag_991_);
lean_inc(v_postponed_990_);
lean_inc(v_zetaDeltaFVarIds_989_);
lean_inc(v_cache_988_);
lean_dec(v___x_987_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_999_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v_mctx_986_);
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_mctx_986_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_cache_988_);
lean_ctor_set(v_reuseFailAlloc_998_, 2, v_zetaDeltaFVarIds_989_);
lean_ctor_set(v_reuseFailAlloc_998_, 3, v_postponed_990_);
lean_ctor_set(v_reuseFailAlloc_998_, 4, v_diag_991_);
v___x_996_ = v_reuseFailAlloc_998_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_997_; 
v___x_997_ = lean_st_ref_put(v___y_901_, v___x_996_);
v_a_933_ = v_fst_985_;
goto v___jp_932_;
}
}
}
v___jp_1001_:
{
lean_object* v_snd_1003_; lean_object* v_fst_1004_; lean_object* v_mctx_1005_; uint8_t v___x_1006_; 
v_snd_1003_ = lean_ctor_get(v___y_1002_, 1);
lean_inc(v_snd_1003_);
v_fst_1004_ = lean_ctor_get(v___y_1002_, 0);
lean_inc(v_fst_1004_);
lean_dec_ref(v___y_1002_);
v_mctx_1005_ = lean_ctor_get(v_snd_1003_, 1);
lean_inc_ref(v_mctx_1005_);
lean_dec(v_snd_1003_);
v___x_1006_ = lean_unbox(v_fst_1004_);
lean_dec(v_fst_1004_);
v_fst_985_ = v___x_1006_;
v_mctx_986_ = v_mctx_1005_;
goto v___jp_984_;
}
}
}
v___jp_912_:
{
lean_object* v___x_915_; 
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 1, v_a_913_);
lean_ctor_set(v___x_909_, 0, v___x_911_);
v___x_915_ = v___x_909_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_911_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_a_913_);
v___x_915_ = v_reuseFailAlloc_919_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
size_t v___x_916_; size_t v___x_917_; lean_object* v___x_918_; 
v___x_916_ = ((size_t)1ULL);
v___x_917_ = lean_usize_add(v_i_898_, v___x_916_);
v___x_918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(v_ignoreLetDecls_894_, v_forbidden_895_, v_as_896_, v_sz_897_, v___x_917_, v___x_915_, v___y_901_);
return v___x_918_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2___boxed(lean_object* v_ignoreLetDecls_1068_, lean_object* v_forbidden_1069_, lean_object* v_as_1070_, lean_object* v_sz_1071_, lean_object* v_i_1072_, lean_object* v_b_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1079_; size_t v_sz_boxed_1080_; size_t v_i_boxed_1081_; lean_object* v_res_1082_; 
v_ignoreLetDecls_boxed_1079_ = lean_unbox(v_ignoreLetDecls_1068_);
v_sz_boxed_1080_ = lean_unbox_usize(v_sz_1071_);
lean_dec(v_sz_1071_);
v_i_boxed_1081_ = lean_unbox_usize(v_i_1072_);
lean_dec(v_i_1072_);
v_res_1082_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2(v_ignoreLetDecls_boxed_1079_, v_forbidden_1069_, v_as_1070_, v_sz_boxed_1080_, v_i_boxed_1081_, v_b_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec_ref(v_as_1070_);
lean_dec(v_forbidden_1069_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(lean_object* v_init_1083_, uint8_t v_ignoreLetDecls_1084_, lean_object* v_forbidden_1085_, lean_object* v_n_1086_, lean_object* v_b_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
if (lean_obj_tag(v_n_1086_) == 0)
{
lean_object* v_cs_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; size_t v_sz_1096_; size_t v___x_1097_; lean_object* v___x_1098_; 
v_cs_1093_ = lean_ctor_get(v_n_1086_, 0);
v___x_1094_ = lean_box(0);
v___x_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
lean_ctor_set(v___x_1095_, 1, v_b_1087_);
v_sz_1096_ = lean_array_size(v_cs_1093_);
v___x_1097_ = ((size_t)0ULL);
v___x_1098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(v_init_1083_, v_ignoreLetDecls_1084_, v_forbidden_1085_, v_cs_1093_, v_sz_1096_, v___x_1097_, v___x_1095_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1113_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1101_ = v___x_1098_;
v_isShared_1102_ = v_isSharedCheck_1113_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1098_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1113_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v_fst_1103_; 
v_fst_1103_ = lean_ctor_get(v_a_1099_, 0);
if (lean_obj_tag(v_fst_1103_) == 0)
{
lean_object* v_snd_1104_; lean_object* v___x_1105_; lean_object* v___x_1107_; 
v_snd_1104_ = lean_ctor_get(v_a_1099_, 1);
lean_inc(v_snd_1104_);
lean_dec(v_a_1099_);
v___x_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1105_, 0, v_snd_1104_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1105_);
v___x_1107_ = v___x_1101_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1105_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
else
{
lean_object* v_val_1109_; lean_object* v___x_1111_; 
lean_inc_ref(v_fst_1103_);
lean_dec(v_a_1099_);
v_val_1109_ = lean_ctor_get(v_fst_1103_, 0);
lean_inc(v_val_1109_);
lean_dec_ref_known(v_fst_1103_, 1);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v_val_1109_);
v___x_1111_ = v___x_1101_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_val_1109_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
v_a_1114_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1098_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1098_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
else
{
lean_object* v_vs_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; size_t v_sz_1125_; size_t v___x_1126_; lean_object* v___x_1127_; 
v_vs_1122_ = lean_ctor_get(v_n_1086_, 0);
v___x_1123_ = lean_box(0);
v___x_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
lean_ctor_set(v___x_1124_, 1, v_b_1087_);
v_sz_1125_ = lean_array_size(v_vs_1122_);
v___x_1126_ = ((size_t)0ULL);
v___x_1127_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2(v_ignoreLetDecls_1084_, v_forbidden_1085_, v_vs_1122_, v_sz_1125_, v___x_1126_, v___x_1124_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1142_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1130_ = v___x_1127_;
v_isShared_1131_ = v_isSharedCheck_1142_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1127_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1142_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v_fst_1132_; 
v_fst_1132_ = lean_ctor_get(v_a_1128_, 0);
if (lean_obj_tag(v_fst_1132_) == 0)
{
lean_object* v_snd_1133_; lean_object* v___x_1134_; lean_object* v___x_1136_; 
v_snd_1133_ = lean_ctor_get(v_a_1128_, 1);
lean_inc(v_snd_1133_);
lean_dec(v_a_1128_);
v___x_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1134_, 0, v_snd_1133_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v___x_1134_);
v___x_1136_ = v___x_1130_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
else
{
lean_object* v_val_1138_; lean_object* v___x_1140_; 
lean_inc_ref(v_fst_1132_);
lean_dec(v_a_1128_);
v_val_1138_ = lean_ctor_get(v_fst_1132_, 0);
lean_inc(v_val_1138_);
lean_dec_ref_known(v_fst_1132_, 1);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v_val_1138_);
v___x_1140_ = v___x_1130_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_val_1138_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
else
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
v_a_1143_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1127_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1127_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(lean_object* v_init_1151_, uint8_t v_ignoreLetDecls_1152_, lean_object* v_forbidden_1153_, lean_object* v_as_1154_, size_t v_sz_1155_, size_t v_i_1156_, lean_object* v_b_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
uint8_t v___x_1163_; 
v___x_1163_ = lean_usize_dec_lt(v_i_1156_, v_sz_1155_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1164_, 0, v_b_1157_);
return v___x_1164_;
}
else
{
lean_object* v_snd_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1199_; 
v_snd_1165_ = lean_ctor_get(v_b_1157_, 1);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_b_1157_);
if (v_isSharedCheck_1199_ == 0)
{
lean_object* v_unused_1200_; 
v_unused_1200_ = lean_ctor_get(v_b_1157_, 0);
lean_dec(v_unused_1200_);
v___x_1167_ = v_b_1157_;
v_isShared_1168_ = v_isSharedCheck_1199_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_snd_1165_);
lean_dec(v_b_1157_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1199_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v_a_1169_; lean_object* v___x_1170_; 
v_a_1169_ = lean_array_uget_borrowed(v_as_1154_, v_i_1156_);
lean_inc(v_snd_1165_);
v___x_1170_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(v_init_1151_, v_ignoreLetDecls_1152_, v_forbidden_1153_, v_a_1169_, v_snd_1165_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1190_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1173_ = v___x_1170_;
v_isShared_1174_ = v_isSharedCheck_1190_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1170_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1190_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
if (lean_obj_tag(v_a_1171_) == 0)
{
lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1175_, 0, v_a_1171_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v___x_1175_);
v___x_1177_ = v___x_1167_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_snd_1165_);
v___x_1177_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1179_; 
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 0, v___x_1177_);
v___x_1179_ = v___x_1173_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1177_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
else
{
lean_object* v_a_1182_; lean_object* v___x_1183_; lean_object* v___x_1185_; 
lean_del_object(v___x_1173_);
lean_dec(v_snd_1165_);
v_a_1182_ = lean_ctor_get(v_a_1171_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v_a_1171_, 1);
v___x_1183_ = lean_box(0);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 1, v_a_1182_);
lean_ctor_set(v___x_1167_, 0, v___x_1183_);
v___x_1185_ = v___x_1167_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1183_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_a_1182_);
v___x_1185_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
size_t v___x_1186_; size_t v___x_1187_; 
v___x_1186_ = ((size_t)1ULL);
v___x_1187_ = lean_usize_add(v_i_1156_, v___x_1186_);
v_i_1156_ = v___x_1187_;
v_b_1157_ = v___x_1185_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
lean_del_object(v___x_1167_);
lean_dec(v_snd_1165_);
v_a_1191_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1170_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1170_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1___boxed(lean_object* v_init_1201_, lean_object* v_ignoreLetDecls_1202_, lean_object* v_forbidden_1203_, lean_object* v_as_1204_, lean_object* v_sz_1205_, lean_object* v_i_1206_, lean_object* v_b_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1213_; size_t v_sz_boxed_1214_; size_t v_i_boxed_1215_; lean_object* v_res_1216_; 
v_ignoreLetDecls_boxed_1213_ = lean_unbox(v_ignoreLetDecls_1202_);
v_sz_boxed_1214_ = lean_unbox_usize(v_sz_1205_);
lean_dec(v_sz_1205_);
v_i_boxed_1215_ = lean_unbox_usize(v_i_1206_);
lean_dec(v_i_1206_);
v_res_1216_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(v_init_1201_, v_ignoreLetDecls_boxed_1213_, v_forbidden_1203_, v_as_1204_, v_sz_boxed_1214_, v_i_boxed_1215_, v_b_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec_ref(v_as_1204_);
lean_dec(v_forbidden_1203_);
lean_dec_ref(v_init_1201_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0___boxed(lean_object* v_init_1217_, lean_object* v_ignoreLetDecls_1218_, lean_object* v_forbidden_1219_, lean_object* v_n_1220_, lean_object* v_b_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1227_; lean_object* v_res_1228_; 
v_ignoreLetDecls_boxed_1227_ = lean_unbox(v_ignoreLetDecls_1218_);
v_res_1228_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(v_init_1217_, v_ignoreLetDecls_boxed_1227_, v_forbidden_1219_, v_n_1220_, v_b_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec_ref(v_n_1220_);
lean_dec(v_forbidden_1219_);
lean_dec_ref(v_init_1217_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0(uint8_t v_ignoreLetDecls_1229_, lean_object* v_forbidden_1230_, lean_object* v_t_1231_, lean_object* v_init_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v_root_1238_; lean_object* v_tail_1239_; lean_object* v___x_1240_; 
v_root_1238_ = lean_ctor_get(v_t_1231_, 0);
v_tail_1239_ = lean_ctor_get(v_t_1231_, 1);
lean_inc_ref(v_init_1232_);
v___x_1240_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(v_init_1232_, v_ignoreLetDecls_1229_, v_forbidden_1230_, v_root_1238_, v_init_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
lean_dec_ref(v_init_1232_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1277_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1243_ = v___x_1240_;
v_isShared_1244_ = v_isSharedCheck_1277_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1240_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1277_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
if (lean_obj_tag(v_a_1241_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1247_; 
v_a_1245_ = lean_ctor_get(v_a_1241_, 0);
lean_inc(v_a_1245_);
lean_dec_ref_known(v_a_1241_, 1);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v_a_1245_);
v___x_1247_ = v___x_1243_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1245_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; size_t v_sz_1252_; size_t v___x_1253_; lean_object* v___x_1254_; 
lean_del_object(v___x_1243_);
v_a_1249_ = lean_ctor_get(v_a_1241_, 0);
lean_inc(v_a_1249_);
lean_dec_ref_known(v_a_1241_, 1);
v___x_1250_ = lean_box(0);
v___x_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
lean_ctor_set(v___x_1251_, 1, v_a_1249_);
v_sz_1252_ = lean_array_size(v_tail_1239_);
v___x_1253_ = ((size_t)0ULL);
v___x_1254_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1(v_ignoreLetDecls_1229_, v_forbidden_1230_, v_tail_1239_, v_sz_1252_, v___x_1253_, v___x_1251_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1268_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1257_ = v___x_1254_;
v_isShared_1258_ = v_isSharedCheck_1268_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1254_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1268_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v_fst_1259_; 
v_fst_1259_ = lean_ctor_get(v_a_1255_, 0);
if (lean_obj_tag(v_fst_1259_) == 0)
{
lean_object* v_snd_1260_; lean_object* v___x_1262_; 
v_snd_1260_ = lean_ctor_get(v_a_1255_, 1);
lean_inc(v_snd_1260_);
lean_dec(v_a_1255_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v_snd_1260_);
v___x_1262_ = v___x_1257_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_snd_1260_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
else
{
lean_object* v_val_1264_; lean_object* v___x_1266_; 
lean_inc_ref(v_fst_1259_);
lean_dec(v_a_1255_);
v_val_1264_ = lean_ctor_get(v_fst_1259_, 0);
lean_inc(v_val_1264_);
lean_dec_ref_known(v_fst_1259_, 1);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v_val_1264_);
v___x_1266_ = v___x_1257_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_val_1264_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
v_a_1269_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1254_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1254_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
}
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
v_a_1278_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1240_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1240_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0___boxed(lean_object* v_ignoreLetDecls_1286_, lean_object* v_forbidden_1287_, lean_object* v_t_1288_, lean_object* v_init_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1295_; lean_object* v_res_1296_; 
v_ignoreLetDecls_boxed_1295_ = lean_unbox(v_ignoreLetDecls_1286_);
v_res_1296_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0(v_ignoreLetDecls_boxed_1295_, v_forbidden_1287_, v_t_1288_, v_init_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec_ref(v_t_1288_);
lean_dec(v_forbidden_1287_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(lean_object* v_as_1297_, size_t v_i_1298_, size_t v_stop_1299_, lean_object* v_b_1300_){
_start:
{
lean_object* v___y_1302_; uint8_t v___x_1306_; 
v___x_1306_ = lean_usize_dec_eq(v_i_1298_, v_stop_1299_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1307_ = lean_array_uget_borrowed(v_as_1297_, v_i_1298_);
v___x_1308_ = l_Lean_Expr_isFVar(v___x_1307_);
if (v___x_1308_ == 0)
{
v___y_1302_ = v_b_1300_;
goto v___jp_1301_;
}
else
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = l_Lean_Expr_fvarId_x21(v___x_1307_);
v___x_1310_ = l_Lean_FVarIdSet_insert(v_b_1300_, v___x_1309_);
v___y_1302_ = v___x_1310_;
goto v___jp_1301_;
}
}
else
{
return v_b_1300_;
}
v___jp_1301_:
{
size_t v___x_1303_; size_t v___x_1304_; 
v___x_1303_ = ((size_t)1ULL);
v___x_1304_ = lean_usize_add(v_i_1298_, v___x_1303_);
v_i_1298_ = v___x_1304_;
v_b_1300_ = v___y_1302_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1___boxed(lean_object* v_as_1311_, lean_object* v_i_1312_, lean_object* v_stop_1313_, lean_object* v_b_1314_){
_start:
{
size_t v_i_boxed_1315_; size_t v_stop_boxed_1316_; lean_object* v_res_1317_; 
v_i_boxed_1315_ = lean_unbox_usize(v_i_1312_);
lean_dec(v_i_1312_);
v_stop_boxed_1316_ = lean_unbox_usize(v_stop_1313_);
lean_dec(v_stop_1313_);
v_res_1317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(v_as_1311_, v_i_boxed_1315_, v_stop_boxed_1316_, v_b_1314_);
lean_dec_ref(v_as_1311_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize(lean_object* v_targets_1318_, lean_object* v_forbidden_1319_, uint8_t v_ignoreLetDecls_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v_r_1326_; lean_object* v___y_1328_; lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v_r_1326_ = lean_box(1);
v___x_1350_ = lean_unsigned_to_nat(0u);
v___x_1351_ = lean_array_get_size(v_targets_1318_);
v___x_1352_ = lean_nat_dec_lt(v___x_1350_, v___x_1351_);
if (v___x_1352_ == 0)
{
v___y_1328_ = v_r_1326_;
goto v___jp_1327_;
}
else
{
uint8_t v___x_1353_; 
v___x_1353_ = lean_nat_dec_le(v___x_1351_, v___x_1351_);
if (v___x_1353_ == 0)
{
if (v___x_1352_ == 0)
{
v___y_1328_ = v_r_1326_;
goto v___jp_1327_;
}
else
{
size_t v___x_1354_; size_t v___x_1355_; lean_object* v___x_1356_; 
v___x_1354_ = ((size_t)0ULL);
v___x_1355_ = lean_usize_of_nat(v___x_1351_);
v___x_1356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(v_targets_1318_, v___x_1354_, v___x_1355_, v_r_1326_);
v___y_1328_ = v___x_1356_;
goto v___jp_1327_;
}
}
else
{
size_t v___x_1357_; size_t v___x_1358_; lean_object* v___x_1359_; 
v___x_1357_ = ((size_t)0ULL);
v___x_1358_ = lean_usize_of_nat(v___x_1351_);
v___x_1359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(v_targets_1318_, v___x_1357_, v___x_1358_, v_r_1326_);
v___y_1328_ = v___x_1359_;
goto v___jp_1327_;
}
}
v___jp_1327_:
{
lean_object* v_lctx_1329_; lean_object* v_decls_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v_lctx_1329_ = lean_ctor_get(v_a_1321_, 2);
v_decls_1330_ = lean_ctor_get(v_lctx_1329_, 1);
v___x_1331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___y_1328_);
lean_ctor_set(v___x_1331_, 1, v_r_1326_);
v___x_1332_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0(v_ignoreLetDecls_1320_, v_forbidden_1319_, v_decls_1330_, v___x_1331_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1341_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1335_ = v___x_1332_;
v_isShared_1336_ = v_isSharedCheck_1341_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1332_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1341_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v_snd_1337_; lean_object* v___x_1339_; 
v_snd_1337_ = lean_ctor_get(v_a_1333_, 1);
lean_inc(v_snd_1337_);
lean_dec(v_a_1333_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v_snd_1337_);
v___x_1339_ = v___x_1335_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_snd_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
v_a_1342_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1332_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1332_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize___boxed(lean_object* v_targets_1360_, lean_object* v_forbidden_1361_, lean_object* v_ignoreLetDecls_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1368_; lean_object* v_res_1369_; 
v_ignoreLetDecls_boxed_1368_ = lean_unbox(v_ignoreLetDecls_1362_);
v_res_1369_ = l_Lean_Meta_getFVarSetToGeneralize(v_targets_1360_, v_forbidden_1361_, v_ignoreLetDecls_boxed_1368_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
lean_dec(v_a_1364_);
lean_dec_ref(v_a_1363_);
lean_dec(v_forbidden_1361_);
lean_dec_ref(v_targets_1360_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4(uint8_t v_ignoreLetDecls_1370_, lean_object* v_forbidden_1371_, lean_object* v_as_1372_, size_t v_sz_1373_, size_t v_i_1374_, lean_object* v_b_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(v_ignoreLetDecls_1370_, v_forbidden_1371_, v_as_1372_, v_sz_1373_, v_i_1374_, v_b_1375_, v___y_1377_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___boxed(lean_object* v_ignoreLetDecls_1382_, lean_object* v_forbidden_1383_, lean_object* v_as_1384_, lean_object* v_sz_1385_, lean_object* v_i_1386_, lean_object* v_b_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1393_; size_t v_sz_boxed_1394_; size_t v_i_boxed_1395_; lean_object* v_res_1396_; 
v_ignoreLetDecls_boxed_1393_ = lean_unbox(v_ignoreLetDecls_1382_);
v_sz_boxed_1394_ = lean_unbox_usize(v_sz_1385_);
lean_dec(v_sz_1385_);
v_i_boxed_1395_ = lean_unbox_usize(v_i_1386_);
lean_dec(v_i_1386_);
v_res_1396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4(v_ignoreLetDecls_boxed_1393_, v_forbidden_1383_, v_as_1384_, v_sz_boxed_1394_, v_i_boxed_1395_, v_b_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec_ref(v_as_1384_);
lean_dec(v_forbidden_1383_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4(uint8_t v_ignoreLetDecls_1397_, lean_object* v_forbidden_1398_, lean_object* v_as_1399_, size_t v_sz_1400_, size_t v_i_1401_, lean_object* v_b_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(v_ignoreLetDecls_1397_, v_forbidden_1398_, v_as_1399_, v_sz_1400_, v_i_1401_, v_b_1402_, v___y_1404_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_ignoreLetDecls_1409_, lean_object* v_forbidden_1410_, lean_object* v_as_1411_, lean_object* v_sz_1412_, lean_object* v_i_1413_, lean_object* v_b_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1420_; size_t v_sz_boxed_1421_; size_t v_i_boxed_1422_; lean_object* v_res_1423_; 
v_ignoreLetDecls_boxed_1420_ = lean_unbox(v_ignoreLetDecls_1409_);
v_sz_boxed_1421_ = lean_unbox_usize(v_sz_1412_);
lean_dec(v_sz_1412_);
v_i_boxed_1422_ = lean_unbox_usize(v_i_1413_);
lean_dec(v_i_1413_);
v_res_1423_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4(v_ignoreLetDecls_boxed_1420_, v_forbidden_1410_, v_as_1411_, v_sz_boxed_1421_, v_i_boxed_1422_, v_b_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec_ref(v_as_1411_);
lean_dec(v_forbidden_1410_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(lean_object* v_init_1424_, lean_object* v_x_1425_){
_start:
{
if (lean_obj_tag(v_x_1425_) == 0)
{
lean_object* v_k_1426_; lean_object* v_l_1427_; lean_object* v_r_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v_k_1426_ = lean_ctor_get(v_x_1425_, 1);
lean_inc(v_k_1426_);
v_l_1427_ = lean_ctor_get(v_x_1425_, 3);
lean_inc(v_l_1427_);
v_r_1428_ = lean_ctor_get(v_x_1425_, 4);
lean_inc(v_r_1428_);
lean_dec_ref_known(v_x_1425_, 5);
v___x_1429_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(v_init_1424_, v_l_1427_);
v___x_1430_ = lean_array_push(v___x_1429_, v_k_1426_);
v_init_1424_ = v___x_1430_;
v_x_1425_ = v_r_1428_;
goto _start;
}
else
{
return v_init_1424_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize(lean_object* v_targets_1432_, lean_object* v_forbidden_1433_, uint8_t v_ignoreLetDecls_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_Meta_mkGeneralizationForbiddenSet(v_targets_1432_, v_forbidden_1433_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v___x_1442_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_a_1441_);
lean_dec_ref_known(v___x_1440_, 1);
v___x_1442_ = l_Lean_Meta_getFVarSetToGeneralize(v_targets_1432_, v_a_1441_, v_ignoreLetDecls_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_);
lean_dec(v_a_1441_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; lean_object* v___y_1445_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc(v_a_1443_);
lean_dec_ref_known(v___x_1442_, 1);
if (lean_obj_tag(v_a_1443_) == 0)
{
lean_object* v_size_1449_; 
v_size_1449_ = lean_ctor_get(v_a_1443_, 0);
lean_inc(v_size_1449_);
v___y_1445_ = v_size_1449_;
goto v___jp_1444_;
}
else
{
lean_object* v___x_1450_; 
v___x_1450_ = lean_unsigned_to_nat(0u);
v___y_1445_ = v___x_1450_;
goto v___jp_1444_;
}
v___jp_1444_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1446_ = lean_mk_empty_array_with_capacity(v___y_1445_);
lean_dec(v___y_1445_);
v___x_1447_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(v___x_1446_, v_a_1443_);
v___x_1448_ = l_Lean_Meta_sortFVarIds___redArg(v___x_1447_, v_a_1435_);
return v___x_1448_;
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
v_a_1451_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1442_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1442_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
else
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
v_a_1459_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v___x_1440_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1440_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize___boxed(lean_object* v_targets_1467_, lean_object* v_forbidden_1468_, lean_object* v_ignoreLetDecls_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1475_; lean_object* v_res_1476_; 
v_ignoreLetDecls_boxed_1475_ = lean_unbox(v_ignoreLetDecls_1469_);
v_res_1476_ = l_Lean_Meta_getFVarsToGeneralize(v_targets_1467_, v_forbidden_1468_, v_ignoreLetDecls_boxed_1475_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
lean_dec_ref(v_targets_1467_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0(lean_object* v_init_1477_, lean_object* v_t_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(v_init_1477_, v_t_1478_);
return v___x_1479_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_CollectFVars(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_GeneralizeVars(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectFVars(builtin);
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
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_GeneralizeVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_GeneralizeVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_GeneralizeVars(builtin);
}
#ifdef __cplusplus
}
#endif
