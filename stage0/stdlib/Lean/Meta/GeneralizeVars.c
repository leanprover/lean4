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
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
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
static const lean_array_object l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2 = (const lean_object*)&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = lean_box(0);
v___x_91_ = lean_unsigned_to_nat(16u);
v___x_92_ = lean_mk_array(v___x_91_, v___x_90_);
return v___x_92_;
}
}
static lean_object* _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0);
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set(v___x_95_, 1, v___x_93_);
return v___x_95_;
}
}
static lean_object* _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_98_ = ((lean_object*)(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2));
v___x_99_ = lean_box(1);
v___x_100_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_101_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v___x_99_);
lean_ctor_set(v___x_101_, 2, v___x_98_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit(lean_object* v_fvarId_102_, lean_object* v_todo_103_, lean_object* v_s_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v_a_111_; lean_object* v_s_x27_123_; lean_object* v___y_124_; lean_object* v___y_125_; lean_object* v___y_126_; lean_object* v___y_127_; lean_object* v___x_133_; 
v___x_133_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_102_, v_a_105_, v_a_107_, v_a_108_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v_a_137_; lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; lean_object* v___x_141_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_a_134_);
lean_dec_ref_known(v___x_133_, 1);
v___x_135_ = l_Lean_LocalDecl_type(v_a_134_);
v___x_136_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(v___x_135_, v_a_106_);
v_a_137_ = lean_ctor_get(v___x_136_, 0);
lean_inc(v_a_137_);
lean_dec_ref(v___x_136_);
v___x_138_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3);
v___x_139_ = l_Lean_collectFVars(v___x_138_, v_a_137_);
v___x_140_ = 0;
v___x_141_ = l_Lean_LocalDecl_value_x3f(v_a_134_, v___x_140_);
lean_dec(v_a_134_);
if (lean_obj_tag(v___x_141_) == 1)
{
lean_object* v_val_142_; lean_object* v___x_143_; lean_object* v_a_144_; lean_object* v___x_145_; 
v_val_142_ = lean_ctor_get(v___x_141_, 0);
lean_inc(v_val_142_);
lean_dec_ref_known(v___x_141_, 1);
v___x_143_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(v_val_142_, v_a_106_);
v_a_144_ = lean_ctor_get(v___x_143_, 0);
lean_inc(v_a_144_);
lean_dec_ref(v___x_143_);
v___x_145_ = l_Lean_collectFVars(v___x_139_, v_a_144_);
v_s_x27_123_ = v___x_145_;
v___y_124_ = v_a_105_;
v___y_125_ = v_a_106_;
v___y_126_ = v_a_107_;
v___y_127_ = v_a_108_;
goto v___jp_122_;
}
else
{
lean_dec(v___x_141_);
v_s_x27_123_ = v___x_139_;
v___y_124_ = v_a_105_;
v___y_125_ = v_a_106_;
v___y_126_ = v_a_107_;
v___y_127_ = v_a_108_;
goto v___jp_122_;
}
}
else
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
lean_dec(v_s_104_);
lean_dec(v_todo_103_);
v_a_146_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___x_133_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_133_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
v___jp_110_:
{
lean_object* v_fst_112_; lean_object* v_snd_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_121_; 
v_fst_112_ = lean_ctor_get(v_a_111_, 0);
v_snd_113_ = lean_ctor_get(v_a_111_, 1);
v_isSharedCheck_121_ = !lean_is_exclusive(v_a_111_);
if (v_isSharedCheck_121_ == 0)
{
v___x_115_ = v_a_111_;
v_isShared_116_ = v_isSharedCheck_121_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_snd_113_);
lean_inc(v_fst_112_);
lean_dec(v_a_111_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_121_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_118_; 
if (v_isShared_116_ == 0)
{
v___x_118_ = v___x_115_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_fst_112_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v_snd_113_);
v___x_118_ = v_reuseFailAlloc_120_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
lean_object* v___x_119_; 
v___x_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
return v___x_119_;
}
}
}
v___jp_122_:
{
lean_object* v_fvarSet_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v_a_131_; lean_object* v_a_132_; 
v_fvarSet_128_ = lean_ctor_get(v_s_x27_123_, 1);
lean_inc(v_fvarSet_128_);
lean_dec_ref(v_s_x27_123_);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v_todo_103_);
lean_ctor_set(v___x_129_, 1, v_s_104_);
v___x_130_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(v___x_129_, v_fvarSet_128_);
v_a_131_ = lean_ctor_get(v___x_130_, 0);
lean_inc(v_a_131_);
lean_dec_ref(v___x_130_);
v_a_132_ = lean_ctor_get(v_a_131_, 0);
lean_inc(v_a_132_);
lean_dec(v_a_131_);
v_a_111_ = v_a_132_;
goto v___jp_110_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___boxed(lean_object* v_fvarId_154_, lean_object* v_todo_155_, lean_object* v_s_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit(v_fvarId_154_, v_todo_155_, v_s_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
lean_dec(v_a_158_);
lean_dec_ref(v_a_157_);
return v_res_162_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0(lean_object* v_00_u03b2_163_, lean_object* v_k_164_, lean_object* v_t_165_){
_start:
{
uint8_t v___x_166_; 
v___x_166_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v_k_164_, v_t_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___boxed(lean_object* v_00_u03b2_167_, lean_object* v_k_168_, lean_object* v_t_169_){
_start:
{
uint8_t v_res_170_; lean_object* v_r_171_; 
v_res_170_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0(v_00_u03b2_167_, v_k_168_, v_t_169_);
lean_dec(v_t_169_);
lean_dec(v_k_168_);
v_r_171_ = lean_box(v_res_170_);
return v_r_171_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1(lean_object* v_init_172_, lean_object* v_x_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(v_init_172_, v_x_173_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___boxed(lean_object* v_init_180_, lean_object* v_x_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1(v_init_180_, v_x_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop(lean_object* v_todo_188_, lean_object* v_s_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
if (lean_obj_tag(v_todo_188_) == 0)
{
lean_object* v___x_195_; 
v___x_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_195_, 0, v_s_189_);
return v___x_195_;
}
else
{
lean_object* v_head_196_; lean_object* v_tail_197_; uint8_t v___x_198_; 
v_head_196_ = lean_ctor_get(v_todo_188_, 0);
lean_inc(v_head_196_);
v_tail_197_ = lean_ctor_get(v_todo_188_, 1);
lean_inc(v_tail_197_);
lean_dec_ref_known(v_todo_188_, 2);
v___x_198_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v_head_196_, v_s_189_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; 
lean_inc(v_head_196_);
v___x_199_ = l_Lean_FVarIdSet_insert(v_s_189_, v_head_196_);
v___x_200_ = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit(v_head_196_, v_tail_197_, v___x_199_, v_a_190_, v_a_191_, v_a_192_, v_a_193_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v_fst_202_; lean_object* v_snd_203_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_a_201_);
lean_dec_ref_known(v___x_200_, 1);
v_fst_202_ = lean_ctor_get(v_a_201_, 0);
lean_inc(v_fst_202_);
v_snd_203_ = lean_ctor_get(v_a_201_, 1);
lean_inc(v_snd_203_);
lean_dec(v_a_201_);
v_todo_188_ = v_fst_202_;
v_s_189_ = v_snd_203_;
goto _start;
}
else
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_212_; 
v_a_205_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_212_ == 0)
{
v___x_207_ = v___x_200_;
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_200_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; 
if (v_isShared_208_ == 0)
{
v___x_210_ = v___x_207_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_a_205_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
else
{
lean_dec(v_head_196_);
v_todo_188_ = v_tail_197_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop___boxed(lean_object* v_todo_214_, lean_object* v_s_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop(v_todo_214_, v_s_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0(lean_object* v_as_222_, size_t v_sz_223_, size_t v_i_224_, lean_object* v_b_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v_a_232_; uint8_t v___x_236_; 
v___x_236_ = lean_usize_dec_lt(v_i_224_, v_sz_223_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; 
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v_b_225_);
return v___x_237_;
}
else
{
lean_object* v_fst_238_; lean_object* v_snd_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_274_; 
v_fst_238_ = lean_ctor_get(v_b_225_, 0);
v_snd_239_ = lean_ctor_get(v_b_225_, 1);
v_isSharedCheck_274_ = !lean_is_exclusive(v_b_225_);
if (v_isSharedCheck_274_ == 0)
{
v___x_241_ = v_b_225_;
v_isShared_242_ = v_isSharedCheck_274_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_snd_239_);
lean_inc(v_fst_238_);
lean_dec(v_b_225_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_274_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v_a_243_; uint8_t v___x_244_; 
v_a_243_ = lean_array_uget_borrowed(v_as_222_, v_i_224_);
v___x_244_ = l_Lean_Expr_isFVar(v_a_243_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; 
lean_inc(v___y_229_);
lean_inc_ref(v___y_228_);
lean_inc(v___y_227_);
lean_inc_ref(v___y_226_);
lean_inc(v_a_243_);
v___x_245_ = lean_infer_type(v_a_243_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_a_246_; lean_object* v___x_247_; 
v_a_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_a_246_);
lean_dec_ref_known(v___x_245_, 1);
v___x_247_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(v_a_246_, v___y_227_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v_a_248_; lean_object* v___x_249_; lean_object* v___x_251_; 
v_a_248_ = lean_ctor_get(v___x_247_, 0);
lean_inc(v_a_248_);
lean_dec_ref_known(v___x_247_, 1);
v___x_249_ = l_Lean_collectFVars(v_fst_238_, v_a_248_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 0, v___x_249_);
v___x_251_ = v___x_241_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_snd_239_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
v_a_232_ = v___x_251_;
goto v___jp_231_;
}
}
else
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
lean_del_object(v___x_241_);
lean_dec(v_snd_239_);
lean_dec(v_fst_238_);
v_a_253_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_247_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_247_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_253_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
lean_del_object(v___x_241_);
lean_dec(v_snd_239_);
lean_dec(v_fst_238_);
v_a_261_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_245_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_245_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
else
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_269_ = l_Lean_Expr_fvarId_x21(v_a_243_);
v___x_270_ = lean_array_push(v_snd_239_, v___x_269_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 1, v___x_270_);
v___x_272_ = v___x_241_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_fst_238_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v___x_270_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
v_a_232_ = v___x_272_;
goto v___jp_231_;
}
}
}
}
v___jp_231_:
{
size_t v___x_233_; size_t v___x_234_; 
v___x_233_ = ((size_t)1ULL);
v___x_234_ = lean_usize_add(v_i_224_, v___x_233_);
v_i_224_ = v___x_234_;
v_b_225_ = v_a_232_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0___boxed(lean_object* v_as_275_, lean_object* v_sz_276_, lean_object* v_i_277_, lean_object* v_b_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
size_t v_sz_boxed_284_; size_t v_i_boxed_285_; lean_object* v_res_286_; 
v_sz_boxed_284_ = lean_unbox_usize(v_sz_276_);
lean_dec(v_sz_276_);
v_i_boxed_285_ = lean_unbox_usize(v_i_277_);
lean_dec(v_i_277_);
v_res_286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0(v_as_275_, v_sz_boxed_284_, v_i_boxed_285_, v_b_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec_ref(v_as_275_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet(lean_object* v_targets_287_, lean_object* v_forbidden_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_object* v___x_294_; lean_object* v_todo_295_; lean_object* v_s_296_; lean_object* v___x_297_; size_t v_sz_298_; size_t v___x_299_; lean_object* v___x_300_; 
v___x_294_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v_todo_295_ = ((lean_object*)(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2));
v_s_296_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_s_296_, 0, v___x_294_);
lean_ctor_set(v_s_296_, 1, v_forbidden_288_);
lean_ctor_set(v_s_296_, 2, v_todo_295_);
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v_s_296_);
lean_ctor_set(v___x_297_, 1, v_todo_295_);
v_sz_298_ = lean_array_size(v_targets_287_);
v___x_299_ = ((size_t)0ULL);
v___x_300_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0(v_targets_287_, v_sz_298_, v___x_299_, v___x_297_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v_fst_302_; lean_object* v_snd_303_; lean_object* v_fvarSet_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_a_301_);
lean_dec_ref_known(v___x_300_, 1);
v_fst_302_ = lean_ctor_get(v_a_301_, 0);
lean_inc(v_fst_302_);
v_snd_303_ = lean_ctor_get(v_a_301_, 1);
lean_inc(v_snd_303_);
lean_dec(v_a_301_);
v_fvarSet_304_ = lean_ctor_get(v_fst_302_, 1);
lean_inc(v_fvarSet_304_);
lean_dec(v_fst_302_);
v___x_305_ = lean_array_to_list(v_snd_303_);
v___x_306_ = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop(v___x_305_, v_fvarSet_304_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
return v___x_306_;
}
else
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
v_a_307_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_314_ == 0)
{
v___x_309_ = v___x_300_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_300_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_307_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet___boxed(lean_object* v_targets_315_, lean_object* v_forbidden_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_Meta_mkGeneralizationForbiddenSet(v_targets_315_, v_forbidden_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
lean_dec_ref(v_targets_315_);
return v_res_322_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1(uint8_t v___y_323_, lean_object* v_x_324_){
_start:
{
return v___y_323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed(lean_object* v___y_325_, lean_object* v_x_326_){
_start:
{
uint8_t v___y_8904__boxed_327_; uint8_t v_res_328_; lean_object* v_r_329_; 
v___y_8904__boxed_327_ = lean_unbox(v___y_325_);
v_res_328_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1(v___y_8904__boxed_327_, v_x_326_);
lean_dec(v_x_326_);
v_r_329_ = lean_box(v_res_328_);
return v_r_329_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0(lean_object* v_fst_330_, lean_object* v_x_331_){
_start:
{
uint8_t v___x_332_; 
v___x_332_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v_x_331_, v_fst_330_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed(lean_object* v_fst_333_, lean_object* v_x_334_){
_start:
{
uint8_t v_res_335_; lean_object* v_r_336_; 
v_res_335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0(v_fst_333_, v_x_334_);
lean_dec(v_x_334_);
lean_dec(v_fst_333_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(lean_object* v_forbidden_337_, uint8_t v_ignoreLetDecls_338_, lean_object* v_as_339_, size_t v_sz_340_, size_t v_i_341_, lean_object* v_b_342_, lean_object* v___y_343_){
_start:
{
uint8_t v___x_345_; 
v___x_345_ = lean_usize_dec_lt(v_i_341_, v_sz_340_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; 
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v_b_342_);
return v___x_346_;
}
else
{
lean_object* v_snd_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_505_; 
v_snd_347_ = lean_ctor_get(v_b_342_, 1);
v_isSharedCheck_505_ = !lean_is_exclusive(v_b_342_);
if (v_isSharedCheck_505_ == 0)
{
lean_object* v_unused_506_; 
v_unused_506_ = lean_ctor_get(v_b_342_, 0);
lean_dec(v_unused_506_);
v___x_349_ = v_b_342_;
v_isShared_350_ = v_isSharedCheck_505_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_snd_347_);
lean_dec(v_b_342_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_505_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; lean_object* v_a_353_; lean_object* v_a_360_; 
v___x_351_ = lean_box(0);
v_a_360_ = lean_array_uget_borrowed(v_as_339_, v_i_341_);
if (lean_obj_tag(v_a_360_) == 0)
{
v_a_353_ = v_snd_347_;
goto v___jp_352_;
}
else
{
lean_object* v_val_361_; lean_object* v_fst_362_; lean_object* v_snd_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_504_; 
v_val_361_ = lean_ctor_get(v_a_360_, 0);
v_fst_362_ = lean_ctor_get(v_snd_347_, 0);
v_snd_363_ = lean_ctor_get(v_snd_347_, 1);
v_isSharedCheck_504_ = !lean_is_exclusive(v_snd_347_);
if (v_isSharedCheck_504_ == 0)
{
v___x_365_ = v_snd_347_;
v_isShared_366_ = v_isSharedCheck_504_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_snd_363_);
lean_inc(v_fst_362_);
lean_dec(v_snd_347_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_504_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_371_; uint8_t v_a_373_; uint8_t v_fst_379_; lean_object* v_mctx_380_; lean_object* v___y_396_; uint8_t v_fst_402_; lean_object* v_snd_403_; lean_object* v___y_420_; uint8_t v_fst_425_; lean_object* v_mctx_426_; lean_object* v___y_442_; uint8_t v___x_447_; 
v___x_371_ = l_Lean_LocalDecl_fvarId(v_val_361_);
v___x_447_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v___x_371_, v_forbidden_337_);
if (v___x_447_ == 0)
{
uint8_t v___x_448_; 
v___x_448_ = l_Lean_LocalDecl_isAuxDecl(v_val_361_);
if (v___x_448_ == 0)
{
uint8_t v___x_449_; uint8_t v___x_450_; 
v___x_449_ = l_Lean_LocalDecl_binderInfo(v_val_361_);
v___x_450_ = l_Lean_BinderInfo_isInstImplicit(v___x_449_);
if (v___x_450_ == 0)
{
lean_object* v___f_451_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v_snd_455_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___y_463_; uint8_t v___y_470_; 
lean_inc(v_fst_362_);
v___f_451_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_451_, 0, v_fst_362_);
if (v_ignoreLetDecls_338_ == 0)
{
lean_del_object(v___x_365_);
v___y_470_ = v___x_447_;
goto v___jp_469_;
}
else
{
uint8_t v___x_502_; 
v___x_502_ = l_Lean_LocalDecl_isLet(v_val_361_, v___x_447_);
if (v___x_502_ == 0)
{
lean_del_object(v___x_365_);
v___y_470_ = v___x_502_;
goto v___jp_469_;
}
else
{
lean_dec_ref(v___f_451_);
lean_dec(v___x_371_);
goto v___jp_367_;
}
}
v___jp_452_:
{
uint8_t v___x_456_; 
v___x_456_ = l_Lean_Expr_hasFVar(v___y_453_);
if (v___x_456_ == 0)
{
uint8_t v___x_457_; 
v___x_457_ = l_Lean_Expr_hasMVar(v___y_453_);
if (v___x_457_ == 0)
{
lean_dec_ref(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec_ref(v___f_451_);
v_fst_402_ = v___x_457_;
v_snd_403_ = v_snd_455_;
goto v___jp_401_;
}
else
{
lean_object* v___x_458_; 
v___x_458_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_451_, v___y_454_, v___y_453_, v_snd_455_);
v___y_420_ = v___x_458_;
goto v___jp_419_;
}
}
else
{
lean_object* v___x_459_; 
v___x_459_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_451_, v___y_454_, v___y_453_, v_snd_455_);
v___y_420_ = v___x_459_;
goto v___jp_419_;
}
}
v___jp_460_:
{
lean_object* v_fst_464_; uint8_t v___x_465_; 
v_fst_464_ = lean_ctor_get(v___y_463_, 0);
v___x_465_ = lean_unbox(v_fst_464_);
if (v___x_465_ == 0)
{
lean_object* v_snd_466_; 
v_snd_466_ = lean_ctor_get(v___y_463_, 1);
lean_inc(v_snd_466_);
lean_dec_ref(v___y_463_);
v___y_453_ = v___y_461_;
v___y_454_ = v___y_462_;
v_snd_455_ = v_snd_466_;
goto v___jp_452_;
}
else
{
lean_object* v_snd_467_; uint8_t v___x_468_; 
lean_inc(v_fst_464_);
lean_dec_ref(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec_ref(v___f_451_);
v_snd_467_ = lean_ctor_get(v___y_463_, 1);
lean_inc(v_snd_467_);
lean_dec_ref(v___y_463_);
v___x_468_ = lean_unbox(v_fst_464_);
lean_dec(v_fst_464_);
v_fst_402_ = v___x_468_;
v_snd_403_ = v_snd_467_;
goto v___jp_401_;
}
}
v___jp_469_:
{
lean_object* v___x_471_; lean_object* v___f_472_; 
v___x_471_ = lean_box(v___y_470_);
v___f_472_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(v___f_472_, 0, v___x_471_);
if (lean_obj_tag(v_val_361_) == 0)
{
lean_object* v_type_473_; lean_object* v___x_474_; lean_object* v_mctx_475_; lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v_type_473_ = lean_ctor_get(v_val_361_, 3);
v___x_474_ = lean_st_ref_get(v___y_343_);
v_mctx_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc_ref_n(v_mctx_475_, 2);
lean_dec(v___x_474_);
v___x_476_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v_mctx_475_);
v___x_478_ = l_Lean_Expr_hasFVar(v_type_473_);
if (v___x_478_ == 0)
{
uint8_t v___x_479_; 
v___x_479_ = l_Lean_Expr_hasMVar(v_type_473_);
if (v___x_479_ == 0)
{
lean_dec_ref_known(v___x_477_, 2);
lean_dec_ref(v___f_472_);
lean_dec_ref(v___f_451_);
v_fst_425_ = v___x_479_;
v_mctx_426_ = v_mctx_475_;
goto v___jp_424_;
}
else
{
lean_object* v___x_480_; 
lean_dec_ref(v_mctx_475_);
lean_inc_ref(v_type_473_);
v___x_480_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_451_, v___f_472_, v_type_473_, v___x_477_);
v___y_442_ = v___x_480_;
goto v___jp_441_;
}
}
else
{
lean_object* v___x_481_; 
lean_dec_ref(v_mctx_475_);
lean_inc_ref(v_type_473_);
v___x_481_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_451_, v___f_472_, v_type_473_, v___x_477_);
v___y_442_ = v___x_481_;
goto v___jp_441_;
}
}
else
{
uint8_t v_nondep_482_; 
v_nondep_482_ = lean_ctor_get_uint8(v_val_361_, sizeof(void*)*5);
if (v_nondep_482_ == 0)
{
lean_object* v_type_483_; lean_object* v_value_484_; lean_object* v___x_485_; lean_object* v_mctx_486_; lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v_type_483_ = lean_ctor_get(v_val_361_, 3);
v_value_484_ = lean_ctor_get(v_val_361_, 4);
v___x_485_ = lean_st_ref_get(v___y_343_);
v_mctx_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc_ref(v_mctx_486_);
lean_dec(v___x_485_);
v___x_487_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v_mctx_486_);
v___x_489_ = l_Lean_Expr_hasFVar(v_type_483_);
if (v___x_489_ == 0)
{
uint8_t v___x_490_; 
v___x_490_ = l_Lean_Expr_hasMVar(v_type_483_);
if (v___x_490_ == 0)
{
lean_inc_ref(v_value_484_);
v___y_453_ = v_value_484_;
v___y_454_ = v___f_472_;
v_snd_455_ = v___x_488_;
goto v___jp_452_;
}
else
{
lean_object* v___x_491_; 
lean_inc_ref(v_type_483_);
lean_inc_ref(v___f_472_);
lean_inc_ref(v___f_451_);
v___x_491_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_451_, v___f_472_, v_type_483_, v___x_488_);
lean_inc_ref(v_value_484_);
v___y_461_ = v_value_484_;
v___y_462_ = v___f_472_;
v___y_463_ = v___x_491_;
goto v___jp_460_;
}
}
else
{
lean_object* v___x_492_; 
lean_inc_ref(v_type_483_);
lean_inc_ref(v___f_472_);
lean_inc_ref(v___f_451_);
v___x_492_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_451_, v___f_472_, v_type_483_, v___x_488_);
lean_inc_ref(v_value_484_);
v___y_461_ = v_value_484_;
v___y_462_ = v___f_472_;
v___y_463_ = v___x_492_;
goto v___jp_460_;
}
}
else
{
lean_object* v_type_493_; lean_object* v___x_494_; lean_object* v_mctx_495_; lean_object* v___x_496_; lean_object* v___x_497_; uint8_t v___x_498_; 
v_type_493_ = lean_ctor_get(v_val_361_, 3);
v___x_494_ = lean_st_ref_get(v___y_343_);
v_mctx_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc_ref_n(v_mctx_495_, 2);
lean_dec(v___x_494_);
v___x_496_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
lean_ctor_set(v___x_497_, 1, v_mctx_495_);
v___x_498_ = l_Lean_Expr_hasFVar(v_type_493_);
if (v___x_498_ == 0)
{
uint8_t v___x_499_; 
v___x_499_ = l_Lean_Expr_hasMVar(v_type_493_);
if (v___x_499_ == 0)
{
lean_dec_ref_known(v___x_497_, 2);
lean_dec_ref(v___f_472_);
lean_dec_ref(v___f_451_);
v_fst_379_ = v___x_499_;
v_mctx_380_ = v_mctx_495_;
goto v___jp_378_;
}
else
{
lean_object* v___x_500_; 
lean_dec_ref(v_mctx_495_);
lean_inc_ref(v_type_493_);
v___x_500_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_451_, v___f_472_, v_type_493_, v___x_497_);
v___y_396_ = v___x_500_;
goto v___jp_395_;
}
}
else
{
lean_object* v___x_501_; 
lean_dec_ref(v_mctx_495_);
lean_inc_ref(v_type_493_);
v___x_501_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_451_, v___f_472_, v_type_493_, v___x_497_);
v___y_396_ = v___x_501_;
goto v___jp_395_;
}
}
}
}
}
else
{
lean_dec(v___x_371_);
goto v___jp_367_;
}
}
else
{
lean_dec(v___x_371_);
goto v___jp_367_;
}
}
else
{
lean_object* v___x_503_; 
lean_dec(v___x_371_);
lean_del_object(v___x_365_);
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v_fst_362_);
lean_ctor_set(v___x_503_, 1, v_snd_363_);
v_a_353_ = v___x_503_;
goto v___jp_352_;
}
v___jp_367_:
{
lean_object* v___x_369_; 
if (v_isShared_366_ == 0)
{
v___x_369_ = v___x_365_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_fst_362_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_snd_363_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
v_a_353_ = v___x_369_;
goto v___jp_352_;
}
}
v___jp_372_:
{
if (v_a_373_ == 0)
{
lean_object* v___x_374_; 
lean_dec(v___x_371_);
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v_fst_362_);
lean_ctor_set(v___x_374_, 1, v_snd_363_);
v_a_353_ = v___x_374_;
goto v___jp_352_;
}
else
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
lean_inc(v___x_371_);
v___x_375_ = l_Lean_FVarIdSet_insert(v_snd_363_, v___x_371_);
v___x_376_ = l_Lean_FVarIdSet_insert(v_fst_362_, v___x_371_);
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
lean_ctor_set(v___x_377_, 1, v___x_375_);
v_a_353_ = v___x_377_;
goto v___jp_352_;
}
}
v___jp_378_:
{
lean_object* v___x_381_; lean_object* v_cache_382_; lean_object* v_zetaDeltaFVarIds_383_; lean_object* v_postponed_384_; lean_object* v_diag_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_393_; 
v___x_381_ = lean_st_ref_take(v___y_343_);
v_cache_382_ = lean_ctor_get(v___x_381_, 1);
v_zetaDeltaFVarIds_383_ = lean_ctor_get(v___x_381_, 2);
v_postponed_384_ = lean_ctor_get(v___x_381_, 3);
v_diag_385_ = lean_ctor_get(v___x_381_, 4);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_393_ == 0)
{
lean_object* v_unused_394_; 
v_unused_394_ = lean_ctor_get(v___x_381_, 0);
lean_dec(v_unused_394_);
v___x_387_ = v___x_381_;
v_isShared_388_ = v_isSharedCheck_393_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_diag_385_);
lean_inc(v_postponed_384_);
lean_inc(v_zetaDeltaFVarIds_383_);
lean_inc(v_cache_382_);
lean_dec(v___x_381_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_393_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 0, v_mctx_380_);
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_mctx_380_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v_cache_382_);
lean_ctor_set(v_reuseFailAlloc_392_, 2, v_zetaDeltaFVarIds_383_);
lean_ctor_set(v_reuseFailAlloc_392_, 3, v_postponed_384_);
lean_ctor_set(v_reuseFailAlloc_392_, 4, v_diag_385_);
v___x_390_ = v_reuseFailAlloc_392_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_391_; 
v___x_391_ = lean_st_ref_put(v___y_343_, v___x_390_);
v_a_373_ = v_fst_379_;
goto v___jp_372_;
}
}
}
v___jp_395_:
{
lean_object* v_snd_397_; lean_object* v_fst_398_; lean_object* v_mctx_399_; uint8_t v___x_400_; 
v_snd_397_ = lean_ctor_get(v___y_396_, 1);
lean_inc(v_snd_397_);
v_fst_398_ = lean_ctor_get(v___y_396_, 0);
lean_inc(v_fst_398_);
lean_dec_ref(v___y_396_);
v_mctx_399_ = lean_ctor_get(v_snd_397_, 1);
lean_inc_ref(v_mctx_399_);
lean_dec(v_snd_397_);
v___x_400_ = lean_unbox(v_fst_398_);
lean_dec(v_fst_398_);
v_fst_379_ = v___x_400_;
v_mctx_380_ = v_mctx_399_;
goto v___jp_378_;
}
v___jp_401_:
{
lean_object* v_mctx_404_; lean_object* v___x_405_; lean_object* v_cache_406_; lean_object* v_zetaDeltaFVarIds_407_; lean_object* v_postponed_408_; lean_object* v_diag_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_417_; 
v_mctx_404_ = lean_ctor_get(v_snd_403_, 1);
lean_inc_ref(v_mctx_404_);
lean_dec_ref(v_snd_403_);
v___x_405_ = lean_st_ref_take(v___y_343_);
v_cache_406_ = lean_ctor_get(v___x_405_, 1);
v_zetaDeltaFVarIds_407_ = lean_ctor_get(v___x_405_, 2);
v_postponed_408_ = lean_ctor_get(v___x_405_, 3);
v_diag_409_ = lean_ctor_get(v___x_405_, 4);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_417_ == 0)
{
lean_object* v_unused_418_; 
v_unused_418_ = lean_ctor_get(v___x_405_, 0);
lean_dec(v_unused_418_);
v___x_411_ = v___x_405_;
v_isShared_412_ = v_isSharedCheck_417_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_diag_409_);
lean_inc(v_postponed_408_);
lean_inc(v_zetaDeltaFVarIds_407_);
lean_inc(v_cache_406_);
lean_dec(v___x_405_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_417_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v_mctx_404_);
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_mctx_404_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v_cache_406_);
lean_ctor_set(v_reuseFailAlloc_416_, 2, v_zetaDeltaFVarIds_407_);
lean_ctor_set(v_reuseFailAlloc_416_, 3, v_postponed_408_);
lean_ctor_set(v_reuseFailAlloc_416_, 4, v_diag_409_);
v___x_414_ = v_reuseFailAlloc_416_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_415_; 
v___x_415_ = lean_st_ref_put(v___y_343_, v___x_414_);
v_a_373_ = v_fst_402_;
goto v___jp_372_;
}
}
}
v___jp_419_:
{
lean_object* v_fst_421_; lean_object* v_snd_422_; uint8_t v___x_423_; 
v_fst_421_ = lean_ctor_get(v___y_420_, 0);
lean_inc(v_fst_421_);
v_snd_422_ = lean_ctor_get(v___y_420_, 1);
lean_inc(v_snd_422_);
lean_dec_ref(v___y_420_);
v___x_423_ = lean_unbox(v_fst_421_);
lean_dec(v_fst_421_);
v_fst_402_ = v___x_423_;
v_snd_403_ = v_snd_422_;
goto v___jp_401_;
}
v___jp_424_:
{
lean_object* v___x_427_; lean_object* v_cache_428_; lean_object* v_zetaDeltaFVarIds_429_; lean_object* v_postponed_430_; lean_object* v_diag_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_439_; 
v___x_427_ = lean_st_ref_take(v___y_343_);
v_cache_428_ = lean_ctor_get(v___x_427_, 1);
v_zetaDeltaFVarIds_429_ = lean_ctor_get(v___x_427_, 2);
v_postponed_430_ = lean_ctor_get(v___x_427_, 3);
v_diag_431_ = lean_ctor_get(v___x_427_, 4);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_439_ == 0)
{
lean_object* v_unused_440_; 
v_unused_440_ = lean_ctor_get(v___x_427_, 0);
lean_dec(v_unused_440_);
v___x_433_ = v___x_427_;
v_isShared_434_ = v_isSharedCheck_439_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_diag_431_);
lean_inc(v_postponed_430_);
lean_inc(v_zetaDeltaFVarIds_429_);
lean_inc(v_cache_428_);
lean_dec(v___x_427_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_439_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v_mctx_426_);
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_mctx_426_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_cache_428_);
lean_ctor_set(v_reuseFailAlloc_438_, 2, v_zetaDeltaFVarIds_429_);
lean_ctor_set(v_reuseFailAlloc_438_, 3, v_postponed_430_);
lean_ctor_set(v_reuseFailAlloc_438_, 4, v_diag_431_);
v___x_436_ = v_reuseFailAlloc_438_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
lean_object* v___x_437_; 
v___x_437_ = lean_st_ref_put(v___y_343_, v___x_436_);
v_a_373_ = v_fst_425_;
goto v___jp_372_;
}
}
}
v___jp_441_:
{
lean_object* v_snd_443_; lean_object* v_fst_444_; lean_object* v_mctx_445_; uint8_t v___x_446_; 
v_snd_443_ = lean_ctor_get(v___y_442_, 1);
lean_inc(v_snd_443_);
v_fst_444_ = lean_ctor_get(v___y_442_, 0);
lean_inc(v_fst_444_);
lean_dec_ref(v___y_442_);
v_mctx_445_ = lean_ctor_get(v_snd_443_, 1);
lean_inc_ref(v_mctx_445_);
lean_dec(v_snd_443_);
v___x_446_ = lean_unbox(v_fst_444_);
lean_dec(v_fst_444_);
v_fst_425_ = v___x_446_;
v_mctx_426_ = v_mctx_445_;
goto v___jp_424_;
}
}
}
v___jp_352_:
{
lean_object* v___x_355_; 
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 1, v_a_353_);
lean_ctor_set(v___x_349_, 0, v___x_351_);
v___x_355_ = v___x_349_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_351_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_a_353_);
v___x_355_ = v_reuseFailAlloc_359_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
size_t v___x_356_; size_t v___x_357_; 
v___x_356_ = ((size_t)1ULL);
v___x_357_ = lean_usize_add(v_i_341_, v___x_356_);
v_i_341_ = v___x_357_;
v_b_342_ = v___x_355_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_forbidden_507_, lean_object* v_ignoreLetDecls_508_, lean_object* v_as_509_, lean_object* v_sz_510_, lean_object* v_i_511_, lean_object* v_b_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_515_; size_t v_sz_boxed_516_; size_t v_i_boxed_517_; lean_object* v_res_518_; 
v_ignoreLetDecls_boxed_515_ = lean_unbox(v_ignoreLetDecls_508_);
v_sz_boxed_516_ = lean_unbox_usize(v_sz_510_);
lean_dec(v_sz_510_);
v_i_boxed_517_ = lean_unbox_usize(v_i_511_);
lean_dec(v_i_511_);
v_res_518_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(v_forbidden_507_, v_ignoreLetDecls_boxed_515_, v_as_509_, v_sz_boxed_516_, v_i_boxed_517_, v_b_512_, v___y_513_);
lean_dec(v___y_513_);
lean_dec_ref(v_as_509_);
lean_dec(v_forbidden_507_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1(lean_object* v_forbidden_519_, uint8_t v_ignoreLetDecls_520_, lean_object* v_as_521_, size_t v_sz_522_, size_t v_i_523_, lean_object* v_b_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
uint8_t v___x_530_; 
v___x_530_ = lean_usize_dec_lt(v_i_523_, v_sz_522_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; 
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v_b_524_);
return v___x_531_;
}
else
{
lean_object* v_snd_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_690_; 
v_snd_532_ = lean_ctor_get(v_b_524_, 1);
v_isSharedCheck_690_ = !lean_is_exclusive(v_b_524_);
if (v_isSharedCheck_690_ == 0)
{
lean_object* v_unused_691_; 
v_unused_691_ = lean_ctor_get(v_b_524_, 0);
lean_dec(v_unused_691_);
v___x_534_ = v_b_524_;
v_isShared_535_ = v_isSharedCheck_690_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_snd_532_);
lean_dec(v_b_524_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_690_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_536_; lean_object* v_a_538_; lean_object* v_a_545_; 
v___x_536_ = lean_box(0);
v_a_545_ = lean_array_uget_borrowed(v_as_521_, v_i_523_);
if (lean_obj_tag(v_a_545_) == 0)
{
v_a_538_ = v_snd_532_;
goto v___jp_537_;
}
else
{
lean_object* v_val_546_; lean_object* v_fst_547_; lean_object* v_snd_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_689_; 
v_val_546_ = lean_ctor_get(v_a_545_, 0);
v_fst_547_ = lean_ctor_get(v_snd_532_, 0);
v_snd_548_ = lean_ctor_get(v_snd_532_, 1);
v_isSharedCheck_689_ = !lean_is_exclusive(v_snd_532_);
if (v_isSharedCheck_689_ == 0)
{
v___x_550_ = v_snd_532_;
v_isShared_551_ = v_isSharedCheck_689_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_snd_548_);
lean_inc(v_fst_547_);
lean_dec(v_snd_532_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_689_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_556_; uint8_t v_a_558_; uint8_t v_fst_564_; lean_object* v_mctx_565_; lean_object* v___y_581_; uint8_t v_fst_587_; lean_object* v_snd_588_; lean_object* v___y_605_; uint8_t v_fst_610_; lean_object* v_mctx_611_; lean_object* v___y_627_; uint8_t v___x_632_; 
v___x_556_ = l_Lean_LocalDecl_fvarId(v_val_546_);
v___x_632_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v___x_556_, v_forbidden_519_);
if (v___x_632_ == 0)
{
uint8_t v___x_633_; 
v___x_633_ = l_Lean_LocalDecl_isAuxDecl(v_val_546_);
if (v___x_633_ == 0)
{
uint8_t v___x_634_; uint8_t v___x_635_; 
v___x_634_ = l_Lean_LocalDecl_binderInfo(v_val_546_);
v___x_635_ = l_Lean_BinderInfo_isInstImplicit(v___x_634_);
if (v___x_635_ == 0)
{
lean_object* v___f_636_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v_snd_640_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; uint8_t v___y_655_; 
lean_inc(v_fst_547_);
v___f_636_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_636_, 0, v_fst_547_);
if (v_ignoreLetDecls_520_ == 0)
{
lean_del_object(v___x_550_);
v___y_655_ = v___x_632_;
goto v___jp_654_;
}
else
{
uint8_t v___x_687_; 
v___x_687_ = l_Lean_LocalDecl_isLet(v_val_546_, v___x_632_);
if (v___x_687_ == 0)
{
lean_del_object(v___x_550_);
v___y_655_ = v___x_687_;
goto v___jp_654_;
}
else
{
lean_dec_ref(v___f_636_);
lean_dec(v___x_556_);
goto v___jp_552_;
}
}
v___jp_637_:
{
uint8_t v___x_641_; 
v___x_641_ = l_Lean_Expr_hasFVar(v___y_638_);
if (v___x_641_ == 0)
{
uint8_t v___x_642_; 
v___x_642_ = l_Lean_Expr_hasMVar(v___y_638_);
if (v___x_642_ == 0)
{
lean_dec_ref(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec_ref(v___f_636_);
v_fst_587_ = v___x_642_;
v_snd_588_ = v_snd_640_;
goto v___jp_586_;
}
else
{
lean_object* v___x_643_; 
v___x_643_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_636_, v___y_639_, v___y_638_, v_snd_640_);
v___y_605_ = v___x_643_;
goto v___jp_604_;
}
}
else
{
lean_object* v___x_644_; 
v___x_644_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_636_, v___y_639_, v___y_638_, v_snd_640_);
v___y_605_ = v___x_644_;
goto v___jp_604_;
}
}
v___jp_645_:
{
lean_object* v_fst_649_; uint8_t v___x_650_; 
v_fst_649_ = lean_ctor_get(v___y_648_, 0);
v___x_650_ = lean_unbox(v_fst_649_);
if (v___x_650_ == 0)
{
lean_object* v_snd_651_; 
v_snd_651_ = lean_ctor_get(v___y_648_, 1);
lean_inc(v_snd_651_);
lean_dec_ref(v___y_648_);
v___y_638_ = v___y_646_;
v___y_639_ = v___y_647_;
v_snd_640_ = v_snd_651_;
goto v___jp_637_;
}
else
{
lean_object* v_snd_652_; uint8_t v___x_653_; 
lean_inc(v_fst_649_);
lean_dec_ref(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec_ref(v___f_636_);
v_snd_652_ = lean_ctor_get(v___y_648_, 1);
lean_inc(v_snd_652_);
lean_dec_ref(v___y_648_);
v___x_653_ = lean_unbox(v_fst_649_);
lean_dec(v_fst_649_);
v_fst_587_ = v___x_653_;
v_snd_588_ = v_snd_652_;
goto v___jp_586_;
}
}
v___jp_654_:
{
lean_object* v___x_656_; lean_object* v___f_657_; 
v___x_656_ = lean_box(v___y_655_);
v___f_657_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(v___f_657_, 0, v___x_656_);
if (lean_obj_tag(v_val_546_) == 0)
{
lean_object* v_type_658_; lean_object* v___x_659_; lean_object* v_mctx_660_; lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v_type_658_ = lean_ctor_get(v_val_546_, 3);
v___x_659_ = lean_st_ref_get(v___y_526_);
v_mctx_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc_ref_n(v_mctx_660_, 2);
lean_dec(v___x_659_);
v___x_661_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
lean_ctor_set(v___x_662_, 1, v_mctx_660_);
v___x_663_ = l_Lean_Expr_hasFVar(v_type_658_);
if (v___x_663_ == 0)
{
uint8_t v___x_664_; 
v___x_664_ = l_Lean_Expr_hasMVar(v_type_658_);
if (v___x_664_ == 0)
{
lean_dec_ref_known(v___x_662_, 2);
lean_dec_ref(v___f_657_);
lean_dec_ref(v___f_636_);
v_fst_610_ = v___x_664_;
v_mctx_611_ = v_mctx_660_;
goto v___jp_609_;
}
else
{
lean_object* v___x_665_; 
lean_dec_ref(v_mctx_660_);
lean_inc_ref(v_type_658_);
v___x_665_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_636_, v___f_657_, v_type_658_, v___x_662_);
v___y_627_ = v___x_665_;
goto v___jp_626_;
}
}
else
{
lean_object* v___x_666_; 
lean_dec_ref(v_mctx_660_);
lean_inc_ref(v_type_658_);
v___x_666_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_636_, v___f_657_, v_type_658_, v___x_662_);
v___y_627_ = v___x_666_;
goto v___jp_626_;
}
}
else
{
uint8_t v_nondep_667_; 
v_nondep_667_ = lean_ctor_get_uint8(v_val_546_, sizeof(void*)*5);
if (v_nondep_667_ == 0)
{
lean_object* v_type_668_; lean_object* v_value_669_; lean_object* v___x_670_; lean_object* v_mctx_671_; lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v_type_668_ = lean_ctor_get(v_val_546_, 3);
v_value_669_ = lean_ctor_get(v_val_546_, 4);
v___x_670_ = lean_st_ref_get(v___y_526_);
v_mctx_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc_ref(v_mctx_671_);
lean_dec(v___x_670_);
v___x_672_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
lean_ctor_set(v___x_673_, 1, v_mctx_671_);
v___x_674_ = l_Lean_Expr_hasFVar(v_type_668_);
if (v___x_674_ == 0)
{
uint8_t v___x_675_; 
v___x_675_ = l_Lean_Expr_hasMVar(v_type_668_);
if (v___x_675_ == 0)
{
lean_inc_ref(v_value_669_);
v___y_638_ = v_value_669_;
v___y_639_ = v___f_657_;
v_snd_640_ = v___x_673_;
goto v___jp_637_;
}
else
{
lean_object* v___x_676_; 
lean_inc_ref(v_type_668_);
lean_inc_ref(v___f_657_);
lean_inc_ref(v___f_636_);
v___x_676_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_636_, v___f_657_, v_type_668_, v___x_673_);
lean_inc_ref(v_value_669_);
v___y_646_ = v_value_669_;
v___y_647_ = v___f_657_;
v___y_648_ = v___x_676_;
goto v___jp_645_;
}
}
else
{
lean_object* v___x_677_; 
lean_inc_ref(v_type_668_);
lean_inc_ref(v___f_657_);
lean_inc_ref(v___f_636_);
v___x_677_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_636_, v___f_657_, v_type_668_, v___x_673_);
lean_inc_ref(v_value_669_);
v___y_646_ = v_value_669_;
v___y_647_ = v___f_657_;
v___y_648_ = v___x_677_;
goto v___jp_645_;
}
}
else
{
lean_object* v_type_678_; lean_object* v___x_679_; lean_object* v_mctx_680_; lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v_type_678_ = lean_ctor_get(v_val_546_, 3);
v___x_679_ = lean_st_ref_get(v___y_526_);
v_mctx_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc_ref_n(v_mctx_680_, 2);
lean_dec(v___x_679_);
v___x_681_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
lean_ctor_set(v___x_682_, 1, v_mctx_680_);
v___x_683_ = l_Lean_Expr_hasFVar(v_type_678_);
if (v___x_683_ == 0)
{
uint8_t v___x_684_; 
v___x_684_ = l_Lean_Expr_hasMVar(v_type_678_);
if (v___x_684_ == 0)
{
lean_dec_ref_known(v___x_682_, 2);
lean_dec_ref(v___f_657_);
lean_dec_ref(v___f_636_);
v_fst_564_ = v___x_684_;
v_mctx_565_ = v_mctx_680_;
goto v___jp_563_;
}
else
{
lean_object* v___x_685_; 
lean_dec_ref(v_mctx_680_);
lean_inc_ref(v_type_678_);
v___x_685_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_636_, v___f_657_, v_type_678_, v___x_682_);
v___y_581_ = v___x_685_;
goto v___jp_580_;
}
}
else
{
lean_object* v___x_686_; 
lean_dec_ref(v_mctx_680_);
lean_inc_ref(v_type_678_);
v___x_686_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_636_, v___f_657_, v_type_678_, v___x_682_);
v___y_581_ = v___x_686_;
goto v___jp_580_;
}
}
}
}
}
else
{
lean_dec(v___x_556_);
goto v___jp_552_;
}
}
else
{
lean_dec(v___x_556_);
goto v___jp_552_;
}
}
else
{
lean_object* v___x_688_; 
lean_dec(v___x_556_);
lean_del_object(v___x_550_);
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v_fst_547_);
lean_ctor_set(v___x_688_, 1, v_snd_548_);
v_a_538_ = v___x_688_;
goto v___jp_537_;
}
v___jp_552_:
{
lean_object* v___x_554_; 
if (v_isShared_551_ == 0)
{
v___x_554_ = v___x_550_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_fst_547_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_snd_548_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
v_a_538_ = v___x_554_;
goto v___jp_537_;
}
}
v___jp_557_:
{
if (v_a_558_ == 0)
{
lean_object* v___x_559_; 
lean_dec(v___x_556_);
v___x_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_559_, 0, v_fst_547_);
lean_ctor_set(v___x_559_, 1, v_snd_548_);
v_a_538_ = v___x_559_;
goto v___jp_537_;
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
lean_inc(v___x_556_);
v___x_560_ = l_Lean_FVarIdSet_insert(v_snd_548_, v___x_556_);
v___x_561_ = l_Lean_FVarIdSet_insert(v_fst_547_, v___x_556_);
v___x_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
lean_ctor_set(v___x_562_, 1, v___x_560_);
v_a_538_ = v___x_562_;
goto v___jp_537_;
}
}
v___jp_563_:
{
lean_object* v___x_566_; lean_object* v_cache_567_; lean_object* v_zetaDeltaFVarIds_568_; lean_object* v_postponed_569_; lean_object* v_diag_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_578_; 
v___x_566_ = lean_st_ref_take(v___y_526_);
v_cache_567_ = lean_ctor_get(v___x_566_, 1);
v_zetaDeltaFVarIds_568_ = lean_ctor_get(v___x_566_, 2);
v_postponed_569_ = lean_ctor_get(v___x_566_, 3);
v_diag_570_ = lean_ctor_get(v___x_566_, 4);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_578_ == 0)
{
lean_object* v_unused_579_; 
v_unused_579_ = lean_ctor_get(v___x_566_, 0);
lean_dec(v_unused_579_);
v___x_572_ = v___x_566_;
v_isShared_573_ = v_isSharedCheck_578_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_diag_570_);
lean_inc(v_postponed_569_);
lean_inc(v_zetaDeltaFVarIds_568_);
lean_inc(v_cache_567_);
lean_dec(v___x_566_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_578_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v_mctx_565_);
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_mctx_565_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v_cache_567_);
lean_ctor_set(v_reuseFailAlloc_577_, 2, v_zetaDeltaFVarIds_568_);
lean_ctor_set(v_reuseFailAlloc_577_, 3, v_postponed_569_);
lean_ctor_set(v_reuseFailAlloc_577_, 4, v_diag_570_);
v___x_575_ = v_reuseFailAlloc_577_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_576_; 
v___x_576_ = lean_st_ref_put(v___y_526_, v___x_575_);
v_a_558_ = v_fst_564_;
goto v___jp_557_;
}
}
}
v___jp_580_:
{
lean_object* v_snd_582_; lean_object* v_fst_583_; lean_object* v_mctx_584_; uint8_t v___x_585_; 
v_snd_582_ = lean_ctor_get(v___y_581_, 1);
lean_inc(v_snd_582_);
v_fst_583_ = lean_ctor_get(v___y_581_, 0);
lean_inc(v_fst_583_);
lean_dec_ref(v___y_581_);
v_mctx_584_ = lean_ctor_get(v_snd_582_, 1);
lean_inc_ref(v_mctx_584_);
lean_dec(v_snd_582_);
v___x_585_ = lean_unbox(v_fst_583_);
lean_dec(v_fst_583_);
v_fst_564_ = v___x_585_;
v_mctx_565_ = v_mctx_584_;
goto v___jp_563_;
}
v___jp_586_:
{
lean_object* v_mctx_589_; lean_object* v___x_590_; lean_object* v_cache_591_; lean_object* v_zetaDeltaFVarIds_592_; lean_object* v_postponed_593_; lean_object* v_diag_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_602_; 
v_mctx_589_ = lean_ctor_get(v_snd_588_, 1);
lean_inc_ref(v_mctx_589_);
lean_dec_ref(v_snd_588_);
v___x_590_ = lean_st_ref_take(v___y_526_);
v_cache_591_ = lean_ctor_get(v___x_590_, 1);
v_zetaDeltaFVarIds_592_ = lean_ctor_get(v___x_590_, 2);
v_postponed_593_ = lean_ctor_get(v___x_590_, 3);
v_diag_594_ = lean_ctor_get(v___x_590_, 4);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_602_ == 0)
{
lean_object* v_unused_603_; 
v_unused_603_ = lean_ctor_get(v___x_590_, 0);
lean_dec(v_unused_603_);
v___x_596_ = v___x_590_;
v_isShared_597_ = v_isSharedCheck_602_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_diag_594_);
lean_inc(v_postponed_593_);
lean_inc(v_zetaDeltaFVarIds_592_);
lean_inc(v_cache_591_);
lean_dec(v___x_590_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_602_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v_mctx_589_);
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_mctx_589_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_cache_591_);
lean_ctor_set(v_reuseFailAlloc_601_, 2, v_zetaDeltaFVarIds_592_);
lean_ctor_set(v_reuseFailAlloc_601_, 3, v_postponed_593_);
lean_ctor_set(v_reuseFailAlloc_601_, 4, v_diag_594_);
v___x_599_ = v_reuseFailAlloc_601_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_object* v___x_600_; 
v___x_600_ = lean_st_ref_put(v___y_526_, v___x_599_);
v_a_558_ = v_fst_587_;
goto v___jp_557_;
}
}
}
v___jp_604_:
{
lean_object* v_fst_606_; lean_object* v_snd_607_; uint8_t v___x_608_; 
v_fst_606_ = lean_ctor_get(v___y_605_, 0);
lean_inc(v_fst_606_);
v_snd_607_ = lean_ctor_get(v___y_605_, 1);
lean_inc(v_snd_607_);
lean_dec_ref(v___y_605_);
v___x_608_ = lean_unbox(v_fst_606_);
lean_dec(v_fst_606_);
v_fst_587_ = v___x_608_;
v_snd_588_ = v_snd_607_;
goto v___jp_586_;
}
v___jp_609_:
{
lean_object* v___x_612_; lean_object* v_cache_613_; lean_object* v_zetaDeltaFVarIds_614_; lean_object* v_postponed_615_; lean_object* v_diag_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_624_; 
v___x_612_ = lean_st_ref_take(v___y_526_);
v_cache_613_ = lean_ctor_get(v___x_612_, 1);
v_zetaDeltaFVarIds_614_ = lean_ctor_get(v___x_612_, 2);
v_postponed_615_ = lean_ctor_get(v___x_612_, 3);
v_diag_616_ = lean_ctor_get(v___x_612_, 4);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_624_ == 0)
{
lean_object* v_unused_625_; 
v_unused_625_ = lean_ctor_get(v___x_612_, 0);
lean_dec(v_unused_625_);
v___x_618_ = v___x_612_;
v_isShared_619_ = v_isSharedCheck_624_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_diag_616_);
lean_inc(v_postponed_615_);
lean_inc(v_zetaDeltaFVarIds_614_);
lean_inc(v_cache_613_);
lean_dec(v___x_612_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_624_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v_mctx_611_);
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_mctx_611_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v_cache_613_);
lean_ctor_set(v_reuseFailAlloc_623_, 2, v_zetaDeltaFVarIds_614_);
lean_ctor_set(v_reuseFailAlloc_623_, 3, v_postponed_615_);
lean_ctor_set(v_reuseFailAlloc_623_, 4, v_diag_616_);
v___x_621_ = v_reuseFailAlloc_623_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v___x_622_; 
v___x_622_ = lean_st_ref_put(v___y_526_, v___x_621_);
v_a_558_ = v_fst_610_;
goto v___jp_557_;
}
}
}
v___jp_626_:
{
lean_object* v_snd_628_; lean_object* v_fst_629_; lean_object* v_mctx_630_; uint8_t v___x_631_; 
v_snd_628_ = lean_ctor_get(v___y_627_, 1);
lean_inc(v_snd_628_);
v_fst_629_ = lean_ctor_get(v___y_627_, 0);
lean_inc(v_fst_629_);
lean_dec_ref(v___y_627_);
v_mctx_630_ = lean_ctor_get(v_snd_628_, 1);
lean_inc_ref(v_mctx_630_);
lean_dec(v_snd_628_);
v___x_631_ = lean_unbox(v_fst_629_);
lean_dec(v_fst_629_);
v_fst_610_ = v___x_631_;
v_mctx_611_ = v_mctx_630_;
goto v___jp_609_;
}
}
}
v___jp_537_:
{
lean_object* v___x_540_; 
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 1, v_a_538_);
lean_ctor_set(v___x_534_, 0, v___x_536_);
v___x_540_ = v___x_534_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_a_538_);
v___x_540_ = v_reuseFailAlloc_544_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
size_t v___x_541_; size_t v___x_542_; lean_object* v___x_543_; 
v___x_541_ = ((size_t)1ULL);
v___x_542_ = lean_usize_add(v_i_523_, v___x_541_);
v___x_543_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(v_forbidden_519_, v_ignoreLetDecls_520_, v_as_521_, v_sz_522_, v___x_542_, v___x_540_, v___y_526_);
return v___x_543_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___boxed(lean_object* v_forbidden_692_, lean_object* v_ignoreLetDecls_693_, lean_object* v_as_694_, lean_object* v_sz_695_, lean_object* v_i_696_, lean_object* v_b_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_703_; size_t v_sz_boxed_704_; size_t v_i_boxed_705_; lean_object* v_res_706_; 
v_ignoreLetDecls_boxed_703_ = lean_unbox(v_ignoreLetDecls_693_);
v_sz_boxed_704_ = lean_unbox_usize(v_sz_695_);
lean_dec(v_sz_695_);
v_i_boxed_705_ = lean_unbox_usize(v_i_696_);
lean_dec(v_i_696_);
v_res_706_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1(v_forbidden_692_, v_ignoreLetDecls_boxed_703_, v_as_694_, v_sz_boxed_704_, v_i_boxed_705_, v_b_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec_ref(v_as_694_);
lean_dec(v_forbidden_692_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_forbidden_707_, uint8_t v_ignoreLetDecls_708_, lean_object* v_as_709_, size_t v_sz_710_, size_t v_i_711_, lean_object* v_b_712_, lean_object* v___y_713_){
_start:
{
uint8_t v___x_715_; 
v___x_715_ = lean_usize_dec_lt(v_i_711_, v_sz_710_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; 
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v_b_712_);
return v___x_716_;
}
else
{
lean_object* v_snd_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_875_; 
v_snd_717_ = lean_ctor_get(v_b_712_, 1);
v_isSharedCheck_875_ = !lean_is_exclusive(v_b_712_);
if (v_isSharedCheck_875_ == 0)
{
lean_object* v_unused_876_; 
v_unused_876_ = lean_ctor_get(v_b_712_, 0);
lean_dec(v_unused_876_);
v___x_719_ = v_b_712_;
v_isShared_720_ = v_isSharedCheck_875_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_snd_717_);
lean_dec(v_b_712_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_875_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_721_; lean_object* v_a_723_; lean_object* v_a_730_; 
v___x_721_ = lean_box(0);
v_a_730_ = lean_array_uget_borrowed(v_as_709_, v_i_711_);
if (lean_obj_tag(v_a_730_) == 0)
{
v_a_723_ = v_snd_717_;
goto v___jp_722_;
}
else
{
lean_object* v_val_731_; lean_object* v_fst_732_; lean_object* v_snd_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_874_; 
v_val_731_ = lean_ctor_get(v_a_730_, 0);
v_fst_732_ = lean_ctor_get(v_snd_717_, 0);
v_snd_733_ = lean_ctor_get(v_snd_717_, 1);
v_isSharedCheck_874_ = !lean_is_exclusive(v_snd_717_);
if (v_isSharedCheck_874_ == 0)
{
v___x_735_ = v_snd_717_;
v_isShared_736_ = v_isSharedCheck_874_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_snd_733_);
lean_inc(v_fst_732_);
lean_dec(v_snd_717_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_874_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_741_; uint8_t v_a_743_; uint8_t v_fst_749_; lean_object* v_mctx_750_; lean_object* v___y_766_; uint8_t v_fst_772_; lean_object* v_snd_773_; lean_object* v___y_790_; uint8_t v_fst_795_; lean_object* v_mctx_796_; lean_object* v___y_812_; uint8_t v___x_817_; 
v___x_741_ = l_Lean_LocalDecl_fvarId(v_val_731_);
v___x_817_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v___x_741_, v_forbidden_707_);
if (v___x_817_ == 0)
{
uint8_t v___x_818_; 
v___x_818_ = l_Lean_LocalDecl_isAuxDecl(v_val_731_);
if (v___x_818_ == 0)
{
uint8_t v___x_819_; uint8_t v___x_820_; 
v___x_819_ = l_Lean_LocalDecl_binderInfo(v_val_731_);
v___x_820_ = l_Lean_BinderInfo_isInstImplicit(v___x_819_);
if (v___x_820_ == 0)
{
lean_object* v___f_821_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v_snd_825_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; uint8_t v___y_840_; 
lean_inc(v_fst_732_);
v___f_821_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_821_, 0, v_fst_732_);
if (v_ignoreLetDecls_708_ == 0)
{
lean_del_object(v___x_735_);
v___y_840_ = v___x_817_;
goto v___jp_839_;
}
else
{
uint8_t v___x_872_; 
v___x_872_ = l_Lean_LocalDecl_isLet(v_val_731_, v___x_817_);
if (v___x_872_ == 0)
{
lean_del_object(v___x_735_);
v___y_840_ = v___x_872_;
goto v___jp_839_;
}
else
{
lean_dec_ref(v___f_821_);
lean_dec(v___x_741_);
goto v___jp_737_;
}
}
v___jp_822_:
{
uint8_t v___x_826_; 
v___x_826_ = l_Lean_Expr_hasFVar(v___y_823_);
if (v___x_826_ == 0)
{
uint8_t v___x_827_; 
v___x_827_ = l_Lean_Expr_hasMVar(v___y_823_);
if (v___x_827_ == 0)
{
lean_dec_ref(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec_ref(v___f_821_);
v_fst_772_ = v___x_827_;
v_snd_773_ = v_snd_825_;
goto v___jp_771_;
}
else
{
lean_object* v___x_828_; 
v___x_828_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_821_, v___y_824_, v___y_823_, v_snd_825_);
v___y_790_ = v___x_828_;
goto v___jp_789_;
}
}
else
{
lean_object* v___x_829_; 
v___x_829_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_821_, v___y_824_, v___y_823_, v_snd_825_);
v___y_790_ = v___x_829_;
goto v___jp_789_;
}
}
v___jp_830_:
{
lean_object* v_fst_834_; uint8_t v___x_835_; 
v_fst_834_ = lean_ctor_get(v___y_833_, 0);
v___x_835_ = lean_unbox(v_fst_834_);
if (v___x_835_ == 0)
{
lean_object* v_snd_836_; 
v_snd_836_ = lean_ctor_get(v___y_833_, 1);
lean_inc(v_snd_836_);
lean_dec_ref(v___y_833_);
v___y_823_ = v___y_831_;
v___y_824_ = v___y_832_;
v_snd_825_ = v_snd_836_;
goto v___jp_822_;
}
else
{
lean_object* v_snd_837_; uint8_t v___x_838_; 
lean_inc(v_fst_834_);
lean_dec_ref(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec_ref(v___f_821_);
v_snd_837_ = lean_ctor_get(v___y_833_, 1);
lean_inc(v_snd_837_);
lean_dec_ref(v___y_833_);
v___x_838_ = lean_unbox(v_fst_834_);
lean_dec(v_fst_834_);
v_fst_772_ = v___x_838_;
v_snd_773_ = v_snd_837_;
goto v___jp_771_;
}
}
v___jp_839_:
{
lean_object* v___x_841_; lean_object* v___f_842_; 
v___x_841_ = lean_box(v___y_840_);
v___f_842_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(v___f_842_, 0, v___x_841_);
if (lean_obj_tag(v_val_731_) == 0)
{
lean_object* v_type_843_; lean_object* v___x_844_; lean_object* v_mctx_845_; lean_object* v___x_846_; lean_object* v___x_847_; uint8_t v___x_848_; 
v_type_843_ = lean_ctor_get(v_val_731_, 3);
v___x_844_ = lean_st_ref_get(v___y_713_);
v_mctx_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc_ref_n(v_mctx_845_, 2);
lean_dec(v___x_844_);
v___x_846_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
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
lean_dec_ref(v___f_821_);
v_fst_795_ = v___x_849_;
v_mctx_796_ = v_mctx_845_;
goto v___jp_794_;
}
else
{
lean_object* v___x_850_; 
lean_dec_ref(v_mctx_845_);
lean_inc_ref(v_type_843_);
v___x_850_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_821_, v___f_842_, v_type_843_, v___x_847_);
v___y_812_ = v___x_850_;
goto v___jp_811_;
}
}
else
{
lean_object* v___x_851_; 
lean_dec_ref(v_mctx_845_);
lean_inc_ref(v_type_843_);
v___x_851_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_821_, v___f_842_, v_type_843_, v___x_847_);
v___y_812_ = v___x_851_;
goto v___jp_811_;
}
}
else
{
uint8_t v_nondep_852_; 
v_nondep_852_ = lean_ctor_get_uint8(v_val_731_, sizeof(void*)*5);
if (v_nondep_852_ == 0)
{
lean_object* v_type_853_; lean_object* v_value_854_; lean_object* v___x_855_; lean_object* v_mctx_856_; lean_object* v___x_857_; lean_object* v___x_858_; uint8_t v___x_859_; 
v_type_853_ = lean_ctor_get(v_val_731_, 3);
v_value_854_ = lean_ctor_get(v_val_731_, 4);
v___x_855_ = lean_st_ref_get(v___y_713_);
v_mctx_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc_ref(v_mctx_856_);
lean_dec(v___x_855_);
v___x_857_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
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
v___y_823_ = v_value_854_;
v___y_824_ = v___f_842_;
v_snd_825_ = v___x_858_;
goto v___jp_822_;
}
else
{
lean_object* v___x_861_; 
lean_inc_ref(v_type_853_);
lean_inc_ref(v___f_842_);
lean_inc_ref(v___f_821_);
v___x_861_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_821_, v___f_842_, v_type_853_, v___x_858_);
lean_inc_ref(v_value_854_);
v___y_831_ = v_value_854_;
v___y_832_ = v___f_842_;
v___y_833_ = v___x_861_;
goto v___jp_830_;
}
}
else
{
lean_object* v___x_862_; 
lean_inc_ref(v_type_853_);
lean_inc_ref(v___f_842_);
lean_inc_ref(v___f_821_);
v___x_862_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_821_, v___f_842_, v_type_853_, v___x_858_);
lean_inc_ref(v_value_854_);
v___y_831_ = v_value_854_;
v___y_832_ = v___f_842_;
v___y_833_ = v___x_862_;
goto v___jp_830_;
}
}
else
{
lean_object* v_type_863_; lean_object* v___x_864_; lean_object* v_mctx_865_; lean_object* v___x_866_; lean_object* v___x_867_; uint8_t v___x_868_; 
v_type_863_ = lean_ctor_get(v_val_731_, 3);
v___x_864_ = lean_st_ref_get(v___y_713_);
v_mctx_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc_ref_n(v_mctx_865_, 2);
lean_dec(v___x_864_);
v___x_866_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
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
lean_dec_ref(v___f_821_);
v_fst_749_ = v___x_869_;
v_mctx_750_ = v_mctx_865_;
goto v___jp_748_;
}
else
{
lean_object* v___x_870_; 
lean_dec_ref(v_mctx_865_);
lean_inc_ref(v_type_863_);
v___x_870_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_821_, v___f_842_, v_type_863_, v___x_867_);
v___y_766_ = v___x_870_;
goto v___jp_765_;
}
}
else
{
lean_object* v___x_871_; 
lean_dec_ref(v_mctx_865_);
lean_inc_ref(v_type_863_);
v___x_871_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_821_, v___f_842_, v_type_863_, v___x_867_);
v___y_766_ = v___x_871_;
goto v___jp_765_;
}
}
}
}
}
else
{
lean_dec(v___x_741_);
goto v___jp_737_;
}
}
else
{
lean_dec(v___x_741_);
goto v___jp_737_;
}
}
else
{
lean_object* v___x_873_; 
lean_dec(v___x_741_);
lean_del_object(v___x_735_);
v___x_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_873_, 0, v_fst_732_);
lean_ctor_set(v___x_873_, 1, v_snd_733_);
v_a_723_ = v___x_873_;
goto v___jp_722_;
}
v___jp_737_:
{
lean_object* v___x_739_; 
if (v_isShared_736_ == 0)
{
v___x_739_ = v___x_735_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_fst_732_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_snd_733_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
v_a_723_ = v___x_739_;
goto v___jp_722_;
}
}
v___jp_742_:
{
if (v_a_743_ == 0)
{
lean_object* v___x_744_; 
lean_dec(v___x_741_);
v___x_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_744_, 0, v_fst_732_);
lean_ctor_set(v___x_744_, 1, v_snd_733_);
v_a_723_ = v___x_744_;
goto v___jp_722_;
}
else
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
lean_inc(v___x_741_);
v___x_745_ = l_Lean_FVarIdSet_insert(v_snd_733_, v___x_741_);
v___x_746_ = l_Lean_FVarIdSet_insert(v_fst_732_, v___x_741_);
v___x_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
lean_ctor_set(v___x_747_, 1, v___x_745_);
v_a_723_ = v___x_747_;
goto v___jp_722_;
}
}
v___jp_748_:
{
lean_object* v___x_751_; lean_object* v_cache_752_; lean_object* v_zetaDeltaFVarIds_753_; lean_object* v_postponed_754_; lean_object* v_diag_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_763_; 
v___x_751_ = lean_st_ref_take(v___y_713_);
v_cache_752_ = lean_ctor_get(v___x_751_, 1);
v_zetaDeltaFVarIds_753_ = lean_ctor_get(v___x_751_, 2);
v_postponed_754_ = lean_ctor_get(v___x_751_, 3);
v_diag_755_ = lean_ctor_get(v___x_751_, 4);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_763_ == 0)
{
lean_object* v_unused_764_; 
v_unused_764_ = lean_ctor_get(v___x_751_, 0);
lean_dec(v_unused_764_);
v___x_757_ = v___x_751_;
v_isShared_758_ = v_isSharedCheck_763_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_diag_755_);
lean_inc(v_postponed_754_);
lean_inc(v_zetaDeltaFVarIds_753_);
lean_inc(v_cache_752_);
lean_dec(v___x_751_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_763_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v_mctx_750_);
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_mctx_750_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_cache_752_);
lean_ctor_set(v_reuseFailAlloc_762_, 2, v_zetaDeltaFVarIds_753_);
lean_ctor_set(v_reuseFailAlloc_762_, 3, v_postponed_754_);
lean_ctor_set(v_reuseFailAlloc_762_, 4, v_diag_755_);
v___x_760_ = v_reuseFailAlloc_762_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_761_; 
v___x_761_ = lean_st_ref_put(v___y_713_, v___x_760_);
v_a_743_ = v_fst_749_;
goto v___jp_742_;
}
}
}
v___jp_765_:
{
lean_object* v_snd_767_; lean_object* v_fst_768_; lean_object* v_mctx_769_; uint8_t v___x_770_; 
v_snd_767_ = lean_ctor_get(v___y_766_, 1);
lean_inc(v_snd_767_);
v_fst_768_ = lean_ctor_get(v___y_766_, 0);
lean_inc(v_fst_768_);
lean_dec_ref(v___y_766_);
v_mctx_769_ = lean_ctor_get(v_snd_767_, 1);
lean_inc_ref(v_mctx_769_);
lean_dec(v_snd_767_);
v___x_770_ = lean_unbox(v_fst_768_);
lean_dec(v_fst_768_);
v_fst_749_ = v___x_770_;
v_mctx_750_ = v_mctx_769_;
goto v___jp_748_;
}
v___jp_771_:
{
lean_object* v_mctx_774_; lean_object* v___x_775_; lean_object* v_cache_776_; lean_object* v_zetaDeltaFVarIds_777_; lean_object* v_postponed_778_; lean_object* v_diag_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_787_; 
v_mctx_774_ = lean_ctor_get(v_snd_773_, 1);
lean_inc_ref(v_mctx_774_);
lean_dec_ref(v_snd_773_);
v___x_775_ = lean_st_ref_take(v___y_713_);
v_cache_776_ = lean_ctor_get(v___x_775_, 1);
v_zetaDeltaFVarIds_777_ = lean_ctor_get(v___x_775_, 2);
v_postponed_778_ = lean_ctor_get(v___x_775_, 3);
v_diag_779_ = lean_ctor_get(v___x_775_, 4);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_787_ == 0)
{
lean_object* v_unused_788_; 
v_unused_788_ = lean_ctor_get(v___x_775_, 0);
lean_dec(v_unused_788_);
v___x_781_ = v___x_775_;
v_isShared_782_ = v_isSharedCheck_787_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_diag_779_);
lean_inc(v_postponed_778_);
lean_inc(v_zetaDeltaFVarIds_777_);
lean_inc(v_cache_776_);
lean_dec(v___x_775_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_787_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v_mctx_774_);
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_mctx_774_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_cache_776_);
lean_ctor_set(v_reuseFailAlloc_786_, 2, v_zetaDeltaFVarIds_777_);
lean_ctor_set(v_reuseFailAlloc_786_, 3, v_postponed_778_);
lean_ctor_set(v_reuseFailAlloc_786_, 4, v_diag_779_);
v___x_784_ = v_reuseFailAlloc_786_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_785_; 
v___x_785_ = lean_st_ref_put(v___y_713_, v___x_784_);
v_a_743_ = v_fst_772_;
goto v___jp_742_;
}
}
}
v___jp_789_:
{
lean_object* v_fst_791_; lean_object* v_snd_792_; uint8_t v___x_793_; 
v_fst_791_ = lean_ctor_get(v___y_790_, 0);
lean_inc(v_fst_791_);
v_snd_792_ = lean_ctor_get(v___y_790_, 1);
lean_inc(v_snd_792_);
lean_dec_ref(v___y_790_);
v___x_793_ = lean_unbox(v_fst_791_);
lean_dec(v_fst_791_);
v_fst_772_ = v___x_793_;
v_snd_773_ = v_snd_792_;
goto v___jp_771_;
}
v___jp_794_:
{
lean_object* v___x_797_; lean_object* v_cache_798_; lean_object* v_zetaDeltaFVarIds_799_; lean_object* v_postponed_800_; lean_object* v_diag_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_809_; 
v___x_797_ = lean_st_ref_take(v___y_713_);
v_cache_798_ = lean_ctor_get(v___x_797_, 1);
v_zetaDeltaFVarIds_799_ = lean_ctor_get(v___x_797_, 2);
v_postponed_800_ = lean_ctor_get(v___x_797_, 3);
v_diag_801_ = lean_ctor_get(v___x_797_, 4);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_809_ == 0)
{
lean_object* v_unused_810_; 
v_unused_810_ = lean_ctor_get(v___x_797_, 0);
lean_dec(v_unused_810_);
v___x_803_ = v___x_797_;
v_isShared_804_ = v_isSharedCheck_809_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_diag_801_);
lean_inc(v_postponed_800_);
lean_inc(v_zetaDeltaFVarIds_799_);
lean_inc(v_cache_798_);
lean_dec(v___x_797_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_809_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 0, v_mctx_796_);
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_mctx_796_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_cache_798_);
lean_ctor_set(v_reuseFailAlloc_808_, 2, v_zetaDeltaFVarIds_799_);
lean_ctor_set(v_reuseFailAlloc_808_, 3, v_postponed_800_);
lean_ctor_set(v_reuseFailAlloc_808_, 4, v_diag_801_);
v___x_806_ = v_reuseFailAlloc_808_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_807_; 
v___x_807_ = lean_st_ref_put(v___y_713_, v___x_806_);
v_a_743_ = v_fst_795_;
goto v___jp_742_;
}
}
}
v___jp_811_:
{
lean_object* v_snd_813_; lean_object* v_fst_814_; lean_object* v_mctx_815_; uint8_t v___x_816_; 
v_snd_813_ = lean_ctor_get(v___y_812_, 1);
lean_inc(v_snd_813_);
v_fst_814_ = lean_ctor_get(v___y_812_, 0);
lean_inc(v_fst_814_);
lean_dec_ref(v___y_812_);
v_mctx_815_ = lean_ctor_get(v_snd_813_, 1);
lean_inc_ref(v_mctx_815_);
lean_dec(v_snd_813_);
v___x_816_ = lean_unbox(v_fst_814_);
lean_dec(v_fst_814_);
v_fst_795_ = v___x_816_;
v_mctx_796_ = v_mctx_815_;
goto v___jp_794_;
}
}
}
v___jp_722_:
{
lean_object* v___x_725_; 
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 1, v_a_723_);
lean_ctor_set(v___x_719_, 0, v___x_721_);
v___x_725_ = v___x_719_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_a_723_);
v___x_725_ = v_reuseFailAlloc_729_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
size_t v___x_726_; size_t v___x_727_; 
v___x_726_ = ((size_t)1ULL);
v___x_727_ = lean_usize_add(v_i_711_, v___x_726_);
v_i_711_ = v___x_727_;
v_b_712_ = v___x_725_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_forbidden_877_, lean_object* v_ignoreLetDecls_878_, lean_object* v_as_879_, lean_object* v_sz_880_, lean_object* v_i_881_, lean_object* v_b_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_885_; size_t v_sz_boxed_886_; size_t v_i_boxed_887_; lean_object* v_res_888_; 
v_ignoreLetDecls_boxed_885_ = lean_unbox(v_ignoreLetDecls_878_);
v_sz_boxed_886_ = lean_unbox_usize(v_sz_880_);
lean_dec(v_sz_880_);
v_i_boxed_887_ = lean_unbox_usize(v_i_881_);
lean_dec(v_i_881_);
v_res_888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(v_forbidden_877_, v_ignoreLetDecls_boxed_885_, v_as_879_, v_sz_boxed_886_, v_i_boxed_887_, v_b_882_, v___y_883_);
lean_dec(v___y_883_);
lean_dec_ref(v_as_879_);
lean_dec(v_forbidden_877_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2(lean_object* v_forbidden_889_, uint8_t v_ignoreLetDecls_890_, lean_object* v_as_891_, size_t v_sz_892_, size_t v_i_893_, lean_object* v_b_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
uint8_t v___x_900_; 
v___x_900_ = lean_usize_dec_lt(v_i_893_, v_sz_892_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; 
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v_b_894_);
return v___x_901_;
}
else
{
lean_object* v_snd_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_1060_; 
v_snd_902_ = lean_ctor_get(v_b_894_, 1);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_b_894_);
if (v_isSharedCheck_1060_ == 0)
{
lean_object* v_unused_1061_; 
v_unused_1061_ = lean_ctor_get(v_b_894_, 0);
lean_dec(v_unused_1061_);
v___x_904_ = v_b_894_;
v_isShared_905_ = v_isSharedCheck_1060_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_snd_902_);
lean_dec(v_b_894_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_1060_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_906_; lean_object* v_a_908_; lean_object* v_a_915_; 
v___x_906_ = lean_box(0);
v_a_915_ = lean_array_uget_borrowed(v_as_891_, v_i_893_);
if (lean_obj_tag(v_a_915_) == 0)
{
v_a_908_ = v_snd_902_;
goto v___jp_907_;
}
else
{
lean_object* v_val_916_; lean_object* v_fst_917_; lean_object* v_snd_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_1059_; 
v_val_916_ = lean_ctor_get(v_a_915_, 0);
v_fst_917_ = lean_ctor_get(v_snd_902_, 0);
v_snd_918_ = lean_ctor_get(v_snd_902_, 1);
v_isSharedCheck_1059_ = !lean_is_exclusive(v_snd_902_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_920_ = v_snd_902_;
v_isShared_921_ = v_isSharedCheck_1059_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_snd_918_);
lean_inc(v_fst_917_);
lean_dec(v_snd_902_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_1059_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_926_; uint8_t v_a_928_; uint8_t v_fst_934_; lean_object* v_mctx_935_; lean_object* v___y_951_; uint8_t v_fst_957_; lean_object* v_snd_958_; lean_object* v___y_975_; uint8_t v_fst_980_; lean_object* v_mctx_981_; lean_object* v___y_997_; uint8_t v___x_1002_; 
v___x_926_ = l_Lean_LocalDecl_fvarId(v_val_916_);
v___x_1002_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v___x_926_, v_forbidden_889_);
if (v___x_1002_ == 0)
{
uint8_t v___x_1003_; 
v___x_1003_ = l_Lean_LocalDecl_isAuxDecl(v_val_916_);
if (v___x_1003_ == 0)
{
uint8_t v___x_1004_; uint8_t v___x_1005_; 
v___x_1004_ = l_Lean_LocalDecl_binderInfo(v_val_916_);
v___x_1005_ = l_Lean_BinderInfo_isInstImplicit(v___x_1004_);
if (v___x_1005_ == 0)
{
lean_object* v___f_1006_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v_snd_1010_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; uint8_t v___y_1025_; 
lean_inc(v_fst_917_);
v___f_1006_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1006_, 0, v_fst_917_);
if (v_ignoreLetDecls_890_ == 0)
{
lean_del_object(v___x_920_);
v___y_1025_ = v___x_1002_;
goto v___jp_1024_;
}
else
{
uint8_t v___x_1057_; 
v___x_1057_ = l_Lean_LocalDecl_isLet(v_val_916_, v___x_1002_);
if (v___x_1057_ == 0)
{
lean_del_object(v___x_920_);
v___y_1025_ = v___x_1057_;
goto v___jp_1024_;
}
else
{
lean_dec_ref(v___f_1006_);
lean_dec(v___x_926_);
goto v___jp_922_;
}
}
v___jp_1007_:
{
uint8_t v___x_1011_; 
v___x_1011_ = l_Lean_Expr_hasFVar(v___y_1009_);
if (v___x_1011_ == 0)
{
uint8_t v___x_1012_; 
v___x_1012_ = l_Lean_Expr_hasMVar(v___y_1009_);
if (v___x_1012_ == 0)
{
lean_dec_ref(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec_ref(v___f_1006_);
v_fst_957_ = v___x_1012_;
v_snd_958_ = v_snd_1010_;
goto v___jp_956_;
}
else
{
lean_object* v___x_1013_; 
v___x_1013_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1006_, v___y_1008_, v___y_1009_, v_snd_1010_);
v___y_975_ = v___x_1013_;
goto v___jp_974_;
}
}
else
{
lean_object* v___x_1014_; 
v___x_1014_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1006_, v___y_1008_, v___y_1009_, v_snd_1010_);
v___y_975_ = v___x_1014_;
goto v___jp_974_;
}
}
v___jp_1015_:
{
lean_object* v_fst_1019_; uint8_t v___x_1020_; 
v_fst_1019_ = lean_ctor_get(v___y_1018_, 0);
v___x_1020_ = lean_unbox(v_fst_1019_);
if (v___x_1020_ == 0)
{
lean_object* v_snd_1021_; 
v_snd_1021_ = lean_ctor_get(v___y_1018_, 1);
lean_inc(v_snd_1021_);
lean_dec_ref(v___y_1018_);
v___y_1008_ = v___y_1016_;
v___y_1009_ = v___y_1017_;
v_snd_1010_ = v_snd_1021_;
goto v___jp_1007_;
}
else
{
lean_object* v_snd_1022_; uint8_t v___x_1023_; 
lean_inc(v_fst_1019_);
lean_dec_ref(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec_ref(v___f_1006_);
v_snd_1022_ = lean_ctor_get(v___y_1018_, 1);
lean_inc(v_snd_1022_);
lean_dec_ref(v___y_1018_);
v___x_1023_ = lean_unbox(v_fst_1019_);
lean_dec(v_fst_1019_);
v_fst_957_ = v___x_1023_;
v_snd_958_ = v_snd_1022_;
goto v___jp_956_;
}
}
v___jp_1024_:
{
lean_object* v___x_1026_; lean_object* v___f_1027_; 
v___x_1026_ = lean_box(v___y_1025_);
v___f_1027_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1027_, 0, v___x_1026_);
if (lean_obj_tag(v_val_916_) == 0)
{
lean_object* v_type_1028_; lean_object* v___x_1029_; lean_object* v_mctx_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
v_type_1028_ = lean_ctor_get(v_val_916_, 3);
v___x_1029_ = lean_st_ref_get(v___y_896_);
v_mctx_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc_ref_n(v_mctx_1030_, 2);
lean_dec(v___x_1029_);
v___x_1031_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
lean_ctor_set(v___x_1032_, 1, v_mctx_1030_);
v___x_1033_ = l_Lean_Expr_hasFVar(v_type_1028_);
if (v___x_1033_ == 0)
{
uint8_t v___x_1034_; 
v___x_1034_ = l_Lean_Expr_hasMVar(v_type_1028_);
if (v___x_1034_ == 0)
{
lean_dec_ref_known(v___x_1032_, 2);
lean_dec_ref(v___f_1027_);
lean_dec_ref(v___f_1006_);
v_fst_980_ = v___x_1034_;
v_mctx_981_ = v_mctx_1030_;
goto v___jp_979_;
}
else
{
lean_object* v___x_1035_; 
lean_dec_ref(v_mctx_1030_);
lean_inc_ref(v_type_1028_);
v___x_1035_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1006_, v___f_1027_, v_type_1028_, v___x_1032_);
v___y_997_ = v___x_1035_;
goto v___jp_996_;
}
}
else
{
lean_object* v___x_1036_; 
lean_dec_ref(v_mctx_1030_);
lean_inc_ref(v_type_1028_);
v___x_1036_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1006_, v___f_1027_, v_type_1028_, v___x_1032_);
v___y_997_ = v___x_1036_;
goto v___jp_996_;
}
}
else
{
uint8_t v_nondep_1037_; 
v_nondep_1037_ = lean_ctor_get_uint8(v_val_916_, sizeof(void*)*5);
if (v_nondep_1037_ == 0)
{
lean_object* v_type_1038_; lean_object* v_value_1039_; lean_object* v___x_1040_; lean_object* v_mctx_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; 
v_type_1038_ = lean_ctor_get(v_val_916_, 3);
v_value_1039_ = lean_ctor_get(v_val_916_, 4);
v___x_1040_ = lean_st_ref_get(v___y_896_);
v_mctx_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc_ref(v_mctx_1041_);
lean_dec(v___x_1040_);
v___x_1042_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
lean_ctor_set(v___x_1043_, 1, v_mctx_1041_);
v___x_1044_ = l_Lean_Expr_hasFVar(v_type_1038_);
if (v___x_1044_ == 0)
{
uint8_t v___x_1045_; 
v___x_1045_ = l_Lean_Expr_hasMVar(v_type_1038_);
if (v___x_1045_ == 0)
{
lean_inc_ref(v_value_1039_);
v___y_1008_ = v___f_1027_;
v___y_1009_ = v_value_1039_;
v_snd_1010_ = v___x_1043_;
goto v___jp_1007_;
}
else
{
lean_object* v___x_1046_; 
lean_inc_ref(v_type_1038_);
lean_inc_ref(v___f_1027_);
lean_inc_ref(v___f_1006_);
v___x_1046_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1006_, v___f_1027_, v_type_1038_, v___x_1043_);
lean_inc_ref(v_value_1039_);
v___y_1016_ = v___f_1027_;
v___y_1017_ = v_value_1039_;
v___y_1018_ = v___x_1046_;
goto v___jp_1015_;
}
}
else
{
lean_object* v___x_1047_; 
lean_inc_ref(v_type_1038_);
lean_inc_ref(v___f_1027_);
lean_inc_ref(v___f_1006_);
v___x_1047_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1006_, v___f_1027_, v_type_1038_, v___x_1043_);
lean_inc_ref(v_value_1039_);
v___y_1016_ = v___f_1027_;
v___y_1017_ = v_value_1039_;
v___y_1018_ = v___x_1047_;
goto v___jp_1015_;
}
}
else
{
lean_object* v_type_1048_; lean_object* v___x_1049_; lean_object* v_mctx_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; 
v_type_1048_ = lean_ctor_get(v_val_916_, 3);
v___x_1049_ = lean_st_ref_get(v___y_896_);
v_mctx_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc_ref_n(v_mctx_1050_, 2);
lean_dec(v___x_1049_);
v___x_1051_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
lean_ctor_set(v___x_1052_, 1, v_mctx_1050_);
v___x_1053_ = l_Lean_Expr_hasFVar(v_type_1048_);
if (v___x_1053_ == 0)
{
uint8_t v___x_1054_; 
v___x_1054_ = l_Lean_Expr_hasMVar(v_type_1048_);
if (v___x_1054_ == 0)
{
lean_dec_ref_known(v___x_1052_, 2);
lean_dec_ref(v___f_1027_);
lean_dec_ref(v___f_1006_);
v_fst_934_ = v___x_1054_;
v_mctx_935_ = v_mctx_1050_;
goto v___jp_933_;
}
else
{
lean_object* v___x_1055_; 
lean_dec_ref(v_mctx_1050_);
lean_inc_ref(v_type_1048_);
v___x_1055_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1006_, v___f_1027_, v_type_1048_, v___x_1052_);
v___y_951_ = v___x_1055_;
goto v___jp_950_;
}
}
else
{
lean_object* v___x_1056_; 
lean_dec_ref(v_mctx_1050_);
lean_inc_ref(v_type_1048_);
v___x_1056_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1006_, v___f_1027_, v_type_1048_, v___x_1052_);
v___y_951_ = v___x_1056_;
goto v___jp_950_;
}
}
}
}
}
else
{
lean_dec(v___x_926_);
goto v___jp_922_;
}
}
else
{
lean_dec(v___x_926_);
goto v___jp_922_;
}
}
else
{
lean_object* v___x_1058_; 
lean_dec(v___x_926_);
lean_del_object(v___x_920_);
v___x_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1058_, 0, v_fst_917_);
lean_ctor_set(v___x_1058_, 1, v_snd_918_);
v_a_908_ = v___x_1058_;
goto v___jp_907_;
}
v___jp_922_:
{
lean_object* v___x_924_; 
if (v_isShared_921_ == 0)
{
v___x_924_ = v___x_920_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_fst_917_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_snd_918_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
v_a_908_ = v___x_924_;
goto v___jp_907_;
}
}
v___jp_927_:
{
if (v_a_928_ == 0)
{
lean_object* v___x_929_; 
lean_dec(v___x_926_);
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v_fst_917_);
lean_ctor_set(v___x_929_, 1, v_snd_918_);
v_a_908_ = v___x_929_;
goto v___jp_907_;
}
else
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
lean_inc(v___x_926_);
v___x_930_ = l_Lean_FVarIdSet_insert(v_snd_918_, v___x_926_);
v___x_931_ = l_Lean_FVarIdSet_insert(v_fst_917_, v___x_926_);
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
lean_ctor_set(v___x_932_, 1, v___x_930_);
v_a_908_ = v___x_932_;
goto v___jp_907_;
}
}
v___jp_933_:
{
lean_object* v___x_936_; lean_object* v_cache_937_; lean_object* v_zetaDeltaFVarIds_938_; lean_object* v_postponed_939_; lean_object* v_diag_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_948_; 
v___x_936_ = lean_st_ref_take(v___y_896_);
v_cache_937_ = lean_ctor_get(v___x_936_, 1);
v_zetaDeltaFVarIds_938_ = lean_ctor_get(v___x_936_, 2);
v_postponed_939_ = lean_ctor_get(v___x_936_, 3);
v_diag_940_ = lean_ctor_get(v___x_936_, 4);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_948_ == 0)
{
lean_object* v_unused_949_; 
v_unused_949_ = lean_ctor_get(v___x_936_, 0);
lean_dec(v_unused_949_);
v___x_942_ = v___x_936_;
v_isShared_943_ = v_isSharedCheck_948_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_diag_940_);
lean_inc(v_postponed_939_);
lean_inc(v_zetaDeltaFVarIds_938_);
lean_inc(v_cache_937_);
lean_dec(v___x_936_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_948_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v_mctx_935_);
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_mctx_935_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_cache_937_);
lean_ctor_set(v_reuseFailAlloc_947_, 2, v_zetaDeltaFVarIds_938_);
lean_ctor_set(v_reuseFailAlloc_947_, 3, v_postponed_939_);
lean_ctor_set(v_reuseFailAlloc_947_, 4, v_diag_940_);
v___x_945_ = v_reuseFailAlloc_947_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
lean_object* v___x_946_; 
v___x_946_ = lean_st_ref_put(v___y_896_, v___x_945_);
v_a_928_ = v_fst_934_;
goto v___jp_927_;
}
}
}
v___jp_950_:
{
lean_object* v_snd_952_; lean_object* v_fst_953_; lean_object* v_mctx_954_; uint8_t v___x_955_; 
v_snd_952_ = lean_ctor_get(v___y_951_, 1);
lean_inc(v_snd_952_);
v_fst_953_ = lean_ctor_get(v___y_951_, 0);
lean_inc(v_fst_953_);
lean_dec_ref(v___y_951_);
v_mctx_954_ = lean_ctor_get(v_snd_952_, 1);
lean_inc_ref(v_mctx_954_);
lean_dec(v_snd_952_);
v___x_955_ = lean_unbox(v_fst_953_);
lean_dec(v_fst_953_);
v_fst_934_ = v___x_955_;
v_mctx_935_ = v_mctx_954_;
goto v___jp_933_;
}
v___jp_956_:
{
lean_object* v_mctx_959_; lean_object* v___x_960_; lean_object* v_cache_961_; lean_object* v_zetaDeltaFVarIds_962_; lean_object* v_postponed_963_; lean_object* v_diag_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_972_; 
v_mctx_959_ = lean_ctor_get(v_snd_958_, 1);
lean_inc_ref(v_mctx_959_);
lean_dec_ref(v_snd_958_);
v___x_960_ = lean_st_ref_take(v___y_896_);
v_cache_961_ = lean_ctor_get(v___x_960_, 1);
v_zetaDeltaFVarIds_962_ = lean_ctor_get(v___x_960_, 2);
v_postponed_963_ = lean_ctor_get(v___x_960_, 3);
v_diag_964_ = lean_ctor_get(v___x_960_, 4);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_972_ == 0)
{
lean_object* v_unused_973_; 
v_unused_973_ = lean_ctor_get(v___x_960_, 0);
lean_dec(v_unused_973_);
v___x_966_ = v___x_960_;
v_isShared_967_ = v_isSharedCheck_972_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_diag_964_);
lean_inc(v_postponed_963_);
lean_inc(v_zetaDeltaFVarIds_962_);
lean_inc(v_cache_961_);
lean_dec(v___x_960_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_972_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v_mctx_959_);
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_mctx_959_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v_cache_961_);
lean_ctor_set(v_reuseFailAlloc_971_, 2, v_zetaDeltaFVarIds_962_);
lean_ctor_set(v_reuseFailAlloc_971_, 3, v_postponed_963_);
lean_ctor_set(v_reuseFailAlloc_971_, 4, v_diag_964_);
v___x_969_ = v_reuseFailAlloc_971_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_970_; 
v___x_970_ = lean_st_ref_put(v___y_896_, v___x_969_);
v_a_928_ = v_fst_957_;
goto v___jp_927_;
}
}
}
v___jp_974_:
{
lean_object* v_fst_976_; lean_object* v_snd_977_; uint8_t v___x_978_; 
v_fst_976_ = lean_ctor_get(v___y_975_, 0);
lean_inc(v_fst_976_);
v_snd_977_ = lean_ctor_get(v___y_975_, 1);
lean_inc(v_snd_977_);
lean_dec_ref(v___y_975_);
v___x_978_ = lean_unbox(v_fst_976_);
lean_dec(v_fst_976_);
v_fst_957_ = v___x_978_;
v_snd_958_ = v_snd_977_;
goto v___jp_956_;
}
v___jp_979_:
{
lean_object* v___x_982_; lean_object* v_cache_983_; lean_object* v_zetaDeltaFVarIds_984_; lean_object* v_postponed_985_; lean_object* v_diag_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_994_; 
v___x_982_ = lean_st_ref_take(v___y_896_);
v_cache_983_ = lean_ctor_get(v___x_982_, 1);
v_zetaDeltaFVarIds_984_ = lean_ctor_get(v___x_982_, 2);
v_postponed_985_ = lean_ctor_get(v___x_982_, 3);
v_diag_986_ = lean_ctor_get(v___x_982_, 4);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_994_ == 0)
{
lean_object* v_unused_995_; 
v_unused_995_ = lean_ctor_get(v___x_982_, 0);
lean_dec(v_unused_995_);
v___x_988_ = v___x_982_;
v_isShared_989_ = v_isSharedCheck_994_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_diag_986_);
lean_inc(v_postponed_985_);
lean_inc(v_zetaDeltaFVarIds_984_);
lean_inc(v_cache_983_);
lean_dec(v___x_982_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_994_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v_mctx_981_);
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_mctx_981_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_cache_983_);
lean_ctor_set(v_reuseFailAlloc_993_, 2, v_zetaDeltaFVarIds_984_);
lean_ctor_set(v_reuseFailAlloc_993_, 3, v_postponed_985_);
lean_ctor_set(v_reuseFailAlloc_993_, 4, v_diag_986_);
v___x_991_ = v_reuseFailAlloc_993_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_992_; 
v___x_992_ = lean_st_ref_put(v___y_896_, v___x_991_);
v_a_928_ = v_fst_980_;
goto v___jp_927_;
}
}
}
v___jp_996_:
{
lean_object* v_snd_998_; lean_object* v_fst_999_; lean_object* v_mctx_1000_; uint8_t v___x_1001_; 
v_snd_998_ = lean_ctor_get(v___y_997_, 1);
lean_inc(v_snd_998_);
v_fst_999_ = lean_ctor_get(v___y_997_, 0);
lean_inc(v_fst_999_);
lean_dec_ref(v___y_997_);
v_mctx_1000_ = lean_ctor_get(v_snd_998_, 1);
lean_inc_ref(v_mctx_1000_);
lean_dec(v_snd_998_);
v___x_1001_ = lean_unbox(v_fst_999_);
lean_dec(v_fst_999_);
v_fst_980_ = v___x_1001_;
v_mctx_981_ = v_mctx_1000_;
goto v___jp_979_;
}
}
}
v___jp_907_:
{
lean_object* v___x_910_; 
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 1, v_a_908_);
lean_ctor_set(v___x_904_, 0, v___x_906_);
v___x_910_ = v___x_904_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v_a_908_);
v___x_910_ = v_reuseFailAlloc_914_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
size_t v___x_911_; size_t v___x_912_; lean_object* v___x_913_; 
v___x_911_ = ((size_t)1ULL);
v___x_912_ = lean_usize_add(v_i_893_, v___x_911_);
v___x_913_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(v_forbidden_889_, v_ignoreLetDecls_890_, v_as_891_, v_sz_892_, v___x_912_, v___x_910_, v___y_896_);
return v___x_913_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2___boxed(lean_object* v_forbidden_1062_, lean_object* v_ignoreLetDecls_1063_, lean_object* v_as_1064_, lean_object* v_sz_1065_, lean_object* v_i_1066_, lean_object* v_b_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1073_; size_t v_sz_boxed_1074_; size_t v_i_boxed_1075_; lean_object* v_res_1076_; 
v_ignoreLetDecls_boxed_1073_ = lean_unbox(v_ignoreLetDecls_1063_);
v_sz_boxed_1074_ = lean_unbox_usize(v_sz_1065_);
lean_dec(v_sz_1065_);
v_i_boxed_1075_ = lean_unbox_usize(v_i_1066_);
lean_dec(v_i_1066_);
v_res_1076_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2(v_forbidden_1062_, v_ignoreLetDecls_boxed_1073_, v_as_1064_, v_sz_boxed_1074_, v_i_boxed_1075_, v_b_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec_ref(v_as_1064_);
lean_dec(v_forbidden_1062_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(lean_object* v_init_1077_, lean_object* v_forbidden_1078_, uint8_t v_ignoreLetDecls_1079_, lean_object* v_n_1080_, lean_object* v_b_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
if (lean_obj_tag(v_n_1080_) == 0)
{
lean_object* v_cs_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; size_t v_sz_1090_; size_t v___x_1091_; lean_object* v___x_1092_; 
v_cs_1087_ = lean_ctor_get(v_n_1080_, 0);
v___x_1088_ = lean_box(0);
v___x_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
lean_ctor_set(v___x_1089_, 1, v_b_1081_);
v_sz_1090_ = lean_array_size(v_cs_1087_);
v___x_1091_ = ((size_t)0ULL);
v___x_1092_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(v_init_1077_, v_forbidden_1078_, v_ignoreLetDecls_1079_, v_cs_1087_, v_sz_1090_, v___x_1091_, v___x_1089_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1107_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1095_ = v___x_1092_;
v_isShared_1096_ = v_isSharedCheck_1107_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1092_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1107_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v_fst_1097_; 
v_fst_1097_ = lean_ctor_get(v_a_1093_, 0);
if (lean_obj_tag(v_fst_1097_) == 0)
{
lean_object* v_snd_1098_; lean_object* v___x_1099_; lean_object* v___x_1101_; 
v_snd_1098_ = lean_ctor_get(v_a_1093_, 1);
lean_inc(v_snd_1098_);
lean_dec(v_a_1093_);
v___x_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1099_, 0, v_snd_1098_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v___x_1099_);
v___x_1101_ = v___x_1095_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1099_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
else
{
lean_object* v_val_1103_; lean_object* v___x_1105_; 
lean_inc_ref(v_fst_1097_);
lean_dec(v_a_1093_);
v_val_1103_ = lean_ctor_get(v_fst_1097_, 0);
lean_inc(v_val_1103_);
lean_dec_ref_known(v_fst_1097_, 1);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v_val_1103_);
v___x_1105_ = v___x_1095_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_val_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
v_a_1108_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1092_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1092_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
else
{
lean_object* v_vs_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; size_t v_sz_1119_; size_t v___x_1120_; lean_object* v___x_1121_; 
v_vs_1116_ = lean_ctor_get(v_n_1080_, 0);
v___x_1117_ = lean_box(0);
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
lean_ctor_set(v___x_1118_, 1, v_b_1081_);
v_sz_1119_ = lean_array_size(v_vs_1116_);
v___x_1120_ = ((size_t)0ULL);
v___x_1121_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2(v_forbidden_1078_, v_ignoreLetDecls_1079_, v_vs_1116_, v_sz_1119_, v___x_1120_, v___x_1118_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1136_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1124_ = v___x_1121_;
v_isShared_1125_ = v_isSharedCheck_1136_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1121_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1136_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v_fst_1126_; 
v_fst_1126_ = lean_ctor_get(v_a_1122_, 0);
if (lean_obj_tag(v_fst_1126_) == 0)
{
lean_object* v_snd_1127_; lean_object* v___x_1128_; lean_object* v___x_1130_; 
v_snd_1127_ = lean_ctor_get(v_a_1122_, 1);
lean_inc(v_snd_1127_);
lean_dec(v_a_1122_);
v___x_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1128_, 0, v_snd_1127_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v___x_1128_);
v___x_1130_ = v___x_1124_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
else
{
lean_object* v_val_1132_; lean_object* v___x_1134_; 
lean_inc_ref(v_fst_1126_);
lean_dec(v_a_1122_);
v_val_1132_ = lean_ctor_get(v_fst_1126_, 0);
lean_inc(v_val_1132_);
lean_dec_ref_known(v_fst_1126_, 1);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v_val_1132_);
v___x_1134_ = v___x_1124_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_val_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
v_a_1137_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1121_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1121_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(lean_object* v_init_1145_, lean_object* v_forbidden_1146_, uint8_t v_ignoreLetDecls_1147_, lean_object* v_as_1148_, size_t v_sz_1149_, size_t v_i_1150_, lean_object* v_b_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
uint8_t v___x_1157_; 
v___x_1157_ = lean_usize_dec_lt(v_i_1150_, v_sz_1149_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; 
v___x_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1158_, 0, v_b_1151_);
return v___x_1158_;
}
else
{
lean_object* v_snd_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1193_; 
v_snd_1159_ = lean_ctor_get(v_b_1151_, 1);
v_isSharedCheck_1193_ = !lean_is_exclusive(v_b_1151_);
if (v_isSharedCheck_1193_ == 0)
{
lean_object* v_unused_1194_; 
v_unused_1194_ = lean_ctor_get(v_b_1151_, 0);
lean_dec(v_unused_1194_);
v___x_1161_ = v_b_1151_;
v_isShared_1162_ = v_isSharedCheck_1193_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_snd_1159_);
lean_dec(v_b_1151_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1193_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1163_; lean_object* v_a_1164_; lean_object* v___x_1165_; 
v___x_1163_ = lean_box(0);
v_a_1164_ = lean_array_uget_borrowed(v_as_1148_, v_i_1150_);
lean_inc(v_snd_1159_);
v___x_1165_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(v_init_1145_, v_forbidden_1146_, v_ignoreLetDecls_1147_, v_a_1164_, v_snd_1159_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1184_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1168_ = v___x_1165_;
v_isShared_1169_ = v_isSharedCheck_1184_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1165_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1184_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
if (lean_obj_tag(v_a_1166_) == 0)
{
lean_object* v___x_1170_; lean_object* v___x_1172_; 
v___x_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1170_, 0, v_a_1166_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 0, v___x_1170_);
v___x_1172_ = v___x_1161_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1170_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v_snd_1159_);
v___x_1172_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
lean_object* v___x_1174_; 
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 0, v___x_1172_);
v___x_1174_ = v___x_1168_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1179_; 
lean_del_object(v___x_1168_);
lean_dec(v_snd_1159_);
v_a_1177_ = lean_ctor_get(v_a_1166_, 0);
lean_inc(v_a_1177_);
lean_dec_ref_known(v_a_1166_, 1);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 1, v_a_1177_);
lean_ctor_set(v___x_1161_, 0, v___x_1163_);
v___x_1179_ = v___x_1161_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___x_1163_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_a_1177_);
v___x_1179_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
size_t v___x_1180_; size_t v___x_1181_; 
v___x_1180_ = ((size_t)1ULL);
v___x_1181_ = lean_usize_add(v_i_1150_, v___x_1180_);
v_i_1150_ = v___x_1181_;
v_b_1151_ = v___x_1179_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
lean_del_object(v___x_1161_);
lean_dec(v_snd_1159_);
v_a_1185_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1165_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1165_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1___boxed(lean_object* v_init_1195_, lean_object* v_forbidden_1196_, lean_object* v_ignoreLetDecls_1197_, lean_object* v_as_1198_, lean_object* v_sz_1199_, lean_object* v_i_1200_, lean_object* v_b_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1207_; size_t v_sz_boxed_1208_; size_t v_i_boxed_1209_; lean_object* v_res_1210_; 
v_ignoreLetDecls_boxed_1207_ = lean_unbox(v_ignoreLetDecls_1197_);
v_sz_boxed_1208_ = lean_unbox_usize(v_sz_1199_);
lean_dec(v_sz_1199_);
v_i_boxed_1209_ = lean_unbox_usize(v_i_1200_);
lean_dec(v_i_1200_);
v_res_1210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(v_init_1195_, v_forbidden_1196_, v_ignoreLetDecls_boxed_1207_, v_as_1198_, v_sz_boxed_1208_, v_i_boxed_1209_, v_b_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec_ref(v_as_1198_);
lean_dec(v_forbidden_1196_);
lean_dec_ref(v_init_1195_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0___boxed(lean_object* v_init_1211_, lean_object* v_forbidden_1212_, lean_object* v_ignoreLetDecls_1213_, lean_object* v_n_1214_, lean_object* v_b_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1221_; lean_object* v_res_1222_; 
v_ignoreLetDecls_boxed_1221_ = lean_unbox(v_ignoreLetDecls_1213_);
v_res_1222_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(v_init_1211_, v_forbidden_1212_, v_ignoreLetDecls_boxed_1221_, v_n_1214_, v_b_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec_ref(v_n_1214_);
lean_dec(v_forbidden_1212_);
lean_dec_ref(v_init_1211_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0(lean_object* v_forbidden_1223_, uint8_t v_ignoreLetDecls_1224_, lean_object* v_t_1225_, lean_object* v_init_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v_root_1232_; lean_object* v_tail_1233_; lean_object* v___x_1234_; 
v_root_1232_ = lean_ctor_get(v_t_1225_, 0);
v_tail_1233_ = lean_ctor_get(v_t_1225_, 1);
lean_inc_ref(v_init_1226_);
v___x_1234_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(v_init_1226_, v_forbidden_1223_, v_ignoreLetDecls_1224_, v_root_1232_, v_init_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
lean_dec_ref(v_init_1226_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1271_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1237_ = v___x_1234_;
v_isShared_1238_ = v_isSharedCheck_1271_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1234_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1271_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
if (lean_obj_tag(v_a_1235_) == 0)
{
lean_object* v_a_1239_; lean_object* v___x_1241_; 
v_a_1239_ = lean_ctor_get(v_a_1235_, 0);
lean_inc(v_a_1239_);
lean_dec_ref_known(v_a_1235_, 1);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 0, v_a_1239_);
v___x_1241_ = v___x_1237_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_a_1239_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; size_t v_sz_1246_; size_t v___x_1247_; lean_object* v___x_1248_; 
lean_del_object(v___x_1237_);
v_a_1243_ = lean_ctor_get(v_a_1235_, 0);
lean_inc(v_a_1243_);
lean_dec_ref_known(v_a_1235_, 1);
v___x_1244_ = lean_box(0);
v___x_1245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
lean_ctor_set(v___x_1245_, 1, v_a_1243_);
v_sz_1246_ = lean_array_size(v_tail_1233_);
v___x_1247_ = ((size_t)0ULL);
v___x_1248_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1(v_forbidden_1223_, v_ignoreLetDecls_1224_, v_tail_1233_, v_sz_1246_, v___x_1247_, v___x_1245_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1262_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1251_ = v___x_1248_;
v_isShared_1252_ = v_isSharedCheck_1262_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1248_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1262_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v_fst_1253_; 
v_fst_1253_ = lean_ctor_get(v_a_1249_, 0);
if (lean_obj_tag(v_fst_1253_) == 0)
{
lean_object* v_snd_1254_; lean_object* v___x_1256_; 
v_snd_1254_ = lean_ctor_get(v_a_1249_, 1);
lean_inc(v_snd_1254_);
lean_dec(v_a_1249_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v_snd_1254_);
v___x_1256_ = v___x_1251_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_snd_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
else
{
lean_object* v_val_1258_; lean_object* v___x_1260_; 
lean_inc_ref(v_fst_1253_);
lean_dec(v_a_1249_);
v_val_1258_ = lean_ctor_get(v_fst_1253_, 0);
lean_inc(v_val_1258_);
lean_dec_ref_known(v_fst_1253_, 1);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v_val_1258_);
v___x_1260_ = v___x_1251_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_val_1258_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
v_a_1263_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1248_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1248_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
v_a_1272_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1234_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1234_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0___boxed(lean_object* v_forbidden_1280_, lean_object* v_ignoreLetDecls_1281_, lean_object* v_t_1282_, lean_object* v_init_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1289_; lean_object* v_res_1290_; 
v_ignoreLetDecls_boxed_1289_ = lean_unbox(v_ignoreLetDecls_1281_);
v_res_1290_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0(v_forbidden_1280_, v_ignoreLetDecls_boxed_1289_, v_t_1282_, v_init_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec_ref(v_t_1282_);
lean_dec(v_forbidden_1280_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(lean_object* v_as_1291_, size_t v_i_1292_, size_t v_stop_1293_, lean_object* v_b_1294_){
_start:
{
lean_object* v___y_1296_; uint8_t v___x_1300_; 
v___x_1300_ = lean_usize_dec_eq(v_i_1292_, v_stop_1293_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1301_ = lean_array_uget_borrowed(v_as_1291_, v_i_1292_);
v___x_1302_ = l_Lean_Expr_isFVar(v___x_1301_);
if (v___x_1302_ == 0)
{
v___y_1296_ = v_b_1294_;
goto v___jp_1295_;
}
else
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = l_Lean_Expr_fvarId_x21(v___x_1301_);
v___x_1304_ = l_Lean_FVarIdSet_insert(v_b_1294_, v___x_1303_);
v___y_1296_ = v___x_1304_;
goto v___jp_1295_;
}
}
else
{
return v_b_1294_;
}
v___jp_1295_:
{
size_t v___x_1297_; size_t v___x_1298_; 
v___x_1297_ = ((size_t)1ULL);
v___x_1298_ = lean_usize_add(v_i_1292_, v___x_1297_);
v_i_1292_ = v___x_1298_;
v_b_1294_ = v___y_1296_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1___boxed(lean_object* v_as_1305_, lean_object* v_i_1306_, lean_object* v_stop_1307_, lean_object* v_b_1308_){
_start:
{
size_t v_i_boxed_1309_; size_t v_stop_boxed_1310_; lean_object* v_res_1311_; 
v_i_boxed_1309_ = lean_unbox_usize(v_i_1306_);
lean_dec(v_i_1306_);
v_stop_boxed_1310_ = lean_unbox_usize(v_stop_1307_);
lean_dec(v_stop_1307_);
v_res_1311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(v_as_1305_, v_i_boxed_1309_, v_stop_boxed_1310_, v_b_1308_);
lean_dec_ref(v_as_1305_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize(lean_object* v_targets_1312_, lean_object* v_forbidden_1313_, uint8_t v_ignoreLetDecls_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_){
_start:
{
lean_object* v_r_1320_; lean_object* v___y_1322_; lean_object* v___x_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
v_r_1320_ = lean_box(1);
v___x_1344_ = lean_unsigned_to_nat(0u);
v___x_1345_ = lean_array_get_size(v_targets_1312_);
v___x_1346_ = lean_nat_dec_lt(v___x_1344_, v___x_1345_);
if (v___x_1346_ == 0)
{
v___y_1322_ = v_r_1320_;
goto v___jp_1321_;
}
else
{
size_t v___x_1347_; size_t v___x_1348_; lean_object* v___x_1349_; 
v___x_1347_ = ((size_t)0ULL);
v___x_1348_ = lean_usize_of_nat(v___x_1345_);
v___x_1349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(v_targets_1312_, v___x_1347_, v___x_1348_, v_r_1320_);
v___y_1322_ = v___x_1349_;
goto v___jp_1321_;
}
v___jp_1321_:
{
lean_object* v_lctx_1323_; lean_object* v_decls_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v_lctx_1323_ = lean_ctor_get(v_a_1315_, 2);
v_decls_1324_ = lean_ctor_get(v_lctx_1323_, 1);
v___x_1325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1325_, 0, v___y_1322_);
lean_ctor_set(v___x_1325_, 1, v_r_1320_);
v___x_1326_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0(v_forbidden_1313_, v_ignoreLetDecls_1314_, v_decls_1324_, v___x_1325_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1335_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1329_ = v___x_1326_;
v_isShared_1330_ = v_isSharedCheck_1335_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1326_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1335_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v_snd_1331_; lean_object* v___x_1333_; 
v_snd_1331_ = lean_ctor_get(v_a_1327_, 1);
lean_inc(v_snd_1331_);
lean_dec(v_a_1327_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v_snd_1331_);
v___x_1333_ = v___x_1329_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_snd_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
else
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
v_a_1336_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1326_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1326_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize___boxed(lean_object* v_targets_1350_, lean_object* v_forbidden_1351_, lean_object* v_ignoreLetDecls_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1358_; lean_object* v_res_1359_; 
v_ignoreLetDecls_boxed_1358_ = lean_unbox(v_ignoreLetDecls_1352_);
v_res_1359_ = l_Lean_Meta_getFVarSetToGeneralize(v_targets_1350_, v_forbidden_1351_, v_ignoreLetDecls_boxed_1358_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
lean_dec(v_a_1356_);
lean_dec_ref(v_a_1355_);
lean_dec(v_a_1354_);
lean_dec_ref(v_a_1353_);
lean_dec(v_forbidden_1351_);
lean_dec_ref(v_targets_1350_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4(lean_object* v_forbidden_1360_, uint8_t v_ignoreLetDecls_1361_, lean_object* v_as_1362_, size_t v_sz_1363_, size_t v_i_1364_, lean_object* v_b_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v___x_1371_; 
v___x_1371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(v_forbidden_1360_, v_ignoreLetDecls_1361_, v_as_1362_, v_sz_1363_, v_i_1364_, v_b_1365_, v___y_1367_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___boxed(lean_object* v_forbidden_1372_, lean_object* v_ignoreLetDecls_1373_, lean_object* v_as_1374_, lean_object* v_sz_1375_, lean_object* v_i_1376_, lean_object* v_b_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1383_; size_t v_sz_boxed_1384_; size_t v_i_boxed_1385_; lean_object* v_res_1386_; 
v_ignoreLetDecls_boxed_1383_ = lean_unbox(v_ignoreLetDecls_1373_);
v_sz_boxed_1384_ = lean_unbox_usize(v_sz_1375_);
lean_dec(v_sz_1375_);
v_i_boxed_1385_ = lean_unbox_usize(v_i_1376_);
lean_dec(v_i_1376_);
v_res_1386_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4(v_forbidden_1372_, v_ignoreLetDecls_boxed_1383_, v_as_1374_, v_sz_boxed_1384_, v_i_boxed_1385_, v_b_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec_ref(v_as_1374_);
lean_dec(v_forbidden_1372_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4(lean_object* v_forbidden_1387_, uint8_t v_ignoreLetDecls_1388_, lean_object* v_as_1389_, size_t v_sz_1390_, size_t v_i_1391_, lean_object* v_b_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(v_forbidden_1387_, v_ignoreLetDecls_1388_, v_as_1389_, v_sz_1390_, v_i_1391_, v_b_1392_, v___y_1394_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_forbidden_1399_, lean_object* v_ignoreLetDecls_1400_, lean_object* v_as_1401_, lean_object* v_sz_1402_, lean_object* v_i_1403_, lean_object* v_b_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1410_; size_t v_sz_boxed_1411_; size_t v_i_boxed_1412_; lean_object* v_res_1413_; 
v_ignoreLetDecls_boxed_1410_ = lean_unbox(v_ignoreLetDecls_1400_);
v_sz_boxed_1411_ = lean_unbox_usize(v_sz_1402_);
lean_dec(v_sz_1402_);
v_i_boxed_1412_ = lean_unbox_usize(v_i_1403_);
lean_dec(v_i_1403_);
v_res_1413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4(v_forbidden_1399_, v_ignoreLetDecls_boxed_1410_, v_as_1401_, v_sz_boxed_1411_, v_i_boxed_1412_, v_b_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec_ref(v_as_1401_);
lean_dec(v_forbidden_1399_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(lean_object* v_init_1414_, lean_object* v_x_1415_){
_start:
{
if (lean_obj_tag(v_x_1415_) == 0)
{
lean_object* v_k_1416_; lean_object* v_l_1417_; lean_object* v_r_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v_k_1416_ = lean_ctor_get(v_x_1415_, 1);
lean_inc(v_k_1416_);
v_l_1417_ = lean_ctor_get(v_x_1415_, 3);
lean_inc(v_l_1417_);
v_r_1418_ = lean_ctor_get(v_x_1415_, 4);
lean_inc(v_r_1418_);
lean_dec_ref_known(v_x_1415_, 5);
v___x_1419_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(v_init_1414_, v_l_1417_);
v___x_1420_ = lean_array_push(v___x_1419_, v_k_1416_);
v_init_1414_ = v___x_1420_;
v_x_1415_ = v_r_1418_;
goto _start;
}
else
{
return v_init_1414_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize(lean_object* v_targets_1422_, lean_object* v_forbidden_1423_, uint8_t v_ignoreLetDecls_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_Meta_mkGeneralizationForbiddenSet(v_targets_1422_, v_forbidden_1423_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1432_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1430_, 1);
v___x_1432_ = l_Lean_Meta_getFVarSetToGeneralize(v_targets_1422_, v_a_1431_, v_ignoreLetDecls_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_);
lean_dec(v_a_1431_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; lean_object* v___y_1435_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1433_);
lean_dec_ref_known(v___x_1432_, 1);
if (lean_obj_tag(v_a_1433_) == 0)
{
lean_object* v_size_1439_; 
v_size_1439_ = lean_ctor_get(v_a_1433_, 0);
lean_inc(v_size_1439_);
v___y_1435_ = v_size_1439_;
goto v___jp_1434_;
}
else
{
lean_object* v___x_1440_; 
v___x_1440_ = lean_unsigned_to_nat(0u);
v___y_1435_ = v___x_1440_;
goto v___jp_1434_;
}
v___jp_1434_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1436_ = lean_mk_empty_array_with_capacity(v___y_1435_);
lean_dec(v___y_1435_);
v___x_1437_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(v___x_1436_, v_a_1433_);
v___x_1438_ = l_Lean_Meta_sortFVarIds___redArg(v___x_1437_, v_a_1425_);
return v___x_1438_;
}
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
v_a_1441_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1432_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1432_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
v_a_1449_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1430_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1430_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize___boxed(lean_object* v_targets_1457_, lean_object* v_forbidden_1458_, lean_object* v_ignoreLetDecls_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1465_; lean_object* v_res_1466_; 
v_ignoreLetDecls_boxed_1465_ = lean_unbox(v_ignoreLetDecls_1459_);
v_res_1466_ = l_Lean_Meta_getFVarsToGeneralize(v_targets_1457_, v_forbidden_1458_, v_ignoreLetDecls_boxed_1465_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
lean_dec(v_a_1463_);
lean_dec_ref(v_a_1462_);
lean_dec(v_a_1461_);
lean_dec_ref(v_a_1460_);
lean_dec_ref(v_targets_1457_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0(lean_object* v_init_1467_, lean_object* v_t_1468_){
_start:
{
lean_object* v___x_1469_; 
v___x_1469_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(v_init_1467_, v_t_1468_);
return v___x_1469_;
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
