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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
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
uint8_t v___x_4_; uint8_t v___x_5_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
v___x_5_ = lean_bool_not(v___x_4_);
if (v___x_5_ == 0)
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
v___x_21_ = lean_st_ref_set(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
else
{
lean_object* v___x_26_; 
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v_e_1_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg___boxed(lean_object* v_e_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(v_e_27_, v___y_28_);
lean_dec(v___y_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(v_e_31_, v___y_33_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___boxed(lean_object* v_e_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2(v_e_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
lean_dec(v___y_40_);
lean_dec_ref(v___y_39_);
return v_res_44_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(lean_object* v_k_45_, lean_object* v_t_46_){
_start:
{
if (lean_obj_tag(v_t_46_) == 0)
{
lean_object* v_k_47_; lean_object* v_l_48_; lean_object* v_r_49_; uint8_t v___x_50_; 
v_k_47_ = lean_ctor_get(v_t_46_, 1);
v_l_48_ = lean_ctor_get(v_t_46_, 3);
v_r_49_ = lean_ctor_get(v_t_46_, 4);
v___x_50_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_45_, v_k_47_);
switch(v___x_50_)
{
case 0:
{
v_t_46_ = v_l_48_;
goto _start;
}
case 1:
{
uint8_t v___x_52_; 
v___x_52_ = 1;
return v___x_52_;
}
default: 
{
v_t_46_ = v_r_49_;
goto _start;
}
}
}
else
{
uint8_t v___x_54_; 
v___x_54_ = 0;
return v___x_54_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg___boxed(lean_object* v_k_55_, lean_object* v_t_56_){
_start:
{
uint8_t v_res_57_; lean_object* v_r_58_; 
v_res_57_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v_k_55_, v_t_56_);
lean_dec(v_t_56_);
lean_dec(v_k_55_);
v_r_58_ = lean_box(v_res_57_);
return v_r_58_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(lean_object* v_init_59_, lean_object* v_x_60_){
_start:
{
if (lean_obj_tag(v_x_60_) == 0)
{
lean_object* v_k_62_; lean_object* v_l_63_; lean_object* v_r_64_; lean_object* v___x_65_; lean_object* v_a_66_; lean_object* v_a_67_; lean_object* v_fst_68_; lean_object* v_snd_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_84_; 
v_k_62_ = lean_ctor_get(v_x_60_, 1);
lean_inc(v_k_62_);
v_l_63_ = lean_ctor_get(v_x_60_, 3);
lean_inc(v_l_63_);
v_r_64_ = lean_ctor_get(v_x_60_, 4);
lean_inc(v_r_64_);
lean_dec_ref_known(v_x_60_, 5);
v___x_65_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(v_init_59_, v_l_63_);
v_a_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_a_66_);
lean_dec_ref(v___x_65_);
v_a_67_ = lean_ctor_get(v_a_66_, 0);
lean_inc(v_a_67_);
lean_dec(v_a_66_);
v_fst_68_ = lean_ctor_get(v_a_67_, 0);
v_snd_69_ = lean_ctor_get(v_a_67_, 1);
v_isSharedCheck_84_ = !lean_is_exclusive(v_a_67_);
if (v_isSharedCheck_84_ == 0)
{
v___x_71_ = v_a_67_;
v_isShared_72_ = v_isSharedCheck_84_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_snd_69_);
lean_inc(v_fst_68_);
lean_dec(v_a_67_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_84_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
uint8_t v___x_73_; 
v___x_73_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v_k_62_, v_snd_69_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_77_; 
lean_inc(v_k_62_);
v___x_74_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_74_, 0, v_k_62_);
lean_ctor_set(v___x_74_, 1, v_fst_68_);
v___x_75_ = l_Lean_FVarIdSet_insert(v_snd_69_, v_k_62_);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 1, v___x_75_);
lean_ctor_set(v___x_71_, 0, v___x_74_);
v___x_77_ = v___x_71_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_74_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v___x_75_);
v___x_77_ = v_reuseFailAlloc_79_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
v_init_59_ = v___x_77_;
v_x_60_ = v_r_64_;
goto _start;
}
}
else
{
lean_object* v___x_81_; 
lean_dec(v_k_62_);
if (v_isShared_72_ == 0)
{
v___x_81_ = v___x_71_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_fst_68_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v_snd_69_);
v___x_81_ = v_reuseFailAlloc_83_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
v_init_59_ = v___x_81_;
v_x_60_ = v_r_64_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_85_, 0, v_init_59_);
v___x_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg___boxed(lean_object* v_init_87_, lean_object* v_x_88_, lean_object* v___y_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(v_init_87_, v_x_88_);
return v_res_90_;
}
}
static lean_object* _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = lean_box(0);
v___x_92_ = lean_unsigned_to_nat(16u);
v___x_93_ = lean_mk_array(v___x_92_, v___x_91_);
return v___x_93_;
}
}
static lean_object* _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0);
v___x_95_ = lean_unsigned_to_nat(0u);
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set(v___x_96_, 1, v___x_94_);
return v___x_96_;
}
}
static lean_object* _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_99_ = ((lean_object*)(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2));
v___x_100_ = lean_box(1);
v___x_101_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_102_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v___x_100_);
lean_ctor_set(v___x_102_, 2, v___x_99_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit(lean_object* v_fvarId_103_, lean_object* v_todo_104_, lean_object* v_s_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_a_112_; lean_object* v_s_x27_124_; lean_object* v___y_125_; lean_object* v___y_126_; lean_object* v___y_127_; lean_object* v___y_128_; lean_object* v___x_134_; 
v___x_134_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_103_, v_a_106_, v_a_108_, v_a_109_);
if (lean_obj_tag(v___x_134_) == 0)
{
lean_object* v_a_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v_a_138_; lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; lean_object* v___x_142_; 
v_a_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc(v_a_135_);
lean_dec_ref_known(v___x_134_, 1);
v___x_136_ = l_Lean_LocalDecl_type(v_a_135_);
v___x_137_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(v___x_136_, v_a_107_);
v_a_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_a_138_);
lean_dec_ref(v___x_137_);
v___x_139_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3);
v___x_140_ = l_Lean_collectFVars(v___x_139_, v_a_138_);
v___x_141_ = 0;
v___x_142_ = l_Lean_LocalDecl_value_x3f(v_a_135_, v___x_141_);
lean_dec(v_a_135_);
if (lean_obj_tag(v___x_142_) == 1)
{
lean_object* v_val_143_; lean_object* v___x_144_; lean_object* v_a_145_; lean_object* v___x_146_; 
v_val_143_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_val_143_);
lean_dec_ref_known(v___x_142_, 1);
v___x_144_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(v_val_143_, v_a_107_);
v_a_145_ = lean_ctor_get(v___x_144_, 0);
lean_inc(v_a_145_);
lean_dec_ref(v___x_144_);
v___x_146_ = l_Lean_collectFVars(v___x_140_, v_a_145_);
v_s_x27_124_ = v___x_146_;
v___y_125_ = v_a_106_;
v___y_126_ = v_a_107_;
v___y_127_ = v_a_108_;
v___y_128_ = v_a_109_;
goto v___jp_123_;
}
else
{
lean_dec(v___x_142_);
v_s_x27_124_ = v___x_140_;
v___y_125_ = v_a_106_;
v___y_126_ = v_a_107_;
v___y_127_ = v_a_108_;
v___y_128_ = v_a_109_;
goto v___jp_123_;
}
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
lean_dec(v_s_105_);
lean_dec(v_todo_104_);
v_a_147_ = lean_ctor_get(v___x_134_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_134_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_134_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
v___jp_111_:
{
lean_object* v_fst_113_; lean_object* v_snd_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_122_; 
v_fst_113_ = lean_ctor_get(v_a_112_, 0);
v_snd_114_ = lean_ctor_get(v_a_112_, 1);
v_isSharedCheck_122_ = !lean_is_exclusive(v_a_112_);
if (v_isSharedCheck_122_ == 0)
{
v___x_116_ = v_a_112_;
v_isShared_117_ = v_isSharedCheck_122_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_snd_114_);
lean_inc(v_fst_113_);
lean_dec(v_a_112_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_122_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_119_; 
if (v_isShared_117_ == 0)
{
v___x_119_ = v___x_116_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_fst_113_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_snd_114_);
v___x_119_ = v_reuseFailAlloc_121_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
lean_object* v___x_120_; 
v___x_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
return v___x_120_;
}
}
}
v___jp_123_:
{
lean_object* v_fvarSet_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v_a_132_; lean_object* v_a_133_; 
v_fvarSet_129_ = lean_ctor_get(v_s_x27_124_, 1);
lean_inc(v_fvarSet_129_);
lean_dec_ref(v_s_x27_124_);
v___x_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_130_, 0, v_todo_104_);
lean_ctor_set(v___x_130_, 1, v_s_105_);
v___x_131_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(v___x_130_, v_fvarSet_129_);
v_a_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_a_132_);
lean_dec_ref(v___x_131_);
v_a_133_ = lean_ctor_get(v_a_132_, 0);
lean_inc(v_a_133_);
lean_dec(v_a_132_);
v_a_112_ = v_a_133_;
goto v___jp_111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___boxed(lean_object* v_fvarId_155_, lean_object* v_todo_156_, lean_object* v_s_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit(v_fvarId_155_, v_todo_156_, v_s_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_);
lean_dec(v_a_161_);
lean_dec_ref(v_a_160_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
return v_res_163_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0(lean_object* v_00_u03b2_164_, lean_object* v_k_165_, lean_object* v_t_166_){
_start:
{
uint8_t v___x_167_; 
v___x_167_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v_k_165_, v_t_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___boxed(lean_object* v_00_u03b2_168_, lean_object* v_k_169_, lean_object* v_t_170_){
_start:
{
uint8_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0(v_00_u03b2_168_, v_k_169_, v_t_170_);
lean_dec(v_t_170_);
lean_dec(v_k_169_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1(lean_object* v_init_173_, lean_object* v_x_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(v_init_173_, v_x_174_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___boxed(lean_object* v_init_181_, lean_object* v_x_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1(v_init_181_, v_x_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop(lean_object* v_todo_189_, lean_object* v_s_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
if (lean_obj_tag(v_todo_189_) == 0)
{
lean_object* v___x_196_; 
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v_s_190_);
return v___x_196_;
}
else
{
lean_object* v_head_197_; lean_object* v_tail_198_; uint8_t v___x_199_; 
v_head_197_ = lean_ctor_get(v_todo_189_, 0);
lean_inc(v_head_197_);
v_tail_198_ = lean_ctor_get(v_todo_189_, 1);
lean_inc(v_tail_198_);
lean_dec_ref_known(v_todo_189_, 2);
v___x_199_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v_head_197_, v_s_190_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; 
lean_inc(v_head_197_);
v___x_200_ = l_Lean_FVarIdSet_insert(v_s_190_, v_head_197_);
v___x_201_ = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit(v_head_197_, v_tail_198_, v___x_200_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v_a_202_; lean_object* v_fst_203_; lean_object* v_snd_204_; 
v_a_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_a_202_);
lean_dec_ref_known(v___x_201_, 1);
v_fst_203_ = lean_ctor_get(v_a_202_, 0);
lean_inc(v_fst_203_);
v_snd_204_ = lean_ctor_get(v_a_202_, 1);
lean_inc(v_snd_204_);
lean_dec(v_a_202_);
v_todo_189_ = v_fst_203_;
v_s_190_ = v_snd_204_;
goto _start;
}
else
{
lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_213_; 
v_a_206_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_213_ == 0)
{
v___x_208_ = v___x_201_;
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_201_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_209_ == 0)
{
v___x_211_ = v___x_208_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_a_206_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
else
{
lean_dec(v_head_197_);
v_todo_189_ = v_tail_198_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop___boxed(lean_object* v_todo_215_, lean_object* v_s_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop(v_todo_215_, v_s_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_);
lean_dec(v_a_220_);
lean_dec_ref(v_a_219_);
lean_dec(v_a_218_);
lean_dec_ref(v_a_217_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0(lean_object* v_as_223_, size_t v_sz_224_, size_t v_i_225_, lean_object* v_b_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v_a_233_; uint8_t v___x_237_; 
v___x_237_ = lean_usize_dec_lt(v_i_225_, v_sz_224_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; 
v___x_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_238_, 0, v_b_226_);
return v___x_238_;
}
else
{
lean_object* v_fst_239_; lean_object* v_snd_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_275_; 
v_fst_239_ = lean_ctor_get(v_b_226_, 0);
v_snd_240_ = lean_ctor_get(v_b_226_, 1);
v_isSharedCheck_275_ = !lean_is_exclusive(v_b_226_);
if (v_isSharedCheck_275_ == 0)
{
v___x_242_ = v_b_226_;
v_isShared_243_ = v_isSharedCheck_275_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_snd_240_);
lean_inc(v_fst_239_);
lean_dec(v_b_226_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_275_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v_a_244_; uint8_t v___x_245_; 
v_a_244_ = lean_array_uget_borrowed(v_as_223_, v_i_225_);
v___x_245_ = l_Lean_Expr_isFVar(v_a_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; 
lean_inc(v___y_230_);
lean_inc_ref(v___y_229_);
lean_inc(v___y_228_);
lean_inc_ref(v___y_227_);
lean_inc(v_a_244_);
v___x_246_ = lean_infer_type(v_a_244_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v_a_247_; lean_object* v___x_248_; 
v_a_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_a_247_);
lean_dec_ref_known(v___x_246_, 1);
v___x_248_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(v_a_247_, v___y_228_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v___x_250_; lean_object* v___x_252_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_a_249_);
lean_dec_ref_known(v___x_248_, 1);
v___x_250_ = l_Lean_collectFVars(v_fst_239_, v_a_249_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 0, v___x_250_);
v___x_252_ = v___x_242_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v_snd_240_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
v_a_233_ = v___x_252_;
goto v___jp_232_;
}
}
else
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
lean_del_object(v___x_242_);
lean_dec(v_snd_240_);
lean_dec(v_fst_239_);
v_a_254_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_261_ == 0)
{
v___x_256_ = v___x_248_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_248_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_a_254_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
else
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
lean_del_object(v___x_242_);
lean_dec(v_snd_240_);
lean_dec(v_fst_239_);
v_a_262_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v___x_246_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_246_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_262_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
else
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_270_ = l_Lean_Expr_fvarId_x21(v_a_244_);
v___x_271_ = lean_array_push(v_snd_240_, v___x_270_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v___x_271_);
v___x_273_ = v___x_242_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_fst_239_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v___x_271_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
v_a_233_ = v___x_273_;
goto v___jp_232_;
}
}
}
}
v___jp_232_:
{
size_t v___x_234_; size_t v___x_235_; 
v___x_234_ = ((size_t)1ULL);
v___x_235_ = lean_usize_add(v_i_225_, v___x_234_);
v_i_225_ = v___x_235_;
v_b_226_ = v_a_233_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0___boxed(lean_object* v_as_276_, lean_object* v_sz_277_, lean_object* v_i_278_, lean_object* v_b_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
size_t v_sz_boxed_285_; size_t v_i_boxed_286_; lean_object* v_res_287_; 
v_sz_boxed_285_ = lean_unbox_usize(v_sz_277_);
lean_dec(v_sz_277_);
v_i_boxed_286_ = lean_unbox_usize(v_i_278_);
lean_dec(v_i_278_);
v_res_287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0(v_as_276_, v_sz_boxed_285_, v_i_boxed_286_, v_b_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec_ref(v_as_276_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet(lean_object* v_targets_288_, lean_object* v_forbidden_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v___x_295_; lean_object* v_todo_296_; lean_object* v_s_297_; lean_object* v___x_298_; size_t v_sz_299_; size_t v___x_300_; lean_object* v___x_301_; 
v___x_295_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v_todo_296_ = ((lean_object*)(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2));
v_s_297_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_s_297_, 0, v___x_295_);
lean_ctor_set(v_s_297_, 1, v_forbidden_289_);
lean_ctor_set(v_s_297_, 2, v_todo_296_);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v_s_297_);
lean_ctor_set(v___x_298_, 1, v_todo_296_);
v_sz_299_ = lean_array_size(v_targets_288_);
v___x_300_ = ((size_t)0ULL);
v___x_301_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0(v_targets_288_, v_sz_299_, v___x_300_, v___x_298_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; lean_object* v_fst_303_; lean_object* v_snd_304_; lean_object* v_fvarSet_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v_a_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_a_302_);
lean_dec_ref_known(v___x_301_, 1);
v_fst_303_ = lean_ctor_get(v_a_302_, 0);
lean_inc(v_fst_303_);
v_snd_304_ = lean_ctor_get(v_a_302_, 1);
lean_inc(v_snd_304_);
lean_dec(v_a_302_);
v_fvarSet_305_ = lean_ctor_get(v_fst_303_, 1);
lean_inc(v_fvarSet_305_);
lean_dec(v_fst_303_);
v___x_306_ = lean_array_to_list(v_snd_304_);
v___x_307_ = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop(v___x_306_, v_fvarSet_305_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
return v___x_307_;
}
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
v_a_308_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_301_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_301_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet___boxed(lean_object* v_targets_316_, lean_object* v_forbidden_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_Meta_mkGeneralizationForbiddenSet(v_targets_316_, v_forbidden_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_);
lean_dec(v_a_321_);
lean_dec_ref(v_a_320_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
lean_dec_ref(v_targets_316_);
return v_res_323_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1(uint8_t v___y_324_, lean_object* v_x_325_){
_start:
{
return v___y_324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed(lean_object* v___y_326_, lean_object* v_x_327_){
_start:
{
uint8_t v___y_10189__boxed_328_; uint8_t v_res_329_; lean_object* v_r_330_; 
v___y_10189__boxed_328_ = lean_unbox(v___y_326_);
v_res_329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1(v___y_10189__boxed_328_, v_x_327_);
lean_dec(v_x_327_);
v_r_330_ = lean_box(v_res_329_);
return v_r_330_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0(lean_object* v_fst_331_, lean_object* v_x_332_){
_start:
{
uint8_t v___x_333_; 
v___x_333_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v_x_332_, v_fst_331_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed(lean_object* v_fst_334_, lean_object* v_x_335_){
_start:
{
uint8_t v_res_336_; lean_object* v_r_337_; 
v_res_336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0(v_fst_334_, v_x_335_);
lean_dec(v_x_335_);
lean_dec(v_fst_334_);
v_r_337_ = lean_box(v_res_336_);
return v_r_337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(uint8_t v_ignoreLetDecls_338_, lean_object* v_forbidden_339_, lean_object* v_as_340_, size_t v_sz_341_, size_t v_i_342_, lean_object* v_b_343_, lean_object* v___y_344_){
_start:
{
uint8_t v___x_346_; 
v___x_346_ = lean_usize_dec_lt(v_i_342_, v_sz_341_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; 
v___x_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_347_, 0, v_b_343_);
return v___x_347_;
}
else
{
lean_object* v_snd_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_531_; 
v_snd_348_ = lean_ctor_get(v_b_343_, 1);
v_isSharedCheck_531_ = !lean_is_exclusive(v_b_343_);
if (v_isSharedCheck_531_ == 0)
{
lean_object* v_unused_532_; 
v_unused_532_ = lean_ctor_get(v_b_343_, 0);
lean_dec(v_unused_532_);
v___x_350_ = v_b_343_;
v_isShared_351_ = v_isSharedCheck_531_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_snd_348_);
lean_dec(v_b_343_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_531_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_352_; lean_object* v_a_354_; lean_object* v_a_361_; 
v___x_352_ = lean_box(0);
v_a_361_ = lean_array_uget_borrowed(v_as_340_, v_i_342_);
if (lean_obj_tag(v_a_361_) == 0)
{
v_a_354_ = v_snd_348_;
goto v___jp_353_;
}
else
{
lean_object* v_val_362_; lean_object* v_fst_363_; lean_object* v_snd_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_530_; 
v_val_362_ = lean_ctor_get(v_a_361_, 0);
v_fst_363_ = lean_ctor_get(v_snd_348_, 0);
v_snd_364_ = lean_ctor_get(v_snd_348_, 1);
v_isSharedCheck_530_ = !lean_is_exclusive(v_snd_348_);
if (v_isSharedCheck_530_ == 0)
{
v___x_366_ = v_snd_348_;
v_isShared_367_ = v_isSharedCheck_530_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_snd_364_);
lean_inc(v_fst_363_);
lean_dec(v_snd_348_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_530_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_372_; uint8_t v_a_374_; uint8_t v_fst_380_; lean_object* v_mctx_381_; uint8_t v_fst_397_; lean_object* v_snd_398_; uint8_t v_fst_415_; lean_object* v_mctx_416_; uint8_t v___x_431_; 
v___x_372_ = l_Lean_LocalDecl_fvarId(v_val_362_);
v___x_431_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v___x_372_, v_forbidden_339_);
if (v___x_431_ == 0)
{
lean_object* v___f_432_; lean_object* v___y_434_; uint8_t v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; uint8_t v___y_439_; uint8_t v___y_446_; lean_object* v___y_447_; lean_object* v___y_448_; lean_object* v___y_449_; uint8_t v___y_450_; lean_object* v___y_456_; lean_object* v___y_457_; uint8_t v_fst_458_; lean_object* v_snd_459_; uint8_t v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_469_; uint8_t v___y_470_; lean_object* v___y_479_; uint8_t v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; uint8_t v___y_484_; uint8_t v___y_491_; uint8_t v___y_524_; uint8_t v___x_526_; 
lean_inc(v_fst_363_);
v___f_432_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_432_, 0, v_fst_363_);
v___x_526_ = l_Lean_LocalDecl_isAuxDecl(v_val_362_);
if (v___x_526_ == 0)
{
uint8_t v___x_527_; uint8_t v___x_528_; 
v___x_527_ = l_Lean_LocalDecl_binderInfo(v_val_362_);
v___x_528_ = l_Lean_BinderInfo_isInstImplicit(v___x_527_);
v___y_524_ = v___x_528_;
goto v___jp_523_;
}
else
{
v___y_524_ = v___x_526_;
goto v___jp_523_;
}
v___jp_433_:
{
if (v___y_439_ == 0)
{
lean_object* v___x_440_; lean_object* v_snd_441_; lean_object* v_fst_442_; lean_object* v_mctx_443_; uint8_t v___x_444_; 
lean_dec_ref(v___y_434_);
v___x_440_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_432_, v___y_438_, v___y_437_, v___y_436_);
v_snd_441_ = lean_ctor_get(v___x_440_, 1);
lean_inc(v_snd_441_);
v_fst_442_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_fst_442_);
lean_dec_ref(v___x_440_);
v_mctx_443_ = lean_ctor_get(v_snd_441_, 1);
lean_inc_ref(v_mctx_443_);
lean_dec(v_snd_441_);
v___x_444_ = lean_unbox(v_fst_442_);
lean_dec(v_fst_442_);
v_fst_415_ = v___x_444_;
v_mctx_416_ = v_mctx_443_;
goto v___jp_414_;
}
else
{
lean_dec_ref(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec_ref(v___f_432_);
v_fst_415_ = v___y_435_;
v_mctx_416_ = v___y_434_;
goto v___jp_414_;
}
}
v___jp_445_:
{
if (v___y_450_ == 0)
{
lean_object* v___x_451_; lean_object* v_fst_452_; lean_object* v_snd_453_; uint8_t v___x_454_; 
v___x_451_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_432_, v___y_449_, v___y_448_, v___y_447_);
v_fst_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_fst_452_);
v_snd_453_ = lean_ctor_get(v___x_451_, 1);
lean_inc(v_snd_453_);
lean_dec_ref(v___x_451_);
v___x_454_ = lean_unbox(v_fst_452_);
lean_dec(v_fst_452_);
v_fst_397_ = v___x_454_;
v_snd_398_ = v_snd_453_;
goto v___jp_396_;
}
else
{
lean_dec_ref(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec_ref(v___f_432_);
v_fst_397_ = v___y_446_;
v_snd_398_ = v___y_447_;
goto v___jp_396_;
}
}
v___jp_455_:
{
uint8_t v___x_460_; uint8_t v___x_461_; 
v___x_460_ = l_Lean_Expr_hasFVar(v___y_457_);
v___x_461_ = lean_bool_not(v___x_460_);
if (v___x_461_ == 0)
{
v___y_446_ = v_fst_458_;
v___y_447_ = v_snd_459_;
v___y_448_ = v___y_457_;
v___y_449_ = v___y_456_;
v___y_450_ = v___x_461_;
goto v___jp_445_;
}
else
{
uint8_t v___x_462_; uint8_t v___x_463_; 
v___x_462_ = l_Lean_Expr_hasMVar(v___y_457_);
v___x_463_ = lean_bool_not(v___x_462_);
v___y_446_ = v_fst_458_;
v___y_447_ = v_snd_459_;
v___y_448_ = v___y_457_;
v___y_449_ = v___y_456_;
v___y_450_ = v___x_463_;
goto v___jp_445_;
}
}
v___jp_464_:
{
if (v___y_470_ == 0)
{
lean_object* v___x_471_; lean_object* v_fst_472_; uint8_t v___x_473_; 
lean_inc_ref(v___y_468_);
lean_inc_ref(v___f_432_);
v___x_471_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_432_, v___y_468_, v___y_466_, v___y_469_);
v_fst_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_fst_472_);
v___x_473_ = lean_unbox(v_fst_472_);
if (v___x_473_ == 0)
{
lean_object* v_snd_474_; uint8_t v___x_475_; 
v_snd_474_ = lean_ctor_get(v___x_471_, 1);
lean_inc(v_snd_474_);
lean_dec_ref(v___x_471_);
v___x_475_ = lean_unbox(v_fst_472_);
lean_dec(v_fst_472_);
v___y_456_ = v___y_468_;
v___y_457_ = v___y_467_;
v_fst_458_ = v___x_475_;
v_snd_459_ = v_snd_474_;
goto v___jp_455_;
}
else
{
lean_object* v_snd_476_; uint8_t v___x_477_; 
lean_dec_ref(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec_ref(v___f_432_);
v_snd_476_ = lean_ctor_get(v___x_471_, 1);
lean_inc(v_snd_476_);
lean_dec_ref(v___x_471_);
v___x_477_ = lean_unbox(v_fst_472_);
lean_dec(v_fst_472_);
v_fst_397_ = v___x_477_;
v_snd_398_ = v_snd_476_;
goto v___jp_396_;
}
}
else
{
lean_dec_ref(v___y_466_);
v___y_456_ = v___y_468_;
v___y_457_ = v___y_467_;
v_fst_458_ = v___y_465_;
v_snd_459_ = v___y_469_;
goto v___jp_455_;
}
}
v___jp_478_:
{
if (v___y_484_ == 0)
{
lean_object* v___x_485_; lean_object* v_snd_486_; lean_object* v_fst_487_; lean_object* v_mctx_488_; uint8_t v___x_489_; 
lean_dec_ref(v___y_483_);
v___x_485_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_432_, v___y_482_, v___y_481_, v___y_479_);
v_snd_486_ = lean_ctor_get(v___x_485_, 1);
lean_inc(v_snd_486_);
v_fst_487_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_fst_487_);
lean_dec_ref(v___x_485_);
v_mctx_488_ = lean_ctor_get(v_snd_486_, 1);
lean_inc_ref(v_mctx_488_);
lean_dec(v_snd_486_);
v___x_489_ = lean_unbox(v_fst_487_);
lean_dec(v_fst_487_);
v_fst_380_ = v___x_489_;
v_mctx_381_ = v_mctx_488_;
goto v___jp_379_;
}
else
{
lean_dec_ref(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec_ref(v___y_479_);
lean_dec_ref(v___f_432_);
v_fst_380_ = v___y_480_;
v_mctx_381_ = v___y_483_;
goto v___jp_379_;
}
}
v___jp_490_:
{
lean_object* v___x_492_; lean_object* v___f_493_; 
v___x_492_ = lean_box(v___y_491_);
v___f_493_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(v___f_493_, 0, v___x_492_);
if (lean_obj_tag(v_val_362_) == 0)
{
lean_object* v_type_494_; lean_object* v___x_495_; lean_object* v_mctx_496_; lean_object* v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; uint8_t v___x_500_; 
v_type_494_ = lean_ctor_get(v_val_362_, 3);
v___x_495_ = lean_st_ref_get(v___y_344_);
v_mctx_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc_ref_n(v_mctx_496_, 2);
lean_dec(v___x_495_);
v___x_497_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
lean_ctor_set(v___x_498_, 1, v_mctx_496_);
v___x_499_ = l_Lean_Expr_hasFVar(v_type_494_);
v___x_500_ = lean_bool_not(v___x_499_);
if (v___x_500_ == 0)
{
lean_inc_ref(v_type_494_);
v___y_434_ = v_mctx_496_;
v___y_435_ = v___y_491_;
v___y_436_ = v___x_498_;
v___y_437_ = v_type_494_;
v___y_438_ = v___f_493_;
v___y_439_ = v___x_500_;
goto v___jp_433_;
}
else
{
uint8_t v___x_501_; uint8_t v___x_502_; 
v___x_501_ = l_Lean_Expr_hasMVar(v_type_494_);
v___x_502_ = lean_bool_not(v___x_501_);
lean_inc_ref(v_type_494_);
v___y_434_ = v_mctx_496_;
v___y_435_ = v___y_491_;
v___y_436_ = v___x_498_;
v___y_437_ = v_type_494_;
v___y_438_ = v___f_493_;
v___y_439_ = v___x_502_;
goto v___jp_433_;
}
}
else
{
uint8_t v_nondep_503_; 
v_nondep_503_ = lean_ctor_get_uint8(v_val_362_, sizeof(void*)*5);
if (v_nondep_503_ == 0)
{
lean_object* v_type_504_; lean_object* v_value_505_; lean_object* v___x_506_; lean_object* v_mctx_507_; lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; uint8_t v___x_511_; 
v_type_504_ = lean_ctor_get(v_val_362_, 3);
v_value_505_ = lean_ctor_get(v_val_362_, 4);
v___x_506_ = lean_st_ref_get(v___y_344_);
v_mctx_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc_ref(v_mctx_507_);
lean_dec(v___x_506_);
v___x_508_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
lean_ctor_set(v___x_509_, 1, v_mctx_507_);
v___x_510_ = l_Lean_Expr_hasFVar(v_type_504_);
v___x_511_ = lean_bool_not(v___x_510_);
if (v___x_511_ == 0)
{
lean_inc_ref(v_value_505_);
lean_inc_ref(v_type_504_);
v___y_465_ = v_nondep_503_;
v___y_466_ = v_type_504_;
v___y_467_ = v_value_505_;
v___y_468_ = v___f_493_;
v___y_469_ = v___x_509_;
v___y_470_ = v___x_511_;
goto v___jp_464_;
}
else
{
uint8_t v___x_512_; uint8_t v___x_513_; 
v___x_512_ = l_Lean_Expr_hasMVar(v_type_504_);
v___x_513_ = lean_bool_not(v___x_512_);
lean_inc_ref(v_value_505_);
lean_inc_ref(v_type_504_);
v___y_465_ = v_nondep_503_;
v___y_466_ = v_type_504_;
v___y_467_ = v_value_505_;
v___y_468_ = v___f_493_;
v___y_469_ = v___x_509_;
v___y_470_ = v___x_513_;
goto v___jp_464_;
}
}
else
{
lean_object* v_type_514_; lean_object* v___x_515_; lean_object* v_mctx_516_; lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; uint8_t v___x_520_; 
v_type_514_ = lean_ctor_get(v_val_362_, 3);
v___x_515_ = lean_st_ref_get(v___y_344_);
v_mctx_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc_ref_n(v_mctx_516_, 2);
lean_dec(v___x_515_);
v___x_517_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
lean_ctor_set(v___x_518_, 1, v_mctx_516_);
v___x_519_ = l_Lean_Expr_hasFVar(v_type_514_);
v___x_520_ = lean_bool_not(v___x_519_);
if (v___x_520_ == 0)
{
lean_inc_ref(v_type_514_);
v___y_479_ = v___x_518_;
v___y_480_ = v___y_491_;
v___y_481_ = v_type_514_;
v___y_482_ = v___f_493_;
v___y_483_ = v_mctx_516_;
v___y_484_ = v___x_520_;
goto v___jp_478_;
}
else
{
uint8_t v___x_521_; uint8_t v___x_522_; 
v___x_521_ = l_Lean_Expr_hasMVar(v_type_514_);
v___x_522_ = lean_bool_not(v___x_521_);
lean_inc_ref(v_type_514_);
v___y_479_ = v___x_518_;
v___y_480_ = v___y_491_;
v___y_481_ = v_type_514_;
v___y_482_ = v___f_493_;
v___y_483_ = v_mctx_516_;
v___y_484_ = v___x_522_;
goto v___jp_478_;
}
}
}
}
v___jp_523_:
{
if (v___y_524_ == 0)
{
if (v_ignoreLetDecls_338_ == 0)
{
lean_del_object(v___x_366_);
v___y_491_ = v_ignoreLetDecls_338_;
goto v___jp_490_;
}
else
{
uint8_t v___x_525_; 
v___x_525_ = l_Lean_LocalDecl_isLet(v_val_362_, v___y_524_);
if (v___x_525_ == 0)
{
lean_del_object(v___x_366_);
v___y_491_ = v___x_525_;
goto v___jp_490_;
}
else
{
lean_dec_ref(v___f_432_);
lean_dec(v___x_372_);
goto v___jp_368_;
}
}
}
else
{
lean_dec_ref(v___f_432_);
lean_dec(v___x_372_);
goto v___jp_368_;
}
}
}
else
{
lean_object* v___x_529_; 
lean_dec(v___x_372_);
lean_del_object(v___x_366_);
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v_fst_363_);
lean_ctor_set(v___x_529_, 1, v_snd_364_);
v_a_354_ = v___x_529_;
goto v___jp_353_;
}
v___jp_368_:
{
lean_object* v___x_370_; 
if (v_isShared_367_ == 0)
{
v___x_370_ = v___x_366_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_fst_363_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_snd_364_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
v_a_354_ = v___x_370_;
goto v___jp_353_;
}
}
v___jp_373_:
{
if (v_a_374_ == 0)
{
lean_object* v___x_375_; 
lean_dec(v___x_372_);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v_fst_363_);
lean_ctor_set(v___x_375_, 1, v_snd_364_);
v_a_354_ = v___x_375_;
goto v___jp_353_;
}
else
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
lean_inc(v___x_372_);
v___x_376_ = l_Lean_FVarIdSet_insert(v_snd_364_, v___x_372_);
v___x_377_ = l_Lean_FVarIdSet_insert(v_fst_363_, v___x_372_);
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
lean_ctor_set(v___x_378_, 1, v___x_376_);
v_a_354_ = v___x_378_;
goto v___jp_353_;
}
}
v___jp_379_:
{
lean_object* v___x_382_; lean_object* v_cache_383_; lean_object* v_zetaDeltaFVarIds_384_; lean_object* v_postponed_385_; lean_object* v_diag_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_394_; 
v___x_382_ = lean_st_ref_take(v___y_344_);
v_cache_383_ = lean_ctor_get(v___x_382_, 1);
v_zetaDeltaFVarIds_384_ = lean_ctor_get(v___x_382_, 2);
v_postponed_385_ = lean_ctor_get(v___x_382_, 3);
v_diag_386_ = lean_ctor_get(v___x_382_, 4);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_394_ == 0)
{
lean_object* v_unused_395_; 
v_unused_395_ = lean_ctor_get(v___x_382_, 0);
lean_dec(v_unused_395_);
v___x_388_ = v___x_382_;
v_isShared_389_ = v_isSharedCheck_394_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_diag_386_);
lean_inc(v_postponed_385_);
lean_inc(v_zetaDeltaFVarIds_384_);
lean_inc(v_cache_383_);
lean_dec(v___x_382_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_394_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v_mctx_381_);
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_mctx_381_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v_cache_383_);
lean_ctor_set(v_reuseFailAlloc_393_, 2, v_zetaDeltaFVarIds_384_);
lean_ctor_set(v_reuseFailAlloc_393_, 3, v_postponed_385_);
lean_ctor_set(v_reuseFailAlloc_393_, 4, v_diag_386_);
v___x_391_ = v_reuseFailAlloc_393_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v___x_392_; 
v___x_392_ = lean_st_ref_set(v___y_344_, v___x_391_);
v_a_374_ = v_fst_380_;
goto v___jp_373_;
}
}
}
v___jp_396_:
{
lean_object* v_mctx_399_; lean_object* v___x_400_; lean_object* v_cache_401_; lean_object* v_zetaDeltaFVarIds_402_; lean_object* v_postponed_403_; lean_object* v_diag_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_412_; 
v_mctx_399_ = lean_ctor_get(v_snd_398_, 1);
lean_inc_ref(v_mctx_399_);
lean_dec_ref(v_snd_398_);
v___x_400_ = lean_st_ref_take(v___y_344_);
v_cache_401_ = lean_ctor_get(v___x_400_, 1);
v_zetaDeltaFVarIds_402_ = lean_ctor_get(v___x_400_, 2);
v_postponed_403_ = lean_ctor_get(v___x_400_, 3);
v_diag_404_ = lean_ctor_get(v___x_400_, 4);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_412_ == 0)
{
lean_object* v_unused_413_; 
v_unused_413_ = lean_ctor_get(v___x_400_, 0);
lean_dec(v_unused_413_);
v___x_406_ = v___x_400_;
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_diag_404_);
lean_inc(v_postponed_403_);
lean_inc(v_zetaDeltaFVarIds_402_);
lean_inc(v_cache_401_);
lean_dec(v___x_400_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_409_; 
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v_mctx_399_);
v___x_409_ = v___x_406_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_mctx_399_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_cache_401_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v_zetaDeltaFVarIds_402_);
lean_ctor_set(v_reuseFailAlloc_411_, 3, v_postponed_403_);
lean_ctor_set(v_reuseFailAlloc_411_, 4, v_diag_404_);
v___x_409_ = v_reuseFailAlloc_411_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
lean_object* v___x_410_; 
v___x_410_ = lean_st_ref_set(v___y_344_, v___x_409_);
v_a_374_ = v_fst_397_;
goto v___jp_373_;
}
}
}
v___jp_414_:
{
lean_object* v___x_417_; lean_object* v_cache_418_; lean_object* v_zetaDeltaFVarIds_419_; lean_object* v_postponed_420_; lean_object* v_diag_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_429_; 
v___x_417_ = lean_st_ref_take(v___y_344_);
v_cache_418_ = lean_ctor_get(v___x_417_, 1);
v_zetaDeltaFVarIds_419_ = lean_ctor_get(v___x_417_, 2);
v_postponed_420_ = lean_ctor_get(v___x_417_, 3);
v_diag_421_ = lean_ctor_get(v___x_417_, 4);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_429_ == 0)
{
lean_object* v_unused_430_; 
v_unused_430_ = lean_ctor_get(v___x_417_, 0);
lean_dec(v_unused_430_);
v___x_423_ = v___x_417_;
v_isShared_424_ = v_isSharedCheck_429_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_diag_421_);
lean_inc(v_postponed_420_);
lean_inc(v_zetaDeltaFVarIds_419_);
lean_inc(v_cache_418_);
lean_dec(v___x_417_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_429_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v_mctx_416_);
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_mctx_416_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_cache_418_);
lean_ctor_set(v_reuseFailAlloc_428_, 2, v_zetaDeltaFVarIds_419_);
lean_ctor_set(v_reuseFailAlloc_428_, 3, v_postponed_420_);
lean_ctor_set(v_reuseFailAlloc_428_, 4, v_diag_421_);
v___x_426_ = v_reuseFailAlloc_428_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_427_; 
v___x_427_ = lean_st_ref_set(v___y_344_, v___x_426_);
v_a_374_ = v_fst_415_;
goto v___jp_373_;
}
}
}
}
}
v___jp_353_:
{
lean_object* v___x_356_; 
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 1, v_a_354_);
lean_ctor_set(v___x_350_, 0, v___x_352_);
v___x_356_ = v___x_350_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_352_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_a_354_);
v___x_356_ = v_reuseFailAlloc_360_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
size_t v___x_357_; size_t v___x_358_; 
v___x_357_ = ((size_t)1ULL);
v___x_358_ = lean_usize_add(v_i_342_, v___x_357_);
v_i_342_ = v___x_358_;
v_b_343_ = v___x_356_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ignoreLetDecls_533_, lean_object* v_forbidden_534_, lean_object* v_as_535_, lean_object* v_sz_536_, lean_object* v_i_537_, lean_object* v_b_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_541_; size_t v_sz_boxed_542_; size_t v_i_boxed_543_; lean_object* v_res_544_; 
v_ignoreLetDecls_boxed_541_ = lean_unbox(v_ignoreLetDecls_533_);
v_sz_boxed_542_ = lean_unbox_usize(v_sz_536_);
lean_dec(v_sz_536_);
v_i_boxed_543_ = lean_unbox_usize(v_i_537_);
lean_dec(v_i_537_);
v_res_544_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(v_ignoreLetDecls_boxed_541_, v_forbidden_534_, v_as_535_, v_sz_boxed_542_, v_i_boxed_543_, v_b_538_, v___y_539_);
lean_dec(v___y_539_);
lean_dec_ref(v_as_535_);
lean_dec(v_forbidden_534_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1(uint8_t v_ignoreLetDecls_545_, lean_object* v_forbidden_546_, lean_object* v_as_547_, size_t v_sz_548_, size_t v_i_549_, lean_object* v_b_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
uint8_t v___x_556_; 
v___x_556_ = lean_usize_dec_lt(v_i_549_, v_sz_548_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; 
v___x_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_557_, 0, v_b_550_);
return v___x_557_;
}
else
{
lean_object* v_snd_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_741_; 
v_snd_558_ = lean_ctor_get(v_b_550_, 1);
v_isSharedCheck_741_ = !lean_is_exclusive(v_b_550_);
if (v_isSharedCheck_741_ == 0)
{
lean_object* v_unused_742_; 
v_unused_742_ = lean_ctor_get(v_b_550_, 0);
lean_dec(v_unused_742_);
v___x_560_ = v_b_550_;
v_isShared_561_ = v_isSharedCheck_741_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_snd_558_);
lean_dec(v_b_550_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_741_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_562_; lean_object* v_a_564_; lean_object* v_a_571_; 
v___x_562_ = lean_box(0);
v_a_571_ = lean_array_uget_borrowed(v_as_547_, v_i_549_);
if (lean_obj_tag(v_a_571_) == 0)
{
v_a_564_ = v_snd_558_;
goto v___jp_563_;
}
else
{
lean_object* v_val_572_; lean_object* v_fst_573_; lean_object* v_snd_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_740_; 
v_val_572_ = lean_ctor_get(v_a_571_, 0);
v_fst_573_ = lean_ctor_get(v_snd_558_, 0);
v_snd_574_ = lean_ctor_get(v_snd_558_, 1);
v_isSharedCheck_740_ = !lean_is_exclusive(v_snd_558_);
if (v_isSharedCheck_740_ == 0)
{
v___x_576_ = v_snd_558_;
v_isShared_577_ = v_isSharedCheck_740_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_snd_574_);
lean_inc(v_fst_573_);
lean_dec(v_snd_558_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_740_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_582_; uint8_t v_a_584_; uint8_t v_fst_590_; lean_object* v_mctx_591_; uint8_t v_fst_607_; lean_object* v_snd_608_; uint8_t v_fst_625_; lean_object* v_mctx_626_; uint8_t v___x_641_; 
v___x_582_ = l_Lean_LocalDecl_fvarId(v_val_572_);
v___x_641_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v___x_582_, v_forbidden_546_);
if (v___x_641_ == 0)
{
lean_object* v___f_642_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; uint8_t v___y_647_; lean_object* v___y_648_; uint8_t v___y_649_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; uint8_t v___y_659_; uint8_t v___y_660_; lean_object* v___y_666_; lean_object* v___y_667_; uint8_t v_fst_668_; lean_object* v_snd_669_; lean_object* v___y_675_; lean_object* v___y_676_; uint8_t v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; uint8_t v___y_680_; lean_object* v___y_689_; lean_object* v___y_690_; uint8_t v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; uint8_t v___y_694_; uint8_t v___y_701_; uint8_t v___y_734_; uint8_t v___x_736_; 
lean_inc(v_fst_573_);
v___f_642_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_642_, 0, v_fst_573_);
v___x_736_ = l_Lean_LocalDecl_isAuxDecl(v_val_572_);
if (v___x_736_ == 0)
{
uint8_t v___x_737_; uint8_t v___x_738_; 
v___x_737_ = l_Lean_LocalDecl_binderInfo(v_val_572_);
v___x_738_ = l_Lean_BinderInfo_isInstImplicit(v___x_737_);
v___y_734_ = v___x_738_;
goto v___jp_733_;
}
else
{
v___y_734_ = v___x_736_;
goto v___jp_733_;
}
v___jp_643_:
{
if (v___y_649_ == 0)
{
lean_object* v___x_650_; lean_object* v_snd_651_; lean_object* v_fst_652_; lean_object* v_mctx_653_; uint8_t v___x_654_; 
lean_dec_ref(v___y_644_);
v___x_650_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_642_, v___y_648_, v___y_646_, v___y_645_);
v_snd_651_ = lean_ctor_get(v___x_650_, 1);
lean_inc(v_snd_651_);
v_fst_652_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_fst_652_);
lean_dec_ref(v___x_650_);
v_mctx_653_ = lean_ctor_get(v_snd_651_, 1);
lean_inc_ref(v_mctx_653_);
lean_dec(v_snd_651_);
v___x_654_ = lean_unbox(v_fst_652_);
lean_dec(v_fst_652_);
v_fst_625_ = v___x_654_;
v_mctx_626_ = v_mctx_653_;
goto v___jp_624_;
}
else
{
lean_dec_ref(v___y_648_);
lean_dec_ref(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec_ref(v___f_642_);
v_fst_625_ = v___y_647_;
v_mctx_626_ = v___y_644_;
goto v___jp_624_;
}
}
v___jp_655_:
{
if (v___y_660_ == 0)
{
lean_object* v___x_661_; lean_object* v_fst_662_; lean_object* v_snd_663_; uint8_t v___x_664_; 
v___x_661_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_642_, v___y_658_, v___y_656_, v___y_657_);
v_fst_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_fst_662_);
v_snd_663_ = lean_ctor_get(v___x_661_, 1);
lean_inc(v_snd_663_);
lean_dec_ref(v___x_661_);
v___x_664_ = lean_unbox(v_fst_662_);
lean_dec(v_fst_662_);
v_fst_607_ = v___x_664_;
v_snd_608_ = v_snd_663_;
goto v___jp_606_;
}
else
{
lean_dec_ref(v___y_658_);
lean_dec_ref(v___y_656_);
lean_dec_ref(v___f_642_);
v_fst_607_ = v___y_659_;
v_snd_608_ = v___y_657_;
goto v___jp_606_;
}
}
v___jp_665_:
{
uint8_t v___x_670_; uint8_t v___x_671_; 
v___x_670_ = l_Lean_Expr_hasFVar(v___y_666_);
v___x_671_ = lean_bool_not(v___x_670_);
if (v___x_671_ == 0)
{
v___y_656_ = v___y_666_;
v___y_657_ = v_snd_669_;
v___y_658_ = v___y_667_;
v___y_659_ = v_fst_668_;
v___y_660_ = v___x_671_;
goto v___jp_655_;
}
else
{
uint8_t v___x_672_; uint8_t v___x_673_; 
v___x_672_ = l_Lean_Expr_hasMVar(v___y_666_);
v___x_673_ = lean_bool_not(v___x_672_);
v___y_656_ = v___y_666_;
v___y_657_ = v_snd_669_;
v___y_658_ = v___y_667_;
v___y_659_ = v_fst_668_;
v___y_660_ = v___x_673_;
goto v___jp_655_;
}
}
v___jp_674_:
{
if (v___y_680_ == 0)
{
lean_object* v___x_681_; lean_object* v_fst_682_; uint8_t v___x_683_; 
lean_inc_ref(v___y_678_);
lean_inc_ref(v___f_642_);
v___x_681_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_642_, v___y_678_, v___y_679_, v___y_676_);
v_fst_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_fst_682_);
v___x_683_ = lean_unbox(v_fst_682_);
if (v___x_683_ == 0)
{
lean_object* v_snd_684_; uint8_t v___x_685_; 
v_snd_684_ = lean_ctor_get(v___x_681_, 1);
lean_inc(v_snd_684_);
lean_dec_ref(v___x_681_);
v___x_685_ = lean_unbox(v_fst_682_);
lean_dec(v_fst_682_);
v___y_666_ = v___y_675_;
v___y_667_ = v___y_678_;
v_fst_668_ = v___x_685_;
v_snd_669_ = v_snd_684_;
goto v___jp_665_;
}
else
{
lean_object* v_snd_686_; uint8_t v___x_687_; 
lean_dec_ref(v___y_678_);
lean_dec_ref(v___y_675_);
lean_dec_ref(v___f_642_);
v_snd_686_ = lean_ctor_get(v___x_681_, 1);
lean_inc(v_snd_686_);
lean_dec_ref(v___x_681_);
v___x_687_ = lean_unbox(v_fst_682_);
lean_dec(v_fst_682_);
v_fst_607_ = v___x_687_;
v_snd_608_ = v_snd_686_;
goto v___jp_606_;
}
}
else
{
lean_dec_ref(v___y_679_);
v___y_666_ = v___y_675_;
v___y_667_ = v___y_678_;
v_fst_668_ = v___y_677_;
v_snd_669_ = v___y_676_;
goto v___jp_665_;
}
}
v___jp_688_:
{
if (v___y_694_ == 0)
{
lean_object* v___x_695_; lean_object* v_snd_696_; lean_object* v_fst_697_; lean_object* v_mctx_698_; uint8_t v___x_699_; 
lean_dec_ref(v___y_690_);
v___x_695_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_642_, v___y_692_, v___y_693_, v___y_689_);
v_snd_696_ = lean_ctor_get(v___x_695_, 1);
lean_inc(v_snd_696_);
v_fst_697_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_fst_697_);
lean_dec_ref(v___x_695_);
v_mctx_698_ = lean_ctor_get(v_snd_696_, 1);
lean_inc_ref(v_mctx_698_);
lean_dec(v_snd_696_);
v___x_699_ = lean_unbox(v_fst_697_);
lean_dec(v_fst_697_);
v_fst_590_ = v___x_699_;
v_mctx_591_ = v_mctx_698_;
goto v___jp_589_;
}
else
{
lean_dec_ref(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec_ref(v___y_689_);
lean_dec_ref(v___f_642_);
v_fst_590_ = v___y_691_;
v_mctx_591_ = v___y_690_;
goto v___jp_589_;
}
}
v___jp_700_:
{
lean_object* v___x_702_; lean_object* v___f_703_; 
v___x_702_ = lean_box(v___y_701_);
v___f_703_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(v___f_703_, 0, v___x_702_);
if (lean_obj_tag(v_val_572_) == 0)
{
lean_object* v_type_704_; lean_object* v___x_705_; lean_object* v_mctx_706_; lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; uint8_t v___x_710_; 
v_type_704_ = lean_ctor_get(v_val_572_, 3);
v___x_705_ = lean_st_ref_get(v___y_552_);
v_mctx_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc_ref_n(v_mctx_706_, 2);
lean_dec(v___x_705_);
v___x_707_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
lean_ctor_set(v___x_708_, 1, v_mctx_706_);
v___x_709_ = l_Lean_Expr_hasFVar(v_type_704_);
v___x_710_ = lean_bool_not(v___x_709_);
if (v___x_710_ == 0)
{
lean_inc_ref(v_type_704_);
v___y_644_ = v_mctx_706_;
v___y_645_ = v___x_708_;
v___y_646_ = v_type_704_;
v___y_647_ = v___y_701_;
v___y_648_ = v___f_703_;
v___y_649_ = v___x_710_;
goto v___jp_643_;
}
else
{
uint8_t v___x_711_; uint8_t v___x_712_; 
v___x_711_ = l_Lean_Expr_hasMVar(v_type_704_);
v___x_712_ = lean_bool_not(v___x_711_);
lean_inc_ref(v_type_704_);
v___y_644_ = v_mctx_706_;
v___y_645_ = v___x_708_;
v___y_646_ = v_type_704_;
v___y_647_ = v___y_701_;
v___y_648_ = v___f_703_;
v___y_649_ = v___x_712_;
goto v___jp_643_;
}
}
else
{
uint8_t v_nondep_713_; 
v_nondep_713_ = lean_ctor_get_uint8(v_val_572_, sizeof(void*)*5);
if (v_nondep_713_ == 0)
{
lean_object* v_type_714_; lean_object* v_value_715_; lean_object* v___x_716_; lean_object* v_mctx_717_; lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; uint8_t v___x_721_; 
v_type_714_ = lean_ctor_get(v_val_572_, 3);
v_value_715_ = lean_ctor_get(v_val_572_, 4);
v___x_716_ = lean_st_ref_get(v___y_552_);
v_mctx_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc_ref(v_mctx_717_);
lean_dec(v___x_716_);
v___x_718_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
lean_ctor_set(v___x_719_, 1, v_mctx_717_);
v___x_720_ = l_Lean_Expr_hasFVar(v_type_714_);
v___x_721_ = lean_bool_not(v___x_720_);
if (v___x_721_ == 0)
{
lean_inc_ref(v_type_714_);
lean_inc_ref(v_value_715_);
v___y_675_ = v_value_715_;
v___y_676_ = v___x_719_;
v___y_677_ = v_nondep_713_;
v___y_678_ = v___f_703_;
v___y_679_ = v_type_714_;
v___y_680_ = v___x_721_;
goto v___jp_674_;
}
else
{
uint8_t v___x_722_; uint8_t v___x_723_; 
v___x_722_ = l_Lean_Expr_hasMVar(v_type_714_);
v___x_723_ = lean_bool_not(v___x_722_);
lean_inc_ref(v_type_714_);
lean_inc_ref(v_value_715_);
v___y_675_ = v_value_715_;
v___y_676_ = v___x_719_;
v___y_677_ = v_nondep_713_;
v___y_678_ = v___f_703_;
v___y_679_ = v_type_714_;
v___y_680_ = v___x_723_;
goto v___jp_674_;
}
}
else
{
lean_object* v_type_724_; lean_object* v___x_725_; lean_object* v_mctx_726_; lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v___x_729_; uint8_t v___x_730_; 
v_type_724_ = lean_ctor_get(v_val_572_, 3);
v___x_725_ = lean_st_ref_get(v___y_552_);
v_mctx_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc_ref_n(v_mctx_726_, 2);
lean_dec(v___x_725_);
v___x_727_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
lean_ctor_set(v___x_728_, 1, v_mctx_726_);
v___x_729_ = l_Lean_Expr_hasFVar(v_type_724_);
v___x_730_ = lean_bool_not(v___x_729_);
if (v___x_730_ == 0)
{
lean_inc_ref(v_type_724_);
v___y_689_ = v___x_728_;
v___y_690_ = v_mctx_726_;
v___y_691_ = v___y_701_;
v___y_692_ = v___f_703_;
v___y_693_ = v_type_724_;
v___y_694_ = v___x_730_;
goto v___jp_688_;
}
else
{
uint8_t v___x_731_; uint8_t v___x_732_; 
v___x_731_ = l_Lean_Expr_hasMVar(v_type_724_);
v___x_732_ = lean_bool_not(v___x_731_);
lean_inc_ref(v_type_724_);
v___y_689_ = v___x_728_;
v___y_690_ = v_mctx_726_;
v___y_691_ = v___y_701_;
v___y_692_ = v___f_703_;
v___y_693_ = v_type_724_;
v___y_694_ = v___x_732_;
goto v___jp_688_;
}
}
}
}
v___jp_733_:
{
if (v___y_734_ == 0)
{
if (v_ignoreLetDecls_545_ == 0)
{
lean_del_object(v___x_576_);
v___y_701_ = v_ignoreLetDecls_545_;
goto v___jp_700_;
}
else
{
uint8_t v___x_735_; 
v___x_735_ = l_Lean_LocalDecl_isLet(v_val_572_, v___y_734_);
if (v___x_735_ == 0)
{
lean_del_object(v___x_576_);
v___y_701_ = v___x_735_;
goto v___jp_700_;
}
else
{
lean_dec_ref(v___f_642_);
lean_dec(v___x_582_);
goto v___jp_578_;
}
}
}
else
{
lean_dec_ref(v___f_642_);
lean_dec(v___x_582_);
goto v___jp_578_;
}
}
}
else
{
lean_object* v___x_739_; 
lean_dec(v___x_582_);
lean_del_object(v___x_576_);
v___x_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_739_, 0, v_fst_573_);
lean_ctor_set(v___x_739_, 1, v_snd_574_);
v_a_564_ = v___x_739_;
goto v___jp_563_;
}
v___jp_578_:
{
lean_object* v___x_580_; 
if (v_isShared_577_ == 0)
{
v___x_580_ = v___x_576_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_fst_573_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_snd_574_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
v_a_564_ = v___x_580_;
goto v___jp_563_;
}
}
v___jp_583_:
{
if (v_a_584_ == 0)
{
lean_object* v___x_585_; 
lean_dec(v___x_582_);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v_fst_573_);
lean_ctor_set(v___x_585_, 1, v_snd_574_);
v_a_564_ = v___x_585_;
goto v___jp_563_;
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
lean_inc(v___x_582_);
v___x_586_ = l_Lean_FVarIdSet_insert(v_snd_574_, v___x_582_);
v___x_587_ = l_Lean_FVarIdSet_insert(v_fst_573_, v___x_582_);
v___x_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set(v___x_588_, 1, v___x_586_);
v_a_564_ = v___x_588_;
goto v___jp_563_;
}
}
v___jp_589_:
{
lean_object* v___x_592_; lean_object* v_cache_593_; lean_object* v_zetaDeltaFVarIds_594_; lean_object* v_postponed_595_; lean_object* v_diag_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_604_; 
v___x_592_ = lean_st_ref_take(v___y_552_);
v_cache_593_ = lean_ctor_get(v___x_592_, 1);
v_zetaDeltaFVarIds_594_ = lean_ctor_get(v___x_592_, 2);
v_postponed_595_ = lean_ctor_get(v___x_592_, 3);
v_diag_596_ = lean_ctor_get(v___x_592_, 4);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_604_ == 0)
{
lean_object* v_unused_605_; 
v_unused_605_ = lean_ctor_get(v___x_592_, 0);
lean_dec(v_unused_605_);
v___x_598_ = v___x_592_;
v_isShared_599_ = v_isSharedCheck_604_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_diag_596_);
lean_inc(v_postponed_595_);
lean_inc(v_zetaDeltaFVarIds_594_);
lean_inc(v_cache_593_);
lean_dec(v___x_592_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_604_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v_mctx_591_);
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_mctx_591_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_cache_593_);
lean_ctor_set(v_reuseFailAlloc_603_, 2, v_zetaDeltaFVarIds_594_);
lean_ctor_set(v_reuseFailAlloc_603_, 3, v_postponed_595_);
lean_ctor_set(v_reuseFailAlloc_603_, 4, v_diag_596_);
v___x_601_ = v_reuseFailAlloc_603_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v___x_602_; 
v___x_602_ = lean_st_ref_set(v___y_552_, v___x_601_);
v_a_584_ = v_fst_590_;
goto v___jp_583_;
}
}
}
v___jp_606_:
{
lean_object* v_mctx_609_; lean_object* v___x_610_; lean_object* v_cache_611_; lean_object* v_zetaDeltaFVarIds_612_; lean_object* v_postponed_613_; lean_object* v_diag_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_622_; 
v_mctx_609_ = lean_ctor_get(v_snd_608_, 1);
lean_inc_ref(v_mctx_609_);
lean_dec_ref(v_snd_608_);
v___x_610_ = lean_st_ref_take(v___y_552_);
v_cache_611_ = lean_ctor_get(v___x_610_, 1);
v_zetaDeltaFVarIds_612_ = lean_ctor_get(v___x_610_, 2);
v_postponed_613_ = lean_ctor_get(v___x_610_, 3);
v_diag_614_ = lean_ctor_get(v___x_610_, 4);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_622_ == 0)
{
lean_object* v_unused_623_; 
v_unused_623_ = lean_ctor_get(v___x_610_, 0);
lean_dec(v_unused_623_);
v___x_616_ = v___x_610_;
v_isShared_617_ = v_isSharedCheck_622_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_diag_614_);
lean_inc(v_postponed_613_);
lean_inc(v_zetaDeltaFVarIds_612_);
lean_inc(v_cache_611_);
lean_dec(v___x_610_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_622_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 0, v_mctx_609_);
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_mctx_609_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_cache_611_);
lean_ctor_set(v_reuseFailAlloc_621_, 2, v_zetaDeltaFVarIds_612_);
lean_ctor_set(v_reuseFailAlloc_621_, 3, v_postponed_613_);
lean_ctor_set(v_reuseFailAlloc_621_, 4, v_diag_614_);
v___x_619_ = v_reuseFailAlloc_621_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_620_; 
v___x_620_ = lean_st_ref_set(v___y_552_, v___x_619_);
v_a_584_ = v_fst_607_;
goto v___jp_583_;
}
}
}
v___jp_624_:
{
lean_object* v___x_627_; lean_object* v_cache_628_; lean_object* v_zetaDeltaFVarIds_629_; lean_object* v_postponed_630_; lean_object* v_diag_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_639_; 
v___x_627_ = lean_st_ref_take(v___y_552_);
v_cache_628_ = lean_ctor_get(v___x_627_, 1);
v_zetaDeltaFVarIds_629_ = lean_ctor_get(v___x_627_, 2);
v_postponed_630_ = lean_ctor_get(v___x_627_, 3);
v_diag_631_ = lean_ctor_get(v___x_627_, 4);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_639_ == 0)
{
lean_object* v_unused_640_; 
v_unused_640_ = lean_ctor_get(v___x_627_, 0);
lean_dec(v_unused_640_);
v___x_633_ = v___x_627_;
v_isShared_634_ = v_isSharedCheck_639_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_diag_631_);
lean_inc(v_postponed_630_);
lean_inc(v_zetaDeltaFVarIds_629_);
lean_inc(v_cache_628_);
lean_dec(v___x_627_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_639_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 0, v_mctx_626_);
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_mctx_626_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_cache_628_);
lean_ctor_set(v_reuseFailAlloc_638_, 2, v_zetaDeltaFVarIds_629_);
lean_ctor_set(v_reuseFailAlloc_638_, 3, v_postponed_630_);
lean_ctor_set(v_reuseFailAlloc_638_, 4, v_diag_631_);
v___x_636_ = v_reuseFailAlloc_638_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_637_; 
v___x_637_ = lean_st_ref_set(v___y_552_, v___x_636_);
v_a_584_ = v_fst_625_;
goto v___jp_583_;
}
}
}
}
}
v___jp_563_:
{
lean_object* v___x_566_; 
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 1, v_a_564_);
lean_ctor_set(v___x_560_, 0, v___x_562_);
v___x_566_ = v___x_560_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v_a_564_);
v___x_566_ = v_reuseFailAlloc_570_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
size_t v___x_567_; size_t v___x_568_; lean_object* v___x_569_; 
v___x_567_ = ((size_t)1ULL);
v___x_568_ = lean_usize_add(v_i_549_, v___x_567_);
v___x_569_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(v_ignoreLetDecls_545_, v_forbidden_546_, v_as_547_, v_sz_548_, v___x_568_, v___x_566_, v___y_552_);
return v___x_569_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___boxed(lean_object* v_ignoreLetDecls_743_, lean_object* v_forbidden_744_, lean_object* v_as_745_, lean_object* v_sz_746_, lean_object* v_i_747_, lean_object* v_b_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_754_; size_t v_sz_boxed_755_; size_t v_i_boxed_756_; lean_object* v_res_757_; 
v_ignoreLetDecls_boxed_754_ = lean_unbox(v_ignoreLetDecls_743_);
v_sz_boxed_755_ = lean_unbox_usize(v_sz_746_);
lean_dec(v_sz_746_);
v_i_boxed_756_ = lean_unbox_usize(v_i_747_);
lean_dec(v_i_747_);
v_res_757_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1(v_ignoreLetDecls_boxed_754_, v_forbidden_744_, v_as_745_, v_sz_boxed_755_, v_i_boxed_756_, v_b_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec_ref(v_as_745_);
lean_dec(v_forbidden_744_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(uint8_t v_ignoreLetDecls_758_, lean_object* v_forbidden_759_, lean_object* v_as_760_, size_t v_sz_761_, size_t v_i_762_, lean_object* v_b_763_, lean_object* v___y_764_){
_start:
{
uint8_t v___x_766_; 
v___x_766_ = lean_usize_dec_lt(v_i_762_, v_sz_761_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; 
v___x_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_767_, 0, v_b_763_);
return v___x_767_;
}
else
{
lean_object* v_snd_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_951_; 
v_snd_768_ = lean_ctor_get(v_b_763_, 1);
v_isSharedCheck_951_ = !lean_is_exclusive(v_b_763_);
if (v_isSharedCheck_951_ == 0)
{
lean_object* v_unused_952_; 
v_unused_952_ = lean_ctor_get(v_b_763_, 0);
lean_dec(v_unused_952_);
v___x_770_ = v_b_763_;
v_isShared_771_ = v_isSharedCheck_951_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_snd_768_);
lean_dec(v_b_763_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_951_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; lean_object* v_a_774_; lean_object* v_a_781_; 
v___x_772_ = lean_box(0);
v_a_781_ = lean_array_uget_borrowed(v_as_760_, v_i_762_);
if (lean_obj_tag(v_a_781_) == 0)
{
v_a_774_ = v_snd_768_;
goto v___jp_773_;
}
else
{
lean_object* v_val_782_; lean_object* v_fst_783_; lean_object* v_snd_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_950_; 
v_val_782_ = lean_ctor_get(v_a_781_, 0);
v_fst_783_ = lean_ctor_get(v_snd_768_, 0);
v_snd_784_ = lean_ctor_get(v_snd_768_, 1);
v_isSharedCheck_950_ = !lean_is_exclusive(v_snd_768_);
if (v_isSharedCheck_950_ == 0)
{
v___x_786_ = v_snd_768_;
v_isShared_787_ = v_isSharedCheck_950_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_snd_784_);
lean_inc(v_fst_783_);
lean_dec(v_snd_768_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_950_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_792_; uint8_t v_a_794_; uint8_t v_fst_800_; lean_object* v_mctx_801_; uint8_t v_fst_817_; lean_object* v_snd_818_; uint8_t v_fst_835_; lean_object* v_mctx_836_; uint8_t v___x_851_; 
v___x_792_ = l_Lean_LocalDecl_fvarId(v_val_782_);
v___x_851_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v___x_792_, v_forbidden_759_);
if (v___x_851_ == 0)
{
lean_object* v___f_852_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; uint8_t v___y_858_; uint8_t v___y_859_; lean_object* v___y_866_; uint8_t v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; uint8_t v___y_870_; lean_object* v___y_876_; lean_object* v___y_877_; uint8_t v_fst_878_; lean_object* v_snd_879_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; uint8_t v___y_888_; lean_object* v___y_889_; uint8_t v___y_890_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; uint8_t v___y_903_; uint8_t v___y_904_; uint8_t v___y_911_; uint8_t v___y_944_; uint8_t v___x_946_; 
lean_inc(v_fst_783_);
v___f_852_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_852_, 0, v_fst_783_);
v___x_946_ = l_Lean_LocalDecl_isAuxDecl(v_val_782_);
if (v___x_946_ == 0)
{
uint8_t v___x_947_; uint8_t v___x_948_; 
v___x_947_ = l_Lean_LocalDecl_binderInfo(v_val_782_);
v___x_948_ = l_Lean_BinderInfo_isInstImplicit(v___x_947_);
v___y_944_ = v___x_948_;
goto v___jp_943_;
}
else
{
v___y_944_ = v___x_946_;
goto v___jp_943_;
}
v___jp_853_:
{
if (v___y_859_ == 0)
{
lean_object* v___x_860_; lean_object* v_snd_861_; lean_object* v_fst_862_; lean_object* v_mctx_863_; uint8_t v___x_864_; 
lean_dec_ref(v___y_857_);
v___x_860_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_852_, v___y_856_, v___y_854_, v___y_855_);
v_snd_861_ = lean_ctor_get(v___x_860_, 1);
lean_inc(v_snd_861_);
v_fst_862_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_fst_862_);
lean_dec_ref(v___x_860_);
v_mctx_863_ = lean_ctor_get(v_snd_861_, 1);
lean_inc_ref(v_mctx_863_);
lean_dec(v_snd_861_);
v___x_864_ = lean_unbox(v_fst_862_);
lean_dec(v_fst_862_);
v_fst_835_ = v___x_864_;
v_mctx_836_ = v_mctx_863_;
goto v___jp_834_;
}
else
{
lean_dec_ref(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec_ref(v___f_852_);
v_fst_835_ = v___y_858_;
v_mctx_836_ = v___y_857_;
goto v___jp_834_;
}
}
v___jp_865_:
{
if (v___y_870_ == 0)
{
lean_object* v___x_871_; lean_object* v_fst_872_; lean_object* v_snd_873_; uint8_t v___x_874_; 
v___x_871_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_852_, v___y_869_, v___y_866_, v___y_868_);
v_fst_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_fst_872_);
v_snd_873_ = lean_ctor_get(v___x_871_, 1);
lean_inc(v_snd_873_);
lean_dec_ref(v___x_871_);
v___x_874_ = lean_unbox(v_fst_872_);
lean_dec(v_fst_872_);
v_fst_817_ = v___x_874_;
v_snd_818_ = v_snd_873_;
goto v___jp_816_;
}
else
{
lean_dec_ref(v___y_869_);
lean_dec_ref(v___y_866_);
lean_dec_ref(v___f_852_);
v_fst_817_ = v___y_867_;
v_snd_818_ = v___y_868_;
goto v___jp_816_;
}
}
v___jp_875_:
{
uint8_t v___x_880_; uint8_t v___x_881_; 
v___x_880_ = l_Lean_Expr_hasFVar(v___y_876_);
v___x_881_ = lean_bool_not(v___x_880_);
if (v___x_881_ == 0)
{
v___y_866_ = v___y_876_;
v___y_867_ = v_fst_878_;
v___y_868_ = v_snd_879_;
v___y_869_ = v___y_877_;
v___y_870_ = v___x_881_;
goto v___jp_865_;
}
else
{
uint8_t v___x_882_; uint8_t v___x_883_; 
v___x_882_ = l_Lean_Expr_hasMVar(v___y_876_);
v___x_883_ = lean_bool_not(v___x_882_);
v___y_866_ = v___y_876_;
v___y_867_ = v_fst_878_;
v___y_868_ = v_snd_879_;
v___y_869_ = v___y_877_;
v___y_870_ = v___x_883_;
goto v___jp_865_;
}
}
v___jp_884_:
{
if (v___y_890_ == 0)
{
lean_object* v___x_891_; lean_object* v_fst_892_; uint8_t v___x_893_; 
lean_inc_ref(v___y_889_);
lean_inc_ref(v___f_852_);
v___x_891_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_852_, v___y_889_, v___y_886_, v___y_887_);
v_fst_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_fst_892_);
v___x_893_ = lean_unbox(v_fst_892_);
if (v___x_893_ == 0)
{
lean_object* v_snd_894_; uint8_t v___x_895_; 
v_snd_894_ = lean_ctor_get(v___x_891_, 1);
lean_inc(v_snd_894_);
lean_dec_ref(v___x_891_);
v___x_895_ = lean_unbox(v_fst_892_);
lean_dec(v_fst_892_);
v___y_876_ = v___y_885_;
v___y_877_ = v___y_889_;
v_fst_878_ = v___x_895_;
v_snd_879_ = v_snd_894_;
goto v___jp_875_;
}
else
{
lean_object* v_snd_896_; uint8_t v___x_897_; 
lean_dec_ref(v___y_889_);
lean_dec_ref(v___y_885_);
lean_dec_ref(v___f_852_);
v_snd_896_ = lean_ctor_get(v___x_891_, 1);
lean_inc(v_snd_896_);
lean_dec_ref(v___x_891_);
v___x_897_ = lean_unbox(v_fst_892_);
lean_dec(v_fst_892_);
v_fst_817_ = v___x_897_;
v_snd_818_ = v_snd_896_;
goto v___jp_816_;
}
}
else
{
lean_dec_ref(v___y_886_);
v___y_876_ = v___y_885_;
v___y_877_ = v___y_889_;
v_fst_878_ = v___y_888_;
v_snd_879_ = v___y_887_;
goto v___jp_875_;
}
}
v___jp_898_:
{
if (v___y_904_ == 0)
{
lean_object* v___x_905_; lean_object* v_snd_906_; lean_object* v_fst_907_; lean_object* v_mctx_908_; uint8_t v___x_909_; 
lean_dec_ref(v___y_901_);
v___x_905_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_852_, v___y_902_, v___y_899_, v___y_900_);
v_snd_906_ = lean_ctor_get(v___x_905_, 1);
lean_inc(v_snd_906_);
v_fst_907_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_fst_907_);
lean_dec_ref(v___x_905_);
v_mctx_908_ = lean_ctor_get(v_snd_906_, 1);
lean_inc_ref(v_mctx_908_);
lean_dec(v_snd_906_);
v___x_909_ = lean_unbox(v_fst_907_);
lean_dec(v_fst_907_);
v_fst_800_ = v___x_909_;
v_mctx_801_ = v_mctx_908_;
goto v___jp_799_;
}
else
{
lean_dec_ref(v___y_902_);
lean_dec_ref(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec_ref(v___f_852_);
v_fst_800_ = v___y_903_;
v_mctx_801_ = v___y_901_;
goto v___jp_799_;
}
}
v___jp_910_:
{
lean_object* v___x_912_; lean_object* v___f_913_; 
v___x_912_ = lean_box(v___y_911_);
v___f_913_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(v___f_913_, 0, v___x_912_);
if (lean_obj_tag(v_val_782_) == 0)
{
lean_object* v_type_914_; lean_object* v___x_915_; lean_object* v_mctx_916_; lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; uint8_t v___x_920_; 
v_type_914_ = lean_ctor_get(v_val_782_, 3);
v___x_915_ = lean_st_ref_get(v___y_764_);
v_mctx_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc_ref_n(v_mctx_916_, 2);
lean_dec(v___x_915_);
v___x_917_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
lean_ctor_set(v___x_918_, 1, v_mctx_916_);
v___x_919_ = l_Lean_Expr_hasFVar(v_type_914_);
v___x_920_ = lean_bool_not(v___x_919_);
if (v___x_920_ == 0)
{
lean_inc_ref(v_type_914_);
v___y_854_ = v_type_914_;
v___y_855_ = v___x_918_;
v___y_856_ = v___f_913_;
v___y_857_ = v_mctx_916_;
v___y_858_ = v___y_911_;
v___y_859_ = v___x_920_;
goto v___jp_853_;
}
else
{
uint8_t v___x_921_; uint8_t v___x_922_; 
v___x_921_ = l_Lean_Expr_hasMVar(v_type_914_);
v___x_922_ = lean_bool_not(v___x_921_);
lean_inc_ref(v_type_914_);
v___y_854_ = v_type_914_;
v___y_855_ = v___x_918_;
v___y_856_ = v___f_913_;
v___y_857_ = v_mctx_916_;
v___y_858_ = v___y_911_;
v___y_859_ = v___x_922_;
goto v___jp_853_;
}
}
else
{
uint8_t v_nondep_923_; 
v_nondep_923_ = lean_ctor_get_uint8(v_val_782_, sizeof(void*)*5);
if (v_nondep_923_ == 0)
{
lean_object* v_type_924_; lean_object* v_value_925_; lean_object* v___x_926_; lean_object* v_mctx_927_; lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; uint8_t v___x_931_; 
v_type_924_ = lean_ctor_get(v_val_782_, 3);
v_value_925_ = lean_ctor_get(v_val_782_, 4);
v___x_926_ = lean_st_ref_get(v___y_764_);
v_mctx_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc_ref(v_mctx_927_);
lean_dec(v___x_926_);
v___x_928_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set(v___x_929_, 1, v_mctx_927_);
v___x_930_ = l_Lean_Expr_hasFVar(v_type_924_);
v___x_931_ = lean_bool_not(v___x_930_);
if (v___x_931_ == 0)
{
lean_inc_ref(v_type_924_);
lean_inc_ref(v_value_925_);
v___y_885_ = v_value_925_;
v___y_886_ = v_type_924_;
v___y_887_ = v___x_929_;
v___y_888_ = v_nondep_923_;
v___y_889_ = v___f_913_;
v___y_890_ = v___x_931_;
goto v___jp_884_;
}
else
{
uint8_t v___x_932_; uint8_t v___x_933_; 
v___x_932_ = l_Lean_Expr_hasMVar(v_type_924_);
v___x_933_ = lean_bool_not(v___x_932_);
lean_inc_ref(v_type_924_);
lean_inc_ref(v_value_925_);
v___y_885_ = v_value_925_;
v___y_886_ = v_type_924_;
v___y_887_ = v___x_929_;
v___y_888_ = v_nondep_923_;
v___y_889_ = v___f_913_;
v___y_890_ = v___x_933_;
goto v___jp_884_;
}
}
else
{
lean_object* v_type_934_; lean_object* v___x_935_; lean_object* v_mctx_936_; lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; uint8_t v___x_940_; 
v_type_934_ = lean_ctor_get(v_val_782_, 3);
v___x_935_ = lean_st_ref_get(v___y_764_);
v_mctx_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc_ref_n(v_mctx_936_, 2);
lean_dec(v___x_935_);
v___x_937_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set(v___x_938_, 1, v_mctx_936_);
v___x_939_ = l_Lean_Expr_hasFVar(v_type_934_);
v___x_940_ = lean_bool_not(v___x_939_);
if (v___x_940_ == 0)
{
lean_inc_ref(v_type_934_);
v___y_899_ = v_type_934_;
v___y_900_ = v___x_938_;
v___y_901_ = v_mctx_936_;
v___y_902_ = v___f_913_;
v___y_903_ = v___y_911_;
v___y_904_ = v___x_940_;
goto v___jp_898_;
}
else
{
uint8_t v___x_941_; uint8_t v___x_942_; 
v___x_941_ = l_Lean_Expr_hasMVar(v_type_934_);
v___x_942_ = lean_bool_not(v___x_941_);
lean_inc_ref(v_type_934_);
v___y_899_ = v_type_934_;
v___y_900_ = v___x_938_;
v___y_901_ = v_mctx_936_;
v___y_902_ = v___f_913_;
v___y_903_ = v___y_911_;
v___y_904_ = v___x_942_;
goto v___jp_898_;
}
}
}
}
v___jp_943_:
{
if (v___y_944_ == 0)
{
if (v_ignoreLetDecls_758_ == 0)
{
lean_del_object(v___x_786_);
v___y_911_ = v_ignoreLetDecls_758_;
goto v___jp_910_;
}
else
{
uint8_t v___x_945_; 
v___x_945_ = l_Lean_LocalDecl_isLet(v_val_782_, v___y_944_);
if (v___x_945_ == 0)
{
lean_del_object(v___x_786_);
v___y_911_ = v___x_945_;
goto v___jp_910_;
}
else
{
lean_dec_ref(v___f_852_);
lean_dec(v___x_792_);
goto v___jp_788_;
}
}
}
else
{
lean_dec_ref(v___f_852_);
lean_dec(v___x_792_);
goto v___jp_788_;
}
}
}
else
{
lean_object* v___x_949_; 
lean_dec(v___x_792_);
lean_del_object(v___x_786_);
v___x_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_949_, 0, v_fst_783_);
lean_ctor_set(v___x_949_, 1, v_snd_784_);
v_a_774_ = v___x_949_;
goto v___jp_773_;
}
v___jp_788_:
{
lean_object* v___x_790_; 
if (v_isShared_787_ == 0)
{
v___x_790_ = v___x_786_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_fst_783_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_snd_784_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
v_a_774_ = v___x_790_;
goto v___jp_773_;
}
}
v___jp_793_:
{
if (v_a_794_ == 0)
{
lean_object* v___x_795_; 
lean_dec(v___x_792_);
v___x_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_795_, 0, v_fst_783_);
lean_ctor_set(v___x_795_, 1, v_snd_784_);
v_a_774_ = v___x_795_;
goto v___jp_773_;
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
lean_inc(v___x_792_);
v___x_796_ = l_Lean_FVarIdSet_insert(v_snd_784_, v___x_792_);
v___x_797_ = l_Lean_FVarIdSet_insert(v_fst_783_, v___x_792_);
v___x_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
lean_ctor_set(v___x_798_, 1, v___x_796_);
v_a_774_ = v___x_798_;
goto v___jp_773_;
}
}
v___jp_799_:
{
lean_object* v___x_802_; lean_object* v_cache_803_; lean_object* v_zetaDeltaFVarIds_804_; lean_object* v_postponed_805_; lean_object* v_diag_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_814_; 
v___x_802_ = lean_st_ref_take(v___y_764_);
v_cache_803_ = lean_ctor_get(v___x_802_, 1);
v_zetaDeltaFVarIds_804_ = lean_ctor_get(v___x_802_, 2);
v_postponed_805_ = lean_ctor_get(v___x_802_, 3);
v_diag_806_ = lean_ctor_get(v___x_802_, 4);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_814_ == 0)
{
lean_object* v_unused_815_; 
v_unused_815_ = lean_ctor_get(v___x_802_, 0);
lean_dec(v_unused_815_);
v___x_808_ = v___x_802_;
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_diag_806_);
lean_inc(v_postponed_805_);
lean_inc(v_zetaDeltaFVarIds_804_);
lean_inc(v_cache_803_);
lean_dec(v___x_802_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v_mctx_801_);
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_mctx_801_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_cache_803_);
lean_ctor_set(v_reuseFailAlloc_813_, 2, v_zetaDeltaFVarIds_804_);
lean_ctor_set(v_reuseFailAlloc_813_, 3, v_postponed_805_);
lean_ctor_set(v_reuseFailAlloc_813_, 4, v_diag_806_);
v___x_811_ = v_reuseFailAlloc_813_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_812_; 
v___x_812_ = lean_st_ref_set(v___y_764_, v___x_811_);
v_a_794_ = v_fst_800_;
goto v___jp_793_;
}
}
}
v___jp_816_:
{
lean_object* v_mctx_819_; lean_object* v___x_820_; lean_object* v_cache_821_; lean_object* v_zetaDeltaFVarIds_822_; lean_object* v_postponed_823_; lean_object* v_diag_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_832_; 
v_mctx_819_ = lean_ctor_get(v_snd_818_, 1);
lean_inc_ref(v_mctx_819_);
lean_dec_ref(v_snd_818_);
v___x_820_ = lean_st_ref_take(v___y_764_);
v_cache_821_ = lean_ctor_get(v___x_820_, 1);
v_zetaDeltaFVarIds_822_ = lean_ctor_get(v___x_820_, 2);
v_postponed_823_ = lean_ctor_get(v___x_820_, 3);
v_diag_824_ = lean_ctor_get(v___x_820_, 4);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_832_ == 0)
{
lean_object* v_unused_833_; 
v_unused_833_ = lean_ctor_get(v___x_820_, 0);
lean_dec(v_unused_833_);
v___x_826_ = v___x_820_;
v_isShared_827_ = v_isSharedCheck_832_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_diag_824_);
lean_inc(v_postponed_823_);
lean_inc(v_zetaDeltaFVarIds_822_);
lean_inc(v_cache_821_);
lean_dec(v___x_820_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_832_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v_mctx_819_);
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_mctx_819_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v_cache_821_);
lean_ctor_set(v_reuseFailAlloc_831_, 2, v_zetaDeltaFVarIds_822_);
lean_ctor_set(v_reuseFailAlloc_831_, 3, v_postponed_823_);
lean_ctor_set(v_reuseFailAlloc_831_, 4, v_diag_824_);
v___x_829_ = v_reuseFailAlloc_831_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
lean_object* v___x_830_; 
v___x_830_ = lean_st_ref_set(v___y_764_, v___x_829_);
v_a_794_ = v_fst_817_;
goto v___jp_793_;
}
}
}
v___jp_834_:
{
lean_object* v___x_837_; lean_object* v_cache_838_; lean_object* v_zetaDeltaFVarIds_839_; lean_object* v_postponed_840_; lean_object* v_diag_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_849_; 
v___x_837_ = lean_st_ref_take(v___y_764_);
v_cache_838_ = lean_ctor_get(v___x_837_, 1);
v_zetaDeltaFVarIds_839_ = lean_ctor_get(v___x_837_, 2);
v_postponed_840_ = lean_ctor_get(v___x_837_, 3);
v_diag_841_ = lean_ctor_get(v___x_837_, 4);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_849_ == 0)
{
lean_object* v_unused_850_; 
v_unused_850_ = lean_ctor_get(v___x_837_, 0);
lean_dec(v_unused_850_);
v___x_843_ = v___x_837_;
v_isShared_844_ = v_isSharedCheck_849_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_diag_841_);
lean_inc(v_postponed_840_);
lean_inc(v_zetaDeltaFVarIds_839_);
lean_inc(v_cache_838_);
lean_dec(v___x_837_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_849_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v_mctx_836_);
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_mctx_836_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_cache_838_);
lean_ctor_set(v_reuseFailAlloc_848_, 2, v_zetaDeltaFVarIds_839_);
lean_ctor_set(v_reuseFailAlloc_848_, 3, v_postponed_840_);
lean_ctor_set(v_reuseFailAlloc_848_, 4, v_diag_841_);
v___x_846_ = v_reuseFailAlloc_848_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
lean_object* v___x_847_; 
v___x_847_ = lean_st_ref_set(v___y_764_, v___x_846_);
v_a_794_ = v_fst_835_;
goto v___jp_793_;
}
}
}
}
}
v___jp_773_:
{
lean_object* v___x_776_; 
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 1, v_a_774_);
lean_ctor_set(v___x_770_, 0, v___x_772_);
v___x_776_ = v___x_770_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_a_774_);
v___x_776_ = v_reuseFailAlloc_780_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
size_t v___x_777_; size_t v___x_778_; 
v___x_777_ = ((size_t)1ULL);
v___x_778_ = lean_usize_add(v_i_762_, v___x_777_);
v_i_762_ = v___x_778_;
v_b_763_ = v___x_776_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_ignoreLetDecls_953_, lean_object* v_forbidden_954_, lean_object* v_as_955_, lean_object* v_sz_956_, lean_object* v_i_957_, lean_object* v_b_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_961_; size_t v_sz_boxed_962_; size_t v_i_boxed_963_; lean_object* v_res_964_; 
v_ignoreLetDecls_boxed_961_ = lean_unbox(v_ignoreLetDecls_953_);
v_sz_boxed_962_ = lean_unbox_usize(v_sz_956_);
lean_dec(v_sz_956_);
v_i_boxed_963_ = lean_unbox_usize(v_i_957_);
lean_dec(v_i_957_);
v_res_964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(v_ignoreLetDecls_boxed_961_, v_forbidden_954_, v_as_955_, v_sz_boxed_962_, v_i_boxed_963_, v_b_958_, v___y_959_);
lean_dec(v___y_959_);
lean_dec_ref(v_as_955_);
lean_dec(v_forbidden_954_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2(uint8_t v_ignoreLetDecls_965_, lean_object* v_forbidden_966_, lean_object* v_as_967_, size_t v_sz_968_, size_t v_i_969_, lean_object* v_b_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
uint8_t v___x_976_; 
v___x_976_ = lean_usize_dec_lt(v_i_969_, v_sz_968_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; 
v___x_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_977_, 0, v_b_970_);
return v___x_977_;
}
else
{
lean_object* v_snd_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_1161_; 
v_snd_978_ = lean_ctor_get(v_b_970_, 1);
v_isSharedCheck_1161_ = !lean_is_exclusive(v_b_970_);
if (v_isSharedCheck_1161_ == 0)
{
lean_object* v_unused_1162_; 
v_unused_1162_ = lean_ctor_get(v_b_970_, 0);
lean_dec(v_unused_1162_);
v___x_980_ = v_b_970_;
v_isShared_981_ = v_isSharedCheck_1161_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_snd_978_);
lean_dec(v_b_970_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_1161_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_982_; lean_object* v_a_984_; lean_object* v_a_991_; 
v___x_982_ = lean_box(0);
v_a_991_ = lean_array_uget_borrowed(v_as_967_, v_i_969_);
if (lean_obj_tag(v_a_991_) == 0)
{
v_a_984_ = v_snd_978_;
goto v___jp_983_;
}
else
{
lean_object* v_val_992_; lean_object* v_fst_993_; lean_object* v_snd_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1160_; 
v_val_992_ = lean_ctor_get(v_a_991_, 0);
v_fst_993_ = lean_ctor_get(v_snd_978_, 0);
v_snd_994_ = lean_ctor_get(v_snd_978_, 1);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_snd_978_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_996_ = v_snd_978_;
v_isShared_997_ = v_isSharedCheck_1160_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_snd_994_);
lean_inc(v_fst_993_);
lean_dec(v_snd_978_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1160_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_1002_; uint8_t v_a_1004_; uint8_t v_fst_1010_; lean_object* v_mctx_1011_; uint8_t v_fst_1027_; lean_object* v_snd_1028_; uint8_t v_fst_1045_; lean_object* v_mctx_1046_; uint8_t v___x_1061_; 
v___x_1002_ = l_Lean_LocalDecl_fvarId(v_val_992_);
v___x_1061_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v___x_1002_, v_forbidden_966_);
if (v___x_1061_ == 0)
{
lean_object* v___f_1062_; lean_object* v___y_1064_; uint8_t v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; uint8_t v___y_1069_; uint8_t v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; uint8_t v___y_1080_; lean_object* v___y_1086_; lean_object* v___y_1087_; uint8_t v_fst_1088_; lean_object* v_snd_1089_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; uint8_t v___y_1098_; lean_object* v___y_1099_; uint8_t v___y_1100_; uint8_t v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; uint8_t v___y_1114_; uint8_t v___y_1121_; uint8_t v___y_1154_; uint8_t v___x_1156_; 
lean_inc(v_fst_993_);
v___f_1062_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1062_, 0, v_fst_993_);
v___x_1156_ = l_Lean_LocalDecl_isAuxDecl(v_val_992_);
if (v___x_1156_ == 0)
{
uint8_t v___x_1157_; uint8_t v___x_1158_; 
v___x_1157_ = l_Lean_LocalDecl_binderInfo(v_val_992_);
v___x_1158_ = l_Lean_BinderInfo_isInstImplicit(v___x_1157_);
v___y_1154_ = v___x_1158_;
goto v___jp_1153_;
}
else
{
v___y_1154_ = v___x_1156_;
goto v___jp_1153_;
}
v___jp_1063_:
{
if (v___y_1069_ == 0)
{
lean_object* v___x_1070_; lean_object* v_snd_1071_; lean_object* v_fst_1072_; lean_object* v_mctx_1073_; uint8_t v___x_1074_; 
lean_dec_ref(v___y_1067_);
v___x_1070_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1062_, v___y_1066_, v___y_1064_, v___y_1068_);
v_snd_1071_ = lean_ctor_get(v___x_1070_, 1);
lean_inc(v_snd_1071_);
v_fst_1072_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_fst_1072_);
lean_dec_ref(v___x_1070_);
v_mctx_1073_ = lean_ctor_get(v_snd_1071_, 1);
lean_inc_ref(v_mctx_1073_);
lean_dec(v_snd_1071_);
v___x_1074_ = lean_unbox(v_fst_1072_);
lean_dec(v_fst_1072_);
v_fst_1045_ = v___x_1074_;
v_mctx_1046_ = v_mctx_1073_;
goto v___jp_1044_;
}
else
{
lean_dec_ref(v___y_1068_);
lean_dec_ref(v___y_1066_);
lean_dec_ref(v___y_1064_);
lean_dec_ref(v___f_1062_);
v_fst_1045_ = v___y_1065_;
v_mctx_1046_ = v___y_1067_;
goto v___jp_1044_;
}
}
v___jp_1075_:
{
if (v___y_1080_ == 0)
{
lean_object* v___x_1081_; lean_object* v_fst_1082_; lean_object* v_snd_1083_; uint8_t v___x_1084_; 
v___x_1081_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1062_, v___y_1079_, v___y_1077_, v___y_1078_);
v_fst_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_fst_1082_);
v_snd_1083_ = lean_ctor_get(v___x_1081_, 1);
lean_inc(v_snd_1083_);
lean_dec_ref(v___x_1081_);
v___x_1084_ = lean_unbox(v_fst_1082_);
lean_dec(v_fst_1082_);
v_fst_1027_ = v___x_1084_;
v_snd_1028_ = v_snd_1083_;
goto v___jp_1026_;
}
else
{
lean_dec_ref(v___y_1079_);
lean_dec_ref(v___y_1077_);
lean_dec_ref(v___f_1062_);
v_fst_1027_ = v___y_1076_;
v_snd_1028_ = v___y_1078_;
goto v___jp_1026_;
}
}
v___jp_1085_:
{
uint8_t v___x_1090_; uint8_t v___x_1091_; 
v___x_1090_ = l_Lean_Expr_hasFVar(v___y_1086_);
v___x_1091_ = lean_bool_not(v___x_1090_);
if (v___x_1091_ == 0)
{
v___y_1076_ = v_fst_1088_;
v___y_1077_ = v___y_1086_;
v___y_1078_ = v_snd_1089_;
v___y_1079_ = v___y_1087_;
v___y_1080_ = v___x_1091_;
goto v___jp_1075_;
}
else
{
uint8_t v___x_1092_; uint8_t v___x_1093_; 
v___x_1092_ = l_Lean_Expr_hasMVar(v___y_1086_);
v___x_1093_ = lean_bool_not(v___x_1092_);
v___y_1076_ = v_fst_1088_;
v___y_1077_ = v___y_1086_;
v___y_1078_ = v_snd_1089_;
v___y_1079_ = v___y_1087_;
v___y_1080_ = v___x_1093_;
goto v___jp_1075_;
}
}
v___jp_1094_:
{
if (v___y_1100_ == 0)
{
lean_object* v___x_1101_; lean_object* v_fst_1102_; uint8_t v___x_1103_; 
lean_inc_ref(v___y_1097_);
lean_inc_ref(v___f_1062_);
v___x_1101_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1062_, v___y_1097_, v___y_1099_, v___y_1095_);
v_fst_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_fst_1102_);
v___x_1103_ = lean_unbox(v_fst_1102_);
if (v___x_1103_ == 0)
{
lean_object* v_snd_1104_; uint8_t v___x_1105_; 
v_snd_1104_ = lean_ctor_get(v___x_1101_, 1);
lean_inc(v_snd_1104_);
lean_dec_ref(v___x_1101_);
v___x_1105_ = lean_unbox(v_fst_1102_);
lean_dec(v_fst_1102_);
v___y_1086_ = v___y_1096_;
v___y_1087_ = v___y_1097_;
v_fst_1088_ = v___x_1105_;
v_snd_1089_ = v_snd_1104_;
goto v___jp_1085_;
}
else
{
lean_object* v_snd_1106_; uint8_t v___x_1107_; 
lean_dec_ref(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec_ref(v___f_1062_);
v_snd_1106_ = lean_ctor_get(v___x_1101_, 1);
lean_inc(v_snd_1106_);
lean_dec_ref(v___x_1101_);
v___x_1107_ = lean_unbox(v_fst_1102_);
lean_dec(v_fst_1102_);
v_fst_1027_ = v___x_1107_;
v_snd_1028_ = v_snd_1106_;
goto v___jp_1026_;
}
}
else
{
lean_dec_ref(v___y_1099_);
v___y_1086_ = v___y_1096_;
v___y_1087_ = v___y_1097_;
v_fst_1088_ = v___y_1098_;
v_snd_1089_ = v___y_1095_;
goto v___jp_1085_;
}
}
v___jp_1108_:
{
if (v___y_1114_ == 0)
{
lean_object* v___x_1115_; lean_object* v_snd_1116_; lean_object* v_fst_1117_; lean_object* v_mctx_1118_; uint8_t v___x_1119_; 
lean_dec_ref(v___y_1110_);
v___x_1115_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1062_, v___y_1111_, v___y_1112_, v___y_1113_);
v_snd_1116_ = lean_ctor_get(v___x_1115_, 1);
lean_inc(v_snd_1116_);
v_fst_1117_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_fst_1117_);
lean_dec_ref(v___x_1115_);
v_mctx_1118_ = lean_ctor_get(v_snd_1116_, 1);
lean_inc_ref(v_mctx_1118_);
lean_dec(v_snd_1116_);
v___x_1119_ = lean_unbox(v_fst_1117_);
lean_dec(v_fst_1117_);
v_fst_1010_ = v___x_1119_;
v_mctx_1011_ = v_mctx_1118_;
goto v___jp_1009_;
}
else
{
lean_dec_ref(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec_ref(v___f_1062_);
v_fst_1010_ = v___y_1109_;
v_mctx_1011_ = v___y_1110_;
goto v___jp_1009_;
}
}
v___jp_1120_:
{
lean_object* v___x_1122_; lean_object* v___f_1123_; 
v___x_1122_ = lean_box(v___y_1121_);
v___f_1123_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1123_, 0, v___x_1122_);
if (lean_obj_tag(v_val_992_) == 0)
{
lean_object* v_type_1124_; lean_object* v___x_1125_; lean_object* v_mctx_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; uint8_t v___x_1129_; uint8_t v___x_1130_; 
v_type_1124_ = lean_ctor_get(v_val_992_, 3);
v___x_1125_ = lean_st_ref_get(v___y_972_);
v_mctx_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc_ref_n(v_mctx_1126_, 2);
lean_dec(v___x_1125_);
v___x_1127_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
lean_ctor_set(v___x_1128_, 1, v_mctx_1126_);
v___x_1129_ = l_Lean_Expr_hasFVar(v_type_1124_);
v___x_1130_ = lean_bool_not(v___x_1129_);
if (v___x_1130_ == 0)
{
lean_inc_ref(v_type_1124_);
v___y_1064_ = v_type_1124_;
v___y_1065_ = v___y_1121_;
v___y_1066_ = v___f_1123_;
v___y_1067_ = v_mctx_1126_;
v___y_1068_ = v___x_1128_;
v___y_1069_ = v___x_1130_;
goto v___jp_1063_;
}
else
{
uint8_t v___x_1131_; uint8_t v___x_1132_; 
v___x_1131_ = l_Lean_Expr_hasMVar(v_type_1124_);
v___x_1132_ = lean_bool_not(v___x_1131_);
lean_inc_ref(v_type_1124_);
v___y_1064_ = v_type_1124_;
v___y_1065_ = v___y_1121_;
v___y_1066_ = v___f_1123_;
v___y_1067_ = v_mctx_1126_;
v___y_1068_ = v___x_1128_;
v___y_1069_ = v___x_1132_;
goto v___jp_1063_;
}
}
else
{
uint8_t v_nondep_1133_; 
v_nondep_1133_ = lean_ctor_get_uint8(v_val_992_, sizeof(void*)*5);
if (v_nondep_1133_ == 0)
{
lean_object* v_type_1134_; lean_object* v_value_1135_; lean_object* v___x_1136_; lean_object* v_mctx_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; uint8_t v___x_1140_; uint8_t v___x_1141_; 
v_type_1134_ = lean_ctor_get(v_val_992_, 3);
v_value_1135_ = lean_ctor_get(v_val_992_, 4);
v___x_1136_ = lean_st_ref_get(v___y_972_);
v_mctx_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc_ref(v_mctx_1137_);
lean_dec(v___x_1136_);
v___x_1138_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
lean_ctor_set(v___x_1139_, 1, v_mctx_1137_);
v___x_1140_ = l_Lean_Expr_hasFVar(v_type_1134_);
v___x_1141_ = lean_bool_not(v___x_1140_);
if (v___x_1141_ == 0)
{
lean_inc_ref(v_type_1134_);
lean_inc_ref(v_value_1135_);
v___y_1095_ = v___x_1139_;
v___y_1096_ = v_value_1135_;
v___y_1097_ = v___f_1123_;
v___y_1098_ = v_nondep_1133_;
v___y_1099_ = v_type_1134_;
v___y_1100_ = v___x_1141_;
goto v___jp_1094_;
}
else
{
uint8_t v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = l_Lean_Expr_hasMVar(v_type_1134_);
v___x_1143_ = lean_bool_not(v___x_1142_);
lean_inc_ref(v_type_1134_);
lean_inc_ref(v_value_1135_);
v___y_1095_ = v___x_1139_;
v___y_1096_ = v_value_1135_;
v___y_1097_ = v___f_1123_;
v___y_1098_ = v_nondep_1133_;
v___y_1099_ = v_type_1134_;
v___y_1100_ = v___x_1143_;
goto v___jp_1094_;
}
}
else
{
lean_object* v_type_1144_; lean_object* v___x_1145_; lean_object* v_mctx_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; uint8_t v___x_1150_; 
v_type_1144_ = lean_ctor_get(v_val_992_, 3);
v___x_1145_ = lean_st_ref_get(v___y_972_);
v_mctx_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc_ref_n(v_mctx_1146_, 2);
lean_dec(v___x_1145_);
v___x_1147_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
lean_ctor_set(v___x_1148_, 1, v_mctx_1146_);
v___x_1149_ = l_Lean_Expr_hasFVar(v_type_1144_);
v___x_1150_ = lean_bool_not(v___x_1149_);
if (v___x_1150_ == 0)
{
lean_inc_ref(v_type_1144_);
v___y_1109_ = v___y_1121_;
v___y_1110_ = v_mctx_1146_;
v___y_1111_ = v___f_1123_;
v___y_1112_ = v_type_1144_;
v___y_1113_ = v___x_1148_;
v___y_1114_ = v___x_1150_;
goto v___jp_1108_;
}
else
{
uint8_t v___x_1151_; uint8_t v___x_1152_; 
v___x_1151_ = l_Lean_Expr_hasMVar(v_type_1144_);
v___x_1152_ = lean_bool_not(v___x_1151_);
lean_inc_ref(v_type_1144_);
v___y_1109_ = v___y_1121_;
v___y_1110_ = v_mctx_1146_;
v___y_1111_ = v___f_1123_;
v___y_1112_ = v_type_1144_;
v___y_1113_ = v___x_1148_;
v___y_1114_ = v___x_1152_;
goto v___jp_1108_;
}
}
}
}
v___jp_1153_:
{
if (v___y_1154_ == 0)
{
if (v_ignoreLetDecls_965_ == 0)
{
lean_del_object(v___x_996_);
v___y_1121_ = v_ignoreLetDecls_965_;
goto v___jp_1120_;
}
else
{
uint8_t v___x_1155_; 
v___x_1155_ = l_Lean_LocalDecl_isLet(v_val_992_, v___y_1154_);
if (v___x_1155_ == 0)
{
lean_del_object(v___x_996_);
v___y_1121_ = v___x_1155_;
goto v___jp_1120_;
}
else
{
lean_dec_ref(v___f_1062_);
lean_dec(v___x_1002_);
goto v___jp_998_;
}
}
}
else
{
lean_dec_ref(v___f_1062_);
lean_dec(v___x_1002_);
goto v___jp_998_;
}
}
}
else
{
lean_object* v___x_1159_; 
lean_dec(v___x_1002_);
lean_del_object(v___x_996_);
v___x_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1159_, 0, v_fst_993_);
lean_ctor_set(v___x_1159_, 1, v_snd_994_);
v_a_984_ = v___x_1159_;
goto v___jp_983_;
}
v___jp_998_:
{
lean_object* v___x_1000_; 
if (v_isShared_997_ == 0)
{
v___x_1000_ = v___x_996_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_fst_993_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_snd_994_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
v_a_984_ = v___x_1000_;
goto v___jp_983_;
}
}
v___jp_1003_:
{
if (v_a_1004_ == 0)
{
lean_object* v___x_1005_; 
lean_dec(v___x_1002_);
v___x_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1005_, 0, v_fst_993_);
lean_ctor_set(v___x_1005_, 1, v_snd_994_);
v_a_984_ = v___x_1005_;
goto v___jp_983_;
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
lean_inc(v___x_1002_);
v___x_1006_ = l_Lean_FVarIdSet_insert(v_snd_994_, v___x_1002_);
v___x_1007_ = l_Lean_FVarIdSet_insert(v_fst_993_, v___x_1002_);
v___x_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v___x_1006_);
v_a_984_ = v___x_1008_;
goto v___jp_983_;
}
}
v___jp_1009_:
{
lean_object* v___x_1012_; lean_object* v_cache_1013_; lean_object* v_zetaDeltaFVarIds_1014_; lean_object* v_postponed_1015_; lean_object* v_diag_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1024_; 
v___x_1012_ = lean_st_ref_take(v___y_972_);
v_cache_1013_ = lean_ctor_get(v___x_1012_, 1);
v_zetaDeltaFVarIds_1014_ = lean_ctor_get(v___x_1012_, 2);
v_postponed_1015_ = lean_ctor_get(v___x_1012_, 3);
v_diag_1016_ = lean_ctor_get(v___x_1012_, 4);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1024_ == 0)
{
lean_object* v_unused_1025_; 
v_unused_1025_ = lean_ctor_get(v___x_1012_, 0);
lean_dec(v_unused_1025_);
v___x_1018_ = v___x_1012_;
v_isShared_1019_ = v_isSharedCheck_1024_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_diag_1016_);
lean_inc(v_postponed_1015_);
lean_inc(v_zetaDeltaFVarIds_1014_);
lean_inc(v_cache_1013_);
lean_dec(v___x_1012_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1024_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 0, v_mctx_1011_);
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_mctx_1011_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_cache_1013_);
lean_ctor_set(v_reuseFailAlloc_1023_, 2, v_zetaDeltaFVarIds_1014_);
lean_ctor_set(v_reuseFailAlloc_1023_, 3, v_postponed_1015_);
lean_ctor_set(v_reuseFailAlloc_1023_, 4, v_diag_1016_);
v___x_1021_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
lean_object* v___x_1022_; 
v___x_1022_ = lean_st_ref_set(v___y_972_, v___x_1021_);
v_a_1004_ = v_fst_1010_;
goto v___jp_1003_;
}
}
}
v___jp_1026_:
{
lean_object* v_mctx_1029_; lean_object* v___x_1030_; lean_object* v_cache_1031_; lean_object* v_zetaDeltaFVarIds_1032_; lean_object* v_postponed_1033_; lean_object* v_diag_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1042_; 
v_mctx_1029_ = lean_ctor_get(v_snd_1028_, 1);
lean_inc_ref(v_mctx_1029_);
lean_dec_ref(v_snd_1028_);
v___x_1030_ = lean_st_ref_take(v___y_972_);
v_cache_1031_ = lean_ctor_get(v___x_1030_, 1);
v_zetaDeltaFVarIds_1032_ = lean_ctor_get(v___x_1030_, 2);
v_postponed_1033_ = lean_ctor_get(v___x_1030_, 3);
v_diag_1034_ = lean_ctor_get(v___x_1030_, 4);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1042_ == 0)
{
lean_object* v_unused_1043_; 
v_unused_1043_ = lean_ctor_get(v___x_1030_, 0);
lean_dec(v_unused_1043_);
v___x_1036_ = v___x_1030_;
v_isShared_1037_ = v_isSharedCheck_1042_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_diag_1034_);
lean_inc(v_postponed_1033_);
lean_inc(v_zetaDeltaFVarIds_1032_);
lean_inc(v_cache_1031_);
lean_dec(v___x_1030_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1042_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v_mctx_1029_);
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_mctx_1029_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v_cache_1031_);
lean_ctor_set(v_reuseFailAlloc_1041_, 2, v_zetaDeltaFVarIds_1032_);
lean_ctor_set(v_reuseFailAlloc_1041_, 3, v_postponed_1033_);
lean_ctor_set(v_reuseFailAlloc_1041_, 4, v_diag_1034_);
v___x_1039_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_st_ref_set(v___y_972_, v___x_1039_);
v_a_1004_ = v_fst_1027_;
goto v___jp_1003_;
}
}
}
v___jp_1044_:
{
lean_object* v___x_1047_; lean_object* v_cache_1048_; lean_object* v_zetaDeltaFVarIds_1049_; lean_object* v_postponed_1050_; lean_object* v_diag_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1059_; 
v___x_1047_ = lean_st_ref_take(v___y_972_);
v_cache_1048_ = lean_ctor_get(v___x_1047_, 1);
v_zetaDeltaFVarIds_1049_ = lean_ctor_get(v___x_1047_, 2);
v_postponed_1050_ = lean_ctor_get(v___x_1047_, 3);
v_diag_1051_ = lean_ctor_get(v___x_1047_, 4);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1059_ == 0)
{
lean_object* v_unused_1060_; 
v_unused_1060_ = lean_ctor_get(v___x_1047_, 0);
lean_dec(v_unused_1060_);
v___x_1053_ = v___x_1047_;
v_isShared_1054_ = v_isSharedCheck_1059_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_diag_1051_);
lean_inc(v_postponed_1050_);
lean_inc(v_zetaDeltaFVarIds_1049_);
lean_inc(v_cache_1048_);
lean_dec(v___x_1047_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1059_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 0, v_mctx_1046_);
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_mctx_1046_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_cache_1048_);
lean_ctor_set(v_reuseFailAlloc_1058_, 2, v_zetaDeltaFVarIds_1049_);
lean_ctor_set(v_reuseFailAlloc_1058_, 3, v_postponed_1050_);
lean_ctor_set(v_reuseFailAlloc_1058_, 4, v_diag_1051_);
v___x_1056_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
lean_object* v___x_1057_; 
v___x_1057_ = lean_st_ref_set(v___y_972_, v___x_1056_);
v_a_1004_ = v_fst_1045_;
goto v___jp_1003_;
}
}
}
}
}
v___jp_983_:
{
lean_object* v___x_986_; 
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 1, v_a_984_);
lean_ctor_set(v___x_980_, 0, v___x_982_);
v___x_986_ = v___x_980_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_982_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_a_984_);
v___x_986_ = v_reuseFailAlloc_990_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
size_t v___x_987_; size_t v___x_988_; lean_object* v___x_989_; 
v___x_987_ = ((size_t)1ULL);
v___x_988_ = lean_usize_add(v_i_969_, v___x_987_);
v___x_989_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(v_ignoreLetDecls_965_, v_forbidden_966_, v_as_967_, v_sz_968_, v___x_988_, v___x_986_, v___y_972_);
return v___x_989_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2___boxed(lean_object* v_ignoreLetDecls_1163_, lean_object* v_forbidden_1164_, lean_object* v_as_1165_, lean_object* v_sz_1166_, lean_object* v_i_1167_, lean_object* v_b_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1174_; size_t v_sz_boxed_1175_; size_t v_i_boxed_1176_; lean_object* v_res_1177_; 
v_ignoreLetDecls_boxed_1174_ = lean_unbox(v_ignoreLetDecls_1163_);
v_sz_boxed_1175_ = lean_unbox_usize(v_sz_1166_);
lean_dec(v_sz_1166_);
v_i_boxed_1176_ = lean_unbox_usize(v_i_1167_);
lean_dec(v_i_1167_);
v_res_1177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2(v_ignoreLetDecls_boxed_1174_, v_forbidden_1164_, v_as_1165_, v_sz_boxed_1175_, v_i_boxed_1176_, v_b_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec_ref(v_as_1165_);
lean_dec(v_forbidden_1164_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(lean_object* v_init_1178_, uint8_t v_ignoreLetDecls_1179_, lean_object* v_forbidden_1180_, lean_object* v_n_1181_, lean_object* v_b_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
if (lean_obj_tag(v_n_1181_) == 0)
{
lean_object* v_cs_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; size_t v_sz_1191_; size_t v___x_1192_; lean_object* v___x_1193_; 
v_cs_1188_ = lean_ctor_get(v_n_1181_, 0);
v___x_1189_ = lean_box(0);
v___x_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
lean_ctor_set(v___x_1190_, 1, v_b_1182_);
v_sz_1191_ = lean_array_size(v_cs_1188_);
v___x_1192_ = ((size_t)0ULL);
v___x_1193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(v_init_1178_, v_ignoreLetDecls_1179_, v_forbidden_1180_, v_cs_1188_, v_sz_1191_, v___x_1192_, v___x_1190_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1208_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1196_ = v___x_1193_;
v_isShared_1197_ = v_isSharedCheck_1208_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1193_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1208_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v_fst_1198_; 
v_fst_1198_ = lean_ctor_get(v_a_1194_, 0);
if (lean_obj_tag(v_fst_1198_) == 0)
{
lean_object* v_snd_1199_; lean_object* v___x_1200_; lean_object* v___x_1202_; 
v_snd_1199_ = lean_ctor_get(v_a_1194_, 1);
lean_inc(v_snd_1199_);
lean_dec(v_a_1194_);
v___x_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1200_, 0, v_snd_1199_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1200_);
v___x_1202_ = v___x_1196_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
else
{
lean_object* v_val_1204_; lean_object* v___x_1206_; 
lean_inc_ref(v_fst_1198_);
lean_dec(v_a_1194_);
v_val_1204_ = lean_ctor_get(v_fst_1198_, 0);
lean_inc(v_val_1204_);
lean_dec_ref_known(v_fst_1198_, 1);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v_val_1204_);
v___x_1206_ = v___x_1196_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_val_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
v_a_1209_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1193_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1193_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
else
{
lean_object* v_vs_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; size_t v_sz_1220_; size_t v___x_1221_; lean_object* v___x_1222_; 
v_vs_1217_ = lean_ctor_get(v_n_1181_, 0);
v___x_1218_ = lean_box(0);
v___x_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
lean_ctor_set(v___x_1219_, 1, v_b_1182_);
v_sz_1220_ = lean_array_size(v_vs_1217_);
v___x_1221_ = ((size_t)0ULL);
v___x_1222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2(v_ignoreLetDecls_1179_, v_forbidden_1180_, v_vs_1217_, v_sz_1220_, v___x_1221_, v___x_1219_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1237_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1225_ = v___x_1222_;
v_isShared_1226_ = v_isSharedCheck_1237_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1222_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1237_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v_fst_1227_; 
v_fst_1227_ = lean_ctor_get(v_a_1223_, 0);
if (lean_obj_tag(v_fst_1227_) == 0)
{
lean_object* v_snd_1228_; lean_object* v___x_1229_; lean_object* v___x_1231_; 
v_snd_1228_ = lean_ctor_get(v_a_1223_, 1);
lean_inc(v_snd_1228_);
lean_dec(v_a_1223_);
v___x_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1229_, 0, v_snd_1228_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v___x_1229_);
v___x_1231_ = v___x_1225_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
else
{
lean_object* v_val_1233_; lean_object* v___x_1235_; 
lean_inc_ref(v_fst_1227_);
lean_dec(v_a_1223_);
v_val_1233_ = lean_ctor_get(v_fst_1227_, 0);
lean_inc(v_val_1233_);
lean_dec_ref_known(v_fst_1227_, 1);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v_val_1233_);
v___x_1235_ = v___x_1225_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_val_1233_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
else
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1245_; 
v_a_1238_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1240_ = v___x_1222_;
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1222_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1238_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(lean_object* v_init_1246_, uint8_t v_ignoreLetDecls_1247_, lean_object* v_forbidden_1248_, lean_object* v_as_1249_, size_t v_sz_1250_, size_t v_i_1251_, lean_object* v_b_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
uint8_t v___x_1258_; 
v___x_1258_ = lean_usize_dec_lt(v_i_1251_, v_sz_1250_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1259_; 
v___x_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1259_, 0, v_b_1252_);
return v___x_1259_;
}
else
{
lean_object* v_snd_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1294_; 
v_snd_1260_ = lean_ctor_get(v_b_1252_, 1);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_b_1252_);
if (v_isSharedCheck_1294_ == 0)
{
lean_object* v_unused_1295_; 
v_unused_1295_ = lean_ctor_get(v_b_1252_, 0);
lean_dec(v_unused_1295_);
v___x_1262_ = v_b_1252_;
v_isShared_1263_ = v_isSharedCheck_1294_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_snd_1260_);
lean_dec(v_b_1252_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1294_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v_a_1264_; lean_object* v___x_1265_; 
v_a_1264_ = lean_array_uget_borrowed(v_as_1249_, v_i_1251_);
lean_inc(v_snd_1260_);
v___x_1265_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(v_init_1246_, v_ignoreLetDecls_1247_, v_forbidden_1248_, v_a_1264_, v_snd_1260_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1285_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1268_ = v___x_1265_;
v_isShared_1269_ = v_isSharedCheck_1285_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1285_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
if (lean_obj_tag(v_a_1266_) == 0)
{
lean_object* v___x_1270_; lean_object* v___x_1272_; 
v___x_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1270_, 0, v_a_1266_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v___x_1270_);
v___x_1272_ = v___x_1262_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1270_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_snd_1260_);
v___x_1272_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
lean_object* v___x_1274_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1272_);
v___x_1274_ = v___x_1268_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1272_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1278_; lean_object* v___x_1280_; 
lean_del_object(v___x_1268_);
lean_dec(v_snd_1260_);
v_a_1277_ = lean_ctor_get(v_a_1266_, 0);
lean_inc(v_a_1277_);
lean_dec_ref_known(v_a_1266_, 1);
v___x_1278_ = lean_box(0);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 1, v_a_1277_);
lean_ctor_set(v___x_1262_, 0, v___x_1278_);
v___x_1280_ = v___x_1262_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1278_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_a_1277_);
v___x_1280_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
size_t v___x_1281_; size_t v___x_1282_; 
v___x_1281_ = ((size_t)1ULL);
v___x_1282_ = lean_usize_add(v_i_1251_, v___x_1281_);
v_i_1251_ = v___x_1282_;
v_b_1252_ = v___x_1280_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_del_object(v___x_1262_);
lean_dec(v_snd_1260_);
v_a_1286_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1265_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1265_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1___boxed(lean_object* v_init_1296_, lean_object* v_ignoreLetDecls_1297_, lean_object* v_forbidden_1298_, lean_object* v_as_1299_, lean_object* v_sz_1300_, lean_object* v_i_1301_, lean_object* v_b_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1308_; size_t v_sz_boxed_1309_; size_t v_i_boxed_1310_; lean_object* v_res_1311_; 
v_ignoreLetDecls_boxed_1308_ = lean_unbox(v_ignoreLetDecls_1297_);
v_sz_boxed_1309_ = lean_unbox_usize(v_sz_1300_);
lean_dec(v_sz_1300_);
v_i_boxed_1310_ = lean_unbox_usize(v_i_1301_);
lean_dec(v_i_1301_);
v_res_1311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(v_init_1296_, v_ignoreLetDecls_boxed_1308_, v_forbidden_1298_, v_as_1299_, v_sz_boxed_1309_, v_i_boxed_1310_, v_b_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec_ref(v_as_1299_);
lean_dec(v_forbidden_1298_);
lean_dec_ref(v_init_1296_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0___boxed(lean_object* v_init_1312_, lean_object* v_ignoreLetDecls_1313_, lean_object* v_forbidden_1314_, lean_object* v_n_1315_, lean_object* v_b_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1322_; lean_object* v_res_1323_; 
v_ignoreLetDecls_boxed_1322_ = lean_unbox(v_ignoreLetDecls_1313_);
v_res_1323_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(v_init_1312_, v_ignoreLetDecls_boxed_1322_, v_forbidden_1314_, v_n_1315_, v_b_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec_ref(v_n_1315_);
lean_dec(v_forbidden_1314_);
lean_dec_ref(v_init_1312_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0(uint8_t v_ignoreLetDecls_1324_, lean_object* v_forbidden_1325_, lean_object* v_t_1326_, lean_object* v_init_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v_root_1333_; lean_object* v_tail_1334_; lean_object* v___x_1335_; 
v_root_1333_ = lean_ctor_get(v_t_1326_, 0);
v_tail_1334_ = lean_ctor_get(v_t_1326_, 1);
lean_inc_ref(v_init_1327_);
v___x_1335_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(v_init_1327_, v_ignoreLetDecls_1324_, v_forbidden_1325_, v_root_1333_, v_init_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
lean_dec_ref(v_init_1327_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1372_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1338_ = v___x_1335_;
v_isShared_1339_ = v_isSharedCheck_1372_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1335_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1372_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
if (lean_obj_tag(v_a_1336_) == 0)
{
lean_object* v_a_1340_; lean_object* v___x_1342_; 
v_a_1340_ = lean_ctor_get(v_a_1336_, 0);
lean_inc(v_a_1340_);
lean_dec_ref_known(v_a_1336_, 1);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v_a_1340_);
v___x_1342_ = v___x_1338_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_a_1340_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; size_t v_sz_1347_; size_t v___x_1348_; lean_object* v___x_1349_; 
lean_del_object(v___x_1338_);
v_a_1344_ = lean_ctor_get(v_a_1336_, 0);
lean_inc(v_a_1344_);
lean_dec_ref_known(v_a_1336_, 1);
v___x_1345_ = lean_box(0);
v___x_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
lean_ctor_set(v___x_1346_, 1, v_a_1344_);
v_sz_1347_ = lean_array_size(v_tail_1334_);
v___x_1348_ = ((size_t)0ULL);
v___x_1349_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1(v_ignoreLetDecls_1324_, v_forbidden_1325_, v_tail_1334_, v_sz_1347_, v___x_1348_, v___x_1346_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1363_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1352_ = v___x_1349_;
v_isShared_1353_ = v_isSharedCheck_1363_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1349_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1363_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v_fst_1354_; 
v_fst_1354_ = lean_ctor_get(v_a_1350_, 0);
if (lean_obj_tag(v_fst_1354_) == 0)
{
lean_object* v_snd_1355_; lean_object* v___x_1357_; 
v_snd_1355_ = lean_ctor_get(v_a_1350_, 1);
lean_inc(v_snd_1355_);
lean_dec(v_a_1350_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v_snd_1355_);
v___x_1357_ = v___x_1352_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_snd_1355_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
else
{
lean_object* v_val_1359_; lean_object* v___x_1361_; 
lean_inc_ref(v_fst_1354_);
lean_dec(v_a_1350_);
v_val_1359_ = lean_ctor_get(v_fst_1354_, 0);
lean_inc(v_val_1359_);
lean_dec_ref_known(v_fst_1354_, 1);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v_val_1359_);
v___x_1361_ = v___x_1352_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_val_1359_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
v_a_1364_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1349_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1349_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
}
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
v_a_1373_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1335_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1335_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0___boxed(lean_object* v_ignoreLetDecls_1381_, lean_object* v_forbidden_1382_, lean_object* v_t_1383_, lean_object* v_init_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1390_; lean_object* v_res_1391_; 
v_ignoreLetDecls_boxed_1390_ = lean_unbox(v_ignoreLetDecls_1381_);
v_res_1391_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0(v_ignoreLetDecls_boxed_1390_, v_forbidden_1382_, v_t_1383_, v_init_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec_ref(v_t_1383_);
lean_dec(v_forbidden_1382_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(lean_object* v_as_1392_, size_t v_i_1393_, size_t v_stop_1394_, lean_object* v_b_1395_){
_start:
{
lean_object* v___y_1397_; uint8_t v___x_1401_; 
v___x_1401_ = lean_usize_dec_eq(v_i_1393_, v_stop_1394_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1402_; uint8_t v___x_1403_; 
v___x_1402_ = lean_array_uget_borrowed(v_as_1392_, v_i_1393_);
v___x_1403_ = l_Lean_Expr_isFVar(v___x_1402_);
if (v___x_1403_ == 0)
{
v___y_1397_ = v_b_1395_;
goto v___jp_1396_;
}
else
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = l_Lean_Expr_fvarId_x21(v___x_1402_);
v___x_1405_ = l_Lean_FVarIdSet_insert(v_b_1395_, v___x_1404_);
v___y_1397_ = v___x_1405_;
goto v___jp_1396_;
}
}
else
{
return v_b_1395_;
}
v___jp_1396_:
{
size_t v___x_1398_; size_t v___x_1399_; 
v___x_1398_ = ((size_t)1ULL);
v___x_1399_ = lean_usize_add(v_i_1393_, v___x_1398_);
v_i_1393_ = v___x_1399_;
v_b_1395_ = v___y_1397_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1___boxed(lean_object* v_as_1406_, lean_object* v_i_1407_, lean_object* v_stop_1408_, lean_object* v_b_1409_){
_start:
{
size_t v_i_boxed_1410_; size_t v_stop_boxed_1411_; lean_object* v_res_1412_; 
v_i_boxed_1410_ = lean_unbox_usize(v_i_1407_);
lean_dec(v_i_1407_);
v_stop_boxed_1411_ = lean_unbox_usize(v_stop_1408_);
lean_dec(v_stop_1408_);
v_res_1412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(v_as_1406_, v_i_boxed_1410_, v_stop_boxed_1411_, v_b_1409_);
lean_dec_ref(v_as_1406_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize(lean_object* v_targets_1413_, lean_object* v_forbidden_1414_, uint8_t v_ignoreLetDecls_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_){
_start:
{
lean_object* v_r_1421_; lean_object* v___y_1423_; lean_object* v___x_1445_; lean_object* v___x_1446_; uint8_t v___x_1447_; 
v_r_1421_ = lean_box(1);
v___x_1445_ = lean_unsigned_to_nat(0u);
v___x_1446_ = lean_array_get_size(v_targets_1413_);
v___x_1447_ = lean_nat_dec_lt(v___x_1445_, v___x_1446_);
if (v___x_1447_ == 0)
{
v___y_1423_ = v_r_1421_;
goto v___jp_1422_;
}
else
{
uint8_t v___x_1448_; 
v___x_1448_ = lean_nat_dec_le(v___x_1446_, v___x_1446_);
if (v___x_1448_ == 0)
{
if (v___x_1447_ == 0)
{
v___y_1423_ = v_r_1421_;
goto v___jp_1422_;
}
else
{
size_t v___x_1449_; size_t v___x_1450_; lean_object* v___x_1451_; 
v___x_1449_ = ((size_t)0ULL);
v___x_1450_ = lean_usize_of_nat(v___x_1446_);
v___x_1451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(v_targets_1413_, v___x_1449_, v___x_1450_, v_r_1421_);
v___y_1423_ = v___x_1451_;
goto v___jp_1422_;
}
}
else
{
size_t v___x_1452_; size_t v___x_1453_; lean_object* v___x_1454_; 
v___x_1452_ = ((size_t)0ULL);
v___x_1453_ = lean_usize_of_nat(v___x_1446_);
v___x_1454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(v_targets_1413_, v___x_1452_, v___x_1453_, v_r_1421_);
v___y_1423_ = v___x_1454_;
goto v___jp_1422_;
}
}
v___jp_1422_:
{
lean_object* v_lctx_1424_; lean_object* v_decls_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v_lctx_1424_ = lean_ctor_get(v_a_1416_, 2);
v_decls_1425_ = lean_ctor_get(v_lctx_1424_, 1);
v___x_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1426_, 0, v___y_1423_);
lean_ctor_set(v___x_1426_, 1, v_r_1421_);
v___x_1427_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0(v_ignoreLetDecls_1415_, v_forbidden_1414_, v_decls_1425_, v___x_1426_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1436_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1436_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1436_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v_snd_1432_; lean_object* v___x_1434_; 
v_snd_1432_ = lean_ctor_get(v_a_1428_, 1);
lean_inc(v_snd_1432_);
lean_dec(v_a_1428_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v_snd_1432_);
v___x_1434_ = v___x_1430_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_snd_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
v_a_1437_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1427_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1427_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize___boxed(lean_object* v_targets_1455_, lean_object* v_forbidden_1456_, lean_object* v_ignoreLetDecls_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1463_; lean_object* v_res_1464_; 
v_ignoreLetDecls_boxed_1463_ = lean_unbox(v_ignoreLetDecls_1457_);
v_res_1464_ = l_Lean_Meta_getFVarSetToGeneralize(v_targets_1455_, v_forbidden_1456_, v_ignoreLetDecls_boxed_1463_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_);
lean_dec(v_a_1461_);
lean_dec_ref(v_a_1460_);
lean_dec(v_a_1459_);
lean_dec_ref(v_a_1458_);
lean_dec(v_forbidden_1456_);
lean_dec_ref(v_targets_1455_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4(uint8_t v_ignoreLetDecls_1465_, lean_object* v_forbidden_1466_, lean_object* v_as_1467_, size_t v_sz_1468_, size_t v_i_1469_, lean_object* v_b_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(v_ignoreLetDecls_1465_, v_forbidden_1466_, v_as_1467_, v_sz_1468_, v_i_1469_, v_b_1470_, v___y_1472_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___boxed(lean_object* v_ignoreLetDecls_1477_, lean_object* v_forbidden_1478_, lean_object* v_as_1479_, lean_object* v_sz_1480_, lean_object* v_i_1481_, lean_object* v_b_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1488_; size_t v_sz_boxed_1489_; size_t v_i_boxed_1490_; lean_object* v_res_1491_; 
v_ignoreLetDecls_boxed_1488_ = lean_unbox(v_ignoreLetDecls_1477_);
v_sz_boxed_1489_ = lean_unbox_usize(v_sz_1480_);
lean_dec(v_sz_1480_);
v_i_boxed_1490_ = lean_unbox_usize(v_i_1481_);
lean_dec(v_i_1481_);
v_res_1491_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4(v_ignoreLetDecls_boxed_1488_, v_forbidden_1478_, v_as_1479_, v_sz_boxed_1489_, v_i_boxed_1490_, v_b_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec_ref(v_as_1479_);
lean_dec(v_forbidden_1478_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4(uint8_t v_ignoreLetDecls_1492_, lean_object* v_forbidden_1493_, lean_object* v_as_1494_, size_t v_sz_1495_, size_t v_i_1496_, lean_object* v_b_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(v_ignoreLetDecls_1492_, v_forbidden_1493_, v_as_1494_, v_sz_1495_, v_i_1496_, v_b_1497_, v___y_1499_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_ignoreLetDecls_1504_, lean_object* v_forbidden_1505_, lean_object* v_as_1506_, lean_object* v_sz_1507_, lean_object* v_i_1508_, lean_object* v_b_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1515_; size_t v_sz_boxed_1516_; size_t v_i_boxed_1517_; lean_object* v_res_1518_; 
v_ignoreLetDecls_boxed_1515_ = lean_unbox(v_ignoreLetDecls_1504_);
v_sz_boxed_1516_ = lean_unbox_usize(v_sz_1507_);
lean_dec(v_sz_1507_);
v_i_boxed_1517_ = lean_unbox_usize(v_i_1508_);
lean_dec(v_i_1508_);
v_res_1518_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4(v_ignoreLetDecls_boxed_1515_, v_forbidden_1505_, v_as_1506_, v_sz_boxed_1516_, v_i_boxed_1517_, v_b_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec_ref(v_as_1506_);
lean_dec(v_forbidden_1505_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(lean_object* v_init_1519_, lean_object* v_x_1520_){
_start:
{
if (lean_obj_tag(v_x_1520_) == 0)
{
lean_object* v_k_1521_; lean_object* v_l_1522_; lean_object* v_r_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v_k_1521_ = lean_ctor_get(v_x_1520_, 1);
lean_inc(v_k_1521_);
v_l_1522_ = lean_ctor_get(v_x_1520_, 3);
lean_inc(v_l_1522_);
v_r_1523_ = lean_ctor_get(v_x_1520_, 4);
lean_inc(v_r_1523_);
lean_dec_ref_known(v_x_1520_, 5);
v___x_1524_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(v_init_1519_, v_l_1522_);
v___x_1525_ = lean_array_push(v___x_1524_, v_k_1521_);
v_init_1519_ = v___x_1525_;
v_x_1520_ = v_r_1523_;
goto _start;
}
else
{
return v_init_1519_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize(lean_object* v_targets_1527_, lean_object* v_forbidden_1528_, uint8_t v_ignoreLetDecls_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Lean_Meta_mkGeneralizationForbiddenSet(v_targets_1527_, v_forbidden_1528_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; lean_object* v___x_1537_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1536_);
lean_dec_ref_known(v___x_1535_, 1);
v___x_1537_ = l_Lean_Meta_getFVarSetToGeneralize(v_targets_1527_, v_a_1536_, v_ignoreLetDecls_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
lean_dec(v_a_1536_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v___y_1540_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1538_);
lean_dec_ref_known(v___x_1537_, 1);
if (lean_obj_tag(v_a_1538_) == 0)
{
lean_object* v_size_1544_; 
v_size_1544_ = lean_ctor_get(v_a_1538_, 0);
lean_inc(v_size_1544_);
v___y_1540_ = v_size_1544_;
goto v___jp_1539_;
}
else
{
lean_object* v___x_1545_; 
v___x_1545_ = lean_unsigned_to_nat(0u);
v___y_1540_ = v___x_1545_;
goto v___jp_1539_;
}
v___jp_1539_:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1541_ = lean_mk_empty_array_with_capacity(v___y_1540_);
lean_dec(v___y_1540_);
v___x_1542_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(v___x_1541_, v_a_1538_);
v___x_1543_ = l_Lean_Meta_sortFVarIds___redArg(v___x_1542_, v_a_1530_);
return v___x_1543_;
}
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
v_a_1546_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1537_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1537_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
else
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
v_a_1554_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v___x_1535_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1535_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize___boxed(lean_object* v_targets_1562_, lean_object* v_forbidden_1563_, lean_object* v_ignoreLetDecls_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1570_; lean_object* v_res_1571_; 
v_ignoreLetDecls_boxed_1570_ = lean_unbox(v_ignoreLetDecls_1564_);
v_res_1571_ = l_Lean_Meta_getFVarsToGeneralize(v_targets_1562_, v_forbidden_1563_, v_ignoreLetDecls_boxed_1570_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_);
lean_dec(v_a_1568_);
lean_dec_ref(v_a_1567_);
lean_dec(v_a_1566_);
lean_dec_ref(v_a_1565_);
lean_dec_ref(v_targets_1562_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0(lean_object* v_init_1572_, lean_object* v_t_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(v_init_1572_, v_t_1573_);
return v___x_1574_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_CollectFVars(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_GeneralizeVars(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
