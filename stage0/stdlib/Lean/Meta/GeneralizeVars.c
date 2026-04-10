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
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_21_ = lean_st_ref_set(v___y_2_, v___x_20_);
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
lean_dec_ref(v_x_59_);
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
lean_dec_ref(v___x_133_);
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
lean_dec_ref(v___x_141_);
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
lean_dec_ref(v_todo_188_);
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
lean_dec_ref(v___x_200_);
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
lean_dec_ref(v___x_245_);
v___x_247_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(v_a_246_, v___y_227_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v_a_248_; lean_object* v___x_249_; lean_object* v___x_251_; 
v_a_248_ = lean_ctor_get(v___x_247_, 0);
lean_inc(v_a_248_);
lean_dec_ref(v___x_247_);
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
lean_dec_ref(v___x_300_);
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
uint8_t v___y_9979__boxed_327_; uint8_t v_res_328_; lean_object* v_r_329_; 
v___y_9979__boxed_327_ = lean_unbox(v___y_325_);
v_res_328_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1(v___y_9979__boxed_327_, v_x_326_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(uint8_t v_ignoreLetDecls_337_, lean_object* v_forbidden_338_, lean_object* v_as_339_, size_t v_sz_340_, size_t v_i_341_, lean_object* v_b_342_, lean_object* v___y_343_){
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
lean_object* v_snd_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_506_; 
v_snd_347_ = lean_ctor_get(v_b_342_, 1);
v_isSharedCheck_506_ = !lean_is_exclusive(v_b_342_);
if (v_isSharedCheck_506_ == 0)
{
lean_object* v_unused_507_; 
v_unused_507_ = lean_ctor_get(v_b_342_, 0);
lean_dec(v_unused_507_);
v___x_349_ = v_b_342_;
v_isShared_350_ = v_isSharedCheck_506_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_snd_347_);
lean_dec(v_b_342_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_506_;
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
lean_object* v_val_361_; lean_object* v_fst_362_; lean_object* v_snd_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_505_; 
v_val_361_ = lean_ctor_get(v_a_360_, 0);
v_fst_362_ = lean_ctor_get(v_snd_347_, 0);
v_snd_363_ = lean_ctor_get(v_snd_347_, 1);
v_isSharedCheck_505_ = !lean_is_exclusive(v_snd_347_);
if (v_isSharedCheck_505_ == 0)
{
v___x_365_ = v_snd_347_;
v_isShared_366_ = v_isSharedCheck_505_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_snd_363_);
lean_inc(v_fst_362_);
lean_dec(v_snd_347_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_505_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_371_; uint8_t v_a_373_; uint8_t v_fst_379_; lean_object* v_mctx_380_; lean_object* v___y_396_; uint8_t v_fst_402_; lean_object* v_snd_403_; lean_object* v___y_420_; uint8_t v_fst_425_; lean_object* v_mctx_426_; lean_object* v___y_442_; uint8_t v___x_447_; 
v___x_371_ = l_Lean_LocalDecl_fvarId(v_val_361_);
v___x_447_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v___x_371_, v_forbidden_338_);
if (v___x_447_ == 0)
{
lean_object* v___f_448_; lean_object* v___y_450_; lean_object* v___y_451_; uint8_t v_fst_452_; lean_object* v_snd_453_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; uint8_t v___y_466_; uint8_t v___y_499_; uint8_t v___x_501_; 
lean_inc(v_fst_362_);
v___f_448_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_448_, 0, v_fst_362_);
v___x_501_ = l_Lean_LocalDecl_isAuxDecl(v_val_361_);
if (v___x_501_ == 0)
{
uint8_t v___x_502_; uint8_t v___x_503_; 
v___x_502_ = l_Lean_LocalDecl_binderInfo(v_val_361_);
v___x_503_ = l_Lean_BinderInfo_isInstImplicit(v___x_502_);
v___y_499_ = v___x_503_;
goto v___jp_498_;
}
else
{
v___y_499_ = v___x_501_;
goto v___jp_498_;
}
v___jp_449_:
{
if (v_fst_452_ == 0)
{
uint8_t v___x_454_; 
v___x_454_ = l_Lean_Expr_hasFVar(v___y_450_);
if (v___x_454_ == 0)
{
uint8_t v___x_455_; 
v___x_455_ = l_Lean_Expr_hasMVar(v___y_450_);
if (v___x_455_ == 0)
{
lean_dec_ref(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec_ref(v___f_448_);
v_fst_402_ = v___x_455_;
v_snd_403_ = v_snd_453_;
goto v___jp_401_;
}
else
{
lean_object* v___x_456_; 
v___x_456_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_448_, v___y_451_, v___y_450_, v_snd_453_);
v___y_420_ = v___x_456_;
goto v___jp_419_;
}
}
else
{
lean_object* v___x_457_; 
v___x_457_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_448_, v___y_451_, v___y_450_, v_snd_453_);
v___y_420_ = v___x_457_;
goto v___jp_419_;
}
}
else
{
lean_dec_ref(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec_ref(v___f_448_);
v_fst_402_ = v_fst_452_;
v_snd_403_ = v_snd_453_;
goto v___jp_401_;
}
}
v___jp_458_:
{
lean_object* v_fst_462_; lean_object* v_snd_463_; uint8_t v___x_464_; 
v_fst_462_ = lean_ctor_get(v___y_461_, 0);
lean_inc(v_fst_462_);
v_snd_463_ = lean_ctor_get(v___y_461_, 1);
lean_inc(v_snd_463_);
lean_dec_ref(v___y_461_);
v___x_464_ = lean_unbox(v_fst_462_);
lean_dec(v_fst_462_);
v___y_450_ = v___y_459_;
v___y_451_ = v___y_460_;
v_fst_452_ = v___x_464_;
v_snd_453_ = v_snd_463_;
goto v___jp_449_;
}
v___jp_465_:
{
lean_object* v___x_467_; lean_object* v___f_468_; 
v___x_467_ = lean_box(v___y_466_);
v___f_468_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(v___f_468_, 0, v___x_467_);
if (lean_obj_tag(v_val_361_) == 0)
{
lean_object* v_type_469_; lean_object* v___x_470_; lean_object* v_mctx_471_; lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
v_type_469_ = lean_ctor_get(v_val_361_, 3);
v___x_470_ = lean_st_ref_get(v___y_343_);
v_mctx_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc_ref_n(v_mctx_471_, 2);
lean_dec(v___x_470_);
v___x_472_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
lean_ctor_set(v___x_473_, 1, v_mctx_471_);
v___x_474_ = l_Lean_Expr_hasFVar(v_type_469_);
if (v___x_474_ == 0)
{
uint8_t v___x_475_; 
v___x_475_ = l_Lean_Expr_hasMVar(v_type_469_);
if (v___x_475_ == 0)
{
lean_dec_ref(v___x_473_);
lean_dec_ref(v___f_468_);
lean_dec_ref(v___f_448_);
v_fst_379_ = v___x_475_;
v_mctx_380_ = v_mctx_471_;
goto v___jp_378_;
}
else
{
lean_object* v___x_476_; 
lean_dec_ref(v_mctx_471_);
lean_inc_ref(v_type_469_);
v___x_476_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_448_, v___f_468_, v_type_469_, v___x_473_);
v___y_396_ = v___x_476_;
goto v___jp_395_;
}
}
else
{
lean_object* v___x_477_; 
lean_dec_ref(v_mctx_471_);
lean_inc_ref(v_type_469_);
v___x_477_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_448_, v___f_468_, v_type_469_, v___x_473_);
v___y_396_ = v___x_477_;
goto v___jp_395_;
}
}
else
{
uint8_t v_nondep_478_; 
v_nondep_478_ = lean_ctor_get_uint8(v_val_361_, sizeof(void*)*5);
if (v_nondep_478_ == 0)
{
lean_object* v_type_479_; lean_object* v_value_480_; lean_object* v___x_481_; lean_object* v_mctx_482_; lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v_type_479_ = lean_ctor_get(v_val_361_, 3);
v_value_480_ = lean_ctor_get(v_val_361_, 4);
v___x_481_ = lean_st_ref_get(v___y_343_);
v_mctx_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc_ref(v_mctx_482_);
lean_dec(v___x_481_);
v___x_483_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
lean_ctor_set(v___x_484_, 1, v_mctx_482_);
v___x_485_ = l_Lean_Expr_hasFVar(v_type_479_);
if (v___x_485_ == 0)
{
uint8_t v___x_486_; 
v___x_486_ = l_Lean_Expr_hasMVar(v_type_479_);
if (v___x_486_ == 0)
{
lean_inc_ref(v_value_480_);
v___y_450_ = v_value_480_;
v___y_451_ = v___f_468_;
v_fst_452_ = v___x_486_;
v_snd_453_ = v___x_484_;
goto v___jp_449_;
}
else
{
lean_object* v___x_487_; 
lean_inc_ref(v_type_479_);
lean_inc_ref(v___f_468_);
lean_inc_ref(v___f_448_);
v___x_487_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_448_, v___f_468_, v_type_479_, v___x_484_);
lean_inc_ref(v_value_480_);
v___y_459_ = v_value_480_;
v___y_460_ = v___f_468_;
v___y_461_ = v___x_487_;
goto v___jp_458_;
}
}
else
{
lean_object* v___x_488_; 
lean_inc_ref(v_type_479_);
lean_inc_ref(v___f_468_);
lean_inc_ref(v___f_448_);
v___x_488_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_448_, v___f_468_, v_type_479_, v___x_484_);
lean_inc_ref(v_value_480_);
v___y_459_ = v_value_480_;
v___y_460_ = v___f_468_;
v___y_461_ = v___x_488_;
goto v___jp_458_;
}
}
else
{
lean_object* v_type_489_; lean_object* v___x_490_; lean_object* v_mctx_491_; lean_object* v___x_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v_type_489_ = lean_ctor_get(v_val_361_, 3);
v___x_490_ = lean_st_ref_get(v___y_343_);
v_mctx_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc_ref_n(v_mctx_491_, 2);
lean_dec(v___x_490_);
v___x_492_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
lean_ctor_set(v___x_493_, 1, v_mctx_491_);
v___x_494_ = l_Lean_Expr_hasFVar(v_type_489_);
if (v___x_494_ == 0)
{
uint8_t v___x_495_; 
v___x_495_ = l_Lean_Expr_hasMVar(v_type_489_);
if (v___x_495_ == 0)
{
lean_dec_ref(v___x_493_);
lean_dec_ref(v___f_468_);
lean_dec_ref(v___f_448_);
v_fst_425_ = v___x_495_;
v_mctx_426_ = v_mctx_491_;
goto v___jp_424_;
}
else
{
lean_object* v___x_496_; 
lean_dec_ref(v_mctx_491_);
lean_inc_ref(v_type_489_);
v___x_496_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_448_, v___f_468_, v_type_489_, v___x_493_);
v___y_442_ = v___x_496_;
goto v___jp_441_;
}
}
else
{
lean_object* v___x_497_; 
lean_dec_ref(v_mctx_491_);
lean_inc_ref(v_type_489_);
v___x_497_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_448_, v___f_468_, v_type_489_, v___x_493_);
v___y_442_ = v___x_497_;
goto v___jp_441_;
}
}
}
}
v___jp_498_:
{
if (v___y_499_ == 0)
{
if (v_ignoreLetDecls_337_ == 0)
{
lean_del_object(v___x_365_);
v___y_466_ = v_ignoreLetDecls_337_;
goto v___jp_465_;
}
else
{
uint8_t v___x_500_; 
v___x_500_ = l_Lean_LocalDecl_isLet(v_val_361_, v___y_499_);
if (v___x_500_ == 0)
{
lean_del_object(v___x_365_);
v___y_466_ = v___x_500_;
goto v___jp_465_;
}
else
{
lean_dec_ref(v___f_448_);
lean_dec(v___x_371_);
goto v___jp_367_;
}
}
}
else
{
lean_dec_ref(v___f_448_);
lean_dec(v___x_371_);
goto v___jp_367_;
}
}
}
else
{
lean_object* v___x_504_; 
lean_dec(v___x_371_);
lean_del_object(v___x_365_);
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v_fst_362_);
lean_ctor_set(v___x_504_, 1, v_snd_363_);
v_a_353_ = v___x_504_;
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
v___x_391_ = lean_st_ref_set(v___y_343_, v___x_390_);
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
v___x_415_ = lean_st_ref_set(v___y_343_, v___x_414_);
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
v___x_437_ = lean_st_ref_set(v___y_343_, v___x_436_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ignoreLetDecls_508_, lean_object* v_forbidden_509_, lean_object* v_as_510_, lean_object* v_sz_511_, lean_object* v_i_512_, lean_object* v_b_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_516_; size_t v_sz_boxed_517_; size_t v_i_boxed_518_; lean_object* v_res_519_; 
v_ignoreLetDecls_boxed_516_ = lean_unbox(v_ignoreLetDecls_508_);
v_sz_boxed_517_ = lean_unbox_usize(v_sz_511_);
lean_dec(v_sz_511_);
v_i_boxed_518_ = lean_unbox_usize(v_i_512_);
lean_dec(v_i_512_);
v_res_519_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(v_ignoreLetDecls_boxed_516_, v_forbidden_509_, v_as_510_, v_sz_boxed_517_, v_i_boxed_518_, v_b_513_, v___y_514_);
lean_dec(v___y_514_);
lean_dec_ref(v_as_510_);
lean_dec(v_forbidden_509_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1(uint8_t v_ignoreLetDecls_520_, lean_object* v_forbidden_521_, lean_object* v_as_522_, size_t v_sz_523_, size_t v_i_524_, lean_object* v_b_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
uint8_t v___x_531_; 
v___x_531_ = lean_usize_dec_lt(v_i_524_, v_sz_523_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; 
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v_b_525_);
return v___x_532_;
}
else
{
lean_object* v_snd_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_692_; 
v_snd_533_ = lean_ctor_get(v_b_525_, 1);
v_isSharedCheck_692_ = !lean_is_exclusive(v_b_525_);
if (v_isSharedCheck_692_ == 0)
{
lean_object* v_unused_693_; 
v_unused_693_ = lean_ctor_get(v_b_525_, 0);
lean_dec(v_unused_693_);
v___x_535_ = v_b_525_;
v_isShared_536_ = v_isSharedCheck_692_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_snd_533_);
lean_dec(v_b_525_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_692_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; lean_object* v_a_539_; lean_object* v_a_546_; 
v___x_537_ = lean_box(0);
v_a_546_ = lean_array_uget_borrowed(v_as_522_, v_i_524_);
if (lean_obj_tag(v_a_546_) == 0)
{
v_a_539_ = v_snd_533_;
goto v___jp_538_;
}
else
{
lean_object* v_val_547_; lean_object* v_fst_548_; lean_object* v_snd_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_691_; 
v_val_547_ = lean_ctor_get(v_a_546_, 0);
v_fst_548_ = lean_ctor_get(v_snd_533_, 0);
v_snd_549_ = lean_ctor_get(v_snd_533_, 1);
v_isSharedCheck_691_ = !lean_is_exclusive(v_snd_533_);
if (v_isSharedCheck_691_ == 0)
{
v___x_551_ = v_snd_533_;
v_isShared_552_ = v_isSharedCheck_691_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_snd_549_);
lean_inc(v_fst_548_);
lean_dec(v_snd_533_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_691_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_557_; uint8_t v_a_559_; uint8_t v_fst_565_; lean_object* v_mctx_566_; lean_object* v___y_582_; uint8_t v_fst_588_; lean_object* v_snd_589_; lean_object* v___y_606_; uint8_t v_fst_611_; lean_object* v_mctx_612_; lean_object* v___y_628_; uint8_t v___x_633_; 
v___x_557_ = l_Lean_LocalDecl_fvarId(v_val_547_);
v___x_633_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v___x_557_, v_forbidden_521_);
if (v___x_633_ == 0)
{
lean_object* v___f_634_; lean_object* v___y_636_; lean_object* v___y_637_; uint8_t v_fst_638_; lean_object* v_snd_639_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; uint8_t v___y_652_; uint8_t v___y_685_; uint8_t v___x_687_; 
lean_inc(v_fst_548_);
v___f_634_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_634_, 0, v_fst_548_);
v___x_687_ = l_Lean_LocalDecl_isAuxDecl(v_val_547_);
if (v___x_687_ == 0)
{
uint8_t v___x_688_; uint8_t v___x_689_; 
v___x_688_ = l_Lean_LocalDecl_binderInfo(v_val_547_);
v___x_689_ = l_Lean_BinderInfo_isInstImplicit(v___x_688_);
v___y_685_ = v___x_689_;
goto v___jp_684_;
}
else
{
v___y_685_ = v___x_687_;
goto v___jp_684_;
}
v___jp_635_:
{
if (v_fst_638_ == 0)
{
uint8_t v___x_640_; 
v___x_640_ = l_Lean_Expr_hasFVar(v___y_636_);
if (v___x_640_ == 0)
{
uint8_t v___x_641_; 
v___x_641_ = l_Lean_Expr_hasMVar(v___y_636_);
if (v___x_641_ == 0)
{
lean_dec_ref(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec_ref(v___f_634_);
v_fst_588_ = v___x_641_;
v_snd_589_ = v_snd_639_;
goto v___jp_587_;
}
else
{
lean_object* v___x_642_; 
v___x_642_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_634_, v___y_637_, v___y_636_, v_snd_639_);
v___y_606_ = v___x_642_;
goto v___jp_605_;
}
}
else
{
lean_object* v___x_643_; 
v___x_643_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_634_, v___y_637_, v___y_636_, v_snd_639_);
v___y_606_ = v___x_643_;
goto v___jp_605_;
}
}
else
{
lean_dec_ref(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec_ref(v___f_634_);
v_fst_588_ = v_fst_638_;
v_snd_589_ = v_snd_639_;
goto v___jp_587_;
}
}
v___jp_644_:
{
lean_object* v_fst_648_; lean_object* v_snd_649_; uint8_t v___x_650_; 
v_fst_648_ = lean_ctor_get(v___y_647_, 0);
lean_inc(v_fst_648_);
v_snd_649_ = lean_ctor_get(v___y_647_, 1);
lean_inc(v_snd_649_);
lean_dec_ref(v___y_647_);
v___x_650_ = lean_unbox(v_fst_648_);
lean_dec(v_fst_648_);
v___y_636_ = v___y_645_;
v___y_637_ = v___y_646_;
v_fst_638_ = v___x_650_;
v_snd_639_ = v_snd_649_;
goto v___jp_635_;
}
v___jp_651_:
{
lean_object* v___x_653_; lean_object* v___f_654_; 
v___x_653_ = lean_box(v___y_652_);
v___f_654_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(v___f_654_, 0, v___x_653_);
if (lean_obj_tag(v_val_547_) == 0)
{
lean_object* v_type_655_; lean_object* v___x_656_; lean_object* v_mctx_657_; lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v_type_655_ = lean_ctor_get(v_val_547_, 3);
v___x_656_ = lean_st_ref_get(v___y_527_);
v_mctx_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc_ref_n(v_mctx_657_, 2);
lean_dec(v___x_656_);
v___x_658_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
lean_ctor_set(v___x_659_, 1, v_mctx_657_);
v___x_660_ = l_Lean_Expr_hasFVar(v_type_655_);
if (v___x_660_ == 0)
{
uint8_t v___x_661_; 
v___x_661_ = l_Lean_Expr_hasMVar(v_type_655_);
if (v___x_661_ == 0)
{
lean_dec_ref(v___x_659_);
lean_dec_ref(v___f_654_);
lean_dec_ref(v___f_634_);
v_fst_565_ = v___x_661_;
v_mctx_566_ = v_mctx_657_;
goto v___jp_564_;
}
else
{
lean_object* v___x_662_; 
lean_dec_ref(v_mctx_657_);
lean_inc_ref(v_type_655_);
v___x_662_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_634_, v___f_654_, v_type_655_, v___x_659_);
v___y_582_ = v___x_662_;
goto v___jp_581_;
}
}
else
{
lean_object* v___x_663_; 
lean_dec_ref(v_mctx_657_);
lean_inc_ref(v_type_655_);
v___x_663_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_634_, v___f_654_, v_type_655_, v___x_659_);
v___y_582_ = v___x_663_;
goto v___jp_581_;
}
}
else
{
uint8_t v_nondep_664_; 
v_nondep_664_ = lean_ctor_get_uint8(v_val_547_, sizeof(void*)*5);
if (v_nondep_664_ == 0)
{
lean_object* v_type_665_; lean_object* v_value_666_; lean_object* v___x_667_; lean_object* v_mctx_668_; lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v_type_665_ = lean_ctor_get(v_val_547_, 3);
v_value_666_ = lean_ctor_get(v_val_547_, 4);
v___x_667_ = lean_st_ref_get(v___y_527_);
v_mctx_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc_ref(v_mctx_668_);
lean_dec(v___x_667_);
v___x_669_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
lean_ctor_set(v___x_670_, 1, v_mctx_668_);
v___x_671_ = l_Lean_Expr_hasFVar(v_type_665_);
if (v___x_671_ == 0)
{
uint8_t v___x_672_; 
v___x_672_ = l_Lean_Expr_hasMVar(v_type_665_);
if (v___x_672_ == 0)
{
lean_inc_ref(v_value_666_);
v___y_636_ = v_value_666_;
v___y_637_ = v___f_654_;
v_fst_638_ = v___x_672_;
v_snd_639_ = v___x_670_;
goto v___jp_635_;
}
else
{
lean_object* v___x_673_; 
lean_inc_ref(v_type_665_);
lean_inc_ref(v___f_654_);
lean_inc_ref(v___f_634_);
v___x_673_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_634_, v___f_654_, v_type_665_, v___x_670_);
lean_inc_ref(v_value_666_);
v___y_645_ = v_value_666_;
v___y_646_ = v___f_654_;
v___y_647_ = v___x_673_;
goto v___jp_644_;
}
}
else
{
lean_object* v___x_674_; 
lean_inc_ref(v_type_665_);
lean_inc_ref(v___f_654_);
lean_inc_ref(v___f_634_);
v___x_674_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_634_, v___f_654_, v_type_665_, v___x_670_);
lean_inc_ref(v_value_666_);
v___y_645_ = v_value_666_;
v___y_646_ = v___f_654_;
v___y_647_ = v___x_674_;
goto v___jp_644_;
}
}
else
{
lean_object* v_type_675_; lean_object* v___x_676_; lean_object* v_mctx_677_; lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v_type_675_ = lean_ctor_get(v_val_547_, 3);
v___x_676_ = lean_st_ref_get(v___y_527_);
v_mctx_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc_ref_n(v_mctx_677_, 2);
lean_dec(v___x_676_);
v___x_678_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
lean_ctor_set(v___x_679_, 1, v_mctx_677_);
v___x_680_ = l_Lean_Expr_hasFVar(v_type_675_);
if (v___x_680_ == 0)
{
uint8_t v___x_681_; 
v___x_681_ = l_Lean_Expr_hasMVar(v_type_675_);
if (v___x_681_ == 0)
{
lean_dec_ref(v___x_679_);
lean_dec_ref(v___f_654_);
lean_dec_ref(v___f_634_);
v_fst_611_ = v___x_681_;
v_mctx_612_ = v_mctx_677_;
goto v___jp_610_;
}
else
{
lean_object* v___x_682_; 
lean_dec_ref(v_mctx_677_);
lean_inc_ref(v_type_675_);
v___x_682_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_634_, v___f_654_, v_type_675_, v___x_679_);
v___y_628_ = v___x_682_;
goto v___jp_627_;
}
}
else
{
lean_object* v___x_683_; 
lean_dec_ref(v_mctx_677_);
lean_inc_ref(v_type_675_);
v___x_683_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_634_, v___f_654_, v_type_675_, v___x_679_);
v___y_628_ = v___x_683_;
goto v___jp_627_;
}
}
}
}
v___jp_684_:
{
if (v___y_685_ == 0)
{
if (v_ignoreLetDecls_520_ == 0)
{
lean_del_object(v___x_551_);
v___y_652_ = v_ignoreLetDecls_520_;
goto v___jp_651_;
}
else
{
uint8_t v___x_686_; 
v___x_686_ = l_Lean_LocalDecl_isLet(v_val_547_, v___y_685_);
if (v___x_686_ == 0)
{
lean_del_object(v___x_551_);
v___y_652_ = v___x_686_;
goto v___jp_651_;
}
else
{
lean_dec_ref(v___f_634_);
lean_dec(v___x_557_);
goto v___jp_553_;
}
}
}
else
{
lean_dec_ref(v___f_634_);
lean_dec(v___x_557_);
goto v___jp_553_;
}
}
}
else
{
lean_object* v___x_690_; 
lean_dec(v___x_557_);
lean_del_object(v___x_551_);
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v_fst_548_);
lean_ctor_set(v___x_690_, 1, v_snd_549_);
v_a_539_ = v___x_690_;
goto v___jp_538_;
}
v___jp_553_:
{
lean_object* v___x_555_; 
if (v_isShared_552_ == 0)
{
v___x_555_ = v___x_551_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_fst_548_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_snd_549_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
v_a_539_ = v___x_555_;
goto v___jp_538_;
}
}
v___jp_558_:
{
if (v_a_559_ == 0)
{
lean_object* v___x_560_; 
lean_dec(v___x_557_);
v___x_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_560_, 0, v_fst_548_);
lean_ctor_set(v___x_560_, 1, v_snd_549_);
v_a_539_ = v___x_560_;
goto v___jp_538_;
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
lean_inc(v___x_557_);
v___x_561_ = l_Lean_FVarIdSet_insert(v_snd_549_, v___x_557_);
v___x_562_ = l_Lean_FVarIdSet_insert(v_fst_548_, v___x_557_);
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
lean_ctor_set(v___x_563_, 1, v___x_561_);
v_a_539_ = v___x_563_;
goto v___jp_538_;
}
}
v___jp_564_:
{
lean_object* v___x_567_; lean_object* v_cache_568_; lean_object* v_zetaDeltaFVarIds_569_; lean_object* v_postponed_570_; lean_object* v_diag_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_579_; 
v___x_567_ = lean_st_ref_take(v___y_527_);
v_cache_568_ = lean_ctor_get(v___x_567_, 1);
v_zetaDeltaFVarIds_569_ = lean_ctor_get(v___x_567_, 2);
v_postponed_570_ = lean_ctor_get(v___x_567_, 3);
v_diag_571_ = lean_ctor_get(v___x_567_, 4);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_579_ == 0)
{
lean_object* v_unused_580_; 
v_unused_580_ = lean_ctor_get(v___x_567_, 0);
lean_dec(v_unused_580_);
v___x_573_ = v___x_567_;
v_isShared_574_ = v_isSharedCheck_579_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_diag_571_);
lean_inc(v_postponed_570_);
lean_inc(v_zetaDeltaFVarIds_569_);
lean_inc(v_cache_568_);
lean_dec(v___x_567_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_579_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v_mctx_566_);
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_mctx_566_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_cache_568_);
lean_ctor_set(v_reuseFailAlloc_578_, 2, v_zetaDeltaFVarIds_569_);
lean_ctor_set(v_reuseFailAlloc_578_, 3, v_postponed_570_);
lean_ctor_set(v_reuseFailAlloc_578_, 4, v_diag_571_);
v___x_576_ = v_reuseFailAlloc_578_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_577_; 
v___x_577_ = lean_st_ref_set(v___y_527_, v___x_576_);
v_a_559_ = v_fst_565_;
goto v___jp_558_;
}
}
}
v___jp_581_:
{
lean_object* v_snd_583_; lean_object* v_fst_584_; lean_object* v_mctx_585_; uint8_t v___x_586_; 
v_snd_583_ = lean_ctor_get(v___y_582_, 1);
lean_inc(v_snd_583_);
v_fst_584_ = lean_ctor_get(v___y_582_, 0);
lean_inc(v_fst_584_);
lean_dec_ref(v___y_582_);
v_mctx_585_ = lean_ctor_get(v_snd_583_, 1);
lean_inc_ref(v_mctx_585_);
lean_dec(v_snd_583_);
v___x_586_ = lean_unbox(v_fst_584_);
lean_dec(v_fst_584_);
v_fst_565_ = v___x_586_;
v_mctx_566_ = v_mctx_585_;
goto v___jp_564_;
}
v___jp_587_:
{
lean_object* v_mctx_590_; lean_object* v___x_591_; lean_object* v_cache_592_; lean_object* v_zetaDeltaFVarIds_593_; lean_object* v_postponed_594_; lean_object* v_diag_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_603_; 
v_mctx_590_ = lean_ctor_get(v_snd_589_, 1);
lean_inc_ref(v_mctx_590_);
lean_dec_ref(v_snd_589_);
v___x_591_ = lean_st_ref_take(v___y_527_);
v_cache_592_ = lean_ctor_get(v___x_591_, 1);
v_zetaDeltaFVarIds_593_ = lean_ctor_get(v___x_591_, 2);
v_postponed_594_ = lean_ctor_get(v___x_591_, 3);
v_diag_595_ = lean_ctor_get(v___x_591_, 4);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_603_ == 0)
{
lean_object* v_unused_604_; 
v_unused_604_ = lean_ctor_get(v___x_591_, 0);
lean_dec(v_unused_604_);
v___x_597_ = v___x_591_;
v_isShared_598_ = v_isSharedCheck_603_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_diag_595_);
lean_inc(v_postponed_594_);
lean_inc(v_zetaDeltaFVarIds_593_);
lean_inc(v_cache_592_);
lean_dec(v___x_591_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_603_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v_mctx_590_);
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_mctx_590_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v_cache_592_);
lean_ctor_set(v_reuseFailAlloc_602_, 2, v_zetaDeltaFVarIds_593_);
lean_ctor_set(v_reuseFailAlloc_602_, 3, v_postponed_594_);
lean_ctor_set(v_reuseFailAlloc_602_, 4, v_diag_595_);
v___x_600_ = v_reuseFailAlloc_602_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_601_; 
v___x_601_ = lean_st_ref_set(v___y_527_, v___x_600_);
v_a_559_ = v_fst_588_;
goto v___jp_558_;
}
}
}
v___jp_605_:
{
lean_object* v_fst_607_; lean_object* v_snd_608_; uint8_t v___x_609_; 
v_fst_607_ = lean_ctor_get(v___y_606_, 0);
lean_inc(v_fst_607_);
v_snd_608_ = lean_ctor_get(v___y_606_, 1);
lean_inc(v_snd_608_);
lean_dec_ref(v___y_606_);
v___x_609_ = lean_unbox(v_fst_607_);
lean_dec(v_fst_607_);
v_fst_588_ = v___x_609_;
v_snd_589_ = v_snd_608_;
goto v___jp_587_;
}
v___jp_610_:
{
lean_object* v___x_613_; lean_object* v_cache_614_; lean_object* v_zetaDeltaFVarIds_615_; lean_object* v_postponed_616_; lean_object* v_diag_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_625_; 
v___x_613_ = lean_st_ref_take(v___y_527_);
v_cache_614_ = lean_ctor_get(v___x_613_, 1);
v_zetaDeltaFVarIds_615_ = lean_ctor_get(v___x_613_, 2);
v_postponed_616_ = lean_ctor_get(v___x_613_, 3);
v_diag_617_ = lean_ctor_get(v___x_613_, 4);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_625_ == 0)
{
lean_object* v_unused_626_; 
v_unused_626_ = lean_ctor_get(v___x_613_, 0);
lean_dec(v_unused_626_);
v___x_619_ = v___x_613_;
v_isShared_620_ = v_isSharedCheck_625_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_diag_617_);
lean_inc(v_postponed_616_);
lean_inc(v_zetaDeltaFVarIds_615_);
lean_inc(v_cache_614_);
lean_dec(v___x_613_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_625_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v_mctx_612_);
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_mctx_612_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_cache_614_);
lean_ctor_set(v_reuseFailAlloc_624_, 2, v_zetaDeltaFVarIds_615_);
lean_ctor_set(v_reuseFailAlloc_624_, 3, v_postponed_616_);
lean_ctor_set(v_reuseFailAlloc_624_, 4, v_diag_617_);
v___x_622_ = v_reuseFailAlloc_624_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_623_; 
v___x_623_ = lean_st_ref_set(v___y_527_, v___x_622_);
v_a_559_ = v_fst_611_;
goto v___jp_558_;
}
}
}
v___jp_627_:
{
lean_object* v_snd_629_; lean_object* v_fst_630_; lean_object* v_mctx_631_; uint8_t v___x_632_; 
v_snd_629_ = lean_ctor_get(v___y_628_, 1);
lean_inc(v_snd_629_);
v_fst_630_ = lean_ctor_get(v___y_628_, 0);
lean_inc(v_fst_630_);
lean_dec_ref(v___y_628_);
v_mctx_631_ = lean_ctor_get(v_snd_629_, 1);
lean_inc_ref(v_mctx_631_);
lean_dec(v_snd_629_);
v___x_632_ = lean_unbox(v_fst_630_);
lean_dec(v_fst_630_);
v_fst_611_ = v___x_632_;
v_mctx_612_ = v_mctx_631_;
goto v___jp_610_;
}
}
}
v___jp_538_:
{
lean_object* v___x_541_; 
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 1, v_a_539_);
lean_ctor_set(v___x_535_, 0, v___x_537_);
v___x_541_ = v___x_535_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_537_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_a_539_);
v___x_541_ = v_reuseFailAlloc_545_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
size_t v___x_542_; size_t v___x_543_; lean_object* v___x_544_; 
v___x_542_ = ((size_t)1ULL);
v___x_543_ = lean_usize_add(v_i_524_, v___x_542_);
v___x_544_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(v_ignoreLetDecls_520_, v_forbidden_521_, v_as_522_, v_sz_523_, v___x_543_, v___x_541_, v___y_527_);
return v___x_544_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___boxed(lean_object* v_ignoreLetDecls_694_, lean_object* v_forbidden_695_, lean_object* v_as_696_, lean_object* v_sz_697_, lean_object* v_i_698_, lean_object* v_b_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_705_; size_t v_sz_boxed_706_; size_t v_i_boxed_707_; lean_object* v_res_708_; 
v_ignoreLetDecls_boxed_705_ = lean_unbox(v_ignoreLetDecls_694_);
v_sz_boxed_706_ = lean_unbox_usize(v_sz_697_);
lean_dec(v_sz_697_);
v_i_boxed_707_ = lean_unbox_usize(v_i_698_);
lean_dec(v_i_698_);
v_res_708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1(v_ignoreLetDecls_boxed_705_, v_forbidden_695_, v_as_696_, v_sz_boxed_706_, v_i_boxed_707_, v_b_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec_ref(v_as_696_);
lean_dec(v_forbidden_695_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(uint8_t v_ignoreLetDecls_709_, lean_object* v_forbidden_710_, lean_object* v_as_711_, size_t v_sz_712_, size_t v_i_713_, lean_object* v_b_714_, lean_object* v___y_715_){
_start:
{
uint8_t v___x_717_; 
v___x_717_ = lean_usize_dec_lt(v_i_713_, v_sz_712_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; 
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v_b_714_);
return v___x_718_;
}
else
{
lean_object* v_snd_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_878_; 
v_snd_719_ = lean_ctor_get(v_b_714_, 1);
v_isSharedCheck_878_ = !lean_is_exclusive(v_b_714_);
if (v_isSharedCheck_878_ == 0)
{
lean_object* v_unused_879_; 
v_unused_879_ = lean_ctor_get(v_b_714_, 0);
lean_dec(v_unused_879_);
v___x_721_ = v_b_714_;
v_isShared_722_ = v_isSharedCheck_878_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_snd_719_);
lean_dec(v_b_714_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_878_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_723_; lean_object* v_a_725_; lean_object* v_a_732_; 
v___x_723_ = lean_box(0);
v_a_732_ = lean_array_uget_borrowed(v_as_711_, v_i_713_);
if (lean_obj_tag(v_a_732_) == 0)
{
v_a_725_ = v_snd_719_;
goto v___jp_724_;
}
else
{
lean_object* v_val_733_; lean_object* v_fst_734_; lean_object* v_snd_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_877_; 
v_val_733_ = lean_ctor_get(v_a_732_, 0);
v_fst_734_ = lean_ctor_get(v_snd_719_, 0);
v_snd_735_ = lean_ctor_get(v_snd_719_, 1);
v_isSharedCheck_877_ = !lean_is_exclusive(v_snd_719_);
if (v_isSharedCheck_877_ == 0)
{
v___x_737_ = v_snd_719_;
v_isShared_738_ = v_isSharedCheck_877_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_snd_735_);
lean_inc(v_fst_734_);
lean_dec(v_snd_719_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_877_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_743_; uint8_t v_a_745_; uint8_t v_fst_751_; lean_object* v_mctx_752_; lean_object* v___y_768_; uint8_t v_fst_774_; lean_object* v_snd_775_; lean_object* v___y_792_; uint8_t v_fst_797_; lean_object* v_mctx_798_; lean_object* v___y_814_; uint8_t v___x_819_; 
v___x_743_ = l_Lean_LocalDecl_fvarId(v_val_733_);
v___x_819_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v___x_743_, v_forbidden_710_);
if (v___x_819_ == 0)
{
lean_object* v___f_820_; lean_object* v___y_822_; lean_object* v___y_823_; uint8_t v_fst_824_; lean_object* v_snd_825_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; uint8_t v___y_838_; uint8_t v___y_871_; uint8_t v___x_873_; 
lean_inc(v_fst_734_);
v___f_820_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_820_, 0, v_fst_734_);
v___x_873_ = l_Lean_LocalDecl_isAuxDecl(v_val_733_);
if (v___x_873_ == 0)
{
uint8_t v___x_874_; uint8_t v___x_875_; 
v___x_874_ = l_Lean_LocalDecl_binderInfo(v_val_733_);
v___x_875_ = l_Lean_BinderInfo_isInstImplicit(v___x_874_);
v___y_871_ = v___x_875_;
goto v___jp_870_;
}
else
{
v___y_871_ = v___x_873_;
goto v___jp_870_;
}
v___jp_821_:
{
if (v_fst_824_ == 0)
{
uint8_t v___x_826_; 
v___x_826_ = l_Lean_Expr_hasFVar(v___y_822_);
if (v___x_826_ == 0)
{
uint8_t v___x_827_; 
v___x_827_ = l_Lean_Expr_hasMVar(v___y_822_);
if (v___x_827_ == 0)
{
lean_dec_ref(v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec_ref(v___f_820_);
v_fst_774_ = v___x_827_;
v_snd_775_ = v_snd_825_;
goto v___jp_773_;
}
else
{
lean_object* v___x_828_; 
v___x_828_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_820_, v___y_823_, v___y_822_, v_snd_825_);
v___y_792_ = v___x_828_;
goto v___jp_791_;
}
}
else
{
lean_object* v___x_829_; 
v___x_829_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_820_, v___y_823_, v___y_822_, v_snd_825_);
v___y_792_ = v___x_829_;
goto v___jp_791_;
}
}
else
{
lean_dec_ref(v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec_ref(v___f_820_);
v_fst_774_ = v_fst_824_;
v_snd_775_ = v_snd_825_;
goto v___jp_773_;
}
}
v___jp_830_:
{
lean_object* v_fst_834_; lean_object* v_snd_835_; uint8_t v___x_836_; 
v_fst_834_ = lean_ctor_get(v___y_833_, 0);
lean_inc(v_fst_834_);
v_snd_835_ = lean_ctor_get(v___y_833_, 1);
lean_inc(v_snd_835_);
lean_dec_ref(v___y_833_);
v___x_836_ = lean_unbox(v_fst_834_);
lean_dec(v_fst_834_);
v___y_822_ = v___y_831_;
v___y_823_ = v___y_832_;
v_fst_824_ = v___x_836_;
v_snd_825_ = v_snd_835_;
goto v___jp_821_;
}
v___jp_837_:
{
lean_object* v___x_839_; lean_object* v___f_840_; 
v___x_839_ = lean_box(v___y_838_);
v___f_840_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(v___f_840_, 0, v___x_839_);
if (lean_obj_tag(v_val_733_) == 0)
{
lean_object* v_type_841_; lean_object* v___x_842_; lean_object* v_mctx_843_; lean_object* v___x_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v_type_841_ = lean_ctor_get(v_val_733_, 3);
v___x_842_ = lean_st_ref_get(v___y_715_);
v_mctx_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc_ref_n(v_mctx_843_, 2);
lean_dec(v___x_842_);
v___x_844_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
lean_ctor_set(v___x_845_, 1, v_mctx_843_);
v___x_846_ = l_Lean_Expr_hasFVar(v_type_841_);
if (v___x_846_ == 0)
{
uint8_t v___x_847_; 
v___x_847_ = l_Lean_Expr_hasMVar(v_type_841_);
if (v___x_847_ == 0)
{
lean_dec_ref(v___x_845_);
lean_dec_ref(v___f_840_);
lean_dec_ref(v___f_820_);
v_fst_751_ = v___x_847_;
v_mctx_752_ = v_mctx_843_;
goto v___jp_750_;
}
else
{
lean_object* v___x_848_; 
lean_dec_ref(v_mctx_843_);
lean_inc_ref(v_type_841_);
v___x_848_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_820_, v___f_840_, v_type_841_, v___x_845_);
v___y_768_ = v___x_848_;
goto v___jp_767_;
}
}
else
{
lean_object* v___x_849_; 
lean_dec_ref(v_mctx_843_);
lean_inc_ref(v_type_841_);
v___x_849_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_820_, v___f_840_, v_type_841_, v___x_845_);
v___y_768_ = v___x_849_;
goto v___jp_767_;
}
}
else
{
uint8_t v_nondep_850_; 
v_nondep_850_ = lean_ctor_get_uint8(v_val_733_, sizeof(void*)*5);
if (v_nondep_850_ == 0)
{
lean_object* v_type_851_; lean_object* v_value_852_; lean_object* v___x_853_; lean_object* v_mctx_854_; lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v_type_851_ = lean_ctor_get(v_val_733_, 3);
v_value_852_ = lean_ctor_get(v_val_733_, 4);
v___x_853_ = lean_st_ref_get(v___y_715_);
v_mctx_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc_ref(v_mctx_854_);
lean_dec(v___x_853_);
v___x_855_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
lean_ctor_set(v___x_856_, 1, v_mctx_854_);
v___x_857_ = l_Lean_Expr_hasFVar(v_type_851_);
if (v___x_857_ == 0)
{
uint8_t v___x_858_; 
v___x_858_ = l_Lean_Expr_hasMVar(v_type_851_);
if (v___x_858_ == 0)
{
lean_inc_ref(v_value_852_);
v___y_822_ = v_value_852_;
v___y_823_ = v___f_840_;
v_fst_824_ = v___x_858_;
v_snd_825_ = v___x_856_;
goto v___jp_821_;
}
else
{
lean_object* v___x_859_; 
lean_inc_ref(v_type_851_);
lean_inc_ref(v___f_840_);
lean_inc_ref(v___f_820_);
v___x_859_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_820_, v___f_840_, v_type_851_, v___x_856_);
lean_inc_ref(v_value_852_);
v___y_831_ = v_value_852_;
v___y_832_ = v___f_840_;
v___y_833_ = v___x_859_;
goto v___jp_830_;
}
}
else
{
lean_object* v___x_860_; 
lean_inc_ref(v_type_851_);
lean_inc_ref(v___f_840_);
lean_inc_ref(v___f_820_);
v___x_860_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_820_, v___f_840_, v_type_851_, v___x_856_);
lean_inc_ref(v_value_852_);
v___y_831_ = v_value_852_;
v___y_832_ = v___f_840_;
v___y_833_ = v___x_860_;
goto v___jp_830_;
}
}
else
{
lean_object* v_type_861_; lean_object* v___x_862_; lean_object* v_mctx_863_; lean_object* v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
v_type_861_ = lean_ctor_get(v_val_733_, 3);
v___x_862_ = lean_st_ref_get(v___y_715_);
v_mctx_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc_ref_n(v_mctx_863_, 2);
lean_dec(v___x_862_);
v___x_864_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
lean_ctor_set(v___x_865_, 1, v_mctx_863_);
v___x_866_ = l_Lean_Expr_hasFVar(v_type_861_);
if (v___x_866_ == 0)
{
uint8_t v___x_867_; 
v___x_867_ = l_Lean_Expr_hasMVar(v_type_861_);
if (v___x_867_ == 0)
{
lean_dec_ref(v___x_865_);
lean_dec_ref(v___f_840_);
lean_dec_ref(v___f_820_);
v_fst_797_ = v___x_867_;
v_mctx_798_ = v_mctx_863_;
goto v___jp_796_;
}
else
{
lean_object* v___x_868_; 
lean_dec_ref(v_mctx_863_);
lean_inc_ref(v_type_861_);
v___x_868_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_820_, v___f_840_, v_type_861_, v___x_865_);
v___y_814_ = v___x_868_;
goto v___jp_813_;
}
}
else
{
lean_object* v___x_869_; 
lean_dec_ref(v_mctx_863_);
lean_inc_ref(v_type_861_);
v___x_869_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_820_, v___f_840_, v_type_861_, v___x_865_);
v___y_814_ = v___x_869_;
goto v___jp_813_;
}
}
}
}
v___jp_870_:
{
if (v___y_871_ == 0)
{
if (v_ignoreLetDecls_709_ == 0)
{
lean_del_object(v___x_737_);
v___y_838_ = v_ignoreLetDecls_709_;
goto v___jp_837_;
}
else
{
uint8_t v___x_872_; 
v___x_872_ = l_Lean_LocalDecl_isLet(v_val_733_, v___y_871_);
if (v___x_872_ == 0)
{
lean_del_object(v___x_737_);
v___y_838_ = v___x_872_;
goto v___jp_837_;
}
else
{
lean_dec_ref(v___f_820_);
lean_dec(v___x_743_);
goto v___jp_739_;
}
}
}
else
{
lean_dec_ref(v___f_820_);
lean_dec(v___x_743_);
goto v___jp_739_;
}
}
}
else
{
lean_object* v___x_876_; 
lean_dec(v___x_743_);
lean_del_object(v___x_737_);
v___x_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_876_, 0, v_fst_734_);
lean_ctor_set(v___x_876_, 1, v_snd_735_);
v_a_725_ = v___x_876_;
goto v___jp_724_;
}
v___jp_739_:
{
lean_object* v___x_741_; 
if (v_isShared_738_ == 0)
{
v___x_741_ = v___x_737_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_fst_734_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_snd_735_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
v_a_725_ = v___x_741_;
goto v___jp_724_;
}
}
v___jp_744_:
{
if (v_a_745_ == 0)
{
lean_object* v___x_746_; 
lean_dec(v___x_743_);
v___x_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_746_, 0, v_fst_734_);
lean_ctor_set(v___x_746_, 1, v_snd_735_);
v_a_725_ = v___x_746_;
goto v___jp_724_;
}
else
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
lean_inc(v___x_743_);
v___x_747_ = l_Lean_FVarIdSet_insert(v_snd_735_, v___x_743_);
v___x_748_ = l_Lean_FVarIdSet_insert(v_fst_734_, v___x_743_);
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
lean_ctor_set(v___x_749_, 1, v___x_747_);
v_a_725_ = v___x_749_;
goto v___jp_724_;
}
}
v___jp_750_:
{
lean_object* v___x_753_; lean_object* v_cache_754_; lean_object* v_zetaDeltaFVarIds_755_; lean_object* v_postponed_756_; lean_object* v_diag_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_765_; 
v___x_753_ = lean_st_ref_take(v___y_715_);
v_cache_754_ = lean_ctor_get(v___x_753_, 1);
v_zetaDeltaFVarIds_755_ = lean_ctor_get(v___x_753_, 2);
v_postponed_756_ = lean_ctor_get(v___x_753_, 3);
v_diag_757_ = lean_ctor_get(v___x_753_, 4);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; 
v_unused_766_ = lean_ctor_get(v___x_753_, 0);
lean_dec(v_unused_766_);
v___x_759_ = v___x_753_;
v_isShared_760_ = v_isSharedCheck_765_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_diag_757_);
lean_inc(v_postponed_756_);
lean_inc(v_zetaDeltaFVarIds_755_);
lean_inc(v_cache_754_);
lean_dec(v___x_753_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_765_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v_mctx_752_);
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_mctx_752_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_cache_754_);
lean_ctor_set(v_reuseFailAlloc_764_, 2, v_zetaDeltaFVarIds_755_);
lean_ctor_set(v_reuseFailAlloc_764_, 3, v_postponed_756_);
lean_ctor_set(v_reuseFailAlloc_764_, 4, v_diag_757_);
v___x_762_ = v_reuseFailAlloc_764_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
lean_object* v___x_763_; 
v___x_763_ = lean_st_ref_set(v___y_715_, v___x_762_);
v_a_745_ = v_fst_751_;
goto v___jp_744_;
}
}
}
v___jp_767_:
{
lean_object* v_snd_769_; lean_object* v_fst_770_; lean_object* v_mctx_771_; uint8_t v___x_772_; 
v_snd_769_ = lean_ctor_get(v___y_768_, 1);
lean_inc(v_snd_769_);
v_fst_770_ = lean_ctor_get(v___y_768_, 0);
lean_inc(v_fst_770_);
lean_dec_ref(v___y_768_);
v_mctx_771_ = lean_ctor_get(v_snd_769_, 1);
lean_inc_ref(v_mctx_771_);
lean_dec(v_snd_769_);
v___x_772_ = lean_unbox(v_fst_770_);
lean_dec(v_fst_770_);
v_fst_751_ = v___x_772_;
v_mctx_752_ = v_mctx_771_;
goto v___jp_750_;
}
v___jp_773_:
{
lean_object* v_mctx_776_; lean_object* v___x_777_; lean_object* v_cache_778_; lean_object* v_zetaDeltaFVarIds_779_; lean_object* v_postponed_780_; lean_object* v_diag_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_789_; 
v_mctx_776_ = lean_ctor_get(v_snd_775_, 1);
lean_inc_ref(v_mctx_776_);
lean_dec_ref(v_snd_775_);
v___x_777_ = lean_st_ref_take(v___y_715_);
v_cache_778_ = lean_ctor_get(v___x_777_, 1);
v_zetaDeltaFVarIds_779_ = lean_ctor_get(v___x_777_, 2);
v_postponed_780_ = lean_ctor_get(v___x_777_, 3);
v_diag_781_ = lean_ctor_get(v___x_777_, 4);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_789_ == 0)
{
lean_object* v_unused_790_; 
v_unused_790_ = lean_ctor_get(v___x_777_, 0);
lean_dec(v_unused_790_);
v___x_783_ = v___x_777_;
v_isShared_784_ = v_isSharedCheck_789_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_diag_781_);
lean_inc(v_postponed_780_);
lean_inc(v_zetaDeltaFVarIds_779_);
lean_inc(v_cache_778_);
lean_dec(v___x_777_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_789_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v_mctx_776_);
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_mctx_776_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_cache_778_);
lean_ctor_set(v_reuseFailAlloc_788_, 2, v_zetaDeltaFVarIds_779_);
lean_ctor_set(v_reuseFailAlloc_788_, 3, v_postponed_780_);
lean_ctor_set(v_reuseFailAlloc_788_, 4, v_diag_781_);
v___x_786_ = v_reuseFailAlloc_788_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_787_; 
v___x_787_ = lean_st_ref_set(v___y_715_, v___x_786_);
v_a_745_ = v_fst_774_;
goto v___jp_744_;
}
}
}
v___jp_791_:
{
lean_object* v_fst_793_; lean_object* v_snd_794_; uint8_t v___x_795_; 
v_fst_793_ = lean_ctor_get(v___y_792_, 0);
lean_inc(v_fst_793_);
v_snd_794_ = lean_ctor_get(v___y_792_, 1);
lean_inc(v_snd_794_);
lean_dec_ref(v___y_792_);
v___x_795_ = lean_unbox(v_fst_793_);
lean_dec(v_fst_793_);
v_fst_774_ = v___x_795_;
v_snd_775_ = v_snd_794_;
goto v___jp_773_;
}
v___jp_796_:
{
lean_object* v___x_799_; lean_object* v_cache_800_; lean_object* v_zetaDeltaFVarIds_801_; lean_object* v_postponed_802_; lean_object* v_diag_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_811_; 
v___x_799_ = lean_st_ref_take(v___y_715_);
v_cache_800_ = lean_ctor_get(v___x_799_, 1);
v_zetaDeltaFVarIds_801_ = lean_ctor_get(v___x_799_, 2);
v_postponed_802_ = lean_ctor_get(v___x_799_, 3);
v_diag_803_ = lean_ctor_get(v___x_799_, 4);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_811_ == 0)
{
lean_object* v_unused_812_; 
v_unused_812_ = lean_ctor_get(v___x_799_, 0);
lean_dec(v_unused_812_);
v___x_805_ = v___x_799_;
v_isShared_806_ = v_isSharedCheck_811_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_diag_803_);
lean_inc(v_postponed_802_);
lean_inc(v_zetaDeltaFVarIds_801_);
lean_inc(v_cache_800_);
lean_dec(v___x_799_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_811_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v_mctx_798_);
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_mctx_798_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_cache_800_);
lean_ctor_set(v_reuseFailAlloc_810_, 2, v_zetaDeltaFVarIds_801_);
lean_ctor_set(v_reuseFailAlloc_810_, 3, v_postponed_802_);
lean_ctor_set(v_reuseFailAlloc_810_, 4, v_diag_803_);
v___x_808_ = v_reuseFailAlloc_810_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_809_; 
v___x_809_ = lean_st_ref_set(v___y_715_, v___x_808_);
v_a_745_ = v_fst_797_;
goto v___jp_744_;
}
}
}
v___jp_813_:
{
lean_object* v_snd_815_; lean_object* v_fst_816_; lean_object* v_mctx_817_; uint8_t v___x_818_; 
v_snd_815_ = lean_ctor_get(v___y_814_, 1);
lean_inc(v_snd_815_);
v_fst_816_ = lean_ctor_get(v___y_814_, 0);
lean_inc(v_fst_816_);
lean_dec_ref(v___y_814_);
v_mctx_817_ = lean_ctor_get(v_snd_815_, 1);
lean_inc_ref(v_mctx_817_);
lean_dec(v_snd_815_);
v___x_818_ = lean_unbox(v_fst_816_);
lean_dec(v_fst_816_);
v_fst_797_ = v___x_818_;
v_mctx_798_ = v_mctx_817_;
goto v___jp_796_;
}
}
}
v___jp_724_:
{
lean_object* v___x_727_; 
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 1, v_a_725_);
lean_ctor_set(v___x_721_, 0, v___x_723_);
v___x_727_ = v___x_721_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_723_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_a_725_);
v___x_727_ = v_reuseFailAlloc_731_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
size_t v___x_728_; size_t v___x_729_; 
v___x_728_ = ((size_t)1ULL);
v___x_729_ = lean_usize_add(v_i_713_, v___x_728_);
v_i_713_ = v___x_729_;
v_b_714_ = v___x_727_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_ignoreLetDecls_880_, lean_object* v_forbidden_881_, lean_object* v_as_882_, lean_object* v_sz_883_, lean_object* v_i_884_, lean_object* v_b_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_888_; size_t v_sz_boxed_889_; size_t v_i_boxed_890_; lean_object* v_res_891_; 
v_ignoreLetDecls_boxed_888_ = lean_unbox(v_ignoreLetDecls_880_);
v_sz_boxed_889_ = lean_unbox_usize(v_sz_883_);
lean_dec(v_sz_883_);
v_i_boxed_890_ = lean_unbox_usize(v_i_884_);
lean_dec(v_i_884_);
v_res_891_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(v_ignoreLetDecls_boxed_888_, v_forbidden_881_, v_as_882_, v_sz_boxed_889_, v_i_boxed_890_, v_b_885_, v___y_886_);
lean_dec(v___y_886_);
lean_dec_ref(v_as_882_);
lean_dec(v_forbidden_881_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2(uint8_t v_ignoreLetDecls_892_, lean_object* v_forbidden_893_, lean_object* v_as_894_, size_t v_sz_895_, size_t v_i_896_, lean_object* v_b_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
uint8_t v___x_903_; 
v___x_903_ = lean_usize_dec_lt(v_i_896_, v_sz_895_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; 
v___x_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_904_, 0, v_b_897_);
return v___x_904_;
}
else
{
lean_object* v_snd_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_1064_; 
v_snd_905_ = lean_ctor_get(v_b_897_, 1);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_b_897_);
if (v_isSharedCheck_1064_ == 0)
{
lean_object* v_unused_1065_; 
v_unused_1065_ = lean_ctor_get(v_b_897_, 0);
lean_dec(v_unused_1065_);
v___x_907_ = v_b_897_;
v_isShared_908_ = v_isSharedCheck_1064_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_snd_905_);
lean_dec(v_b_897_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_1064_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_909_; lean_object* v_a_911_; lean_object* v_a_918_; 
v___x_909_ = lean_box(0);
v_a_918_ = lean_array_uget_borrowed(v_as_894_, v_i_896_);
if (lean_obj_tag(v_a_918_) == 0)
{
v_a_911_ = v_snd_905_;
goto v___jp_910_;
}
else
{
lean_object* v_val_919_; lean_object* v_fst_920_; lean_object* v_snd_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_1063_; 
v_val_919_ = lean_ctor_get(v_a_918_, 0);
v_fst_920_ = lean_ctor_get(v_snd_905_, 0);
v_snd_921_ = lean_ctor_get(v_snd_905_, 1);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_snd_905_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_923_ = v_snd_905_;
v_isShared_924_ = v_isSharedCheck_1063_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_snd_921_);
lean_inc(v_fst_920_);
lean_dec(v_snd_905_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_1063_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_929_; uint8_t v_a_931_; uint8_t v_fst_937_; lean_object* v_mctx_938_; lean_object* v___y_954_; uint8_t v_fst_960_; lean_object* v_snd_961_; lean_object* v___y_978_; uint8_t v_fst_983_; lean_object* v_mctx_984_; lean_object* v___y_1000_; uint8_t v___x_1005_; 
v___x_929_ = l_Lean_LocalDecl_fvarId(v_val_919_);
v___x_1005_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v___x_929_, v_forbidden_893_);
if (v___x_1005_ == 0)
{
lean_object* v___f_1006_; lean_object* v___y_1008_; lean_object* v___y_1009_; uint8_t v_fst_1010_; lean_object* v_snd_1011_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; uint8_t v___y_1024_; uint8_t v___y_1057_; uint8_t v___x_1059_; 
lean_inc(v_fst_920_);
v___f_1006_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1006_, 0, v_fst_920_);
v___x_1059_ = l_Lean_LocalDecl_isAuxDecl(v_val_919_);
if (v___x_1059_ == 0)
{
uint8_t v___x_1060_; uint8_t v___x_1061_; 
v___x_1060_ = l_Lean_LocalDecl_binderInfo(v_val_919_);
v___x_1061_ = l_Lean_BinderInfo_isInstImplicit(v___x_1060_);
v___y_1057_ = v___x_1061_;
goto v___jp_1056_;
}
else
{
v___y_1057_ = v___x_1059_;
goto v___jp_1056_;
}
v___jp_1007_:
{
if (v_fst_1010_ == 0)
{
uint8_t v___x_1012_; 
v___x_1012_ = l_Lean_Expr_hasFVar(v___y_1008_);
if (v___x_1012_ == 0)
{
uint8_t v___x_1013_; 
v___x_1013_ = l_Lean_Expr_hasMVar(v___y_1008_);
if (v___x_1013_ == 0)
{
lean_dec_ref(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec_ref(v___f_1006_);
v_fst_960_ = v___x_1013_;
v_snd_961_ = v_snd_1011_;
goto v___jp_959_;
}
else
{
lean_object* v___x_1014_; 
v___x_1014_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1006_, v___y_1009_, v___y_1008_, v_snd_1011_);
v___y_978_ = v___x_1014_;
goto v___jp_977_;
}
}
else
{
lean_object* v___x_1015_; 
v___x_1015_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1006_, v___y_1009_, v___y_1008_, v_snd_1011_);
v___y_978_ = v___x_1015_;
goto v___jp_977_;
}
}
else
{
lean_dec_ref(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec_ref(v___f_1006_);
v_fst_960_ = v_fst_1010_;
v_snd_961_ = v_snd_1011_;
goto v___jp_959_;
}
}
v___jp_1016_:
{
lean_object* v_fst_1020_; lean_object* v_snd_1021_; uint8_t v___x_1022_; 
v_fst_1020_ = lean_ctor_get(v___y_1019_, 0);
lean_inc(v_fst_1020_);
v_snd_1021_ = lean_ctor_get(v___y_1019_, 1);
lean_inc(v_snd_1021_);
lean_dec_ref(v___y_1019_);
v___x_1022_ = lean_unbox(v_fst_1020_);
lean_dec(v_fst_1020_);
v___y_1008_ = v___y_1017_;
v___y_1009_ = v___y_1018_;
v_fst_1010_ = v___x_1022_;
v_snd_1011_ = v_snd_1021_;
goto v___jp_1007_;
}
v___jp_1023_:
{
lean_object* v___x_1025_; lean_object* v___f_1026_; 
v___x_1025_ = lean_box(v___y_1024_);
v___f_1026_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1026_, 0, v___x_1025_);
if (lean_obj_tag(v_val_919_) == 0)
{
lean_object* v_type_1027_; lean_object* v___x_1028_; lean_object* v_mctx_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; uint8_t v___x_1032_; 
v_type_1027_ = lean_ctor_get(v_val_919_, 3);
v___x_1028_ = lean_st_ref_get(v___y_899_);
v_mctx_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc_ref_n(v_mctx_1029_, 2);
lean_dec(v___x_1028_);
v___x_1030_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
lean_ctor_set(v___x_1031_, 1, v_mctx_1029_);
v___x_1032_ = l_Lean_Expr_hasFVar(v_type_1027_);
if (v___x_1032_ == 0)
{
uint8_t v___x_1033_; 
v___x_1033_ = l_Lean_Expr_hasMVar(v_type_1027_);
if (v___x_1033_ == 0)
{
lean_dec_ref(v___x_1031_);
lean_dec_ref(v___f_1026_);
lean_dec_ref(v___f_1006_);
v_fst_937_ = v___x_1033_;
v_mctx_938_ = v_mctx_1029_;
goto v___jp_936_;
}
else
{
lean_object* v___x_1034_; 
lean_dec_ref(v_mctx_1029_);
lean_inc_ref(v_type_1027_);
v___x_1034_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1006_, v___f_1026_, v_type_1027_, v___x_1031_);
v___y_954_ = v___x_1034_;
goto v___jp_953_;
}
}
else
{
lean_object* v___x_1035_; 
lean_dec_ref(v_mctx_1029_);
lean_inc_ref(v_type_1027_);
v___x_1035_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1006_, v___f_1026_, v_type_1027_, v___x_1031_);
v___y_954_ = v___x_1035_;
goto v___jp_953_;
}
}
else
{
uint8_t v_nondep_1036_; 
v_nondep_1036_ = lean_ctor_get_uint8(v_val_919_, sizeof(void*)*5);
if (v_nondep_1036_ == 0)
{
lean_object* v_type_1037_; lean_object* v_value_1038_; lean_object* v___x_1039_; lean_object* v_mctx_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; 
v_type_1037_ = lean_ctor_get(v_val_919_, 3);
v_value_1038_ = lean_ctor_get(v_val_919_, 4);
v___x_1039_ = lean_st_ref_get(v___y_899_);
v_mctx_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc_ref(v_mctx_1040_);
lean_dec(v___x_1039_);
v___x_1041_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
lean_ctor_set(v___x_1042_, 1, v_mctx_1040_);
v___x_1043_ = l_Lean_Expr_hasFVar(v_type_1037_);
if (v___x_1043_ == 0)
{
uint8_t v___x_1044_; 
v___x_1044_ = l_Lean_Expr_hasMVar(v_type_1037_);
if (v___x_1044_ == 0)
{
lean_inc_ref(v_value_1038_);
v___y_1008_ = v_value_1038_;
v___y_1009_ = v___f_1026_;
v_fst_1010_ = v___x_1044_;
v_snd_1011_ = v___x_1042_;
goto v___jp_1007_;
}
else
{
lean_object* v___x_1045_; 
lean_inc_ref(v_type_1037_);
lean_inc_ref(v___f_1026_);
lean_inc_ref(v___f_1006_);
v___x_1045_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1006_, v___f_1026_, v_type_1037_, v___x_1042_);
lean_inc_ref(v_value_1038_);
v___y_1017_ = v_value_1038_;
v___y_1018_ = v___f_1026_;
v___y_1019_ = v___x_1045_;
goto v___jp_1016_;
}
}
else
{
lean_object* v___x_1046_; 
lean_inc_ref(v_type_1037_);
lean_inc_ref(v___f_1026_);
lean_inc_ref(v___f_1006_);
v___x_1046_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1006_, v___f_1026_, v_type_1037_, v___x_1042_);
lean_inc_ref(v_value_1038_);
v___y_1017_ = v_value_1038_;
v___y_1018_ = v___f_1026_;
v___y_1019_ = v___x_1046_;
goto v___jp_1016_;
}
}
else
{
lean_object* v_type_1047_; lean_object* v___x_1048_; lean_object* v_mctx_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v_type_1047_ = lean_ctor_get(v_val_919_, 3);
v___x_1048_ = lean_st_ref_get(v___y_899_);
v_mctx_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc_ref_n(v_mctx_1049_, 2);
lean_dec(v___x_1048_);
v___x_1050_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
lean_ctor_set(v___x_1051_, 1, v_mctx_1049_);
v___x_1052_ = l_Lean_Expr_hasFVar(v_type_1047_);
if (v___x_1052_ == 0)
{
uint8_t v___x_1053_; 
v___x_1053_ = l_Lean_Expr_hasMVar(v_type_1047_);
if (v___x_1053_ == 0)
{
lean_dec_ref(v___x_1051_);
lean_dec_ref(v___f_1026_);
lean_dec_ref(v___f_1006_);
v_fst_983_ = v___x_1053_;
v_mctx_984_ = v_mctx_1049_;
goto v___jp_982_;
}
else
{
lean_object* v___x_1054_; 
lean_dec_ref(v_mctx_1049_);
lean_inc_ref(v_type_1047_);
v___x_1054_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1006_, v___f_1026_, v_type_1047_, v___x_1051_);
v___y_1000_ = v___x_1054_;
goto v___jp_999_;
}
}
else
{
lean_object* v___x_1055_; 
lean_dec_ref(v_mctx_1049_);
lean_inc_ref(v_type_1047_);
v___x_1055_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1006_, v___f_1026_, v_type_1047_, v___x_1051_);
v___y_1000_ = v___x_1055_;
goto v___jp_999_;
}
}
}
}
v___jp_1056_:
{
if (v___y_1057_ == 0)
{
if (v_ignoreLetDecls_892_ == 0)
{
lean_del_object(v___x_923_);
v___y_1024_ = v_ignoreLetDecls_892_;
goto v___jp_1023_;
}
else
{
uint8_t v___x_1058_; 
v___x_1058_ = l_Lean_LocalDecl_isLet(v_val_919_, v___y_1057_);
if (v___x_1058_ == 0)
{
lean_del_object(v___x_923_);
v___y_1024_ = v___x_1058_;
goto v___jp_1023_;
}
else
{
lean_dec_ref(v___f_1006_);
lean_dec(v___x_929_);
goto v___jp_925_;
}
}
}
else
{
lean_dec_ref(v___f_1006_);
lean_dec(v___x_929_);
goto v___jp_925_;
}
}
}
else
{
lean_object* v___x_1062_; 
lean_dec(v___x_929_);
lean_del_object(v___x_923_);
v___x_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1062_, 0, v_fst_920_);
lean_ctor_set(v___x_1062_, 1, v_snd_921_);
v_a_911_ = v___x_1062_;
goto v___jp_910_;
}
v___jp_925_:
{
lean_object* v___x_927_; 
if (v_isShared_924_ == 0)
{
v___x_927_ = v___x_923_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_fst_920_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v_snd_921_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
v_a_911_ = v___x_927_;
goto v___jp_910_;
}
}
v___jp_930_:
{
if (v_a_931_ == 0)
{
lean_object* v___x_932_; 
lean_dec(v___x_929_);
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v_fst_920_);
lean_ctor_set(v___x_932_, 1, v_snd_921_);
v_a_911_ = v___x_932_;
goto v___jp_910_;
}
else
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
lean_inc(v___x_929_);
v___x_933_ = l_Lean_FVarIdSet_insert(v_snd_921_, v___x_929_);
v___x_934_ = l_Lean_FVarIdSet_insert(v_fst_920_, v___x_929_);
v___x_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
lean_ctor_set(v___x_935_, 1, v___x_933_);
v_a_911_ = v___x_935_;
goto v___jp_910_;
}
}
v___jp_936_:
{
lean_object* v___x_939_; lean_object* v_cache_940_; lean_object* v_zetaDeltaFVarIds_941_; lean_object* v_postponed_942_; lean_object* v_diag_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_951_; 
v___x_939_ = lean_st_ref_take(v___y_899_);
v_cache_940_ = lean_ctor_get(v___x_939_, 1);
v_zetaDeltaFVarIds_941_ = lean_ctor_get(v___x_939_, 2);
v_postponed_942_ = lean_ctor_get(v___x_939_, 3);
v_diag_943_ = lean_ctor_get(v___x_939_, 4);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_951_ == 0)
{
lean_object* v_unused_952_; 
v_unused_952_ = lean_ctor_get(v___x_939_, 0);
lean_dec(v_unused_952_);
v___x_945_ = v___x_939_;
v_isShared_946_ = v_isSharedCheck_951_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_diag_943_);
lean_inc(v_postponed_942_);
lean_inc(v_zetaDeltaFVarIds_941_);
lean_inc(v_cache_940_);
lean_dec(v___x_939_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_951_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v_mctx_938_);
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_mctx_938_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_cache_940_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_zetaDeltaFVarIds_941_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v_postponed_942_);
lean_ctor_set(v_reuseFailAlloc_950_, 4, v_diag_943_);
v___x_948_ = v_reuseFailAlloc_950_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_949_; 
v___x_949_ = lean_st_ref_set(v___y_899_, v___x_948_);
v_a_931_ = v_fst_937_;
goto v___jp_930_;
}
}
}
v___jp_953_:
{
lean_object* v_snd_955_; lean_object* v_fst_956_; lean_object* v_mctx_957_; uint8_t v___x_958_; 
v_snd_955_ = lean_ctor_get(v___y_954_, 1);
lean_inc(v_snd_955_);
v_fst_956_ = lean_ctor_get(v___y_954_, 0);
lean_inc(v_fst_956_);
lean_dec_ref(v___y_954_);
v_mctx_957_ = lean_ctor_get(v_snd_955_, 1);
lean_inc_ref(v_mctx_957_);
lean_dec(v_snd_955_);
v___x_958_ = lean_unbox(v_fst_956_);
lean_dec(v_fst_956_);
v_fst_937_ = v___x_958_;
v_mctx_938_ = v_mctx_957_;
goto v___jp_936_;
}
v___jp_959_:
{
lean_object* v_mctx_962_; lean_object* v___x_963_; lean_object* v_cache_964_; lean_object* v_zetaDeltaFVarIds_965_; lean_object* v_postponed_966_; lean_object* v_diag_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_975_; 
v_mctx_962_ = lean_ctor_get(v_snd_961_, 1);
lean_inc_ref(v_mctx_962_);
lean_dec_ref(v_snd_961_);
v___x_963_ = lean_st_ref_take(v___y_899_);
v_cache_964_ = lean_ctor_get(v___x_963_, 1);
v_zetaDeltaFVarIds_965_ = lean_ctor_get(v___x_963_, 2);
v_postponed_966_ = lean_ctor_get(v___x_963_, 3);
v_diag_967_ = lean_ctor_get(v___x_963_, 4);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_975_ == 0)
{
lean_object* v_unused_976_; 
v_unused_976_ = lean_ctor_get(v___x_963_, 0);
lean_dec(v_unused_976_);
v___x_969_ = v___x_963_;
v_isShared_970_ = v_isSharedCheck_975_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_diag_967_);
lean_inc(v_postponed_966_);
lean_inc(v_zetaDeltaFVarIds_965_);
lean_inc(v_cache_964_);
lean_dec(v___x_963_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_975_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 0, v_mctx_962_);
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_mctx_962_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_cache_964_);
lean_ctor_set(v_reuseFailAlloc_974_, 2, v_zetaDeltaFVarIds_965_);
lean_ctor_set(v_reuseFailAlloc_974_, 3, v_postponed_966_);
lean_ctor_set(v_reuseFailAlloc_974_, 4, v_diag_967_);
v___x_972_ = v_reuseFailAlloc_974_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
lean_object* v___x_973_; 
v___x_973_ = lean_st_ref_set(v___y_899_, v___x_972_);
v_a_931_ = v_fst_960_;
goto v___jp_930_;
}
}
}
v___jp_977_:
{
lean_object* v_fst_979_; lean_object* v_snd_980_; uint8_t v___x_981_; 
v_fst_979_ = lean_ctor_get(v___y_978_, 0);
lean_inc(v_fst_979_);
v_snd_980_ = lean_ctor_get(v___y_978_, 1);
lean_inc(v_snd_980_);
lean_dec_ref(v___y_978_);
v___x_981_ = lean_unbox(v_fst_979_);
lean_dec(v_fst_979_);
v_fst_960_ = v___x_981_;
v_snd_961_ = v_snd_980_;
goto v___jp_959_;
}
v___jp_982_:
{
lean_object* v___x_985_; lean_object* v_cache_986_; lean_object* v_zetaDeltaFVarIds_987_; lean_object* v_postponed_988_; lean_object* v_diag_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_997_; 
v___x_985_ = lean_st_ref_take(v___y_899_);
v_cache_986_ = lean_ctor_get(v___x_985_, 1);
v_zetaDeltaFVarIds_987_ = lean_ctor_get(v___x_985_, 2);
v_postponed_988_ = lean_ctor_get(v___x_985_, 3);
v_diag_989_ = lean_ctor_get(v___x_985_, 4);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_997_ == 0)
{
lean_object* v_unused_998_; 
v_unused_998_ = lean_ctor_get(v___x_985_, 0);
lean_dec(v_unused_998_);
v___x_991_ = v___x_985_;
v_isShared_992_ = v_isSharedCheck_997_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_diag_989_);
lean_inc(v_postponed_988_);
lean_inc(v_zetaDeltaFVarIds_987_);
lean_inc(v_cache_986_);
lean_dec(v___x_985_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_997_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v_mctx_984_);
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_mctx_984_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v_cache_986_);
lean_ctor_set(v_reuseFailAlloc_996_, 2, v_zetaDeltaFVarIds_987_);
lean_ctor_set(v_reuseFailAlloc_996_, 3, v_postponed_988_);
lean_ctor_set(v_reuseFailAlloc_996_, 4, v_diag_989_);
v___x_994_ = v_reuseFailAlloc_996_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
lean_object* v___x_995_; 
v___x_995_ = lean_st_ref_set(v___y_899_, v___x_994_);
v_a_931_ = v_fst_983_;
goto v___jp_930_;
}
}
}
v___jp_999_:
{
lean_object* v_snd_1001_; lean_object* v_fst_1002_; lean_object* v_mctx_1003_; uint8_t v___x_1004_; 
v_snd_1001_ = lean_ctor_get(v___y_1000_, 1);
lean_inc(v_snd_1001_);
v_fst_1002_ = lean_ctor_get(v___y_1000_, 0);
lean_inc(v_fst_1002_);
lean_dec_ref(v___y_1000_);
v_mctx_1003_ = lean_ctor_get(v_snd_1001_, 1);
lean_inc_ref(v_mctx_1003_);
lean_dec(v_snd_1001_);
v___x_1004_ = lean_unbox(v_fst_1002_);
lean_dec(v_fst_1002_);
v_fst_983_ = v___x_1004_;
v_mctx_984_ = v_mctx_1003_;
goto v___jp_982_;
}
}
}
v___jp_910_:
{
lean_object* v___x_913_; 
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 1, v_a_911_);
lean_ctor_set(v___x_907_, 0, v___x_909_);
v___x_913_ = v___x_907_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v_a_911_);
v___x_913_ = v_reuseFailAlloc_917_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
size_t v___x_914_; size_t v___x_915_; lean_object* v___x_916_; 
v___x_914_ = ((size_t)1ULL);
v___x_915_ = lean_usize_add(v_i_896_, v___x_914_);
v___x_916_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(v_ignoreLetDecls_892_, v_forbidden_893_, v_as_894_, v_sz_895_, v___x_915_, v___x_913_, v___y_899_);
return v___x_916_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2___boxed(lean_object* v_ignoreLetDecls_1066_, lean_object* v_forbidden_1067_, lean_object* v_as_1068_, lean_object* v_sz_1069_, lean_object* v_i_1070_, lean_object* v_b_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1077_; size_t v_sz_boxed_1078_; size_t v_i_boxed_1079_; lean_object* v_res_1080_; 
v_ignoreLetDecls_boxed_1077_ = lean_unbox(v_ignoreLetDecls_1066_);
v_sz_boxed_1078_ = lean_unbox_usize(v_sz_1069_);
lean_dec(v_sz_1069_);
v_i_boxed_1079_ = lean_unbox_usize(v_i_1070_);
lean_dec(v_i_1070_);
v_res_1080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2(v_ignoreLetDecls_boxed_1077_, v_forbidden_1067_, v_as_1068_, v_sz_boxed_1078_, v_i_boxed_1079_, v_b_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec_ref(v_as_1068_);
lean_dec(v_forbidden_1067_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(lean_object* v_init_1081_, uint8_t v_ignoreLetDecls_1082_, lean_object* v_forbidden_1083_, lean_object* v_n_1084_, lean_object* v_b_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
if (lean_obj_tag(v_n_1084_) == 0)
{
lean_object* v_cs_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1125_; 
v_cs_1091_ = lean_ctor_get(v_n_1084_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_n_1084_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1093_ = v_n_1084_;
v_isShared_1094_ = v_isSharedCheck_1125_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_cs_1091_);
lean_dec(v_n_1084_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1125_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; size_t v_sz_1097_; size_t v___x_1098_; lean_object* v___x_1099_; 
v___x_1095_ = lean_box(0);
v___x_1096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
lean_ctor_set(v___x_1096_, 1, v_b_1085_);
v_sz_1097_ = lean_array_size(v_cs_1091_);
v___x_1098_ = ((size_t)0ULL);
v___x_1099_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(v_init_1081_, v_ignoreLetDecls_1082_, v_forbidden_1083_, v_cs_1091_, v_sz_1097_, v___x_1098_, v___x_1096_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
lean_dec_ref(v_cs_1091_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1116_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1102_ = v___x_1099_;
v_isShared_1103_ = v_isSharedCheck_1116_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1099_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1116_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v_fst_1104_; 
v_fst_1104_ = lean_ctor_get(v_a_1100_, 0);
if (lean_obj_tag(v_fst_1104_) == 0)
{
lean_object* v_snd_1105_; lean_object* v___x_1107_; 
v_snd_1105_ = lean_ctor_get(v_a_1100_, 1);
lean_inc(v_snd_1105_);
lean_dec(v_a_1100_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set_tag(v___x_1093_, 1);
lean_ctor_set(v___x_1093_, 0, v_snd_1105_);
v___x_1107_ = v___x_1093_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_snd_1105_);
v___x_1107_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_object* v___x_1109_; 
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 0, v___x_1107_);
v___x_1109_ = v___x_1102_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1107_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
else
{
lean_object* v_val_1112_; lean_object* v___x_1114_; 
lean_inc_ref(v_fst_1104_);
lean_dec(v_a_1100_);
lean_del_object(v___x_1093_);
v_val_1112_ = lean_ctor_get(v_fst_1104_, 0);
lean_inc(v_val_1112_);
lean_dec_ref(v_fst_1104_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 0, v_val_1112_);
v___x_1114_ = v___x_1102_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_val_1112_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_del_object(v___x_1093_);
v_a_1117_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1099_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1099_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
else
{
lean_object* v_vs_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1160_; 
v_vs_1126_ = lean_ctor_get(v_n_1084_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_n_1084_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1128_ = v_n_1084_;
v_isShared_1129_ = v_isSharedCheck_1160_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_vs_1126_);
lean_dec(v_n_1084_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1160_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; size_t v_sz_1132_; size_t v___x_1133_; lean_object* v___x_1134_; 
v___x_1130_ = lean_box(0);
v___x_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
lean_ctor_set(v___x_1131_, 1, v_b_1085_);
v_sz_1132_ = lean_array_size(v_vs_1126_);
v___x_1133_ = ((size_t)0ULL);
v___x_1134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2(v_ignoreLetDecls_1082_, v_forbidden_1083_, v_vs_1126_, v_sz_1132_, v___x_1133_, v___x_1131_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
lean_dec_ref(v_vs_1126_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1151_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1137_ = v___x_1134_;
v_isShared_1138_ = v_isSharedCheck_1151_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1134_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1151_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v_fst_1139_; 
v_fst_1139_ = lean_ctor_get(v_a_1135_, 0);
if (lean_obj_tag(v_fst_1139_) == 0)
{
lean_object* v_snd_1140_; lean_object* v___x_1142_; 
v_snd_1140_ = lean_ctor_get(v_a_1135_, 1);
lean_inc(v_snd_1140_);
lean_dec(v_a_1135_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 0, v_snd_1140_);
v___x_1142_ = v___x_1128_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_snd_1140_);
v___x_1142_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1144_; 
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1142_);
v___x_1144_ = v___x_1137_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1142_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
else
{
lean_object* v_val_1147_; lean_object* v___x_1149_; 
lean_inc_ref(v_fst_1139_);
lean_dec(v_a_1135_);
lean_del_object(v___x_1128_);
v_val_1147_ = lean_ctor_get(v_fst_1139_, 0);
lean_inc(v_val_1147_);
lean_dec_ref(v_fst_1139_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v_val_1147_);
v___x_1149_ = v___x_1137_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_val_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_del_object(v___x_1128_);
v_a_1152_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1134_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1134_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(lean_object* v_init_1161_, uint8_t v_ignoreLetDecls_1162_, lean_object* v_forbidden_1163_, lean_object* v_as_1164_, size_t v_sz_1165_, size_t v_i_1166_, lean_object* v_b_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
uint8_t v___x_1173_; 
v___x_1173_ = lean_usize_dec_lt(v_i_1166_, v_sz_1165_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; 
v___x_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1174_, 0, v_b_1167_);
return v___x_1174_;
}
else
{
lean_object* v_snd_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1209_; 
v_snd_1175_ = lean_ctor_get(v_b_1167_, 1);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_b_1167_);
if (v_isSharedCheck_1209_ == 0)
{
lean_object* v_unused_1210_; 
v_unused_1210_ = lean_ctor_get(v_b_1167_, 0);
lean_dec(v_unused_1210_);
v___x_1177_ = v_b_1167_;
v_isShared_1178_ = v_isSharedCheck_1209_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_snd_1175_);
lean_dec(v_b_1167_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1209_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v_a_1179_; lean_object* v___x_1180_; 
v_a_1179_ = lean_array_uget_borrowed(v_as_1164_, v_i_1166_);
lean_inc(v_snd_1175_);
lean_inc(v_a_1179_);
v___x_1180_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(v_init_1161_, v_ignoreLetDecls_1162_, v_forbidden_1163_, v_a_1179_, v_snd_1175_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1200_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1183_ = v___x_1180_;
v_isShared_1184_ = v_isSharedCheck_1200_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1180_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1200_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
if (lean_obj_tag(v_a_1181_) == 0)
{
lean_object* v___x_1185_; lean_object* v___x_1187_; 
v___x_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1185_, 0, v_a_1181_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v___x_1185_);
v___x_1187_ = v___x_1177_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1185_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v_snd_1175_);
v___x_1187_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1189_; 
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 0, v___x_1187_);
v___x_1189_ = v___x_1183_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1193_; lean_object* v___x_1195_; 
lean_del_object(v___x_1183_);
lean_dec(v_snd_1175_);
v_a_1192_ = lean_ctor_get(v_a_1181_, 0);
lean_inc(v_a_1192_);
lean_dec_ref(v_a_1181_);
v___x_1193_ = lean_box(0);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 1, v_a_1192_);
lean_ctor_set(v___x_1177_, 0, v___x_1193_);
v___x_1195_ = v___x_1177_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v_a_1192_);
v___x_1195_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
size_t v___x_1196_; size_t v___x_1197_; 
v___x_1196_ = ((size_t)1ULL);
v___x_1197_ = lean_usize_add(v_i_1166_, v___x_1196_);
v_i_1166_ = v___x_1197_;
v_b_1167_ = v___x_1195_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
lean_del_object(v___x_1177_);
lean_dec(v_snd_1175_);
v_a_1201_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1180_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1180_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1___boxed(lean_object* v_init_1211_, lean_object* v_ignoreLetDecls_1212_, lean_object* v_forbidden_1213_, lean_object* v_as_1214_, lean_object* v_sz_1215_, lean_object* v_i_1216_, lean_object* v_b_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1223_; size_t v_sz_boxed_1224_; size_t v_i_boxed_1225_; lean_object* v_res_1226_; 
v_ignoreLetDecls_boxed_1223_ = lean_unbox(v_ignoreLetDecls_1212_);
v_sz_boxed_1224_ = lean_unbox_usize(v_sz_1215_);
lean_dec(v_sz_1215_);
v_i_boxed_1225_ = lean_unbox_usize(v_i_1216_);
lean_dec(v_i_1216_);
v_res_1226_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(v_init_1211_, v_ignoreLetDecls_boxed_1223_, v_forbidden_1213_, v_as_1214_, v_sz_boxed_1224_, v_i_boxed_1225_, v_b_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec_ref(v_as_1214_);
lean_dec(v_forbidden_1213_);
lean_dec_ref(v_init_1211_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0___boxed(lean_object* v_init_1227_, lean_object* v_ignoreLetDecls_1228_, lean_object* v_forbidden_1229_, lean_object* v_n_1230_, lean_object* v_b_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1237_; lean_object* v_res_1238_; 
v_ignoreLetDecls_boxed_1237_ = lean_unbox(v_ignoreLetDecls_1228_);
v_res_1238_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(v_init_1227_, v_ignoreLetDecls_boxed_1237_, v_forbidden_1229_, v_n_1230_, v_b_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v_forbidden_1229_);
lean_dec_ref(v_init_1227_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0(uint8_t v_ignoreLetDecls_1239_, lean_object* v_forbidden_1240_, lean_object* v_t_1241_, lean_object* v_init_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v_root_1248_; lean_object* v_tail_1249_; lean_object* v___x_1250_; 
v_root_1248_ = lean_ctor_get(v_t_1241_, 0);
lean_inc_ref(v_root_1248_);
v_tail_1249_ = lean_ctor_get(v_t_1241_, 1);
lean_inc_ref(v_tail_1249_);
lean_dec_ref(v_t_1241_);
lean_inc_ref(v_init_1242_);
v___x_1250_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(v_init_1242_, v_ignoreLetDecls_1239_, v_forbidden_1240_, v_root_1248_, v_init_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
lean_dec_ref(v_init_1242_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1287_; 
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1253_ = v___x_1250_;
v_isShared_1254_ = v_isSharedCheck_1287_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1250_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1287_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
if (lean_obj_tag(v_a_1251_) == 0)
{
lean_object* v_a_1255_; lean_object* v___x_1257_; 
lean_dec_ref(v_tail_1249_);
v_a_1255_ = lean_ctor_get(v_a_1251_, 0);
lean_inc(v_a_1255_);
lean_dec_ref(v_a_1251_);
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 0, v_a_1255_);
v___x_1257_ = v___x_1253_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1255_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; size_t v_sz_1262_; size_t v___x_1263_; lean_object* v___x_1264_; 
lean_del_object(v___x_1253_);
v_a_1259_ = lean_ctor_get(v_a_1251_, 0);
lean_inc(v_a_1259_);
lean_dec_ref(v_a_1251_);
v___x_1260_ = lean_box(0);
v___x_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
lean_ctor_set(v___x_1261_, 1, v_a_1259_);
v_sz_1262_ = lean_array_size(v_tail_1249_);
v___x_1263_ = ((size_t)0ULL);
v___x_1264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1(v_ignoreLetDecls_1239_, v_forbidden_1240_, v_tail_1249_, v_sz_1262_, v___x_1263_, v___x_1261_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
lean_dec_ref(v_tail_1249_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1278_; 
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1267_ = v___x_1264_;
v_isShared_1268_ = v_isSharedCheck_1278_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1264_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1278_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v_fst_1269_; 
v_fst_1269_ = lean_ctor_get(v_a_1265_, 0);
if (lean_obj_tag(v_fst_1269_) == 0)
{
lean_object* v_snd_1270_; lean_object* v___x_1272_; 
v_snd_1270_ = lean_ctor_get(v_a_1265_, 1);
lean_inc(v_snd_1270_);
lean_dec(v_a_1265_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v_snd_1270_);
v___x_1272_ = v___x_1267_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_snd_1270_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
else
{
lean_object* v_val_1274_; lean_object* v___x_1276_; 
lean_inc_ref(v_fst_1269_);
lean_dec(v_a_1265_);
v_val_1274_ = lean_ctor_get(v_fst_1269_, 0);
lean_inc(v_val_1274_);
lean_dec_ref(v_fst_1269_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v_val_1274_);
v___x_1276_ = v___x_1267_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_val_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
else
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1286_; 
v_a_1279_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1281_ = v___x_1264_;
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1264_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec_ref(v_tail_1249_);
v_a_1288_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1250_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1250_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0___boxed(lean_object* v_ignoreLetDecls_1296_, lean_object* v_forbidden_1297_, lean_object* v_t_1298_, lean_object* v_init_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1305_; lean_object* v_res_1306_; 
v_ignoreLetDecls_boxed_1305_ = lean_unbox(v_ignoreLetDecls_1296_);
v_res_1306_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0(v_ignoreLetDecls_boxed_1305_, v_forbidden_1297_, v_t_1298_, v_init_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v_forbidden_1297_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(lean_object* v_as_1307_, size_t v_i_1308_, size_t v_stop_1309_, lean_object* v_b_1310_){
_start:
{
lean_object* v___y_1312_; uint8_t v___x_1316_; 
v___x_1316_ = lean_usize_dec_eq(v_i_1308_, v_stop_1309_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1317_ = lean_array_uget_borrowed(v_as_1307_, v_i_1308_);
v___x_1318_ = l_Lean_Expr_isFVar(v___x_1317_);
if (v___x_1318_ == 0)
{
v___y_1312_ = v_b_1310_;
goto v___jp_1311_;
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = l_Lean_Expr_fvarId_x21(v___x_1317_);
v___x_1320_ = l_Lean_FVarIdSet_insert(v_b_1310_, v___x_1319_);
v___y_1312_ = v___x_1320_;
goto v___jp_1311_;
}
}
else
{
return v_b_1310_;
}
v___jp_1311_:
{
size_t v___x_1313_; size_t v___x_1314_; 
v___x_1313_ = ((size_t)1ULL);
v___x_1314_ = lean_usize_add(v_i_1308_, v___x_1313_);
v_i_1308_ = v___x_1314_;
v_b_1310_ = v___y_1312_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1___boxed(lean_object* v_as_1321_, lean_object* v_i_1322_, lean_object* v_stop_1323_, lean_object* v_b_1324_){
_start:
{
size_t v_i_boxed_1325_; size_t v_stop_boxed_1326_; lean_object* v_res_1327_; 
v_i_boxed_1325_ = lean_unbox_usize(v_i_1322_);
lean_dec(v_i_1322_);
v_stop_boxed_1326_ = lean_unbox_usize(v_stop_1323_);
lean_dec(v_stop_1323_);
v_res_1327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(v_as_1321_, v_i_boxed_1325_, v_stop_boxed_1326_, v_b_1324_);
lean_dec_ref(v_as_1321_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize(lean_object* v_targets_1328_, lean_object* v_forbidden_1329_, uint8_t v_ignoreLetDecls_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v_r_1336_; lean_object* v___y_1338_; lean_object* v___x_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; 
v_r_1336_ = lean_box(1);
v___x_1360_ = lean_unsigned_to_nat(0u);
v___x_1361_ = lean_array_get_size(v_targets_1328_);
v___x_1362_ = lean_nat_dec_lt(v___x_1360_, v___x_1361_);
if (v___x_1362_ == 0)
{
v___y_1338_ = v_r_1336_;
goto v___jp_1337_;
}
else
{
uint8_t v___x_1363_; 
v___x_1363_ = lean_nat_dec_le(v___x_1361_, v___x_1361_);
if (v___x_1363_ == 0)
{
if (v___x_1362_ == 0)
{
v___y_1338_ = v_r_1336_;
goto v___jp_1337_;
}
else
{
size_t v___x_1364_; size_t v___x_1365_; lean_object* v___x_1366_; 
v___x_1364_ = ((size_t)0ULL);
v___x_1365_ = lean_usize_of_nat(v___x_1361_);
v___x_1366_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(v_targets_1328_, v___x_1364_, v___x_1365_, v_r_1336_);
v___y_1338_ = v___x_1366_;
goto v___jp_1337_;
}
}
else
{
size_t v___x_1367_; size_t v___x_1368_; lean_object* v___x_1369_; 
v___x_1367_ = ((size_t)0ULL);
v___x_1368_ = lean_usize_of_nat(v___x_1361_);
v___x_1369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(v_targets_1328_, v___x_1367_, v___x_1368_, v_r_1336_);
v___y_1338_ = v___x_1369_;
goto v___jp_1337_;
}
}
v___jp_1337_:
{
lean_object* v_lctx_1339_; lean_object* v_decls_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v_lctx_1339_ = lean_ctor_get(v_a_1331_, 2);
v_decls_1340_ = lean_ctor_get(v_lctx_1339_, 1);
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v___y_1338_);
lean_ctor_set(v___x_1341_, 1, v_r_1336_);
lean_inc_ref(v_decls_1340_);
v___x_1342_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0(v_ignoreLetDecls_1330_, v_forbidden_1329_, v_decls_1340_, v___x_1341_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1351_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1345_ = v___x_1342_;
v_isShared_1346_ = v_isSharedCheck_1351_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1342_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1351_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v_snd_1347_; lean_object* v___x_1349_; 
v_snd_1347_ = lean_ctor_get(v_a_1343_, 1);
lean_inc(v_snd_1347_);
lean_dec(v_a_1343_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v_snd_1347_);
v___x_1349_ = v___x_1345_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_snd_1347_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
v_a_1352_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1342_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1342_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize___boxed(lean_object* v_targets_1370_, lean_object* v_forbidden_1371_, lean_object* v_ignoreLetDecls_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1378_; lean_object* v_res_1379_; 
v_ignoreLetDecls_boxed_1378_ = lean_unbox(v_ignoreLetDecls_1372_);
v_res_1379_ = l_Lean_Meta_getFVarSetToGeneralize(v_targets_1370_, v_forbidden_1371_, v_ignoreLetDecls_boxed_1378_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_);
lean_dec(v_a_1376_);
lean_dec_ref(v_a_1375_);
lean_dec(v_a_1374_);
lean_dec_ref(v_a_1373_);
lean_dec(v_forbidden_1371_);
lean_dec_ref(v_targets_1370_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4(uint8_t v_ignoreLetDecls_1380_, lean_object* v_forbidden_1381_, lean_object* v_as_1382_, size_t v_sz_1383_, size_t v_i_1384_, lean_object* v_b_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(v_ignoreLetDecls_1380_, v_forbidden_1381_, v_as_1382_, v_sz_1383_, v_i_1384_, v_b_1385_, v___y_1387_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___boxed(lean_object* v_ignoreLetDecls_1392_, lean_object* v_forbidden_1393_, lean_object* v_as_1394_, lean_object* v_sz_1395_, lean_object* v_i_1396_, lean_object* v_b_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1403_; size_t v_sz_boxed_1404_; size_t v_i_boxed_1405_; lean_object* v_res_1406_; 
v_ignoreLetDecls_boxed_1403_ = lean_unbox(v_ignoreLetDecls_1392_);
v_sz_boxed_1404_ = lean_unbox_usize(v_sz_1395_);
lean_dec(v_sz_1395_);
v_i_boxed_1405_ = lean_unbox_usize(v_i_1396_);
lean_dec(v_i_1396_);
v_res_1406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4(v_ignoreLetDecls_boxed_1403_, v_forbidden_1393_, v_as_1394_, v_sz_boxed_1404_, v_i_boxed_1405_, v_b_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec_ref(v_as_1394_);
lean_dec(v_forbidden_1393_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4(uint8_t v_ignoreLetDecls_1407_, lean_object* v_forbidden_1408_, lean_object* v_as_1409_, size_t v_sz_1410_, size_t v_i_1411_, lean_object* v_b_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v___x_1418_; 
v___x_1418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(v_ignoreLetDecls_1407_, v_forbidden_1408_, v_as_1409_, v_sz_1410_, v_i_1411_, v_b_1412_, v___y_1414_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_ignoreLetDecls_1419_, lean_object* v_forbidden_1420_, lean_object* v_as_1421_, lean_object* v_sz_1422_, lean_object* v_i_1423_, lean_object* v_b_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1430_; size_t v_sz_boxed_1431_; size_t v_i_boxed_1432_; lean_object* v_res_1433_; 
v_ignoreLetDecls_boxed_1430_ = lean_unbox(v_ignoreLetDecls_1419_);
v_sz_boxed_1431_ = lean_unbox_usize(v_sz_1422_);
lean_dec(v_sz_1422_);
v_i_boxed_1432_ = lean_unbox_usize(v_i_1423_);
lean_dec(v_i_1423_);
v_res_1433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4(v_ignoreLetDecls_boxed_1430_, v_forbidden_1420_, v_as_1421_, v_sz_boxed_1431_, v_i_boxed_1432_, v_b_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec_ref(v_as_1421_);
lean_dec(v_forbidden_1420_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(lean_object* v_init_1434_, lean_object* v_x_1435_){
_start:
{
if (lean_obj_tag(v_x_1435_) == 0)
{
lean_object* v_k_1436_; lean_object* v_l_1437_; lean_object* v_r_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v_k_1436_ = lean_ctor_get(v_x_1435_, 1);
lean_inc(v_k_1436_);
v_l_1437_ = lean_ctor_get(v_x_1435_, 3);
lean_inc(v_l_1437_);
v_r_1438_ = lean_ctor_get(v_x_1435_, 4);
lean_inc(v_r_1438_);
lean_dec_ref(v_x_1435_);
v___x_1439_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(v_init_1434_, v_l_1437_);
v___x_1440_ = lean_array_push(v___x_1439_, v_k_1436_);
v_init_1434_ = v___x_1440_;
v_x_1435_ = v_r_1438_;
goto _start;
}
else
{
return v_init_1434_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize(lean_object* v_targets_1442_, lean_object* v_forbidden_1443_, uint8_t v_ignoreLetDecls_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_Meta_mkGeneralizationForbiddenSet(v_targets_1442_, v_forbidden_1443_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; lean_object* v___x_1452_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1451_);
lean_dec_ref(v___x_1450_);
v___x_1452_ = l_Lean_Meta_getFVarSetToGeneralize(v_targets_1442_, v_a_1451_, v_ignoreLetDecls_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
lean_dec(v_a_1451_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; lean_object* v___y_1455_; 
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
lean_inc(v_a_1453_);
lean_dec_ref(v___x_1452_);
if (lean_obj_tag(v_a_1453_) == 0)
{
lean_object* v_size_1459_; 
v_size_1459_ = lean_ctor_get(v_a_1453_, 0);
lean_inc(v_size_1459_);
v___y_1455_ = v_size_1459_;
goto v___jp_1454_;
}
else
{
lean_object* v___x_1460_; 
v___x_1460_ = lean_unsigned_to_nat(0u);
v___y_1455_ = v___x_1460_;
goto v___jp_1454_;
}
v___jp_1454_:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1456_ = lean_mk_empty_array_with_capacity(v___y_1455_);
lean_dec(v___y_1455_);
v___x_1457_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(v___x_1456_, v_a_1453_);
v___x_1458_ = l_Lean_Meta_sortFVarIds___redArg(v___x_1457_, v_a_1445_);
return v___x_1458_;
}
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
v_a_1461_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1452_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1452_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
v_a_1469_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1450_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1450_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize___boxed(lean_object* v_targets_1477_, lean_object* v_forbidden_1478_, lean_object* v_ignoreLetDecls_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1485_; lean_object* v_res_1486_; 
v_ignoreLetDecls_boxed_1485_ = lean_unbox(v_ignoreLetDecls_1479_);
v_res_1486_ = l_Lean_Meta_getFVarsToGeneralize(v_targets_1477_, v_forbidden_1478_, v_ignoreLetDecls_boxed_1485_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_);
lean_dec(v_a_1483_);
lean_dec_ref(v_a_1482_);
lean_dec(v_a_1481_);
lean_dec_ref(v_a_1480_);
lean_dec_ref(v_targets_1477_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0(lean_object* v_init_1487_, lean_object* v_t_1488_){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(v_init_1487_, v_t_1488_);
return v___x_1489_;
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
