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
lean_object* l_Lean_CollectFVars_State_ofFVarSet(lean_object*, lean_object*);
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
static const lean_array_object l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0 = (const lean_object*)&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1;
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
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1;
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
static lean_object* _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = ((lean_object*)(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0));
v___x_93_ = lean_box(1);
v___x_94_ = l_Lean_CollectFVars_State_ofFVarSet(v___x_93_, v___x_92_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit(lean_object* v_fvarId_95_, lean_object* v_todo_96_, lean_object* v_s_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
lean_object* v_a_104_; lean_object* v_s_x27_116_; lean_object* v___y_117_; lean_object* v___y_118_; lean_object* v___y_119_; lean_object* v___y_120_; lean_object* v___x_126_; 
v___x_126_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_95_, v_a_98_, v_a_100_, v_a_101_);
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v_a_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v_a_130_; lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; lean_object* v___x_134_; 
v_a_127_ = lean_ctor_get(v___x_126_, 0);
lean_inc(v_a_127_);
lean_dec_ref_known(v___x_126_, 1);
v___x_128_ = l_Lean_LocalDecl_type(v_a_127_);
v___x_129_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(v___x_128_, v_a_99_);
v_a_130_ = lean_ctor_get(v___x_129_, 0);
lean_inc(v_a_130_);
lean_dec_ref(v___x_129_);
v___x_131_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_132_ = l_Lean_collectFVars(v___x_131_, v_a_130_);
v___x_133_ = 0;
v___x_134_ = l_Lean_LocalDecl_value_x3f(v_a_127_, v___x_133_);
lean_dec(v_a_127_);
if (lean_obj_tag(v___x_134_) == 1)
{
lean_object* v_val_135_; lean_object* v___x_136_; lean_object* v_a_137_; lean_object* v___x_138_; 
v_val_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc(v_val_135_);
lean_dec_ref_known(v___x_134_, 1);
v___x_136_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(v_val_135_, v_a_99_);
v_a_137_ = lean_ctor_get(v___x_136_, 0);
lean_inc(v_a_137_);
lean_dec_ref(v___x_136_);
v___x_138_ = l_Lean_collectFVars(v___x_132_, v_a_137_);
v_s_x27_116_ = v___x_138_;
v___y_117_ = v_a_98_;
v___y_118_ = v_a_99_;
v___y_119_ = v_a_100_;
v___y_120_ = v_a_101_;
goto v___jp_115_;
}
else
{
lean_dec(v___x_134_);
v_s_x27_116_ = v___x_132_;
v___y_117_ = v_a_98_;
v___y_118_ = v_a_99_;
v___y_119_ = v_a_100_;
v___y_120_ = v_a_101_;
goto v___jp_115_;
}
}
else
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
lean_dec(v_s_97_);
lean_dec(v_todo_96_);
v_a_139_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___x_126_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_126_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
v___jp_103_:
{
lean_object* v_fst_105_; lean_object* v_snd_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_114_; 
v_fst_105_ = lean_ctor_get(v_a_104_, 0);
v_snd_106_ = lean_ctor_get(v_a_104_, 1);
v_isSharedCheck_114_ = !lean_is_exclusive(v_a_104_);
if (v_isSharedCheck_114_ == 0)
{
v___x_108_ = v_a_104_;
v_isShared_109_ = v_isSharedCheck_114_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_snd_106_);
lean_inc(v_fst_105_);
lean_dec(v_a_104_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_114_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_111_; 
if (v_isShared_109_ == 0)
{
v___x_111_ = v___x_108_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_fst_105_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_snd_106_);
v___x_111_ = v_reuseFailAlloc_113_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
lean_object* v___x_112_; 
v___x_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
return v___x_112_;
}
}
}
v___jp_115_:
{
lean_object* v_fvarSet_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v_a_124_; lean_object* v_a_125_; 
v_fvarSet_121_ = lean_ctor_get(v_s_x27_116_, 1);
lean_inc(v_fvarSet_121_);
lean_dec_ref(v_s_x27_116_);
v___x_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_122_, 0, v_todo_96_);
lean_ctor_set(v___x_122_, 1, v_s_97_);
v___x_123_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(v___x_122_, v_fvarSet_121_);
v_a_124_ = lean_ctor_get(v___x_123_, 0);
lean_inc(v_a_124_);
lean_dec_ref(v___x_123_);
v_a_125_ = lean_ctor_get(v_a_124_, 0);
lean_inc(v_a_125_);
lean_dec(v_a_124_);
v_a_104_ = v_a_125_;
goto v___jp_103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___boxed(lean_object* v_fvarId_147_, lean_object* v_todo_148_, lean_object* v_s_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit(v_fvarId_147_, v_todo_148_, v_s_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
return v_res_155_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0(lean_object* v_00_u03b2_156_, lean_object* v_k_157_, lean_object* v_t_158_){
_start:
{
uint8_t v___x_159_; 
v___x_159_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v_k_157_, v_t_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___boxed(lean_object* v_00_u03b2_160_, lean_object* v_k_161_, lean_object* v_t_162_){
_start:
{
uint8_t v_res_163_; lean_object* v_r_164_; 
v_res_163_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0(v_00_u03b2_160_, v_k_161_, v_t_162_);
lean_dec(v_t_162_);
lean_dec(v_k_161_);
v_r_164_ = lean_box(v_res_163_);
return v_r_164_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1(lean_object* v_init_165_, lean_object* v_x_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(v_init_165_, v_x_166_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___boxed(lean_object* v_init_173_, lean_object* v_x_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1(v_init_173_, v_x_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop(lean_object* v_todo_181_, lean_object* v_s_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
if (lean_obj_tag(v_todo_181_) == 0)
{
lean_object* v___x_188_; 
v___x_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_188_, 0, v_s_182_);
return v___x_188_;
}
else
{
lean_object* v_head_189_; lean_object* v_tail_190_; uint8_t v___x_191_; 
v_head_189_ = lean_ctor_get(v_todo_181_, 0);
lean_inc(v_head_189_);
v_tail_190_ = lean_ctor_get(v_todo_181_, 1);
lean_inc(v_tail_190_);
lean_dec_ref_known(v_todo_181_, 2);
v___x_191_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v_head_189_, v_s_182_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; lean_object* v___x_193_; 
lean_inc(v_head_189_);
v___x_192_ = l_Lean_FVarIdSet_insert(v_s_182_, v_head_189_);
v___x_193_ = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit(v_head_189_, v_tail_190_, v___x_192_, v_a_183_, v_a_184_, v_a_185_, v_a_186_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; lean_object* v_fst_195_; lean_object* v_snd_196_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
lean_inc(v_a_194_);
lean_dec_ref_known(v___x_193_, 1);
v_fst_195_ = lean_ctor_get(v_a_194_, 0);
lean_inc(v_fst_195_);
v_snd_196_ = lean_ctor_get(v_a_194_, 1);
lean_inc(v_snd_196_);
lean_dec(v_a_194_);
v_todo_181_ = v_fst_195_;
v_s_182_ = v_snd_196_;
goto _start;
}
else
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
v_a_198_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v___x_193_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_193_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_a_198_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
else
{
lean_dec(v_head_189_);
v_todo_181_ = v_tail_190_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop___boxed(lean_object* v_todo_207_, lean_object* v_s_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop(v_todo_207_, v_s_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
lean_dec(v_a_210_);
lean_dec_ref(v_a_209_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0(lean_object* v_as_215_, size_t v_sz_216_, size_t v_i_217_, lean_object* v_b_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
lean_object* v_a_225_; uint8_t v___x_229_; 
v___x_229_ = lean_usize_dec_lt(v_i_217_, v_sz_216_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; 
v___x_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_230_, 0, v_b_218_);
return v___x_230_;
}
else
{
lean_object* v_fst_231_; lean_object* v_snd_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_267_; 
v_fst_231_ = lean_ctor_get(v_b_218_, 0);
v_snd_232_ = lean_ctor_get(v_b_218_, 1);
v_isSharedCheck_267_ = !lean_is_exclusive(v_b_218_);
if (v_isSharedCheck_267_ == 0)
{
v___x_234_ = v_b_218_;
v_isShared_235_ = v_isSharedCheck_267_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_snd_232_);
lean_inc(v_fst_231_);
lean_dec(v_b_218_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_267_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v_a_236_; uint8_t v___x_237_; 
v_a_236_ = lean_array_uget_borrowed(v_as_215_, v_i_217_);
v___x_237_ = l_Lean_Expr_isFVar(v_a_236_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; 
lean_inc(v___y_222_);
lean_inc_ref(v___y_221_);
lean_inc(v___y_220_);
lean_inc_ref(v___y_219_);
lean_inc(v_a_236_);
v___x_238_ = lean_infer_type(v_a_236_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v_a_239_; lean_object* v___x_240_; 
v_a_239_ = lean_ctor_get(v___x_238_, 0);
lean_inc(v_a_239_);
lean_dec_ref_known(v___x_238_, 1);
v___x_240_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(v_a_239_, v___y_220_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v___x_242_; lean_object* v___x_244_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_a_241_);
lean_dec_ref_known(v___x_240_, 1);
v___x_242_ = l_Lean_collectFVars(v_fst_231_, v_a_241_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 0, v___x_242_);
v___x_244_ = v___x_234_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v_snd_232_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
v_a_225_ = v___x_244_;
goto v___jp_224_;
}
}
else
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
lean_del_object(v___x_234_);
lean_dec(v_snd_232_);
lean_dec(v_fst_231_);
v_a_246_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v___x_240_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_240_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_a_246_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
else
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
lean_del_object(v___x_234_);
lean_dec(v_snd_232_);
lean_dec(v_fst_231_);
v_a_254_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_261_ == 0)
{
v___x_256_ = v___x_238_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_238_);
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
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_265_; 
v___x_262_ = l_Lean_Expr_fvarId_x21(v_a_236_);
v___x_263_ = lean_array_push(v_snd_232_, v___x_262_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 1, v___x_263_);
v___x_265_ = v___x_234_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_fst_231_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v___x_263_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
v_a_225_ = v___x_265_;
goto v___jp_224_;
}
}
}
}
v___jp_224_:
{
size_t v___x_226_; size_t v___x_227_; 
v___x_226_ = ((size_t)1ULL);
v___x_227_ = lean_usize_add(v_i_217_, v___x_226_);
v_i_217_ = v___x_227_;
v_b_218_ = v_a_225_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0___boxed(lean_object* v_as_268_, lean_object* v_sz_269_, lean_object* v_i_270_, lean_object* v_b_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
size_t v_sz_boxed_277_; size_t v_i_boxed_278_; lean_object* v_res_279_; 
v_sz_boxed_277_ = lean_unbox_usize(v_sz_269_);
lean_dec(v_sz_269_);
v_i_boxed_278_ = lean_unbox_usize(v_i_270_);
lean_dec(v_i_270_);
v_res_279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0(v_as_268_, v_sz_boxed_277_, v_i_boxed_278_, v_b_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec_ref(v_as_268_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet(lean_object* v_targets_280_, lean_object* v_forbidden_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_){
_start:
{
lean_object* v_todo_287_; lean_object* v_s_288_; lean_object* v___x_289_; size_t v_sz_290_; size_t v___x_291_; lean_object* v___x_292_; 
v_todo_287_ = ((lean_object*)(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0));
v_s_288_ = l_Lean_CollectFVars_State_ofFVarSet(v_forbidden_281_, v_todo_287_);
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v_s_288_);
lean_ctor_set(v___x_289_, 1, v_todo_287_);
v_sz_290_ = lean_array_size(v_targets_280_);
v___x_291_ = ((size_t)0ULL);
v___x_292_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0(v_targets_280_, v_sz_290_, v___x_291_, v___x_289_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v_fst_294_; lean_object* v_snd_295_; lean_object* v_fvarSet_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_a_293_);
lean_dec_ref_known(v___x_292_, 1);
v_fst_294_ = lean_ctor_get(v_a_293_, 0);
lean_inc(v_fst_294_);
v_snd_295_ = lean_ctor_get(v_a_293_, 1);
lean_inc(v_snd_295_);
lean_dec(v_a_293_);
v_fvarSet_296_ = lean_ctor_get(v_fst_294_, 1);
lean_inc(v_fvarSet_296_);
lean_dec(v_fst_294_);
v___x_297_ = lean_array_to_list(v_snd_295_);
v___x_298_ = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop(v___x_297_, v_fvarSet_296_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
return v___x_298_;
}
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
v_a_299_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_292_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_292_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet___boxed(lean_object* v_targets_307_, lean_object* v_forbidden_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_Meta_mkGeneralizationForbiddenSet(v_targets_307_, v_forbidden_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_);
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
lean_dec_ref(v_targets_307_);
return v_res_314_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1(uint8_t v___y_315_, lean_object* v_x_316_){
_start:
{
return v___y_315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed(lean_object* v___y_317_, lean_object* v_x_318_){
_start:
{
uint8_t v___y_8904__boxed_319_; uint8_t v_res_320_; lean_object* v_r_321_; 
v___y_8904__boxed_319_ = lean_unbox(v___y_317_);
v_res_320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1(v___y_8904__boxed_319_, v_x_318_);
lean_dec(v_x_318_);
v_r_321_ = lean_box(v_res_320_);
return v_r_321_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0(lean_object* v_fst_322_, lean_object* v_x_323_){
_start:
{
uint8_t v___x_324_; 
v___x_324_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v_x_323_, v_fst_322_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed(lean_object* v_fst_325_, lean_object* v_x_326_){
_start:
{
uint8_t v_res_327_; lean_object* v_r_328_; 
v_res_327_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0(v_fst_325_, v_x_326_);
lean_dec(v_x_326_);
lean_dec(v_fst_325_);
v_r_328_ = lean_box(v_res_327_);
return v_r_328_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = lean_box(0);
v___x_330_ = lean_unsigned_to_nat(16u);
v___x_331_ = lean_mk_array(v___x_330_, v___x_329_);
return v___x_331_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_332_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__0);
v___x_333_ = lean_unsigned_to_nat(0u);
v___x_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v___x_332_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(lean_object* v_forbidden_335_, uint8_t v_ignoreLetDecls_336_, lean_object* v_as_337_, size_t v_sz_338_, size_t v_i_339_, lean_object* v_b_340_, lean_object* v___y_341_){
_start:
{
uint8_t v___x_343_; 
v___x_343_ = lean_usize_dec_lt(v_i_339_, v_sz_338_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; 
v___x_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_344_, 0, v_b_340_);
return v___x_344_;
}
else
{
lean_object* v_snd_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_503_; 
v_snd_345_ = lean_ctor_get(v_b_340_, 1);
v_isSharedCheck_503_ = !lean_is_exclusive(v_b_340_);
if (v_isSharedCheck_503_ == 0)
{
lean_object* v_unused_504_; 
v_unused_504_ = lean_ctor_get(v_b_340_, 0);
lean_dec(v_unused_504_);
v___x_347_ = v_b_340_;
v_isShared_348_ = v_isSharedCheck_503_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_snd_345_);
lean_dec(v_b_340_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_503_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; lean_object* v_a_351_; lean_object* v_a_358_; 
v___x_349_ = lean_box(0);
v_a_358_ = lean_array_uget_borrowed(v_as_337_, v_i_339_);
if (lean_obj_tag(v_a_358_) == 0)
{
v_a_351_ = v_snd_345_;
goto v___jp_350_;
}
else
{
lean_object* v_val_359_; lean_object* v_fst_360_; lean_object* v_snd_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_502_; 
v_val_359_ = lean_ctor_get(v_a_358_, 0);
v_fst_360_ = lean_ctor_get(v_snd_345_, 0);
v_snd_361_ = lean_ctor_get(v_snd_345_, 1);
v_isSharedCheck_502_ = !lean_is_exclusive(v_snd_345_);
if (v_isSharedCheck_502_ == 0)
{
v___x_363_ = v_snd_345_;
v_isShared_364_ = v_isSharedCheck_502_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_snd_361_);
lean_inc(v_fst_360_);
lean_dec(v_snd_345_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_502_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_369_; uint8_t v_a_371_; uint8_t v_fst_377_; lean_object* v_mctx_378_; lean_object* v___y_394_; uint8_t v_fst_400_; lean_object* v_snd_401_; lean_object* v___y_418_; uint8_t v_fst_423_; lean_object* v_mctx_424_; lean_object* v___y_440_; uint8_t v___x_445_; 
v___x_369_ = l_Lean_LocalDecl_fvarId(v_val_359_);
v___x_445_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v___x_369_, v_forbidden_335_);
if (v___x_445_ == 0)
{
uint8_t v___x_446_; 
v___x_446_ = l_Lean_LocalDecl_isAuxDecl(v_val_359_);
if (v___x_446_ == 0)
{
uint8_t v___x_447_; uint8_t v___x_448_; 
v___x_447_ = l_Lean_LocalDecl_binderInfo(v_val_359_);
v___x_448_ = l_Lean_BinderInfo_isInstImplicit(v___x_447_);
if (v___x_448_ == 0)
{
lean_object* v___f_449_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v_snd_453_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; uint8_t v___y_468_; 
lean_inc(v_fst_360_);
v___f_449_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_449_, 0, v_fst_360_);
if (v_ignoreLetDecls_336_ == 0)
{
lean_del_object(v___x_363_);
v___y_468_ = v___x_445_;
goto v___jp_467_;
}
else
{
uint8_t v___x_500_; 
v___x_500_ = l_Lean_LocalDecl_isLet(v_val_359_, v___x_445_);
if (v___x_500_ == 0)
{
lean_del_object(v___x_363_);
v___y_468_ = v___x_500_;
goto v___jp_467_;
}
else
{
lean_dec_ref(v___f_449_);
lean_dec(v___x_369_);
goto v___jp_365_;
}
}
v___jp_450_:
{
uint8_t v___x_454_; 
v___x_454_ = l_Lean_Expr_hasFVar(v___y_451_);
if (v___x_454_ == 0)
{
uint8_t v___x_455_; 
v___x_455_ = l_Lean_Expr_hasMVar(v___y_451_);
if (v___x_455_ == 0)
{
lean_dec_ref(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec_ref(v___f_449_);
v_fst_400_ = v___x_455_;
v_snd_401_ = v_snd_453_;
goto v___jp_399_;
}
else
{
lean_object* v___x_456_; 
v___x_456_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_449_, v___y_452_, v___y_451_, v_snd_453_);
v___y_418_ = v___x_456_;
goto v___jp_417_;
}
}
else
{
lean_object* v___x_457_; 
v___x_457_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_449_, v___y_452_, v___y_451_, v_snd_453_);
v___y_418_ = v___x_457_;
goto v___jp_417_;
}
}
v___jp_458_:
{
lean_object* v_fst_462_; uint8_t v___x_463_; 
v_fst_462_ = lean_ctor_get(v___y_461_, 0);
v___x_463_ = lean_unbox(v_fst_462_);
if (v___x_463_ == 0)
{
lean_object* v_snd_464_; 
v_snd_464_ = lean_ctor_get(v___y_461_, 1);
lean_inc(v_snd_464_);
lean_dec_ref(v___y_461_);
v___y_451_ = v___y_459_;
v___y_452_ = v___y_460_;
v_snd_453_ = v_snd_464_;
goto v___jp_450_;
}
else
{
lean_object* v_snd_465_; uint8_t v___x_466_; 
lean_inc(v_fst_462_);
lean_dec_ref(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec_ref(v___f_449_);
v_snd_465_ = lean_ctor_get(v___y_461_, 1);
lean_inc(v_snd_465_);
lean_dec_ref(v___y_461_);
v___x_466_ = lean_unbox(v_fst_462_);
lean_dec(v_fst_462_);
v_fst_400_ = v___x_466_;
v_snd_401_ = v_snd_465_;
goto v___jp_399_;
}
}
v___jp_467_:
{
lean_object* v___x_469_; lean_object* v___f_470_; 
v___x_469_ = lean_box(v___y_468_);
v___f_470_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(v___f_470_, 0, v___x_469_);
if (lean_obj_tag(v_val_359_) == 0)
{
lean_object* v_type_471_; lean_object* v___x_472_; lean_object* v_mctx_473_; lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v_type_471_ = lean_ctor_get(v_val_359_, 3);
v___x_472_ = lean_st_ref_get(v___y_341_);
v_mctx_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc_ref_n(v_mctx_473_, 2);
lean_dec(v___x_472_);
v___x_474_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1);
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
lean_dec_ref(v___f_449_);
v_fst_423_ = v___x_477_;
v_mctx_424_ = v_mctx_473_;
goto v___jp_422_;
}
else
{
lean_object* v___x_478_; 
lean_dec_ref(v_mctx_473_);
lean_inc_ref(v_type_471_);
v___x_478_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_449_, v___f_470_, v_type_471_, v___x_475_);
v___y_440_ = v___x_478_;
goto v___jp_439_;
}
}
else
{
lean_object* v___x_479_; 
lean_dec_ref(v_mctx_473_);
lean_inc_ref(v_type_471_);
v___x_479_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_449_, v___f_470_, v_type_471_, v___x_475_);
v___y_440_ = v___x_479_;
goto v___jp_439_;
}
}
else
{
uint8_t v_nondep_480_; 
v_nondep_480_ = lean_ctor_get_uint8(v_val_359_, sizeof(void*)*5);
if (v_nondep_480_ == 0)
{
lean_object* v_type_481_; lean_object* v_value_482_; lean_object* v___x_483_; lean_object* v_mctx_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v_type_481_ = lean_ctor_get(v_val_359_, 3);
v_value_482_ = lean_ctor_get(v_val_359_, 4);
v___x_483_ = lean_st_ref_get(v___y_341_);
v_mctx_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc_ref(v_mctx_484_);
lean_dec(v___x_483_);
v___x_485_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1);
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
v___y_451_ = v_value_482_;
v___y_452_ = v___f_470_;
v_snd_453_ = v___x_486_;
goto v___jp_450_;
}
else
{
lean_object* v___x_489_; 
lean_inc_ref(v_type_481_);
lean_inc_ref(v___f_470_);
lean_inc_ref(v___f_449_);
v___x_489_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_449_, v___f_470_, v_type_481_, v___x_486_);
lean_inc_ref(v_value_482_);
v___y_459_ = v_value_482_;
v___y_460_ = v___f_470_;
v___y_461_ = v___x_489_;
goto v___jp_458_;
}
}
else
{
lean_object* v___x_490_; 
lean_inc_ref(v_type_481_);
lean_inc_ref(v___f_470_);
lean_inc_ref(v___f_449_);
v___x_490_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_449_, v___f_470_, v_type_481_, v___x_486_);
lean_inc_ref(v_value_482_);
v___y_459_ = v_value_482_;
v___y_460_ = v___f_470_;
v___y_461_ = v___x_490_;
goto v___jp_458_;
}
}
else
{
lean_object* v_type_491_; lean_object* v___x_492_; lean_object* v_mctx_493_; lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v_type_491_ = lean_ctor_get(v_val_359_, 3);
v___x_492_ = lean_st_ref_get(v___y_341_);
v_mctx_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc_ref_n(v_mctx_493_, 2);
lean_dec(v___x_492_);
v___x_494_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1);
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
lean_dec_ref(v___f_449_);
v_fst_377_ = v___x_497_;
v_mctx_378_ = v_mctx_493_;
goto v___jp_376_;
}
else
{
lean_object* v___x_498_; 
lean_dec_ref(v_mctx_493_);
lean_inc_ref(v_type_491_);
v___x_498_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_449_, v___f_470_, v_type_491_, v___x_495_);
v___y_394_ = v___x_498_;
goto v___jp_393_;
}
}
else
{
lean_object* v___x_499_; 
lean_dec_ref(v_mctx_493_);
lean_inc_ref(v_type_491_);
v___x_499_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_449_, v___f_470_, v_type_491_, v___x_495_);
v___y_394_ = v___x_499_;
goto v___jp_393_;
}
}
}
}
}
else
{
lean_dec(v___x_369_);
goto v___jp_365_;
}
}
else
{
lean_dec(v___x_369_);
goto v___jp_365_;
}
}
else
{
lean_object* v___x_501_; 
lean_dec(v___x_369_);
lean_del_object(v___x_363_);
v___x_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_501_, 0, v_fst_360_);
lean_ctor_set(v___x_501_, 1, v_snd_361_);
v_a_351_ = v___x_501_;
goto v___jp_350_;
}
v___jp_365_:
{
lean_object* v___x_367_; 
if (v_isShared_364_ == 0)
{
v___x_367_ = v___x_363_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_fst_360_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_snd_361_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
v_a_351_ = v___x_367_;
goto v___jp_350_;
}
}
v___jp_370_:
{
if (v_a_371_ == 0)
{
lean_object* v___x_372_; 
lean_dec(v___x_369_);
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v_fst_360_);
lean_ctor_set(v___x_372_, 1, v_snd_361_);
v_a_351_ = v___x_372_;
goto v___jp_350_;
}
else
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
lean_inc(v___x_369_);
v___x_373_ = l_Lean_FVarIdSet_insert(v_snd_361_, v___x_369_);
v___x_374_ = l_Lean_FVarIdSet_insert(v_fst_360_, v___x_369_);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v___x_373_);
v_a_351_ = v___x_375_;
goto v___jp_350_;
}
}
v___jp_376_:
{
lean_object* v___x_379_; lean_object* v_cache_380_; lean_object* v_zetaDeltaFVarIds_381_; lean_object* v_postponed_382_; lean_object* v_diag_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_391_; 
v___x_379_ = lean_st_ref_take(v___y_341_);
v_cache_380_ = lean_ctor_get(v___x_379_, 1);
v_zetaDeltaFVarIds_381_ = lean_ctor_get(v___x_379_, 2);
v_postponed_382_ = lean_ctor_get(v___x_379_, 3);
v_diag_383_ = lean_ctor_get(v___x_379_, 4);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_391_ == 0)
{
lean_object* v_unused_392_; 
v_unused_392_ = lean_ctor_get(v___x_379_, 0);
lean_dec(v_unused_392_);
v___x_385_ = v___x_379_;
v_isShared_386_ = v_isSharedCheck_391_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_diag_383_);
lean_inc(v_postponed_382_);
lean_inc(v_zetaDeltaFVarIds_381_);
lean_inc(v_cache_380_);
lean_dec(v___x_379_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_391_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 0, v_mctx_378_);
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_mctx_378_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_cache_380_);
lean_ctor_set(v_reuseFailAlloc_390_, 2, v_zetaDeltaFVarIds_381_);
lean_ctor_set(v_reuseFailAlloc_390_, 3, v_postponed_382_);
lean_ctor_set(v_reuseFailAlloc_390_, 4, v_diag_383_);
v___x_388_ = v_reuseFailAlloc_390_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
lean_object* v___x_389_; 
v___x_389_ = lean_st_ref_put(v___y_341_, v___x_388_);
v_a_371_ = v_fst_377_;
goto v___jp_370_;
}
}
}
v___jp_393_:
{
lean_object* v_snd_395_; lean_object* v_fst_396_; lean_object* v_mctx_397_; uint8_t v___x_398_; 
v_snd_395_ = lean_ctor_get(v___y_394_, 1);
lean_inc(v_snd_395_);
v_fst_396_ = lean_ctor_get(v___y_394_, 0);
lean_inc(v_fst_396_);
lean_dec_ref(v___y_394_);
v_mctx_397_ = lean_ctor_get(v_snd_395_, 1);
lean_inc_ref(v_mctx_397_);
lean_dec(v_snd_395_);
v___x_398_ = lean_unbox(v_fst_396_);
lean_dec(v_fst_396_);
v_fst_377_ = v___x_398_;
v_mctx_378_ = v_mctx_397_;
goto v___jp_376_;
}
v___jp_399_:
{
lean_object* v_mctx_402_; lean_object* v___x_403_; lean_object* v_cache_404_; lean_object* v_zetaDeltaFVarIds_405_; lean_object* v_postponed_406_; lean_object* v_diag_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_415_; 
v_mctx_402_ = lean_ctor_get(v_snd_401_, 1);
lean_inc_ref(v_mctx_402_);
lean_dec_ref(v_snd_401_);
v___x_403_ = lean_st_ref_take(v___y_341_);
v_cache_404_ = lean_ctor_get(v___x_403_, 1);
v_zetaDeltaFVarIds_405_ = lean_ctor_get(v___x_403_, 2);
v_postponed_406_ = lean_ctor_get(v___x_403_, 3);
v_diag_407_ = lean_ctor_get(v___x_403_, 4);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_415_ == 0)
{
lean_object* v_unused_416_; 
v_unused_416_ = lean_ctor_get(v___x_403_, 0);
lean_dec(v_unused_416_);
v___x_409_ = v___x_403_;
v_isShared_410_ = v_isSharedCheck_415_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_diag_407_);
lean_inc(v_postponed_406_);
lean_inc(v_zetaDeltaFVarIds_405_);
lean_inc(v_cache_404_);
lean_dec(v___x_403_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_415_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v_mctx_402_);
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_mctx_402_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v_cache_404_);
lean_ctor_set(v_reuseFailAlloc_414_, 2, v_zetaDeltaFVarIds_405_);
lean_ctor_set(v_reuseFailAlloc_414_, 3, v_postponed_406_);
lean_ctor_set(v_reuseFailAlloc_414_, 4, v_diag_407_);
v___x_412_ = v_reuseFailAlloc_414_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
lean_object* v___x_413_; 
v___x_413_ = lean_st_ref_put(v___y_341_, v___x_412_);
v_a_371_ = v_fst_400_;
goto v___jp_370_;
}
}
}
v___jp_417_:
{
lean_object* v_fst_419_; lean_object* v_snd_420_; uint8_t v___x_421_; 
v_fst_419_ = lean_ctor_get(v___y_418_, 0);
lean_inc(v_fst_419_);
v_snd_420_ = lean_ctor_get(v___y_418_, 1);
lean_inc(v_snd_420_);
lean_dec_ref(v___y_418_);
v___x_421_ = lean_unbox(v_fst_419_);
lean_dec(v_fst_419_);
v_fst_400_ = v___x_421_;
v_snd_401_ = v_snd_420_;
goto v___jp_399_;
}
v___jp_422_:
{
lean_object* v___x_425_; lean_object* v_cache_426_; lean_object* v_zetaDeltaFVarIds_427_; lean_object* v_postponed_428_; lean_object* v_diag_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_437_; 
v___x_425_ = lean_st_ref_take(v___y_341_);
v_cache_426_ = lean_ctor_get(v___x_425_, 1);
v_zetaDeltaFVarIds_427_ = lean_ctor_get(v___x_425_, 2);
v_postponed_428_ = lean_ctor_get(v___x_425_, 3);
v_diag_429_ = lean_ctor_get(v___x_425_, 4);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_437_ == 0)
{
lean_object* v_unused_438_; 
v_unused_438_ = lean_ctor_get(v___x_425_, 0);
lean_dec(v_unused_438_);
v___x_431_ = v___x_425_;
v_isShared_432_ = v_isSharedCheck_437_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_diag_429_);
lean_inc(v_postponed_428_);
lean_inc(v_zetaDeltaFVarIds_427_);
lean_inc(v_cache_426_);
lean_dec(v___x_425_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_437_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v_mctx_424_);
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_mctx_424_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_cache_426_);
lean_ctor_set(v_reuseFailAlloc_436_, 2, v_zetaDeltaFVarIds_427_);
lean_ctor_set(v_reuseFailAlloc_436_, 3, v_postponed_428_);
lean_ctor_set(v_reuseFailAlloc_436_, 4, v_diag_429_);
v___x_434_ = v_reuseFailAlloc_436_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
lean_object* v___x_435_; 
v___x_435_ = lean_st_ref_put(v___y_341_, v___x_434_);
v_a_371_ = v_fst_423_;
goto v___jp_370_;
}
}
}
v___jp_439_:
{
lean_object* v_snd_441_; lean_object* v_fst_442_; lean_object* v_mctx_443_; uint8_t v___x_444_; 
v_snd_441_ = lean_ctor_get(v___y_440_, 1);
lean_inc(v_snd_441_);
v_fst_442_ = lean_ctor_get(v___y_440_, 0);
lean_inc(v_fst_442_);
lean_dec_ref(v___y_440_);
v_mctx_443_ = lean_ctor_get(v_snd_441_, 1);
lean_inc_ref(v_mctx_443_);
lean_dec(v_snd_441_);
v___x_444_ = lean_unbox(v_fst_442_);
lean_dec(v_fst_442_);
v_fst_423_ = v___x_444_;
v_mctx_424_ = v_mctx_443_;
goto v___jp_422_;
}
}
}
v___jp_350_:
{
lean_object* v___x_353_; 
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 1, v_a_351_);
lean_ctor_set(v___x_347_, 0, v___x_349_);
v___x_353_ = v___x_347_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_a_351_);
v___x_353_ = v_reuseFailAlloc_357_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
size_t v___x_354_; size_t v___x_355_; 
v___x_354_ = ((size_t)1ULL);
v___x_355_ = lean_usize_add(v_i_339_, v___x_354_);
v_i_339_ = v___x_355_;
v_b_340_ = v___x_353_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_forbidden_505_, lean_object* v_ignoreLetDecls_506_, lean_object* v_as_507_, lean_object* v_sz_508_, lean_object* v_i_509_, lean_object* v_b_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_513_; size_t v_sz_boxed_514_; size_t v_i_boxed_515_; lean_object* v_res_516_; 
v_ignoreLetDecls_boxed_513_ = lean_unbox(v_ignoreLetDecls_506_);
v_sz_boxed_514_ = lean_unbox_usize(v_sz_508_);
lean_dec(v_sz_508_);
v_i_boxed_515_ = lean_unbox_usize(v_i_509_);
lean_dec(v_i_509_);
v_res_516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(v_forbidden_505_, v_ignoreLetDecls_boxed_513_, v_as_507_, v_sz_boxed_514_, v_i_boxed_515_, v_b_510_, v___y_511_);
lean_dec(v___y_511_);
lean_dec_ref(v_as_507_);
lean_dec(v_forbidden_505_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1(lean_object* v_forbidden_517_, uint8_t v_ignoreLetDecls_518_, lean_object* v_as_519_, size_t v_sz_520_, size_t v_i_521_, lean_object* v_b_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
uint8_t v___x_528_; 
v___x_528_ = lean_usize_dec_lt(v_i_521_, v_sz_520_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; 
v___x_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_529_, 0, v_b_522_);
return v___x_529_;
}
else
{
lean_object* v_snd_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_688_; 
v_snd_530_ = lean_ctor_get(v_b_522_, 1);
v_isSharedCheck_688_ = !lean_is_exclusive(v_b_522_);
if (v_isSharedCheck_688_ == 0)
{
lean_object* v_unused_689_; 
v_unused_689_ = lean_ctor_get(v_b_522_, 0);
lean_dec(v_unused_689_);
v___x_532_ = v_b_522_;
v_isShared_533_ = v_isSharedCheck_688_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_snd_530_);
lean_dec(v_b_522_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_688_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v_a_536_; lean_object* v_a_543_; 
v___x_534_ = lean_box(0);
v_a_543_ = lean_array_uget_borrowed(v_as_519_, v_i_521_);
if (lean_obj_tag(v_a_543_) == 0)
{
v_a_536_ = v_snd_530_;
goto v___jp_535_;
}
else
{
lean_object* v_val_544_; lean_object* v_fst_545_; lean_object* v_snd_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_687_; 
v_val_544_ = lean_ctor_get(v_a_543_, 0);
v_fst_545_ = lean_ctor_get(v_snd_530_, 0);
v_snd_546_ = lean_ctor_get(v_snd_530_, 1);
v_isSharedCheck_687_ = !lean_is_exclusive(v_snd_530_);
if (v_isSharedCheck_687_ == 0)
{
v___x_548_ = v_snd_530_;
v_isShared_549_ = v_isSharedCheck_687_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_snd_546_);
lean_inc(v_fst_545_);
lean_dec(v_snd_530_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_687_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_554_; uint8_t v_a_556_; uint8_t v_fst_562_; lean_object* v_mctx_563_; lean_object* v___y_579_; uint8_t v_fst_585_; lean_object* v_snd_586_; lean_object* v___y_603_; uint8_t v_fst_608_; lean_object* v_mctx_609_; lean_object* v___y_625_; uint8_t v___x_630_; 
v___x_554_ = l_Lean_LocalDecl_fvarId(v_val_544_);
v___x_630_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v___x_554_, v_forbidden_517_);
if (v___x_630_ == 0)
{
uint8_t v___x_631_; 
v___x_631_ = l_Lean_LocalDecl_isAuxDecl(v_val_544_);
if (v___x_631_ == 0)
{
uint8_t v___x_632_; uint8_t v___x_633_; 
v___x_632_ = l_Lean_LocalDecl_binderInfo(v_val_544_);
v___x_633_ = l_Lean_BinderInfo_isInstImplicit(v___x_632_);
if (v___x_633_ == 0)
{
lean_object* v___f_634_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v_snd_638_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; uint8_t v___y_653_; 
lean_inc(v_fst_545_);
v___f_634_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_634_, 0, v_fst_545_);
if (v_ignoreLetDecls_518_ == 0)
{
lean_del_object(v___x_548_);
v___y_653_ = v___x_630_;
goto v___jp_652_;
}
else
{
uint8_t v___x_685_; 
v___x_685_ = l_Lean_LocalDecl_isLet(v_val_544_, v___x_630_);
if (v___x_685_ == 0)
{
lean_del_object(v___x_548_);
v___y_653_ = v___x_685_;
goto v___jp_652_;
}
else
{
lean_dec_ref(v___f_634_);
lean_dec(v___x_554_);
goto v___jp_550_;
}
}
v___jp_635_:
{
uint8_t v___x_639_; 
v___x_639_ = l_Lean_Expr_hasFVar(v___y_637_);
if (v___x_639_ == 0)
{
uint8_t v___x_640_; 
v___x_640_ = l_Lean_Expr_hasMVar(v___y_637_);
if (v___x_640_ == 0)
{
lean_dec_ref(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec_ref(v___f_634_);
v_fst_585_ = v___x_640_;
v_snd_586_ = v_snd_638_;
goto v___jp_584_;
}
else
{
lean_object* v___x_641_; 
v___x_641_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_634_, v___y_636_, v___y_637_, v_snd_638_);
v___y_603_ = v___x_641_;
goto v___jp_602_;
}
}
else
{
lean_object* v___x_642_; 
v___x_642_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_634_, v___y_636_, v___y_637_, v_snd_638_);
v___y_603_ = v___x_642_;
goto v___jp_602_;
}
}
v___jp_643_:
{
lean_object* v_fst_647_; uint8_t v___x_648_; 
v_fst_647_ = lean_ctor_get(v___y_646_, 0);
v___x_648_ = lean_unbox(v_fst_647_);
if (v___x_648_ == 0)
{
lean_object* v_snd_649_; 
v_snd_649_ = lean_ctor_get(v___y_646_, 1);
lean_inc(v_snd_649_);
lean_dec_ref(v___y_646_);
v___y_636_ = v___y_644_;
v___y_637_ = v___y_645_;
v_snd_638_ = v_snd_649_;
goto v___jp_635_;
}
else
{
lean_object* v_snd_650_; uint8_t v___x_651_; 
lean_inc(v_fst_647_);
lean_dec_ref(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec_ref(v___f_634_);
v_snd_650_ = lean_ctor_get(v___y_646_, 1);
lean_inc(v_snd_650_);
lean_dec_ref(v___y_646_);
v___x_651_ = lean_unbox(v_fst_647_);
lean_dec(v_fst_647_);
v_fst_585_ = v___x_651_;
v_snd_586_ = v_snd_650_;
goto v___jp_584_;
}
}
v___jp_652_:
{
lean_object* v___x_654_; lean_object* v___f_655_; 
v___x_654_ = lean_box(v___y_653_);
v___f_655_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(v___f_655_, 0, v___x_654_);
if (lean_obj_tag(v_val_544_) == 0)
{
lean_object* v_type_656_; lean_object* v___x_657_; lean_object* v_mctx_658_; lean_object* v___x_659_; lean_object* v___x_660_; uint8_t v___x_661_; 
v_type_656_ = lean_ctor_get(v_val_544_, 3);
v___x_657_ = lean_st_ref_get(v___y_524_);
v_mctx_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc_ref_n(v_mctx_658_, 2);
lean_dec(v___x_657_);
v___x_659_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1);
v___x_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
lean_ctor_set(v___x_660_, 1, v_mctx_658_);
v___x_661_ = l_Lean_Expr_hasFVar(v_type_656_);
if (v___x_661_ == 0)
{
uint8_t v___x_662_; 
v___x_662_ = l_Lean_Expr_hasMVar(v_type_656_);
if (v___x_662_ == 0)
{
lean_dec_ref_known(v___x_660_, 2);
lean_dec_ref(v___f_655_);
lean_dec_ref(v___f_634_);
v_fst_608_ = v___x_662_;
v_mctx_609_ = v_mctx_658_;
goto v___jp_607_;
}
else
{
lean_object* v___x_663_; 
lean_dec_ref(v_mctx_658_);
lean_inc_ref(v_type_656_);
v___x_663_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_634_, v___f_655_, v_type_656_, v___x_660_);
v___y_625_ = v___x_663_;
goto v___jp_624_;
}
}
else
{
lean_object* v___x_664_; 
lean_dec_ref(v_mctx_658_);
lean_inc_ref(v_type_656_);
v___x_664_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_634_, v___f_655_, v_type_656_, v___x_660_);
v___y_625_ = v___x_664_;
goto v___jp_624_;
}
}
else
{
uint8_t v_nondep_665_; 
v_nondep_665_ = lean_ctor_get_uint8(v_val_544_, sizeof(void*)*5);
if (v_nondep_665_ == 0)
{
lean_object* v_type_666_; lean_object* v_value_667_; lean_object* v___x_668_; lean_object* v_mctx_669_; lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v_type_666_ = lean_ctor_get(v_val_544_, 3);
v_value_667_ = lean_ctor_get(v_val_544_, 4);
v___x_668_ = lean_st_ref_get(v___y_524_);
v_mctx_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc_ref(v_mctx_669_);
lean_dec(v___x_668_);
v___x_670_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1);
v___x_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
lean_ctor_set(v___x_671_, 1, v_mctx_669_);
v___x_672_ = l_Lean_Expr_hasFVar(v_type_666_);
if (v___x_672_ == 0)
{
uint8_t v___x_673_; 
v___x_673_ = l_Lean_Expr_hasMVar(v_type_666_);
if (v___x_673_ == 0)
{
lean_inc_ref(v_value_667_);
v___y_636_ = v___f_655_;
v___y_637_ = v_value_667_;
v_snd_638_ = v___x_671_;
goto v___jp_635_;
}
else
{
lean_object* v___x_674_; 
lean_inc_ref(v_type_666_);
lean_inc_ref(v___f_655_);
lean_inc_ref(v___f_634_);
v___x_674_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_634_, v___f_655_, v_type_666_, v___x_671_);
lean_inc_ref(v_value_667_);
v___y_644_ = v___f_655_;
v___y_645_ = v_value_667_;
v___y_646_ = v___x_674_;
goto v___jp_643_;
}
}
else
{
lean_object* v___x_675_; 
lean_inc_ref(v_type_666_);
lean_inc_ref(v___f_655_);
lean_inc_ref(v___f_634_);
v___x_675_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_634_, v___f_655_, v_type_666_, v___x_671_);
lean_inc_ref(v_value_667_);
v___y_644_ = v___f_655_;
v___y_645_ = v_value_667_;
v___y_646_ = v___x_675_;
goto v___jp_643_;
}
}
else
{
lean_object* v_type_676_; lean_object* v___x_677_; lean_object* v_mctx_678_; lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v_type_676_ = lean_ctor_get(v_val_544_, 3);
v___x_677_ = lean_st_ref_get(v___y_524_);
v_mctx_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc_ref_n(v_mctx_678_, 2);
lean_dec(v___x_677_);
v___x_679_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1);
v___x_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
lean_ctor_set(v___x_680_, 1, v_mctx_678_);
v___x_681_ = l_Lean_Expr_hasFVar(v_type_676_);
if (v___x_681_ == 0)
{
uint8_t v___x_682_; 
v___x_682_ = l_Lean_Expr_hasMVar(v_type_676_);
if (v___x_682_ == 0)
{
lean_dec_ref_known(v___x_680_, 2);
lean_dec_ref(v___f_655_);
lean_dec_ref(v___f_634_);
v_fst_562_ = v___x_682_;
v_mctx_563_ = v_mctx_678_;
goto v___jp_561_;
}
else
{
lean_object* v___x_683_; 
lean_dec_ref(v_mctx_678_);
lean_inc_ref(v_type_676_);
v___x_683_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_634_, v___f_655_, v_type_676_, v___x_680_);
v___y_579_ = v___x_683_;
goto v___jp_578_;
}
}
else
{
lean_object* v___x_684_; 
lean_dec_ref(v_mctx_678_);
lean_inc_ref(v_type_676_);
v___x_684_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_634_, v___f_655_, v_type_676_, v___x_680_);
v___y_579_ = v___x_684_;
goto v___jp_578_;
}
}
}
}
}
else
{
lean_dec(v___x_554_);
goto v___jp_550_;
}
}
else
{
lean_dec(v___x_554_);
goto v___jp_550_;
}
}
else
{
lean_object* v___x_686_; 
lean_dec(v___x_554_);
lean_del_object(v___x_548_);
v___x_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_686_, 0, v_fst_545_);
lean_ctor_set(v___x_686_, 1, v_snd_546_);
v_a_536_ = v___x_686_;
goto v___jp_535_;
}
v___jp_550_:
{
lean_object* v___x_552_; 
if (v_isShared_549_ == 0)
{
v___x_552_ = v___x_548_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_fst_545_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_snd_546_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
v_a_536_ = v___x_552_;
goto v___jp_535_;
}
}
v___jp_555_:
{
if (v_a_556_ == 0)
{
lean_object* v___x_557_; 
lean_dec(v___x_554_);
v___x_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_557_, 0, v_fst_545_);
lean_ctor_set(v___x_557_, 1, v_snd_546_);
v_a_536_ = v___x_557_;
goto v___jp_535_;
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
lean_inc(v___x_554_);
v___x_558_ = l_Lean_FVarIdSet_insert(v_snd_546_, v___x_554_);
v___x_559_ = l_Lean_FVarIdSet_insert(v_fst_545_, v___x_554_);
v___x_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
lean_ctor_set(v___x_560_, 1, v___x_558_);
v_a_536_ = v___x_560_;
goto v___jp_535_;
}
}
v___jp_561_:
{
lean_object* v___x_564_; lean_object* v_cache_565_; lean_object* v_zetaDeltaFVarIds_566_; lean_object* v_postponed_567_; lean_object* v_diag_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_576_; 
v___x_564_ = lean_st_ref_take(v___y_524_);
v_cache_565_ = lean_ctor_get(v___x_564_, 1);
v_zetaDeltaFVarIds_566_ = lean_ctor_get(v___x_564_, 2);
v_postponed_567_ = lean_ctor_get(v___x_564_, 3);
v_diag_568_ = lean_ctor_get(v___x_564_, 4);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_576_ == 0)
{
lean_object* v_unused_577_; 
v_unused_577_ = lean_ctor_get(v___x_564_, 0);
lean_dec(v_unused_577_);
v___x_570_ = v___x_564_;
v_isShared_571_ = v_isSharedCheck_576_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_diag_568_);
lean_inc(v_postponed_567_);
lean_inc(v_zetaDeltaFVarIds_566_);
lean_inc(v_cache_565_);
lean_dec(v___x_564_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_576_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v_mctx_563_);
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_mctx_563_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v_cache_565_);
lean_ctor_set(v_reuseFailAlloc_575_, 2, v_zetaDeltaFVarIds_566_);
lean_ctor_set(v_reuseFailAlloc_575_, 3, v_postponed_567_);
lean_ctor_set(v_reuseFailAlloc_575_, 4, v_diag_568_);
v___x_573_ = v_reuseFailAlloc_575_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
lean_object* v___x_574_; 
v___x_574_ = lean_st_ref_put(v___y_524_, v___x_573_);
v_a_556_ = v_fst_562_;
goto v___jp_555_;
}
}
}
v___jp_578_:
{
lean_object* v_snd_580_; lean_object* v_fst_581_; lean_object* v_mctx_582_; uint8_t v___x_583_; 
v_snd_580_ = lean_ctor_get(v___y_579_, 1);
lean_inc(v_snd_580_);
v_fst_581_ = lean_ctor_get(v___y_579_, 0);
lean_inc(v_fst_581_);
lean_dec_ref(v___y_579_);
v_mctx_582_ = lean_ctor_get(v_snd_580_, 1);
lean_inc_ref(v_mctx_582_);
lean_dec(v_snd_580_);
v___x_583_ = lean_unbox(v_fst_581_);
lean_dec(v_fst_581_);
v_fst_562_ = v___x_583_;
v_mctx_563_ = v_mctx_582_;
goto v___jp_561_;
}
v___jp_584_:
{
lean_object* v_mctx_587_; lean_object* v___x_588_; lean_object* v_cache_589_; lean_object* v_zetaDeltaFVarIds_590_; lean_object* v_postponed_591_; lean_object* v_diag_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_600_; 
v_mctx_587_ = lean_ctor_get(v_snd_586_, 1);
lean_inc_ref(v_mctx_587_);
lean_dec_ref(v_snd_586_);
v___x_588_ = lean_st_ref_take(v___y_524_);
v_cache_589_ = lean_ctor_get(v___x_588_, 1);
v_zetaDeltaFVarIds_590_ = lean_ctor_get(v___x_588_, 2);
v_postponed_591_ = lean_ctor_get(v___x_588_, 3);
v_diag_592_ = lean_ctor_get(v___x_588_, 4);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_600_ == 0)
{
lean_object* v_unused_601_; 
v_unused_601_ = lean_ctor_get(v___x_588_, 0);
lean_dec(v_unused_601_);
v___x_594_ = v___x_588_;
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_diag_592_);
lean_inc(v_postponed_591_);
lean_inc(v_zetaDeltaFVarIds_590_);
lean_inc(v_cache_589_);
lean_dec(v___x_588_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v_mctx_587_);
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_mctx_587_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_cache_589_);
lean_ctor_set(v_reuseFailAlloc_599_, 2, v_zetaDeltaFVarIds_590_);
lean_ctor_set(v_reuseFailAlloc_599_, 3, v_postponed_591_);
lean_ctor_set(v_reuseFailAlloc_599_, 4, v_diag_592_);
v___x_597_ = v_reuseFailAlloc_599_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
lean_object* v___x_598_; 
v___x_598_ = lean_st_ref_put(v___y_524_, v___x_597_);
v_a_556_ = v_fst_585_;
goto v___jp_555_;
}
}
}
v___jp_602_:
{
lean_object* v_fst_604_; lean_object* v_snd_605_; uint8_t v___x_606_; 
v_fst_604_ = lean_ctor_get(v___y_603_, 0);
lean_inc(v_fst_604_);
v_snd_605_ = lean_ctor_get(v___y_603_, 1);
lean_inc(v_snd_605_);
lean_dec_ref(v___y_603_);
v___x_606_ = lean_unbox(v_fst_604_);
lean_dec(v_fst_604_);
v_fst_585_ = v___x_606_;
v_snd_586_ = v_snd_605_;
goto v___jp_584_;
}
v___jp_607_:
{
lean_object* v___x_610_; lean_object* v_cache_611_; lean_object* v_zetaDeltaFVarIds_612_; lean_object* v_postponed_613_; lean_object* v_diag_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_622_; 
v___x_610_ = lean_st_ref_take(v___y_524_);
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
v___x_620_ = lean_st_ref_put(v___y_524_, v___x_619_);
v_a_556_ = v_fst_608_;
goto v___jp_555_;
}
}
}
v___jp_624_:
{
lean_object* v_snd_626_; lean_object* v_fst_627_; lean_object* v_mctx_628_; uint8_t v___x_629_; 
v_snd_626_ = lean_ctor_get(v___y_625_, 1);
lean_inc(v_snd_626_);
v_fst_627_ = lean_ctor_get(v___y_625_, 0);
lean_inc(v_fst_627_);
lean_dec_ref(v___y_625_);
v_mctx_628_ = lean_ctor_get(v_snd_626_, 1);
lean_inc_ref(v_mctx_628_);
lean_dec(v_snd_626_);
v___x_629_ = lean_unbox(v_fst_627_);
lean_dec(v_fst_627_);
v_fst_608_ = v___x_629_;
v_mctx_609_ = v_mctx_628_;
goto v___jp_607_;
}
}
}
v___jp_535_:
{
lean_object* v___x_538_; 
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 1, v_a_536_);
lean_ctor_set(v___x_532_, 0, v___x_534_);
v___x_538_ = v___x_532_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_534_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_a_536_);
v___x_538_ = v_reuseFailAlloc_542_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
size_t v___x_539_; size_t v___x_540_; lean_object* v___x_541_; 
v___x_539_ = ((size_t)1ULL);
v___x_540_ = lean_usize_add(v_i_521_, v___x_539_);
v___x_541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(v_forbidden_517_, v_ignoreLetDecls_518_, v_as_519_, v_sz_520_, v___x_540_, v___x_538_, v___y_524_);
return v___x_541_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___boxed(lean_object* v_forbidden_690_, lean_object* v_ignoreLetDecls_691_, lean_object* v_as_692_, lean_object* v_sz_693_, lean_object* v_i_694_, lean_object* v_b_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_701_; size_t v_sz_boxed_702_; size_t v_i_boxed_703_; lean_object* v_res_704_; 
v_ignoreLetDecls_boxed_701_ = lean_unbox(v_ignoreLetDecls_691_);
v_sz_boxed_702_ = lean_unbox_usize(v_sz_693_);
lean_dec(v_sz_693_);
v_i_boxed_703_ = lean_unbox_usize(v_i_694_);
lean_dec(v_i_694_);
v_res_704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1(v_forbidden_690_, v_ignoreLetDecls_boxed_701_, v_as_692_, v_sz_boxed_702_, v_i_boxed_703_, v_b_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec_ref(v_as_692_);
lean_dec(v_forbidden_690_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_forbidden_705_, uint8_t v_ignoreLetDecls_706_, lean_object* v_as_707_, size_t v_sz_708_, size_t v_i_709_, lean_object* v_b_710_, lean_object* v___y_711_){
_start:
{
uint8_t v___x_713_; 
v___x_713_ = lean_usize_dec_lt(v_i_709_, v_sz_708_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; 
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v_b_710_);
return v___x_714_;
}
else
{
lean_object* v_snd_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_873_; 
v_snd_715_ = lean_ctor_get(v_b_710_, 1);
v_isSharedCheck_873_ = !lean_is_exclusive(v_b_710_);
if (v_isSharedCheck_873_ == 0)
{
lean_object* v_unused_874_; 
v_unused_874_ = lean_ctor_get(v_b_710_, 0);
lean_dec(v_unused_874_);
v___x_717_ = v_b_710_;
v_isShared_718_ = v_isSharedCheck_873_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_snd_715_);
lean_dec(v_b_710_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_873_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_719_; lean_object* v_a_721_; lean_object* v_a_728_; 
v___x_719_ = lean_box(0);
v_a_728_ = lean_array_uget_borrowed(v_as_707_, v_i_709_);
if (lean_obj_tag(v_a_728_) == 0)
{
v_a_721_ = v_snd_715_;
goto v___jp_720_;
}
else
{
lean_object* v_val_729_; lean_object* v_fst_730_; lean_object* v_snd_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_872_; 
v_val_729_ = lean_ctor_get(v_a_728_, 0);
v_fst_730_ = lean_ctor_get(v_snd_715_, 0);
v_snd_731_ = lean_ctor_get(v_snd_715_, 1);
v_isSharedCheck_872_ = !lean_is_exclusive(v_snd_715_);
if (v_isSharedCheck_872_ == 0)
{
v___x_733_ = v_snd_715_;
v_isShared_734_ = v_isSharedCheck_872_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_snd_731_);
lean_inc(v_fst_730_);
lean_dec(v_snd_715_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_872_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_739_; uint8_t v_a_741_; uint8_t v_fst_747_; lean_object* v_mctx_748_; lean_object* v___y_764_; uint8_t v_fst_770_; lean_object* v_snd_771_; lean_object* v___y_788_; uint8_t v_fst_793_; lean_object* v_mctx_794_; lean_object* v___y_810_; uint8_t v___x_815_; 
v___x_739_ = l_Lean_LocalDecl_fvarId(v_val_729_);
v___x_815_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v___x_739_, v_forbidden_705_);
if (v___x_815_ == 0)
{
uint8_t v___x_816_; 
v___x_816_ = l_Lean_LocalDecl_isAuxDecl(v_val_729_);
if (v___x_816_ == 0)
{
uint8_t v___x_817_; uint8_t v___x_818_; 
v___x_817_ = l_Lean_LocalDecl_binderInfo(v_val_729_);
v___x_818_ = l_Lean_BinderInfo_isInstImplicit(v___x_817_);
if (v___x_818_ == 0)
{
lean_object* v___f_819_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v_snd_823_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; uint8_t v___y_838_; 
lean_inc(v_fst_730_);
v___f_819_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_819_, 0, v_fst_730_);
if (v_ignoreLetDecls_706_ == 0)
{
lean_del_object(v___x_733_);
v___y_838_ = v___x_815_;
goto v___jp_837_;
}
else
{
uint8_t v___x_870_; 
v___x_870_ = l_Lean_LocalDecl_isLet(v_val_729_, v___x_815_);
if (v___x_870_ == 0)
{
lean_del_object(v___x_733_);
v___y_838_ = v___x_870_;
goto v___jp_837_;
}
else
{
lean_dec_ref(v___f_819_);
lean_dec(v___x_739_);
goto v___jp_735_;
}
}
v___jp_820_:
{
uint8_t v___x_824_; 
v___x_824_ = l_Lean_Expr_hasFVar(v___y_822_);
if (v___x_824_ == 0)
{
uint8_t v___x_825_; 
v___x_825_ = l_Lean_Expr_hasMVar(v___y_822_);
if (v___x_825_ == 0)
{
lean_dec_ref(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec_ref(v___f_819_);
v_fst_770_ = v___x_825_;
v_snd_771_ = v_snd_823_;
goto v___jp_769_;
}
else
{
lean_object* v___x_826_; 
v___x_826_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_819_, v___y_821_, v___y_822_, v_snd_823_);
v___y_788_ = v___x_826_;
goto v___jp_787_;
}
}
else
{
lean_object* v___x_827_; 
v___x_827_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_819_, v___y_821_, v___y_822_, v_snd_823_);
v___y_788_ = v___x_827_;
goto v___jp_787_;
}
}
v___jp_828_:
{
lean_object* v_fst_832_; uint8_t v___x_833_; 
v_fst_832_ = lean_ctor_get(v___y_831_, 0);
v___x_833_ = lean_unbox(v_fst_832_);
if (v___x_833_ == 0)
{
lean_object* v_snd_834_; 
v_snd_834_ = lean_ctor_get(v___y_831_, 1);
lean_inc(v_snd_834_);
lean_dec_ref(v___y_831_);
v___y_821_ = v___y_830_;
v___y_822_ = v___y_829_;
v_snd_823_ = v_snd_834_;
goto v___jp_820_;
}
else
{
lean_object* v_snd_835_; uint8_t v___x_836_; 
lean_inc(v_fst_832_);
lean_dec_ref(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec_ref(v___f_819_);
v_snd_835_ = lean_ctor_get(v___y_831_, 1);
lean_inc(v_snd_835_);
lean_dec_ref(v___y_831_);
v___x_836_ = lean_unbox(v_fst_832_);
lean_dec(v_fst_832_);
v_fst_770_ = v___x_836_;
v_snd_771_ = v_snd_835_;
goto v___jp_769_;
}
}
v___jp_837_:
{
lean_object* v___x_839_; lean_object* v___f_840_; 
v___x_839_ = lean_box(v___y_838_);
v___f_840_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(v___f_840_, 0, v___x_839_);
if (lean_obj_tag(v_val_729_) == 0)
{
lean_object* v_type_841_; lean_object* v___x_842_; lean_object* v_mctx_843_; lean_object* v___x_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v_type_841_ = lean_ctor_get(v_val_729_, 3);
v___x_842_ = lean_st_ref_get(v___y_711_);
v_mctx_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc_ref_n(v_mctx_843_, 2);
lean_dec(v___x_842_);
v___x_844_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1);
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
lean_dec_ref_known(v___x_845_, 2);
lean_dec_ref(v___f_840_);
lean_dec_ref(v___f_819_);
v_fst_793_ = v___x_847_;
v_mctx_794_ = v_mctx_843_;
goto v___jp_792_;
}
else
{
lean_object* v___x_848_; 
lean_dec_ref(v_mctx_843_);
lean_inc_ref(v_type_841_);
v___x_848_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_819_, v___f_840_, v_type_841_, v___x_845_);
v___y_810_ = v___x_848_;
goto v___jp_809_;
}
}
else
{
lean_object* v___x_849_; 
lean_dec_ref(v_mctx_843_);
lean_inc_ref(v_type_841_);
v___x_849_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_819_, v___f_840_, v_type_841_, v___x_845_);
v___y_810_ = v___x_849_;
goto v___jp_809_;
}
}
else
{
uint8_t v_nondep_850_; 
v_nondep_850_ = lean_ctor_get_uint8(v_val_729_, sizeof(void*)*5);
if (v_nondep_850_ == 0)
{
lean_object* v_type_851_; lean_object* v_value_852_; lean_object* v___x_853_; lean_object* v_mctx_854_; lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v_type_851_ = lean_ctor_get(v_val_729_, 3);
v_value_852_ = lean_ctor_get(v_val_729_, 4);
v___x_853_ = lean_st_ref_get(v___y_711_);
v_mctx_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc_ref(v_mctx_854_);
lean_dec(v___x_853_);
v___x_855_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1);
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
v___y_821_ = v___f_840_;
v___y_822_ = v_value_852_;
v_snd_823_ = v___x_856_;
goto v___jp_820_;
}
else
{
lean_object* v___x_859_; 
lean_inc_ref(v_type_851_);
lean_inc_ref(v___f_840_);
lean_inc_ref(v___f_819_);
v___x_859_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_819_, v___f_840_, v_type_851_, v___x_856_);
lean_inc_ref(v_value_852_);
v___y_829_ = v_value_852_;
v___y_830_ = v___f_840_;
v___y_831_ = v___x_859_;
goto v___jp_828_;
}
}
else
{
lean_object* v___x_860_; 
lean_inc_ref(v_type_851_);
lean_inc_ref(v___f_840_);
lean_inc_ref(v___f_819_);
v___x_860_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_819_, v___f_840_, v_type_851_, v___x_856_);
lean_inc_ref(v_value_852_);
v___y_829_ = v_value_852_;
v___y_830_ = v___f_840_;
v___y_831_ = v___x_860_;
goto v___jp_828_;
}
}
else
{
lean_object* v_type_861_; lean_object* v___x_862_; lean_object* v_mctx_863_; lean_object* v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
v_type_861_ = lean_ctor_get(v_val_729_, 3);
v___x_862_ = lean_st_ref_get(v___y_711_);
v_mctx_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc_ref_n(v_mctx_863_, 2);
lean_dec(v___x_862_);
v___x_864_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1);
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
lean_dec_ref_known(v___x_865_, 2);
lean_dec_ref(v___f_840_);
lean_dec_ref(v___f_819_);
v_fst_747_ = v___x_867_;
v_mctx_748_ = v_mctx_863_;
goto v___jp_746_;
}
else
{
lean_object* v___x_868_; 
lean_dec_ref(v_mctx_863_);
lean_inc_ref(v_type_861_);
v___x_868_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_819_, v___f_840_, v_type_861_, v___x_865_);
v___y_764_ = v___x_868_;
goto v___jp_763_;
}
}
else
{
lean_object* v___x_869_; 
lean_dec_ref(v_mctx_863_);
lean_inc_ref(v_type_861_);
v___x_869_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_819_, v___f_840_, v_type_861_, v___x_865_);
v___y_764_ = v___x_869_;
goto v___jp_763_;
}
}
}
}
}
else
{
lean_dec(v___x_739_);
goto v___jp_735_;
}
}
else
{
lean_dec(v___x_739_);
goto v___jp_735_;
}
}
else
{
lean_object* v___x_871_; 
lean_dec(v___x_739_);
lean_del_object(v___x_733_);
v___x_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_871_, 0, v_fst_730_);
lean_ctor_set(v___x_871_, 1, v_snd_731_);
v_a_721_ = v___x_871_;
goto v___jp_720_;
}
v___jp_735_:
{
lean_object* v___x_737_; 
if (v_isShared_734_ == 0)
{
v___x_737_ = v___x_733_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_fst_730_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_snd_731_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
v_a_721_ = v___x_737_;
goto v___jp_720_;
}
}
v___jp_740_:
{
if (v_a_741_ == 0)
{
lean_object* v___x_742_; 
lean_dec(v___x_739_);
v___x_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_742_, 0, v_fst_730_);
lean_ctor_set(v___x_742_, 1, v_snd_731_);
v_a_721_ = v___x_742_;
goto v___jp_720_;
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
lean_inc(v___x_739_);
v___x_743_ = l_Lean_FVarIdSet_insert(v_snd_731_, v___x_739_);
v___x_744_ = l_Lean_FVarIdSet_insert(v_fst_730_, v___x_739_);
v___x_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
lean_ctor_set(v___x_745_, 1, v___x_743_);
v_a_721_ = v___x_745_;
goto v___jp_720_;
}
}
v___jp_746_:
{
lean_object* v___x_749_; lean_object* v_cache_750_; lean_object* v_zetaDeltaFVarIds_751_; lean_object* v_postponed_752_; lean_object* v_diag_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_761_; 
v___x_749_ = lean_st_ref_take(v___y_711_);
v_cache_750_ = lean_ctor_get(v___x_749_, 1);
v_zetaDeltaFVarIds_751_ = lean_ctor_get(v___x_749_, 2);
v_postponed_752_ = lean_ctor_get(v___x_749_, 3);
v_diag_753_ = lean_ctor_get(v___x_749_, 4);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_761_ == 0)
{
lean_object* v_unused_762_; 
v_unused_762_ = lean_ctor_get(v___x_749_, 0);
lean_dec(v_unused_762_);
v___x_755_ = v___x_749_;
v_isShared_756_ = v_isSharedCheck_761_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_diag_753_);
lean_inc(v_postponed_752_);
lean_inc(v_zetaDeltaFVarIds_751_);
lean_inc(v_cache_750_);
lean_dec(v___x_749_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_761_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v_mctx_748_);
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_mctx_748_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_cache_750_);
lean_ctor_set(v_reuseFailAlloc_760_, 2, v_zetaDeltaFVarIds_751_);
lean_ctor_set(v_reuseFailAlloc_760_, 3, v_postponed_752_);
lean_ctor_set(v_reuseFailAlloc_760_, 4, v_diag_753_);
v___x_758_ = v_reuseFailAlloc_760_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_759_; 
v___x_759_ = lean_st_ref_put(v___y_711_, v___x_758_);
v_a_741_ = v_fst_747_;
goto v___jp_740_;
}
}
}
v___jp_763_:
{
lean_object* v_snd_765_; lean_object* v_fst_766_; lean_object* v_mctx_767_; uint8_t v___x_768_; 
v_snd_765_ = lean_ctor_get(v___y_764_, 1);
lean_inc(v_snd_765_);
v_fst_766_ = lean_ctor_get(v___y_764_, 0);
lean_inc(v_fst_766_);
lean_dec_ref(v___y_764_);
v_mctx_767_ = lean_ctor_get(v_snd_765_, 1);
lean_inc_ref(v_mctx_767_);
lean_dec(v_snd_765_);
v___x_768_ = lean_unbox(v_fst_766_);
lean_dec(v_fst_766_);
v_fst_747_ = v___x_768_;
v_mctx_748_ = v_mctx_767_;
goto v___jp_746_;
}
v___jp_769_:
{
lean_object* v_mctx_772_; lean_object* v___x_773_; lean_object* v_cache_774_; lean_object* v_zetaDeltaFVarIds_775_; lean_object* v_postponed_776_; lean_object* v_diag_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_785_; 
v_mctx_772_ = lean_ctor_get(v_snd_771_, 1);
lean_inc_ref(v_mctx_772_);
lean_dec_ref(v_snd_771_);
v___x_773_ = lean_st_ref_take(v___y_711_);
v_cache_774_ = lean_ctor_get(v___x_773_, 1);
v_zetaDeltaFVarIds_775_ = lean_ctor_get(v___x_773_, 2);
v_postponed_776_ = lean_ctor_get(v___x_773_, 3);
v_diag_777_ = lean_ctor_get(v___x_773_, 4);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_785_ == 0)
{
lean_object* v_unused_786_; 
v_unused_786_ = lean_ctor_get(v___x_773_, 0);
lean_dec(v_unused_786_);
v___x_779_ = v___x_773_;
v_isShared_780_ = v_isSharedCheck_785_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_diag_777_);
lean_inc(v_postponed_776_);
lean_inc(v_zetaDeltaFVarIds_775_);
lean_inc(v_cache_774_);
lean_dec(v___x_773_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_785_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v_mctx_772_);
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_mctx_772_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_cache_774_);
lean_ctor_set(v_reuseFailAlloc_784_, 2, v_zetaDeltaFVarIds_775_);
lean_ctor_set(v_reuseFailAlloc_784_, 3, v_postponed_776_);
lean_ctor_set(v_reuseFailAlloc_784_, 4, v_diag_777_);
v___x_782_ = v_reuseFailAlloc_784_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
lean_object* v___x_783_; 
v___x_783_ = lean_st_ref_put(v___y_711_, v___x_782_);
v_a_741_ = v_fst_770_;
goto v___jp_740_;
}
}
}
v___jp_787_:
{
lean_object* v_fst_789_; lean_object* v_snd_790_; uint8_t v___x_791_; 
v_fst_789_ = lean_ctor_get(v___y_788_, 0);
lean_inc(v_fst_789_);
v_snd_790_ = lean_ctor_get(v___y_788_, 1);
lean_inc(v_snd_790_);
lean_dec_ref(v___y_788_);
v___x_791_ = lean_unbox(v_fst_789_);
lean_dec(v_fst_789_);
v_fst_770_ = v___x_791_;
v_snd_771_ = v_snd_790_;
goto v___jp_769_;
}
v___jp_792_:
{
lean_object* v___x_795_; lean_object* v_cache_796_; lean_object* v_zetaDeltaFVarIds_797_; lean_object* v_postponed_798_; lean_object* v_diag_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_807_; 
v___x_795_ = lean_st_ref_take(v___y_711_);
v_cache_796_ = lean_ctor_get(v___x_795_, 1);
v_zetaDeltaFVarIds_797_ = lean_ctor_get(v___x_795_, 2);
v_postponed_798_ = lean_ctor_get(v___x_795_, 3);
v_diag_799_ = lean_ctor_get(v___x_795_, 4);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_807_ == 0)
{
lean_object* v_unused_808_; 
v_unused_808_ = lean_ctor_get(v___x_795_, 0);
lean_dec(v_unused_808_);
v___x_801_ = v___x_795_;
v_isShared_802_ = v_isSharedCheck_807_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_diag_799_);
lean_inc(v_postponed_798_);
lean_inc(v_zetaDeltaFVarIds_797_);
lean_inc(v_cache_796_);
lean_dec(v___x_795_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_807_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v_mctx_794_);
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_mctx_794_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_cache_796_);
lean_ctor_set(v_reuseFailAlloc_806_, 2, v_zetaDeltaFVarIds_797_);
lean_ctor_set(v_reuseFailAlloc_806_, 3, v_postponed_798_);
lean_ctor_set(v_reuseFailAlloc_806_, 4, v_diag_799_);
v___x_804_ = v_reuseFailAlloc_806_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
lean_object* v___x_805_; 
v___x_805_ = lean_st_ref_put(v___y_711_, v___x_804_);
v_a_741_ = v_fst_793_;
goto v___jp_740_;
}
}
}
v___jp_809_:
{
lean_object* v_snd_811_; lean_object* v_fst_812_; lean_object* v_mctx_813_; uint8_t v___x_814_; 
v_snd_811_ = lean_ctor_get(v___y_810_, 1);
lean_inc(v_snd_811_);
v_fst_812_ = lean_ctor_get(v___y_810_, 0);
lean_inc(v_fst_812_);
lean_dec_ref(v___y_810_);
v_mctx_813_ = lean_ctor_get(v_snd_811_, 1);
lean_inc_ref(v_mctx_813_);
lean_dec(v_snd_811_);
v___x_814_ = lean_unbox(v_fst_812_);
lean_dec(v_fst_812_);
v_fst_793_ = v___x_814_;
v_mctx_794_ = v_mctx_813_;
goto v___jp_792_;
}
}
}
v___jp_720_:
{
lean_object* v___x_723_; 
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 1, v_a_721_);
lean_ctor_set(v___x_717_, 0, v___x_719_);
v___x_723_ = v___x_717_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_a_721_);
v___x_723_ = v_reuseFailAlloc_727_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
size_t v___x_724_; size_t v___x_725_; 
v___x_724_ = ((size_t)1ULL);
v___x_725_ = lean_usize_add(v_i_709_, v___x_724_);
v_i_709_ = v___x_725_;
v_b_710_ = v___x_723_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_forbidden_875_, lean_object* v_ignoreLetDecls_876_, lean_object* v_as_877_, lean_object* v_sz_878_, lean_object* v_i_879_, lean_object* v_b_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_883_; size_t v_sz_boxed_884_; size_t v_i_boxed_885_; lean_object* v_res_886_; 
v_ignoreLetDecls_boxed_883_ = lean_unbox(v_ignoreLetDecls_876_);
v_sz_boxed_884_ = lean_unbox_usize(v_sz_878_);
lean_dec(v_sz_878_);
v_i_boxed_885_ = lean_unbox_usize(v_i_879_);
lean_dec(v_i_879_);
v_res_886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(v_forbidden_875_, v_ignoreLetDecls_boxed_883_, v_as_877_, v_sz_boxed_884_, v_i_boxed_885_, v_b_880_, v___y_881_);
lean_dec(v___y_881_);
lean_dec_ref(v_as_877_);
lean_dec(v_forbidden_875_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2(lean_object* v_forbidden_887_, uint8_t v_ignoreLetDecls_888_, lean_object* v_as_889_, size_t v_sz_890_, size_t v_i_891_, lean_object* v_b_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
uint8_t v___x_898_; 
v___x_898_ = lean_usize_dec_lt(v_i_891_, v_sz_890_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; 
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v_b_892_);
return v___x_899_;
}
else
{
lean_object* v_snd_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_1058_; 
v_snd_900_ = lean_ctor_get(v_b_892_, 1);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_b_892_);
if (v_isSharedCheck_1058_ == 0)
{
lean_object* v_unused_1059_; 
v_unused_1059_ = lean_ctor_get(v_b_892_, 0);
lean_dec(v_unused_1059_);
v___x_902_ = v_b_892_;
v_isShared_903_ = v_isSharedCheck_1058_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_snd_900_);
lean_dec(v_b_892_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_1058_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_904_; lean_object* v_a_906_; lean_object* v_a_913_; 
v___x_904_ = lean_box(0);
v_a_913_ = lean_array_uget_borrowed(v_as_889_, v_i_891_);
if (lean_obj_tag(v_a_913_) == 0)
{
v_a_906_ = v_snd_900_;
goto v___jp_905_;
}
else
{
lean_object* v_val_914_; lean_object* v_fst_915_; lean_object* v_snd_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_1057_; 
v_val_914_ = lean_ctor_get(v_a_913_, 0);
v_fst_915_ = lean_ctor_get(v_snd_900_, 0);
v_snd_916_ = lean_ctor_get(v_snd_900_, 1);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_snd_900_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_918_ = v_snd_900_;
v_isShared_919_ = v_isSharedCheck_1057_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_snd_916_);
lean_inc(v_fst_915_);
lean_dec(v_snd_900_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_1057_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_924_; uint8_t v_a_926_; uint8_t v_fst_932_; lean_object* v_mctx_933_; lean_object* v___y_949_; uint8_t v_fst_955_; lean_object* v_snd_956_; lean_object* v___y_973_; uint8_t v_fst_978_; lean_object* v_mctx_979_; lean_object* v___y_995_; uint8_t v___x_1000_; 
v___x_924_ = l_Lean_LocalDecl_fvarId(v_val_914_);
v___x_1000_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v___x_924_, v_forbidden_887_);
if (v___x_1000_ == 0)
{
uint8_t v___x_1001_; 
v___x_1001_ = l_Lean_LocalDecl_isAuxDecl(v_val_914_);
if (v___x_1001_ == 0)
{
uint8_t v___x_1002_; uint8_t v___x_1003_; 
v___x_1002_ = l_Lean_LocalDecl_binderInfo(v_val_914_);
v___x_1003_ = l_Lean_BinderInfo_isInstImplicit(v___x_1002_);
if (v___x_1003_ == 0)
{
lean_object* v___f_1004_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v_snd_1008_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; uint8_t v___y_1023_; 
lean_inc(v_fst_915_);
v___f_1004_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1004_, 0, v_fst_915_);
if (v_ignoreLetDecls_888_ == 0)
{
lean_del_object(v___x_918_);
v___y_1023_ = v___x_1000_;
goto v___jp_1022_;
}
else
{
uint8_t v___x_1055_; 
v___x_1055_ = l_Lean_LocalDecl_isLet(v_val_914_, v___x_1000_);
if (v___x_1055_ == 0)
{
lean_del_object(v___x_918_);
v___y_1023_ = v___x_1055_;
goto v___jp_1022_;
}
else
{
lean_dec_ref(v___f_1004_);
lean_dec(v___x_924_);
goto v___jp_920_;
}
}
v___jp_1005_:
{
uint8_t v___x_1009_; 
v___x_1009_ = l_Lean_Expr_hasFVar(v___y_1007_);
if (v___x_1009_ == 0)
{
uint8_t v___x_1010_; 
v___x_1010_ = l_Lean_Expr_hasMVar(v___y_1007_);
if (v___x_1010_ == 0)
{
lean_dec_ref(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec_ref(v___f_1004_);
v_fst_955_ = v___x_1010_;
v_snd_956_ = v_snd_1008_;
goto v___jp_954_;
}
else
{
lean_object* v___x_1011_; 
v___x_1011_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1004_, v___y_1006_, v___y_1007_, v_snd_1008_);
v___y_973_ = v___x_1011_;
goto v___jp_972_;
}
}
else
{
lean_object* v___x_1012_; 
v___x_1012_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1004_, v___y_1006_, v___y_1007_, v_snd_1008_);
v___y_973_ = v___x_1012_;
goto v___jp_972_;
}
}
v___jp_1013_:
{
lean_object* v_fst_1017_; uint8_t v___x_1018_; 
v_fst_1017_ = lean_ctor_get(v___y_1016_, 0);
v___x_1018_ = lean_unbox(v_fst_1017_);
if (v___x_1018_ == 0)
{
lean_object* v_snd_1019_; 
v_snd_1019_ = lean_ctor_get(v___y_1016_, 1);
lean_inc(v_snd_1019_);
lean_dec_ref(v___y_1016_);
v___y_1006_ = v___y_1014_;
v___y_1007_ = v___y_1015_;
v_snd_1008_ = v_snd_1019_;
goto v___jp_1005_;
}
else
{
lean_object* v_snd_1020_; uint8_t v___x_1021_; 
lean_inc(v_fst_1017_);
lean_dec_ref(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec_ref(v___f_1004_);
v_snd_1020_ = lean_ctor_get(v___y_1016_, 1);
lean_inc(v_snd_1020_);
lean_dec_ref(v___y_1016_);
v___x_1021_ = lean_unbox(v_fst_1017_);
lean_dec(v_fst_1017_);
v_fst_955_ = v___x_1021_;
v_snd_956_ = v_snd_1020_;
goto v___jp_954_;
}
}
v___jp_1022_:
{
lean_object* v___x_1024_; lean_object* v___f_1025_; 
v___x_1024_ = lean_box(v___y_1023_);
v___f_1025_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1025_, 0, v___x_1024_);
if (lean_obj_tag(v_val_914_) == 0)
{
lean_object* v_type_1026_; lean_object* v___x_1027_; lean_object* v_mctx_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; uint8_t v___x_1031_; 
v_type_1026_ = lean_ctor_get(v_val_914_, 3);
v___x_1027_ = lean_st_ref_get(v___y_894_);
v_mctx_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc_ref_n(v_mctx_1028_, 2);
lean_dec(v___x_1027_);
v___x_1029_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1);
v___x_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
lean_ctor_set(v___x_1030_, 1, v_mctx_1028_);
v___x_1031_ = l_Lean_Expr_hasFVar(v_type_1026_);
if (v___x_1031_ == 0)
{
uint8_t v___x_1032_; 
v___x_1032_ = l_Lean_Expr_hasMVar(v_type_1026_);
if (v___x_1032_ == 0)
{
lean_dec_ref_known(v___x_1030_, 2);
lean_dec_ref(v___f_1025_);
lean_dec_ref(v___f_1004_);
v_fst_978_ = v___x_1032_;
v_mctx_979_ = v_mctx_1028_;
goto v___jp_977_;
}
else
{
lean_object* v___x_1033_; 
lean_dec_ref(v_mctx_1028_);
lean_inc_ref(v_type_1026_);
v___x_1033_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1004_, v___f_1025_, v_type_1026_, v___x_1030_);
v___y_995_ = v___x_1033_;
goto v___jp_994_;
}
}
else
{
lean_object* v___x_1034_; 
lean_dec_ref(v_mctx_1028_);
lean_inc_ref(v_type_1026_);
v___x_1034_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1004_, v___f_1025_, v_type_1026_, v___x_1030_);
v___y_995_ = v___x_1034_;
goto v___jp_994_;
}
}
else
{
uint8_t v_nondep_1035_; 
v_nondep_1035_ = lean_ctor_get_uint8(v_val_914_, sizeof(void*)*5);
if (v_nondep_1035_ == 0)
{
lean_object* v_type_1036_; lean_object* v_value_1037_; lean_object* v___x_1038_; lean_object* v_mctx_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; uint8_t v___x_1042_; 
v_type_1036_ = lean_ctor_get(v_val_914_, 3);
v_value_1037_ = lean_ctor_get(v_val_914_, 4);
v___x_1038_ = lean_st_ref_get(v___y_894_);
v_mctx_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc_ref(v_mctx_1039_);
lean_dec(v___x_1038_);
v___x_1040_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1);
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
lean_ctor_set(v___x_1041_, 1, v_mctx_1039_);
v___x_1042_ = l_Lean_Expr_hasFVar(v_type_1036_);
if (v___x_1042_ == 0)
{
uint8_t v___x_1043_; 
v___x_1043_ = l_Lean_Expr_hasMVar(v_type_1036_);
if (v___x_1043_ == 0)
{
lean_inc_ref(v_value_1037_);
v___y_1006_ = v___f_1025_;
v___y_1007_ = v_value_1037_;
v_snd_1008_ = v___x_1041_;
goto v___jp_1005_;
}
else
{
lean_object* v___x_1044_; 
lean_inc_ref(v_type_1036_);
lean_inc_ref(v___f_1025_);
lean_inc_ref(v___f_1004_);
v___x_1044_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1004_, v___f_1025_, v_type_1036_, v___x_1041_);
lean_inc_ref(v_value_1037_);
v___y_1014_ = v___f_1025_;
v___y_1015_ = v_value_1037_;
v___y_1016_ = v___x_1044_;
goto v___jp_1013_;
}
}
else
{
lean_object* v___x_1045_; 
lean_inc_ref(v_type_1036_);
lean_inc_ref(v___f_1025_);
lean_inc_ref(v___f_1004_);
v___x_1045_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1004_, v___f_1025_, v_type_1036_, v___x_1041_);
lean_inc_ref(v_value_1037_);
v___y_1014_ = v___f_1025_;
v___y_1015_ = v_value_1037_;
v___y_1016_ = v___x_1045_;
goto v___jp_1013_;
}
}
else
{
lean_object* v_type_1046_; lean_object* v___x_1047_; lean_object* v_mctx_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; uint8_t v___x_1051_; 
v_type_1046_ = lean_ctor_get(v_val_914_, 3);
v___x_1047_ = lean_st_ref_get(v___y_894_);
v_mctx_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc_ref_n(v_mctx_1048_, 2);
lean_dec(v___x_1047_);
v___x_1049_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___closed__1);
v___x_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set(v___x_1050_, 1, v_mctx_1048_);
v___x_1051_ = l_Lean_Expr_hasFVar(v_type_1046_);
if (v___x_1051_ == 0)
{
uint8_t v___x_1052_; 
v___x_1052_ = l_Lean_Expr_hasMVar(v_type_1046_);
if (v___x_1052_ == 0)
{
lean_dec_ref_known(v___x_1050_, 2);
lean_dec_ref(v___f_1025_);
lean_dec_ref(v___f_1004_);
v_fst_932_ = v___x_1052_;
v_mctx_933_ = v_mctx_1048_;
goto v___jp_931_;
}
else
{
lean_object* v___x_1053_; 
lean_dec_ref(v_mctx_1048_);
lean_inc_ref(v_type_1046_);
v___x_1053_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1004_, v___f_1025_, v_type_1046_, v___x_1050_);
v___y_949_ = v___x_1053_;
goto v___jp_948_;
}
}
else
{
lean_object* v___x_1054_; 
lean_dec_ref(v_mctx_1048_);
lean_inc_ref(v_type_1046_);
v___x_1054_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1004_, v___f_1025_, v_type_1046_, v___x_1050_);
v___y_949_ = v___x_1054_;
goto v___jp_948_;
}
}
}
}
}
else
{
lean_dec(v___x_924_);
goto v___jp_920_;
}
}
else
{
lean_dec(v___x_924_);
goto v___jp_920_;
}
}
else
{
lean_object* v___x_1056_; 
lean_dec(v___x_924_);
lean_del_object(v___x_918_);
v___x_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1056_, 0, v_fst_915_);
lean_ctor_set(v___x_1056_, 1, v_snd_916_);
v_a_906_ = v___x_1056_;
goto v___jp_905_;
}
v___jp_920_:
{
lean_object* v___x_922_; 
if (v_isShared_919_ == 0)
{
v___x_922_ = v___x_918_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_fst_915_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_snd_916_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
v_a_906_ = v___x_922_;
goto v___jp_905_;
}
}
v___jp_925_:
{
if (v_a_926_ == 0)
{
lean_object* v___x_927_; 
lean_dec(v___x_924_);
v___x_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_927_, 0, v_fst_915_);
lean_ctor_set(v___x_927_, 1, v_snd_916_);
v_a_906_ = v___x_927_;
goto v___jp_905_;
}
else
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
lean_inc(v___x_924_);
v___x_928_ = l_Lean_FVarIdSet_insert(v_snd_916_, v___x_924_);
v___x_929_ = l_Lean_FVarIdSet_insert(v_fst_915_, v___x_924_);
v___x_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
lean_ctor_set(v___x_930_, 1, v___x_928_);
v_a_906_ = v___x_930_;
goto v___jp_905_;
}
}
v___jp_931_:
{
lean_object* v___x_934_; lean_object* v_cache_935_; lean_object* v_zetaDeltaFVarIds_936_; lean_object* v_postponed_937_; lean_object* v_diag_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_946_; 
v___x_934_ = lean_st_ref_take(v___y_894_);
v_cache_935_ = lean_ctor_get(v___x_934_, 1);
v_zetaDeltaFVarIds_936_ = lean_ctor_get(v___x_934_, 2);
v_postponed_937_ = lean_ctor_get(v___x_934_, 3);
v_diag_938_ = lean_ctor_get(v___x_934_, 4);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_946_ == 0)
{
lean_object* v_unused_947_; 
v_unused_947_ = lean_ctor_get(v___x_934_, 0);
lean_dec(v_unused_947_);
v___x_940_ = v___x_934_;
v_isShared_941_ = v_isSharedCheck_946_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_diag_938_);
lean_inc(v_postponed_937_);
lean_inc(v_zetaDeltaFVarIds_936_);
lean_inc(v_cache_935_);
lean_dec(v___x_934_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_946_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v_mctx_933_);
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_mctx_933_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v_cache_935_);
lean_ctor_set(v_reuseFailAlloc_945_, 2, v_zetaDeltaFVarIds_936_);
lean_ctor_set(v_reuseFailAlloc_945_, 3, v_postponed_937_);
lean_ctor_set(v_reuseFailAlloc_945_, 4, v_diag_938_);
v___x_943_ = v_reuseFailAlloc_945_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_944_; 
v___x_944_ = lean_st_ref_put(v___y_894_, v___x_943_);
v_a_926_ = v_fst_932_;
goto v___jp_925_;
}
}
}
v___jp_948_:
{
lean_object* v_snd_950_; lean_object* v_fst_951_; lean_object* v_mctx_952_; uint8_t v___x_953_; 
v_snd_950_ = lean_ctor_get(v___y_949_, 1);
lean_inc(v_snd_950_);
v_fst_951_ = lean_ctor_get(v___y_949_, 0);
lean_inc(v_fst_951_);
lean_dec_ref(v___y_949_);
v_mctx_952_ = lean_ctor_get(v_snd_950_, 1);
lean_inc_ref(v_mctx_952_);
lean_dec(v_snd_950_);
v___x_953_ = lean_unbox(v_fst_951_);
lean_dec(v_fst_951_);
v_fst_932_ = v___x_953_;
v_mctx_933_ = v_mctx_952_;
goto v___jp_931_;
}
v___jp_954_:
{
lean_object* v_mctx_957_; lean_object* v___x_958_; lean_object* v_cache_959_; lean_object* v_zetaDeltaFVarIds_960_; lean_object* v_postponed_961_; lean_object* v_diag_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_970_; 
v_mctx_957_ = lean_ctor_get(v_snd_956_, 1);
lean_inc_ref(v_mctx_957_);
lean_dec_ref(v_snd_956_);
v___x_958_ = lean_st_ref_take(v___y_894_);
v_cache_959_ = lean_ctor_get(v___x_958_, 1);
v_zetaDeltaFVarIds_960_ = lean_ctor_get(v___x_958_, 2);
v_postponed_961_ = lean_ctor_get(v___x_958_, 3);
v_diag_962_ = lean_ctor_get(v___x_958_, 4);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_970_ == 0)
{
lean_object* v_unused_971_; 
v_unused_971_ = lean_ctor_get(v___x_958_, 0);
lean_dec(v_unused_971_);
v___x_964_ = v___x_958_;
v_isShared_965_ = v_isSharedCheck_970_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_diag_962_);
lean_inc(v_postponed_961_);
lean_inc(v_zetaDeltaFVarIds_960_);
lean_inc(v_cache_959_);
lean_dec(v___x_958_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_970_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v_mctx_957_);
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_mctx_957_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v_cache_959_);
lean_ctor_set(v_reuseFailAlloc_969_, 2, v_zetaDeltaFVarIds_960_);
lean_ctor_set(v_reuseFailAlloc_969_, 3, v_postponed_961_);
lean_ctor_set(v_reuseFailAlloc_969_, 4, v_diag_962_);
v___x_967_ = v_reuseFailAlloc_969_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
lean_object* v___x_968_; 
v___x_968_ = lean_st_ref_put(v___y_894_, v___x_967_);
v_a_926_ = v_fst_955_;
goto v___jp_925_;
}
}
}
v___jp_972_:
{
lean_object* v_fst_974_; lean_object* v_snd_975_; uint8_t v___x_976_; 
v_fst_974_ = lean_ctor_get(v___y_973_, 0);
lean_inc(v_fst_974_);
v_snd_975_ = lean_ctor_get(v___y_973_, 1);
lean_inc(v_snd_975_);
lean_dec_ref(v___y_973_);
v___x_976_ = lean_unbox(v_fst_974_);
lean_dec(v_fst_974_);
v_fst_955_ = v___x_976_;
v_snd_956_ = v_snd_975_;
goto v___jp_954_;
}
v___jp_977_:
{
lean_object* v___x_980_; lean_object* v_cache_981_; lean_object* v_zetaDeltaFVarIds_982_; lean_object* v_postponed_983_; lean_object* v_diag_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_992_; 
v___x_980_ = lean_st_ref_take(v___y_894_);
v_cache_981_ = lean_ctor_get(v___x_980_, 1);
v_zetaDeltaFVarIds_982_ = lean_ctor_get(v___x_980_, 2);
v_postponed_983_ = lean_ctor_get(v___x_980_, 3);
v_diag_984_ = lean_ctor_get(v___x_980_, 4);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_992_ == 0)
{
lean_object* v_unused_993_; 
v_unused_993_ = lean_ctor_get(v___x_980_, 0);
lean_dec(v_unused_993_);
v___x_986_ = v___x_980_;
v_isShared_987_ = v_isSharedCheck_992_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_diag_984_);
lean_inc(v_postponed_983_);
lean_inc(v_zetaDeltaFVarIds_982_);
lean_inc(v_cache_981_);
lean_dec(v___x_980_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_992_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 0, v_mctx_979_);
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_mctx_979_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v_cache_981_);
lean_ctor_set(v_reuseFailAlloc_991_, 2, v_zetaDeltaFVarIds_982_);
lean_ctor_set(v_reuseFailAlloc_991_, 3, v_postponed_983_);
lean_ctor_set(v_reuseFailAlloc_991_, 4, v_diag_984_);
v___x_989_ = v_reuseFailAlloc_991_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
lean_object* v___x_990_; 
v___x_990_ = lean_st_ref_put(v___y_894_, v___x_989_);
v_a_926_ = v_fst_978_;
goto v___jp_925_;
}
}
}
v___jp_994_:
{
lean_object* v_snd_996_; lean_object* v_fst_997_; lean_object* v_mctx_998_; uint8_t v___x_999_; 
v_snd_996_ = lean_ctor_get(v___y_995_, 1);
lean_inc(v_snd_996_);
v_fst_997_ = lean_ctor_get(v___y_995_, 0);
lean_inc(v_fst_997_);
lean_dec_ref(v___y_995_);
v_mctx_998_ = lean_ctor_get(v_snd_996_, 1);
lean_inc_ref(v_mctx_998_);
lean_dec(v_snd_996_);
v___x_999_ = lean_unbox(v_fst_997_);
lean_dec(v_fst_997_);
v_fst_978_ = v___x_999_;
v_mctx_979_ = v_mctx_998_;
goto v___jp_977_;
}
}
}
v___jp_905_:
{
lean_object* v___x_908_; 
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 1, v_a_906_);
lean_ctor_set(v___x_902_, 0, v___x_904_);
v___x_908_ = v___x_902_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_a_906_);
v___x_908_ = v_reuseFailAlloc_912_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
size_t v___x_909_; size_t v___x_910_; lean_object* v___x_911_; 
v___x_909_ = ((size_t)1ULL);
v___x_910_ = lean_usize_add(v_i_891_, v___x_909_);
v___x_911_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(v_forbidden_887_, v_ignoreLetDecls_888_, v_as_889_, v_sz_890_, v___x_910_, v___x_908_, v___y_894_);
return v___x_911_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2___boxed(lean_object* v_forbidden_1060_, lean_object* v_ignoreLetDecls_1061_, lean_object* v_as_1062_, lean_object* v_sz_1063_, lean_object* v_i_1064_, lean_object* v_b_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1071_; size_t v_sz_boxed_1072_; size_t v_i_boxed_1073_; lean_object* v_res_1074_; 
v_ignoreLetDecls_boxed_1071_ = lean_unbox(v_ignoreLetDecls_1061_);
v_sz_boxed_1072_ = lean_unbox_usize(v_sz_1063_);
lean_dec(v_sz_1063_);
v_i_boxed_1073_ = lean_unbox_usize(v_i_1064_);
lean_dec(v_i_1064_);
v_res_1074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2(v_forbidden_1060_, v_ignoreLetDecls_boxed_1071_, v_as_1062_, v_sz_boxed_1072_, v_i_boxed_1073_, v_b_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec_ref(v_as_1062_);
lean_dec(v_forbidden_1060_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(lean_object* v_init_1075_, lean_object* v_forbidden_1076_, uint8_t v_ignoreLetDecls_1077_, lean_object* v_n_1078_, lean_object* v_b_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
if (lean_obj_tag(v_n_1078_) == 0)
{
lean_object* v_cs_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; size_t v_sz_1088_; size_t v___x_1089_; lean_object* v___x_1090_; 
v_cs_1085_ = lean_ctor_get(v_n_1078_, 0);
v___x_1086_ = lean_box(0);
v___x_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
lean_ctor_set(v___x_1087_, 1, v_b_1079_);
v_sz_1088_ = lean_array_size(v_cs_1085_);
v___x_1089_ = ((size_t)0ULL);
v___x_1090_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(v_init_1075_, v_forbidden_1076_, v_ignoreLetDecls_1077_, v_cs_1085_, v_sz_1088_, v___x_1089_, v___x_1087_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1105_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1093_ = v___x_1090_;
v_isShared_1094_ = v_isSharedCheck_1105_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1090_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1105_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v_fst_1095_; 
v_fst_1095_ = lean_ctor_get(v_a_1091_, 0);
if (lean_obj_tag(v_fst_1095_) == 0)
{
lean_object* v_snd_1096_; lean_object* v___x_1097_; lean_object* v___x_1099_; 
v_snd_1096_ = lean_ctor_get(v_a_1091_, 1);
lean_inc(v_snd_1096_);
lean_dec(v_a_1091_);
v___x_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1097_, 0, v_snd_1096_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 0, v___x_1097_);
v___x_1099_ = v___x_1093_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
else
{
lean_object* v_val_1101_; lean_object* v___x_1103_; 
lean_inc_ref(v_fst_1095_);
lean_dec(v_a_1091_);
v_val_1101_ = lean_ctor_get(v_fst_1095_, 0);
lean_inc(v_val_1101_);
lean_dec_ref_known(v_fst_1095_, 1);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 0, v_val_1101_);
v___x_1103_ = v___x_1093_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_val_1101_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
v_a_1106_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1090_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1090_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
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
lean_object* v_vs_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; size_t v_sz_1117_; size_t v___x_1118_; lean_object* v___x_1119_; 
v_vs_1114_ = lean_ctor_get(v_n_1078_, 0);
v___x_1115_ = lean_box(0);
v___x_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
lean_ctor_set(v___x_1116_, 1, v_b_1079_);
v_sz_1117_ = lean_array_size(v_vs_1114_);
v___x_1118_ = ((size_t)0ULL);
v___x_1119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2(v_forbidden_1076_, v_ignoreLetDecls_1077_, v_vs_1114_, v_sz_1117_, v___x_1118_, v___x_1116_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1134_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1122_ = v___x_1119_;
v_isShared_1123_ = v_isSharedCheck_1134_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1119_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1134_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v_fst_1124_; 
v_fst_1124_ = lean_ctor_get(v_a_1120_, 0);
if (lean_obj_tag(v_fst_1124_) == 0)
{
lean_object* v_snd_1125_; lean_object* v___x_1126_; lean_object* v___x_1128_; 
v_snd_1125_ = lean_ctor_get(v_a_1120_, 1);
lean_inc(v_snd_1125_);
lean_dec(v_a_1120_);
v___x_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1126_, 0, v_snd_1125_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v___x_1126_);
v___x_1128_ = v___x_1122_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1126_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
else
{
lean_object* v_val_1130_; lean_object* v___x_1132_; 
lean_inc_ref(v_fst_1124_);
lean_dec(v_a_1120_);
v_val_1130_ = lean_ctor_get(v_fst_1124_, 0);
lean_inc(v_val_1130_);
lean_dec_ref_known(v_fst_1124_, 1);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v_val_1130_);
v___x_1132_ = v___x_1122_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_val_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
v_a_1135_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1119_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1119_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(lean_object* v_init_1143_, lean_object* v_forbidden_1144_, uint8_t v_ignoreLetDecls_1145_, lean_object* v_as_1146_, size_t v_sz_1147_, size_t v_i_1148_, lean_object* v_b_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
uint8_t v___x_1155_; 
v___x_1155_ = lean_usize_dec_lt(v_i_1148_, v_sz_1147_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; 
v___x_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1156_, 0, v_b_1149_);
return v___x_1156_;
}
else
{
lean_object* v_snd_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1191_; 
v_snd_1157_ = lean_ctor_get(v_b_1149_, 1);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_b_1149_);
if (v_isSharedCheck_1191_ == 0)
{
lean_object* v_unused_1192_; 
v_unused_1192_ = lean_ctor_get(v_b_1149_, 0);
lean_dec(v_unused_1192_);
v___x_1159_ = v_b_1149_;
v_isShared_1160_ = v_isSharedCheck_1191_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_snd_1157_);
lean_dec(v_b_1149_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1191_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v_a_1162_; lean_object* v___x_1163_; 
v___x_1161_ = lean_box(0);
v_a_1162_ = lean_array_uget_borrowed(v_as_1146_, v_i_1148_);
lean_inc(v_snd_1157_);
v___x_1163_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(v_init_1143_, v_forbidden_1144_, v_ignoreLetDecls_1145_, v_a_1162_, v_snd_1157_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1182_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1166_ = v___x_1163_;
v_isShared_1167_ = v_isSharedCheck_1182_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1163_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1182_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
if (lean_obj_tag(v_a_1164_) == 0)
{
lean_object* v___x_1168_; lean_object* v___x_1170_; 
v___x_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1168_, 0, v_a_1164_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1168_);
v___x_1170_ = v___x_1159_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v_snd_1157_);
v___x_1170_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
lean_object* v___x_1172_; 
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 0, v___x_1170_);
v___x_1172_ = v___x_1166_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1170_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; 
lean_del_object(v___x_1166_);
lean_dec(v_snd_1157_);
v_a_1175_ = lean_ctor_get(v_a_1164_, 0);
lean_inc(v_a_1175_);
lean_dec_ref_known(v_a_1164_, 1);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 1, v_a_1175_);
lean_ctor_set(v___x_1159_, 0, v___x_1161_);
v___x_1177_ = v___x_1159_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_a_1175_);
v___x_1177_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
size_t v___x_1178_; size_t v___x_1179_; 
v___x_1178_ = ((size_t)1ULL);
v___x_1179_ = lean_usize_add(v_i_1148_, v___x_1178_);
v_i_1148_ = v___x_1179_;
v_b_1149_ = v___x_1177_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
lean_del_object(v___x_1159_);
lean_dec(v_snd_1157_);
v_a_1183_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1163_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1163_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1___boxed(lean_object* v_init_1193_, lean_object* v_forbidden_1194_, lean_object* v_ignoreLetDecls_1195_, lean_object* v_as_1196_, lean_object* v_sz_1197_, lean_object* v_i_1198_, lean_object* v_b_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1205_; size_t v_sz_boxed_1206_; size_t v_i_boxed_1207_; lean_object* v_res_1208_; 
v_ignoreLetDecls_boxed_1205_ = lean_unbox(v_ignoreLetDecls_1195_);
v_sz_boxed_1206_ = lean_unbox_usize(v_sz_1197_);
lean_dec(v_sz_1197_);
v_i_boxed_1207_ = lean_unbox_usize(v_i_1198_);
lean_dec(v_i_1198_);
v_res_1208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(v_init_1193_, v_forbidden_1194_, v_ignoreLetDecls_boxed_1205_, v_as_1196_, v_sz_boxed_1206_, v_i_boxed_1207_, v_b_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec_ref(v_as_1196_);
lean_dec(v_forbidden_1194_);
lean_dec_ref(v_init_1193_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0___boxed(lean_object* v_init_1209_, lean_object* v_forbidden_1210_, lean_object* v_ignoreLetDecls_1211_, lean_object* v_n_1212_, lean_object* v_b_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1219_; lean_object* v_res_1220_; 
v_ignoreLetDecls_boxed_1219_ = lean_unbox(v_ignoreLetDecls_1211_);
v_res_1220_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(v_init_1209_, v_forbidden_1210_, v_ignoreLetDecls_boxed_1219_, v_n_1212_, v_b_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec_ref(v_n_1212_);
lean_dec(v_forbidden_1210_);
lean_dec_ref(v_init_1209_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0(lean_object* v_forbidden_1221_, uint8_t v_ignoreLetDecls_1222_, lean_object* v_t_1223_, lean_object* v_init_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v_root_1230_; lean_object* v_tail_1231_; lean_object* v___x_1232_; 
v_root_1230_ = lean_ctor_get(v_t_1223_, 0);
v_tail_1231_ = lean_ctor_get(v_t_1223_, 1);
lean_inc_ref(v_init_1224_);
v___x_1232_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(v_init_1224_, v_forbidden_1221_, v_ignoreLetDecls_1222_, v_root_1230_, v_init_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
lean_dec_ref(v_init_1224_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1269_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1235_ = v___x_1232_;
v_isShared_1236_ = v_isSharedCheck_1269_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1232_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1269_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
if (lean_obj_tag(v_a_1233_) == 0)
{
lean_object* v_a_1237_; lean_object* v___x_1239_; 
v_a_1237_ = lean_ctor_get(v_a_1233_, 0);
lean_inc(v_a_1237_);
lean_dec_ref_known(v_a_1233_, 1);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v_a_1237_);
v___x_1239_ = v___x_1235_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1237_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; size_t v_sz_1244_; size_t v___x_1245_; lean_object* v___x_1246_; 
lean_del_object(v___x_1235_);
v_a_1241_ = lean_ctor_get(v_a_1233_, 0);
lean_inc(v_a_1241_);
lean_dec_ref_known(v_a_1233_, 1);
v___x_1242_ = lean_box(0);
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
lean_ctor_set(v___x_1243_, 1, v_a_1241_);
v_sz_1244_ = lean_array_size(v_tail_1231_);
v___x_1245_ = ((size_t)0ULL);
v___x_1246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1(v_forbidden_1221_, v_ignoreLetDecls_1222_, v_tail_1231_, v_sz_1244_, v___x_1245_, v___x_1243_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1260_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1249_ = v___x_1246_;
v_isShared_1250_ = v_isSharedCheck_1260_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1246_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1260_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v_fst_1251_; 
v_fst_1251_ = lean_ctor_get(v_a_1247_, 0);
if (lean_obj_tag(v_fst_1251_) == 0)
{
lean_object* v_snd_1252_; lean_object* v___x_1254_; 
v_snd_1252_ = lean_ctor_get(v_a_1247_, 1);
lean_inc(v_snd_1252_);
lean_dec(v_a_1247_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v_snd_1252_);
v___x_1254_ = v___x_1249_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_snd_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
else
{
lean_object* v_val_1256_; lean_object* v___x_1258_; 
lean_inc_ref(v_fst_1251_);
lean_dec(v_a_1247_);
v_val_1256_ = lean_ctor_get(v_fst_1251_, 0);
lean_inc(v_val_1256_);
lean_dec_ref_known(v_fst_1251_, 1);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v_val_1256_);
v___x_1258_ = v___x_1249_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_val_1256_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
v_a_1261_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1246_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1246_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1261_);
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
}
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
v_a_1270_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1232_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1232_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0___boxed(lean_object* v_forbidden_1278_, lean_object* v_ignoreLetDecls_1279_, lean_object* v_t_1280_, lean_object* v_init_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1287_; lean_object* v_res_1288_; 
v_ignoreLetDecls_boxed_1287_ = lean_unbox(v_ignoreLetDecls_1279_);
v_res_1288_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0(v_forbidden_1278_, v_ignoreLetDecls_boxed_1287_, v_t_1280_, v_init_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec_ref(v_t_1280_);
lean_dec(v_forbidden_1278_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(lean_object* v_as_1289_, size_t v_i_1290_, size_t v_stop_1291_, lean_object* v_b_1292_){
_start:
{
lean_object* v___y_1294_; uint8_t v___x_1298_; 
v___x_1298_ = lean_usize_dec_eq(v_i_1290_, v_stop_1291_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; uint8_t v___x_1300_; 
v___x_1299_ = lean_array_uget_borrowed(v_as_1289_, v_i_1290_);
v___x_1300_ = l_Lean_Expr_isFVar(v___x_1299_);
if (v___x_1300_ == 0)
{
v___y_1294_ = v_b_1292_;
goto v___jp_1293_;
}
else
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = l_Lean_Expr_fvarId_x21(v___x_1299_);
v___x_1302_ = l_Lean_FVarIdSet_insert(v_b_1292_, v___x_1301_);
v___y_1294_ = v___x_1302_;
goto v___jp_1293_;
}
}
else
{
return v_b_1292_;
}
v___jp_1293_:
{
size_t v___x_1295_; size_t v___x_1296_; 
v___x_1295_ = ((size_t)1ULL);
v___x_1296_ = lean_usize_add(v_i_1290_, v___x_1295_);
v_i_1290_ = v___x_1296_;
v_b_1292_ = v___y_1294_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1___boxed(lean_object* v_as_1303_, lean_object* v_i_1304_, lean_object* v_stop_1305_, lean_object* v_b_1306_){
_start:
{
size_t v_i_boxed_1307_; size_t v_stop_boxed_1308_; lean_object* v_res_1309_; 
v_i_boxed_1307_ = lean_unbox_usize(v_i_1304_);
lean_dec(v_i_1304_);
v_stop_boxed_1308_ = lean_unbox_usize(v_stop_1305_);
lean_dec(v_stop_1305_);
v_res_1309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(v_as_1303_, v_i_boxed_1307_, v_stop_boxed_1308_, v_b_1306_);
lean_dec_ref(v_as_1303_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize(lean_object* v_targets_1310_, lean_object* v_forbidden_1311_, uint8_t v_ignoreLetDecls_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v_r_1318_; lean_object* v___y_1320_; lean_object* v___x_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; 
v_r_1318_ = lean_box(1);
v___x_1342_ = lean_unsigned_to_nat(0u);
v___x_1343_ = lean_array_get_size(v_targets_1310_);
v___x_1344_ = lean_nat_dec_lt(v___x_1342_, v___x_1343_);
if (v___x_1344_ == 0)
{
v___y_1320_ = v_r_1318_;
goto v___jp_1319_;
}
else
{
size_t v___x_1345_; size_t v___x_1346_; lean_object* v___x_1347_; 
v___x_1345_ = ((size_t)0ULL);
v___x_1346_ = lean_usize_of_nat(v___x_1343_);
v___x_1347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(v_targets_1310_, v___x_1345_, v___x_1346_, v_r_1318_);
v___y_1320_ = v___x_1347_;
goto v___jp_1319_;
}
v___jp_1319_:
{
lean_object* v_lctx_1321_; lean_object* v_decls_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v_lctx_1321_ = lean_ctor_get(v_a_1313_, 2);
v_decls_1322_ = lean_ctor_get(v_lctx_1321_, 1);
v___x_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___y_1320_);
lean_ctor_set(v___x_1323_, 1, v_r_1318_);
v___x_1324_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0(v_forbidden_1311_, v_ignoreLetDecls_1312_, v_decls_1322_, v___x_1323_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1333_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1327_ = v___x_1324_;
v_isShared_1328_ = v_isSharedCheck_1333_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1324_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1333_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v_snd_1329_; lean_object* v___x_1331_; 
v_snd_1329_ = lean_ctor_get(v_a_1325_, 1);
lean_inc(v_snd_1329_);
lean_dec(v_a_1325_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v_snd_1329_);
v___x_1331_ = v___x_1327_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_snd_1329_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
else
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
v_a_1334_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v___x_1324_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1324_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize___boxed(lean_object* v_targets_1348_, lean_object* v_forbidden_1349_, lean_object* v_ignoreLetDecls_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1356_; lean_object* v_res_1357_; 
v_ignoreLetDecls_boxed_1356_ = lean_unbox(v_ignoreLetDecls_1350_);
v_res_1357_ = l_Lean_Meta_getFVarSetToGeneralize(v_targets_1348_, v_forbidden_1349_, v_ignoreLetDecls_boxed_1356_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
lean_dec(v_a_1354_);
lean_dec_ref(v_a_1353_);
lean_dec(v_a_1352_);
lean_dec_ref(v_a_1351_);
lean_dec(v_forbidden_1349_);
lean_dec_ref(v_targets_1348_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4(lean_object* v_forbidden_1358_, uint8_t v_ignoreLetDecls_1359_, lean_object* v_as_1360_, size_t v_sz_1361_, size_t v_i_1362_, lean_object* v_b_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(v_forbidden_1358_, v_ignoreLetDecls_1359_, v_as_1360_, v_sz_1361_, v_i_1362_, v_b_1363_, v___y_1365_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___boxed(lean_object* v_forbidden_1370_, lean_object* v_ignoreLetDecls_1371_, lean_object* v_as_1372_, lean_object* v_sz_1373_, lean_object* v_i_1374_, lean_object* v_b_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1381_; size_t v_sz_boxed_1382_; size_t v_i_boxed_1383_; lean_object* v_res_1384_; 
v_ignoreLetDecls_boxed_1381_ = lean_unbox(v_ignoreLetDecls_1371_);
v_sz_boxed_1382_ = lean_unbox_usize(v_sz_1373_);
lean_dec(v_sz_1373_);
v_i_boxed_1383_ = lean_unbox_usize(v_i_1374_);
lean_dec(v_i_1374_);
v_res_1384_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4(v_forbidden_1370_, v_ignoreLetDecls_boxed_1381_, v_as_1372_, v_sz_boxed_1382_, v_i_boxed_1383_, v_b_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec_ref(v_as_1372_);
lean_dec(v_forbidden_1370_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4(lean_object* v_forbidden_1385_, uint8_t v_ignoreLetDecls_1386_, lean_object* v_as_1387_, size_t v_sz_1388_, size_t v_i_1389_, lean_object* v_b_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(v_forbidden_1385_, v_ignoreLetDecls_1386_, v_as_1387_, v_sz_1388_, v_i_1389_, v_b_1390_, v___y_1392_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_forbidden_1397_, lean_object* v_ignoreLetDecls_1398_, lean_object* v_as_1399_, lean_object* v_sz_1400_, lean_object* v_i_1401_, lean_object* v_b_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1408_; size_t v_sz_boxed_1409_; size_t v_i_boxed_1410_; lean_object* v_res_1411_; 
v_ignoreLetDecls_boxed_1408_ = lean_unbox(v_ignoreLetDecls_1398_);
v_sz_boxed_1409_ = lean_unbox_usize(v_sz_1400_);
lean_dec(v_sz_1400_);
v_i_boxed_1410_ = lean_unbox_usize(v_i_1401_);
lean_dec(v_i_1401_);
v_res_1411_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4(v_forbidden_1397_, v_ignoreLetDecls_boxed_1408_, v_as_1399_, v_sz_boxed_1409_, v_i_boxed_1410_, v_b_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec_ref(v_as_1399_);
lean_dec(v_forbidden_1397_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(lean_object* v_init_1412_, lean_object* v_x_1413_){
_start:
{
if (lean_obj_tag(v_x_1413_) == 0)
{
lean_object* v_k_1414_; lean_object* v_l_1415_; lean_object* v_r_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v_k_1414_ = lean_ctor_get(v_x_1413_, 1);
lean_inc(v_k_1414_);
v_l_1415_ = lean_ctor_get(v_x_1413_, 3);
lean_inc(v_l_1415_);
v_r_1416_ = lean_ctor_get(v_x_1413_, 4);
lean_inc(v_r_1416_);
lean_dec_ref_known(v_x_1413_, 5);
v___x_1417_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(v_init_1412_, v_l_1415_);
v___x_1418_ = lean_array_push(v___x_1417_, v_k_1414_);
v_init_1412_ = v___x_1418_;
v_x_1413_ = v_r_1416_;
goto _start;
}
else
{
return v_init_1412_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize(lean_object* v_targets_1420_, lean_object* v_forbidden_1421_, uint8_t v_ignoreLetDecls_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Lean_Meta_mkGeneralizationForbiddenSet(v_targets_1420_, v_forbidden_1421_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___x_1430_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_a_1429_);
lean_dec_ref_known(v___x_1428_, 1);
v___x_1430_ = l_Lean_Meta_getFVarSetToGeneralize(v_targets_1420_, v_a_1429_, v_ignoreLetDecls_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_);
lean_dec(v_a_1429_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v___y_1433_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1430_, 1);
if (lean_obj_tag(v_a_1431_) == 0)
{
lean_object* v_size_1437_; 
v_size_1437_ = lean_ctor_get(v_a_1431_, 0);
lean_inc(v_size_1437_);
v___y_1433_ = v_size_1437_;
goto v___jp_1432_;
}
else
{
lean_object* v___x_1438_; 
v___x_1438_ = lean_unsigned_to_nat(0u);
v___y_1433_ = v___x_1438_;
goto v___jp_1432_;
}
v___jp_1432_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1434_ = lean_mk_empty_array_with_capacity(v___y_1433_);
lean_dec(v___y_1433_);
v___x_1435_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(v___x_1434_, v_a_1431_);
v___x_1436_ = l_Lean_Meta_sortFVarIds___redArg(v___x_1435_, v_a_1423_);
return v___x_1436_;
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
v_a_1439_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1430_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1430_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
v_a_1447_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1428_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1428_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize___boxed(lean_object* v_targets_1455_, lean_object* v_forbidden_1456_, lean_object* v_ignoreLetDecls_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1463_; lean_object* v_res_1464_; 
v_ignoreLetDecls_boxed_1463_ = lean_unbox(v_ignoreLetDecls_1457_);
v_res_1464_ = l_Lean_Meta_getFVarsToGeneralize(v_targets_1455_, v_forbidden_1456_, v_ignoreLetDecls_boxed_1463_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_);
lean_dec(v_a_1461_);
lean_dec_ref(v_a_1460_);
lean_dec(v_a_1459_);
lean_dec_ref(v_a_1458_);
lean_dec_ref(v_targets_1455_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0(lean_object* v_init_1465_, lean_object* v_t_1466_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(v_init_1465_, v_t_1466_);
return v___x_1467_;
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
