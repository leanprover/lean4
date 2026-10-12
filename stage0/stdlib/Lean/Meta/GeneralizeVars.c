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
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
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
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v_res_26_;
v_res_26_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(v_e_1_, v___y_2_);
stack->m_obj
 = v_res_26_;
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
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(v_e_31_, v___y_33_);
return v___x_37_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_31_ = stack[0].m_obj;
lean_object* v___y_32_ = stack[1].m_obj;
lean_object* v___y_33_ = stack[2].m_obj;
lean_object* v___y_34_ = stack[3].m_obj;
lean_object* v___y_35_ = stack[4].m_obj;
lean_object* v_res_38_;
v_res_38_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2(v_e_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_);
stack->m_obj
 = v_res_38_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___boxed(lean_object* v_e_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2(v_e_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
return v_res_45_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(lean_object* v_k_46_, lean_object* v_t_47_){
_start:
{
if (lean_obj_tag(v_t_47_) == 0)
{
lean_object* v_k_48_; lean_object* v_l_49_; lean_object* v_r_50_; uint8_t v___x_51_; 
v_k_48_ = lean_ctor_get(v_t_47_, 1);
v_l_49_ = lean_ctor_get(v_t_47_, 3);
v_r_50_ = lean_ctor_get(v_t_47_, 4);
v___x_51_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_46_, v_k_48_);
switch(v___x_51_)
{
case 0:
{
v_t_47_ = v_l_49_;
goto _start;
}
case 1:
{
uint8_t v___x_53_; 
v___x_53_ = 1;
return v___x_53_;
}
default: 
{
v_t_47_ = v_r_50_;
goto _start;
}
}
}
else
{
uint8_t v___x_55_; 
v___x_55_ = 0;
return v___x_55_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_46_ = stack[0].m_obj;
lean_object* v_t_47_ = stack[1].m_obj;
uint8_t v_res_56_;
v_res_56_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v_k_46_, v_t_47_);
stack->m_num = v_res_56_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg___boxed(lean_object* v_k_57_, lean_object* v_t_58_){
_start:
{
uint8_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v_k_57_, v_t_58_);
lean_dec(v_t_58_);
lean_dec(v_k_57_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(lean_object* v_init_61_, lean_object* v_x_62_){
_start:
{
if (lean_obj_tag(v_x_62_) == 0)
{
lean_object* v_k_64_; lean_object* v_l_65_; lean_object* v_r_66_; lean_object* v___x_67_; lean_object* v_a_68_; lean_object* v_a_69_; lean_object* v_fst_70_; lean_object* v_snd_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_86_; 
v_k_64_ = lean_ctor_get(v_x_62_, 1);
lean_inc(v_k_64_);
v_l_65_ = lean_ctor_get(v_x_62_, 3);
lean_inc(v_l_65_);
v_r_66_ = lean_ctor_get(v_x_62_, 4);
lean_inc(v_r_66_);
lean_dec_ref_known(v_x_62_, 5);
v___x_67_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(v_init_61_, v_l_65_);
v_a_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc(v_a_68_);
lean_dec_ref(v___x_67_);
v_a_69_ = lean_ctor_get(v_a_68_, 0);
lean_inc(v_a_69_);
lean_dec(v_a_68_);
v_fst_70_ = lean_ctor_get(v_a_69_, 0);
v_snd_71_ = lean_ctor_get(v_a_69_, 1);
v_isSharedCheck_86_ = !lean_is_exclusive(v_a_69_);
if (v_isSharedCheck_86_ == 0)
{
v___x_73_ = v_a_69_;
v_isShared_74_ = v_isSharedCheck_86_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_snd_71_);
lean_inc(v_fst_70_);
lean_dec(v_a_69_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_86_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
uint8_t v___x_75_; 
v___x_75_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v_k_64_, v_snd_71_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_79_; 
lean_inc(v_k_64_);
v___x_76_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_76_, 0, v_k_64_);
lean_ctor_set(v___x_76_, 1, v_fst_70_);
v___x_77_ = l_Lean_FVarIdSet_insert(v_snd_71_, v_k_64_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 1, v___x_77_);
lean_ctor_set(v___x_73_, 0, v___x_76_);
v___x_79_ = v___x_73_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_76_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v___x_77_);
v___x_79_ = v_reuseFailAlloc_81_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
v_init_61_ = v___x_79_;
v_x_62_ = v_r_66_;
goto _start;
}
}
else
{
lean_object* v___x_83_; 
lean_dec(v_k_64_);
if (v_isShared_74_ == 0)
{
v___x_83_ = v___x_73_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_fst_70_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v_snd_71_);
v___x_83_ = v_reuseFailAlloc_85_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
v_init_61_ = v___x_83_;
v_x_62_ = v_r_66_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_87_, 0, v_init_61_);
v___x_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
return v___x_88_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_61_ = stack[0].m_obj;
lean_object* v_x_62_ = stack[1].m_obj;
lean_object* v_res_89_;
v_res_89_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(v_init_61_, v_x_62_);
stack->m_obj
 = v_res_89_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg___boxed(lean_object* v_init_90_, lean_object* v_x_91_, lean_object* v___y_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(v_init_90_, v_x_91_);
return v_res_93_;
}
}
static lean_object* _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = lean_box(0);
v___x_95_ = lean_unsigned_to_nat(16u);
v___x_96_ = lean_mk_array(v___x_95_, v___x_94_);
return v___x_96_;
}
}
static lean_object* _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0);
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v___x_97_);
return v___x_99_;
}
}
static lean_object* _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_102_ = ((lean_object*)(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2));
v___x_103_ = lean_box(1);
v___x_104_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_105_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set(v___x_105_, 1, v___x_103_);
lean_ctor_set(v___x_105_, 2, v___x_102_);
return v___x_105_;
}
}
lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit(lean_object* v_fvarId_106_, lean_object* v_todo_107_, lean_object* v_s_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v_a_115_; lean_object* v_s_x27_127_; lean_object* v___y_128_; lean_object* v___y_129_; lean_object* v___y_130_; lean_object* v___y_131_; lean_object* v___x_137_; 
v___x_137_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_106_, v_a_109_, v_a_111_, v_a_112_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_a_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v_a_141_; lean_object* v___x_142_; lean_object* v___x_143_; uint8_t v___x_144_; lean_object* v___x_145_; 
v_a_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_a_138_);
lean_dec_ref_known(v___x_137_, 1);
v___x_139_ = l_Lean_LocalDecl_type(v_a_138_);
v___x_140_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(v___x_139_, v_a_110_);
v_a_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc(v_a_141_);
lean_dec_ref(v___x_140_);
v___x_142_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3);
v___x_143_ = l_Lean_collectFVars(v___x_142_, v_a_141_);
v___x_144_ = 0;
v___x_145_ = l_Lean_LocalDecl_value_x3f(v_a_138_, v___x_144_);
lean_dec(v_a_138_);
if (lean_obj_tag(v___x_145_) == 1)
{
lean_object* v_val_146_; lean_object* v___x_147_; lean_object* v_a_148_; lean_object* v___x_149_; 
v_val_146_ = lean_ctor_get(v___x_145_, 0);
lean_inc(v_val_146_);
lean_dec_ref_known(v___x_145_, 1);
v___x_147_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(v_val_146_, v_a_110_);
v_a_148_ = lean_ctor_get(v___x_147_, 0);
lean_inc(v_a_148_);
lean_dec_ref(v___x_147_);
v___x_149_ = l_Lean_collectFVars(v___x_143_, v_a_148_);
v_s_x27_127_ = v___x_149_;
v___y_128_ = v_a_109_;
v___y_129_ = v_a_110_;
v___y_130_ = v_a_111_;
v___y_131_ = v_a_112_;
goto v___jp_126_;
}
else
{
lean_dec(v___x_145_);
v_s_x27_127_ = v___x_143_;
v___y_128_ = v_a_109_;
v___y_129_ = v_a_110_;
v___y_130_ = v_a_111_;
v___y_131_ = v_a_112_;
goto v___jp_126_;
}
}
else
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_157_; 
lean_dec(v_s_108_);
lean_dec(v_todo_107_);
v_a_150_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_157_ == 0)
{
v___x_152_ = v___x_137_;
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_137_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_153_ == 0)
{
v___x_155_ = v___x_152_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_a_150_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
v___jp_114_:
{
lean_object* v_fst_116_; lean_object* v_snd_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_125_; 
v_fst_116_ = lean_ctor_get(v_a_115_, 0);
v_snd_117_ = lean_ctor_get(v_a_115_, 1);
v_isSharedCheck_125_ = !lean_is_exclusive(v_a_115_);
if (v_isSharedCheck_125_ == 0)
{
v___x_119_ = v_a_115_;
v_isShared_120_ = v_isSharedCheck_125_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_snd_117_);
lean_inc(v_fst_116_);
lean_dec(v_a_115_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_125_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_122_; 
if (v_isShared_120_ == 0)
{
v___x_122_ = v___x_119_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_fst_116_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v_snd_117_);
v___x_122_ = v_reuseFailAlloc_124_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
lean_object* v___x_123_; 
v___x_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
return v___x_123_;
}
}
}
v___jp_126_:
{
lean_object* v_fvarSet_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v_a_135_; lean_object* v_a_136_; 
v_fvarSet_132_ = lean_ctor_get(v_s_x27_127_, 1);
lean_inc(v_fvarSet_132_);
lean_dec_ref(v_s_x27_127_);
v___x_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_133_, 0, v_todo_107_);
lean_ctor_set(v___x_133_, 1, v_s_108_);
v___x_134_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(v___x_133_, v_fvarSet_132_);
v_a_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc(v_a_135_);
lean_dec_ref(v___x_134_);
v_a_136_ = lean_ctor_get(v_a_135_, 0);
lean_inc(v_a_136_);
lean_dec(v_a_135_);
v_a_115_ = v_a_136_;
goto v___jp_114_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_106_ = stack[0].m_obj;
lean_object* v_todo_107_ = stack[1].m_obj;
lean_object* v_s_108_ = stack[2].m_obj;
lean_object* v_a_109_ = stack[3].m_obj;
lean_object* v_a_110_ = stack[4].m_obj;
lean_object* v_a_111_ = stack[5].m_obj;
lean_object* v_a_112_ = stack[6].m_obj;
lean_object* v_res_158_;
v_res_158_ = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit(v_fvarId_106_, v_todo_107_, v_s_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
stack->m_obj
 = v_res_158_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___boxed(lean_object* v_fvarId_159_, lean_object* v_todo_160_, lean_object* v_s_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit(v_fvarId_159_, v_todo_160_, v_s_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
lean_dec(v_a_163_);
lean_dec_ref(v_a_162_);
return v_res_167_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0(lean_object* v_00_u03b2_168_, lean_object* v_k_169_, lean_object* v_t_170_){
_start:
{
uint8_t v___x_171_; 
v___x_171_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v_k_169_, v_t_170_);
return v___x_171_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_169_ = stack[1].m_obj;
lean_object* v_t_170_ = stack[2].m_obj;
uint8_t v_res_172_;
v_res_172_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0(lean_box(0), v_k_169_, v_t_170_);
stack->m_num = v_res_172_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___boxed(lean_object* v_00_u03b2_173_, lean_object* v_k_174_, lean_object* v_t_175_){
_start:
{
uint8_t v_res_176_; lean_object* v_r_177_; 
v_res_176_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0(v_00_u03b2_173_, v_k_174_, v_t_175_);
lean_dec(v_t_175_);
lean_dec(v_k_174_);
v_r_177_ = lean_box(v_res_176_);
return v_r_177_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1(lean_object* v_init_178_, lean_object* v_x_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(v_init_178_, v_x_179_);
return v___x_185_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_178_ = stack[0].m_obj;
lean_object* v_x_179_ = stack[1].m_obj;
lean_object* v___y_180_ = stack[2].m_obj;
lean_object* v___y_181_ = stack[3].m_obj;
lean_object* v___y_182_ = stack[4].m_obj;
lean_object* v___y_183_ = stack[5].m_obj;
lean_object* v_res_186_;
v_res_186_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1(v_init_178_, v_x_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_);
stack->m_obj
 = v_res_186_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___boxed(lean_object* v_init_187_, lean_object* v_x_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1(v_init_187_, v_x_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
return v_res_194_;
}
}
lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop(lean_object* v_todo_195_, lean_object* v_s_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
if (lean_obj_tag(v_todo_195_) == 0)
{
lean_object* v___x_202_; 
v___x_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_202_, 0, v_s_196_);
return v___x_202_;
}
else
{
lean_object* v_head_203_; lean_object* v_tail_204_; uint8_t v___x_205_; 
v_head_203_ = lean_ctor_get(v_todo_195_, 0);
lean_inc(v_head_203_);
v_tail_204_ = lean_ctor_get(v_todo_195_, 1);
lean_inc(v_tail_204_);
lean_dec_ref_known(v_todo_195_, 2);
v___x_205_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v_head_203_, v_s_196_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; lean_object* v___x_207_; 
lean_inc(v_head_203_);
v___x_206_ = l_Lean_FVarIdSet_insert(v_s_196_, v_head_203_);
v___x_207_ = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit(v_head_203_, v_tail_204_, v___x_206_, v_a_197_, v_a_198_, v_a_199_, v_a_200_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; lean_object* v_fst_209_; lean_object* v_snd_210_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_a_208_);
lean_dec_ref_known(v___x_207_, 1);
v_fst_209_ = lean_ctor_get(v_a_208_, 0);
lean_inc(v_fst_209_);
v_snd_210_ = lean_ctor_get(v_a_208_, 1);
lean_inc(v_snd_210_);
lean_dec(v_a_208_);
v_todo_195_ = v_fst_209_;
v_s_196_ = v_snd_210_;
goto _start;
}
else
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_219_; 
v_a_212_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_219_ == 0)
{
v___x_214_ = v___x_207_;
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_207_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_217_; 
if (v_isShared_215_ == 0)
{
v___x_217_ = v___x_214_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_a_212_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
else
{
lean_dec(v_head_203_);
v_todo_195_ = v_tail_204_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_todo_195_ = stack[0].m_obj;
lean_object* v_s_196_ = stack[1].m_obj;
lean_object* v_a_197_ = stack[2].m_obj;
lean_object* v_a_198_ = stack[3].m_obj;
lean_object* v_a_199_ = stack[4].m_obj;
lean_object* v_a_200_ = stack[5].m_obj;
lean_object* v_res_221_;
v_res_221_ = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop(v_todo_195_, v_s_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_);
stack->m_obj
 = v_res_221_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop___boxed(lean_object* v_todo_222_, lean_object* v_s_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop(v_todo_222_, v_s_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
return v_res_229_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0(lean_object* v_as_230_, size_t v_sz_231_, size_t v_i_232_, lean_object* v_b_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v_a_240_; uint8_t v___x_244_; 
v___x_244_ = lean_usize_dec_lt(v_i_232_, v_sz_231_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; 
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v_b_233_);
return v___x_245_;
}
else
{
lean_object* v_fst_246_; lean_object* v_snd_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_282_; 
v_fst_246_ = lean_ctor_get(v_b_233_, 0);
v_snd_247_ = lean_ctor_get(v_b_233_, 1);
v_isSharedCheck_282_ = !lean_is_exclusive(v_b_233_);
if (v_isSharedCheck_282_ == 0)
{
v___x_249_ = v_b_233_;
v_isShared_250_ = v_isSharedCheck_282_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_snd_247_);
lean_inc(v_fst_246_);
lean_dec(v_b_233_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_282_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v_a_251_; uint8_t v___x_252_; 
v_a_251_ = lean_array_uget_borrowed(v_as_230_, v_i_232_);
v___x_252_ = l_Lean_Expr_isFVar(v_a_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
lean_inc(v___y_237_);
lean_inc_ref(v___y_236_);
lean_inc(v___y_235_);
lean_inc_ref(v___y_234_);
lean_inc(v_a_251_);
v___x_253_ = lean_infer_type(v_a_251_, v___y_234_, v___y_235_, v___y_236_, v___y_237_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; lean_object* v___x_255_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc(v_a_254_);
lean_dec_ref_known(v___x_253_, 1);
v___x_255_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(v_a_254_, v___y_235_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_a_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_a_256_);
lean_dec_ref_known(v___x_255_, 1);
v___x_257_ = l_Lean_collectFVars(v_fst_246_, v_a_256_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 0, v___x_257_);
v___x_259_ = v___x_249_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_257_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_snd_247_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
v_a_240_ = v___x_259_;
goto v___jp_239_;
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
lean_del_object(v___x_249_);
lean_dec(v_snd_247_);
lean_dec(v_fst_246_);
v_a_261_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_255_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_255_);
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
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_del_object(v___x_249_);
lean_dec(v_snd_247_);
lean_dec(v_fst_246_);
v_a_269_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_253_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_253_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
else
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_280_; 
v___x_277_ = l_Lean_Expr_fvarId_x21(v_a_251_);
v___x_278_ = lean_array_push(v_snd_247_, v___x_277_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 1, v___x_278_);
v___x_280_ = v___x_249_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_fst_246_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v___x_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
v_a_240_ = v___x_280_;
goto v___jp_239_;
}
}
}
}
v___jp_239_:
{
size_t v___x_241_; size_t v___x_242_; 
v___x_241_ = ((size_t)1ULL);
v___x_242_ = lean_usize_add(v_i_232_, v___x_241_);
v_i_232_ = v___x_242_;
v_b_233_ = v_a_240_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_230_ = stack[0].m_obj;
size_t v_sz_231_ = stack[1].m_num;
size_t v_i_232_ = stack[2].m_num;
lean_object* v_b_233_ = stack[3].m_obj;
lean_object* v___y_234_ = stack[4].m_obj;
lean_object* v___y_235_ = stack[5].m_obj;
lean_object* v___y_236_ = stack[6].m_obj;
lean_object* v___y_237_ = stack[7].m_obj;
lean_object* v_res_283_;
v_res_283_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0(v_as_230_, v_sz_231_, v_i_232_, v_b_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_);
stack->m_obj
 = v_res_283_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0___boxed(lean_object* v_as_284_, lean_object* v_sz_285_, lean_object* v_i_286_, lean_object* v_b_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
size_t v_sz_boxed_293_; size_t v_i_boxed_294_; lean_object* v_res_295_; 
v_sz_boxed_293_ = lean_unbox_usize(v_sz_285_);
lean_dec(v_sz_285_);
v_i_boxed_294_ = lean_unbox_usize(v_i_286_);
lean_dec(v_i_286_);
v_res_295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0(v_as_284_, v_sz_boxed_293_, v_i_boxed_294_, v_b_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec_ref(v_as_284_);
return v_res_295_;
}
}
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet(lean_object* v_targets_296_, lean_object* v_forbidden_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v___x_303_; lean_object* v_todo_304_; lean_object* v_s_305_; lean_object* v___x_306_; size_t v_sz_307_; size_t v___x_308_; lean_object* v___x_309_; 
v___x_303_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v_todo_304_ = ((lean_object*)(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2));
v_s_305_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_s_305_, 0, v___x_303_);
lean_ctor_set(v_s_305_, 1, v_forbidden_297_);
lean_ctor_set(v_s_305_, 2, v_todo_304_);
v___x_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_306_, 0, v_s_305_);
lean_ctor_set(v___x_306_, 1, v_todo_304_);
v_sz_307_ = lean_array_size(v_targets_296_);
v___x_308_ = ((size_t)0ULL);
v___x_309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0(v_targets_296_, v_sz_307_, v___x_308_, v___x_306_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; lean_object* v_fst_311_; lean_object* v_snd_312_; lean_object* v_fvarSet_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_a_310_);
lean_dec_ref_known(v___x_309_, 1);
v_fst_311_ = lean_ctor_get(v_a_310_, 0);
lean_inc(v_fst_311_);
v_snd_312_ = lean_ctor_get(v_a_310_, 1);
lean_inc(v_snd_312_);
lean_dec(v_a_310_);
v_fvarSet_313_ = lean_ctor_get(v_fst_311_, 1);
lean_inc(v_fvarSet_313_);
lean_dec(v_fst_311_);
v___x_314_ = lean_array_to_list(v_snd_312_);
v___x_315_ = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop(v___x_314_, v_fvarSet_313_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
return v___x_315_;
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
v_a_316_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_309_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_309_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkGeneralizationForbiddenSet_0interp(lean_interpreter_value* stack)
{
lean_object* v_targets_296_ = stack[0].m_obj;
lean_object* v_forbidden_297_ = stack[1].m_obj;
lean_object* v_a_298_ = stack[2].m_obj;
lean_object* v_a_299_ = stack[3].m_obj;
lean_object* v_a_300_ = stack[4].m_obj;
lean_object* v_a_301_ = stack[5].m_obj;
lean_object* v_res_324_;
v_res_324_ = l_Lean_Meta_mkGeneralizationForbiddenSet(v_targets_296_, v_forbidden_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
stack->m_obj
 = v_res_324_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet___boxed(lean_object* v_targets_325_, lean_object* v_forbidden_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_Meta_mkGeneralizationForbiddenSet(v_targets_325_, v_forbidden_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec_ref(v_targets_325_);
return v_res_332_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1(uint8_t v___y_333_, lean_object* v_x_334_){
_start:
{
return v___y_333_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_333_ = stack[0].m_num;
lean_object* v_x_334_ = stack[1].m_obj;
uint8_t v_res_335_;
v_res_335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1(v___y_333_, v_x_334_);
stack->m_num = v_res_335_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed(lean_object* v___y_336_, lean_object* v_x_337_){
_start:
{
uint8_t v___y_8784__boxed_338_; uint8_t v_res_339_; lean_object* v_r_340_; 
v___y_8784__boxed_338_ = lean_unbox(v___y_336_);
v_res_339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1(v___y_8784__boxed_338_, v_x_337_);
lean_dec(v_x_337_);
v_r_340_ = lean_box(v_res_339_);
return v_r_340_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0(lean_object* v_fst_341_, lean_object* v_x_342_){
_start:
{
uint8_t v___x_343_; 
v___x_343_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v_x_342_, v_fst_341_);
return v___x_343_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_341_ = stack[0].m_obj;
lean_object* v_x_342_ = stack[1].m_obj;
uint8_t v_res_344_;
v_res_344_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0(v_fst_341_, v_x_342_);
stack->m_num = v_res_344_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed(lean_object* v_fst_345_, lean_object* v_x_346_){
_start:
{
uint8_t v_res_347_; lean_object* v_r_348_; 
v_res_347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0(v_fst_345_, v_x_346_);
lean_dec(v_x_346_);
lean_dec(v_fst_345_);
v_r_348_ = lean_box(v_res_347_);
return v_r_348_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(lean_object* v_forbidden_349_, uint8_t v_ignoreLetDecls_350_, lean_object* v_as_351_, size_t v_sz_352_, size_t v_i_353_, lean_object* v_b_354_, lean_object* v___y_355_){
_start:
{
uint8_t v___x_357_; 
v___x_357_ = lean_usize_dec_lt(v_i_353_, v_sz_352_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; 
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v_b_354_);
return v___x_358_;
}
else
{
lean_object* v_snd_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_518_; 
v_snd_359_ = lean_ctor_get(v_b_354_, 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v_b_354_);
if (v_isSharedCheck_518_ == 0)
{
lean_object* v_unused_519_; 
v_unused_519_ = lean_ctor_get(v_b_354_, 0);
lean_dec(v_unused_519_);
v___x_361_ = v_b_354_;
v_isShared_362_ = v_isSharedCheck_518_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_snd_359_);
lean_dec(v_b_354_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_518_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; lean_object* v_a_365_; lean_object* v_a_372_; 
v___x_363_ = lean_box(0);
v_a_372_ = lean_array_uget_borrowed(v_as_351_, v_i_353_);
if (lean_obj_tag(v_a_372_) == 0)
{
v_a_365_ = v_snd_359_;
goto v___jp_364_;
}
else
{
lean_object* v_val_373_; lean_object* v_fst_374_; lean_object* v_snd_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_517_; 
v_val_373_ = lean_ctor_get(v_a_372_, 0);
v_fst_374_ = lean_ctor_get(v_snd_359_, 0);
v_snd_375_ = lean_ctor_get(v_snd_359_, 1);
v_isSharedCheck_517_ = !lean_is_exclusive(v_snd_359_);
if (v_isSharedCheck_517_ == 0)
{
v___x_377_ = v_snd_359_;
v_isShared_378_ = v_isSharedCheck_517_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_snd_375_);
lean_inc(v_fst_374_);
lean_dec(v_snd_359_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_517_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_383_; uint8_t v_a_385_; uint8_t v_fst_391_; lean_object* v_mctx_392_; lean_object* v___y_408_; uint8_t v_fst_414_; lean_object* v_snd_415_; lean_object* v___y_432_; uint8_t v_fst_437_; lean_object* v_mctx_438_; lean_object* v___y_454_; uint8_t v___x_459_; 
v___x_383_ = l_Lean_LocalDecl_fvarId(v_val_373_);
v___x_459_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v___x_383_, v_forbidden_349_);
if (v___x_459_ == 0)
{
lean_object* v___f_460_; lean_object* v___y_462_; lean_object* v___y_463_; uint8_t v_fst_464_; lean_object* v_snd_465_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; uint8_t v___y_478_; uint8_t v___y_511_; uint8_t v___x_513_; 
lean_inc(v_fst_374_);
v___f_460_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_460_, 0, v_fst_374_);
v___x_513_ = l_Lean_LocalDecl_isAuxDecl(v_val_373_);
if (v___x_513_ == 0)
{
uint8_t v___x_514_; uint8_t v___x_515_; 
v___x_514_ = l_Lean_LocalDecl_binderInfo(v_val_373_);
v___x_515_ = l_Lean_BinderInfo_isInstImplicit(v___x_514_);
v___y_511_ = v___x_515_;
goto v___jp_510_;
}
else
{
v___y_511_ = v___x_513_;
goto v___jp_510_;
}
v___jp_461_:
{
if (v_fst_464_ == 0)
{
uint8_t v___x_466_; 
v___x_466_ = l_Lean_Expr_hasFVar(v___y_463_);
if (v___x_466_ == 0)
{
uint8_t v___x_467_; 
v___x_467_ = l_Lean_Expr_hasMVar(v___y_463_);
if (v___x_467_ == 0)
{
lean_dec_ref(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec_ref(v___f_460_);
v_fst_414_ = v___x_467_;
v_snd_415_ = v_snd_465_;
goto v___jp_413_;
}
else
{
lean_object* v___x_468_; 
v___x_468_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_460_, v___y_462_, v___y_463_, v_snd_465_);
v___y_432_ = v___x_468_;
goto v___jp_431_;
}
}
else
{
lean_object* v___x_469_; 
v___x_469_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_460_, v___y_462_, v___y_463_, v_snd_465_);
v___y_432_ = v___x_469_;
goto v___jp_431_;
}
}
else
{
lean_dec_ref(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec_ref(v___f_460_);
v_fst_414_ = v_fst_464_;
v_snd_415_ = v_snd_465_;
goto v___jp_413_;
}
}
v___jp_470_:
{
lean_object* v_fst_474_; lean_object* v_snd_475_; uint8_t v___x_476_; 
v_fst_474_ = lean_ctor_get(v___y_473_, 0);
lean_inc(v_fst_474_);
v_snd_475_ = lean_ctor_get(v___y_473_, 1);
lean_inc(v_snd_475_);
lean_dec_ref(v___y_473_);
v___x_476_ = lean_unbox(v_fst_474_);
lean_dec(v_fst_474_);
v___y_462_ = v___y_472_;
v___y_463_ = v___y_471_;
v_fst_464_ = v___x_476_;
v_snd_465_ = v_snd_475_;
goto v___jp_461_;
}
v___jp_477_:
{
if (v___y_478_ == 0)
{
lean_object* v___x_479_; lean_object* v___f_480_; 
lean_del_object(v___x_377_);
v___x_479_ = lean_box(v___y_478_);
v___f_480_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(v___f_480_, 0, v___x_479_);
if (lean_obj_tag(v_val_373_) == 0)
{
lean_object* v_type_481_; lean_object* v___x_482_; lean_object* v_mctx_483_; lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v_type_481_ = lean_ctor_get(v_val_373_, 3);
v___x_482_ = lean_st_ref_get(v___y_355_);
v_mctx_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc_ref_n(v_mctx_483_, 2);
lean_dec(v___x_482_);
v___x_484_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
lean_ctor_set(v___x_485_, 1, v_mctx_483_);
v___x_486_ = l_Lean_Expr_hasFVar(v_type_481_);
if (v___x_486_ == 0)
{
uint8_t v___x_487_; 
v___x_487_ = l_Lean_Expr_hasMVar(v_type_481_);
if (v___x_487_ == 0)
{
lean_dec_ref_known(v___x_485_, 2);
lean_dec_ref(v___f_480_);
lean_dec_ref(v___f_460_);
v_fst_437_ = v___x_487_;
v_mctx_438_ = v_mctx_483_;
goto v___jp_436_;
}
else
{
lean_object* v___x_488_; 
lean_dec_ref(v_mctx_483_);
lean_inc_ref(v_type_481_);
v___x_488_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_460_, v___f_480_, v_type_481_, v___x_485_);
v___y_454_ = v___x_488_;
goto v___jp_453_;
}
}
else
{
lean_object* v___x_489_; 
lean_dec_ref(v_mctx_483_);
lean_inc_ref(v_type_481_);
v___x_489_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_460_, v___f_480_, v_type_481_, v___x_485_);
v___y_454_ = v___x_489_;
goto v___jp_453_;
}
}
else
{
uint8_t v_nondep_490_; 
v_nondep_490_ = lean_ctor_get_uint8(v_val_373_, sizeof(void*)*5);
if (v_nondep_490_ == 0)
{
lean_object* v_type_491_; lean_object* v_value_492_; lean_object* v___x_493_; lean_object* v_mctx_494_; lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
v_type_491_ = lean_ctor_get(v_val_373_, 3);
v_value_492_ = lean_ctor_get(v_val_373_, 4);
v___x_493_ = lean_st_ref_get(v___y_355_);
v_mctx_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc_ref(v_mctx_494_);
lean_dec(v___x_493_);
v___x_495_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
lean_ctor_set(v___x_496_, 1, v_mctx_494_);
v___x_497_ = l_Lean_Expr_hasFVar(v_type_491_);
if (v___x_497_ == 0)
{
uint8_t v___x_498_; 
v___x_498_ = l_Lean_Expr_hasMVar(v_type_491_);
if (v___x_498_ == 0)
{
lean_inc_ref(v_value_492_);
v___y_462_ = v___f_480_;
v___y_463_ = v_value_492_;
v_fst_464_ = v___x_498_;
v_snd_465_ = v___x_496_;
goto v___jp_461_;
}
else
{
lean_object* v___x_499_; 
lean_inc_ref(v_type_491_);
lean_inc_ref(v___f_480_);
lean_inc_ref(v___f_460_);
v___x_499_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_460_, v___f_480_, v_type_491_, v___x_496_);
lean_inc_ref(v_value_492_);
v___y_471_ = v_value_492_;
v___y_472_ = v___f_480_;
v___y_473_ = v___x_499_;
goto v___jp_470_;
}
}
else
{
lean_object* v___x_500_; 
lean_inc_ref(v_type_491_);
lean_inc_ref(v___f_480_);
lean_inc_ref(v___f_460_);
v___x_500_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_460_, v___f_480_, v_type_491_, v___x_496_);
lean_inc_ref(v_value_492_);
v___y_471_ = v_value_492_;
v___y_472_ = v___f_480_;
v___y_473_ = v___x_500_;
goto v___jp_470_;
}
}
else
{
lean_object* v_type_501_; lean_object* v___x_502_; lean_object* v_mctx_503_; lean_object* v___x_504_; lean_object* v___x_505_; uint8_t v___x_506_; 
v_type_501_ = lean_ctor_get(v_val_373_, 3);
v___x_502_ = lean_st_ref_get(v___y_355_);
v_mctx_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc_ref_n(v_mctx_503_, 2);
lean_dec(v___x_502_);
v___x_504_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
lean_ctor_set(v___x_505_, 1, v_mctx_503_);
v___x_506_ = l_Lean_Expr_hasFVar(v_type_501_);
if (v___x_506_ == 0)
{
uint8_t v___x_507_; 
v___x_507_ = l_Lean_Expr_hasMVar(v_type_501_);
if (v___x_507_ == 0)
{
lean_dec_ref_known(v___x_505_, 2);
lean_dec_ref(v___f_480_);
lean_dec_ref(v___f_460_);
v_fst_391_ = v___x_507_;
v_mctx_392_ = v_mctx_503_;
goto v___jp_390_;
}
else
{
lean_object* v___x_508_; 
lean_dec_ref(v_mctx_503_);
lean_inc_ref(v_type_501_);
v___x_508_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_460_, v___f_480_, v_type_501_, v___x_505_);
v___y_408_ = v___x_508_;
goto v___jp_407_;
}
}
else
{
lean_object* v___x_509_; 
lean_dec_ref(v_mctx_503_);
lean_inc_ref(v_type_501_);
v___x_509_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_460_, v___f_480_, v_type_501_, v___x_505_);
v___y_408_ = v___x_509_;
goto v___jp_407_;
}
}
}
}
else
{
lean_dec_ref(v___f_460_);
lean_dec(v___x_383_);
goto v___jp_379_;
}
}
v___jp_510_:
{
if (v___y_511_ == 0)
{
if (v_ignoreLetDecls_350_ == 0)
{
v___y_478_ = v___x_459_;
goto v___jp_477_;
}
else
{
uint8_t v___x_512_; 
v___x_512_ = l_Lean_LocalDecl_isLet(v_val_373_, v___x_459_);
v___y_478_ = v___x_512_;
goto v___jp_477_;
}
}
else
{
lean_dec_ref(v___f_460_);
lean_dec(v___x_383_);
goto v___jp_379_;
}
}
}
else
{
lean_object* v___x_516_; 
lean_dec(v___x_383_);
lean_del_object(v___x_377_);
v___x_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_516_, 0, v_fst_374_);
lean_ctor_set(v___x_516_, 1, v_snd_375_);
v_a_365_ = v___x_516_;
goto v___jp_364_;
}
v___jp_379_:
{
lean_object* v___x_381_; 
if (v_isShared_378_ == 0)
{
v___x_381_ = v___x_377_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_fst_374_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_snd_375_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
v_a_365_ = v___x_381_;
goto v___jp_364_;
}
}
v___jp_384_:
{
if (v_a_385_ == 0)
{
lean_object* v___x_386_; 
lean_dec(v___x_383_);
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v_fst_374_);
lean_ctor_set(v___x_386_, 1, v_snd_375_);
v_a_365_ = v___x_386_;
goto v___jp_364_;
}
else
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
lean_inc(v___x_383_);
v___x_387_ = l_Lean_FVarIdSet_insert(v_snd_375_, v___x_383_);
v___x_388_ = l_Lean_FVarIdSet_insert(v_fst_374_, v___x_383_);
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
lean_ctor_set(v___x_389_, 1, v___x_387_);
v_a_365_ = v___x_389_;
goto v___jp_364_;
}
}
v___jp_390_:
{
lean_object* v___x_393_; lean_object* v_cache_394_; lean_object* v_zetaDeltaFVarIds_395_; lean_object* v_postponed_396_; lean_object* v_diag_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_405_; 
v___x_393_ = lean_st_ref_take(v___y_355_);
v_cache_394_ = lean_ctor_get(v___x_393_, 1);
v_zetaDeltaFVarIds_395_ = lean_ctor_get(v___x_393_, 2);
v_postponed_396_ = lean_ctor_get(v___x_393_, 3);
v_diag_397_ = lean_ctor_get(v___x_393_, 4);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_405_ == 0)
{
lean_object* v_unused_406_; 
v_unused_406_ = lean_ctor_get(v___x_393_, 0);
lean_dec(v_unused_406_);
v___x_399_ = v___x_393_;
v_isShared_400_ = v_isSharedCheck_405_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_diag_397_);
lean_inc(v_postponed_396_);
lean_inc(v_zetaDeltaFVarIds_395_);
lean_inc(v_cache_394_);
lean_dec(v___x_393_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_405_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v_mctx_392_);
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_mctx_392_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_cache_394_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v_zetaDeltaFVarIds_395_);
lean_ctor_set(v_reuseFailAlloc_404_, 3, v_postponed_396_);
lean_ctor_set(v_reuseFailAlloc_404_, 4, v_diag_397_);
v___x_402_ = v_reuseFailAlloc_404_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_403_; 
v___x_403_ = lean_st_ref_put(v___y_355_, v___x_402_);
v_a_385_ = v_fst_391_;
goto v___jp_384_;
}
}
}
v___jp_407_:
{
lean_object* v_snd_409_; lean_object* v_fst_410_; lean_object* v_mctx_411_; uint8_t v___x_412_; 
v_snd_409_ = lean_ctor_get(v___y_408_, 1);
lean_inc(v_snd_409_);
v_fst_410_ = lean_ctor_get(v___y_408_, 0);
lean_inc(v_fst_410_);
lean_dec_ref(v___y_408_);
v_mctx_411_ = lean_ctor_get(v_snd_409_, 1);
lean_inc_ref(v_mctx_411_);
lean_dec(v_snd_409_);
v___x_412_ = lean_unbox(v_fst_410_);
lean_dec(v_fst_410_);
v_fst_391_ = v___x_412_;
v_mctx_392_ = v_mctx_411_;
goto v___jp_390_;
}
v___jp_413_:
{
lean_object* v_mctx_416_; lean_object* v___x_417_; lean_object* v_cache_418_; lean_object* v_zetaDeltaFVarIds_419_; lean_object* v_postponed_420_; lean_object* v_diag_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_429_; 
v_mctx_416_ = lean_ctor_get(v_snd_415_, 1);
lean_inc_ref(v_mctx_416_);
lean_dec_ref(v_snd_415_);
v___x_417_ = lean_st_ref_take(v___y_355_);
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
v___x_427_ = lean_st_ref_put(v___y_355_, v___x_426_);
v_a_385_ = v_fst_414_;
goto v___jp_384_;
}
}
}
v___jp_431_:
{
lean_object* v_fst_433_; lean_object* v_snd_434_; uint8_t v___x_435_; 
v_fst_433_ = lean_ctor_get(v___y_432_, 0);
lean_inc(v_fst_433_);
v_snd_434_ = lean_ctor_get(v___y_432_, 1);
lean_inc(v_snd_434_);
lean_dec_ref(v___y_432_);
v___x_435_ = lean_unbox(v_fst_433_);
lean_dec(v_fst_433_);
v_fst_414_ = v___x_435_;
v_snd_415_ = v_snd_434_;
goto v___jp_413_;
}
v___jp_436_:
{
lean_object* v___x_439_; lean_object* v_cache_440_; lean_object* v_zetaDeltaFVarIds_441_; lean_object* v_postponed_442_; lean_object* v_diag_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_451_; 
v___x_439_ = lean_st_ref_take(v___y_355_);
v_cache_440_ = lean_ctor_get(v___x_439_, 1);
v_zetaDeltaFVarIds_441_ = lean_ctor_get(v___x_439_, 2);
v_postponed_442_ = lean_ctor_get(v___x_439_, 3);
v_diag_443_ = lean_ctor_get(v___x_439_, 4);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_451_ == 0)
{
lean_object* v_unused_452_; 
v_unused_452_ = lean_ctor_get(v___x_439_, 0);
lean_dec(v_unused_452_);
v___x_445_ = v___x_439_;
v_isShared_446_ = v_isSharedCheck_451_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_diag_443_);
lean_inc(v_postponed_442_);
lean_inc(v_zetaDeltaFVarIds_441_);
lean_inc(v_cache_440_);
lean_dec(v___x_439_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_451_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v_mctx_438_);
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_mctx_438_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v_cache_440_);
lean_ctor_set(v_reuseFailAlloc_450_, 2, v_zetaDeltaFVarIds_441_);
lean_ctor_set(v_reuseFailAlloc_450_, 3, v_postponed_442_);
lean_ctor_set(v_reuseFailAlloc_450_, 4, v_diag_443_);
v___x_448_ = v_reuseFailAlloc_450_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_449_; 
v___x_449_ = lean_st_ref_put(v___y_355_, v___x_448_);
v_a_385_ = v_fst_437_;
goto v___jp_384_;
}
}
}
v___jp_453_:
{
lean_object* v_snd_455_; lean_object* v_fst_456_; lean_object* v_mctx_457_; uint8_t v___x_458_; 
v_snd_455_ = lean_ctor_get(v___y_454_, 1);
lean_inc(v_snd_455_);
v_fst_456_ = lean_ctor_get(v___y_454_, 0);
lean_inc(v_fst_456_);
lean_dec_ref(v___y_454_);
v_mctx_457_ = lean_ctor_get(v_snd_455_, 1);
lean_inc_ref(v_mctx_457_);
lean_dec(v_snd_455_);
v___x_458_ = lean_unbox(v_fst_456_);
lean_dec(v_fst_456_);
v_fst_437_ = v___x_458_;
v_mctx_438_ = v_mctx_457_;
goto v___jp_436_;
}
}
}
v___jp_364_:
{
lean_object* v___x_367_; 
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 1, v_a_365_);
lean_ctor_set(v___x_361_, 0, v___x_363_);
v___x_367_ = v___x_361_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_a_365_);
v___x_367_ = v_reuseFailAlloc_371_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
size_t v___x_368_; size_t v___x_369_; 
v___x_368_ = ((size_t)1ULL);
v___x_369_ = lean_usize_add(v_i_353_, v___x_368_);
v_i_353_ = v___x_369_;
v_b_354_ = v___x_367_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_forbidden_349_ = stack[0].m_obj;
uint8_t v_ignoreLetDecls_350_ = stack[1].m_num;
lean_object* v_as_351_ = stack[2].m_obj;
size_t v_sz_352_ = stack[3].m_num;
size_t v_i_353_ = stack[4].m_num;
lean_object* v_b_354_ = stack[5].m_obj;
lean_object* v___y_355_ = stack[6].m_obj;
lean_object* v_res_520_;
v_res_520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(v_forbidden_349_, v_ignoreLetDecls_350_, v_as_351_, v_sz_352_, v_i_353_, v_b_354_, v___y_355_);
stack->m_obj
 = v_res_520_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_forbidden_521_, lean_object* v_ignoreLetDecls_522_, lean_object* v_as_523_, lean_object* v_sz_524_, lean_object* v_i_525_, lean_object* v_b_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_529_; size_t v_sz_boxed_530_; size_t v_i_boxed_531_; lean_object* v_res_532_; 
v_ignoreLetDecls_boxed_529_ = lean_unbox(v_ignoreLetDecls_522_);
v_sz_boxed_530_ = lean_unbox_usize(v_sz_524_);
lean_dec(v_sz_524_);
v_i_boxed_531_ = lean_unbox_usize(v_i_525_);
lean_dec(v_i_525_);
v_res_532_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(v_forbidden_521_, v_ignoreLetDecls_boxed_529_, v_as_523_, v_sz_boxed_530_, v_i_boxed_531_, v_b_526_, v___y_527_);
lean_dec(v___y_527_);
lean_dec_ref(v_as_523_);
lean_dec(v_forbidden_521_);
return v_res_532_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1(lean_object* v_forbidden_533_, uint8_t v_ignoreLetDecls_534_, lean_object* v_as_535_, size_t v_sz_536_, size_t v_i_537_, lean_object* v_b_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
uint8_t v___x_544_; 
v___x_544_ = lean_usize_dec_lt(v_i_537_, v_sz_536_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; 
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v_b_538_);
return v___x_545_;
}
else
{
lean_object* v_snd_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_705_; 
v_snd_546_ = lean_ctor_get(v_b_538_, 1);
v_isSharedCheck_705_ = !lean_is_exclusive(v_b_538_);
if (v_isSharedCheck_705_ == 0)
{
lean_object* v_unused_706_; 
v_unused_706_ = lean_ctor_get(v_b_538_, 0);
lean_dec(v_unused_706_);
v___x_548_ = v_b_538_;
v_isShared_549_ = v_isSharedCheck_705_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_snd_546_);
lean_dec(v_b_538_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_705_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; lean_object* v_a_552_; lean_object* v_a_559_; 
v___x_550_ = lean_box(0);
v_a_559_ = lean_array_uget_borrowed(v_as_535_, v_i_537_);
if (lean_obj_tag(v_a_559_) == 0)
{
v_a_552_ = v_snd_546_;
goto v___jp_551_;
}
else
{
lean_object* v_val_560_; lean_object* v_fst_561_; lean_object* v_snd_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_704_; 
v_val_560_ = lean_ctor_get(v_a_559_, 0);
v_fst_561_ = lean_ctor_get(v_snd_546_, 0);
v_snd_562_ = lean_ctor_get(v_snd_546_, 1);
v_isSharedCheck_704_ = !lean_is_exclusive(v_snd_546_);
if (v_isSharedCheck_704_ == 0)
{
v___x_564_ = v_snd_546_;
v_isShared_565_ = v_isSharedCheck_704_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_snd_562_);
lean_inc(v_fst_561_);
lean_dec(v_snd_546_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_704_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_570_; uint8_t v_a_572_; uint8_t v_fst_578_; lean_object* v_mctx_579_; lean_object* v___y_595_; uint8_t v_fst_601_; lean_object* v_snd_602_; lean_object* v___y_619_; uint8_t v_fst_624_; lean_object* v_mctx_625_; lean_object* v___y_641_; uint8_t v___x_646_; 
v___x_570_ = l_Lean_LocalDecl_fvarId(v_val_560_);
v___x_646_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v___x_570_, v_forbidden_533_);
if (v___x_646_ == 0)
{
lean_object* v___f_647_; lean_object* v___y_649_; lean_object* v___y_650_; uint8_t v_fst_651_; lean_object* v_snd_652_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; uint8_t v___y_665_; uint8_t v___y_698_; uint8_t v___x_700_; 
lean_inc(v_fst_561_);
v___f_647_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_647_, 0, v_fst_561_);
v___x_700_ = l_Lean_LocalDecl_isAuxDecl(v_val_560_);
if (v___x_700_ == 0)
{
uint8_t v___x_701_; uint8_t v___x_702_; 
v___x_701_ = l_Lean_LocalDecl_binderInfo(v_val_560_);
v___x_702_ = l_Lean_BinderInfo_isInstImplicit(v___x_701_);
v___y_698_ = v___x_702_;
goto v___jp_697_;
}
else
{
v___y_698_ = v___x_700_;
goto v___jp_697_;
}
v___jp_648_:
{
if (v_fst_651_ == 0)
{
uint8_t v___x_653_; 
v___x_653_ = l_Lean_Expr_hasFVar(v___y_650_);
if (v___x_653_ == 0)
{
uint8_t v___x_654_; 
v___x_654_ = l_Lean_Expr_hasMVar(v___y_650_);
if (v___x_654_ == 0)
{
lean_dec_ref(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec_ref(v___f_647_);
v_fst_601_ = v___x_654_;
v_snd_602_ = v_snd_652_;
goto v___jp_600_;
}
else
{
lean_object* v___x_655_; 
v___x_655_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_647_, v___y_649_, v___y_650_, v_snd_652_);
v___y_619_ = v___x_655_;
goto v___jp_618_;
}
}
else
{
lean_object* v___x_656_; 
v___x_656_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_647_, v___y_649_, v___y_650_, v_snd_652_);
v___y_619_ = v___x_656_;
goto v___jp_618_;
}
}
else
{
lean_dec_ref(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec_ref(v___f_647_);
v_fst_601_ = v_fst_651_;
v_snd_602_ = v_snd_652_;
goto v___jp_600_;
}
}
v___jp_657_:
{
lean_object* v_fst_661_; lean_object* v_snd_662_; uint8_t v___x_663_; 
v_fst_661_ = lean_ctor_get(v___y_660_, 0);
lean_inc(v_fst_661_);
v_snd_662_ = lean_ctor_get(v___y_660_, 1);
lean_inc(v_snd_662_);
lean_dec_ref(v___y_660_);
v___x_663_ = lean_unbox(v_fst_661_);
lean_dec(v_fst_661_);
v___y_649_ = v___y_658_;
v___y_650_ = v___y_659_;
v_fst_651_ = v___x_663_;
v_snd_652_ = v_snd_662_;
goto v___jp_648_;
}
v___jp_664_:
{
if (v___y_665_ == 0)
{
lean_object* v___x_666_; lean_object* v___f_667_; 
lean_del_object(v___x_564_);
v___x_666_ = lean_box(v___y_665_);
v___f_667_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(v___f_667_, 0, v___x_666_);
if (lean_obj_tag(v_val_560_) == 0)
{
lean_object* v_type_668_; lean_object* v___x_669_; lean_object* v_mctx_670_; lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v_type_668_ = lean_ctor_get(v_val_560_, 3);
v___x_669_ = lean_st_ref_get(v___y_540_);
v_mctx_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc_ref_n(v_mctx_670_, 2);
lean_dec(v___x_669_);
v___x_671_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set(v___x_672_, 1, v_mctx_670_);
v___x_673_ = l_Lean_Expr_hasFVar(v_type_668_);
if (v___x_673_ == 0)
{
uint8_t v___x_674_; 
v___x_674_ = l_Lean_Expr_hasMVar(v_type_668_);
if (v___x_674_ == 0)
{
lean_dec_ref_known(v___x_672_, 2);
lean_dec_ref(v___f_667_);
lean_dec_ref(v___f_647_);
v_fst_624_ = v___x_674_;
v_mctx_625_ = v_mctx_670_;
goto v___jp_623_;
}
else
{
lean_object* v___x_675_; 
lean_dec_ref(v_mctx_670_);
lean_inc_ref(v_type_668_);
v___x_675_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_647_, v___f_667_, v_type_668_, v___x_672_);
v___y_641_ = v___x_675_;
goto v___jp_640_;
}
}
else
{
lean_object* v___x_676_; 
lean_dec_ref(v_mctx_670_);
lean_inc_ref(v_type_668_);
v___x_676_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_647_, v___f_667_, v_type_668_, v___x_672_);
v___y_641_ = v___x_676_;
goto v___jp_640_;
}
}
else
{
uint8_t v_nondep_677_; 
v_nondep_677_ = lean_ctor_get_uint8(v_val_560_, sizeof(void*)*5);
if (v_nondep_677_ == 0)
{
lean_object* v_type_678_; lean_object* v_value_679_; lean_object* v___x_680_; lean_object* v_mctx_681_; lean_object* v___x_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v_type_678_ = lean_ctor_get(v_val_560_, 3);
v_value_679_ = lean_ctor_get(v_val_560_, 4);
v___x_680_ = lean_st_ref_get(v___y_540_);
v_mctx_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc_ref(v_mctx_681_);
lean_dec(v___x_680_);
v___x_682_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
lean_ctor_set(v___x_683_, 1, v_mctx_681_);
v___x_684_ = l_Lean_Expr_hasFVar(v_type_678_);
if (v___x_684_ == 0)
{
uint8_t v___x_685_; 
v___x_685_ = l_Lean_Expr_hasMVar(v_type_678_);
if (v___x_685_ == 0)
{
lean_inc_ref(v_value_679_);
v___y_649_ = v___f_667_;
v___y_650_ = v_value_679_;
v_fst_651_ = v___x_685_;
v_snd_652_ = v___x_683_;
goto v___jp_648_;
}
else
{
lean_object* v___x_686_; 
lean_inc_ref(v_type_678_);
lean_inc_ref(v___f_667_);
lean_inc_ref(v___f_647_);
v___x_686_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_647_, v___f_667_, v_type_678_, v___x_683_);
lean_inc_ref(v_value_679_);
v___y_658_ = v___f_667_;
v___y_659_ = v_value_679_;
v___y_660_ = v___x_686_;
goto v___jp_657_;
}
}
else
{
lean_object* v___x_687_; 
lean_inc_ref(v_type_678_);
lean_inc_ref(v___f_667_);
lean_inc_ref(v___f_647_);
v___x_687_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_647_, v___f_667_, v_type_678_, v___x_683_);
lean_inc_ref(v_value_679_);
v___y_658_ = v___f_667_;
v___y_659_ = v_value_679_;
v___y_660_ = v___x_687_;
goto v___jp_657_;
}
}
else
{
lean_object* v_type_688_; lean_object* v___x_689_; lean_object* v_mctx_690_; lean_object* v___x_691_; lean_object* v___x_692_; uint8_t v___x_693_; 
v_type_688_ = lean_ctor_get(v_val_560_, 3);
v___x_689_ = lean_st_ref_get(v___y_540_);
v_mctx_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc_ref_n(v_mctx_690_, 2);
lean_dec(v___x_689_);
v___x_691_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v_mctx_690_);
v___x_693_ = l_Lean_Expr_hasFVar(v_type_688_);
if (v___x_693_ == 0)
{
uint8_t v___x_694_; 
v___x_694_ = l_Lean_Expr_hasMVar(v_type_688_);
if (v___x_694_ == 0)
{
lean_dec_ref_known(v___x_692_, 2);
lean_dec_ref(v___f_667_);
lean_dec_ref(v___f_647_);
v_fst_578_ = v___x_694_;
v_mctx_579_ = v_mctx_690_;
goto v___jp_577_;
}
else
{
lean_object* v___x_695_; 
lean_dec_ref(v_mctx_690_);
lean_inc_ref(v_type_688_);
v___x_695_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_647_, v___f_667_, v_type_688_, v___x_692_);
v___y_595_ = v___x_695_;
goto v___jp_594_;
}
}
else
{
lean_object* v___x_696_; 
lean_dec_ref(v_mctx_690_);
lean_inc_ref(v_type_688_);
v___x_696_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_647_, v___f_667_, v_type_688_, v___x_692_);
v___y_595_ = v___x_696_;
goto v___jp_594_;
}
}
}
}
else
{
lean_dec_ref(v___f_647_);
lean_dec(v___x_570_);
goto v___jp_566_;
}
}
v___jp_697_:
{
if (v___y_698_ == 0)
{
if (v_ignoreLetDecls_534_ == 0)
{
v___y_665_ = v___x_646_;
goto v___jp_664_;
}
else
{
uint8_t v___x_699_; 
v___x_699_ = l_Lean_LocalDecl_isLet(v_val_560_, v___x_646_);
v___y_665_ = v___x_699_;
goto v___jp_664_;
}
}
else
{
lean_dec_ref(v___f_647_);
lean_dec(v___x_570_);
goto v___jp_566_;
}
}
}
else
{
lean_object* v___x_703_; 
lean_dec(v___x_570_);
lean_del_object(v___x_564_);
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v_fst_561_);
lean_ctor_set(v___x_703_, 1, v_snd_562_);
v_a_552_ = v___x_703_;
goto v___jp_551_;
}
v___jp_566_:
{
lean_object* v___x_568_; 
if (v_isShared_565_ == 0)
{
v___x_568_ = v___x_564_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_fst_561_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_snd_562_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
v_a_552_ = v___x_568_;
goto v___jp_551_;
}
}
v___jp_571_:
{
if (v_a_572_ == 0)
{
lean_object* v___x_573_; 
lean_dec(v___x_570_);
v___x_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_573_, 0, v_fst_561_);
lean_ctor_set(v___x_573_, 1, v_snd_562_);
v_a_552_ = v___x_573_;
goto v___jp_551_;
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
lean_inc(v___x_570_);
v___x_574_ = l_Lean_FVarIdSet_insert(v_snd_562_, v___x_570_);
v___x_575_ = l_Lean_FVarIdSet_insert(v_fst_561_, v___x_570_);
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
lean_ctor_set(v___x_576_, 1, v___x_574_);
v_a_552_ = v___x_576_;
goto v___jp_551_;
}
}
v___jp_577_:
{
lean_object* v___x_580_; lean_object* v_cache_581_; lean_object* v_zetaDeltaFVarIds_582_; lean_object* v_postponed_583_; lean_object* v_diag_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_592_; 
v___x_580_ = lean_st_ref_take(v___y_540_);
v_cache_581_ = lean_ctor_get(v___x_580_, 1);
v_zetaDeltaFVarIds_582_ = lean_ctor_get(v___x_580_, 2);
v_postponed_583_ = lean_ctor_get(v___x_580_, 3);
v_diag_584_ = lean_ctor_get(v___x_580_, 4);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_592_ == 0)
{
lean_object* v_unused_593_; 
v_unused_593_ = lean_ctor_get(v___x_580_, 0);
lean_dec(v_unused_593_);
v___x_586_ = v___x_580_;
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_diag_584_);
lean_inc(v_postponed_583_);
lean_inc(v_zetaDeltaFVarIds_582_);
lean_inc(v_cache_581_);
lean_dec(v___x_580_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v_mctx_579_);
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_mctx_579_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_cache_581_);
lean_ctor_set(v_reuseFailAlloc_591_, 2, v_zetaDeltaFVarIds_582_);
lean_ctor_set(v_reuseFailAlloc_591_, 3, v_postponed_583_);
lean_ctor_set(v_reuseFailAlloc_591_, 4, v_diag_584_);
v___x_589_ = v_reuseFailAlloc_591_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_590_; 
v___x_590_ = lean_st_ref_put(v___y_540_, v___x_589_);
v_a_572_ = v_fst_578_;
goto v___jp_571_;
}
}
}
v___jp_594_:
{
lean_object* v_snd_596_; lean_object* v_fst_597_; lean_object* v_mctx_598_; uint8_t v___x_599_; 
v_snd_596_ = lean_ctor_get(v___y_595_, 1);
lean_inc(v_snd_596_);
v_fst_597_ = lean_ctor_get(v___y_595_, 0);
lean_inc(v_fst_597_);
lean_dec_ref(v___y_595_);
v_mctx_598_ = lean_ctor_get(v_snd_596_, 1);
lean_inc_ref(v_mctx_598_);
lean_dec(v_snd_596_);
v___x_599_ = lean_unbox(v_fst_597_);
lean_dec(v_fst_597_);
v_fst_578_ = v___x_599_;
v_mctx_579_ = v_mctx_598_;
goto v___jp_577_;
}
v___jp_600_:
{
lean_object* v_mctx_603_; lean_object* v___x_604_; lean_object* v_cache_605_; lean_object* v_zetaDeltaFVarIds_606_; lean_object* v_postponed_607_; lean_object* v_diag_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_616_; 
v_mctx_603_ = lean_ctor_get(v_snd_602_, 1);
lean_inc_ref(v_mctx_603_);
lean_dec_ref(v_snd_602_);
v___x_604_ = lean_st_ref_take(v___y_540_);
v_cache_605_ = lean_ctor_get(v___x_604_, 1);
v_zetaDeltaFVarIds_606_ = lean_ctor_get(v___x_604_, 2);
v_postponed_607_ = lean_ctor_get(v___x_604_, 3);
v_diag_608_ = lean_ctor_get(v___x_604_, 4);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_616_ == 0)
{
lean_object* v_unused_617_; 
v_unused_617_ = lean_ctor_get(v___x_604_, 0);
lean_dec(v_unused_617_);
v___x_610_ = v___x_604_;
v_isShared_611_ = v_isSharedCheck_616_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_diag_608_);
lean_inc(v_postponed_607_);
lean_inc(v_zetaDeltaFVarIds_606_);
lean_inc(v_cache_605_);
lean_dec(v___x_604_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_616_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v_mctx_603_);
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_mctx_603_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_cache_605_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v_zetaDeltaFVarIds_606_);
lean_ctor_set(v_reuseFailAlloc_615_, 3, v_postponed_607_);
lean_ctor_set(v_reuseFailAlloc_615_, 4, v_diag_608_);
v___x_613_ = v_reuseFailAlloc_615_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_614_; 
v___x_614_ = lean_st_ref_put(v___y_540_, v___x_613_);
v_a_572_ = v_fst_601_;
goto v___jp_571_;
}
}
}
v___jp_618_:
{
lean_object* v_fst_620_; lean_object* v_snd_621_; uint8_t v___x_622_; 
v_fst_620_ = lean_ctor_get(v___y_619_, 0);
lean_inc(v_fst_620_);
v_snd_621_ = lean_ctor_get(v___y_619_, 1);
lean_inc(v_snd_621_);
lean_dec_ref(v___y_619_);
v___x_622_ = lean_unbox(v_fst_620_);
lean_dec(v_fst_620_);
v_fst_601_ = v___x_622_;
v_snd_602_ = v_snd_621_;
goto v___jp_600_;
}
v___jp_623_:
{
lean_object* v___x_626_; lean_object* v_cache_627_; lean_object* v_zetaDeltaFVarIds_628_; lean_object* v_postponed_629_; lean_object* v_diag_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_638_; 
v___x_626_ = lean_st_ref_take(v___y_540_);
v_cache_627_ = lean_ctor_get(v___x_626_, 1);
v_zetaDeltaFVarIds_628_ = lean_ctor_get(v___x_626_, 2);
v_postponed_629_ = lean_ctor_get(v___x_626_, 3);
v_diag_630_ = lean_ctor_get(v___x_626_, 4);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_638_ == 0)
{
lean_object* v_unused_639_; 
v_unused_639_ = lean_ctor_get(v___x_626_, 0);
lean_dec(v_unused_639_);
v___x_632_ = v___x_626_;
v_isShared_633_ = v_isSharedCheck_638_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_diag_630_);
lean_inc(v_postponed_629_);
lean_inc(v_zetaDeltaFVarIds_628_);
lean_inc(v_cache_627_);
lean_dec(v___x_626_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_638_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v_mctx_625_);
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_mctx_625_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_cache_627_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_zetaDeltaFVarIds_628_);
lean_ctor_set(v_reuseFailAlloc_637_, 3, v_postponed_629_);
lean_ctor_set(v_reuseFailAlloc_637_, 4, v_diag_630_);
v___x_635_ = v_reuseFailAlloc_637_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_object* v___x_636_; 
v___x_636_ = lean_st_ref_put(v___y_540_, v___x_635_);
v_a_572_ = v_fst_624_;
goto v___jp_571_;
}
}
}
v___jp_640_:
{
lean_object* v_snd_642_; lean_object* v_fst_643_; lean_object* v_mctx_644_; uint8_t v___x_645_; 
v_snd_642_ = lean_ctor_get(v___y_641_, 1);
lean_inc(v_snd_642_);
v_fst_643_ = lean_ctor_get(v___y_641_, 0);
lean_inc(v_fst_643_);
lean_dec_ref(v___y_641_);
v_mctx_644_ = lean_ctor_get(v_snd_642_, 1);
lean_inc_ref(v_mctx_644_);
lean_dec(v_snd_642_);
v___x_645_ = lean_unbox(v_fst_643_);
lean_dec(v_fst_643_);
v_fst_624_ = v___x_645_;
v_mctx_625_ = v_mctx_644_;
goto v___jp_623_;
}
}
}
v___jp_551_:
{
lean_object* v___x_554_; 
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 1, v_a_552_);
lean_ctor_set(v___x_548_, 0, v___x_550_);
v___x_554_ = v___x_548_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_550_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_a_552_);
v___x_554_ = v_reuseFailAlloc_558_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
size_t v___x_555_; size_t v___x_556_; lean_object* v___x_557_; 
v___x_555_ = ((size_t)1ULL);
v___x_556_ = lean_usize_add(v_i_537_, v___x_555_);
v___x_557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(v_forbidden_533_, v_ignoreLetDecls_534_, v_as_535_, v_sz_536_, v___x_556_, v___x_554_, v___y_540_);
return v___x_557_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_forbidden_533_ = stack[0].m_obj;
uint8_t v_ignoreLetDecls_534_ = stack[1].m_num;
lean_object* v_as_535_ = stack[2].m_obj;
size_t v_sz_536_ = stack[3].m_num;
size_t v_i_537_ = stack[4].m_num;
lean_object* v_b_538_ = stack[5].m_obj;
lean_object* v___y_539_ = stack[6].m_obj;
lean_object* v___y_540_ = stack[7].m_obj;
lean_object* v___y_541_ = stack[8].m_obj;
lean_object* v___y_542_ = stack[9].m_obj;
lean_object* v_res_707_;
v_res_707_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1(v_forbidden_533_, v_ignoreLetDecls_534_, v_as_535_, v_sz_536_, v_i_537_, v_b_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
stack->m_obj
 = v_res_707_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___boxed(lean_object* v_forbidden_708_, lean_object* v_ignoreLetDecls_709_, lean_object* v_as_710_, lean_object* v_sz_711_, lean_object* v_i_712_, lean_object* v_b_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_719_; size_t v_sz_boxed_720_; size_t v_i_boxed_721_; lean_object* v_res_722_; 
v_ignoreLetDecls_boxed_719_ = lean_unbox(v_ignoreLetDecls_709_);
v_sz_boxed_720_ = lean_unbox_usize(v_sz_711_);
lean_dec(v_sz_711_);
v_i_boxed_721_ = lean_unbox_usize(v_i_712_);
lean_dec(v_i_712_);
v_res_722_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1(v_forbidden_708_, v_ignoreLetDecls_boxed_719_, v_as_710_, v_sz_boxed_720_, v_i_boxed_721_, v_b_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec_ref(v_as_710_);
lean_dec(v_forbidden_708_);
return v_res_722_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_forbidden_723_, uint8_t v_ignoreLetDecls_724_, lean_object* v_as_725_, size_t v_sz_726_, size_t v_i_727_, lean_object* v_b_728_, lean_object* v___y_729_){
_start:
{
uint8_t v___x_731_; 
v___x_731_ = lean_usize_dec_lt(v_i_727_, v_sz_726_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; 
v___x_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_732_, 0, v_b_728_);
return v___x_732_;
}
else
{
lean_object* v_snd_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_892_; 
v_snd_733_ = lean_ctor_get(v_b_728_, 1);
v_isSharedCheck_892_ = !lean_is_exclusive(v_b_728_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v_b_728_, 0);
lean_dec(v_unused_893_);
v___x_735_ = v_b_728_;
v_isShared_736_ = v_isSharedCheck_892_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_snd_733_);
lean_dec(v_b_728_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_892_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; lean_object* v_a_739_; lean_object* v_a_746_; 
v___x_737_ = lean_box(0);
v_a_746_ = lean_array_uget_borrowed(v_as_725_, v_i_727_);
if (lean_obj_tag(v_a_746_) == 0)
{
v_a_739_ = v_snd_733_;
goto v___jp_738_;
}
else
{
lean_object* v_val_747_; lean_object* v_fst_748_; lean_object* v_snd_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_891_; 
v_val_747_ = lean_ctor_get(v_a_746_, 0);
v_fst_748_ = lean_ctor_get(v_snd_733_, 0);
v_snd_749_ = lean_ctor_get(v_snd_733_, 1);
v_isSharedCheck_891_ = !lean_is_exclusive(v_snd_733_);
if (v_isSharedCheck_891_ == 0)
{
v___x_751_ = v_snd_733_;
v_isShared_752_ = v_isSharedCheck_891_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_snd_749_);
lean_inc(v_fst_748_);
lean_dec(v_snd_733_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_891_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_757_; uint8_t v_a_759_; uint8_t v_fst_765_; lean_object* v_mctx_766_; lean_object* v___y_782_; uint8_t v_fst_788_; lean_object* v_snd_789_; lean_object* v___y_806_; uint8_t v_fst_811_; lean_object* v_mctx_812_; lean_object* v___y_828_; uint8_t v___x_833_; 
v___x_757_ = l_Lean_LocalDecl_fvarId(v_val_747_);
v___x_833_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v___x_757_, v_forbidden_723_);
if (v___x_833_ == 0)
{
lean_object* v___f_834_; lean_object* v___y_836_; lean_object* v___y_837_; uint8_t v_fst_838_; lean_object* v_snd_839_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; uint8_t v___y_852_; uint8_t v___y_885_; uint8_t v___x_887_; 
lean_inc(v_fst_748_);
v___f_834_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_834_, 0, v_fst_748_);
v___x_887_ = l_Lean_LocalDecl_isAuxDecl(v_val_747_);
if (v___x_887_ == 0)
{
uint8_t v___x_888_; uint8_t v___x_889_; 
v___x_888_ = l_Lean_LocalDecl_binderInfo(v_val_747_);
v___x_889_ = l_Lean_BinderInfo_isInstImplicit(v___x_888_);
v___y_885_ = v___x_889_;
goto v___jp_884_;
}
else
{
v___y_885_ = v___x_887_;
goto v___jp_884_;
}
v___jp_835_:
{
if (v_fst_838_ == 0)
{
uint8_t v___x_840_; 
v___x_840_ = l_Lean_Expr_hasFVar(v___y_837_);
if (v___x_840_ == 0)
{
uint8_t v___x_841_; 
v___x_841_ = l_Lean_Expr_hasMVar(v___y_837_);
if (v___x_841_ == 0)
{
lean_dec_ref(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec_ref(v___f_834_);
v_fst_788_ = v___x_841_;
v_snd_789_ = v_snd_839_;
goto v___jp_787_;
}
else
{
lean_object* v___x_842_; 
v___x_842_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_834_, v___y_836_, v___y_837_, v_snd_839_);
v___y_806_ = v___x_842_;
goto v___jp_805_;
}
}
else
{
lean_object* v___x_843_; 
v___x_843_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_834_, v___y_836_, v___y_837_, v_snd_839_);
v___y_806_ = v___x_843_;
goto v___jp_805_;
}
}
else
{
lean_dec_ref(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec_ref(v___f_834_);
v_fst_788_ = v_fst_838_;
v_snd_789_ = v_snd_839_;
goto v___jp_787_;
}
}
v___jp_844_:
{
lean_object* v_fst_848_; lean_object* v_snd_849_; uint8_t v___x_850_; 
v_fst_848_ = lean_ctor_get(v___y_847_, 0);
lean_inc(v_fst_848_);
v_snd_849_ = lean_ctor_get(v___y_847_, 1);
lean_inc(v_snd_849_);
lean_dec_ref(v___y_847_);
v___x_850_ = lean_unbox(v_fst_848_);
lean_dec(v_fst_848_);
v___y_836_ = v___y_845_;
v___y_837_ = v___y_846_;
v_fst_838_ = v___x_850_;
v_snd_839_ = v_snd_849_;
goto v___jp_835_;
}
v___jp_851_:
{
if (v___y_852_ == 0)
{
lean_object* v___x_853_; lean_object* v___f_854_; 
lean_del_object(v___x_751_);
v___x_853_ = lean_box(v___y_852_);
v___f_854_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(v___f_854_, 0, v___x_853_);
if (lean_obj_tag(v_val_747_) == 0)
{
lean_object* v_type_855_; lean_object* v___x_856_; lean_object* v_mctx_857_; lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v_type_855_ = lean_ctor_get(v_val_747_, 3);
v___x_856_ = lean_st_ref_get(v___y_729_);
v_mctx_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc_ref_n(v_mctx_857_, 2);
lean_dec(v___x_856_);
v___x_858_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
lean_ctor_set(v___x_859_, 1, v_mctx_857_);
v___x_860_ = l_Lean_Expr_hasFVar(v_type_855_);
if (v___x_860_ == 0)
{
uint8_t v___x_861_; 
v___x_861_ = l_Lean_Expr_hasMVar(v_type_855_);
if (v___x_861_ == 0)
{
lean_dec_ref_known(v___x_859_, 2);
lean_dec_ref(v___f_854_);
lean_dec_ref(v___f_834_);
v_fst_811_ = v___x_861_;
v_mctx_812_ = v_mctx_857_;
goto v___jp_810_;
}
else
{
lean_object* v___x_862_; 
lean_dec_ref(v_mctx_857_);
lean_inc_ref(v_type_855_);
v___x_862_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_834_, v___f_854_, v_type_855_, v___x_859_);
v___y_828_ = v___x_862_;
goto v___jp_827_;
}
}
else
{
lean_object* v___x_863_; 
lean_dec_ref(v_mctx_857_);
lean_inc_ref(v_type_855_);
v___x_863_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_834_, v___f_854_, v_type_855_, v___x_859_);
v___y_828_ = v___x_863_;
goto v___jp_827_;
}
}
else
{
uint8_t v_nondep_864_; 
v_nondep_864_ = lean_ctor_get_uint8(v_val_747_, sizeof(void*)*5);
if (v_nondep_864_ == 0)
{
lean_object* v_type_865_; lean_object* v_value_866_; lean_object* v___x_867_; lean_object* v_mctx_868_; lean_object* v___x_869_; lean_object* v___x_870_; uint8_t v___x_871_; 
v_type_865_ = lean_ctor_get(v_val_747_, 3);
v_value_866_ = lean_ctor_get(v_val_747_, 4);
v___x_867_ = lean_st_ref_get(v___y_729_);
v_mctx_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc_ref(v_mctx_868_);
lean_dec(v___x_867_);
v___x_869_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
lean_ctor_set(v___x_870_, 1, v_mctx_868_);
v___x_871_ = l_Lean_Expr_hasFVar(v_type_865_);
if (v___x_871_ == 0)
{
uint8_t v___x_872_; 
v___x_872_ = l_Lean_Expr_hasMVar(v_type_865_);
if (v___x_872_ == 0)
{
lean_inc_ref(v_value_866_);
v___y_836_ = v___f_854_;
v___y_837_ = v_value_866_;
v_fst_838_ = v___x_872_;
v_snd_839_ = v___x_870_;
goto v___jp_835_;
}
else
{
lean_object* v___x_873_; 
lean_inc_ref(v_type_865_);
lean_inc_ref(v___f_854_);
lean_inc_ref(v___f_834_);
v___x_873_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_834_, v___f_854_, v_type_865_, v___x_870_);
lean_inc_ref(v_value_866_);
v___y_845_ = v___f_854_;
v___y_846_ = v_value_866_;
v___y_847_ = v___x_873_;
goto v___jp_844_;
}
}
else
{
lean_object* v___x_874_; 
lean_inc_ref(v_type_865_);
lean_inc_ref(v___f_854_);
lean_inc_ref(v___f_834_);
v___x_874_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_834_, v___f_854_, v_type_865_, v___x_870_);
lean_inc_ref(v_value_866_);
v___y_845_ = v___f_854_;
v___y_846_ = v_value_866_;
v___y_847_ = v___x_874_;
goto v___jp_844_;
}
}
else
{
lean_object* v_type_875_; lean_object* v___x_876_; lean_object* v_mctx_877_; lean_object* v___x_878_; lean_object* v___x_879_; uint8_t v___x_880_; 
v_type_875_ = lean_ctor_get(v_val_747_, 3);
v___x_876_ = lean_st_ref_get(v___y_729_);
v_mctx_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc_ref_n(v_mctx_877_, 2);
lean_dec(v___x_876_);
v___x_878_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
lean_ctor_set(v___x_879_, 1, v_mctx_877_);
v___x_880_ = l_Lean_Expr_hasFVar(v_type_875_);
if (v___x_880_ == 0)
{
uint8_t v___x_881_; 
v___x_881_ = l_Lean_Expr_hasMVar(v_type_875_);
if (v___x_881_ == 0)
{
lean_dec_ref_known(v___x_879_, 2);
lean_dec_ref(v___f_854_);
lean_dec_ref(v___f_834_);
v_fst_765_ = v___x_881_;
v_mctx_766_ = v_mctx_877_;
goto v___jp_764_;
}
else
{
lean_object* v___x_882_; 
lean_dec_ref(v_mctx_877_);
lean_inc_ref(v_type_875_);
v___x_882_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_834_, v___f_854_, v_type_875_, v___x_879_);
v___y_782_ = v___x_882_;
goto v___jp_781_;
}
}
else
{
lean_object* v___x_883_; 
lean_dec_ref(v_mctx_877_);
lean_inc_ref(v_type_875_);
v___x_883_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_834_, v___f_854_, v_type_875_, v___x_879_);
v___y_782_ = v___x_883_;
goto v___jp_781_;
}
}
}
}
else
{
lean_dec_ref(v___f_834_);
lean_dec(v___x_757_);
goto v___jp_753_;
}
}
v___jp_884_:
{
if (v___y_885_ == 0)
{
if (v_ignoreLetDecls_724_ == 0)
{
v___y_852_ = v___x_833_;
goto v___jp_851_;
}
else
{
uint8_t v___x_886_; 
v___x_886_ = l_Lean_LocalDecl_isLet(v_val_747_, v___x_833_);
v___y_852_ = v___x_886_;
goto v___jp_851_;
}
}
else
{
lean_dec_ref(v___f_834_);
lean_dec(v___x_757_);
goto v___jp_753_;
}
}
}
else
{
lean_object* v___x_890_; 
lean_dec(v___x_757_);
lean_del_object(v___x_751_);
v___x_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_890_, 0, v_fst_748_);
lean_ctor_set(v___x_890_, 1, v_snd_749_);
v_a_739_ = v___x_890_;
goto v___jp_738_;
}
v___jp_753_:
{
lean_object* v___x_755_; 
if (v_isShared_752_ == 0)
{
v___x_755_ = v___x_751_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_fst_748_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_snd_749_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
v_a_739_ = v___x_755_;
goto v___jp_738_;
}
}
v___jp_758_:
{
if (v_a_759_ == 0)
{
lean_object* v___x_760_; 
lean_dec(v___x_757_);
v___x_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_760_, 0, v_fst_748_);
lean_ctor_set(v___x_760_, 1, v_snd_749_);
v_a_739_ = v___x_760_;
goto v___jp_738_;
}
else
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
lean_inc(v___x_757_);
v___x_761_ = l_Lean_FVarIdSet_insert(v_snd_749_, v___x_757_);
v___x_762_ = l_Lean_FVarIdSet_insert(v_fst_748_, v___x_757_);
v___x_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
lean_ctor_set(v___x_763_, 1, v___x_761_);
v_a_739_ = v___x_763_;
goto v___jp_738_;
}
}
v___jp_764_:
{
lean_object* v___x_767_; lean_object* v_cache_768_; lean_object* v_zetaDeltaFVarIds_769_; lean_object* v_postponed_770_; lean_object* v_diag_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_779_; 
v___x_767_ = lean_st_ref_take(v___y_729_);
v_cache_768_ = lean_ctor_get(v___x_767_, 1);
v_zetaDeltaFVarIds_769_ = lean_ctor_get(v___x_767_, 2);
v_postponed_770_ = lean_ctor_get(v___x_767_, 3);
v_diag_771_ = lean_ctor_get(v___x_767_, 4);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_779_ == 0)
{
lean_object* v_unused_780_; 
v_unused_780_ = lean_ctor_get(v___x_767_, 0);
lean_dec(v_unused_780_);
v___x_773_ = v___x_767_;
v_isShared_774_ = v_isSharedCheck_779_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_diag_771_);
lean_inc(v_postponed_770_);
lean_inc(v_zetaDeltaFVarIds_769_);
lean_inc(v_cache_768_);
lean_dec(v___x_767_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_779_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v_mctx_766_);
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_mctx_766_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_cache_768_);
lean_ctor_set(v_reuseFailAlloc_778_, 2, v_zetaDeltaFVarIds_769_);
lean_ctor_set(v_reuseFailAlloc_778_, 3, v_postponed_770_);
lean_ctor_set(v_reuseFailAlloc_778_, 4, v_diag_771_);
v___x_776_ = v_reuseFailAlloc_778_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_777_; 
v___x_777_ = lean_st_ref_put(v___y_729_, v___x_776_);
v_a_759_ = v_fst_765_;
goto v___jp_758_;
}
}
}
v___jp_781_:
{
lean_object* v_snd_783_; lean_object* v_fst_784_; lean_object* v_mctx_785_; uint8_t v___x_786_; 
v_snd_783_ = lean_ctor_get(v___y_782_, 1);
lean_inc(v_snd_783_);
v_fst_784_ = lean_ctor_get(v___y_782_, 0);
lean_inc(v_fst_784_);
lean_dec_ref(v___y_782_);
v_mctx_785_ = lean_ctor_get(v_snd_783_, 1);
lean_inc_ref(v_mctx_785_);
lean_dec(v_snd_783_);
v___x_786_ = lean_unbox(v_fst_784_);
lean_dec(v_fst_784_);
v_fst_765_ = v___x_786_;
v_mctx_766_ = v_mctx_785_;
goto v___jp_764_;
}
v___jp_787_:
{
lean_object* v_mctx_790_; lean_object* v___x_791_; lean_object* v_cache_792_; lean_object* v_zetaDeltaFVarIds_793_; lean_object* v_postponed_794_; lean_object* v_diag_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_803_; 
v_mctx_790_ = lean_ctor_get(v_snd_789_, 1);
lean_inc_ref(v_mctx_790_);
lean_dec_ref(v_snd_789_);
v___x_791_ = lean_st_ref_take(v___y_729_);
v_cache_792_ = lean_ctor_get(v___x_791_, 1);
v_zetaDeltaFVarIds_793_ = lean_ctor_get(v___x_791_, 2);
v_postponed_794_ = lean_ctor_get(v___x_791_, 3);
v_diag_795_ = lean_ctor_get(v___x_791_, 4);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_803_ == 0)
{
lean_object* v_unused_804_; 
v_unused_804_ = lean_ctor_get(v___x_791_, 0);
lean_dec(v_unused_804_);
v___x_797_ = v___x_791_;
v_isShared_798_ = v_isSharedCheck_803_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_diag_795_);
lean_inc(v_postponed_794_);
lean_inc(v_zetaDeltaFVarIds_793_);
lean_inc(v_cache_792_);
lean_dec(v___x_791_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_803_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v_mctx_790_);
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_mctx_790_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_cache_792_);
lean_ctor_set(v_reuseFailAlloc_802_, 2, v_zetaDeltaFVarIds_793_);
lean_ctor_set(v_reuseFailAlloc_802_, 3, v_postponed_794_);
lean_ctor_set(v_reuseFailAlloc_802_, 4, v_diag_795_);
v___x_800_ = v_reuseFailAlloc_802_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_801_; 
v___x_801_ = lean_st_ref_put(v___y_729_, v___x_800_);
v_a_759_ = v_fst_788_;
goto v___jp_758_;
}
}
}
v___jp_805_:
{
lean_object* v_fst_807_; lean_object* v_snd_808_; uint8_t v___x_809_; 
v_fst_807_ = lean_ctor_get(v___y_806_, 0);
lean_inc(v_fst_807_);
v_snd_808_ = lean_ctor_get(v___y_806_, 1);
lean_inc(v_snd_808_);
lean_dec_ref(v___y_806_);
v___x_809_ = lean_unbox(v_fst_807_);
lean_dec(v_fst_807_);
v_fst_788_ = v___x_809_;
v_snd_789_ = v_snd_808_;
goto v___jp_787_;
}
v___jp_810_:
{
lean_object* v___x_813_; lean_object* v_cache_814_; lean_object* v_zetaDeltaFVarIds_815_; lean_object* v_postponed_816_; lean_object* v_diag_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_825_; 
v___x_813_ = lean_st_ref_take(v___y_729_);
v_cache_814_ = lean_ctor_get(v___x_813_, 1);
v_zetaDeltaFVarIds_815_ = lean_ctor_get(v___x_813_, 2);
v_postponed_816_ = lean_ctor_get(v___x_813_, 3);
v_diag_817_ = lean_ctor_get(v___x_813_, 4);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_825_ == 0)
{
lean_object* v_unused_826_; 
v_unused_826_ = lean_ctor_get(v___x_813_, 0);
lean_dec(v_unused_826_);
v___x_819_ = v___x_813_;
v_isShared_820_ = v_isSharedCheck_825_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_diag_817_);
lean_inc(v_postponed_816_);
lean_inc(v_zetaDeltaFVarIds_815_);
lean_inc(v_cache_814_);
lean_dec(v___x_813_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_825_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v_mctx_812_);
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_mctx_812_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v_cache_814_);
lean_ctor_set(v_reuseFailAlloc_824_, 2, v_zetaDeltaFVarIds_815_);
lean_ctor_set(v_reuseFailAlloc_824_, 3, v_postponed_816_);
lean_ctor_set(v_reuseFailAlloc_824_, 4, v_diag_817_);
v___x_822_ = v_reuseFailAlloc_824_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_823_; 
v___x_823_ = lean_st_ref_put(v___y_729_, v___x_822_);
v_a_759_ = v_fst_811_;
goto v___jp_758_;
}
}
}
v___jp_827_:
{
lean_object* v_snd_829_; lean_object* v_fst_830_; lean_object* v_mctx_831_; uint8_t v___x_832_; 
v_snd_829_ = lean_ctor_get(v___y_828_, 1);
lean_inc(v_snd_829_);
v_fst_830_ = lean_ctor_get(v___y_828_, 0);
lean_inc(v_fst_830_);
lean_dec_ref(v___y_828_);
v_mctx_831_ = lean_ctor_get(v_snd_829_, 1);
lean_inc_ref(v_mctx_831_);
lean_dec(v_snd_829_);
v___x_832_ = lean_unbox(v_fst_830_);
lean_dec(v_fst_830_);
v_fst_811_ = v___x_832_;
v_mctx_812_ = v_mctx_831_;
goto v___jp_810_;
}
}
}
v___jp_738_:
{
lean_object* v___x_741_; 
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 1, v_a_739_);
lean_ctor_set(v___x_735_, 0, v___x_737_);
v___x_741_ = v___x_735_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_a_739_);
v___x_741_ = v_reuseFailAlloc_745_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
size_t v___x_742_; size_t v___x_743_; 
v___x_742_ = ((size_t)1ULL);
v___x_743_ = lean_usize_add(v_i_727_, v___x_742_);
v_i_727_ = v___x_743_;
v_b_728_ = v___x_741_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_forbidden_723_ = stack[0].m_obj;
uint8_t v_ignoreLetDecls_724_ = stack[1].m_num;
lean_object* v_as_725_ = stack[2].m_obj;
size_t v_sz_726_ = stack[3].m_num;
size_t v_i_727_ = stack[4].m_num;
lean_object* v_b_728_ = stack[5].m_obj;
lean_object* v___y_729_ = stack[6].m_obj;
lean_object* v_res_894_;
v_res_894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(v_forbidden_723_, v_ignoreLetDecls_724_, v_as_725_, v_sz_726_, v_i_727_, v_b_728_, v___y_729_);
stack->m_obj
 = v_res_894_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_forbidden_895_, lean_object* v_ignoreLetDecls_896_, lean_object* v_as_897_, lean_object* v_sz_898_, lean_object* v_i_899_, lean_object* v_b_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_903_; size_t v_sz_boxed_904_; size_t v_i_boxed_905_; lean_object* v_res_906_; 
v_ignoreLetDecls_boxed_903_ = lean_unbox(v_ignoreLetDecls_896_);
v_sz_boxed_904_ = lean_unbox_usize(v_sz_898_);
lean_dec(v_sz_898_);
v_i_boxed_905_ = lean_unbox_usize(v_i_899_);
lean_dec(v_i_899_);
v_res_906_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(v_forbidden_895_, v_ignoreLetDecls_boxed_903_, v_as_897_, v_sz_boxed_904_, v_i_boxed_905_, v_b_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v_as_897_);
lean_dec(v_forbidden_895_);
return v_res_906_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2(lean_object* v_forbidden_907_, uint8_t v_ignoreLetDecls_908_, lean_object* v_as_909_, size_t v_sz_910_, size_t v_i_911_, lean_object* v_b_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
uint8_t v___x_918_; 
v___x_918_ = lean_usize_dec_lt(v_i_911_, v_sz_910_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; 
v___x_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_919_, 0, v_b_912_);
return v___x_919_;
}
else
{
lean_object* v_snd_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_1079_; 
v_snd_920_ = lean_ctor_get(v_b_912_, 1);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_b_912_);
if (v_isSharedCheck_1079_ == 0)
{
lean_object* v_unused_1080_; 
v_unused_1080_ = lean_ctor_get(v_b_912_, 0);
lean_dec(v_unused_1080_);
v___x_922_ = v_b_912_;
v_isShared_923_ = v_isSharedCheck_1079_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_snd_920_);
lean_dec(v_b_912_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_1079_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_924_; lean_object* v_a_926_; lean_object* v_a_933_; 
v___x_924_ = lean_box(0);
v_a_933_ = lean_array_uget_borrowed(v_as_909_, v_i_911_);
if (lean_obj_tag(v_a_933_) == 0)
{
v_a_926_ = v_snd_920_;
goto v___jp_925_;
}
else
{
lean_object* v_val_934_; lean_object* v_fst_935_; lean_object* v_snd_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_1078_; 
v_val_934_ = lean_ctor_get(v_a_933_, 0);
v_fst_935_ = lean_ctor_get(v_snd_920_, 0);
v_snd_936_ = lean_ctor_get(v_snd_920_, 1);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_snd_920_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_938_ = v_snd_920_;
v_isShared_939_ = v_isSharedCheck_1078_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_snd_936_);
lean_inc(v_fst_935_);
lean_dec(v_snd_920_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_1078_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_944_; uint8_t v_a_946_; uint8_t v_fst_952_; lean_object* v_mctx_953_; lean_object* v___y_969_; uint8_t v_fst_975_; lean_object* v_snd_976_; lean_object* v___y_993_; uint8_t v_fst_998_; lean_object* v_mctx_999_; lean_object* v___y_1015_; uint8_t v___x_1020_; 
v___x_944_ = l_Lean_LocalDecl_fvarId(v_val_934_);
v___x_1020_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v___x_944_, v_forbidden_907_);
if (v___x_1020_ == 0)
{
lean_object* v___f_1021_; lean_object* v___y_1023_; lean_object* v___y_1024_; uint8_t v_fst_1025_; lean_object* v_snd_1026_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; uint8_t v___y_1039_; uint8_t v___y_1072_; uint8_t v___x_1074_; 
lean_inc(v_fst_935_);
v___f_1021_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1021_, 0, v_fst_935_);
v___x_1074_ = l_Lean_LocalDecl_isAuxDecl(v_val_934_);
if (v___x_1074_ == 0)
{
uint8_t v___x_1075_; uint8_t v___x_1076_; 
v___x_1075_ = l_Lean_LocalDecl_binderInfo(v_val_934_);
v___x_1076_ = l_Lean_BinderInfo_isInstImplicit(v___x_1075_);
v___y_1072_ = v___x_1076_;
goto v___jp_1071_;
}
else
{
v___y_1072_ = v___x_1074_;
goto v___jp_1071_;
}
v___jp_1022_:
{
if (v_fst_1025_ == 0)
{
uint8_t v___x_1027_; 
v___x_1027_ = l_Lean_Expr_hasFVar(v___y_1023_);
if (v___x_1027_ == 0)
{
uint8_t v___x_1028_; 
v___x_1028_ = l_Lean_Expr_hasMVar(v___y_1023_);
if (v___x_1028_ == 0)
{
lean_dec_ref(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec_ref(v___f_1021_);
v_fst_975_ = v___x_1028_;
v_snd_976_ = v_snd_1026_;
goto v___jp_974_;
}
else
{
lean_object* v___x_1029_; 
v___x_1029_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1021_, v___y_1024_, v___y_1023_, v_snd_1026_);
v___y_993_ = v___x_1029_;
goto v___jp_992_;
}
}
else
{
lean_object* v___x_1030_; 
v___x_1030_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1021_, v___y_1024_, v___y_1023_, v_snd_1026_);
v___y_993_ = v___x_1030_;
goto v___jp_992_;
}
}
else
{
lean_dec_ref(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec_ref(v___f_1021_);
v_fst_975_ = v_fst_1025_;
v_snd_976_ = v_snd_1026_;
goto v___jp_974_;
}
}
v___jp_1031_:
{
lean_object* v_fst_1035_; lean_object* v_snd_1036_; uint8_t v___x_1037_; 
v_fst_1035_ = lean_ctor_get(v___y_1034_, 0);
lean_inc(v_fst_1035_);
v_snd_1036_ = lean_ctor_get(v___y_1034_, 1);
lean_inc(v_snd_1036_);
lean_dec_ref(v___y_1034_);
v___x_1037_ = lean_unbox(v_fst_1035_);
lean_dec(v_fst_1035_);
v___y_1023_ = v___y_1032_;
v___y_1024_ = v___y_1033_;
v_fst_1025_ = v___x_1037_;
v_snd_1026_ = v_snd_1036_;
goto v___jp_1022_;
}
v___jp_1038_:
{
if (v___y_1039_ == 0)
{
lean_object* v___x_1040_; lean_object* v___f_1041_; 
lean_del_object(v___x_938_);
v___x_1040_ = lean_box(v___y_1039_);
v___f_1041_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1041_, 0, v___x_1040_);
if (lean_obj_tag(v_val_934_) == 0)
{
lean_object* v_type_1042_; lean_object* v___x_1043_; lean_object* v_mctx_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; uint8_t v___x_1047_; 
v_type_1042_ = lean_ctor_get(v_val_934_, 3);
v___x_1043_ = lean_st_ref_get(v___y_914_);
v_mctx_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc_ref_n(v_mctx_1044_, 2);
lean_dec(v___x_1043_);
v___x_1045_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
lean_ctor_set(v___x_1046_, 1, v_mctx_1044_);
v___x_1047_ = l_Lean_Expr_hasFVar(v_type_1042_);
if (v___x_1047_ == 0)
{
uint8_t v___x_1048_; 
v___x_1048_ = l_Lean_Expr_hasMVar(v_type_1042_);
if (v___x_1048_ == 0)
{
lean_dec_ref_known(v___x_1046_, 2);
lean_dec_ref(v___f_1041_);
lean_dec_ref(v___f_1021_);
v_fst_998_ = v___x_1048_;
v_mctx_999_ = v_mctx_1044_;
goto v___jp_997_;
}
else
{
lean_object* v___x_1049_; 
lean_dec_ref(v_mctx_1044_);
lean_inc_ref(v_type_1042_);
v___x_1049_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1021_, v___f_1041_, v_type_1042_, v___x_1046_);
v___y_1015_ = v___x_1049_;
goto v___jp_1014_;
}
}
else
{
lean_object* v___x_1050_; 
lean_dec_ref(v_mctx_1044_);
lean_inc_ref(v_type_1042_);
v___x_1050_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1021_, v___f_1041_, v_type_1042_, v___x_1046_);
v___y_1015_ = v___x_1050_;
goto v___jp_1014_;
}
}
else
{
uint8_t v_nondep_1051_; 
v_nondep_1051_ = lean_ctor_get_uint8(v_val_934_, sizeof(void*)*5);
if (v_nondep_1051_ == 0)
{
lean_object* v_type_1052_; lean_object* v_value_1053_; lean_object* v___x_1054_; lean_object* v_mctx_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
v_type_1052_ = lean_ctor_get(v_val_934_, 3);
v_value_1053_ = lean_ctor_get(v_val_934_, 4);
v___x_1054_ = lean_st_ref_get(v___y_914_);
v_mctx_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc_ref(v_mctx_1055_);
lean_dec(v___x_1054_);
v___x_1056_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
lean_ctor_set(v___x_1057_, 1, v_mctx_1055_);
v___x_1058_ = l_Lean_Expr_hasFVar(v_type_1052_);
if (v___x_1058_ == 0)
{
uint8_t v___x_1059_; 
v___x_1059_ = l_Lean_Expr_hasMVar(v_type_1052_);
if (v___x_1059_ == 0)
{
lean_inc_ref(v_value_1053_);
v___y_1023_ = v_value_1053_;
v___y_1024_ = v___f_1041_;
v_fst_1025_ = v___x_1059_;
v_snd_1026_ = v___x_1057_;
goto v___jp_1022_;
}
else
{
lean_object* v___x_1060_; 
lean_inc_ref(v_type_1052_);
lean_inc_ref(v___f_1041_);
lean_inc_ref(v___f_1021_);
v___x_1060_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1021_, v___f_1041_, v_type_1052_, v___x_1057_);
lean_inc_ref(v_value_1053_);
v___y_1032_ = v_value_1053_;
v___y_1033_ = v___f_1041_;
v___y_1034_ = v___x_1060_;
goto v___jp_1031_;
}
}
else
{
lean_object* v___x_1061_; 
lean_inc_ref(v_type_1052_);
lean_inc_ref(v___f_1041_);
lean_inc_ref(v___f_1021_);
v___x_1061_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1021_, v___f_1041_, v_type_1052_, v___x_1057_);
lean_inc_ref(v_value_1053_);
v___y_1032_ = v_value_1053_;
v___y_1033_ = v___f_1041_;
v___y_1034_ = v___x_1061_;
goto v___jp_1031_;
}
}
else
{
lean_object* v_type_1062_; lean_object* v___x_1063_; lean_object* v_mctx_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v_type_1062_ = lean_ctor_get(v_val_934_, 3);
v___x_1063_ = lean_st_ref_get(v___y_914_);
v_mctx_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc_ref_n(v_mctx_1064_, 2);
lean_dec(v___x_1063_);
v___x_1065_ = lean_obj_once(&l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1, &l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once, _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
v___x_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
lean_ctor_set(v___x_1066_, 1, v_mctx_1064_);
v___x_1067_ = l_Lean_Expr_hasFVar(v_type_1062_);
if (v___x_1067_ == 0)
{
uint8_t v___x_1068_; 
v___x_1068_ = l_Lean_Expr_hasMVar(v_type_1062_);
if (v___x_1068_ == 0)
{
lean_dec_ref_known(v___x_1066_, 2);
lean_dec_ref(v___f_1041_);
lean_dec_ref(v___f_1021_);
v_fst_952_ = v___x_1068_;
v_mctx_953_ = v_mctx_1064_;
goto v___jp_951_;
}
else
{
lean_object* v___x_1069_; 
lean_dec_ref(v_mctx_1064_);
lean_inc_ref(v_type_1062_);
v___x_1069_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1021_, v___f_1041_, v_type_1062_, v___x_1066_);
v___y_969_ = v___x_1069_;
goto v___jp_968_;
}
}
else
{
lean_object* v___x_1070_; 
lean_dec_ref(v_mctx_1064_);
lean_inc_ref(v_type_1062_);
v___x_1070_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_1021_, v___f_1041_, v_type_1062_, v___x_1066_);
v___y_969_ = v___x_1070_;
goto v___jp_968_;
}
}
}
}
else
{
lean_dec_ref(v___f_1021_);
lean_dec(v___x_944_);
goto v___jp_940_;
}
}
v___jp_1071_:
{
if (v___y_1072_ == 0)
{
if (v_ignoreLetDecls_908_ == 0)
{
v___y_1039_ = v___x_1020_;
goto v___jp_1038_;
}
else
{
uint8_t v___x_1073_; 
v___x_1073_ = l_Lean_LocalDecl_isLet(v_val_934_, v___x_1020_);
v___y_1039_ = v___x_1073_;
goto v___jp_1038_;
}
}
else
{
lean_dec_ref(v___f_1021_);
lean_dec(v___x_944_);
goto v___jp_940_;
}
}
}
else
{
lean_object* v___x_1077_; 
lean_dec(v___x_944_);
lean_del_object(v___x_938_);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v_fst_935_);
lean_ctor_set(v___x_1077_, 1, v_snd_936_);
v_a_926_ = v___x_1077_;
goto v___jp_925_;
}
v___jp_940_:
{
lean_object* v___x_942_; 
if (v_isShared_939_ == 0)
{
v___x_942_ = v___x_938_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_fst_935_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v_snd_936_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
v_a_926_ = v___x_942_;
goto v___jp_925_;
}
}
v___jp_945_:
{
if (v_a_946_ == 0)
{
lean_object* v___x_947_; 
lean_dec(v___x_944_);
v___x_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_947_, 0, v_fst_935_);
lean_ctor_set(v___x_947_, 1, v_snd_936_);
v_a_926_ = v___x_947_;
goto v___jp_925_;
}
else
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
lean_inc(v___x_944_);
v___x_948_ = l_Lean_FVarIdSet_insert(v_snd_936_, v___x_944_);
v___x_949_ = l_Lean_FVarIdSet_insert(v_fst_935_, v___x_944_);
v___x_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
lean_ctor_set(v___x_950_, 1, v___x_948_);
v_a_926_ = v___x_950_;
goto v___jp_925_;
}
}
v___jp_951_:
{
lean_object* v___x_954_; lean_object* v_cache_955_; lean_object* v_zetaDeltaFVarIds_956_; lean_object* v_postponed_957_; lean_object* v_diag_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_966_; 
v___x_954_ = lean_st_ref_take(v___y_914_);
v_cache_955_ = lean_ctor_get(v___x_954_, 1);
v_zetaDeltaFVarIds_956_ = lean_ctor_get(v___x_954_, 2);
v_postponed_957_ = lean_ctor_get(v___x_954_, 3);
v_diag_958_ = lean_ctor_get(v___x_954_, 4);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_966_ == 0)
{
lean_object* v_unused_967_; 
v_unused_967_ = lean_ctor_get(v___x_954_, 0);
lean_dec(v_unused_967_);
v___x_960_ = v___x_954_;
v_isShared_961_ = v_isSharedCheck_966_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_diag_958_);
lean_inc(v_postponed_957_);
lean_inc(v_zetaDeltaFVarIds_956_);
lean_inc(v_cache_955_);
lean_dec(v___x_954_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_966_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 0, v_mctx_953_);
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_mctx_953_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_cache_955_);
lean_ctor_set(v_reuseFailAlloc_965_, 2, v_zetaDeltaFVarIds_956_);
lean_ctor_set(v_reuseFailAlloc_965_, 3, v_postponed_957_);
lean_ctor_set(v_reuseFailAlloc_965_, 4, v_diag_958_);
v___x_963_ = v_reuseFailAlloc_965_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v___x_964_; 
v___x_964_ = lean_st_ref_put(v___y_914_, v___x_963_);
v_a_946_ = v_fst_952_;
goto v___jp_945_;
}
}
}
v___jp_968_:
{
lean_object* v_snd_970_; lean_object* v_fst_971_; lean_object* v_mctx_972_; uint8_t v___x_973_; 
v_snd_970_ = lean_ctor_get(v___y_969_, 1);
lean_inc(v_snd_970_);
v_fst_971_ = lean_ctor_get(v___y_969_, 0);
lean_inc(v_fst_971_);
lean_dec_ref(v___y_969_);
v_mctx_972_ = lean_ctor_get(v_snd_970_, 1);
lean_inc_ref(v_mctx_972_);
lean_dec(v_snd_970_);
v___x_973_ = lean_unbox(v_fst_971_);
lean_dec(v_fst_971_);
v_fst_952_ = v___x_973_;
v_mctx_953_ = v_mctx_972_;
goto v___jp_951_;
}
v___jp_974_:
{
lean_object* v_mctx_977_; lean_object* v___x_978_; lean_object* v_cache_979_; lean_object* v_zetaDeltaFVarIds_980_; lean_object* v_postponed_981_; lean_object* v_diag_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_990_; 
v_mctx_977_ = lean_ctor_get(v_snd_976_, 1);
lean_inc_ref(v_mctx_977_);
lean_dec_ref(v_snd_976_);
v___x_978_ = lean_st_ref_take(v___y_914_);
v_cache_979_ = lean_ctor_get(v___x_978_, 1);
v_zetaDeltaFVarIds_980_ = lean_ctor_get(v___x_978_, 2);
v_postponed_981_ = lean_ctor_get(v___x_978_, 3);
v_diag_982_ = lean_ctor_get(v___x_978_, 4);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_990_ == 0)
{
lean_object* v_unused_991_; 
v_unused_991_ = lean_ctor_get(v___x_978_, 0);
lean_dec(v_unused_991_);
v___x_984_ = v___x_978_;
v_isShared_985_ = v_isSharedCheck_990_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_diag_982_);
lean_inc(v_postponed_981_);
lean_inc(v_zetaDeltaFVarIds_980_);
lean_inc(v_cache_979_);
lean_dec(v___x_978_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_990_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v_mctx_977_);
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_mctx_977_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_cache_979_);
lean_ctor_set(v_reuseFailAlloc_989_, 2, v_zetaDeltaFVarIds_980_);
lean_ctor_set(v_reuseFailAlloc_989_, 3, v_postponed_981_);
lean_ctor_set(v_reuseFailAlloc_989_, 4, v_diag_982_);
v___x_987_ = v_reuseFailAlloc_989_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
lean_object* v___x_988_; 
v___x_988_ = lean_st_ref_put(v___y_914_, v___x_987_);
v_a_946_ = v_fst_975_;
goto v___jp_945_;
}
}
}
v___jp_992_:
{
lean_object* v_fst_994_; lean_object* v_snd_995_; uint8_t v___x_996_; 
v_fst_994_ = lean_ctor_get(v___y_993_, 0);
lean_inc(v_fst_994_);
v_snd_995_ = lean_ctor_get(v___y_993_, 1);
lean_inc(v_snd_995_);
lean_dec_ref(v___y_993_);
v___x_996_ = lean_unbox(v_fst_994_);
lean_dec(v_fst_994_);
v_fst_975_ = v___x_996_;
v_snd_976_ = v_snd_995_;
goto v___jp_974_;
}
v___jp_997_:
{
lean_object* v___x_1000_; lean_object* v_cache_1001_; lean_object* v_zetaDeltaFVarIds_1002_; lean_object* v_postponed_1003_; lean_object* v_diag_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1012_; 
v___x_1000_ = lean_st_ref_take(v___y_914_);
v_cache_1001_ = lean_ctor_get(v___x_1000_, 1);
v_zetaDeltaFVarIds_1002_ = lean_ctor_get(v___x_1000_, 2);
v_postponed_1003_ = lean_ctor_get(v___x_1000_, 3);
v_diag_1004_ = lean_ctor_get(v___x_1000_, 4);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1012_ == 0)
{
lean_object* v_unused_1013_; 
v_unused_1013_ = lean_ctor_get(v___x_1000_, 0);
lean_dec(v_unused_1013_);
v___x_1006_ = v___x_1000_;
v_isShared_1007_ = v_isSharedCheck_1012_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_diag_1004_);
lean_inc(v_postponed_1003_);
lean_inc(v_zetaDeltaFVarIds_1002_);
lean_inc(v_cache_1001_);
lean_dec(v___x_1000_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1012_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v_mctx_999_);
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_mctx_999_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_cache_1001_);
lean_ctor_set(v_reuseFailAlloc_1011_, 2, v_zetaDeltaFVarIds_1002_);
lean_ctor_set(v_reuseFailAlloc_1011_, 3, v_postponed_1003_);
lean_ctor_set(v_reuseFailAlloc_1011_, 4, v_diag_1004_);
v___x_1009_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
lean_object* v___x_1010_; 
v___x_1010_ = lean_st_ref_put(v___y_914_, v___x_1009_);
v_a_946_ = v_fst_998_;
goto v___jp_945_;
}
}
}
v___jp_1014_:
{
lean_object* v_snd_1016_; lean_object* v_fst_1017_; lean_object* v_mctx_1018_; uint8_t v___x_1019_; 
v_snd_1016_ = lean_ctor_get(v___y_1015_, 1);
lean_inc(v_snd_1016_);
v_fst_1017_ = lean_ctor_get(v___y_1015_, 0);
lean_inc(v_fst_1017_);
lean_dec_ref(v___y_1015_);
v_mctx_1018_ = lean_ctor_get(v_snd_1016_, 1);
lean_inc_ref(v_mctx_1018_);
lean_dec(v_snd_1016_);
v___x_1019_ = lean_unbox(v_fst_1017_);
lean_dec(v_fst_1017_);
v_fst_998_ = v___x_1019_;
v_mctx_999_ = v_mctx_1018_;
goto v___jp_997_;
}
}
}
v___jp_925_:
{
lean_object* v___x_928_; 
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 1, v_a_926_);
lean_ctor_set(v___x_922_, 0, v___x_924_);
v___x_928_ = v___x_922_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_a_926_);
v___x_928_ = v_reuseFailAlloc_932_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
size_t v___x_929_; size_t v___x_930_; lean_object* v___x_931_; 
v___x_929_ = ((size_t)1ULL);
v___x_930_ = lean_usize_add(v_i_911_, v___x_929_);
v___x_931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(v_forbidden_907_, v_ignoreLetDecls_908_, v_as_909_, v_sz_910_, v___x_930_, v___x_928_, v___y_914_);
return v___x_931_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_forbidden_907_ = stack[0].m_obj;
uint8_t v_ignoreLetDecls_908_ = stack[1].m_num;
lean_object* v_as_909_ = stack[2].m_obj;
size_t v_sz_910_ = stack[3].m_num;
size_t v_i_911_ = stack[4].m_num;
lean_object* v_b_912_ = stack[5].m_obj;
lean_object* v___y_913_ = stack[6].m_obj;
lean_object* v___y_914_ = stack[7].m_obj;
lean_object* v___y_915_ = stack[8].m_obj;
lean_object* v___y_916_ = stack[9].m_obj;
lean_object* v_res_1081_;
v_res_1081_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2(v_forbidden_907_, v_ignoreLetDecls_908_, v_as_909_, v_sz_910_, v_i_911_, v_b_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
stack->m_obj
 = v_res_1081_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2___boxed(lean_object* v_forbidden_1082_, lean_object* v_ignoreLetDecls_1083_, lean_object* v_as_1084_, lean_object* v_sz_1085_, lean_object* v_i_1086_, lean_object* v_b_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1093_; size_t v_sz_boxed_1094_; size_t v_i_boxed_1095_; lean_object* v_res_1096_; 
v_ignoreLetDecls_boxed_1093_ = lean_unbox(v_ignoreLetDecls_1083_);
v_sz_boxed_1094_ = lean_unbox_usize(v_sz_1085_);
lean_dec(v_sz_1085_);
v_i_boxed_1095_ = lean_unbox_usize(v_i_1086_);
lean_dec(v_i_1086_);
v_res_1096_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2(v_forbidden_1082_, v_ignoreLetDecls_boxed_1093_, v_as_1084_, v_sz_boxed_1094_, v_i_boxed_1095_, v_b_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec_ref(v_as_1084_);
lean_dec(v_forbidden_1082_);
return v_res_1096_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(lean_object* v_init_1097_, lean_object* v_forbidden_1098_, uint8_t v_ignoreLetDecls_1099_, lean_object* v_n_1100_, lean_object* v_b_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
if (lean_obj_tag(v_n_1100_) == 0)
{
lean_object* v_cs_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; size_t v_sz_1110_; size_t v___x_1111_; lean_object* v___x_1112_; 
v_cs_1107_ = lean_ctor_get(v_n_1100_, 0);
v___x_1108_ = lean_box(0);
v___x_1109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
lean_ctor_set(v___x_1109_, 1, v_b_1101_);
v_sz_1110_ = lean_array_size(v_cs_1107_);
v___x_1111_ = ((size_t)0ULL);
v___x_1112_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(v_init_1097_, v_forbidden_1098_, v_ignoreLetDecls_1099_, v_cs_1107_, v_sz_1110_, v___x_1111_, v___x_1109_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1127_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1115_ = v___x_1112_;
v_isShared_1116_ = v_isSharedCheck_1127_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1112_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1127_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v_fst_1117_; 
v_fst_1117_ = lean_ctor_get(v_a_1113_, 0);
if (lean_obj_tag(v_fst_1117_) == 0)
{
lean_object* v_snd_1118_; lean_object* v___x_1119_; lean_object* v___x_1121_; 
v_snd_1118_ = lean_ctor_get(v_a_1113_, 1);
lean_inc(v_snd_1118_);
lean_dec(v_a_1113_);
v___x_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1119_, 0, v_snd_1118_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v___x_1119_);
v___x_1121_ = v___x_1115_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
else
{
lean_object* v_val_1123_; lean_object* v___x_1125_; 
lean_inc_ref(v_fst_1117_);
lean_dec(v_a_1113_);
v_val_1123_ = lean_ctor_get(v_fst_1117_, 0);
lean_inc(v_val_1123_);
lean_dec_ref_known(v_fst_1117_, 1);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v_val_1123_);
v___x_1125_ = v___x_1115_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_val_1123_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
v_a_1128_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1112_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1112_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
else
{
lean_object* v_vs_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; size_t v_sz_1139_; size_t v___x_1140_; lean_object* v___x_1141_; 
v_vs_1136_ = lean_ctor_get(v_n_1100_, 0);
v___x_1137_ = lean_box(0);
v___x_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
lean_ctor_set(v___x_1138_, 1, v_b_1101_);
v_sz_1139_ = lean_array_size(v_vs_1136_);
v___x_1140_ = ((size_t)0ULL);
v___x_1141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2(v_forbidden_1098_, v_ignoreLetDecls_1099_, v_vs_1136_, v_sz_1139_, v___x_1140_, v___x_1138_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1156_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1144_ = v___x_1141_;
v_isShared_1145_ = v_isSharedCheck_1156_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1141_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1156_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v_fst_1146_; 
v_fst_1146_ = lean_ctor_get(v_a_1142_, 0);
if (lean_obj_tag(v_fst_1146_) == 0)
{
lean_object* v_snd_1147_; lean_object* v___x_1148_; lean_object* v___x_1150_; 
v_snd_1147_ = lean_ctor_get(v_a_1142_, 1);
lean_inc(v_snd_1147_);
lean_dec(v_a_1142_);
v___x_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1148_, 0, v_snd_1147_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v___x_1148_);
v___x_1150_ = v___x_1144_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
else
{
lean_object* v_val_1152_; lean_object* v___x_1154_; 
lean_inc_ref(v_fst_1146_);
lean_dec(v_a_1142_);
v_val_1152_ = lean_ctor_get(v_fst_1146_, 0);
lean_inc(v_val_1152_);
lean_dec_ref_known(v_fst_1146_, 1);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v_val_1152_);
v___x_1154_ = v___x_1144_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_val_1152_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
v_a_1157_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1141_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1141_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1097_ = stack[0].m_obj;
lean_object* v_forbidden_1098_ = stack[1].m_obj;
uint8_t v_ignoreLetDecls_1099_ = stack[2].m_num;
lean_object* v_n_1100_ = stack[3].m_obj;
lean_object* v_b_1101_ = stack[4].m_obj;
lean_object* v___y_1102_ = stack[5].m_obj;
lean_object* v___y_1103_ = stack[6].m_obj;
lean_object* v___y_1104_ = stack[7].m_obj;
lean_object* v___y_1105_ = stack[8].m_obj;
lean_object* v_res_1165_;
v_res_1165_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(v_init_1097_, v_forbidden_1098_, v_ignoreLetDecls_1099_, v_n_1100_, v_b_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
stack->m_obj
 = v_res_1165_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(lean_object* v_init_1166_, lean_object* v_forbidden_1167_, uint8_t v_ignoreLetDecls_1168_, lean_object* v_as_1169_, size_t v_sz_1170_, size_t v_i_1171_, lean_object* v_b_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
uint8_t v___x_1178_; 
v___x_1178_ = lean_usize_dec_lt(v_i_1171_, v_sz_1170_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1179_, 0, v_b_1172_);
return v___x_1179_;
}
else
{
lean_object* v_snd_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1214_; 
v_snd_1180_ = lean_ctor_get(v_b_1172_, 1);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_b_1172_);
if (v_isSharedCheck_1214_ == 0)
{
lean_object* v_unused_1215_; 
v_unused_1215_ = lean_ctor_get(v_b_1172_, 0);
lean_dec(v_unused_1215_);
v___x_1182_ = v_b_1172_;
v_isShared_1183_ = v_isSharedCheck_1214_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_snd_1180_);
lean_dec(v_b_1172_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1214_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; lean_object* v_a_1185_; lean_object* v___x_1186_; 
v___x_1184_ = lean_box(0);
v_a_1185_ = lean_array_uget_borrowed(v_as_1169_, v_i_1171_);
lean_inc(v_snd_1180_);
v___x_1186_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(v_init_1166_, v_forbidden_1167_, v_ignoreLetDecls_1168_, v_a_1185_, v_snd_1180_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1205_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1189_ = v___x_1186_;
v_isShared_1190_ = v_isSharedCheck_1205_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1186_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1205_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
if (lean_obj_tag(v_a_1187_) == 0)
{
lean_object* v___x_1191_; lean_object* v___x_1193_; 
v___x_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1191_, 0, v_a_1187_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v___x_1191_);
v___x_1193_ = v___x_1182_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1191_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_snd_1180_);
v___x_1193_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v___x_1195_; 
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v___x_1193_);
v___x_1195_ = v___x_1189_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1200_; 
lean_del_object(v___x_1189_);
lean_dec(v_snd_1180_);
v_a_1198_ = lean_ctor_get(v_a_1187_, 0);
lean_inc(v_a_1198_);
lean_dec_ref_known(v_a_1187_, 1);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 1, v_a_1198_);
lean_ctor_set(v___x_1182_, 0, v___x_1184_);
v___x_1200_ = v___x_1182_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1184_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_a_1198_);
v___x_1200_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
size_t v___x_1201_; size_t v___x_1202_; 
v___x_1201_ = ((size_t)1ULL);
v___x_1202_ = lean_usize_add(v_i_1171_, v___x_1201_);
v_i_1171_ = v___x_1202_;
v_b_1172_ = v___x_1200_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
lean_del_object(v___x_1182_);
lean_dec(v_snd_1180_);
v_a_1206_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1186_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1186_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1166_ = stack[0].m_obj;
lean_object* v_forbidden_1167_ = stack[1].m_obj;
uint8_t v_ignoreLetDecls_1168_ = stack[2].m_num;
lean_object* v_as_1169_ = stack[3].m_obj;
size_t v_sz_1170_ = stack[4].m_num;
size_t v_i_1171_ = stack[5].m_num;
lean_object* v_b_1172_ = stack[6].m_obj;
lean_object* v___y_1173_ = stack[7].m_obj;
lean_object* v___y_1174_ = stack[8].m_obj;
lean_object* v___y_1175_ = stack[9].m_obj;
lean_object* v___y_1176_ = stack[10].m_obj;
lean_object* v_res_1216_;
v_res_1216_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(v_init_1166_, v_forbidden_1167_, v_ignoreLetDecls_1168_, v_as_1169_, v_sz_1170_, v_i_1171_, v_b_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
stack->m_obj
 = v_res_1216_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1___boxed(lean_object* v_init_1217_, lean_object* v_forbidden_1218_, lean_object* v_ignoreLetDecls_1219_, lean_object* v_as_1220_, lean_object* v_sz_1221_, lean_object* v_i_1222_, lean_object* v_b_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1229_; size_t v_sz_boxed_1230_; size_t v_i_boxed_1231_; lean_object* v_res_1232_; 
v_ignoreLetDecls_boxed_1229_ = lean_unbox(v_ignoreLetDecls_1219_);
v_sz_boxed_1230_ = lean_unbox_usize(v_sz_1221_);
lean_dec(v_sz_1221_);
v_i_boxed_1231_ = lean_unbox_usize(v_i_1222_);
lean_dec(v_i_1222_);
v_res_1232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(v_init_1217_, v_forbidden_1218_, v_ignoreLetDecls_boxed_1229_, v_as_1220_, v_sz_boxed_1230_, v_i_boxed_1231_, v_b_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec_ref(v_as_1220_);
lean_dec(v_forbidden_1218_);
lean_dec_ref(v_init_1217_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0___boxed(lean_object* v_init_1233_, lean_object* v_forbidden_1234_, lean_object* v_ignoreLetDecls_1235_, lean_object* v_n_1236_, lean_object* v_b_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1243_; lean_object* v_res_1244_; 
v_ignoreLetDecls_boxed_1243_ = lean_unbox(v_ignoreLetDecls_1235_);
v_res_1244_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(v_init_1233_, v_forbidden_1234_, v_ignoreLetDecls_boxed_1243_, v_n_1236_, v_b_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec_ref(v_n_1236_);
lean_dec(v_forbidden_1234_);
lean_dec_ref(v_init_1233_);
return v_res_1244_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0(lean_object* v_forbidden_1245_, uint8_t v_ignoreLetDecls_1246_, lean_object* v_t_1247_, lean_object* v_init_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v_root_1254_; lean_object* v_tail_1255_; lean_object* v___x_1256_; 
v_root_1254_ = lean_ctor_get(v_t_1247_, 0);
v_tail_1255_ = lean_ctor_get(v_t_1247_, 1);
lean_inc_ref(v_init_1248_);
v___x_1256_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(v_init_1248_, v_forbidden_1245_, v_ignoreLetDecls_1246_, v_root_1254_, v_init_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
lean_dec_ref(v_init_1248_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1293_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1259_ = v___x_1256_;
v_isShared_1260_ = v_isSharedCheck_1293_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1256_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1293_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
if (lean_obj_tag(v_a_1257_) == 0)
{
lean_object* v_a_1261_; lean_object* v___x_1263_; 
v_a_1261_ = lean_ctor_get(v_a_1257_, 0);
lean_inc(v_a_1261_);
lean_dec_ref_known(v_a_1257_, 1);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v_a_1261_);
v___x_1263_ = v___x_1259_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1261_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; size_t v_sz_1268_; size_t v___x_1269_; lean_object* v___x_1270_; 
lean_del_object(v___x_1259_);
v_a_1265_ = lean_ctor_get(v_a_1257_, 0);
lean_inc(v_a_1265_);
lean_dec_ref_known(v_a_1257_, 1);
v___x_1266_ = lean_box(0);
v___x_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
lean_ctor_set(v___x_1267_, 1, v_a_1265_);
v_sz_1268_ = lean_array_size(v_tail_1255_);
v___x_1269_ = ((size_t)0ULL);
v___x_1270_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1(v_forbidden_1245_, v_ignoreLetDecls_1246_, v_tail_1255_, v_sz_1268_, v___x_1269_, v___x_1267_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1284_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1273_ = v___x_1270_;
v_isShared_1274_ = v_isSharedCheck_1284_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1270_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1284_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v_fst_1275_; 
v_fst_1275_ = lean_ctor_get(v_a_1271_, 0);
if (lean_obj_tag(v_fst_1275_) == 0)
{
lean_object* v_snd_1276_; lean_object* v___x_1278_; 
v_snd_1276_ = lean_ctor_get(v_a_1271_, 1);
lean_inc(v_snd_1276_);
lean_dec(v_a_1271_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v_snd_1276_);
v___x_1278_ = v___x_1273_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_snd_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
else
{
lean_object* v_val_1280_; lean_object* v___x_1282_; 
lean_inc_ref(v_fst_1275_);
lean_dec(v_a_1271_);
v_val_1280_ = lean_ctor_get(v_fst_1275_, 0);
lean_inc(v_val_1280_);
lean_dec_ref_known(v_fst_1275_, 1);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v_val_1280_);
v___x_1282_ = v___x_1273_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_val_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
v_a_1285_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1270_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1270_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
v_a_1294_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1256_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1256_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_forbidden_1245_ = stack[0].m_obj;
uint8_t v_ignoreLetDecls_1246_ = stack[1].m_num;
lean_object* v_t_1247_ = stack[2].m_obj;
lean_object* v_init_1248_ = stack[3].m_obj;
lean_object* v___y_1249_ = stack[4].m_obj;
lean_object* v___y_1250_ = stack[5].m_obj;
lean_object* v___y_1251_ = stack[6].m_obj;
lean_object* v___y_1252_ = stack[7].m_obj;
lean_object* v_res_1302_;
v_res_1302_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0(v_forbidden_1245_, v_ignoreLetDecls_1246_, v_t_1247_, v_init_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
stack->m_obj
 = v_res_1302_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0___boxed(lean_object* v_forbidden_1303_, lean_object* v_ignoreLetDecls_1304_, lean_object* v_t_1305_, lean_object* v_init_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1312_; lean_object* v_res_1313_; 
v_ignoreLetDecls_boxed_1312_ = lean_unbox(v_ignoreLetDecls_1304_);
v_res_1313_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0(v_forbidden_1303_, v_ignoreLetDecls_boxed_1312_, v_t_1305_, v_init_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec_ref(v_t_1305_);
lean_dec(v_forbidden_1303_);
return v_res_1313_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(lean_object* v_as_1314_, size_t v_i_1315_, size_t v_stop_1316_, lean_object* v_b_1317_){
_start:
{
lean_object* v___y_1319_; uint8_t v___x_1323_; 
v___x_1323_ = lean_usize_dec_eq(v_i_1315_, v_stop_1316_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; uint8_t v___x_1325_; 
v___x_1324_ = lean_array_uget_borrowed(v_as_1314_, v_i_1315_);
v___x_1325_ = l_Lean_Expr_isFVar(v___x_1324_);
if (v___x_1325_ == 0)
{
v___y_1319_ = v_b_1317_;
goto v___jp_1318_;
}
else
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = l_Lean_Expr_fvarId_x21(v___x_1324_);
v___x_1327_ = l_Lean_FVarIdSet_insert(v_b_1317_, v___x_1326_);
v___y_1319_ = v___x_1327_;
goto v___jp_1318_;
}
}
else
{
return v_b_1317_;
}
v___jp_1318_:
{
size_t v___x_1320_; size_t v___x_1321_; 
v___x_1320_ = ((size_t)1ULL);
v___x_1321_ = lean_usize_add(v_i_1315_, v___x_1320_);
v_i_1315_ = v___x_1321_;
v_b_1317_ = v___y_1319_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1314_ = stack[0].m_obj;
size_t v_i_1315_ = stack[1].m_num;
size_t v_stop_1316_ = stack[2].m_num;
lean_object* v_b_1317_ = stack[3].m_obj;
lean_object* v_res_1328_;
v_res_1328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(v_as_1314_, v_i_1315_, v_stop_1316_, v_b_1317_);
stack->m_obj
 = v_res_1328_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1___boxed(lean_object* v_as_1329_, lean_object* v_i_1330_, lean_object* v_stop_1331_, lean_object* v_b_1332_){
_start:
{
size_t v_i_boxed_1333_; size_t v_stop_boxed_1334_; lean_object* v_res_1335_; 
v_i_boxed_1333_ = lean_unbox_usize(v_i_1330_);
lean_dec(v_i_1330_);
v_stop_boxed_1334_ = lean_unbox_usize(v_stop_1331_);
lean_dec(v_stop_1331_);
v_res_1335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(v_as_1329_, v_i_boxed_1333_, v_stop_boxed_1334_, v_b_1332_);
lean_dec_ref(v_as_1329_);
return v_res_1335_;
}
}
lean_object* l_Lean_Meta_getFVarSetToGeneralize(lean_object* v_targets_1336_, lean_object* v_forbidden_1337_, uint8_t v_ignoreLetDecls_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_){
_start:
{
lean_object* v_r_1344_; lean_object* v___y_1346_; lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; 
v_r_1344_ = lean_box(1);
v___x_1368_ = lean_unsigned_to_nat(0u);
v___x_1369_ = lean_array_get_size(v_targets_1336_);
v___x_1370_ = lean_nat_dec_lt(v___x_1368_, v___x_1369_);
if (v___x_1370_ == 0)
{
v___y_1346_ = v_r_1344_;
goto v___jp_1345_;
}
else
{
uint8_t v___x_1371_; 
v___x_1371_ = lean_nat_dec_le(v___x_1369_, v___x_1369_);
if (v___x_1371_ == 0)
{
if (v___x_1370_ == 0)
{
v___y_1346_ = v_r_1344_;
goto v___jp_1345_;
}
else
{
size_t v___x_1372_; size_t v___x_1373_; lean_object* v___x_1374_; 
v___x_1372_ = ((size_t)0ULL);
v___x_1373_ = lean_usize_of_nat(v___x_1369_);
v___x_1374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(v_targets_1336_, v___x_1372_, v___x_1373_, v_r_1344_);
v___y_1346_ = v___x_1374_;
goto v___jp_1345_;
}
}
else
{
size_t v___x_1375_; size_t v___x_1376_; lean_object* v___x_1377_; 
v___x_1375_ = ((size_t)0ULL);
v___x_1376_ = lean_usize_of_nat(v___x_1369_);
v___x_1377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(v_targets_1336_, v___x_1375_, v___x_1376_, v_r_1344_);
v___y_1346_ = v___x_1377_;
goto v___jp_1345_;
}
}
v___jp_1345_:
{
lean_object* v_lctx_1347_; lean_object* v_decls_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v_lctx_1347_ = lean_ctor_get(v_a_1339_, 2);
v_decls_1348_ = lean_ctor_get(v_lctx_1347_, 1);
v___x_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___y_1346_);
lean_ctor_set(v___x_1349_, 1, v_r_1344_);
v___x_1350_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0(v_forbidden_1337_, v_ignoreLetDecls_1338_, v_decls_1348_, v___x_1349_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1359_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1353_ = v___x_1350_;
v_isShared_1354_ = v_isSharedCheck_1359_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1350_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1359_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v_snd_1355_; lean_object* v___x_1357_; 
v_snd_1355_ = lean_ctor_get(v_a_1351_, 1);
lean_inc(v_snd_1355_);
lean_dec(v_a_1351_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 0, v_snd_1355_);
v___x_1357_ = v___x_1353_;
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
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
v_a_1360_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1350_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1350_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_getFVarSetToGeneralize_0interp(lean_interpreter_value* stack)
{
lean_object* v_targets_1336_ = stack[0].m_obj;
lean_object* v_forbidden_1337_ = stack[1].m_obj;
uint8_t v_ignoreLetDecls_1338_ = stack[2].m_num;
lean_object* v_a_1339_ = stack[3].m_obj;
lean_object* v_a_1340_ = stack[4].m_obj;
lean_object* v_a_1341_ = stack[5].m_obj;
lean_object* v_a_1342_ = stack[6].m_obj;
lean_object* v_res_1378_;
v_res_1378_ = l_Lean_Meta_getFVarSetToGeneralize(v_targets_1336_, v_forbidden_1337_, v_ignoreLetDecls_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_);
stack->m_obj
 = v_res_1378_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize___boxed(lean_object* v_targets_1379_, lean_object* v_forbidden_1380_, lean_object* v_ignoreLetDecls_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1387_; lean_object* v_res_1388_; 
v_ignoreLetDecls_boxed_1387_ = lean_unbox(v_ignoreLetDecls_1381_);
v_res_1388_ = l_Lean_Meta_getFVarSetToGeneralize(v_targets_1379_, v_forbidden_1380_, v_ignoreLetDecls_boxed_1387_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
lean_dec(v_forbidden_1380_);
lean_dec_ref(v_targets_1379_);
return v_res_1388_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4(lean_object* v_forbidden_1389_, uint8_t v_ignoreLetDecls_1390_, lean_object* v_as_1391_, size_t v_sz_1392_, size_t v_i_1393_, lean_object* v_b_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(v_forbidden_1389_, v_ignoreLetDecls_1390_, v_as_1391_, v_sz_1392_, v_i_1393_, v_b_1394_, v___y_1396_);
return v___x_1400_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_forbidden_1389_ = stack[0].m_obj;
uint8_t v_ignoreLetDecls_1390_ = stack[1].m_num;
lean_object* v_as_1391_ = stack[2].m_obj;
size_t v_sz_1392_ = stack[3].m_num;
size_t v_i_1393_ = stack[4].m_num;
lean_object* v_b_1394_ = stack[5].m_obj;
lean_object* v___y_1395_ = stack[6].m_obj;
lean_object* v___y_1396_ = stack[7].m_obj;
lean_object* v___y_1397_ = stack[8].m_obj;
lean_object* v___y_1398_ = stack[9].m_obj;
lean_object* v_res_1401_;
v_res_1401_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4(v_forbidden_1389_, v_ignoreLetDecls_1390_, v_as_1391_, v_sz_1392_, v_i_1393_, v_b_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
stack->m_obj
 = v_res_1401_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___boxed(lean_object* v_forbidden_1402_, lean_object* v_ignoreLetDecls_1403_, lean_object* v_as_1404_, lean_object* v_sz_1405_, lean_object* v_i_1406_, lean_object* v_b_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1413_; size_t v_sz_boxed_1414_; size_t v_i_boxed_1415_; lean_object* v_res_1416_; 
v_ignoreLetDecls_boxed_1413_ = lean_unbox(v_ignoreLetDecls_1403_);
v_sz_boxed_1414_ = lean_unbox_usize(v_sz_1405_);
lean_dec(v_sz_1405_);
v_i_boxed_1415_ = lean_unbox_usize(v_i_1406_);
lean_dec(v_i_1406_);
v_res_1416_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4(v_forbidden_1402_, v_ignoreLetDecls_boxed_1413_, v_as_1404_, v_sz_boxed_1414_, v_i_boxed_1415_, v_b_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec_ref(v_as_1404_);
lean_dec(v_forbidden_1402_);
return v_res_1416_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4(lean_object* v_forbidden_1417_, uint8_t v_ignoreLetDecls_1418_, lean_object* v_as_1419_, size_t v_sz_1420_, size_t v_i_1421_, lean_object* v_b_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(v_forbidden_1417_, v_ignoreLetDecls_1418_, v_as_1419_, v_sz_1420_, v_i_1421_, v_b_1422_, v___y_1424_);
return v___x_1428_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_forbidden_1417_ = stack[0].m_obj;
uint8_t v_ignoreLetDecls_1418_ = stack[1].m_num;
lean_object* v_as_1419_ = stack[2].m_obj;
size_t v_sz_1420_ = stack[3].m_num;
size_t v_i_1421_ = stack[4].m_num;
lean_object* v_b_1422_ = stack[5].m_obj;
lean_object* v___y_1423_ = stack[6].m_obj;
lean_object* v___y_1424_ = stack[7].m_obj;
lean_object* v___y_1425_ = stack[8].m_obj;
lean_object* v___y_1426_ = stack[9].m_obj;
lean_object* v_res_1429_;
v_res_1429_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4(v_forbidden_1417_, v_ignoreLetDecls_1418_, v_as_1419_, v_sz_1420_, v_i_1421_, v_b_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
stack->m_obj
 = v_res_1429_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_forbidden_1430_, lean_object* v_ignoreLetDecls_1431_, lean_object* v_as_1432_, lean_object* v_sz_1433_, lean_object* v_i_1434_, lean_object* v_b_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1441_; size_t v_sz_boxed_1442_; size_t v_i_boxed_1443_; lean_object* v_res_1444_; 
v_ignoreLetDecls_boxed_1441_ = lean_unbox(v_ignoreLetDecls_1431_);
v_sz_boxed_1442_ = lean_unbox_usize(v_sz_1433_);
lean_dec(v_sz_1433_);
v_i_boxed_1443_ = lean_unbox_usize(v_i_1434_);
lean_dec(v_i_1434_);
v_res_1444_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4(v_forbidden_1430_, v_ignoreLetDecls_boxed_1441_, v_as_1432_, v_sz_boxed_1442_, v_i_boxed_1443_, v_b_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec_ref(v_as_1432_);
lean_dec(v_forbidden_1430_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(lean_object* v_init_1445_, lean_object* v_x_1446_){
_start:
{
if (lean_obj_tag(v_x_1446_) == 0)
{
lean_object* v_k_1447_; lean_object* v_l_1448_; lean_object* v_r_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v_k_1447_ = lean_ctor_get(v_x_1446_, 1);
lean_inc(v_k_1447_);
v_l_1448_ = lean_ctor_get(v_x_1446_, 3);
lean_inc(v_l_1448_);
v_r_1449_ = lean_ctor_get(v_x_1446_, 4);
lean_inc(v_r_1449_);
lean_dec_ref_known(v_x_1446_, 5);
v___x_1450_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(v_init_1445_, v_l_1448_);
v___x_1451_ = lean_array_push(v___x_1450_, v_k_1447_);
v_init_1445_ = v___x_1451_;
v_x_1446_ = v_r_1449_;
goto _start;
}
else
{
return v_init_1445_;
}
}
}
lean_object* l_Lean_Meta_getFVarsToGeneralize(lean_object* v_targets_1453_, lean_object* v_forbidden_1454_, uint8_t v_ignoreLetDecls_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l_Lean_Meta_mkGeneralizationForbiddenSet(v_targets_1453_, v_forbidden_1454_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v___x_1463_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_a_1462_);
lean_dec_ref_known(v___x_1461_, 1);
v___x_1463_ = l_Lean_Meta_getFVarSetToGeneralize(v_targets_1453_, v_a_1462_, v_ignoreLetDecls_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_);
lean_dec(v_a_1462_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___y_1466_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_a_1464_);
lean_dec_ref_known(v___x_1463_, 1);
if (lean_obj_tag(v_a_1464_) == 0)
{
lean_object* v_size_1470_; 
v_size_1470_ = lean_ctor_get(v_a_1464_, 0);
lean_inc(v_size_1470_);
v___y_1466_ = v_size_1470_;
goto v___jp_1465_;
}
else
{
lean_object* v___x_1471_; 
v___x_1471_ = lean_unsigned_to_nat(0u);
v___y_1466_ = v___x_1471_;
goto v___jp_1465_;
}
v___jp_1465_:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1467_ = lean_mk_empty_array_with_capacity(v___y_1466_);
lean_dec(v___y_1466_);
v___x_1468_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(v___x_1467_, v_a_1464_);
v___x_1469_ = l_Lean_Meta_sortFVarIds___redArg(v___x_1468_, v_a_1456_);
return v___x_1469_;
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
v_a_1472_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1463_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1463_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
v_a_1480_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1461_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1461_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_getFVarsToGeneralize_0interp(lean_interpreter_value* stack)
{
lean_object* v_targets_1453_ = stack[0].m_obj;
lean_object* v_forbidden_1454_ = stack[1].m_obj;
uint8_t v_ignoreLetDecls_1455_ = stack[2].m_num;
lean_object* v_a_1456_ = stack[3].m_obj;
lean_object* v_a_1457_ = stack[4].m_obj;
lean_object* v_a_1458_ = stack[5].m_obj;
lean_object* v_a_1459_ = stack[6].m_obj;
lean_object* v_res_1488_;
v_res_1488_ = l_Lean_Meta_getFVarsToGeneralize(v_targets_1453_, v_forbidden_1454_, v_ignoreLetDecls_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_);
stack->m_obj
 = v_res_1488_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize___boxed(lean_object* v_targets_1489_, lean_object* v_forbidden_1490_, lean_object* v_ignoreLetDecls_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_){
_start:
{
uint8_t v_ignoreLetDecls_boxed_1497_; lean_object* v_res_1498_; 
v_ignoreLetDecls_boxed_1497_ = lean_unbox(v_ignoreLetDecls_1491_);
v_res_1498_ = l_Lean_Meta_getFVarsToGeneralize(v_targets_1489_, v_forbidden_1490_, v_ignoreLetDecls_boxed_1497_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
lean_dec(v_a_1495_);
lean_dec_ref(v_a_1494_);
lean_dec(v_a_1493_);
lean_dec_ref(v_a_1492_);
lean_dec_ref(v_targets_1489_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0(lean_object* v_init_1499_, lean_object* v_t_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(v_init_1499_, v_t_1500_);
return v___x_1501_;
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
