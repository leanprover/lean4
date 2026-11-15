// Lean compiler output
// Module: Lake.Build.Index
// Imports: public import Lake.Build.Fetch import Lake.Config.Monad import Lake.Build.Topological import Lake.Util.StoreInsts
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
lean_object* lean_st_ref_take(lean_object*);
uint8_t l_Lake_BuildKey_quickCmp(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_Lake_instDecidableEqBuildKey_decEq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_BuildInfo_key(lean_object*);
lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_io_basemutex_lock(lean_object*);
lean_object* lean_io_basemutex_unlock(lean_object*);
lean_object* l_Lake_BuildKey_toString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_FacetConfigMap_get_x3f(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lake_buildCycleError(lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__0 = (const lean_object*)&l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__0_value;
static const lean_string_object l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__1 = (const lean_object*)&l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__1_value;
static const lean_string_object l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "<nil>"};
static const lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__2 = (const lean_object*)&l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__2_value;
static lean_once_cell_t l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__3;
static const lean_string_object l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "invalid target '"};
static const lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__4 = (const lean_object*)&l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__4_value;
static const lean_string_object l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "': target not found in package"};
static const lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__5 = (const lean_object*)&l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__5_value;
static const lean_string_object l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "': input target is of kind '"};
static const lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__6 = (const lean_object*)&l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__6_value;
static const lean_string_object l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "', but facet expects '"};
static const lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__7 = (const lean_object*)&l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__7_value;
static const lean_string_object l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__8 = (const lean_object*)&l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__8_value;
static const lean_string_object l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "': unknown facet '"};
static const lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__9 = (const lean_object*)&l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recFetchWithIndex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recFetchWithIndex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_FetchT_run___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Index_0__Lake_recFetchWithIndex___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_FetchT_run___redArg___closed__0 = (const lean_object*)&l_Lake_FetchT_run___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_FetchT_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_FetchT_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_FetchT_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_FetchT_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(lean_object* v_mutex_1_, lean_object* v_k_2_){
_start:
{
lean_object* v_ref_4_; lean_object* v_mutex_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v_ref_4_ = lean_ctor_get(v_mutex_1_, 0);
lean_inc(v_ref_4_);
v_mutex_5_ = lean_ctor_get(v_mutex_1_, 1);
lean_inc(v_mutex_5_);
lean_dec_ref(v_mutex_1_);
v___x_6_ = lean_io_basemutex_lock(v_mutex_5_);
v___x_7_ = lean_apply_2(v_k_2_, v_ref_4_, lean_box(0));
v___x_8_ = lean_io_basemutex_unlock(v_mutex_5_);
lean_dec(v_mutex_5_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg___boxed(lean_object* v_mutex_9_, lean_object* v_k_10_, lean_object* v___y_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(v_mutex_9_, v_k_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1(lean_object* v_00_u03b1_13_, lean_object* v_00_u03b2_14_, lean_object* v_mutex_15_, lean_object* v_k_16_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(v_mutex_15_, v_k_16_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___boxed(lean_object* v_00_u03b1_19_, lean_object* v_00_u03b2_20_, lean_object* v_mutex_21_, lean_object* v_k_22_, lean_object* v___y_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1(v_00_u03b1_19_, v_00_u03b2_20_, v_mutex_21_, v_k_22_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg(lean_object* v_t_25_, lean_object* v_k_26_){
_start:
{
if (lean_obj_tag(v_t_25_) == 0)
{
lean_object* v_k_27_; lean_object* v_v_28_; lean_object* v_l_29_; lean_object* v_r_30_; uint8_t v___x_31_; 
v_k_27_ = lean_ctor_get(v_t_25_, 1);
v_v_28_ = lean_ctor_get(v_t_25_, 2);
v_l_29_ = lean_ctor_get(v_t_25_, 3);
v_r_30_ = lean_ctor_get(v_t_25_, 4);
v___x_31_ = l_Lake_BuildKey_quickCmp(v_k_26_, v_k_27_);
switch(v___x_31_)
{
case 0:
{
v_t_25_ = v_l_29_;
goto _start;
}
case 1:
{
lean_object* v___x_33_; 
lean_inc(v_v_28_);
v___x_33_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_33_, 0, v_v_28_);
return v___x_33_;
}
default: 
{
v_t_25_ = v_r_30_;
goto _start;
}
}
}
else
{
lean_object* v___x_35_; 
v___x_35_ = lean_box(0);
return v___x_35_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg___boxed(lean_object* v_t_36_, lean_object* v_k_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg(v_t_36_, v_k_37_);
lean_dec_ref(v_k_37_);
lean_dec(v_t_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__0(lean_object* v_key_39_, lean_object* v_ref_40_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_st_ref_get(v_ref_40_);
v___x_43_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg(v___x_42_, v_key_39_);
lean_dec(v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__0___boxed(lean_object* v_key_44_, lean_object* v_ref_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__0(v_key_44_, v_ref_45_);
lean_dec(v_ref_45_);
lean_dec_ref(v_key_44_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__2___redArg(lean_object* v_k_48_, lean_object* v_v_49_, lean_object* v_t_50_){
_start:
{
if (lean_obj_tag(v_t_50_) == 0)
{
lean_object* v_size_51_; lean_object* v_k_52_; lean_object* v_v_53_; lean_object* v_l_54_; lean_object* v_r_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_335_; 
v_size_51_ = lean_ctor_get(v_t_50_, 0);
v_k_52_ = lean_ctor_get(v_t_50_, 1);
v_v_53_ = lean_ctor_get(v_t_50_, 2);
v_l_54_ = lean_ctor_get(v_t_50_, 3);
v_r_55_ = lean_ctor_get(v_t_50_, 4);
v_isSharedCheck_335_ = !lean_is_exclusive(v_t_50_);
if (v_isSharedCheck_335_ == 0)
{
v___x_57_ = v_t_50_;
v_isShared_58_ = v_isSharedCheck_335_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_r_55_);
lean_inc(v_l_54_);
lean_inc(v_v_53_);
lean_inc(v_k_52_);
lean_inc(v_size_51_);
lean_dec(v_t_50_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_335_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
uint8_t v___x_59_; 
v___x_59_ = l_Lake_BuildKey_quickCmp(v_k_48_, v_k_52_);
switch(v___x_59_)
{
case 0:
{
lean_object* v_impl_60_; lean_object* v___x_61_; 
lean_dec(v_size_51_);
v_impl_60_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__2___redArg(v_k_48_, v_v_49_, v_l_54_);
v___x_61_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_55_) == 0)
{
lean_object* v_size_62_; lean_object* v_size_63_; lean_object* v_k_64_; lean_object* v_v_65_; lean_object* v_l_66_; lean_object* v_r_67_; lean_object* v___x_68_; lean_object* v___x_69_; uint8_t v___x_70_; 
v_size_62_ = lean_ctor_get(v_r_55_, 0);
v_size_63_ = lean_ctor_get(v_impl_60_, 0);
v_k_64_ = lean_ctor_get(v_impl_60_, 1);
v_v_65_ = lean_ctor_get(v_impl_60_, 2);
v_l_66_ = lean_ctor_get(v_impl_60_, 3);
v_r_67_ = lean_ctor_get(v_impl_60_, 4);
lean_inc(v_r_67_);
v___x_68_ = lean_unsigned_to_nat(3u);
v___x_69_ = lean_nat_mul(v___x_68_, v_size_62_);
v___x_70_ = lean_nat_dec_lt(v___x_69_, v_size_63_);
lean_dec(v___x_69_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_74_; 
lean_dec(v_r_67_);
v___x_71_ = lean_nat_add(v___x_61_, v_size_63_);
v___x_72_ = lean_nat_add(v___x_71_, v_size_62_);
lean_dec(v___x_71_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 3, v_impl_60_);
lean_ctor_set(v___x_57_, 0, v___x_72_);
v___x_74_ = v___x_57_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v___x_72_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_75_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_75_, 3, v_impl_60_);
lean_ctor_set(v_reuseFailAlloc_75_, 4, v_r_55_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
else
{
lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_141_; 
lean_inc(v_l_66_);
lean_inc(v_v_65_);
lean_inc(v_k_64_);
lean_inc(v_size_63_);
v_isSharedCheck_141_ = !lean_is_exclusive(v_impl_60_);
if (v_isSharedCheck_141_ == 0)
{
lean_object* v_unused_142_; lean_object* v_unused_143_; lean_object* v_unused_144_; lean_object* v_unused_145_; lean_object* v_unused_146_; 
v_unused_142_ = lean_ctor_get(v_impl_60_, 4);
lean_dec(v_unused_142_);
v_unused_143_ = lean_ctor_get(v_impl_60_, 3);
lean_dec(v_unused_143_);
v_unused_144_ = lean_ctor_get(v_impl_60_, 2);
lean_dec(v_unused_144_);
v_unused_145_ = lean_ctor_get(v_impl_60_, 1);
lean_dec(v_unused_145_);
v_unused_146_ = lean_ctor_get(v_impl_60_, 0);
lean_dec(v_unused_146_);
v___x_77_ = v_impl_60_;
v_isShared_78_ = v_isSharedCheck_141_;
goto v_resetjp_76_;
}
else
{
lean_dec(v_impl_60_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_141_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v_size_79_; lean_object* v_size_80_; lean_object* v_k_81_; lean_object* v_v_82_; lean_object* v_l_83_; lean_object* v_r_84_; lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; 
v_size_79_ = lean_ctor_get(v_l_66_, 0);
v_size_80_ = lean_ctor_get(v_r_67_, 0);
v_k_81_ = lean_ctor_get(v_r_67_, 1);
v_v_82_ = lean_ctor_get(v_r_67_, 2);
v_l_83_ = lean_ctor_get(v_r_67_, 3);
v_r_84_ = lean_ctor_get(v_r_67_, 4);
v___x_85_ = lean_unsigned_to_nat(2u);
v___x_86_ = lean_nat_mul(v___x_85_, v_size_79_);
v___x_87_ = lean_nat_dec_lt(v_size_80_, v___x_86_);
lean_dec(v___x_86_);
if (v___x_87_ == 0)
{
lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_116_; 
lean_inc(v_r_84_);
lean_inc(v_l_83_);
lean_inc(v_v_82_);
lean_inc(v_k_81_);
v_isSharedCheck_116_ = !lean_is_exclusive(v_r_67_);
if (v_isSharedCheck_116_ == 0)
{
lean_object* v_unused_117_; lean_object* v_unused_118_; lean_object* v_unused_119_; lean_object* v_unused_120_; lean_object* v_unused_121_; 
v_unused_117_ = lean_ctor_get(v_r_67_, 4);
lean_dec(v_unused_117_);
v_unused_118_ = lean_ctor_get(v_r_67_, 3);
lean_dec(v_unused_118_);
v_unused_119_ = lean_ctor_get(v_r_67_, 2);
lean_dec(v_unused_119_);
v_unused_120_ = lean_ctor_get(v_r_67_, 1);
lean_dec(v_unused_120_);
v_unused_121_ = lean_ctor_get(v_r_67_, 0);
lean_dec(v_unused_121_);
v___x_89_ = v_r_67_;
v_isShared_90_ = v_isSharedCheck_116_;
goto v_resetjp_88_;
}
else
{
lean_dec(v_r_67_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_116_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___y_94_; lean_object* v___y_95_; lean_object* v___y_96_; lean_object* v___x_104_; lean_object* v___y_106_; 
v___x_91_ = lean_nat_add(v___x_61_, v_size_63_);
lean_dec(v_size_63_);
v___x_92_ = lean_nat_add(v___x_91_, v_size_62_);
lean_dec(v___x_91_);
v___x_104_ = lean_nat_add(v___x_61_, v_size_79_);
if (lean_obj_tag(v_l_83_) == 0)
{
lean_object* v_size_114_; 
v_size_114_ = lean_ctor_get(v_l_83_, 0);
lean_inc(v_size_114_);
v___y_106_ = v_size_114_;
goto v___jp_105_;
}
else
{
lean_object* v___x_115_; 
v___x_115_ = lean_unsigned_to_nat(0u);
v___y_106_ = v___x_115_;
goto v___jp_105_;
}
v___jp_93_:
{
lean_object* v___x_97_; lean_object* v___x_99_; 
v___x_97_ = lean_nat_add(v___y_94_, v___y_96_);
lean_dec(v___y_96_);
lean_dec(v___y_94_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 4, v_r_55_);
lean_ctor_set(v___x_89_, 3, v_r_84_);
lean_ctor_set(v___x_89_, 2, v_v_53_);
lean_ctor_set(v___x_89_, 1, v_k_52_);
lean_ctor_set(v___x_89_, 0, v___x_97_);
v___x_99_ = v___x_89_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_97_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_103_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_103_, 3, v_r_84_);
lean_ctor_set(v_reuseFailAlloc_103_, 4, v_r_55_);
v___x_99_ = v_reuseFailAlloc_103_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v___x_101_; 
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v___x_99_);
lean_ctor_set(v___x_77_, 3, v___y_95_);
lean_ctor_set(v___x_77_, 2, v_v_82_);
lean_ctor_set(v___x_77_, 1, v_k_81_);
lean_ctor_set(v___x_77_, 0, v___x_92_);
v___x_101_ = v___x_77_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___x_92_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v_k_81_);
lean_ctor_set(v_reuseFailAlloc_102_, 2, v_v_82_);
lean_ctor_set(v_reuseFailAlloc_102_, 3, v___y_95_);
lean_ctor_set(v_reuseFailAlloc_102_, 4, v___x_99_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
v___jp_105_:
{
lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_107_ = lean_nat_add(v___x_104_, v___y_106_);
lean_dec(v___y_106_);
lean_dec(v___x_104_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 4, v_l_83_);
lean_ctor_set(v___x_57_, 3, v_l_66_);
lean_ctor_set(v___x_57_, 2, v_v_65_);
lean_ctor_set(v___x_57_, 1, v_k_64_);
lean_ctor_set(v___x_57_, 0, v___x_107_);
v___x_109_ = v___x_57_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_k_64_);
lean_ctor_set(v_reuseFailAlloc_113_, 2, v_v_65_);
lean_ctor_set(v_reuseFailAlloc_113_, 3, v_l_66_);
lean_ctor_set(v_reuseFailAlloc_113_, 4, v_l_83_);
v___x_109_ = v_reuseFailAlloc_113_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; 
v___x_110_ = lean_nat_add(v___x_61_, v_size_62_);
if (lean_obj_tag(v_r_84_) == 0)
{
lean_object* v_size_111_; 
v_size_111_ = lean_ctor_get(v_r_84_, 0);
lean_inc(v_size_111_);
v___y_94_ = v___x_110_;
v___y_95_ = v___x_109_;
v___y_96_ = v_size_111_;
goto v___jp_93_;
}
else
{
lean_object* v___x_112_; 
v___x_112_ = lean_unsigned_to_nat(0u);
v___y_94_ = v___x_110_;
v___y_95_ = v___x_109_;
v___y_96_ = v___x_112_;
goto v___jp_93_;
}
}
}
}
}
else
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_127_; 
lean_del_object(v___x_57_);
v___x_122_ = lean_nat_add(v___x_61_, v_size_63_);
lean_dec(v_size_63_);
v___x_123_ = lean_nat_add(v___x_122_, v_size_62_);
lean_dec(v___x_122_);
v___x_124_ = lean_nat_add(v___x_61_, v_size_62_);
v___x_125_ = lean_nat_add(v___x_124_, v_size_80_);
lean_dec(v___x_124_);
lean_inc_ref(v_r_55_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v_r_55_);
lean_ctor_set(v___x_77_, 3, v_r_67_);
lean_ctor_set(v___x_77_, 2, v_v_53_);
lean_ctor_set(v___x_77_, 1, v_k_52_);
lean_ctor_set(v___x_77_, 0, v___x_125_);
v___x_127_ = v___x_77_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_125_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_140_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_140_, 3, v_r_67_);
lean_ctor_set(v_reuseFailAlloc_140_, 4, v_r_55_);
v___x_127_ = v_reuseFailAlloc_140_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_134_; 
v_isSharedCheck_134_ = !lean_is_exclusive(v_r_55_);
if (v_isSharedCheck_134_ == 0)
{
lean_object* v_unused_135_; lean_object* v_unused_136_; lean_object* v_unused_137_; lean_object* v_unused_138_; lean_object* v_unused_139_; 
v_unused_135_ = lean_ctor_get(v_r_55_, 4);
lean_dec(v_unused_135_);
v_unused_136_ = lean_ctor_get(v_r_55_, 3);
lean_dec(v_unused_136_);
v_unused_137_ = lean_ctor_get(v_r_55_, 2);
lean_dec(v_unused_137_);
v_unused_138_ = lean_ctor_get(v_r_55_, 1);
lean_dec(v_unused_138_);
v_unused_139_ = lean_ctor_get(v_r_55_, 0);
lean_dec(v_unused_139_);
v___x_129_ = v_r_55_;
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
else
{
lean_dec(v_r_55_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_132_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v___x_127_);
lean_ctor_set(v___x_129_, 3, v_l_66_);
lean_ctor_set(v___x_129_, 2, v_v_65_);
lean_ctor_set(v___x_129_, 1, v_k_64_);
lean_ctor_set(v___x_129_, 0, v___x_123_);
v___x_132_ = v___x_129_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_123_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v_k_64_);
lean_ctor_set(v_reuseFailAlloc_133_, 2, v_v_65_);
lean_ctor_set(v_reuseFailAlloc_133_, 3, v_l_66_);
lean_ctor_set(v_reuseFailAlloc_133_, 4, v___x_127_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_147_; 
v_l_147_ = lean_ctor_get(v_impl_60_, 3);
if (lean_obj_tag(v_l_147_) == 0)
{
lean_object* v_r_148_; lean_object* v_k_149_; lean_object* v_v_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_161_; 
lean_inc_ref(v_l_147_);
v_r_148_ = lean_ctor_get(v_impl_60_, 4);
v_k_149_ = lean_ctor_get(v_impl_60_, 1);
v_v_150_ = lean_ctor_get(v_impl_60_, 2);
v_isSharedCheck_161_ = !lean_is_exclusive(v_impl_60_);
if (v_isSharedCheck_161_ == 0)
{
lean_object* v_unused_162_; lean_object* v_unused_163_; 
v_unused_162_ = lean_ctor_get(v_impl_60_, 3);
lean_dec(v_unused_162_);
v_unused_163_ = lean_ctor_get(v_impl_60_, 0);
lean_dec(v_unused_163_);
v___x_152_ = v_impl_60_;
v_isShared_153_ = v_isSharedCheck_161_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_r_148_);
lean_inc(v_v_150_);
lean_inc(v_k_149_);
lean_dec(v_impl_60_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_161_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_154_; lean_object* v___x_156_; 
v___x_154_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_148_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 3, v_r_148_);
lean_ctor_set(v___x_152_, 2, v_v_53_);
lean_ctor_set(v___x_152_, 1, v_k_52_);
lean_ctor_set(v___x_152_, 0, v___x_61_);
v___x_156_ = v___x_152_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_61_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_160_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_160_, 3, v_r_148_);
lean_ctor_set(v_reuseFailAlloc_160_, 4, v_r_148_);
v___x_156_ = v_reuseFailAlloc_160_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_object* v___x_158_; 
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 4, v___x_156_);
lean_ctor_set(v___x_57_, 3, v_l_147_);
lean_ctor_set(v___x_57_, 2, v_v_150_);
lean_ctor_set(v___x_57_, 1, v_k_149_);
lean_ctor_set(v___x_57_, 0, v___x_154_);
v___x_158_ = v___x_57_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_154_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v_k_149_);
lean_ctor_set(v_reuseFailAlloc_159_, 2, v_v_150_);
lean_ctor_set(v_reuseFailAlloc_159_, 3, v_l_147_);
lean_ctor_set(v_reuseFailAlloc_159_, 4, v___x_156_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
}
else
{
lean_object* v_r_164_; 
v_r_164_ = lean_ctor_get(v_impl_60_, 4);
lean_inc(v_r_164_);
if (lean_obj_tag(v_r_164_) == 0)
{
lean_object* v_k_165_; lean_object* v_v_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_189_; 
lean_inc(v_l_147_);
v_k_165_ = lean_ctor_get(v_impl_60_, 1);
v_v_166_ = lean_ctor_get(v_impl_60_, 2);
v_isSharedCheck_189_ = !lean_is_exclusive(v_impl_60_);
if (v_isSharedCheck_189_ == 0)
{
lean_object* v_unused_190_; lean_object* v_unused_191_; lean_object* v_unused_192_; 
v_unused_190_ = lean_ctor_get(v_impl_60_, 4);
lean_dec(v_unused_190_);
v_unused_191_ = lean_ctor_get(v_impl_60_, 3);
lean_dec(v_unused_191_);
v_unused_192_ = lean_ctor_get(v_impl_60_, 0);
lean_dec(v_unused_192_);
v___x_168_ = v_impl_60_;
v_isShared_169_ = v_isSharedCheck_189_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_v_166_);
lean_inc(v_k_165_);
lean_dec(v_impl_60_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_189_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v_k_170_; lean_object* v_v_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_185_; 
v_k_170_ = lean_ctor_get(v_r_164_, 1);
v_v_171_ = lean_ctor_get(v_r_164_, 2);
v_isSharedCheck_185_ = !lean_is_exclusive(v_r_164_);
if (v_isSharedCheck_185_ == 0)
{
lean_object* v_unused_186_; lean_object* v_unused_187_; lean_object* v_unused_188_; 
v_unused_186_ = lean_ctor_get(v_r_164_, 4);
lean_dec(v_unused_186_);
v_unused_187_ = lean_ctor_get(v_r_164_, 3);
lean_dec(v_unused_187_);
v_unused_188_ = lean_ctor_get(v_r_164_, 0);
lean_dec(v_unused_188_);
v___x_173_ = v_r_164_;
v_isShared_174_ = v_isSharedCheck_185_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_v_171_);
lean_inc(v_k_170_);
lean_dec(v_r_164_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_185_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_175_ = lean_unsigned_to_nat(3u);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 4, v_l_147_);
lean_ctor_set(v___x_173_, 3, v_l_147_);
lean_ctor_set(v___x_173_, 2, v_v_166_);
lean_ctor_set(v___x_173_, 1, v_k_165_);
lean_ctor_set(v___x_173_, 0, v___x_61_);
v___x_177_ = v___x_173_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_61_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v_k_165_);
lean_ctor_set(v_reuseFailAlloc_184_, 2, v_v_166_);
lean_ctor_set(v_reuseFailAlloc_184_, 3, v_l_147_);
lean_ctor_set(v_reuseFailAlloc_184_, 4, v_l_147_);
v___x_177_ = v_reuseFailAlloc_184_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
lean_object* v___x_179_; 
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 4, v_l_147_);
lean_ctor_set(v___x_168_, 2, v_v_53_);
lean_ctor_set(v___x_168_, 1, v_k_52_);
lean_ctor_set(v___x_168_, 0, v___x_61_);
v___x_179_ = v___x_168_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_61_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_183_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_183_, 3, v_l_147_);
lean_ctor_set(v_reuseFailAlloc_183_, 4, v_l_147_);
v___x_179_ = v_reuseFailAlloc_183_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_object* v___x_181_; 
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 4, v___x_179_);
lean_ctor_set(v___x_57_, 3, v___x_177_);
lean_ctor_set(v___x_57_, 2, v_v_171_);
lean_ctor_set(v___x_57_, 1, v_k_170_);
lean_ctor_set(v___x_57_, 0, v___x_175_);
v___x_181_ = v___x_57_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_175_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_k_170_);
lean_ctor_set(v_reuseFailAlloc_182_, 2, v_v_171_);
lean_ctor_set(v_reuseFailAlloc_182_, 3, v___x_177_);
lean_ctor_set(v_reuseFailAlloc_182_, 4, v___x_179_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
}
}
else
{
lean_object* v___x_193_; lean_object* v___x_195_; 
v___x_193_ = lean_unsigned_to_nat(2u);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 4, v_r_164_);
lean_ctor_set(v___x_57_, 3, v_impl_60_);
lean_ctor_set(v___x_57_, 0, v___x_193_);
v___x_195_ = v___x_57_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_196_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_196_, 3, v_impl_60_);
lean_ctor_set(v_reuseFailAlloc_196_, 4, v_r_164_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
}
case 1:
{
lean_object* v___x_198_; 
lean_dec(v_v_53_);
lean_dec(v_k_52_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 2, v_v_49_);
lean_ctor_set(v___x_57_, 1, v_k_48_);
v___x_198_ = v___x_57_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_size_51_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v_k_48_);
lean_ctor_set(v_reuseFailAlloc_199_, 2, v_v_49_);
lean_ctor_set(v_reuseFailAlloc_199_, 3, v_l_54_);
lean_ctor_set(v_reuseFailAlloc_199_, 4, v_r_55_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
default: 
{
lean_object* v_impl_200_; lean_object* v___x_201_; 
lean_dec(v_size_51_);
v_impl_200_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__2___redArg(v_k_48_, v_v_49_, v_r_55_);
v___x_201_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_54_) == 0)
{
lean_object* v_size_202_; lean_object* v_size_203_; lean_object* v_k_204_; lean_object* v_v_205_; lean_object* v_l_206_; lean_object* v_r_207_; lean_object* v___x_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v_size_202_ = lean_ctor_get(v_l_54_, 0);
v_size_203_ = lean_ctor_get(v_impl_200_, 0);
v_k_204_ = lean_ctor_get(v_impl_200_, 1);
v_v_205_ = lean_ctor_get(v_impl_200_, 2);
v_l_206_ = lean_ctor_get(v_impl_200_, 3);
lean_inc(v_l_206_);
v_r_207_ = lean_ctor_get(v_impl_200_, 4);
v___x_208_ = lean_unsigned_to_nat(3u);
v___x_209_ = lean_nat_mul(v___x_208_, v_size_202_);
v___x_210_ = lean_nat_dec_lt(v___x_209_, v_size_203_);
lean_dec(v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_214_; 
lean_dec(v_l_206_);
v___x_211_ = lean_nat_add(v___x_201_, v_size_202_);
v___x_212_ = lean_nat_add(v___x_211_, v_size_203_);
lean_dec(v___x_211_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 4, v_impl_200_);
lean_ctor_set(v___x_57_, 0, v___x_212_);
v___x_214_ = v___x_57_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_212_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_215_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_215_, 3, v_l_54_);
lean_ctor_set(v_reuseFailAlloc_215_, 4, v_impl_200_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
else
{
lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_279_; 
lean_inc(v_r_207_);
lean_inc(v_v_205_);
lean_inc(v_k_204_);
lean_inc(v_size_203_);
v_isSharedCheck_279_ = !lean_is_exclusive(v_impl_200_);
if (v_isSharedCheck_279_ == 0)
{
lean_object* v_unused_280_; lean_object* v_unused_281_; lean_object* v_unused_282_; lean_object* v_unused_283_; lean_object* v_unused_284_; 
v_unused_280_ = lean_ctor_get(v_impl_200_, 4);
lean_dec(v_unused_280_);
v_unused_281_ = lean_ctor_get(v_impl_200_, 3);
lean_dec(v_unused_281_);
v_unused_282_ = lean_ctor_get(v_impl_200_, 2);
lean_dec(v_unused_282_);
v_unused_283_ = lean_ctor_get(v_impl_200_, 1);
lean_dec(v_unused_283_);
v_unused_284_ = lean_ctor_get(v_impl_200_, 0);
lean_dec(v_unused_284_);
v___x_217_ = v_impl_200_;
v_isShared_218_ = v_isSharedCheck_279_;
goto v_resetjp_216_;
}
else
{
lean_dec(v_impl_200_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_279_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v_size_219_; lean_object* v_k_220_; lean_object* v_v_221_; lean_object* v_l_222_; lean_object* v_r_223_; lean_object* v_size_224_; lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v_size_219_ = lean_ctor_get(v_l_206_, 0);
v_k_220_ = lean_ctor_get(v_l_206_, 1);
v_v_221_ = lean_ctor_get(v_l_206_, 2);
v_l_222_ = lean_ctor_get(v_l_206_, 3);
v_r_223_ = lean_ctor_get(v_l_206_, 4);
v_size_224_ = lean_ctor_get(v_r_207_, 0);
v___x_225_ = lean_unsigned_to_nat(2u);
v___x_226_ = lean_nat_mul(v___x_225_, v_size_224_);
v___x_227_ = lean_nat_dec_lt(v_size_219_, v___x_226_);
lean_dec(v___x_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_255_; 
lean_inc(v_r_223_);
lean_inc(v_l_222_);
lean_inc(v_v_221_);
lean_inc(v_k_220_);
v_isSharedCheck_255_ = !lean_is_exclusive(v_l_206_);
if (v_isSharedCheck_255_ == 0)
{
lean_object* v_unused_256_; lean_object* v_unused_257_; lean_object* v_unused_258_; lean_object* v_unused_259_; lean_object* v_unused_260_; 
v_unused_256_ = lean_ctor_get(v_l_206_, 4);
lean_dec(v_unused_256_);
v_unused_257_ = lean_ctor_get(v_l_206_, 3);
lean_dec(v_unused_257_);
v_unused_258_ = lean_ctor_get(v_l_206_, 2);
lean_dec(v_unused_258_);
v_unused_259_ = lean_ctor_get(v_l_206_, 1);
lean_dec(v_unused_259_);
v_unused_260_ = lean_ctor_get(v_l_206_, 0);
lean_dec(v_unused_260_);
v___x_229_ = v_l_206_;
v_isShared_230_ = v_isSharedCheck_255_;
goto v_resetjp_228_;
}
else
{
lean_dec(v_l_206_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_255_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___y_234_; lean_object* v___y_235_; lean_object* v___y_236_; lean_object* v___y_245_; 
v___x_231_ = lean_nat_add(v___x_201_, v_size_202_);
v___x_232_ = lean_nat_add(v___x_231_, v_size_203_);
lean_dec(v_size_203_);
if (lean_obj_tag(v_l_222_) == 0)
{
lean_object* v_size_253_; 
v_size_253_ = lean_ctor_get(v_l_222_, 0);
lean_inc(v_size_253_);
v___y_245_ = v_size_253_;
goto v___jp_244_;
}
else
{
lean_object* v___x_254_; 
v___x_254_ = lean_unsigned_to_nat(0u);
v___y_245_ = v___x_254_;
goto v___jp_244_;
}
v___jp_233_:
{
lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_237_ = lean_nat_add(v___y_235_, v___y_236_);
lean_dec(v___y_236_);
lean_dec(v___y_235_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 4, v_r_207_);
lean_ctor_set(v___x_229_, 3, v_r_223_);
lean_ctor_set(v___x_229_, 2, v_v_205_);
lean_ctor_set(v___x_229_, 1, v_k_204_);
lean_ctor_set(v___x_229_, 0, v___x_237_);
v___x_239_ = v___x_229_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_237_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_k_204_);
lean_ctor_set(v_reuseFailAlloc_243_, 2, v_v_205_);
lean_ctor_set(v_reuseFailAlloc_243_, 3, v_r_223_);
lean_ctor_set(v_reuseFailAlloc_243_, 4, v_r_207_);
v___x_239_ = v_reuseFailAlloc_243_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_241_; 
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 4, v___x_239_);
lean_ctor_set(v___x_217_, 3, v___y_234_);
lean_ctor_set(v___x_217_, 2, v_v_221_);
lean_ctor_set(v___x_217_, 1, v_k_220_);
lean_ctor_set(v___x_217_, 0, v___x_232_);
v___x_241_ = v___x_217_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_k_220_);
lean_ctor_set(v_reuseFailAlloc_242_, 2, v_v_221_);
lean_ctor_set(v_reuseFailAlloc_242_, 3, v___y_234_);
lean_ctor_set(v_reuseFailAlloc_242_, 4, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
v___jp_244_:
{
lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_246_ = lean_nat_add(v___x_231_, v___y_245_);
lean_dec(v___y_245_);
lean_dec(v___x_231_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 4, v_l_222_);
lean_ctor_set(v___x_57_, 0, v___x_246_);
v___x_248_ = v___x_57_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_252_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_252_, 3, v_l_54_);
lean_ctor_set(v_reuseFailAlloc_252_, 4, v_l_222_);
v___x_248_ = v_reuseFailAlloc_252_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_249_; 
v___x_249_ = lean_nat_add(v___x_201_, v_size_224_);
if (lean_obj_tag(v_r_223_) == 0)
{
lean_object* v_size_250_; 
v_size_250_ = lean_ctor_get(v_r_223_, 0);
lean_inc(v_size_250_);
v___y_234_ = v___x_248_;
v___y_235_ = v___x_249_;
v___y_236_ = v_size_250_;
goto v___jp_233_;
}
else
{
lean_object* v___x_251_; 
v___x_251_ = lean_unsigned_to_nat(0u);
v___y_234_ = v___x_248_;
v___y_235_ = v___x_249_;
v___y_236_ = v___x_251_;
goto v___jp_233_;
}
}
}
}
}
else
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_265_; 
lean_del_object(v___x_57_);
v___x_261_ = lean_nat_add(v___x_201_, v_size_202_);
v___x_262_ = lean_nat_add(v___x_261_, v_size_203_);
lean_dec(v_size_203_);
v___x_263_ = lean_nat_add(v___x_261_, v_size_219_);
lean_dec(v___x_261_);
lean_inc_ref(v_l_54_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 4, v_l_206_);
lean_ctor_set(v___x_217_, 3, v_l_54_);
lean_ctor_set(v___x_217_, 2, v_v_53_);
lean_ctor_set(v___x_217_, 1, v_k_52_);
lean_ctor_set(v___x_217_, 0, v___x_263_);
v___x_265_ = v___x_217_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_263_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_278_, 3, v_l_54_);
lean_ctor_set(v_reuseFailAlloc_278_, 4, v_l_206_);
v___x_265_ = v_reuseFailAlloc_278_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
v_isSharedCheck_272_ = !lean_is_exclusive(v_l_54_);
if (v_isSharedCheck_272_ == 0)
{
lean_object* v_unused_273_; lean_object* v_unused_274_; lean_object* v_unused_275_; lean_object* v_unused_276_; lean_object* v_unused_277_; 
v_unused_273_ = lean_ctor_get(v_l_54_, 4);
lean_dec(v_unused_273_);
v_unused_274_ = lean_ctor_get(v_l_54_, 3);
lean_dec(v_unused_274_);
v_unused_275_ = lean_ctor_get(v_l_54_, 2);
lean_dec(v_unused_275_);
v_unused_276_ = lean_ctor_get(v_l_54_, 1);
lean_dec(v_unused_276_);
v_unused_277_ = lean_ctor_get(v_l_54_, 0);
lean_dec(v_unused_277_);
v___x_267_ = v_l_54_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_dec(v_l_54_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 4, v_r_207_);
lean_ctor_set(v___x_267_, 3, v___x_265_);
lean_ctor_set(v___x_267_, 2, v_v_205_);
lean_ctor_set(v___x_267_, 1, v_k_204_);
lean_ctor_set(v___x_267_, 0, v___x_262_);
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_262_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_k_204_);
lean_ctor_set(v_reuseFailAlloc_271_, 2, v_v_205_);
lean_ctor_set(v_reuseFailAlloc_271_, 3, v___x_265_);
lean_ctor_set(v_reuseFailAlloc_271_, 4, v_r_207_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_285_; 
v_l_285_ = lean_ctor_get(v_impl_200_, 3);
lean_inc(v_l_285_);
if (lean_obj_tag(v_l_285_) == 0)
{
lean_object* v_r_286_; lean_object* v_k_287_; lean_object* v_v_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_311_; 
v_r_286_ = lean_ctor_get(v_impl_200_, 4);
v_k_287_ = lean_ctor_get(v_impl_200_, 1);
v_v_288_ = lean_ctor_get(v_impl_200_, 2);
v_isSharedCheck_311_ = !lean_is_exclusive(v_impl_200_);
if (v_isSharedCheck_311_ == 0)
{
lean_object* v_unused_312_; lean_object* v_unused_313_; 
v_unused_312_ = lean_ctor_get(v_impl_200_, 3);
lean_dec(v_unused_312_);
v_unused_313_ = lean_ctor_get(v_impl_200_, 0);
lean_dec(v_unused_313_);
v___x_290_ = v_impl_200_;
v_isShared_291_ = v_isSharedCheck_311_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_r_286_);
lean_inc(v_v_288_);
lean_inc(v_k_287_);
lean_dec(v_impl_200_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_311_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v_k_292_; lean_object* v_v_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_307_; 
v_k_292_ = lean_ctor_get(v_l_285_, 1);
v_v_293_ = lean_ctor_get(v_l_285_, 2);
v_isSharedCheck_307_ = !lean_is_exclusive(v_l_285_);
if (v_isSharedCheck_307_ == 0)
{
lean_object* v_unused_308_; lean_object* v_unused_309_; lean_object* v_unused_310_; 
v_unused_308_ = lean_ctor_get(v_l_285_, 4);
lean_dec(v_unused_308_);
v_unused_309_ = lean_ctor_get(v_l_285_, 3);
lean_dec(v_unused_309_);
v_unused_310_ = lean_ctor_get(v_l_285_, 0);
lean_dec(v_unused_310_);
v___x_295_ = v_l_285_;
v_isShared_296_ = v_isSharedCheck_307_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_v_293_);
lean_inc(v_k_292_);
lean_dec(v_l_285_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_307_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_297_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_286_, 2);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 4, v_r_286_);
lean_ctor_set(v___x_295_, 3, v_r_286_);
lean_ctor_set(v___x_295_, 2, v_v_53_);
lean_ctor_set(v___x_295_, 1, v_k_52_);
lean_ctor_set(v___x_295_, 0, v___x_201_);
v___x_299_ = v___x_295_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_201_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_306_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_306_, 3, v_r_286_);
lean_ctor_set(v_reuseFailAlloc_306_, 4, v_r_286_);
v___x_299_ = v_reuseFailAlloc_306_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_301_; 
lean_inc(v_r_286_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 3, v_r_286_);
lean_ctor_set(v___x_290_, 0, v___x_201_);
v___x_301_ = v___x_290_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_201_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v_k_287_);
lean_ctor_set(v_reuseFailAlloc_305_, 2, v_v_288_);
lean_ctor_set(v_reuseFailAlloc_305_, 3, v_r_286_);
lean_ctor_set(v_reuseFailAlloc_305_, 4, v_r_286_);
v___x_301_ = v_reuseFailAlloc_305_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_303_; 
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 4, v___x_301_);
lean_ctor_set(v___x_57_, 3, v___x_299_);
lean_ctor_set(v___x_57_, 2, v_v_293_);
lean_ctor_set(v___x_57_, 1, v_k_292_);
lean_ctor_set(v___x_57_, 0, v___x_297_);
v___x_303_ = v___x_57_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_297_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v_k_292_);
lean_ctor_set(v_reuseFailAlloc_304_, 2, v_v_293_);
lean_ctor_set(v_reuseFailAlloc_304_, 3, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_304_, 4, v___x_301_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
}
}
else
{
lean_object* v_r_314_; 
v_r_314_ = lean_ctor_get(v_impl_200_, 4);
lean_inc(v_r_314_);
if (lean_obj_tag(v_r_314_) == 0)
{
lean_object* v_k_315_; lean_object* v_v_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_327_; 
v_k_315_ = lean_ctor_get(v_impl_200_, 1);
v_v_316_ = lean_ctor_get(v_impl_200_, 2);
v_isSharedCheck_327_ = !lean_is_exclusive(v_impl_200_);
if (v_isSharedCheck_327_ == 0)
{
lean_object* v_unused_328_; lean_object* v_unused_329_; lean_object* v_unused_330_; 
v_unused_328_ = lean_ctor_get(v_impl_200_, 4);
lean_dec(v_unused_328_);
v_unused_329_ = lean_ctor_get(v_impl_200_, 3);
lean_dec(v_unused_329_);
v_unused_330_ = lean_ctor_get(v_impl_200_, 0);
lean_dec(v_unused_330_);
v___x_318_ = v_impl_200_;
v_isShared_319_ = v_isSharedCheck_327_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_v_316_);
lean_inc(v_k_315_);
lean_dec(v_impl_200_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_327_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v___x_322_; 
v___x_320_ = lean_unsigned_to_nat(3u);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 4, v_l_285_);
lean_ctor_set(v___x_318_, 2, v_v_53_);
lean_ctor_set(v___x_318_, 1, v_k_52_);
lean_ctor_set(v___x_318_, 0, v___x_201_);
v___x_322_ = v___x_318_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_201_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_326_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_326_, 3, v_l_285_);
lean_ctor_set(v_reuseFailAlloc_326_, 4, v_l_285_);
v___x_322_ = v_reuseFailAlloc_326_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_324_; 
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 4, v_r_314_);
lean_ctor_set(v___x_57_, 3, v___x_322_);
lean_ctor_set(v___x_57_, 2, v_v_316_);
lean_ctor_set(v___x_57_, 1, v_k_315_);
lean_ctor_set(v___x_57_, 0, v___x_320_);
v___x_324_ = v___x_57_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_320_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_k_315_);
lean_ctor_set(v_reuseFailAlloc_325_, 2, v_v_316_);
lean_ctor_set(v_reuseFailAlloc_325_, 3, v___x_322_);
lean_ctor_set(v_reuseFailAlloc_325_, 4, v_r_314_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
else
{
lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_331_ = lean_unsigned_to_nat(2u);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 4, v_impl_200_);
lean_ctor_set(v___x_57_, 3, v_r_314_);
lean_ctor_set(v___x_57_, 0, v___x_331_);
v___x_333_ = v___x_57_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_331_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_k_52_);
lean_ctor_set(v_reuseFailAlloc_334_, 2, v_v_53_);
lean_ctor_set(v_reuseFailAlloc_334_, 3, v_r_314_);
lean_ctor_set(v_reuseFailAlloc_334_, 4, v_impl_200_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_unsigned_to_nat(1u);
v___x_337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v_k_48_);
lean_ctor_set(v___x_337_, 2, v_v_49_);
lean_ctor_set(v___x_337_, 3, v_t_50_);
lean_ctor_set(v___x_337_, 4, v_t_50_);
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__1(lean_object* v_key_338_, lean_object* v_a_339_, lean_object* v_x_340_){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_342_ = lean_st_ref_take(v_x_340_);
v___x_343_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__2___redArg(v_key_338_, v_a_339_, v___x_342_);
v___x_344_ = lean_st_ref_put(v_x_340_, v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__1___boxed(lean_object* v_key_345_, lean_object* v_a_346_, lean_object* v_x_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__1(v_key_345_, v_a_346_, v_x_347_);
lean_dec(v_x_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__2(lean_object* v___x_350_, lean_object* v_ref_351_){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_st_ref_get(v_ref_351_);
v___x_354_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg(v___x_353_, v___x_350_);
lean_dec(v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__2___boxed(lean_object* v___x_355_, lean_object* v_ref_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__2(v___x_355_, v_ref_356_);
lean_dec(v_ref_356_);
lean_dec_ref(v___x_355_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__3(lean_object* v___x_359_, lean_object* v_a_360_, lean_object* v_x_361_){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_363_ = lean_st_ref_take(v_x_361_);
v___x_364_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__2___redArg(v___x_359_, v_a_360_, v___x_363_);
v___x_365_ = lean_st_ref_put(v_x_361_, v___x_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__3___boxed(lean_object* v___x_366_, lean_object* v_a_367_, lean_object* v_x_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__3(v___x_366_, v_a_367_, v_x_368_);
lean_dec(v_x_368_);
return v_res_370_;
}
}
static lean_object* _init_l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__3(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__2));
v___x_376_ = l_Lake_BuildTrace_nil(v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex(lean_object* v_info_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
if (lean_obj_tag(v_info_383_) == 0)
{
lean_object* v_package_391_; lean_object* v_target_392_; lean_object* v___x_393_; 
v_package_391_ = lean_ctor_get(v_info_383_, 0);
v_target_392_ = lean_ctor_get(v_info_383_, 1);
v___x_393_ = l_Lake_Package_findTargetDecl_x3f(v_target_392_, v_package_391_);
if (lean_obj_tag(v___x_393_) == 1)
{
lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_435_; 
lean_inc(v_target_392_);
lean_inc_ref(v_package_391_);
v_isSharedCheck_435_ = !lean_is_exclusive(v_info_383_);
if (v_isSharedCheck_435_ == 0)
{
lean_object* v_unused_436_; lean_object* v_unused_437_; 
v_unused_436_ = lean_ctor_get(v_info_383_, 1);
lean_dec(v_unused_436_);
v_unused_437_ = lean_ctor_get(v_info_383_, 0);
lean_dec(v_unused_437_);
v___x_395_ = v_info_383_;
v_isShared_396_ = v_isSharedCheck_435_;
goto v_resetjp_394_;
}
else
{
lean_dec(v_info_383_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_435_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v_val_397_; lean_object* v_name_398_; lean_object* v_kind_399_; lean_object* v_config_400_; uint8_t v___x_401_; 
v_val_397_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_val_397_);
lean_dec_ref_known(v___x_393_, 1);
v_name_398_ = lean_ctor_get(v_val_397_, 1);
lean_inc(v_name_398_);
v_kind_399_ = lean_ctor_get(v_val_397_, 2);
lean_inc(v_kind_399_);
v_config_400_ = lean_ctor_get(v_val_397_, 3);
lean_inc(v_config_400_);
lean_dec(v_val_397_);
v___x_401_ = l_Lean_Name_isAnonymous(v_kind_399_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_410_; 
lean_dec(v_target_392_);
lean_dec_ref(v_a_384_);
v___x_402_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_402_, 0, v_package_391_);
lean_ctor_set(v___x_402_, 1, v_name_398_);
lean_ctor_set(v___x_402_, 2, v_config_400_);
v___x_403_ = lean_unsigned_to_nat(0u);
v___x_404_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__0));
v___x_405_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__1));
v___x_406_ = 0;
v___x_407_ = lean_obj_once(&l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__3, &l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__3_once, _init_l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__3);
v___x_408_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_408_, 0, v___x_404_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
lean_ctor_set(v___x_408_, 2, v___x_403_);
lean_ctor_set_uint8(v___x_408_, sizeof(void*)*3, v___x_406_);
lean_ctor_set_uint8(v___x_408_, sizeof(void*)*3 + 1, v___x_401_);
lean_ctor_set_uint8(v___x_408_, sizeof(void*)*3 + 2, v___x_401_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 1, v___x_408_);
lean_ctor_set(v___x_395_, 0, v___x_402_);
v___x_410_ = v___x_395_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v___x_408_);
v___x_410_ = v_reuseFailAlloc_414_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
lean_object* v___x_411_; lean_object* v_job_412_; lean_object* v___x_413_; 
v___x_411_ = lean_task_pure(v___x_410_);
v_job_412_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_412_, 0, v___x_411_);
lean_ctor_set(v_job_412_, 1, v_kind_399_);
lean_ctor_set(v_job_412_, 2, v___x_405_);
lean_ctor_set_uint8(v_job_412_, sizeof(void*)*3, v___x_401_);
v___x_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_413_, 0, v_job_412_);
lean_ctor_set(v___x_413_, 1, v_a_389_);
return v___x_413_;
}
}
else
{
lean_object* v_keyName_415_; lean_object* v_fetchFn_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_433_; 
lean_dec(v_kind_399_);
lean_dec(v_name_398_);
v_keyName_415_ = lean_ctor_get(v_package_391_, 2);
v_fetchFn_416_ = lean_ctor_get(v_config_400_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v_config_400_);
if (v_isSharedCheck_433_ == 0)
{
lean_object* v_unused_434_; 
v_unused_434_ = lean_ctor_get(v_config_400_, 1);
lean_dec(v_unused_434_);
v___x_418_ = v_config_400_;
v_isShared_419_ = v_isSharedCheck_433_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_fetchFn_416_);
lean_dec(v_config_400_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_433_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v_key_421_; 
lean_inc(v_keyName_415_);
if (v_isShared_419_ == 0)
{
lean_ctor_set_tag(v___x_418_, 3);
lean_ctor_set(v___x_418_, 1, v_target_392_);
lean_ctor_set(v___x_418_, 0, v_keyName_415_);
v_key_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_keyName_415_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_target_392_);
v_key_421_ = v_reuseFailAlloc_432_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
lean_object* v___f_422_; lean_object* v___x_423_; 
lean_inc_ref(v_key_421_);
v___f_422_ = lean_alloc_closure((void*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__0___boxed), 3, 1);
lean_closure_set(v___f_422_, 0, v_key_421_);
lean_inc_ref(v_a_387_);
v___x_423_ = l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(v_a_387_, v___f_422_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v___x_424_; 
lean_del_object(v___x_395_);
lean_inc_ref(v_a_388_);
lean_inc_ref(v_a_387_);
lean_inc(v_a_386_);
lean_inc(v_a_385_);
v___x_424_ = lean_apply_8(v_fetchFn_416_, v_package_391_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, lean_box(0));
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v___f_426_; lean_object* v___x_427_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_a_425_);
v___f_426_ = lean_alloc_closure((void*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__1___boxed), 4, 2);
lean_closure_set(v___f_426_, 0, v_key_421_);
lean_closure_set(v___f_426_, 1, v_a_425_);
lean_inc_ref(v_a_387_);
v___x_427_ = l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(v_a_387_, v___f_426_);
lean_dec(v___x_427_);
return v___x_424_;
}
else
{
lean_dec_ref(v_key_421_);
return v___x_424_;
}
}
else
{
lean_object* v_val_428_; lean_object* v___x_430_; 
lean_dec_ref(v_key_421_);
lean_dec_ref(v_fetchFn_416_);
lean_dec_ref(v_package_391_);
lean_dec_ref(v_a_384_);
v_val_428_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_val_428_);
lean_dec_ref_known(v___x_423_, 1);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 1, v_a_389_);
lean_ctor_set(v___x_395_, 0, v_val_428_);
v___x_430_ = v___x_395_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_val_428_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_a_389_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
lean_dec(v___x_393_);
lean_dec_ref(v_a_384_);
v___x_438_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__4));
v___x_439_ = l_Lake_BuildInfo_key(v_info_383_);
v___x_440_ = l_Lake_BuildKey_toString(v___x_439_);
v___x_441_ = lean_string_append(v___x_438_, v___x_440_);
lean_dec_ref(v___x_440_);
v___x_442_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__5));
v___x_443_ = lean_string_append(v___x_441_, v___x_442_);
v___x_444_ = 3;
v___x_445_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_445_, 0, v___x_443_);
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*1, v___x_444_);
v___x_446_ = lean_array_get_size(v_a_389_);
v___x_447_ = lean_array_push(v_a_389_, v___x_445_);
v___x_448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_446_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
return v___x_448_;
}
}
else
{
lean_object* v_toContext_449_; lean_object* v_target_450_; lean_object* v_kind_451_; lean_object* v_data_452_; lean_object* v_facet_453_; lean_object* v_facetConfigs_454_; lean_object* v___x_455_; 
v_toContext_449_ = lean_ctor_get(v_a_388_, 1);
v_target_450_ = lean_ctor_get(v_info_383_, 0);
v_kind_451_ = lean_ctor_get(v_info_383_, 1);
v_data_452_ = lean_ctor_get(v_info_383_, 2);
v_facet_453_ = lean_ctor_get(v_info_383_, 3);
v_facetConfigs_454_ = lean_ctor_get(v_toContext_449_, 6);
v___x_455_ = l_Lake_FacetConfigMap_get_x3f(v_facet_453_, v_facetConfigs_454_);
if (lean_obj_tag(v___x_455_) == 1)
{
lean_object* v_val_456_; lean_object* v_kind_457_; lean_object* v_fetchFn_458_; uint8_t v_memoize_459_; uint8_t v___x_460_; 
lean_inc(v_kind_451_);
v_val_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_val_456_);
lean_dec_ref_known(v___x_455_, 1);
v_kind_457_ = lean_ctor_get(v_val_456_, 0);
lean_inc(v_kind_457_);
v_fetchFn_458_ = lean_ctor_get(v_val_456_, 1);
lean_inc_ref(v_fetchFn_458_);
v_memoize_459_ = lean_ctor_get_uint8(v_val_456_, sizeof(void*)*4 + 1);
lean_dec(v_val_456_);
v___x_460_ = lean_name_eq(v_kind_457_, v_kind_451_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; uint8_t v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
lean_dec_ref(v_fetchFn_458_);
lean_dec_ref(v_a_384_);
v___x_461_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__4));
v___x_462_ = l_Lake_BuildInfo_key(v_info_383_);
v___x_463_ = l_Lake_BuildKey_toString(v___x_462_);
v___x_464_ = lean_string_append(v___x_461_, v___x_463_);
lean_dec_ref(v___x_463_);
v___x_465_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__6));
v___x_466_ = lean_string_append(v___x_464_, v___x_465_);
v___x_467_ = 1;
v___x_468_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_451_, v___x_467_);
v___x_469_ = lean_string_append(v___x_466_, v___x_468_);
lean_dec_ref(v___x_468_);
v___x_470_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__7));
v___x_471_ = lean_string_append(v___x_469_, v___x_470_);
v___x_472_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_457_, v___x_467_);
v___x_473_ = lean_string_append(v___x_471_, v___x_472_);
lean_dec_ref(v___x_472_);
v___x_474_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__8));
v___x_475_ = lean_string_append(v___x_473_, v___x_474_);
v___x_476_ = 3;
v___x_477_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_477_, 0, v___x_475_);
lean_ctor_set_uint8(v___x_477_, sizeof(void*)*1, v___x_476_);
v___x_478_ = lean_array_get_size(v_a_389_);
v___x_479_ = lean_array_push(v_a_389_, v___x_477_);
v___x_480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_480_, 0, v___x_478_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
return v___x_480_;
}
else
{
lean_inc(v_facet_453_);
lean_inc(v_data_452_);
lean_inc_ref(v_target_450_);
lean_dec(v_kind_457_);
lean_dec(v_kind_451_);
lean_dec_ref_known(v_info_383_, 4);
if (v_memoize_459_ == 0)
{
lean_object* v___x_481_; 
lean_dec(v_facet_453_);
lean_dec_ref(v_target_450_);
lean_inc_ref(v_a_388_);
lean_inc_ref(v_a_387_);
lean_inc(v_a_386_);
lean_inc(v_a_385_);
v___x_481_ = lean_apply_8(v_fetchFn_458_, v_data_452_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, lean_box(0));
return v___x_481_;
}
else
{
lean_object* v___x_482_; lean_object* v___f_483_; lean_object* v___x_484_; 
v___x_482_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_482_, 0, v_target_450_);
lean_ctor_set(v___x_482_, 1, v_facet_453_);
lean_inc_ref(v___x_482_);
v___f_483_ = lean_alloc_closure((void*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__2___boxed), 3, 1);
lean_closure_set(v___f_483_, 0, v___x_482_);
lean_inc_ref(v_a_387_);
v___x_484_ = l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(v_a_387_, v___f_483_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v___x_485_; 
lean_inc_ref(v_a_388_);
lean_inc_ref(v_a_387_);
lean_inc(v_a_386_);
lean_inc(v_a_385_);
v___x_485_ = lean_apply_8(v_fetchFn_458_, v_data_452_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, lean_box(0));
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; lean_object* v___f_487_; lean_object* v___x_488_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_a_486_);
v___f_487_ = lean_alloc_closure((void*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__3___boxed), 4, 2);
lean_closure_set(v___f_487_, 0, v___x_482_);
lean_closure_set(v___f_487_, 1, v_a_486_);
lean_inc_ref(v_a_387_);
v___x_488_ = l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(v_a_387_, v___f_487_);
lean_dec(v___x_488_);
return v___x_485_;
}
else
{
lean_dec_ref_known(v___x_482_, 2);
return v___x_485_;
}
}
else
{
lean_object* v_val_489_; lean_object* v___x_490_; 
lean_dec_ref_known(v___x_482_, 2);
lean_dec_ref(v_fetchFn_458_);
lean_dec(v_data_452_);
lean_dec_ref(v_a_384_);
v_val_489_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_val_489_);
lean_dec_ref_known(v___x_484_, 1);
v___x_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_490_, 0, v_val_489_);
lean_ctor_set(v___x_490_, 1, v_a_389_);
return v___x_490_;
}
}
}
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; uint8_t v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
lean_inc(v_facet_453_);
lean_dec(v___x_455_);
lean_dec_ref(v_a_384_);
v___x_491_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__4));
v___x_492_ = l_Lake_BuildInfo_key(v_info_383_);
v___x_493_ = l_Lake_BuildKey_toString(v___x_492_);
v___x_494_ = lean_string_append(v___x_491_, v___x_493_);
lean_dec_ref(v___x_493_);
v___x_495_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__9));
v___x_496_ = lean_string_append(v___x_494_, v___x_495_);
v___x_497_ = 1;
v___x_498_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_facet_453_, v___x_497_);
v___x_499_ = lean_string_append(v___x_496_, v___x_498_);
lean_dec_ref(v___x_498_);
v___x_500_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__8));
v___x_501_ = lean_string_append(v___x_499_, v___x_500_);
v___x_502_ = 3;
v___x_503_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_503_, 0, v___x_501_);
lean_ctor_set_uint8(v___x_503_, sizeof(void*)*1, v___x_502_);
v___x_504_ = lean_array_get_size(v_a_389_);
v___x_505_ = lean_array_push(v_a_389_, v___x_503_);
v___x_506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_504_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
return v___x_506_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___boxed(lean_object* v_info_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l___private_Lake_Build_Index_0__Lake_recBuildWithIndex(v_info_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
lean_dec_ref(v_a_512_);
lean_dec_ref(v_a_511_);
lean_dec(v_a_510_);
lean_dec(v_a_509_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0(lean_object* v_00_u03b2_516_, lean_object* v_inst_517_, lean_object* v_t_518_, lean_object* v_k_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg(v_t_518_, v_k_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___boxed(lean_object* v_00_u03b2_521_, lean_object* v_inst_522_, lean_object* v_t_523_, lean_object* v_k_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0(v_00_u03b2_521_, v_inst_522_, v_t_523_, v_k_524_);
lean_dec_ref(v_k_524_);
lean_dec(v_t_523_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__2(lean_object* v_00_u03b2_526_, lean_object* v_k_527_, lean_object* v_v_528_, lean_object* v_t_529_, lean_object* v_hl_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__2___redArg(v_k_527_, v_v_528_, v_t_529_);
return v___x_531_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__0(lean_object* v_a_532_, lean_object* v_x_533_){
_start:
{
if (lean_obj_tag(v_x_533_) == 0)
{
uint8_t v___x_534_; 
v___x_534_ = 0;
return v___x_534_;
}
else
{
lean_object* v_head_535_; lean_object* v_tail_536_; uint8_t v___x_537_; 
v_head_535_ = lean_ctor_get(v_x_533_, 0);
v_tail_536_ = lean_ctor_get(v_x_533_, 1);
v___x_537_ = l_Lake_instDecidableEqBuildKey_decEq(v_a_532_, v_head_535_);
if (v___x_537_ == 0)
{
v_x_533_ = v_tail_536_;
goto _start;
}
else
{
return v___x_537_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__0___boxed(lean_object* v_a_539_, lean_object* v_x_540_){
_start:
{
uint8_t v_res_541_; lean_object* v_r_542_; 
v_res_541_ = l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__0(v_a_539_, v_x_540_);
lean_dec(v_x_540_);
lean_dec_ref(v_a_539_);
v_r_542_ = lean_box(v_res_541_);
return v_r_542_;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__1(lean_object* v___x_543_, uint8_t v___x_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
if (lean_obj_tag(v_a_545_) == 0)
{
lean_object* v_fst_547_; lean_object* v_snd_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_557_; 
v_fst_547_ = lean_ctor_get(v_a_546_, 0);
v_snd_548_ = lean_ctor_get(v_a_546_, 1);
v_isSharedCheck_557_ = !lean_is_exclusive(v_a_546_);
if (v_isSharedCheck_557_ == 0)
{
v___x_550_ = v_a_546_;
v_isShared_551_ = v_isSharedCheck_557_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_snd_548_);
lean_inc(v_fst_547_);
lean_dec(v_a_546_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_557_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_552_ = l_List_reverse___redArg(v_fst_547_);
v___x_553_ = l_List_reverse___redArg(v_snd_548_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 1, v___x_553_);
lean_ctor_set(v___x_550_, 0, v___x_552_);
v___x_555_ = v___x_550_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v___x_553_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
else
{
lean_object* v_head_558_; lean_object* v_tail_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_581_; 
v_head_558_ = lean_ctor_get(v_a_545_, 0);
v_tail_559_ = lean_ctor_get(v_a_545_, 1);
v_isSharedCheck_581_ = !lean_is_exclusive(v_a_545_);
if (v_isSharedCheck_581_ == 0)
{
v___x_561_ = v_a_545_;
v_isShared_562_ = v_isSharedCheck_581_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_tail_559_);
lean_inc(v_head_558_);
lean_dec(v_a_545_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_581_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v_fst_563_; lean_object* v_snd_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_580_; 
v_fst_563_ = lean_ctor_get(v_a_546_, 0);
v_snd_564_ = lean_ctor_get(v_a_546_, 1);
v_isSharedCheck_580_ = !lean_is_exclusive(v_a_546_);
if (v_isSharedCheck_580_ == 0)
{
v___x_566_ = v_a_546_;
v_isShared_567_ = v_isSharedCheck_580_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_snd_564_);
lean_inc(v_fst_563_);
lean_dec(v_a_546_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_580_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
uint8_t v___x_576_; 
v___x_576_ = l_Lake_instDecidableEqBuildKey_decEq(v_head_558_, v___x_543_);
if (v___x_576_ == 0)
{
if (v___x_544_ == 0)
{
goto v___jp_568_;
}
else
{
lean_object* v___x_577_; lean_object* v___x_578_; 
lean_del_object(v___x_566_);
lean_del_object(v___x_561_);
v___x_577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_577_, 0, v_head_558_);
lean_ctor_set(v___x_577_, 1, v_fst_563_);
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
lean_ctor_set(v___x_578_, 1, v_snd_564_);
v_a_545_ = v_tail_559_;
v_a_546_ = v___x_578_;
goto _start;
}
}
else
{
goto v___jp_568_;
}
v___jp_568_:
{
lean_object* v___x_570_; 
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 1, v_snd_564_);
v___x_570_ = v___x_561_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_head_558_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v_snd_564_);
v___x_570_ = v_reuseFailAlloc_575_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_572_; 
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 1, v___x_570_);
v___x_572_ = v___x_566_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_fst_563_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v___x_570_);
v___x_572_ = v_reuseFailAlloc_574_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
v_a_545_ = v_tail_559_;
v_a_546_ = v___x_572_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__1___boxed(lean_object* v___x_582_, lean_object* v___x_583_, lean_object* v_a_584_, lean_object* v_a_585_){
_start:
{
uint8_t v___x_3126__boxed_586_; lean_object* v_res_587_; 
v___x_3126__boxed_586_ = lean_unbox(v___x_583_);
v_res_587_ = l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__1(v___x_582_, v___x_3126__boxed_586_, v_a_584_, v_a_585_);
lean_dec_ref(v___x_582_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___lam__0___boxed(lean_object* v___x_588_, lean_object* v_a_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___lam__0(v___x_588_, v_a_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec(v___y_590_);
lean_dec(v___x_588_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(lean_object* v_a_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v___x_606_; uint8_t v___x_607_; 
lean_inc_ref(v_a_599_);
v___x_606_ = l_Lake_BuildInfo_key(v_a_599_);
v___x_607_ = l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__0(v___x_606_, v___y_601_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; lean_object* v___f_609_; lean_object* v___x_610_; 
lean_inc(v___y_601_);
v___x_608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set(v___x_608_, 1, v___y_601_);
lean_inc_ref(v___x_608_);
v___f_609_ = lean_alloc_closure((void*)(l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_609_, 0, v___x_608_);
v___x_610_ = l___private_Lake_Build_Index_0__Lake_recBuildWithIndex(v_a_599_, v___f_609_, v___y_600_, v___x_608_, v___y_602_, v___y_603_, v___y_604_);
lean_dec_ref_known(v___x_608_, 2);
return v___x_610_;
}
else
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v_fst_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_629_; 
lean_dec_ref(v_a_599_);
v___x_611_ = lean_box(0);
v___x_612_ = ((lean_object*)(l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___closed__0));
lean_inc(v___y_601_);
v___x_613_ = l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__1(v___x_606_, v___x_607_, v___y_601_, v___x_612_);
v_fst_614_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_629_ == 0)
{
lean_object* v_unused_630_; 
v_unused_630_ = lean_ctor_get(v___x_613_, 1);
lean_dec(v_unused_630_);
v___x_616_ = v___x_613_;
v_isShared_617_ = v_isSharedCheck_629_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_fst_614_);
lean_dec(v___x_613_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_629_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
lean_inc_ref(v___x_606_);
if (v_isShared_617_ == 0)
{
lean_ctor_set_tag(v___x_616_, 1);
lean_ctor_set(v___x_616_, 1, v_fst_614_);
lean_ctor_set(v___x_616_, 0, v___x_606_);
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_fst_614_);
v___x_619_ = v_reuseFailAlloc_628_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_606_);
lean_ctor_set(v___x_620_, 1, v___x_611_);
v___x_621_ = l_List_appendTR___redArg(v___x_619_, v___x_620_);
v___x_622_ = l_Lake_buildCycleError(v___x_621_);
v___x_623_ = 3;
v___x_624_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_624_, 0, v___x_622_);
lean_ctor_set_uint8(v___x_624_, sizeof(void*)*1, v___x_623_);
v___x_625_ = lean_array_get_size(v___y_604_);
v___x_626_ = lean_array_push(v___y_604_, v___x_624_);
v___x_627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_625_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
return v___x_627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___lam__0(lean_object* v___x_631_, lean_object* v_a_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(v_a_632_, v___y_633_, v___x_631_, v___y_635_, v___y_636_, v___y_637_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___boxed(lean_object* v_a_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(v_a_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec(v___y_641_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recFetchWithIndex(lean_object* v_info_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(v_info_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recFetchWithIndex___boxed(lean_object* v_info_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l___private_Lake_Build_Index_0__Lake_recFetchWithIndex(v_info_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_);
lean_dec_ref(v_a_660_);
lean_dec_ref(v_a_659_);
lean_dec(v_a_658_);
lean_dec(v_a_657_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0(lean_object* v_a_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(v_a_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0___boxed(lean_object* v_a_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0(v_a_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec(v___y_673_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2(lean_object* v_inst_680_, lean_object* v_a_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(v_a_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___boxed(lean_object* v_inst_689_, lean_object* v_a_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2(v_inst_689_, v_a_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec(v___y_692_);
lean_dec(v___y_691_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchT_run___redArg(lean_object* v_x_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = ((lean_object*)(l_Lake_FetchT_run___redArg___closed__0));
lean_inc_ref(v_a_703_);
lean_inc_ref(v_a_702_);
lean_inc(v_a_701_);
lean_inc(v_a_700_);
v___x_705_ = lean_apply_5(v_x_699_, v___x_704_, v_a_700_, v_a_701_, v_a_702_, v_a_703_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchT_run___redArg___boxed(lean_object* v_x_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lake_FetchT_run___redArg(v_x_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
lean_dec_ref(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec(v_a_708_);
lean_dec(v_a_707_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchT_run(lean_object* v_m_712_, lean_object* v_00_u03b1_713_, lean_object* v_x_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = ((lean_object*)(l_Lake_FetchT_run___redArg___closed__0));
lean_inc_ref(v_a_718_);
lean_inc_ref(v_a_717_);
lean_inc(v_a_716_);
lean_inc(v_a_715_);
v___x_720_ = lean_apply_5(v_x_714_, v___x_719_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchT_run___boxed(lean_object* v_m_721_, lean_object* v_00_u03b1_722_, lean_object* v_x_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lake_FetchT_run(v_m_721_, v_00_u03b1_722_, v_x_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
lean_dec_ref(v_a_727_);
lean_dec_ref(v_a_726_);
lean_dec(v_a_725_);
lean_dec(v_a_724_);
return v_res_728_;
}
}
lean_object* runtime_initialize_Lake_Build_Fetch(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Topological(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_StoreInsts(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Index(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Build_Fetch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Topological(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_StoreInsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_Index(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Build_Fetch(uint8_t builtin);
lean_object* initialize_Lake_Config_Monad(uint8_t builtin);
lean_object* initialize_Lake_Build_Topological(uint8_t builtin);
lean_object* initialize_Lake_Util_StoreInsts(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Index(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Fetch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Topological(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_StoreInsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Index(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_Index(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_Index(builtin);
}
#ifdef __cplusplus
}
#endif
