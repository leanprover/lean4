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
uint8_t l_Lake_BuildKey_quickCmp(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
lean_object* l_instMonadFinallyBaseIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildKey_quickCmp___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_instMonadBaseIO;
lean_object* l_instMonadLiftT___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Std_Mutex_atomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_BuildKey_quickCmp___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27___lam__0___closed__0 = (const lean_object*)&l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27___closed__0 = (const lean_object*)&l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27___closed__0_value;
static const lean_closure_object l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadFinallyBaseIO___aux__1___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27___closed__1 = (const lean_object*)&l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__2___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27___lam__0(lean_object* v_key_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_5_ = lean_st_ref_get(v_ref_3_);
v___x_6_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27___lam__0___closed__0));
v___x_7_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_6_, v___x_5_, v_key_2_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27___lam__0___boxed(lean_object* v_key_8_, lean_object* v_ref_9_, lean_object* v___y_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27___lam__0(v_key_8_, v_ref_9_);
lean_dec(v_ref_9_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27___lam__1(lean_object* v_key_12_, lean_object* v_a_13_, lean_object* v_x_14_){
_start:
{
lean_object* v___x_16_; lean_object* v_fst_18_; lean_object* v_snd_19_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_16_ = lean_st_ref_take(v_x_14_);
v___x_21_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27___lam__0___closed__0));
lean_inc_ref(v_key_12_);
lean_inc(v___x_16_);
v___x_22_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_21_, v___x_16_, v_key_12_);
if (lean_obj_tag(v___x_22_) == 0)
{
uint8_t v___x_23_; 
lean_inc(v___x_16_);
lean_inc_ref(v_key_12_);
v___x_23_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___x_21_, v_key_12_, v___x_16_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; 
lean_inc_ref(v_a_13_);
v___x_24_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_21_, v_key_12_, v_a_13_, v___x_16_);
v_fst_18_ = v_a_13_;
v_snd_19_ = v___x_24_;
goto v___jp_17_;
}
else
{
lean_dec_ref(v_key_12_);
v_fst_18_ = v_a_13_;
v_snd_19_ = v___x_16_;
goto v___jp_17_;
}
}
else
{
lean_object* v_val_25_; 
lean_dec_ref(v_a_13_);
lean_dec_ref(v_key_12_);
v_val_25_ = lean_ctor_get(v___x_22_, 0);
lean_inc(v_val_25_);
lean_dec_ref_known(v___x_22_, 1);
v_fst_18_ = v_val_25_;
v_snd_19_ = v___x_16_;
goto v___jp_17_;
}
v___jp_17_:
{
lean_object* v___x_20_; 
v___x_20_ = lean_st_ref_put(v_x_14_, v_snd_19_);
return v_fst_18_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27___lam__1___boxed(lean_object* v_key_26_, lean_object* v_a_27_, lean_object* v_x_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27___lam__1(v_key_26_, v_a_27_, v_x_28_);
lean_dec(v_x_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27(lean_object* v_key_33_, lean_object* v_create_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_){
_start:
{
lean_object* v___f_42_; lean_object* v___x_43_; lean_object* v___f_44_; lean_object* v___x_45_; lean_object* v___x_7492__overap_46_; lean_object* v___x_47_; 
lean_inc_ref(v_key_33_);
v___f_42_ = lean_alloc_closure((void*)(l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27___lam__0___boxed), 3, 1);
lean_closure_set(v___f_42_, 0, v_key_33_);
v___x_43_ = l_instMonadBaseIO;
v___f_44_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27___closed__0));
v___x_45_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27___closed__1));
lean_inc_ref(v_a_38_);
v___x_7492__overap_46_ = l_Std_Mutex_atomically___redArg(v___x_43_, v___f_44_, v___x_45_, v_a_38_, v___f_42_);
v___x_47_ = lean_apply_1(v___x_7492__overap_46_, lean_box(0));
if (lean_obj_tag(v___x_47_) == 1)
{
lean_object* v_val_48_; lean_object* v___x_49_; 
lean_dec_ref(v_a_35_);
lean_dec_ref(v_create_34_);
lean_dec_ref(v_key_33_);
v_val_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc(v_val_48_);
lean_dec_ref_known(v___x_47_, 1);
v___x_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_49_, 0, v_val_48_);
lean_ctor_set(v___x_49_, 1, v_a_40_);
return v___x_49_;
}
else
{
lean_object* v___x_50_; 
lean_dec(v___x_47_);
lean_inc_ref(v_a_39_);
lean_inc_ref(v_a_38_);
lean_inc(v_a_37_);
lean_inc(v_a_36_);
v___x_50_ = lean_apply_7(v_create_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, lean_box(0));
if (lean_obj_tag(v___x_50_) == 0)
{
lean_object* v_a_51_; lean_object* v_a_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_62_; 
v_a_51_ = lean_ctor_get(v___x_50_, 0);
v_a_52_ = lean_ctor_get(v___x_50_, 1);
v_isSharedCheck_62_ = !lean_is_exclusive(v___x_50_);
if (v_isSharedCheck_62_ == 0)
{
v___x_54_ = v___x_50_;
v_isShared_55_ = v_isSharedCheck_62_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_a_52_);
lean_inc(v_a_51_);
lean_dec(v___x_50_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_62_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___f_56_; lean_object* v___x_7497__overap_57_; lean_object* v___x_58_; lean_object* v___x_60_; 
v___f_56_ = lean_alloc_closure((void*)(l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27___lam__1___boxed), 4, 2);
lean_closure_set(v___f_56_, 0, v_key_33_);
lean_closure_set(v___f_56_, 1, v_a_51_);
lean_inc_ref(v_a_38_);
v___x_7497__overap_57_ = l_Std_Mutex_atomically___redArg(v___x_43_, v___f_44_, v___x_45_, v_a_38_, v___f_56_);
v___x_58_ = lean_apply_1(v___x_7497__overap_57_, lean_box(0));
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 0, v___x_58_);
v___x_60_ = v___x_54_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v___x_58_);
lean_ctor_set(v_reuseFailAlloc_61_, 1, v_a_52_);
v___x_60_ = v_reuseFailAlloc_61_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
return v___x_60_;
}
}
}
else
{
lean_dec_ref(v_key_33_);
return v___x_50_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27___boxed(lean_object* v_key_63_, lean_object* v_create_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Lake_Build_Index_0__Lake_fetchOrCreate_x27(v_key_63_, v_create_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
lean_dec_ref(v_a_69_);
lean_dec_ref(v_a_68_);
lean_dec(v_a_67_);
lean_dec(v_a_66_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(lean_object* v_mutex_73_, lean_object* v_k_74_){
_start:
{
lean_object* v_ref_76_; lean_object* v_mutex_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v_ref_76_ = lean_ctor_get(v_mutex_73_, 0);
lean_inc(v_ref_76_);
v_mutex_77_ = lean_ctor_get(v_mutex_73_, 1);
lean_inc(v_mutex_77_);
lean_dec_ref(v_mutex_73_);
v___x_78_ = lean_io_basemutex_lock(v_mutex_77_);
v___x_79_ = lean_apply_2(v_k_74_, v_ref_76_, lean_box(0));
v___x_80_ = lean_io_basemutex_unlock(v_mutex_77_);
lean_dec(v_mutex_77_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg___boxed(lean_object* v_mutex_81_, lean_object* v_k_82_, lean_object* v___y_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(v_mutex_81_, v_k_82_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1(lean_object* v_00_u03b1_85_, lean_object* v_00_u03b2_86_, lean_object* v_mutex_87_, lean_object* v_k_88_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(v_mutex_87_, v_k_88_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___boxed(lean_object* v_00_u03b1_91_, lean_object* v_00_u03b2_92_, lean_object* v_mutex_93_, lean_object* v_k_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1(v_00_u03b1_91_, v_00_u03b2_92_, v_mutex_93_, v_k_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg(lean_object* v_t_97_, lean_object* v_k_98_){
_start:
{
if (lean_obj_tag(v_t_97_) == 0)
{
lean_object* v_k_99_; lean_object* v_v_100_; lean_object* v_l_101_; lean_object* v_r_102_; uint8_t v___x_103_; 
v_k_99_ = lean_ctor_get(v_t_97_, 1);
v_v_100_ = lean_ctor_get(v_t_97_, 2);
v_l_101_ = lean_ctor_get(v_t_97_, 3);
v_r_102_ = lean_ctor_get(v_t_97_, 4);
v___x_103_ = l_Lake_BuildKey_quickCmp(v_k_98_, v_k_99_);
switch(v___x_103_)
{
case 0:
{
v_t_97_ = v_l_101_;
goto _start;
}
case 1:
{
lean_object* v___x_105_; 
lean_inc(v_v_100_);
v___x_105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_105_, 0, v_v_100_);
return v___x_105_;
}
default: 
{
v_t_97_ = v_r_102_;
goto _start;
}
}
}
else
{
lean_object* v___x_107_; 
v___x_107_ = lean_box(0);
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg___boxed(lean_object* v_t_108_, lean_object* v_k_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg(v_t_108_, v_k_109_);
lean_dec_ref(v_k_109_);
lean_dec(v_t_108_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__0(lean_object* v_key_111_, lean_object* v_ref_112_){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lean_st_ref_get(v_ref_112_);
v___x_115_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg(v___x_114_, v_key_111_);
lean_dec(v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__0___boxed(lean_object* v_key_116_, lean_object* v_ref_117_, lean_object* v___y_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__0(v_key_116_, v_ref_117_);
lean_dec(v_ref_117_);
lean_dec_ref(v_key_116_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__3___redArg(lean_object* v_k_120_, lean_object* v_v_121_, lean_object* v_t_122_){
_start:
{
if (lean_obj_tag(v_t_122_) == 0)
{
lean_object* v_size_123_; lean_object* v_k_124_; lean_object* v_v_125_; lean_object* v_l_126_; lean_object* v_r_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_407_; 
v_size_123_ = lean_ctor_get(v_t_122_, 0);
v_k_124_ = lean_ctor_get(v_t_122_, 1);
v_v_125_ = lean_ctor_get(v_t_122_, 2);
v_l_126_ = lean_ctor_get(v_t_122_, 3);
v_r_127_ = lean_ctor_get(v_t_122_, 4);
v_isSharedCheck_407_ = !lean_is_exclusive(v_t_122_);
if (v_isSharedCheck_407_ == 0)
{
v___x_129_ = v_t_122_;
v_isShared_130_ = v_isSharedCheck_407_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_r_127_);
lean_inc(v_l_126_);
lean_inc(v_v_125_);
lean_inc(v_k_124_);
lean_inc(v_size_123_);
lean_dec(v_t_122_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_407_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
uint8_t v___x_131_; 
v___x_131_ = l_Lake_BuildKey_quickCmp(v_k_120_, v_k_124_);
switch(v___x_131_)
{
case 0:
{
lean_object* v_impl_132_; lean_object* v___x_133_; 
lean_dec(v_size_123_);
v_impl_132_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__3___redArg(v_k_120_, v_v_121_, v_l_126_);
v___x_133_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_127_) == 0)
{
lean_object* v_size_134_; lean_object* v_size_135_; lean_object* v_k_136_; lean_object* v_v_137_; lean_object* v_l_138_; lean_object* v_r_139_; lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v_size_134_ = lean_ctor_get(v_r_127_, 0);
v_size_135_ = lean_ctor_get(v_impl_132_, 0);
v_k_136_ = lean_ctor_get(v_impl_132_, 1);
v_v_137_ = lean_ctor_get(v_impl_132_, 2);
v_l_138_ = lean_ctor_get(v_impl_132_, 3);
v_r_139_ = lean_ctor_get(v_impl_132_, 4);
lean_inc(v_r_139_);
v___x_140_ = lean_unsigned_to_nat(3u);
v___x_141_ = lean_nat_mul(v___x_140_, v_size_134_);
v___x_142_ = lean_nat_dec_lt(v___x_141_, v_size_135_);
lean_dec(v___x_141_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_146_; 
lean_dec(v_r_139_);
v___x_143_ = lean_nat_add(v___x_133_, v_size_135_);
v___x_144_ = lean_nat_add(v___x_143_, v_size_134_);
lean_dec(v___x_143_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 3, v_impl_132_);
lean_ctor_set(v___x_129_, 0, v___x_144_);
v___x_146_ = v___x_129_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_144_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_147_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_147_, 3, v_impl_132_);
lean_ctor_set(v_reuseFailAlloc_147_, 4, v_r_127_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
else
{
lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_213_; 
lean_inc(v_l_138_);
lean_inc(v_v_137_);
lean_inc(v_k_136_);
lean_inc(v_size_135_);
v_isSharedCheck_213_ = !lean_is_exclusive(v_impl_132_);
if (v_isSharedCheck_213_ == 0)
{
lean_object* v_unused_214_; lean_object* v_unused_215_; lean_object* v_unused_216_; lean_object* v_unused_217_; lean_object* v_unused_218_; 
v_unused_214_ = lean_ctor_get(v_impl_132_, 4);
lean_dec(v_unused_214_);
v_unused_215_ = lean_ctor_get(v_impl_132_, 3);
lean_dec(v_unused_215_);
v_unused_216_ = lean_ctor_get(v_impl_132_, 2);
lean_dec(v_unused_216_);
v_unused_217_ = lean_ctor_get(v_impl_132_, 1);
lean_dec(v_unused_217_);
v_unused_218_ = lean_ctor_get(v_impl_132_, 0);
lean_dec(v_unused_218_);
v___x_149_ = v_impl_132_;
v_isShared_150_ = v_isSharedCheck_213_;
goto v_resetjp_148_;
}
else
{
lean_dec(v_impl_132_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_213_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v_size_151_; lean_object* v_size_152_; lean_object* v_k_153_; lean_object* v_v_154_; lean_object* v_l_155_; lean_object* v_r_156_; lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v_size_151_ = lean_ctor_get(v_l_138_, 0);
v_size_152_ = lean_ctor_get(v_r_139_, 0);
v_k_153_ = lean_ctor_get(v_r_139_, 1);
v_v_154_ = lean_ctor_get(v_r_139_, 2);
v_l_155_ = lean_ctor_get(v_r_139_, 3);
v_r_156_ = lean_ctor_get(v_r_139_, 4);
v___x_157_ = lean_unsigned_to_nat(2u);
v___x_158_ = lean_nat_mul(v___x_157_, v_size_151_);
v___x_159_ = lean_nat_dec_lt(v_size_152_, v___x_158_);
lean_dec(v___x_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_188_; 
lean_inc(v_r_156_);
lean_inc(v_l_155_);
lean_inc(v_v_154_);
lean_inc(v_k_153_);
v_isSharedCheck_188_ = !lean_is_exclusive(v_r_139_);
if (v_isSharedCheck_188_ == 0)
{
lean_object* v_unused_189_; lean_object* v_unused_190_; lean_object* v_unused_191_; lean_object* v_unused_192_; lean_object* v_unused_193_; 
v_unused_189_ = lean_ctor_get(v_r_139_, 4);
lean_dec(v_unused_189_);
v_unused_190_ = lean_ctor_get(v_r_139_, 3);
lean_dec(v_unused_190_);
v_unused_191_ = lean_ctor_get(v_r_139_, 2);
lean_dec(v_unused_191_);
v_unused_192_ = lean_ctor_get(v_r_139_, 1);
lean_dec(v_unused_192_);
v_unused_193_ = lean_ctor_get(v_r_139_, 0);
lean_dec(v_unused_193_);
v___x_161_ = v_r_139_;
v_isShared_162_ = v_isSharedCheck_188_;
goto v_resetjp_160_;
}
else
{
lean_dec(v_r_139_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_188_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___y_166_; lean_object* v___y_167_; lean_object* v___y_168_; lean_object* v___x_176_; lean_object* v___y_178_; 
v___x_163_ = lean_nat_add(v___x_133_, v_size_135_);
lean_dec(v_size_135_);
v___x_164_ = lean_nat_add(v___x_163_, v_size_134_);
lean_dec(v___x_163_);
v___x_176_ = lean_nat_add(v___x_133_, v_size_151_);
if (lean_obj_tag(v_l_155_) == 0)
{
lean_object* v_size_186_; 
v_size_186_ = lean_ctor_get(v_l_155_, 0);
lean_inc(v_size_186_);
v___y_178_ = v_size_186_;
goto v___jp_177_;
}
else
{
lean_object* v___x_187_; 
v___x_187_ = lean_unsigned_to_nat(0u);
v___y_178_ = v___x_187_;
goto v___jp_177_;
}
v___jp_165_:
{
lean_object* v___x_169_; lean_object* v___x_171_; 
v___x_169_ = lean_nat_add(v___y_167_, v___y_168_);
lean_dec(v___y_168_);
lean_dec(v___y_167_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 4, v_r_127_);
lean_ctor_set(v___x_161_, 3, v_r_156_);
lean_ctor_set(v___x_161_, 2, v_v_125_);
lean_ctor_set(v___x_161_, 1, v_k_124_);
lean_ctor_set(v___x_161_, 0, v___x_169_);
v___x_171_ = v___x_161_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_169_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_175_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_175_, 3, v_r_156_);
lean_ctor_set(v_reuseFailAlloc_175_, 4, v_r_127_);
v___x_171_ = v_reuseFailAlloc_175_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
lean_object* v___x_173_; 
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 4, v___x_171_);
lean_ctor_set(v___x_149_, 3, v___y_166_);
lean_ctor_set(v___x_149_, 2, v_v_154_);
lean_ctor_set(v___x_149_, 1, v_k_153_);
lean_ctor_set(v___x_149_, 0, v___x_164_);
v___x_173_ = v___x_149_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v_k_153_);
lean_ctor_set(v_reuseFailAlloc_174_, 2, v_v_154_);
lean_ctor_set(v_reuseFailAlloc_174_, 3, v___y_166_);
lean_ctor_set(v_reuseFailAlloc_174_, 4, v___x_171_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
v___jp_177_:
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = lean_nat_add(v___x_176_, v___y_178_);
lean_dec(v___y_178_);
lean_dec(v___x_176_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v_l_155_);
lean_ctor_set(v___x_129_, 3, v_l_138_);
lean_ctor_set(v___x_129_, 2, v_v_137_);
lean_ctor_set(v___x_129_, 1, v_k_136_);
lean_ctor_set(v___x_129_, 0, v___x_179_);
v___x_181_ = v___x_129_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_179_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v_k_136_);
lean_ctor_set(v_reuseFailAlloc_185_, 2, v_v_137_);
lean_ctor_set(v_reuseFailAlloc_185_, 3, v_l_138_);
lean_ctor_set(v_reuseFailAlloc_185_, 4, v_l_155_);
v___x_181_ = v_reuseFailAlloc_185_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_182_; 
v___x_182_ = lean_nat_add(v___x_133_, v_size_134_);
if (lean_obj_tag(v_r_156_) == 0)
{
lean_object* v_size_183_; 
v_size_183_ = lean_ctor_get(v_r_156_, 0);
lean_inc(v_size_183_);
v___y_166_ = v___x_181_;
v___y_167_ = v___x_182_;
v___y_168_ = v_size_183_;
goto v___jp_165_;
}
else
{
lean_object* v___x_184_; 
v___x_184_ = lean_unsigned_to_nat(0u);
v___y_166_ = v___x_181_;
v___y_167_ = v___x_182_;
v___y_168_ = v___x_184_;
goto v___jp_165_;
}
}
}
}
}
else
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_199_; 
lean_del_object(v___x_129_);
v___x_194_ = lean_nat_add(v___x_133_, v_size_135_);
lean_dec(v_size_135_);
v___x_195_ = lean_nat_add(v___x_194_, v_size_134_);
lean_dec(v___x_194_);
v___x_196_ = lean_nat_add(v___x_133_, v_size_134_);
v___x_197_ = lean_nat_add(v___x_196_, v_size_152_);
lean_dec(v___x_196_);
lean_inc_ref(v_r_127_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 4, v_r_127_);
lean_ctor_set(v___x_149_, 3, v_r_139_);
lean_ctor_set(v___x_149_, 2, v_v_125_);
lean_ctor_set(v___x_149_, 1, v_k_124_);
lean_ctor_set(v___x_149_, 0, v___x_197_);
v___x_199_ = v___x_149_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_212_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_212_, 3, v_r_139_);
lean_ctor_set(v_reuseFailAlloc_212_, 4, v_r_127_);
v___x_199_ = v_reuseFailAlloc_212_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
v_isSharedCheck_206_ = !lean_is_exclusive(v_r_127_);
if (v_isSharedCheck_206_ == 0)
{
lean_object* v_unused_207_; lean_object* v_unused_208_; lean_object* v_unused_209_; lean_object* v_unused_210_; lean_object* v_unused_211_; 
v_unused_207_ = lean_ctor_get(v_r_127_, 4);
lean_dec(v_unused_207_);
v_unused_208_ = lean_ctor_get(v_r_127_, 3);
lean_dec(v_unused_208_);
v_unused_209_ = lean_ctor_get(v_r_127_, 2);
lean_dec(v_unused_209_);
v_unused_210_ = lean_ctor_get(v_r_127_, 1);
lean_dec(v_unused_210_);
v_unused_211_ = lean_ctor_get(v_r_127_, 0);
lean_dec(v_unused_211_);
v___x_201_ = v_r_127_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_dec(v_r_127_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 4, v___x_199_);
lean_ctor_set(v___x_201_, 3, v_l_138_);
lean_ctor_set(v___x_201_, 2, v_v_137_);
lean_ctor_set(v___x_201_, 1, v_k_136_);
lean_ctor_set(v___x_201_, 0, v___x_195_);
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v_k_136_);
lean_ctor_set(v_reuseFailAlloc_205_, 2, v_v_137_);
lean_ctor_set(v_reuseFailAlloc_205_, 3, v_l_138_);
lean_ctor_set(v_reuseFailAlloc_205_, 4, v___x_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_219_; 
v_l_219_ = lean_ctor_get(v_impl_132_, 3);
if (lean_obj_tag(v_l_219_) == 0)
{
lean_object* v_r_220_; lean_object* v_k_221_; lean_object* v_v_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_233_; 
lean_inc_ref(v_l_219_);
v_r_220_ = lean_ctor_get(v_impl_132_, 4);
v_k_221_ = lean_ctor_get(v_impl_132_, 1);
v_v_222_ = lean_ctor_get(v_impl_132_, 2);
v_isSharedCheck_233_ = !lean_is_exclusive(v_impl_132_);
if (v_isSharedCheck_233_ == 0)
{
lean_object* v_unused_234_; lean_object* v_unused_235_; 
v_unused_234_ = lean_ctor_get(v_impl_132_, 3);
lean_dec(v_unused_234_);
v_unused_235_ = lean_ctor_get(v_impl_132_, 0);
lean_dec(v_unused_235_);
v___x_224_ = v_impl_132_;
v_isShared_225_ = v_isSharedCheck_233_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_r_220_);
lean_inc(v_v_222_);
lean_inc(v_k_221_);
lean_dec(v_impl_132_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_233_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_226_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_220_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 3, v_r_220_);
lean_ctor_set(v___x_224_, 2, v_v_125_);
lean_ctor_set(v___x_224_, 1, v_k_124_);
lean_ctor_set(v___x_224_, 0, v___x_133_);
v___x_228_ = v___x_224_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_133_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_232_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_232_, 3, v_r_220_);
lean_ctor_set(v_reuseFailAlloc_232_, 4, v_r_220_);
v___x_228_ = v_reuseFailAlloc_232_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_230_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v___x_228_);
lean_ctor_set(v___x_129_, 3, v_l_219_);
lean_ctor_set(v___x_129_, 2, v_v_222_);
lean_ctor_set(v___x_129_, 1, v_k_221_);
lean_ctor_set(v___x_129_, 0, v___x_226_);
v___x_230_ = v___x_129_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_226_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v_k_221_);
lean_ctor_set(v_reuseFailAlloc_231_, 2, v_v_222_);
lean_ctor_set(v_reuseFailAlloc_231_, 3, v_l_219_);
lean_ctor_set(v_reuseFailAlloc_231_, 4, v___x_228_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
else
{
lean_object* v_r_236_; 
v_r_236_ = lean_ctor_get(v_impl_132_, 4);
lean_inc(v_r_236_);
if (lean_obj_tag(v_r_236_) == 0)
{
lean_object* v_k_237_; lean_object* v_v_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_261_; 
lean_inc(v_l_219_);
v_k_237_ = lean_ctor_get(v_impl_132_, 1);
v_v_238_ = lean_ctor_get(v_impl_132_, 2);
v_isSharedCheck_261_ = !lean_is_exclusive(v_impl_132_);
if (v_isSharedCheck_261_ == 0)
{
lean_object* v_unused_262_; lean_object* v_unused_263_; lean_object* v_unused_264_; 
v_unused_262_ = lean_ctor_get(v_impl_132_, 4);
lean_dec(v_unused_262_);
v_unused_263_ = lean_ctor_get(v_impl_132_, 3);
lean_dec(v_unused_263_);
v_unused_264_ = lean_ctor_get(v_impl_132_, 0);
lean_dec(v_unused_264_);
v___x_240_ = v_impl_132_;
v_isShared_241_ = v_isSharedCheck_261_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_v_238_);
lean_inc(v_k_237_);
lean_dec(v_impl_132_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_261_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v_k_242_; lean_object* v_v_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_257_; 
v_k_242_ = lean_ctor_get(v_r_236_, 1);
v_v_243_ = lean_ctor_get(v_r_236_, 2);
v_isSharedCheck_257_ = !lean_is_exclusive(v_r_236_);
if (v_isSharedCheck_257_ == 0)
{
lean_object* v_unused_258_; lean_object* v_unused_259_; lean_object* v_unused_260_; 
v_unused_258_ = lean_ctor_get(v_r_236_, 4);
lean_dec(v_unused_258_);
v_unused_259_ = lean_ctor_get(v_r_236_, 3);
lean_dec(v_unused_259_);
v_unused_260_ = lean_ctor_get(v_r_236_, 0);
lean_dec(v_unused_260_);
v___x_245_ = v_r_236_;
v_isShared_246_ = v_isSharedCheck_257_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_v_243_);
lean_inc(v_k_242_);
lean_dec(v_r_236_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_257_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_247_ = lean_unsigned_to_nat(3u);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 4, v_l_219_);
lean_ctor_set(v___x_245_, 3, v_l_219_);
lean_ctor_set(v___x_245_, 2, v_v_238_);
lean_ctor_set(v___x_245_, 1, v_k_237_);
lean_ctor_set(v___x_245_, 0, v___x_133_);
v___x_249_ = v___x_245_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_133_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_k_237_);
lean_ctor_set(v_reuseFailAlloc_256_, 2, v_v_238_);
lean_ctor_set(v_reuseFailAlloc_256_, 3, v_l_219_);
lean_ctor_set(v_reuseFailAlloc_256_, 4, v_l_219_);
v___x_249_ = v_reuseFailAlloc_256_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v___x_251_; 
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 4, v_l_219_);
lean_ctor_set(v___x_240_, 2, v_v_125_);
lean_ctor_set(v___x_240_, 1, v_k_124_);
lean_ctor_set(v___x_240_, 0, v___x_133_);
v___x_251_ = v___x_240_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_133_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_255_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_255_, 3, v_l_219_);
lean_ctor_set(v_reuseFailAlloc_255_, 4, v_l_219_);
v___x_251_ = v_reuseFailAlloc_255_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_253_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v___x_251_);
lean_ctor_set(v___x_129_, 3, v___x_249_);
lean_ctor_set(v___x_129_, 2, v_v_243_);
lean_ctor_set(v___x_129_, 1, v_k_242_);
lean_ctor_set(v___x_129_, 0, v___x_247_);
v___x_253_ = v___x_129_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_k_242_);
lean_ctor_set(v_reuseFailAlloc_254_, 2, v_v_243_);
lean_ctor_set(v_reuseFailAlloc_254_, 3, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_254_, 4, v___x_251_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
}
}
else
{
lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_265_ = lean_unsigned_to_nat(2u);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v_r_236_);
lean_ctor_set(v___x_129_, 3, v_impl_132_);
lean_ctor_set(v___x_129_, 0, v___x_265_);
v___x_267_ = v___x_129_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_265_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_268_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_268_, 3, v_impl_132_);
lean_ctor_set(v_reuseFailAlloc_268_, 4, v_r_236_);
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
}
case 1:
{
lean_object* v___x_270_; 
lean_dec(v_v_125_);
lean_dec(v_k_124_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 2, v_v_121_);
lean_ctor_set(v___x_129_, 1, v_k_120_);
v___x_270_ = v___x_129_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_size_123_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_k_120_);
lean_ctor_set(v_reuseFailAlloc_271_, 2, v_v_121_);
lean_ctor_set(v_reuseFailAlloc_271_, 3, v_l_126_);
lean_ctor_set(v_reuseFailAlloc_271_, 4, v_r_127_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
default: 
{
lean_object* v_impl_272_; lean_object* v___x_273_; 
lean_dec(v_size_123_);
v_impl_272_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__3___redArg(v_k_120_, v_v_121_, v_r_127_);
v___x_273_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_126_) == 0)
{
lean_object* v_size_274_; lean_object* v_size_275_; lean_object* v_k_276_; lean_object* v_v_277_; lean_object* v_l_278_; lean_object* v_r_279_; lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v_size_274_ = lean_ctor_get(v_l_126_, 0);
v_size_275_ = lean_ctor_get(v_impl_272_, 0);
v_k_276_ = lean_ctor_get(v_impl_272_, 1);
v_v_277_ = lean_ctor_get(v_impl_272_, 2);
v_l_278_ = lean_ctor_get(v_impl_272_, 3);
lean_inc(v_l_278_);
v_r_279_ = lean_ctor_get(v_impl_272_, 4);
v___x_280_ = lean_unsigned_to_nat(3u);
v___x_281_ = lean_nat_mul(v___x_280_, v_size_274_);
v___x_282_ = lean_nat_dec_lt(v___x_281_, v_size_275_);
lean_dec(v___x_281_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_286_; 
lean_dec(v_l_278_);
v___x_283_ = lean_nat_add(v___x_273_, v_size_274_);
v___x_284_ = lean_nat_add(v___x_283_, v_size_275_);
lean_dec(v___x_283_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v_impl_272_);
lean_ctor_set(v___x_129_, 0, v___x_284_);
v___x_286_ = v___x_129_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_287_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_287_, 3, v_l_126_);
lean_ctor_set(v_reuseFailAlloc_287_, 4, v_impl_272_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
else
{
lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_351_; 
lean_inc(v_r_279_);
lean_inc(v_v_277_);
lean_inc(v_k_276_);
lean_inc(v_size_275_);
v_isSharedCheck_351_ = !lean_is_exclusive(v_impl_272_);
if (v_isSharedCheck_351_ == 0)
{
lean_object* v_unused_352_; lean_object* v_unused_353_; lean_object* v_unused_354_; lean_object* v_unused_355_; lean_object* v_unused_356_; 
v_unused_352_ = lean_ctor_get(v_impl_272_, 4);
lean_dec(v_unused_352_);
v_unused_353_ = lean_ctor_get(v_impl_272_, 3);
lean_dec(v_unused_353_);
v_unused_354_ = lean_ctor_get(v_impl_272_, 2);
lean_dec(v_unused_354_);
v_unused_355_ = lean_ctor_get(v_impl_272_, 1);
lean_dec(v_unused_355_);
v_unused_356_ = lean_ctor_get(v_impl_272_, 0);
lean_dec(v_unused_356_);
v___x_289_ = v_impl_272_;
v_isShared_290_ = v_isSharedCheck_351_;
goto v_resetjp_288_;
}
else
{
lean_dec(v_impl_272_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_351_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v_size_291_; lean_object* v_k_292_; lean_object* v_v_293_; lean_object* v_l_294_; lean_object* v_r_295_; lean_object* v_size_296_; lean_object* v___x_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v_size_291_ = lean_ctor_get(v_l_278_, 0);
v_k_292_ = lean_ctor_get(v_l_278_, 1);
v_v_293_ = lean_ctor_get(v_l_278_, 2);
v_l_294_ = lean_ctor_get(v_l_278_, 3);
v_r_295_ = lean_ctor_get(v_l_278_, 4);
v_size_296_ = lean_ctor_get(v_r_279_, 0);
v___x_297_ = lean_unsigned_to_nat(2u);
v___x_298_ = lean_nat_mul(v___x_297_, v_size_296_);
v___x_299_ = lean_nat_dec_lt(v_size_291_, v___x_298_);
lean_dec(v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_327_; 
lean_inc(v_r_295_);
lean_inc(v_l_294_);
lean_inc(v_v_293_);
lean_inc(v_k_292_);
v_isSharedCheck_327_ = !lean_is_exclusive(v_l_278_);
if (v_isSharedCheck_327_ == 0)
{
lean_object* v_unused_328_; lean_object* v_unused_329_; lean_object* v_unused_330_; lean_object* v_unused_331_; lean_object* v_unused_332_; 
v_unused_328_ = lean_ctor_get(v_l_278_, 4);
lean_dec(v_unused_328_);
v_unused_329_ = lean_ctor_get(v_l_278_, 3);
lean_dec(v_unused_329_);
v_unused_330_ = lean_ctor_get(v_l_278_, 2);
lean_dec(v_unused_330_);
v_unused_331_ = lean_ctor_get(v_l_278_, 1);
lean_dec(v_unused_331_);
v_unused_332_ = lean_ctor_get(v_l_278_, 0);
lean_dec(v_unused_332_);
v___x_301_ = v_l_278_;
v_isShared_302_ = v_isSharedCheck_327_;
goto v_resetjp_300_;
}
else
{
lean_dec(v_l_278_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_327_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___y_306_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_317_; 
v___x_303_ = lean_nat_add(v___x_273_, v_size_274_);
v___x_304_ = lean_nat_add(v___x_303_, v_size_275_);
lean_dec(v_size_275_);
if (lean_obj_tag(v_l_294_) == 0)
{
lean_object* v_size_325_; 
v_size_325_ = lean_ctor_get(v_l_294_, 0);
lean_inc(v_size_325_);
v___y_317_ = v_size_325_;
goto v___jp_316_;
}
else
{
lean_object* v___x_326_; 
v___x_326_ = lean_unsigned_to_nat(0u);
v___y_317_ = v___x_326_;
goto v___jp_316_;
}
v___jp_305_:
{
lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_309_ = lean_nat_add(v___y_306_, v___y_308_);
lean_dec(v___y_308_);
lean_dec(v___y_306_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 4, v_r_279_);
lean_ctor_set(v___x_301_, 3, v_r_295_);
lean_ctor_set(v___x_301_, 2, v_v_277_);
lean_ctor_set(v___x_301_, 1, v_k_276_);
lean_ctor_set(v___x_301_, 0, v___x_309_);
v___x_311_ = v___x_301_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_309_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_k_276_);
lean_ctor_set(v_reuseFailAlloc_315_, 2, v_v_277_);
lean_ctor_set(v_reuseFailAlloc_315_, 3, v_r_295_);
lean_ctor_set(v_reuseFailAlloc_315_, 4, v_r_279_);
v___x_311_ = v_reuseFailAlloc_315_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_313_; 
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 4, v___x_311_);
lean_ctor_set(v___x_289_, 3, v___y_307_);
lean_ctor_set(v___x_289_, 2, v_v_293_);
lean_ctor_set(v___x_289_, 1, v_k_292_);
lean_ctor_set(v___x_289_, 0, v___x_304_);
v___x_313_ = v___x_289_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_304_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v_k_292_);
lean_ctor_set(v_reuseFailAlloc_314_, 2, v_v_293_);
lean_ctor_set(v_reuseFailAlloc_314_, 3, v___y_307_);
lean_ctor_set(v_reuseFailAlloc_314_, 4, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
v___jp_316_:
{
lean_object* v___x_318_; lean_object* v___x_320_; 
v___x_318_ = lean_nat_add(v___x_303_, v___y_317_);
lean_dec(v___y_317_);
lean_dec(v___x_303_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v_l_294_);
lean_ctor_set(v___x_129_, 0, v___x_318_);
v___x_320_ = v___x_129_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_318_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_324_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_324_, 3, v_l_126_);
lean_ctor_set(v_reuseFailAlloc_324_, 4, v_l_294_);
v___x_320_ = v_reuseFailAlloc_324_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_321_; 
v___x_321_ = lean_nat_add(v___x_273_, v_size_296_);
if (lean_obj_tag(v_r_295_) == 0)
{
lean_object* v_size_322_; 
v_size_322_ = lean_ctor_get(v_r_295_, 0);
lean_inc(v_size_322_);
v___y_306_ = v___x_321_;
v___y_307_ = v___x_320_;
v___y_308_ = v_size_322_;
goto v___jp_305_;
}
else
{
lean_object* v___x_323_; 
v___x_323_ = lean_unsigned_to_nat(0u);
v___y_306_ = v___x_321_;
v___y_307_ = v___x_320_;
v___y_308_ = v___x_323_;
goto v___jp_305_;
}
}
}
}
}
else
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_337_; 
lean_del_object(v___x_129_);
v___x_333_ = lean_nat_add(v___x_273_, v_size_274_);
v___x_334_ = lean_nat_add(v___x_333_, v_size_275_);
lean_dec(v_size_275_);
v___x_335_ = lean_nat_add(v___x_333_, v_size_291_);
lean_dec(v___x_333_);
lean_inc_ref(v_l_126_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 4, v_l_278_);
lean_ctor_set(v___x_289_, 3, v_l_126_);
lean_ctor_set(v___x_289_, 2, v_v_125_);
lean_ctor_set(v___x_289_, 1, v_k_124_);
lean_ctor_set(v___x_289_, 0, v___x_335_);
v___x_337_ = v___x_289_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_335_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_350_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_350_, 3, v_l_126_);
lean_ctor_set(v_reuseFailAlloc_350_, 4, v_l_278_);
v___x_337_ = v_reuseFailAlloc_350_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
v_isSharedCheck_344_ = !lean_is_exclusive(v_l_126_);
if (v_isSharedCheck_344_ == 0)
{
lean_object* v_unused_345_; lean_object* v_unused_346_; lean_object* v_unused_347_; lean_object* v_unused_348_; lean_object* v_unused_349_; 
v_unused_345_ = lean_ctor_get(v_l_126_, 4);
lean_dec(v_unused_345_);
v_unused_346_ = lean_ctor_get(v_l_126_, 3);
lean_dec(v_unused_346_);
v_unused_347_ = lean_ctor_get(v_l_126_, 2);
lean_dec(v_unused_347_);
v_unused_348_ = lean_ctor_get(v_l_126_, 1);
lean_dec(v_unused_348_);
v_unused_349_ = lean_ctor_get(v_l_126_, 0);
lean_dec(v_unused_349_);
v___x_339_ = v_l_126_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_dec(v_l_126_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 4, v_r_279_);
lean_ctor_set(v___x_339_, 3, v___x_337_);
lean_ctor_set(v___x_339_, 2, v_v_277_);
lean_ctor_set(v___x_339_, 1, v_k_276_);
lean_ctor_set(v___x_339_, 0, v___x_334_);
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_334_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_k_276_);
lean_ctor_set(v_reuseFailAlloc_343_, 2, v_v_277_);
lean_ctor_set(v_reuseFailAlloc_343_, 3, v___x_337_);
lean_ctor_set(v_reuseFailAlloc_343_, 4, v_r_279_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_357_; 
v_l_357_ = lean_ctor_get(v_impl_272_, 3);
lean_inc(v_l_357_);
if (lean_obj_tag(v_l_357_) == 0)
{
lean_object* v_r_358_; lean_object* v_k_359_; lean_object* v_v_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_383_; 
v_r_358_ = lean_ctor_get(v_impl_272_, 4);
v_k_359_ = lean_ctor_get(v_impl_272_, 1);
v_v_360_ = lean_ctor_get(v_impl_272_, 2);
v_isSharedCheck_383_ = !lean_is_exclusive(v_impl_272_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; lean_object* v_unused_385_; 
v_unused_384_ = lean_ctor_get(v_impl_272_, 3);
lean_dec(v_unused_384_);
v_unused_385_ = lean_ctor_get(v_impl_272_, 0);
lean_dec(v_unused_385_);
v___x_362_ = v_impl_272_;
v_isShared_363_ = v_isSharedCheck_383_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_r_358_);
lean_inc(v_v_360_);
lean_inc(v_k_359_);
lean_dec(v_impl_272_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_383_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v_k_364_; lean_object* v_v_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_379_; 
v_k_364_ = lean_ctor_get(v_l_357_, 1);
v_v_365_ = lean_ctor_get(v_l_357_, 2);
v_isSharedCheck_379_ = !lean_is_exclusive(v_l_357_);
if (v_isSharedCheck_379_ == 0)
{
lean_object* v_unused_380_; lean_object* v_unused_381_; lean_object* v_unused_382_; 
v_unused_380_ = lean_ctor_get(v_l_357_, 4);
lean_dec(v_unused_380_);
v_unused_381_ = lean_ctor_get(v_l_357_, 3);
lean_dec(v_unused_381_);
v_unused_382_ = lean_ctor_get(v_l_357_, 0);
lean_dec(v_unused_382_);
v___x_367_ = v_l_357_;
v_isShared_368_ = v_isSharedCheck_379_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_v_365_);
lean_inc(v_k_364_);
lean_dec(v_l_357_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_379_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_369_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_358_, 2);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 4, v_r_358_);
lean_ctor_set(v___x_367_, 3, v_r_358_);
lean_ctor_set(v___x_367_, 2, v_v_125_);
lean_ctor_set(v___x_367_, 1, v_k_124_);
lean_ctor_set(v___x_367_, 0, v___x_273_);
v___x_371_ = v___x_367_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_378_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_378_, 3, v_r_358_);
lean_ctor_set(v_reuseFailAlloc_378_, 4, v_r_358_);
v___x_371_ = v_reuseFailAlloc_378_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_373_; 
lean_inc(v_r_358_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 3, v_r_358_);
lean_ctor_set(v___x_362_, 0, v___x_273_);
v___x_373_ = v___x_362_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_k_359_);
lean_ctor_set(v_reuseFailAlloc_377_, 2, v_v_360_);
lean_ctor_set(v_reuseFailAlloc_377_, 3, v_r_358_);
lean_ctor_set(v_reuseFailAlloc_377_, 4, v_r_358_);
v___x_373_ = v_reuseFailAlloc_377_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_375_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v___x_373_);
lean_ctor_set(v___x_129_, 3, v___x_371_);
lean_ctor_set(v___x_129_, 2, v_v_365_);
lean_ctor_set(v___x_129_, 1, v_k_364_);
lean_ctor_set(v___x_129_, 0, v___x_369_);
v___x_375_ = v___x_129_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_369_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_k_364_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v_v_365_);
lean_ctor_set(v_reuseFailAlloc_376_, 3, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_376_, 4, v___x_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
}
}
else
{
lean_object* v_r_386_; 
v_r_386_ = lean_ctor_get(v_impl_272_, 4);
lean_inc(v_r_386_);
if (lean_obj_tag(v_r_386_) == 0)
{
lean_object* v_k_387_; lean_object* v_v_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_399_; 
v_k_387_ = lean_ctor_get(v_impl_272_, 1);
v_v_388_ = lean_ctor_get(v_impl_272_, 2);
v_isSharedCheck_399_ = !lean_is_exclusive(v_impl_272_);
if (v_isSharedCheck_399_ == 0)
{
lean_object* v_unused_400_; lean_object* v_unused_401_; lean_object* v_unused_402_; 
v_unused_400_ = lean_ctor_get(v_impl_272_, 4);
lean_dec(v_unused_400_);
v_unused_401_ = lean_ctor_get(v_impl_272_, 3);
lean_dec(v_unused_401_);
v_unused_402_ = lean_ctor_get(v_impl_272_, 0);
lean_dec(v_unused_402_);
v___x_390_ = v_impl_272_;
v_isShared_391_ = v_isSharedCheck_399_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_v_388_);
lean_inc(v_k_387_);
lean_dec(v_impl_272_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_399_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_392_ = lean_unsigned_to_nat(3u);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 4, v_l_357_);
lean_ctor_set(v___x_390_, 2, v_v_125_);
lean_ctor_set(v___x_390_, 1, v_k_124_);
lean_ctor_set(v___x_390_, 0, v___x_273_);
v___x_394_ = v___x_390_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_398_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_398_, 3, v_l_357_);
lean_ctor_set(v_reuseFailAlloc_398_, 4, v_l_357_);
v___x_394_ = v_reuseFailAlloc_398_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_396_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v_r_386_);
lean_ctor_set(v___x_129_, 3, v___x_394_);
lean_ctor_set(v___x_129_, 2, v_v_388_);
lean_ctor_set(v___x_129_, 1, v_k_387_);
lean_ctor_set(v___x_129_, 0, v___x_392_);
v___x_396_ = v___x_129_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_k_387_);
lean_ctor_set(v_reuseFailAlloc_397_, 2, v_v_388_);
lean_ctor_set(v_reuseFailAlloc_397_, 3, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_397_, 4, v_r_386_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
else
{
lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_403_ = lean_unsigned_to_nat(2u);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v_impl_272_);
lean_ctor_set(v___x_129_, 3, v_r_386_);
lean_ctor_set(v___x_129_, 0, v___x_403_);
v___x_405_ = v___x_129_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_406_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_406_, 3, v_r_386_);
lean_ctor_set(v_reuseFailAlloc_406_, 4, v_impl_272_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
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
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_unsigned_to_nat(1u);
v___x_409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v_k_120_);
lean_ctor_set(v___x_409_, 2, v_v_121_);
lean_ctor_set(v___x_409_, 3, v_t_122_);
lean_ctor_set(v___x_409_, 4, v_t_122_);
return v___x_409_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__2___redArg(lean_object* v_k_410_, lean_object* v_t_411_){
_start:
{
if (lean_obj_tag(v_t_411_) == 0)
{
lean_object* v_k_412_; lean_object* v_l_413_; lean_object* v_r_414_; uint8_t v___x_415_; 
v_k_412_ = lean_ctor_get(v_t_411_, 1);
v_l_413_ = lean_ctor_get(v_t_411_, 3);
v_r_414_ = lean_ctor_get(v_t_411_, 4);
v___x_415_ = l_Lake_BuildKey_quickCmp(v_k_410_, v_k_412_);
switch(v___x_415_)
{
case 0:
{
v_t_411_ = v_l_413_;
goto _start;
}
case 1:
{
uint8_t v___x_417_; 
v___x_417_ = 1;
return v___x_417_;
}
default: 
{
v_t_411_ = v_r_414_;
goto _start;
}
}
}
else
{
uint8_t v___x_419_; 
v___x_419_ = 0;
return v___x_419_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__2___redArg___boxed(lean_object* v_k_420_, lean_object* v_t_421_){
_start:
{
uint8_t v_res_422_; lean_object* v_r_423_; 
v_res_422_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__2___redArg(v_k_420_, v_t_421_);
lean_dec(v_t_421_);
lean_dec_ref(v_k_420_);
v_r_423_ = lean_box(v_res_422_);
return v_r_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__1(lean_object* v_key_424_, lean_object* v_a_425_, lean_object* v_x_426_){
_start:
{
lean_object* v___x_428_; lean_object* v_fst_430_; lean_object* v_snd_431_; lean_object* v___x_433_; 
v___x_428_ = lean_st_ref_take(v_x_426_);
v___x_433_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg(v___x_428_, v_key_424_);
if (lean_obj_tag(v___x_433_) == 0)
{
uint8_t v___x_434_; 
v___x_434_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__2___redArg(v_key_424_, v___x_428_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; 
lean_inc_ref(v_a_425_);
v___x_435_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__3___redArg(v_key_424_, v_a_425_, v___x_428_);
v_fst_430_ = v_a_425_;
v_snd_431_ = v___x_435_;
goto v___jp_429_;
}
else
{
lean_dec_ref(v_key_424_);
v_fst_430_ = v_a_425_;
v_snd_431_ = v___x_428_;
goto v___jp_429_;
}
}
else
{
lean_object* v_val_436_; 
lean_dec_ref(v_a_425_);
lean_dec_ref(v_key_424_);
v_val_436_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_val_436_);
lean_dec_ref_known(v___x_433_, 1);
v_fst_430_ = v_val_436_;
v_snd_431_ = v___x_428_;
goto v___jp_429_;
}
v___jp_429_:
{
lean_object* v___x_432_; 
v___x_432_ = lean_st_ref_put(v_x_426_, v_snd_431_);
return v_fst_430_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__1___boxed(lean_object* v_key_437_, lean_object* v_a_438_, lean_object* v_x_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__1(v_key_437_, v_a_438_, v_x_439_);
lean_dec(v_x_439_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__2(lean_object* v___x_442_, lean_object* v_ref_443_){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_st_ref_get(v_ref_443_);
v___x_446_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg(v___x_445_, v___x_442_);
lean_dec(v___x_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__2___boxed(lean_object* v___x_447_, lean_object* v_ref_448_, lean_object* v___y_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__2(v___x_447_, v_ref_448_);
lean_dec(v_ref_448_);
lean_dec_ref(v___x_447_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__3(lean_object* v___x_451_, lean_object* v_a_452_, lean_object* v_x_453_){
_start:
{
lean_object* v___x_455_; lean_object* v_fst_457_; lean_object* v_snd_458_; lean_object* v___x_460_; 
v___x_455_ = lean_st_ref_take(v_x_453_);
v___x_460_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg(v___x_455_, v___x_451_);
if (lean_obj_tag(v___x_460_) == 0)
{
uint8_t v___x_461_; 
v___x_461_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__2___redArg(v___x_451_, v___x_455_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; 
lean_inc_ref(v_a_452_);
v___x_462_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__3___redArg(v___x_451_, v_a_452_, v___x_455_);
v_fst_457_ = v_a_452_;
v_snd_458_ = v___x_462_;
goto v___jp_456_;
}
else
{
lean_dec_ref(v___x_451_);
v_fst_457_ = v_a_452_;
v_snd_458_ = v___x_455_;
goto v___jp_456_;
}
}
else
{
lean_object* v_val_463_; 
lean_dec_ref(v_a_452_);
lean_dec_ref(v___x_451_);
v_val_463_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_val_463_);
lean_dec_ref_known(v___x_460_, 1);
v_fst_457_ = v_val_463_;
v_snd_458_ = v___x_455_;
goto v___jp_456_;
}
v___jp_456_:
{
lean_object* v___x_459_; 
v___x_459_ = lean_st_ref_put(v_x_453_, v_snd_458_);
return v_fst_457_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__3___boxed(lean_object* v___x_464_, lean_object* v_a_465_, lean_object* v_x_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__3(v___x_464_, v_a_465_, v_x_466_);
lean_dec(v_x_466_);
return v_res_468_;
}
}
static lean_object* _init_l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__3(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__2));
v___x_474_ = l_Lake_BuildTrace_nil(v___x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex(lean_object* v_info_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
if (lean_obj_tag(v_info_481_) == 0)
{
lean_object* v_package_489_; lean_object* v_target_490_; lean_object* v___x_491_; 
v_package_489_ = lean_ctor_get(v_info_481_, 0);
v_target_490_ = lean_ctor_get(v_info_481_, 1);
v___x_491_ = l_Lake_Package_findTargetDecl_x3f(v_target_490_, v_package_489_);
if (lean_obj_tag(v___x_491_) == 1)
{
lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_541_; 
lean_inc(v_target_490_);
lean_inc_ref(v_package_489_);
v_isSharedCheck_541_ = !lean_is_exclusive(v_info_481_);
if (v_isSharedCheck_541_ == 0)
{
lean_object* v_unused_542_; lean_object* v_unused_543_; 
v_unused_542_ = lean_ctor_get(v_info_481_, 1);
lean_dec(v_unused_542_);
v_unused_543_ = lean_ctor_get(v_info_481_, 0);
lean_dec(v_unused_543_);
v___x_493_ = v_info_481_;
v_isShared_494_ = v_isSharedCheck_541_;
goto v_resetjp_492_;
}
else
{
lean_dec(v_info_481_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_541_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v_val_495_; lean_object* v_name_496_; lean_object* v_kind_497_; lean_object* v_config_498_; uint8_t v___x_499_; 
v_val_495_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_val_495_);
lean_dec_ref_known(v___x_491_, 1);
v_name_496_ = lean_ctor_get(v_val_495_, 1);
lean_inc(v_name_496_);
v_kind_497_ = lean_ctor_get(v_val_495_, 2);
lean_inc(v_kind_497_);
v_config_498_ = lean_ctor_get(v_val_495_, 3);
lean_inc(v_config_498_);
lean_dec(v_val_495_);
v___x_499_ = l_Lean_Name_isAnonymous(v_kind_497_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; uint8_t v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_508_; 
lean_dec(v_target_490_);
lean_dec_ref(v_a_482_);
v___x_500_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_500_, 0, v_package_489_);
lean_ctor_set(v___x_500_, 1, v_name_496_);
lean_ctor_set(v___x_500_, 2, v_config_498_);
v___x_501_ = lean_unsigned_to_nat(0u);
v___x_502_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__0));
v___x_503_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__1));
v___x_504_ = 0;
v___x_505_ = lean_obj_once(&l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__3, &l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__3_once, _init_l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__3);
v___x_506_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_506_, 0, v___x_502_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
lean_ctor_set(v___x_506_, 2, v___x_501_);
lean_ctor_set_uint8(v___x_506_, sizeof(void*)*3, v___x_504_);
lean_ctor_set_uint8(v___x_506_, sizeof(void*)*3 + 1, v___x_499_);
lean_ctor_set_uint8(v___x_506_, sizeof(void*)*3 + 2, v___x_499_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 1, v___x_506_);
lean_ctor_set(v___x_493_, 0, v___x_500_);
v___x_508_ = v___x_493_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_500_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v___x_506_);
v___x_508_ = v_reuseFailAlloc_512_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_509_; lean_object* v_job_510_; lean_object* v___x_511_; 
v___x_509_ = lean_task_pure(v___x_508_);
v_job_510_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_510_, 0, v___x_509_);
lean_ctor_set(v_job_510_, 1, v_kind_497_);
lean_ctor_set(v_job_510_, 2, v___x_503_);
lean_ctor_set_uint8(v_job_510_, sizeof(void*)*3, v___x_499_);
v___x_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_511_, 0, v_job_510_);
lean_ctor_set(v___x_511_, 1, v_a_487_);
return v___x_511_;
}
}
else
{
lean_object* v_keyName_513_; lean_object* v_fetchFn_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_539_; 
lean_dec(v_kind_497_);
lean_dec(v_name_496_);
v_keyName_513_ = lean_ctor_get(v_package_489_, 2);
v_fetchFn_514_ = lean_ctor_get(v_config_498_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v_config_498_);
if (v_isSharedCheck_539_ == 0)
{
lean_object* v_unused_540_; 
v_unused_540_ = lean_ctor_get(v_config_498_, 1);
lean_dec(v_unused_540_);
v___x_516_ = v_config_498_;
v_isShared_517_ = v_isSharedCheck_539_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_fetchFn_514_);
lean_dec(v_config_498_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_539_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v_key_519_; 
lean_inc(v_keyName_513_);
if (v_isShared_517_ == 0)
{
lean_ctor_set_tag(v___x_516_, 3);
lean_ctor_set(v___x_516_, 1, v_target_490_);
lean_ctor_set(v___x_516_, 0, v_keyName_513_);
v_key_519_ = v___x_516_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_keyName_513_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_target_490_);
v_key_519_ = v_reuseFailAlloc_538_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
lean_object* v___f_520_; lean_object* v___x_521_; 
lean_inc_ref(v_key_519_);
v___f_520_ = lean_alloc_closure((void*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__0___boxed), 3, 1);
lean_closure_set(v___f_520_, 0, v_key_519_);
lean_inc_ref(v_a_485_);
v___x_521_ = l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(v_a_485_, v___f_520_);
if (lean_obj_tag(v___x_521_) == 1)
{
lean_object* v_val_522_; lean_object* v___x_524_; 
lean_dec_ref(v_key_519_);
lean_dec_ref(v_fetchFn_514_);
lean_dec_ref(v_package_489_);
lean_dec_ref(v_a_482_);
v_val_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_val_522_);
lean_dec_ref_known(v___x_521_, 1);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 1, v_a_487_);
lean_ctor_set(v___x_493_, 0, v_val_522_);
v___x_524_ = v___x_493_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_val_522_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v_a_487_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
else
{
lean_object* v___x_526_; 
lean_dec(v___x_521_);
lean_del_object(v___x_493_);
lean_inc_ref(v_a_486_);
lean_inc_ref(v_a_485_);
lean_inc(v_a_484_);
lean_inc(v_a_483_);
v___x_526_ = lean_apply_8(v_fetchFn_514_, v_package_489_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, lean_box(0));
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_537_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
v_a_528_ = lean_ctor_get(v___x_526_, 1);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_537_ == 0)
{
v___x_530_ = v___x_526_;
v_isShared_531_ = v_isSharedCheck_537_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_inc(v_a_527_);
lean_dec(v___x_526_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_537_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___f_532_; lean_object* v___x_533_; lean_object* v___x_535_; 
v___f_532_ = lean_alloc_closure((void*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__1___boxed), 4, 2);
lean_closure_set(v___f_532_, 0, v_key_519_);
lean_closure_set(v___f_532_, 1, v_a_527_);
lean_inc_ref(v_a_485_);
v___x_533_ = l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(v_a_485_, v___f_532_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_533_);
v___x_535_ = v___x_530_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v_a_528_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
else
{
lean_dec_ref(v_key_519_);
return v___x_526_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
lean_dec(v___x_491_);
lean_dec_ref(v_a_482_);
v___x_544_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__4));
v___x_545_ = l_Lake_BuildInfo_key(v_info_481_);
v___x_546_ = l_Lake_BuildKey_toString(v___x_545_);
v___x_547_ = lean_string_append(v___x_544_, v___x_546_);
lean_dec_ref(v___x_546_);
v___x_548_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__5));
v___x_549_ = lean_string_append(v___x_547_, v___x_548_);
v___x_550_ = 3;
v___x_551_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_551_, 0, v___x_549_);
lean_ctor_set_uint8(v___x_551_, sizeof(void*)*1, v___x_550_);
v___x_552_ = lean_array_get_size(v_a_487_);
v___x_553_ = lean_array_push(v_a_487_, v___x_551_);
v___x_554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_552_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
return v___x_554_;
}
}
else
{
lean_object* v_toContext_555_; lean_object* v_target_556_; lean_object* v_kind_557_; lean_object* v_data_558_; lean_object* v_facet_559_; lean_object* v_facetConfigs_560_; lean_object* v___x_561_; 
v_toContext_555_ = lean_ctor_get(v_a_486_, 1);
v_target_556_ = lean_ctor_get(v_info_481_, 0);
v_kind_557_ = lean_ctor_get(v_info_481_, 1);
v_data_558_ = lean_ctor_get(v_info_481_, 2);
v_facet_559_ = lean_ctor_get(v_info_481_, 3);
v_facetConfigs_560_ = lean_ctor_get(v_toContext_555_, 6);
v___x_561_ = l_Lake_FacetConfigMap_get_x3f(v_facet_559_, v_facetConfigs_560_);
if (lean_obj_tag(v___x_561_) == 1)
{
lean_object* v_val_562_; lean_object* v_kind_563_; lean_object* v_fetchFn_564_; uint8_t v_memoize_565_; uint8_t v___x_566_; 
lean_inc(v_kind_557_);
v_val_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_val_562_);
lean_dec_ref_known(v___x_561_, 1);
v_kind_563_ = lean_ctor_get(v_val_562_, 0);
lean_inc(v_kind_563_);
v_fetchFn_564_ = lean_ctor_get(v_val_562_, 1);
lean_inc_ref(v_fetchFn_564_);
v_memoize_565_ = lean_ctor_get_uint8(v_val_562_, sizeof(void*)*4 + 1);
lean_dec(v_val_562_);
v___x_566_ = lean_name_eq(v_kind_563_, v_kind_557_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; uint8_t v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
lean_dec_ref(v_fetchFn_564_);
lean_dec_ref(v_a_482_);
v___x_567_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__4));
v___x_568_ = l_Lake_BuildInfo_key(v_info_481_);
v___x_569_ = l_Lake_BuildKey_toString(v___x_568_);
v___x_570_ = lean_string_append(v___x_567_, v___x_569_);
lean_dec_ref(v___x_569_);
v___x_571_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__6));
v___x_572_ = lean_string_append(v___x_570_, v___x_571_);
v___x_573_ = 1;
v___x_574_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_557_, v___x_573_);
v___x_575_ = lean_string_append(v___x_572_, v___x_574_);
lean_dec_ref(v___x_574_);
v___x_576_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__7));
v___x_577_ = lean_string_append(v___x_575_, v___x_576_);
v___x_578_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_563_, v___x_573_);
v___x_579_ = lean_string_append(v___x_577_, v___x_578_);
lean_dec_ref(v___x_578_);
v___x_580_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__8));
v___x_581_ = lean_string_append(v___x_579_, v___x_580_);
v___x_582_ = 3;
v___x_583_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_583_, 0, v___x_581_);
lean_ctor_set_uint8(v___x_583_, sizeof(void*)*1, v___x_582_);
v___x_584_ = lean_array_get_size(v_a_487_);
v___x_585_ = lean_array_push(v_a_487_, v___x_583_);
v___x_586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_584_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
return v___x_586_;
}
else
{
lean_inc(v_facet_559_);
lean_inc(v_data_558_);
lean_inc_ref(v_target_556_);
lean_dec(v_kind_563_);
lean_dec(v_kind_557_);
lean_dec_ref_known(v_info_481_, 4);
if (v_memoize_565_ == 0)
{
lean_object* v___x_587_; 
lean_dec(v_facet_559_);
lean_dec_ref(v_target_556_);
lean_inc_ref(v_a_486_);
lean_inc_ref(v_a_485_);
lean_inc(v_a_484_);
lean_inc(v_a_483_);
v___x_587_ = lean_apply_8(v_fetchFn_564_, v_data_558_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, lean_box(0));
return v___x_587_;
}
else
{
lean_object* v___x_588_; lean_object* v___f_589_; lean_object* v___x_590_; 
v___x_588_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_588_, 0, v_target_556_);
lean_ctor_set(v___x_588_, 1, v_facet_559_);
lean_inc_ref(v___x_588_);
v___f_589_ = lean_alloc_closure((void*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__2___boxed), 3, 1);
lean_closure_set(v___f_589_, 0, v___x_588_);
lean_inc_ref(v_a_485_);
v___x_590_ = l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(v_a_485_, v___f_589_);
if (lean_obj_tag(v___x_590_) == 1)
{
lean_object* v_val_591_; lean_object* v___x_592_; 
lean_dec_ref_known(v___x_588_, 2);
lean_dec_ref(v_fetchFn_564_);
lean_dec(v_data_558_);
lean_dec_ref(v_a_482_);
v_val_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_val_591_);
lean_dec_ref_known(v___x_590_, 1);
v___x_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_592_, 0, v_val_591_);
lean_ctor_set(v___x_592_, 1, v_a_487_);
return v___x_592_;
}
else
{
lean_object* v___x_593_; 
lean_dec(v___x_590_);
lean_inc_ref(v_a_486_);
lean_inc_ref(v_a_485_);
lean_inc(v_a_484_);
lean_inc(v_a_483_);
v___x_593_ = lean_apply_8(v_fetchFn_564_, v_data_558_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, lean_box(0));
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_604_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
v_a_595_ = lean_ctor_get(v___x_593_, 1);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_604_ == 0)
{
v___x_597_ = v___x_593_;
v_isShared_598_ = v_isSharedCheck_604_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_inc(v_a_594_);
lean_dec(v___x_593_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_604_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___f_599_; lean_object* v___x_600_; lean_object* v___x_602_; 
v___f_599_ = lean_alloc_closure((void*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___lam__3___boxed), 4, 2);
lean_closure_set(v___f_599_, 0, v___x_588_);
lean_closure_set(v___f_599_, 1, v_a_594_);
lean_inc_ref(v_a_485_);
v___x_600_ = l_Std_Mutex_atomically___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(v_a_485_, v___f_599_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_600_);
v___x_602_ = v___x_597_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_a_595_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
else
{
lean_dec_ref_known(v___x_588_, 2);
return v___x_593_;
}
}
}
}
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; uint8_t v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; uint8_t v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
lean_inc(v_facet_559_);
lean_dec(v___x_561_);
lean_dec_ref(v_a_482_);
v___x_605_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__4));
v___x_606_ = l_Lake_BuildInfo_key(v_info_481_);
v___x_607_ = l_Lake_BuildKey_toString(v___x_606_);
v___x_608_ = lean_string_append(v___x_605_, v___x_607_);
lean_dec_ref(v___x_607_);
v___x_609_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__9));
v___x_610_ = lean_string_append(v___x_608_, v___x_609_);
v___x_611_ = 1;
v___x_612_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_facet_559_, v___x_611_);
v___x_613_ = lean_string_append(v___x_610_, v___x_612_);
lean_dec_ref(v___x_612_);
v___x_614_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__8));
v___x_615_ = lean_string_append(v___x_613_, v___x_614_);
v___x_616_ = 3;
v___x_617_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_617_, 0, v___x_615_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*1, v___x_616_);
v___x_618_ = lean_array_get_size(v_a_487_);
v___x_619_ = lean_array_push(v_a_487_, v___x_617_);
v___x_620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_618_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
return v___x_620_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___boxed(lean_object* v_info_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l___private_Lake_Build_Index_0__Lake_recBuildWithIndex(v_info_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
lean_dec_ref(v_a_626_);
lean_dec_ref(v_a_625_);
lean_dec(v_a_624_);
lean_dec(v_a_623_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0(lean_object* v_00_u03b2_630_, lean_object* v_inst_631_, lean_object* v_t_632_, lean_object* v_k_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg(v_t_632_, v_k_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___boxed(lean_object* v_00_u03b2_635_, lean_object* v_inst_636_, lean_object* v_t_637_, lean_object* v_k_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0(v_00_u03b2_635_, v_inst_636_, v_t_637_, v_k_638_);
lean_dec_ref(v_k_638_);
lean_dec(v_t_637_);
return v_res_639_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__2(lean_object* v_00_u03b2_640_, lean_object* v_k_641_, lean_object* v_t_642_){
_start:
{
uint8_t v___x_643_; 
v___x_643_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__2___redArg(v_k_641_, v_t_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__2___boxed(lean_object* v_00_u03b2_644_, lean_object* v_k_645_, lean_object* v_t_646_){
_start:
{
uint8_t v_res_647_; lean_object* v_r_648_; 
v_res_647_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__2(v_00_u03b2_644_, v_k_645_, v_t_646_);
lean_dec(v_t_646_);
lean_dec_ref(v_k_645_);
v_r_648_ = lean_box(v_res_647_);
return v_r_648_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__3(lean_object* v_00_u03b2_649_, lean_object* v_k_650_, lean_object* v_v_651_, lean_object* v_t_652_, lean_object* v_hl_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__3___redArg(v_k_650_, v_v_651_, v_t_652_);
return v___x_654_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__0(lean_object* v_a_655_, lean_object* v_x_656_){
_start:
{
if (lean_obj_tag(v_x_656_) == 0)
{
uint8_t v___x_657_; 
v___x_657_ = 0;
return v___x_657_;
}
else
{
lean_object* v_head_658_; lean_object* v_tail_659_; uint8_t v___x_660_; 
v_head_658_ = lean_ctor_get(v_x_656_, 0);
v_tail_659_ = lean_ctor_get(v_x_656_, 1);
v___x_660_ = l_Lake_instDecidableEqBuildKey_decEq(v_a_655_, v_head_658_);
if (v___x_660_ == 0)
{
v_x_656_ = v_tail_659_;
goto _start;
}
else
{
return v___x_660_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__0___boxed(lean_object* v_a_662_, lean_object* v_x_663_){
_start:
{
uint8_t v_res_664_; lean_object* v_r_665_; 
v_res_664_ = l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__0(v_a_662_, v_x_663_);
lean_dec(v_x_663_);
lean_dec_ref(v_a_662_);
v_r_665_ = lean_box(v_res_664_);
return v_r_665_;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__1(lean_object* v___x_666_, uint8_t v___x_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
if (lean_obj_tag(v_a_668_) == 0)
{
lean_object* v_fst_670_; lean_object* v_snd_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_680_; 
v_fst_670_ = lean_ctor_get(v_a_669_, 0);
v_snd_671_ = lean_ctor_get(v_a_669_, 1);
v_isSharedCheck_680_ = !lean_is_exclusive(v_a_669_);
if (v_isSharedCheck_680_ == 0)
{
v___x_673_ = v_a_669_;
v_isShared_674_ = v_isSharedCheck_680_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_snd_671_);
lean_inc(v_fst_670_);
lean_dec(v_a_669_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_680_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_675_ = l_List_reverse___redArg(v_fst_670_);
v___x_676_ = l_List_reverse___redArg(v_snd_671_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 1, v___x_676_);
lean_ctor_set(v___x_673_, 0, v___x_675_);
v___x_678_ = v___x_673_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v___x_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
else
{
lean_object* v_head_681_; lean_object* v_tail_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_704_; 
v_head_681_ = lean_ctor_get(v_a_668_, 0);
v_tail_682_ = lean_ctor_get(v_a_668_, 1);
v_isSharedCheck_704_ = !lean_is_exclusive(v_a_668_);
if (v_isSharedCheck_704_ == 0)
{
v___x_684_ = v_a_668_;
v_isShared_685_ = v_isSharedCheck_704_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_tail_682_);
lean_inc(v_head_681_);
lean_dec(v_a_668_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_704_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v_fst_686_; lean_object* v_snd_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_703_; 
v_fst_686_ = lean_ctor_get(v_a_669_, 0);
v_snd_687_ = lean_ctor_get(v_a_669_, 1);
v_isSharedCheck_703_ = !lean_is_exclusive(v_a_669_);
if (v_isSharedCheck_703_ == 0)
{
v___x_689_ = v_a_669_;
v_isShared_690_ = v_isSharedCheck_703_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_snd_687_);
lean_inc(v_fst_686_);
lean_dec(v_a_669_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_703_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
uint8_t v___x_699_; 
v___x_699_ = l_Lake_instDecidableEqBuildKey_decEq(v_head_681_, v___x_666_);
if (v___x_699_ == 0)
{
if (v___x_667_ == 0)
{
goto v___jp_691_;
}
else
{
lean_object* v___x_700_; lean_object* v___x_701_; 
lean_del_object(v___x_689_);
lean_del_object(v___x_684_);
v___x_700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_700_, 0, v_head_681_);
lean_ctor_set(v___x_700_, 1, v_fst_686_);
v___x_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
lean_ctor_set(v___x_701_, 1, v_snd_687_);
v_a_668_ = v_tail_682_;
v_a_669_ = v___x_701_;
goto _start;
}
}
else
{
goto v___jp_691_;
}
v___jp_691_:
{
lean_object* v___x_693_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v_snd_687_);
v___x_693_ = v___x_684_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_head_681_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_snd_687_);
v___x_693_ = v_reuseFailAlloc_698_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_695_; 
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 1, v___x_693_);
v___x_695_ = v___x_689_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_fst_686_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v___x_693_);
v___x_695_ = v_reuseFailAlloc_697_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
v_a_668_ = v_tail_682_;
v_a_669_ = v___x_695_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__1___boxed(lean_object* v___x_705_, lean_object* v___x_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
uint8_t v___x_3126__boxed_709_; lean_object* v_res_710_; 
v___x_3126__boxed_709_ = lean_unbox(v___x_706_);
v_res_710_ = l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__1(v___x_705_, v___x_3126__boxed_709_, v_a_707_, v_a_708_);
lean_dec_ref(v___x_705_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___lam__0___boxed(lean_object* v___x_711_, lean_object* v_a_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___lam__0(v___x_711_, v_a_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec(v___y_713_);
lean_dec(v___x_711_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(lean_object* v_a_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v___x_729_; uint8_t v___x_730_; 
lean_inc_ref(v_a_722_);
v___x_729_ = l_Lake_BuildInfo_key(v_a_722_);
v___x_730_ = l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__0(v___x_729_, v___y_724_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; lean_object* v___f_732_; lean_object* v___x_733_; 
lean_inc(v___y_724_);
v___x_731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_729_);
lean_ctor_set(v___x_731_, 1, v___y_724_);
lean_inc_ref(v___x_731_);
v___f_732_ = lean_alloc_closure((void*)(l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_732_, 0, v___x_731_);
v___x_733_ = l___private_Lake_Build_Index_0__Lake_recBuildWithIndex(v_a_722_, v___f_732_, v___y_723_, v___x_731_, v___y_725_, v___y_726_, v___y_727_);
lean_dec_ref_known(v___x_731_, 2);
return v___x_733_;
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v_fst_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_752_; 
lean_dec_ref(v_a_722_);
v___x_734_ = lean_box(0);
v___x_735_ = ((lean_object*)(l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___closed__0));
lean_inc(v___y_724_);
v___x_736_ = l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__1(v___x_729_, v___x_730_, v___y_724_, v___x_735_);
v_fst_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_752_ == 0)
{
lean_object* v_unused_753_; 
v_unused_753_ = lean_ctor_get(v___x_736_, 1);
lean_dec(v_unused_753_);
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_752_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_fst_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_752_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
lean_inc_ref(v___x_729_);
if (v_isShared_740_ == 0)
{
lean_ctor_set_tag(v___x_739_, 1);
lean_ctor_set(v___x_739_, 1, v_fst_737_);
lean_ctor_set(v___x_739_, 0, v___x_729_);
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_729_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_fst_737_);
v___x_742_ = v_reuseFailAlloc_751_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; uint8_t v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_729_);
lean_ctor_set(v___x_743_, 1, v___x_734_);
v___x_744_ = l_List_appendTR___redArg(v___x_742_, v___x_743_);
v___x_745_ = l_Lake_buildCycleError(v___x_744_);
v___x_746_ = 3;
v___x_747_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_747_, 0, v___x_745_);
lean_ctor_set_uint8(v___x_747_, sizeof(void*)*1, v___x_746_);
v___x_748_ = lean_array_get_size(v___y_727_);
v___x_749_ = lean_array_push(v___y_727_, v___x_747_);
v___x_750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_748_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
return v___x_750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___lam__0(lean_object* v___x_754_, lean_object* v_a_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(v_a_755_, v___y_756_, v___x_754_, v___y_758_, v___y_759_, v___y_760_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___boxed(lean_object* v_a_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(v_a_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec(v___y_764_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recFetchWithIndex(lean_object* v_info_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(v_info_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recFetchWithIndex___boxed(lean_object* v_info_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l___private_Lake_Build_Index_0__Lake_recFetchWithIndex(v_info_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_);
lean_dec_ref(v_a_783_);
lean_dec_ref(v_a_782_);
lean_dec(v_a_781_);
lean_dec(v_a_780_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0(lean_object* v_a_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(v_a_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0___boxed(lean_object* v_a_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0(v_a_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec(v___y_796_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2(lean_object* v_inst_803_, lean_object* v_a_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(v_a_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___boxed(lean_object* v_inst_812_, lean_object* v_a_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2(v_inst_812_, v_a_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v___y_815_);
lean_dec(v___y_814_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchT_run___redArg(lean_object* v_x_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = ((lean_object*)(l_Lake_FetchT_run___redArg___closed__0));
lean_inc_ref(v_a_826_);
lean_inc_ref(v_a_825_);
lean_inc(v_a_824_);
lean_inc(v_a_823_);
v___x_828_ = lean_apply_5(v_x_822_, v___x_827_, v_a_823_, v_a_824_, v_a_825_, v_a_826_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchT_run___redArg___boxed(lean_object* v_x_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lake_FetchT_run___redArg(v_x_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_);
lean_dec_ref(v_a_833_);
lean_dec_ref(v_a_832_);
lean_dec(v_a_831_);
lean_dec(v_a_830_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchT_run(lean_object* v_m_835_, lean_object* v_00_u03b1_836_, lean_object* v_x_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = ((lean_object*)(l_Lake_FetchT_run___redArg___closed__0));
lean_inc_ref(v_a_841_);
lean_inc_ref(v_a_840_);
lean_inc(v_a_839_);
lean_inc(v_a_838_);
v___x_843_ = lean_apply_5(v_x_837_, v___x_842_, v_a_838_, v_a_839_, v_a_840_, v_a_841_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchT_run___boxed(lean_object* v_m_844_, lean_object* v_00_u03b1_845_, lean_object* v_x_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lake_FetchT_run(v_m_844_, v_00_u03b1_845_, v_x_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_);
lean_dec_ref(v_a_850_);
lean_dec_ref(v_a_849_);
lean_dec(v_a_848_);
lean_dec(v_a_847_);
return v_res_851_;
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
