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
lean_object* l_Lake_BuildTrace_nil(lean_object*);
uint8_t l_Lake_BuildKey_quickCmp(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_Lake_instDecidableEqBuildKey_decEq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_BuildInfo_key(lean_object*);
lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lake_BuildKey_toString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_FacetConfigMap_get_x3f(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lake_buildCycleError(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(lean_object* v_k_1_, lean_object* v_v_2_, lean_object* v_t_3_){
_start:
{
if (lean_obj_tag(v_t_3_) == 0)
{
lean_object* v_size_4_; lean_object* v_k_5_; lean_object* v_v_6_; lean_object* v_l_7_; lean_object* v_r_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_288_; 
v_size_4_ = lean_ctor_get(v_t_3_, 0);
v_k_5_ = lean_ctor_get(v_t_3_, 1);
v_v_6_ = lean_ctor_get(v_t_3_, 2);
v_l_7_ = lean_ctor_get(v_t_3_, 3);
v_r_8_ = lean_ctor_get(v_t_3_, 4);
v_isSharedCheck_288_ = !lean_is_exclusive(v_t_3_);
if (v_isSharedCheck_288_ == 0)
{
v___x_10_ = v_t_3_;
v_isShared_11_ = v_isSharedCheck_288_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_r_8_);
lean_inc(v_l_7_);
lean_inc(v_v_6_);
lean_inc(v_k_5_);
lean_inc(v_size_4_);
lean_dec(v_t_3_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_288_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
uint8_t v___x_12_; 
v___x_12_ = l_Lake_BuildKey_quickCmp(v_k_1_, v_k_5_);
switch(v___x_12_)
{
case 0:
{
lean_object* v_impl_13_; lean_object* v___x_14_; 
lean_dec(v_size_4_);
v_impl_13_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(v_k_1_, v_v_2_, v_l_7_);
v___x_14_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_8_) == 0)
{
lean_object* v_size_15_; lean_object* v_size_16_; lean_object* v_k_17_; lean_object* v_v_18_; lean_object* v_l_19_; lean_object* v_r_20_; lean_object* v___x_21_; lean_object* v___x_22_; uint8_t v___x_23_; 
v_size_15_ = lean_ctor_get(v_r_8_, 0);
v_size_16_ = lean_ctor_get(v_impl_13_, 0);
v_k_17_ = lean_ctor_get(v_impl_13_, 1);
v_v_18_ = lean_ctor_get(v_impl_13_, 2);
v_l_19_ = lean_ctor_get(v_impl_13_, 3);
v_r_20_ = lean_ctor_get(v_impl_13_, 4);
lean_inc(v_r_20_);
v___x_21_ = lean_unsigned_to_nat(3u);
v___x_22_ = lean_nat_mul(v___x_21_, v_size_15_);
v___x_23_ = lean_nat_dec_lt(v___x_22_, v_size_16_);
lean_dec(v___x_22_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_27_; 
lean_dec(v_r_20_);
v___x_24_ = lean_nat_add(v___x_14_, v_size_16_);
v___x_25_ = lean_nat_add(v___x_24_, v_size_15_);
lean_dec(v___x_24_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 3, v_impl_13_);
lean_ctor_set(v___x_10_, 0, v___x_25_);
v___x_27_ = v___x_10_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v___x_25_);
lean_ctor_set(v_reuseFailAlloc_28_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_28_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_28_, 3, v_impl_13_);
lean_ctor_set(v_reuseFailAlloc_28_, 4, v_r_8_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
else
{
lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_94_; 
lean_inc(v_l_19_);
lean_inc(v_v_18_);
lean_inc(v_k_17_);
lean_inc(v_size_16_);
v_isSharedCheck_94_ = !lean_is_exclusive(v_impl_13_);
if (v_isSharedCheck_94_ == 0)
{
lean_object* v_unused_95_; lean_object* v_unused_96_; lean_object* v_unused_97_; lean_object* v_unused_98_; lean_object* v_unused_99_; 
v_unused_95_ = lean_ctor_get(v_impl_13_, 4);
lean_dec(v_unused_95_);
v_unused_96_ = lean_ctor_get(v_impl_13_, 3);
lean_dec(v_unused_96_);
v_unused_97_ = lean_ctor_get(v_impl_13_, 2);
lean_dec(v_unused_97_);
v_unused_98_ = lean_ctor_get(v_impl_13_, 1);
lean_dec(v_unused_98_);
v_unused_99_ = lean_ctor_get(v_impl_13_, 0);
lean_dec(v_unused_99_);
v___x_30_ = v_impl_13_;
v_isShared_31_ = v_isSharedCheck_94_;
goto v_resetjp_29_;
}
else
{
lean_dec(v_impl_13_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_94_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v_size_32_; lean_object* v_size_33_; lean_object* v_k_34_; lean_object* v_v_35_; lean_object* v_l_36_; lean_object* v_r_37_; lean_object* v___x_38_; lean_object* v___x_39_; uint8_t v___x_40_; 
v_size_32_ = lean_ctor_get(v_l_19_, 0);
v_size_33_ = lean_ctor_get(v_r_20_, 0);
v_k_34_ = lean_ctor_get(v_r_20_, 1);
v_v_35_ = lean_ctor_get(v_r_20_, 2);
v_l_36_ = lean_ctor_get(v_r_20_, 3);
v_r_37_ = lean_ctor_get(v_r_20_, 4);
v___x_38_ = lean_unsigned_to_nat(2u);
v___x_39_ = lean_nat_mul(v___x_38_, v_size_32_);
v___x_40_ = lean_nat_dec_lt(v_size_33_, v___x_39_);
lean_dec(v___x_39_);
if (v___x_40_ == 0)
{
lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_69_; 
lean_inc(v_r_37_);
lean_inc(v_l_36_);
lean_inc(v_v_35_);
lean_inc(v_k_34_);
v_isSharedCheck_69_ = !lean_is_exclusive(v_r_20_);
if (v_isSharedCheck_69_ == 0)
{
lean_object* v_unused_70_; lean_object* v_unused_71_; lean_object* v_unused_72_; lean_object* v_unused_73_; lean_object* v_unused_74_; 
v_unused_70_ = lean_ctor_get(v_r_20_, 4);
lean_dec(v_unused_70_);
v_unused_71_ = lean_ctor_get(v_r_20_, 3);
lean_dec(v_unused_71_);
v_unused_72_ = lean_ctor_get(v_r_20_, 2);
lean_dec(v_unused_72_);
v_unused_73_ = lean_ctor_get(v_r_20_, 1);
lean_dec(v_unused_73_);
v_unused_74_ = lean_ctor_get(v_r_20_, 0);
lean_dec(v_unused_74_);
v___x_42_ = v_r_20_;
v_isShared_43_ = v_isSharedCheck_69_;
goto v_resetjp_41_;
}
else
{
lean_dec(v_r_20_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_69_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___y_47_; lean_object* v___y_48_; lean_object* v___y_49_; lean_object* v___x_57_; lean_object* v___y_59_; 
v___x_44_ = lean_nat_add(v___x_14_, v_size_16_);
lean_dec(v_size_16_);
v___x_45_ = lean_nat_add(v___x_44_, v_size_15_);
lean_dec(v___x_44_);
v___x_57_ = lean_nat_add(v___x_14_, v_size_32_);
if (lean_obj_tag(v_l_36_) == 0)
{
lean_object* v_size_67_; 
v_size_67_ = lean_ctor_get(v_l_36_, 0);
lean_inc(v_size_67_);
v___y_59_ = v_size_67_;
goto v___jp_58_;
}
else
{
lean_object* v___x_68_; 
v___x_68_ = lean_unsigned_to_nat(0u);
v___y_59_ = v___x_68_;
goto v___jp_58_;
}
v___jp_46_:
{
lean_object* v___x_50_; lean_object* v___x_52_; 
v___x_50_ = lean_nat_add(v___y_48_, v___y_49_);
lean_dec(v___y_49_);
lean_dec(v___y_48_);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 4, v_r_8_);
lean_ctor_set(v___x_42_, 3, v_r_37_);
lean_ctor_set(v___x_42_, 2, v_v_6_);
lean_ctor_set(v___x_42_, 1, v_k_5_);
lean_ctor_set(v___x_42_, 0, v___x_50_);
v___x_52_ = v___x_42_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v___x_50_);
lean_ctor_set(v_reuseFailAlloc_56_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_56_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_56_, 3, v_r_37_);
lean_ctor_set(v_reuseFailAlloc_56_, 4, v_r_8_);
v___x_52_ = v_reuseFailAlloc_56_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
lean_object* v___x_54_; 
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 4, v___x_52_);
lean_ctor_set(v___x_30_, 3, v___y_47_);
lean_ctor_set(v___x_30_, 2, v_v_35_);
lean_ctor_set(v___x_30_, 1, v_k_34_);
lean_ctor_set(v___x_30_, 0, v___x_45_);
v___x_54_ = v___x_30_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_45_);
lean_ctor_set(v_reuseFailAlloc_55_, 1, v_k_34_);
lean_ctor_set(v_reuseFailAlloc_55_, 2, v_v_35_);
lean_ctor_set(v_reuseFailAlloc_55_, 3, v___y_47_);
lean_ctor_set(v_reuseFailAlloc_55_, 4, v___x_52_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
v___jp_58_:
{
lean_object* v___x_60_; lean_object* v___x_62_; 
v___x_60_ = lean_nat_add(v___x_57_, v___y_59_);
lean_dec(v___y_59_);
lean_dec(v___x_57_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 4, v_l_36_);
lean_ctor_set(v___x_10_, 3, v_l_19_);
lean_ctor_set(v___x_10_, 2, v_v_18_);
lean_ctor_set(v___x_10_, 1, v_k_17_);
lean_ctor_set(v___x_10_, 0, v___x_60_);
v___x_62_ = v___x_10_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_60_);
lean_ctor_set(v_reuseFailAlloc_66_, 1, v_k_17_);
lean_ctor_set(v_reuseFailAlloc_66_, 2, v_v_18_);
lean_ctor_set(v_reuseFailAlloc_66_, 3, v_l_19_);
lean_ctor_set(v_reuseFailAlloc_66_, 4, v_l_36_);
v___x_62_ = v_reuseFailAlloc_66_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
lean_object* v___x_63_; 
v___x_63_ = lean_nat_add(v___x_14_, v_size_15_);
if (lean_obj_tag(v_r_37_) == 0)
{
lean_object* v_size_64_; 
v_size_64_ = lean_ctor_get(v_r_37_, 0);
lean_inc(v_size_64_);
v___y_47_ = v___x_62_;
v___y_48_ = v___x_63_;
v___y_49_ = v_size_64_;
goto v___jp_46_;
}
else
{
lean_object* v___x_65_; 
v___x_65_ = lean_unsigned_to_nat(0u);
v___y_47_ = v___x_62_;
v___y_48_ = v___x_63_;
v___y_49_ = v___x_65_;
goto v___jp_46_;
}
}
}
}
}
else
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_80_; 
lean_del_object(v___x_10_);
v___x_75_ = lean_nat_add(v___x_14_, v_size_16_);
lean_dec(v_size_16_);
v___x_76_ = lean_nat_add(v___x_75_, v_size_15_);
lean_dec(v___x_75_);
v___x_77_ = lean_nat_add(v___x_14_, v_size_15_);
v___x_78_ = lean_nat_add(v___x_77_, v_size_33_);
lean_dec(v___x_77_);
lean_inc_ref(v_r_8_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 4, v_r_8_);
lean_ctor_set(v___x_30_, 3, v_r_20_);
lean_ctor_set(v___x_30_, 2, v_v_6_);
lean_ctor_set(v___x_30_, 1, v_k_5_);
lean_ctor_set(v___x_30_, 0, v___x_78_);
v___x_80_ = v___x_30_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_78_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_93_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_93_, 3, v_r_20_);
lean_ctor_set(v_reuseFailAlloc_93_, 4, v_r_8_);
v___x_80_ = v_reuseFailAlloc_93_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_87_; 
v_isSharedCheck_87_ = !lean_is_exclusive(v_r_8_);
if (v_isSharedCheck_87_ == 0)
{
lean_object* v_unused_88_; lean_object* v_unused_89_; lean_object* v_unused_90_; lean_object* v_unused_91_; lean_object* v_unused_92_; 
v_unused_88_ = lean_ctor_get(v_r_8_, 4);
lean_dec(v_unused_88_);
v_unused_89_ = lean_ctor_get(v_r_8_, 3);
lean_dec(v_unused_89_);
v_unused_90_ = lean_ctor_get(v_r_8_, 2);
lean_dec(v_unused_90_);
v_unused_91_ = lean_ctor_get(v_r_8_, 1);
lean_dec(v_unused_91_);
v_unused_92_ = lean_ctor_get(v_r_8_, 0);
lean_dec(v_unused_92_);
v___x_82_ = v_r_8_;
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
else
{
lean_dec(v_r_8_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_85_; 
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 4, v___x_80_);
lean_ctor_set(v___x_82_, 3, v_l_19_);
lean_ctor_set(v___x_82_, 2, v_v_18_);
lean_ctor_set(v___x_82_, 1, v_k_17_);
lean_ctor_set(v___x_82_, 0, v___x_76_);
v___x_85_ = v___x_82_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v___x_76_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v_k_17_);
lean_ctor_set(v_reuseFailAlloc_86_, 2, v_v_18_);
lean_ctor_set(v_reuseFailAlloc_86_, 3, v_l_19_);
lean_ctor_set(v_reuseFailAlloc_86_, 4, v___x_80_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_100_; 
v_l_100_ = lean_ctor_get(v_impl_13_, 3);
if (lean_obj_tag(v_l_100_) == 0)
{
lean_object* v_r_101_; lean_object* v_k_102_; lean_object* v_v_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_114_; 
lean_inc_ref(v_l_100_);
v_r_101_ = lean_ctor_get(v_impl_13_, 4);
v_k_102_ = lean_ctor_get(v_impl_13_, 1);
v_v_103_ = lean_ctor_get(v_impl_13_, 2);
v_isSharedCheck_114_ = !lean_is_exclusive(v_impl_13_);
if (v_isSharedCheck_114_ == 0)
{
lean_object* v_unused_115_; lean_object* v_unused_116_; 
v_unused_115_ = lean_ctor_get(v_impl_13_, 3);
lean_dec(v_unused_115_);
v_unused_116_ = lean_ctor_get(v_impl_13_, 0);
lean_dec(v_unused_116_);
v___x_105_ = v_impl_13_;
v_isShared_106_ = v_isSharedCheck_114_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_r_101_);
lean_inc(v_v_103_);
lean_inc(v_k_102_);
lean_dec(v_impl_13_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_114_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_107_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_101_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 3, v_r_101_);
lean_ctor_set(v___x_105_, 2, v_v_6_);
lean_ctor_set(v___x_105_, 1, v_k_5_);
lean_ctor_set(v___x_105_, 0, v___x_14_);
v___x_109_ = v___x_105_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_14_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_113_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_113_, 3, v_r_101_);
lean_ctor_set(v_reuseFailAlloc_113_, 4, v_r_101_);
v___x_109_ = v_reuseFailAlloc_113_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_111_; 
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 4, v___x_109_);
lean_ctor_set(v___x_10_, 3, v_l_100_);
lean_ctor_set(v___x_10_, 2, v_v_103_);
lean_ctor_set(v___x_10_, 1, v_k_102_);
lean_ctor_set(v___x_10_, 0, v___x_107_);
v___x_111_ = v___x_10_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v_k_102_);
lean_ctor_set(v_reuseFailAlloc_112_, 2, v_v_103_);
lean_ctor_set(v_reuseFailAlloc_112_, 3, v_l_100_);
lean_ctor_set(v_reuseFailAlloc_112_, 4, v___x_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
else
{
lean_object* v_r_117_; 
v_r_117_ = lean_ctor_get(v_impl_13_, 4);
lean_inc(v_r_117_);
if (lean_obj_tag(v_r_117_) == 0)
{
lean_object* v_k_118_; lean_object* v_v_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_142_; 
lean_inc(v_l_100_);
v_k_118_ = lean_ctor_get(v_impl_13_, 1);
v_v_119_ = lean_ctor_get(v_impl_13_, 2);
v_isSharedCheck_142_ = !lean_is_exclusive(v_impl_13_);
if (v_isSharedCheck_142_ == 0)
{
lean_object* v_unused_143_; lean_object* v_unused_144_; lean_object* v_unused_145_; 
v_unused_143_ = lean_ctor_get(v_impl_13_, 4);
lean_dec(v_unused_143_);
v_unused_144_ = lean_ctor_get(v_impl_13_, 3);
lean_dec(v_unused_144_);
v_unused_145_ = lean_ctor_get(v_impl_13_, 0);
lean_dec(v_unused_145_);
v___x_121_ = v_impl_13_;
v_isShared_122_ = v_isSharedCheck_142_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_v_119_);
lean_inc(v_k_118_);
lean_dec(v_impl_13_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_142_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v_k_123_; lean_object* v_v_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_138_; 
v_k_123_ = lean_ctor_get(v_r_117_, 1);
v_v_124_ = lean_ctor_get(v_r_117_, 2);
v_isSharedCheck_138_ = !lean_is_exclusive(v_r_117_);
if (v_isSharedCheck_138_ == 0)
{
lean_object* v_unused_139_; lean_object* v_unused_140_; lean_object* v_unused_141_; 
v_unused_139_ = lean_ctor_get(v_r_117_, 4);
lean_dec(v_unused_139_);
v_unused_140_ = lean_ctor_get(v_r_117_, 3);
lean_dec(v_unused_140_);
v_unused_141_ = lean_ctor_get(v_r_117_, 0);
lean_dec(v_unused_141_);
v___x_126_ = v_r_117_;
v_isShared_127_ = v_isSharedCheck_138_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_v_124_);
lean_inc(v_k_123_);
lean_dec(v_r_117_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_138_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_128_ = lean_unsigned_to_nat(3u);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 4, v_l_100_);
lean_ctor_set(v___x_126_, 3, v_l_100_);
lean_ctor_set(v___x_126_, 2, v_v_119_);
lean_ctor_set(v___x_126_, 1, v_k_118_);
lean_ctor_set(v___x_126_, 0, v___x_14_);
v___x_130_ = v___x_126_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_14_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_k_118_);
lean_ctor_set(v_reuseFailAlloc_137_, 2, v_v_119_);
lean_ctor_set(v_reuseFailAlloc_137_, 3, v_l_100_);
lean_ctor_set(v_reuseFailAlloc_137_, 4, v_l_100_);
v___x_130_ = v_reuseFailAlloc_137_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_132_; 
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 4, v_l_100_);
lean_ctor_set(v___x_121_, 2, v_v_6_);
lean_ctor_set(v___x_121_, 1, v_k_5_);
lean_ctor_set(v___x_121_, 0, v___x_14_);
v___x_132_ = v___x_121_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_14_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_136_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_136_, 3, v_l_100_);
lean_ctor_set(v_reuseFailAlloc_136_, 4, v_l_100_);
v___x_132_ = v_reuseFailAlloc_136_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
lean_object* v___x_134_; 
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 4, v___x_132_);
lean_ctor_set(v___x_10_, 3, v___x_130_);
lean_ctor_set(v___x_10_, 2, v_v_124_);
lean_ctor_set(v___x_10_, 1, v_k_123_);
lean_ctor_set(v___x_10_, 0, v___x_128_);
v___x_134_ = v___x_10_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_128_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_k_123_);
lean_ctor_set(v_reuseFailAlloc_135_, 2, v_v_124_);
lean_ctor_set(v_reuseFailAlloc_135_, 3, v___x_130_);
lean_ctor_set(v_reuseFailAlloc_135_, 4, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
}
}
else
{
lean_object* v___x_146_; lean_object* v___x_148_; 
v___x_146_ = lean_unsigned_to_nat(2u);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 4, v_r_117_);
lean_ctor_set(v___x_10_, 3, v_impl_13_);
lean_ctor_set(v___x_10_, 0, v___x_146_);
v___x_148_ = v___x_10_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_146_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_149_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_149_, 3, v_impl_13_);
lean_ctor_set(v_reuseFailAlloc_149_, 4, v_r_117_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
}
case 1:
{
lean_object* v___x_151_; 
lean_dec(v_v_6_);
lean_dec(v_k_5_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 2, v_v_2_);
lean_ctor_set(v___x_10_, 1, v_k_1_);
v___x_151_ = v___x_10_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_size_4_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_k_1_);
lean_ctor_set(v_reuseFailAlloc_152_, 2, v_v_2_);
lean_ctor_set(v_reuseFailAlloc_152_, 3, v_l_7_);
lean_ctor_set(v_reuseFailAlloc_152_, 4, v_r_8_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
default: 
{
lean_object* v_impl_153_; lean_object* v___x_154_; 
lean_dec(v_size_4_);
v_impl_153_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(v_k_1_, v_v_2_, v_r_8_);
v___x_154_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_7_) == 0)
{
lean_object* v_size_155_; lean_object* v_size_156_; lean_object* v_k_157_; lean_object* v_v_158_; lean_object* v_l_159_; lean_object* v_r_160_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v_size_155_ = lean_ctor_get(v_l_7_, 0);
v_size_156_ = lean_ctor_get(v_impl_153_, 0);
v_k_157_ = lean_ctor_get(v_impl_153_, 1);
v_v_158_ = lean_ctor_get(v_impl_153_, 2);
v_l_159_ = lean_ctor_get(v_impl_153_, 3);
lean_inc(v_l_159_);
v_r_160_ = lean_ctor_get(v_impl_153_, 4);
v___x_161_ = lean_unsigned_to_nat(3u);
v___x_162_ = lean_nat_mul(v___x_161_, v_size_155_);
v___x_163_ = lean_nat_dec_lt(v___x_162_, v_size_156_);
lean_dec(v___x_162_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_167_; 
lean_dec(v_l_159_);
v___x_164_ = lean_nat_add(v___x_154_, v_size_155_);
v___x_165_ = lean_nat_add(v___x_164_, v_size_156_);
lean_dec(v___x_164_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 4, v_impl_153_);
lean_ctor_set(v___x_10_, 0, v___x_165_);
v___x_167_ = v___x_10_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_168_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_168_, 3, v_l_7_);
lean_ctor_set(v_reuseFailAlloc_168_, 4, v_impl_153_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
else
{
lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_232_; 
lean_inc(v_r_160_);
lean_inc(v_v_158_);
lean_inc(v_k_157_);
lean_inc(v_size_156_);
v_isSharedCheck_232_ = !lean_is_exclusive(v_impl_153_);
if (v_isSharedCheck_232_ == 0)
{
lean_object* v_unused_233_; lean_object* v_unused_234_; lean_object* v_unused_235_; lean_object* v_unused_236_; lean_object* v_unused_237_; 
v_unused_233_ = lean_ctor_get(v_impl_153_, 4);
lean_dec(v_unused_233_);
v_unused_234_ = lean_ctor_get(v_impl_153_, 3);
lean_dec(v_unused_234_);
v_unused_235_ = lean_ctor_get(v_impl_153_, 2);
lean_dec(v_unused_235_);
v_unused_236_ = lean_ctor_get(v_impl_153_, 1);
lean_dec(v_unused_236_);
v_unused_237_ = lean_ctor_get(v_impl_153_, 0);
lean_dec(v_unused_237_);
v___x_170_ = v_impl_153_;
v_isShared_171_ = v_isSharedCheck_232_;
goto v_resetjp_169_;
}
else
{
lean_dec(v_impl_153_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_232_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v_size_172_; lean_object* v_k_173_; lean_object* v_v_174_; lean_object* v_l_175_; lean_object* v_r_176_; lean_object* v_size_177_; lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v_size_172_ = lean_ctor_get(v_l_159_, 0);
v_k_173_ = lean_ctor_get(v_l_159_, 1);
v_v_174_ = lean_ctor_get(v_l_159_, 2);
v_l_175_ = lean_ctor_get(v_l_159_, 3);
v_r_176_ = lean_ctor_get(v_l_159_, 4);
v_size_177_ = lean_ctor_get(v_r_160_, 0);
v___x_178_ = lean_unsigned_to_nat(2u);
v___x_179_ = lean_nat_mul(v___x_178_, v_size_177_);
v___x_180_ = lean_nat_dec_lt(v_size_172_, v___x_179_);
lean_dec(v___x_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_208_; 
lean_inc(v_r_176_);
lean_inc(v_l_175_);
lean_inc(v_v_174_);
lean_inc(v_k_173_);
v_isSharedCheck_208_ = !lean_is_exclusive(v_l_159_);
if (v_isSharedCheck_208_ == 0)
{
lean_object* v_unused_209_; lean_object* v_unused_210_; lean_object* v_unused_211_; lean_object* v_unused_212_; lean_object* v_unused_213_; 
v_unused_209_ = lean_ctor_get(v_l_159_, 4);
lean_dec(v_unused_209_);
v_unused_210_ = lean_ctor_get(v_l_159_, 3);
lean_dec(v_unused_210_);
v_unused_211_ = lean_ctor_get(v_l_159_, 2);
lean_dec(v_unused_211_);
v_unused_212_ = lean_ctor_get(v_l_159_, 1);
lean_dec(v_unused_212_);
v_unused_213_ = lean_ctor_get(v_l_159_, 0);
lean_dec(v_unused_213_);
v___x_182_ = v_l_159_;
v_isShared_183_ = v_isSharedCheck_208_;
goto v_resetjp_181_;
}
else
{
lean_dec(v_l_159_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_208_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___y_187_; lean_object* v___y_188_; lean_object* v___y_189_; lean_object* v___y_198_; 
v___x_184_ = lean_nat_add(v___x_154_, v_size_155_);
v___x_185_ = lean_nat_add(v___x_184_, v_size_156_);
lean_dec(v_size_156_);
if (lean_obj_tag(v_l_175_) == 0)
{
lean_object* v_size_206_; 
v_size_206_ = lean_ctor_get(v_l_175_, 0);
lean_inc(v_size_206_);
v___y_198_ = v_size_206_;
goto v___jp_197_;
}
else
{
lean_object* v___x_207_; 
v___x_207_ = lean_unsigned_to_nat(0u);
v___y_198_ = v___x_207_;
goto v___jp_197_;
}
v___jp_186_:
{
lean_object* v___x_190_; lean_object* v___x_192_; 
v___x_190_ = lean_nat_add(v___y_188_, v___y_189_);
lean_dec(v___y_189_);
lean_dec(v___y_188_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 4, v_r_160_);
lean_ctor_set(v___x_182_, 3, v_r_176_);
lean_ctor_set(v___x_182_, 2, v_v_158_);
lean_ctor_set(v___x_182_, 1, v_k_157_);
lean_ctor_set(v___x_182_, 0, v___x_190_);
v___x_192_ = v___x_182_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_190_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_k_157_);
lean_ctor_set(v_reuseFailAlloc_196_, 2, v_v_158_);
lean_ctor_set(v_reuseFailAlloc_196_, 3, v_r_176_);
lean_ctor_set(v_reuseFailAlloc_196_, 4, v_r_160_);
v___x_192_ = v_reuseFailAlloc_196_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
lean_object* v___x_194_; 
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 4, v___x_192_);
lean_ctor_set(v___x_170_, 3, v___y_187_);
lean_ctor_set(v___x_170_, 2, v_v_174_);
lean_ctor_set(v___x_170_, 1, v_k_173_);
lean_ctor_set(v___x_170_, 0, v___x_185_);
v___x_194_ = v___x_170_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_185_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_k_173_);
lean_ctor_set(v_reuseFailAlloc_195_, 2, v_v_174_);
lean_ctor_set(v_reuseFailAlloc_195_, 3, v___y_187_);
lean_ctor_set(v_reuseFailAlloc_195_, 4, v___x_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
v___jp_197_:
{
lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_199_ = lean_nat_add(v___x_184_, v___y_198_);
lean_dec(v___y_198_);
lean_dec(v___x_184_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 4, v_l_175_);
lean_ctor_set(v___x_10_, 0, v___x_199_);
v___x_201_ = v___x_10_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_199_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_205_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_205_, 3, v_l_7_);
lean_ctor_set(v_reuseFailAlloc_205_, 4, v_l_175_);
v___x_201_ = v_reuseFailAlloc_205_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
lean_object* v___x_202_; 
v___x_202_ = lean_nat_add(v___x_154_, v_size_177_);
if (lean_obj_tag(v_r_176_) == 0)
{
lean_object* v_size_203_; 
v_size_203_ = lean_ctor_get(v_r_176_, 0);
lean_inc(v_size_203_);
v___y_187_ = v___x_201_;
v___y_188_ = v___x_202_;
v___y_189_ = v_size_203_;
goto v___jp_186_;
}
else
{
lean_object* v___x_204_; 
v___x_204_ = lean_unsigned_to_nat(0u);
v___y_187_ = v___x_201_;
v___y_188_ = v___x_202_;
v___y_189_ = v___x_204_;
goto v___jp_186_;
}
}
}
}
}
else
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_218_; 
lean_del_object(v___x_10_);
v___x_214_ = lean_nat_add(v___x_154_, v_size_155_);
v___x_215_ = lean_nat_add(v___x_214_, v_size_156_);
lean_dec(v_size_156_);
v___x_216_ = lean_nat_add(v___x_214_, v_size_172_);
lean_dec(v___x_214_);
lean_inc_ref(v_l_7_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 4, v_l_159_);
lean_ctor_set(v___x_170_, 3, v_l_7_);
lean_ctor_set(v___x_170_, 2, v_v_6_);
lean_ctor_set(v___x_170_, 1, v_k_5_);
lean_ctor_set(v___x_170_, 0, v___x_216_);
v___x_218_ = v___x_170_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_216_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_231_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_231_, 3, v_l_7_);
lean_ctor_set(v_reuseFailAlloc_231_, 4, v_l_159_);
v___x_218_ = v_reuseFailAlloc_231_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
v_isSharedCheck_225_ = !lean_is_exclusive(v_l_7_);
if (v_isSharedCheck_225_ == 0)
{
lean_object* v_unused_226_; lean_object* v_unused_227_; lean_object* v_unused_228_; lean_object* v_unused_229_; lean_object* v_unused_230_; 
v_unused_226_ = lean_ctor_get(v_l_7_, 4);
lean_dec(v_unused_226_);
v_unused_227_ = lean_ctor_get(v_l_7_, 3);
lean_dec(v_unused_227_);
v_unused_228_ = lean_ctor_get(v_l_7_, 2);
lean_dec(v_unused_228_);
v_unused_229_ = lean_ctor_get(v_l_7_, 1);
lean_dec(v_unused_229_);
v_unused_230_ = lean_ctor_get(v_l_7_, 0);
lean_dec(v_unused_230_);
v___x_220_ = v_l_7_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_dec(v_l_7_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 4, v_r_160_);
lean_ctor_set(v___x_220_, 3, v___x_218_);
lean_ctor_set(v___x_220_, 2, v_v_158_);
lean_ctor_set(v___x_220_, 1, v_k_157_);
lean_ctor_set(v___x_220_, 0, v___x_215_);
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_215_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_k_157_);
lean_ctor_set(v_reuseFailAlloc_224_, 2, v_v_158_);
lean_ctor_set(v_reuseFailAlloc_224_, 3, v___x_218_);
lean_ctor_set(v_reuseFailAlloc_224_, 4, v_r_160_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_238_; 
v_l_238_ = lean_ctor_get(v_impl_153_, 3);
lean_inc(v_l_238_);
if (lean_obj_tag(v_l_238_) == 0)
{
lean_object* v_r_239_; lean_object* v_k_240_; lean_object* v_v_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_264_; 
v_r_239_ = lean_ctor_get(v_impl_153_, 4);
v_k_240_ = lean_ctor_get(v_impl_153_, 1);
v_v_241_ = lean_ctor_get(v_impl_153_, 2);
v_isSharedCheck_264_ = !lean_is_exclusive(v_impl_153_);
if (v_isSharedCheck_264_ == 0)
{
lean_object* v_unused_265_; lean_object* v_unused_266_; 
v_unused_265_ = lean_ctor_get(v_impl_153_, 3);
lean_dec(v_unused_265_);
v_unused_266_ = lean_ctor_get(v_impl_153_, 0);
lean_dec(v_unused_266_);
v___x_243_ = v_impl_153_;
v_isShared_244_ = v_isSharedCheck_264_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_r_239_);
lean_inc(v_v_241_);
lean_inc(v_k_240_);
lean_dec(v_impl_153_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_264_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v_k_245_; lean_object* v_v_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_260_; 
v_k_245_ = lean_ctor_get(v_l_238_, 1);
v_v_246_ = lean_ctor_get(v_l_238_, 2);
v_isSharedCheck_260_ = !lean_is_exclusive(v_l_238_);
if (v_isSharedCheck_260_ == 0)
{
lean_object* v_unused_261_; lean_object* v_unused_262_; lean_object* v_unused_263_; 
v_unused_261_ = lean_ctor_get(v_l_238_, 4);
lean_dec(v_unused_261_);
v_unused_262_ = lean_ctor_get(v_l_238_, 3);
lean_dec(v_unused_262_);
v_unused_263_ = lean_ctor_get(v_l_238_, 0);
lean_dec(v_unused_263_);
v___x_248_ = v_l_238_;
v_isShared_249_ = v_isSharedCheck_260_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_v_246_);
lean_inc(v_k_245_);
lean_dec(v_l_238_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_260_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v___x_252_; 
v___x_250_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_239_, 2);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 4, v_r_239_);
lean_ctor_set(v___x_248_, 3, v_r_239_);
lean_ctor_set(v___x_248_, 2, v_v_6_);
lean_ctor_set(v___x_248_, 1, v_k_5_);
lean_ctor_set(v___x_248_, 0, v___x_154_);
v___x_252_ = v___x_248_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_154_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_259_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_259_, 3, v_r_239_);
lean_ctor_set(v_reuseFailAlloc_259_, 4, v_r_239_);
v___x_252_ = v_reuseFailAlloc_259_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_254_; 
lean_inc(v_r_239_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 3, v_r_239_);
lean_ctor_set(v___x_243_, 0, v___x_154_);
v___x_254_ = v___x_243_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_154_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_k_240_);
lean_ctor_set(v_reuseFailAlloc_258_, 2, v_v_241_);
lean_ctor_set(v_reuseFailAlloc_258_, 3, v_r_239_);
lean_ctor_set(v_reuseFailAlloc_258_, 4, v_r_239_);
v___x_254_ = v_reuseFailAlloc_258_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_256_; 
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 4, v___x_254_);
lean_ctor_set(v___x_10_, 3, v___x_252_);
lean_ctor_set(v___x_10_, 2, v_v_246_);
lean_ctor_set(v___x_10_, 1, v_k_245_);
lean_ctor_set(v___x_10_, 0, v___x_250_);
v___x_256_ = v___x_10_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_k_245_);
lean_ctor_set(v_reuseFailAlloc_257_, 2, v_v_246_);
lean_ctor_set(v_reuseFailAlloc_257_, 3, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_257_, 4, v___x_254_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
}
}
else
{
lean_object* v_r_267_; 
v_r_267_ = lean_ctor_get(v_impl_153_, 4);
lean_inc(v_r_267_);
if (lean_obj_tag(v_r_267_) == 0)
{
lean_object* v_k_268_; lean_object* v_v_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_280_; 
v_k_268_ = lean_ctor_get(v_impl_153_, 1);
v_v_269_ = lean_ctor_get(v_impl_153_, 2);
v_isSharedCheck_280_ = !lean_is_exclusive(v_impl_153_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; lean_object* v_unused_282_; lean_object* v_unused_283_; 
v_unused_281_ = lean_ctor_get(v_impl_153_, 4);
lean_dec(v_unused_281_);
v_unused_282_ = lean_ctor_get(v_impl_153_, 3);
lean_dec(v_unused_282_);
v_unused_283_ = lean_ctor_get(v_impl_153_, 0);
lean_dec(v_unused_283_);
v___x_271_ = v_impl_153_;
v_isShared_272_ = v_isSharedCheck_280_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_v_269_);
lean_inc(v_k_268_);
lean_dec(v_impl_153_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_280_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_273_ = lean_unsigned_to_nat(3u);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 4, v_l_238_);
lean_ctor_set(v___x_271_, 2, v_v_6_);
lean_ctor_set(v___x_271_, 1, v_k_5_);
lean_ctor_set(v___x_271_, 0, v___x_154_);
v___x_275_ = v___x_271_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_154_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_279_, 3, v_l_238_);
lean_ctor_set(v_reuseFailAlloc_279_, 4, v_l_238_);
v___x_275_ = v_reuseFailAlloc_279_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_277_; 
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 4, v_r_267_);
lean_ctor_set(v___x_10_, 3, v___x_275_);
lean_ctor_set(v___x_10_, 2, v_v_269_);
lean_ctor_set(v___x_10_, 1, v_k_268_);
lean_ctor_set(v___x_10_, 0, v___x_273_);
v___x_277_ = v___x_10_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_k_268_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v_v_269_);
lean_ctor_set(v_reuseFailAlloc_278_, 3, v___x_275_);
lean_ctor_set(v_reuseFailAlloc_278_, 4, v_r_267_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
else
{
lean_object* v___x_284_; lean_object* v___x_286_; 
v___x_284_ = lean_unsigned_to_nat(2u);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 4, v_impl_153_);
lean_ctor_set(v___x_10_, 3, v_r_267_);
lean_ctor_set(v___x_10_, 0, v___x_284_);
v___x_286_ = v___x_10_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_287_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_287_, 3, v_r_267_);
lean_ctor_set(v_reuseFailAlloc_287_, 4, v_impl_153_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
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
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = lean_unsigned_to_nat(1u);
v___x_290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v_k_1_);
lean_ctor_set(v___x_290_, 2, v_v_2_);
lean_ctor_set(v___x_290_, 3, v_t_3_);
lean_ctor_set(v___x_290_, 4, v_t_3_);
return v___x_290_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg(lean_object* v_t_291_, lean_object* v_k_292_){
_start:
{
if (lean_obj_tag(v_t_291_) == 0)
{
lean_object* v_k_293_; lean_object* v_v_294_; lean_object* v_l_295_; lean_object* v_r_296_; uint8_t v___x_297_; 
v_k_293_ = lean_ctor_get(v_t_291_, 1);
v_v_294_ = lean_ctor_get(v_t_291_, 2);
v_l_295_ = lean_ctor_get(v_t_291_, 3);
v_r_296_ = lean_ctor_get(v_t_291_, 4);
v___x_297_ = l_Lake_BuildKey_quickCmp(v_k_292_, v_k_293_);
switch(v___x_297_)
{
case 0:
{
v_t_291_ = v_l_295_;
goto _start;
}
case 1:
{
lean_object* v___x_299_; 
lean_inc(v_v_294_);
v___x_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_299_, 0, v_v_294_);
return v___x_299_;
}
default: 
{
v_t_291_ = v_r_296_;
goto _start;
}
}
}
else
{
lean_object* v___x_301_; 
v___x_301_ = lean_box(0);
return v___x_301_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg___boxed(lean_object* v_t_302_, lean_object* v_k_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg(v_t_302_, v_k_303_);
lean_dec_ref(v_k_303_);
lean_dec(v_t_302_);
return v_res_304_;
}
}
static lean_object* _init_l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__3(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__2));
v___x_310_ = l_Lake_BuildTrace_nil(v___x_309_);
return v___x_310_;
}
}
lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex(lean_object* v_info_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
if (lean_obj_tag(v_info_317_) == 0)
{
lean_object* v_package_325_; lean_object* v_target_326_; lean_object* v___x_327_; 
v_package_325_ = lean_ctor_get(v_info_317_, 0);
v_target_326_ = lean_ctor_get(v_info_317_, 1);
v___x_327_ = l_Lake_Package_findTargetDecl_x3f(v_target_326_, v_package_325_);
if (lean_obj_tag(v___x_327_) == 1)
{
lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_371_; 
lean_inc(v_target_326_);
lean_inc_ref(v_package_325_);
v_isSharedCheck_371_ = !lean_is_exclusive(v_info_317_);
if (v_isSharedCheck_371_ == 0)
{
lean_object* v_unused_372_; lean_object* v_unused_373_; 
v_unused_372_ = lean_ctor_get(v_info_317_, 1);
lean_dec(v_unused_372_);
v_unused_373_ = lean_ctor_get(v_info_317_, 0);
lean_dec(v_unused_373_);
v___x_329_ = v_info_317_;
v_isShared_330_ = v_isSharedCheck_371_;
goto v_resetjp_328_;
}
else
{
lean_dec(v_info_317_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_371_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v_val_331_; lean_object* v_name_332_; lean_object* v_kind_333_; lean_object* v_config_334_; uint8_t v___x_335_; 
v_val_331_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_val_331_);
lean_dec_ref_known(v___x_327_, 1);
v_name_332_ = lean_ctor_get(v_val_331_, 1);
lean_inc(v_name_332_);
v_kind_333_ = lean_ctor_get(v_val_331_, 2);
lean_inc(v_kind_333_);
v_config_334_ = lean_ctor_get(v_val_331_, 3);
lean_inc(v_config_334_);
lean_dec(v_val_331_);
v___x_335_ = l_Lean_Name_isAnonymous(v_kind_333_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_344_; 
lean_dec(v_target_326_);
lean_dec_ref(v_a_318_);
v___x_336_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_336_, 0, v_package_325_);
lean_ctor_set(v___x_336_, 1, v_name_332_);
lean_ctor_set(v___x_336_, 2, v_config_334_);
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__0));
v___x_339_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__1));
v___x_340_ = 0;
v___x_341_ = lean_obj_once(&l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__3, &l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__3_once, _init_l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__3);
v___x_342_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_342_, 0, v___x_338_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
lean_ctor_set(v___x_342_, 2, v___x_337_);
lean_ctor_set_uint8(v___x_342_, sizeof(void*)*3, v___x_340_);
lean_ctor_set_uint8(v___x_342_, sizeof(void*)*3 + 1, v___x_335_);
lean_ctor_set_uint8(v___x_342_, sizeof(void*)*3 + 2, v___x_335_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 1, v___x_342_);
lean_ctor_set(v___x_329_, 0, v___x_336_);
v___x_344_ = v___x_329_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v___x_342_);
v___x_344_ = v_reuseFailAlloc_348_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
lean_object* v___x_345_; lean_object* v_job_346_; lean_object* v___x_347_; 
v___x_345_ = lean_task_pure(v___x_344_);
v_job_346_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_346_, 0, v___x_345_);
lean_ctor_set(v_job_346_, 1, v_kind_333_);
lean_ctor_set(v_job_346_, 2, v___x_339_);
lean_ctor_set_uint8(v_job_346_, sizeof(void*)*3, v___x_335_);
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v_job_346_);
lean_ctor_set(v___x_347_, 1, v_a_323_);
return v___x_347_;
}
}
else
{
lean_object* v_keyName_349_; lean_object* v_fetchFn_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_369_; 
lean_dec(v_kind_333_);
lean_dec(v_name_332_);
v_keyName_349_ = lean_ctor_get(v_package_325_, 2);
v_fetchFn_350_ = lean_ctor_get(v_config_334_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v_config_334_);
if (v_isSharedCheck_369_ == 0)
{
lean_object* v_unused_370_; 
v_unused_370_ = lean_ctor_get(v_config_334_, 1);
lean_dec(v_unused_370_);
v___x_352_ = v_config_334_;
v_isShared_353_ = v_isSharedCheck_369_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_fetchFn_350_);
lean_dec(v_config_334_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_369_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v_key_355_; 
lean_inc(v_keyName_349_);
if (v_isShared_353_ == 0)
{
lean_ctor_set_tag(v___x_352_, 3);
lean_ctor_set(v___x_352_, 1, v_target_326_);
lean_ctor_set(v___x_352_, 0, v_keyName_349_);
v_key_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_keyName_349_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_target_326_);
v_key_355_ = v_reuseFailAlloc_368_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_356_ = lean_st_ref_take(v_a_321_);
v___x_357_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg(v___x_356_, v_key_355_);
v___x_358_ = lean_st_ref_put(v_a_321_, v___x_356_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v___x_359_; 
lean_del_object(v___x_329_);
lean_inc_ref(v_a_322_);
lean_inc(v_a_321_);
lean_inc(v_a_320_);
lean_inc(v_a_319_);
v___x_359_ = lean_apply_8(v_fetchFn_350_, v_package_325_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, lean_box(0));
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v_a_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v_a_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_a_360_);
v___x_361_ = lean_st_ref_take(v_a_321_);
v___x_362_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(v_key_355_, v_a_360_, v___x_361_);
v___x_363_ = lean_st_ref_put(v_a_321_, v___x_362_);
return v___x_359_;
}
else
{
lean_dec_ref(v_key_355_);
return v___x_359_;
}
}
else
{
lean_object* v_val_364_; lean_object* v___x_366_; 
lean_dec_ref(v_key_355_);
lean_dec_ref(v_fetchFn_350_);
lean_dec_ref(v_package_325_);
lean_dec_ref(v_a_318_);
v_val_364_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_val_364_);
lean_dec_ref_known(v___x_357_, 1);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 1, v_a_323_);
lean_ctor_set(v___x_329_, 0, v_val_364_);
v___x_366_ = v___x_329_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_val_364_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_a_323_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
lean_dec(v___x_327_);
lean_dec_ref(v_a_318_);
v___x_374_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__4));
v___x_375_ = l_Lake_BuildInfo_key(v_info_317_);
v___x_376_ = l_Lake_BuildKey_toString(v___x_375_);
v___x_377_ = lean_string_append(v___x_374_, v___x_376_);
lean_dec_ref(v___x_376_);
v___x_378_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__5));
v___x_379_ = lean_string_append(v___x_377_, v___x_378_);
v___x_380_ = 3;
v___x_381_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_381_, 0, v___x_379_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*1, v___x_380_);
v___x_382_ = lean_array_get_size(v_a_323_);
v___x_383_ = lean_array_push(v_a_323_, v___x_381_);
v___x_384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_382_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
return v___x_384_;
}
}
else
{
lean_object* v_toContext_385_; lean_object* v_target_386_; lean_object* v_kind_387_; lean_object* v_data_388_; lean_object* v_facet_389_; lean_object* v_facetConfigs_390_; lean_object* v___x_391_; 
v_toContext_385_ = lean_ctor_get(v_a_322_, 1);
v_target_386_ = lean_ctor_get(v_info_317_, 0);
v_kind_387_ = lean_ctor_get(v_info_317_, 1);
v_data_388_ = lean_ctor_get(v_info_317_, 2);
v_facet_389_ = lean_ctor_get(v_info_317_, 3);
v_facetConfigs_390_ = lean_ctor_get(v_toContext_385_, 6);
v___x_391_ = l_Lake_FacetConfigMap_get_x3f(v_facet_389_, v_facetConfigs_390_);
if (lean_obj_tag(v___x_391_) == 1)
{
lean_object* v_val_392_; lean_object* v_kind_393_; lean_object* v_fetchFn_394_; uint8_t v_memoize_395_; uint8_t v___y_397_; uint8_t v___x_410_; 
lean_inc(v_kind_387_);
v_val_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_val_392_);
lean_dec_ref_known(v___x_391_, 1);
v_kind_393_ = lean_ctor_get(v_val_392_, 0);
lean_inc(v_kind_393_);
v_fetchFn_394_ = lean_ctor_get(v_val_392_, 1);
lean_inc_ref(v_fetchFn_394_);
v_memoize_395_ = lean_ctor_get_uint8(v_val_392_, sizeof(void*)*4 + 1);
lean_dec(v_val_392_);
v___x_410_ = lean_name_eq(v_kind_393_, v_kind_387_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; uint8_t v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec_ref(v_fetchFn_394_);
lean_dec_ref(v_a_318_);
v___x_411_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__4));
v___x_412_ = l_Lake_BuildInfo_key(v_info_317_);
v___x_413_ = l_Lake_BuildKey_toString(v___x_412_);
v___x_414_ = lean_string_append(v___x_411_, v___x_413_);
lean_dec_ref(v___x_413_);
v___x_415_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__6));
v___x_416_ = lean_string_append(v___x_414_, v___x_415_);
v___x_417_ = 1;
v___x_418_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_387_, v___x_417_);
v___x_419_ = lean_string_append(v___x_416_, v___x_418_);
lean_dec_ref(v___x_418_);
v___x_420_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__7));
v___x_421_ = lean_string_append(v___x_419_, v___x_420_);
v___x_422_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_393_, v___x_417_);
v___x_423_ = lean_string_append(v___x_421_, v___x_422_);
lean_dec_ref(v___x_422_);
v___x_424_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__8));
v___x_425_ = lean_string_append(v___x_423_, v___x_424_);
v___x_426_ = 3;
v___x_427_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_427_, 0, v___x_425_);
lean_ctor_set_uint8(v___x_427_, sizeof(void*)*1, v___x_426_);
v___x_428_ = lean_array_get_size(v_a_323_);
v___x_429_ = lean_array_push(v_a_323_, v___x_427_);
v___x_430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_428_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
return v___x_430_;
}
else
{
lean_inc(v_facet_389_);
lean_inc(v_data_388_);
lean_inc_ref(v_target_386_);
lean_dec(v_kind_393_);
lean_dec(v_kind_387_);
lean_dec_ref_known(v_info_317_, 4);
if (v___x_410_ == 0)
{
v___y_397_ = v___x_410_;
goto v___jp_396_;
}
else
{
v___y_397_ = v_memoize_395_;
goto v___jp_396_;
}
}
v___jp_396_:
{
if (v___y_397_ == 0)
{
lean_object* v___x_398_; 
lean_dec(v_facet_389_);
lean_dec_ref(v_target_386_);
lean_inc_ref(v_a_322_);
lean_inc(v_a_321_);
lean_inc(v_a_320_);
lean_inc(v_a_319_);
v___x_398_ = lean_apply_8(v_fetchFn_394_, v_data_388_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, lean_box(0));
return v___x_398_;
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_399_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_399_, 0, v_target_386_);
lean_ctor_set(v___x_399_, 1, v_facet_389_);
v___x_400_ = lean_st_ref_take(v_a_321_);
v___x_401_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg(v___x_400_, v___x_399_);
v___x_402_ = lean_st_ref_put(v_a_321_, v___x_400_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v___x_403_; 
lean_inc_ref(v_a_322_);
lean_inc(v_a_321_);
lean_inc(v_a_320_);
lean_inc(v_a_319_);
v___x_403_ = lean_apply_8(v_fetchFn_394_, v_data_388_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, lean_box(0));
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc(v_a_404_);
v___x_405_ = lean_st_ref_take(v_a_321_);
v___x_406_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(v___x_399_, v_a_404_, v___x_405_);
v___x_407_ = lean_st_ref_put(v_a_321_, v___x_406_);
return v___x_403_;
}
else
{
lean_dec_ref_known(v___x_399_, 2);
return v___x_403_;
}
}
else
{
lean_object* v_val_408_; lean_object* v___x_409_; 
lean_dec_ref_known(v___x_399_, 2);
lean_dec_ref(v_fetchFn_394_);
lean_dec(v_data_388_);
lean_dec_ref(v_a_318_);
v_val_408_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_val_408_);
lean_dec_ref_known(v___x_401_, 1);
v___x_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_409_, 0, v_val_408_);
lean_ctor_set(v___x_409_, 1, v_a_323_);
return v___x_409_;
}
}
}
}
else
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; uint8_t v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
lean_inc(v_facet_389_);
lean_dec(v___x_391_);
lean_dec_ref(v_a_318_);
v___x_431_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__4));
v___x_432_ = l_Lake_BuildInfo_key(v_info_317_);
v___x_433_ = l_Lake_BuildKey_toString(v___x_432_);
v___x_434_ = lean_string_append(v___x_431_, v___x_433_);
lean_dec_ref(v___x_433_);
v___x_435_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__9));
v___x_436_ = lean_string_append(v___x_434_, v___x_435_);
v___x_437_ = 1;
v___x_438_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_facet_389_, v___x_437_);
v___x_439_ = lean_string_append(v___x_436_, v___x_438_);
lean_dec_ref(v___x_438_);
v___x_440_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__8));
v___x_441_ = lean_string_append(v___x_439_, v___x_440_);
v___x_442_ = 3;
v___x_443_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_443_, 0, v___x_441_);
lean_ctor_set_uint8(v___x_443_, sizeof(void*)*1, v___x_442_);
v___x_444_ = lean_array_get_size(v_a_323_);
v___x_445_ = lean_array_push(v_a_323_, v___x_443_);
v___x_446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_444_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
return v___x_446_;
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Index_0__Lake_recBuildWithIndex_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_317_ = stack[0].m_obj;
lean_object* v_a_318_ = stack[1].m_obj;
lean_object* v_a_319_ = stack[2].m_obj;
lean_object* v_a_320_ = stack[3].m_obj;
lean_object* v_a_321_ = stack[4].m_obj;
lean_object* v_a_322_ = stack[5].m_obj;
lean_object* v_a_323_ = stack[6].m_obj;
lean_object* v_res_447_;
v_res_447_ = l___private_Lake_Build_Index_0__Lake_recBuildWithIndex(v_info_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
stack->m_obj
 = v_res_447_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___boxed(lean_object* v_info_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l___private_Lake_Build_Index_0__Lake_recBuildWithIndex(v_info_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_);
lean_dec_ref(v_a_453_);
lean_dec(v_a_452_);
lean_dec(v_a_451_);
lean_dec(v_a_450_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0(lean_object* v_00_u03b2_457_, lean_object* v_inst_458_, lean_object* v_t_459_, lean_object* v_k_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg(v_t_459_, v_k_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___boxed(lean_object* v_00_u03b2_462_, lean_object* v_inst_463_, lean_object* v_t_464_, lean_object* v_k_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0(v_00_u03b2_462_, v_inst_463_, v_t_464_, v_k_465_);
lean_dec_ref(v_k_465_);
lean_dec(v_t_464_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1(lean_object* v_00_u03b2_467_, lean_object* v_k_468_, lean_object* v_v_469_, lean_object* v_t_470_, lean_object* v_hl_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(v_k_468_, v_v_469_, v_t_470_);
return v___x_472_;
}
}
uint8_t l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__0(lean_object* v_a_473_, lean_object* v_x_474_){
_start:
{
if (lean_obj_tag(v_x_474_) == 0)
{
uint8_t v___x_475_; 
v___x_475_ = 0;
return v___x_475_;
}
else
{
lean_object* v_head_476_; lean_object* v_tail_477_; uint8_t v___x_478_; 
v_head_476_ = lean_ctor_get(v_x_474_, 0);
v_tail_477_ = lean_ctor_get(v_x_474_, 1);
v___x_478_ = l_Lake_instDecidableEqBuildKey_decEq(v_a_473_, v_head_476_);
if (v___x_478_ == 0)
{
v_x_474_ = v_tail_477_;
goto _start;
}
else
{
return v___x_478_;
}
}
}
}
LEAN_EXPORT void l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_473_ = stack[0].m_obj;
lean_object* v_x_474_ = stack[1].m_obj;
uint8_t v_res_480_;
v_res_480_ = l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__0(v_a_473_, v_x_474_);
stack->m_num = v_res_480_;
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__0___boxed(lean_object* v_a_481_, lean_object* v_x_482_){
_start:
{
uint8_t v_res_483_; lean_object* v_r_484_; 
v_res_483_ = l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__0(v_a_481_, v_x_482_);
lean_dec(v_x_482_);
lean_dec_ref(v_a_481_);
v_r_484_ = lean_box(v_res_483_);
return v_r_484_;
}
}
lean_object* l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__1(lean_object* v___x_485_, uint8_t v___x_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
if (lean_obj_tag(v_a_487_) == 0)
{
lean_object* v_fst_489_; lean_object* v_snd_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_499_; 
v_fst_489_ = lean_ctor_get(v_a_488_, 0);
v_snd_490_ = lean_ctor_get(v_a_488_, 1);
v_isSharedCheck_499_ = !lean_is_exclusive(v_a_488_);
if (v_isSharedCheck_499_ == 0)
{
v___x_492_ = v_a_488_;
v_isShared_493_ = v_isSharedCheck_499_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_snd_490_);
lean_inc(v_fst_489_);
lean_dec(v_a_488_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_499_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_497_; 
v___x_494_ = l_List_reverse___redArg(v_fst_489_);
v___x_495_ = l_List_reverse___redArg(v_snd_490_);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 1, v___x_495_);
lean_ctor_set(v___x_492_, 0, v___x_494_);
v___x_497_ = v___x_492_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_494_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v___x_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
else
{
lean_object* v_head_500_; lean_object* v_tail_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_523_; 
v_head_500_ = lean_ctor_get(v_a_487_, 0);
v_tail_501_ = lean_ctor_get(v_a_487_, 1);
v_isSharedCheck_523_ = !lean_is_exclusive(v_a_487_);
if (v_isSharedCheck_523_ == 0)
{
v___x_503_ = v_a_487_;
v_isShared_504_ = v_isSharedCheck_523_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_tail_501_);
lean_inc(v_head_500_);
lean_dec(v_a_487_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_523_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v_fst_505_; lean_object* v_snd_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_522_; 
v_fst_505_ = lean_ctor_get(v_a_488_, 0);
v_snd_506_ = lean_ctor_get(v_a_488_, 1);
v_isSharedCheck_522_ = !lean_is_exclusive(v_a_488_);
if (v_isSharedCheck_522_ == 0)
{
v___x_508_ = v_a_488_;
v_isShared_509_ = v_isSharedCheck_522_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_snd_506_);
lean_inc(v_fst_505_);
lean_dec(v_a_488_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_522_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
uint8_t v___x_518_; 
v___x_518_ = l_Lake_instDecidableEqBuildKey_decEq(v_head_500_, v___x_485_);
if (v___x_518_ == 0)
{
if (v___x_486_ == 0)
{
goto v___jp_510_;
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; 
lean_del_object(v___x_508_);
lean_del_object(v___x_503_);
v___x_519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_519_, 0, v_head_500_);
lean_ctor_set(v___x_519_, 1, v_fst_505_);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
lean_ctor_set(v___x_520_, 1, v_snd_506_);
v_a_487_ = v_tail_501_;
v_a_488_ = v___x_520_;
goto _start;
}
}
else
{
goto v___jp_510_;
}
v___jp_510_:
{
lean_object* v___x_512_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v_snd_506_);
v___x_512_ = v___x_503_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_head_500_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_snd_506_);
v___x_512_ = v_reuseFailAlloc_517_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_514_; 
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 1, v___x_512_);
v___x_514_ = v___x_508_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_fst_505_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v___x_512_);
v___x_514_ = v_reuseFailAlloc_516_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
v_a_487_ = v_tail_501_;
v_a_488_ = v___x_514_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_485_ = stack[0].m_obj;
uint8_t v___x_486_ = stack[1].m_num;
lean_object* v_a_487_ = stack[2].m_obj;
lean_object* v_a_488_ = stack[3].m_obj;
lean_object* v_res_524_;
v_res_524_ = l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__1(v___x_485_, v___x_486_, v_a_487_, v_a_488_);
stack->m_obj
 = v_res_524_;
}
LEAN_EXPORT lean_object* l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__1___boxed(lean_object* v___x_525_, lean_object* v___x_526_, lean_object* v_a_527_, lean_object* v_a_528_){
_start:
{
uint8_t v___x_3095__boxed_529_; lean_object* v_res_530_; 
v___x_3095__boxed_529_ = lean_unbox(v___x_526_);
v_res_530_ = l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__1(v___x_525_, v___x_3095__boxed_529_, v_a_527_, v_a_528_);
lean_dec_ref(v___x_525_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___lam__0___boxed(lean_object* v___x_531_, lean_object* v_a_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___lam__0(v___x_531_, v_a_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec(v___y_534_);
lean_dec(v___y_533_);
lean_dec(v___x_531_);
return v_res_539_;
}
}
lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(lean_object* v_a_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v___x_549_; uint8_t v___x_550_; 
lean_inc_ref(v_a_542_);
v___x_549_ = l_Lake_BuildInfo_key(v_a_542_);
v___x_550_ = l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__0(v___x_549_, v___y_544_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___f_552_; lean_object* v___x_553_; 
lean_inc(v___y_544_);
v___x_551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_549_);
lean_ctor_set(v___x_551_, 1, v___y_544_);
lean_inc_ref(v___x_551_);
v___f_552_ = lean_alloc_closure((void*)(l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_552_, 0, v___x_551_);
v___x_553_ = l___private_Lake_Build_Index_0__Lake_recBuildWithIndex(v_a_542_, v___f_552_, v___y_543_, v___x_551_, v___y_545_, v___y_546_, v___y_547_);
lean_dec_ref_known(v___x_551_, 2);
return v___x_553_;
}
else
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v_fst_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_572_; 
lean_dec_ref(v_a_542_);
v___x_554_ = lean_box(0);
v___x_555_ = ((lean_object*)(l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___closed__0));
lean_inc(v___y_544_);
v___x_556_ = l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__1(v___x_549_, v___x_550_, v___y_544_, v___x_555_);
v_fst_557_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_572_ == 0)
{
lean_object* v_unused_573_; 
v_unused_573_ = lean_ctor_get(v___x_556_, 1);
lean_dec(v_unused_573_);
v___x_559_ = v___x_556_;
v_isShared_560_ = v_isSharedCheck_572_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_fst_557_);
lean_dec(v___x_556_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_572_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
lean_inc_ref(v___x_549_);
if (v_isShared_560_ == 0)
{
lean_ctor_set_tag(v___x_559_, 1);
lean_ctor_set(v___x_559_, 1, v_fst_557_);
lean_ctor_set(v___x_559_, 0, v___x_549_);
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_fst_557_);
v___x_562_ = v_reuseFailAlloc_571_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_549_);
lean_ctor_set(v___x_563_, 1, v___x_554_);
v___x_564_ = l_List_appendTR___redArg(v___x_562_, v___x_563_);
v___x_565_ = l_Lake_buildCycleError(v___x_564_);
v___x_566_ = 3;
v___x_567_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_567_, 0, v___x_565_);
lean_ctor_set_uint8(v___x_567_, sizeof(void*)*1, v___x_566_);
v___x_568_ = lean_array_get_size(v___y_547_);
v___x_569_ = lean_array_push(v___y_547_, v___x_567_);
v___x_570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_568_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
return v___x_570_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_542_ = stack[0].m_obj;
lean_object* v___y_543_ = stack[1].m_obj;
lean_object* v___y_544_ = stack[2].m_obj;
lean_object* v___y_545_ = stack[3].m_obj;
lean_object* v___y_546_ = stack[4].m_obj;
lean_object* v___y_547_ = stack[5].m_obj;
lean_object* v_res_574_;
v_res_574_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(v_a_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
stack->m_obj
 = v_res_574_;
}
lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___lam__0(lean_object* v___x_575_, lean_object* v_a_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(v_a_576_, v___y_577_, v___x_575_, v___y_579_, v___y_580_, v___y_581_);
return v___x_583_;
}
}
LEAN_EXPORT void l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_575_ = stack[0].m_obj;
lean_object* v_a_576_ = stack[1].m_obj;
lean_object* v___y_577_ = stack[2].m_obj;
lean_object* v___y_578_ = stack[3].m_obj;
lean_object* v___y_579_ = stack[4].m_obj;
lean_object* v___y_580_ = stack[5].m_obj;
lean_object* v___y_581_ = stack[6].m_obj;
lean_object* v_res_584_;
v_res_584_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___lam__0(v___x_575_, v_a_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
stack->m_obj
 = v_res_584_;
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___boxed(lean_object* v_a_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(v_a_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec(v___y_587_);
lean_dec(v___y_586_);
return v_res_592_;
}
}
lean_object* l___private_Lake_Build_Index_0__Lake_recFetchWithIndex(lean_object* v_info_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(v_info_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
return v___x_600_;
}
}
LEAN_EXPORT void l___private_Lake_Build_Index_0__Lake_recFetchWithIndex_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_593_ = stack[0].m_obj;
lean_object* v_a_594_ = stack[1].m_obj;
lean_object* v_a_595_ = stack[2].m_obj;
lean_object* v_a_596_ = stack[3].m_obj;
lean_object* v_a_597_ = stack[4].m_obj;
lean_object* v_a_598_ = stack[5].m_obj;
lean_object* v_res_601_;
v_res_601_ = l___private_Lake_Build_Index_0__Lake_recFetchWithIndex(v_info_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
stack->m_obj
 = v_res_601_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recFetchWithIndex___boxed(lean_object* v_info_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l___private_Lake_Build_Index_0__Lake_recFetchWithIndex(v_info_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_);
lean_dec_ref(v_a_606_);
lean_dec(v_a_605_);
lean_dec(v_a_604_);
lean_dec(v_a_603_);
return v_res_609_;
}
}
lean_object* l_Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0(lean_object* v_a_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(v_a_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
return v___x_617_;
}
}
LEAN_EXPORT void l_Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_610_ = stack[0].m_obj;
lean_object* v___y_611_ = stack[1].m_obj;
lean_object* v___y_612_ = stack[2].m_obj;
lean_object* v___y_613_ = stack[3].m_obj;
lean_object* v___y_614_ = stack[4].m_obj;
lean_object* v___y_615_ = stack[5].m_obj;
lean_object* v_res_618_;
v_res_618_ = l_Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0(v_a_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
stack->m_obj
 = v_res_618_;
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0___boxed(lean_object* v_a_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0(v_a_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec(v___y_621_);
lean_dec(v___y_620_);
return v_res_626_;
}
}
lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2(lean_object* v_inst_627_, lean_object* v_a_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(v_a_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
return v___x_635_;
}
}
LEAN_EXPORT void l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_628_ = stack[1].m_obj;
lean_object* v___y_629_ = stack[2].m_obj;
lean_object* v___y_630_ = stack[3].m_obj;
lean_object* v___y_631_ = stack[4].m_obj;
lean_object* v___y_632_ = stack[5].m_obj;
lean_object* v___y_633_ = stack[6].m_obj;
lean_object* v_res_636_;
v_res_636_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2(lean_box(0), v_a_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
stack->m_obj
 = v_res_636_;
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___boxed(lean_object* v_inst_637_, lean_object* v_a_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2(v_inst_637_, v_a_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec(v___y_640_);
lean_dec(v___y_639_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchT_run___redArg(lean_object* v_x_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = ((lean_object*)(l_Lake_FetchT_run___redArg___closed__0));
lean_inc_ref(v_a_651_);
lean_inc(v_a_650_);
lean_inc(v_a_649_);
lean_inc(v_a_648_);
v___x_653_ = lean_apply_5(v_x_647_, v___x_652_, v_a_648_, v_a_649_, v_a_650_, v_a_651_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchT_run___redArg___boxed(lean_object* v_x_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lake_FetchT_run___redArg(v_x_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_);
lean_dec_ref(v_a_658_);
lean_dec(v_a_657_);
lean_dec(v_a_656_);
lean_dec(v_a_655_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchT_run(lean_object* v_m_660_, lean_object* v_00_u03b1_661_, lean_object* v_x_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = ((lean_object*)(l_Lake_FetchT_run___redArg___closed__0));
lean_inc_ref(v_a_666_);
lean_inc(v_a_665_);
lean_inc(v_a_664_);
lean_inc(v_a_663_);
v___x_668_ = lean_apply_5(v_x_662_, v___x_667_, v_a_663_, v_a_664_, v_a_665_, v_a_666_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchT_run___boxed(lean_object* v_m_669_, lean_object* v_00_u03b1_670_, lean_object* v_x_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lake_FetchT_run(v_m_669_, v_00_u03b1_670_, v_x_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
lean_dec_ref(v_a_675_);
lean_dec(v_a_674_);
lean_dec(v_a_673_);
lean_dec(v_a_672_);
return v_res_676_;
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
