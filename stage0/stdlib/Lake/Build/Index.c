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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_inc(v_size_16_);
v_k_17_ = lean_ctor_get(v_impl_13_, 1);
lean_inc(v_k_17_);
v_v_18_ = lean_ctor_get(v_impl_13_, 2);
lean_inc(v_v_18_);
v_l_19_ = lean_ctor_get(v_impl_13_, 3);
lean_inc(v_l_19_);
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
lean_dec(v_l_19_);
lean_dec(v_v_18_);
lean_dec(v_k_17_);
v___x_24_ = lean_nat_add(v___x_14_, v_size_16_);
lean_dec(v_size_16_);
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
v___x_50_ = lean_nat_add(v___y_47_, v___y_49_);
lean_dec(v___y_49_);
lean_dec(v___y_47_);
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
lean_ctor_set(v___x_30_, 3, v___y_48_);
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
lean_ctor_set(v_reuseFailAlloc_55_, 3, v___y_48_);
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
v___y_47_ = v___x_63_;
v___y_48_ = v___x_62_;
v___y_49_ = v_size_64_;
goto v___jp_46_;
}
else
{
lean_object* v___x_65_; 
v___x_65_ = lean_unsigned_to_nat(0u);
v___y_47_ = v___x_63_;
v___y_48_ = v___x_62_;
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
lean_inc(v_l_100_);
if (lean_obj_tag(v_l_100_) == 0)
{
lean_object* v_r_101_; lean_object* v_k_102_; lean_object* v_v_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_114_; 
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
lean_inc(v_size_156_);
v_k_157_ = lean_ctor_get(v_impl_153_, 1);
lean_inc(v_k_157_);
v_v_158_ = lean_ctor_get(v_impl_153_, 2);
lean_inc(v_v_158_);
v_l_159_ = lean_ctor_get(v_impl_153_, 3);
lean_inc(v_l_159_);
v_r_160_ = lean_ctor_get(v_impl_153_, 4);
lean_inc(v_r_160_);
v___x_161_ = lean_unsigned_to_nat(3u);
v___x_162_ = lean_nat_mul(v___x_161_, v_size_155_);
v___x_163_ = lean_nat_dec_lt(v___x_162_, v_size_156_);
lean_dec(v___x_162_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_167_; 
lean_dec(v_r_160_);
lean_dec(v_l_159_);
lean_dec(v_v_158_);
lean_dec(v_k_157_);
v___x_164_ = lean_nat_add(v___x_154_, v_size_155_);
v___x_165_ = lean_nat_add(v___x_164_, v_size_156_);
lean_dec(v_size_156_);
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
v___x_190_ = lean_nat_add(v___y_187_, v___y_189_);
lean_dec(v___y_189_);
lean_dec(v___y_187_);
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
lean_ctor_set(v___x_170_, 3, v___y_188_);
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
lean_ctor_set(v_reuseFailAlloc_195_, 3, v___y_188_);
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
v___y_187_ = v___x_202_;
v___y_188_ = v___x_201_;
v___y_189_ = v_size_203_;
goto v___jp_186_;
}
else
{
lean_object* v___x_204_; 
v___x_204_ = lean_unsigned_to_nat(0u);
v___y_187_ = v___x_202_;
v___y_188_ = v___x_201_;
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex(lean_object* v_info_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_){
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
lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_364_; 
lean_inc(v_target_326_);
lean_inc_ref(v_package_325_);
v_isSharedCheck_364_ = !lean_is_exclusive(v_info_317_);
if (v_isSharedCheck_364_ == 0)
{
lean_object* v_unused_365_; lean_object* v_unused_366_; 
v_unused_365_ = lean_ctor_get(v_info_317_, 1);
lean_dec(v_unused_365_);
v_unused_366_ = lean_ctor_get(v_info_317_, 0);
lean_dec(v_unused_366_);
v___x_329_ = v_info_317_;
v_isShared_330_ = v_isSharedCheck_364_;
goto v_resetjp_328_;
}
else
{
lean_dec(v_info_317_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_364_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v_val_331_; lean_object* v_name_332_; lean_object* v_kind_333_; lean_object* v_config_334_; uint8_t v___x_335_; 
v_val_331_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_val_331_);
lean_dec_ref(v___x_327_);
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
v___x_342_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_342_, 0, v___x_338_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
lean_ctor_set(v___x_342_, 2, v___x_337_);
lean_ctor_set_uint8(v___x_342_, sizeof(void*)*3, v___x_340_);
lean_ctor_set_uint8(v___x_342_, sizeof(void*)*3 + 1, v___x_335_);
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
lean_object* v_keyName_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v_key_353_; 
lean_dec(v_kind_333_);
lean_dec(v_name_332_);
v_keyName_349_ = lean_ctor_get(v_package_325_, 2);
v___x_350_ = lean_st_ref_take(v_a_321_);
lean_inc(v___x_350_);
v___x_351_ = lean_st_ref_set(v_a_321_, v___x_350_);
lean_inc(v_keyName_349_);
if (v_isShared_330_ == 0)
{
lean_ctor_set_tag(v___x_329_, 3);
lean_ctor_set(v___x_329_, 0, v_keyName_349_);
v_key_353_ = v___x_329_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_keyName_349_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v_target_326_);
v_key_353_ = v_reuseFailAlloc_363_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_354_; 
v___x_354_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg(v___x_350_, v_key_353_);
lean_dec(v___x_350_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_fetchFn_355_; lean_object* v___x_356_; 
v_fetchFn_355_ = lean_ctor_get(v_config_334_, 0);
lean_inc_ref(v_fetchFn_355_);
lean_dec(v_config_334_);
lean_inc_ref(v_a_322_);
lean_inc(v_a_321_);
lean_inc(v_a_320_);
lean_inc(v_a_319_);
v___x_356_ = lean_apply_8(v_fetchFn_355_, v_package_325_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, lean_box(0));
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v_a_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_a_357_);
v___x_358_ = lean_st_ref_take(v_a_321_);
v___x_359_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(v_key_353_, v_a_357_, v___x_358_);
v___x_360_ = lean_st_ref_set(v_a_321_, v___x_359_);
return v___x_356_;
}
else
{
lean_dec_ref(v_key_353_);
return v___x_356_;
}
}
else
{
lean_object* v_val_361_; lean_object* v___x_362_; 
lean_dec_ref(v_key_353_);
lean_dec(v_config_334_);
lean_dec_ref(v_package_325_);
lean_dec_ref(v_a_318_);
v_val_361_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_val_361_);
lean_dec_ref(v___x_354_);
v___x_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_362_, 0, v_val_361_);
lean_ctor_set(v___x_362_, 1, v_a_323_);
return v___x_362_;
}
}
}
}
}
else
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
lean_dec(v___x_327_);
lean_dec_ref(v_a_318_);
v___x_367_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__4));
v___x_368_ = l_Lake_BuildInfo_key(v_info_317_);
v___x_369_ = l_Lake_BuildKey_toString(v___x_368_);
v___x_370_ = lean_string_append(v___x_367_, v___x_369_);
lean_dec_ref(v___x_369_);
v___x_371_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__5));
v___x_372_ = lean_string_append(v___x_370_, v___x_371_);
v___x_373_ = 3;
v___x_374_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_374_, 0, v___x_372_);
lean_ctor_set_uint8(v___x_374_, sizeof(void*)*1, v___x_373_);
v___x_375_ = lean_array_get_size(v_a_323_);
v___x_376_ = lean_array_push(v_a_323_, v___x_374_);
v___x_377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_375_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
return v___x_377_;
}
}
else
{
lean_object* v_toContext_378_; lean_object* v_target_379_; lean_object* v_kind_380_; lean_object* v_data_381_; lean_object* v_facet_382_; lean_object* v_facetConfigs_383_; lean_object* v___x_384_; 
v_toContext_378_ = lean_ctor_get(v_a_322_, 1);
v_target_379_ = lean_ctor_get(v_info_317_, 0);
v_kind_380_ = lean_ctor_get(v_info_317_, 1);
v_data_381_ = lean_ctor_get(v_info_317_, 2);
v_facet_382_ = lean_ctor_get(v_info_317_, 3);
v_facetConfigs_383_ = lean_ctor_get(v_toContext_378_, 6);
v___x_384_ = l_Lake_FacetConfigMap_get_x3f(v_facet_382_, v_facetConfigs_383_);
if (lean_obj_tag(v___x_384_) == 1)
{
lean_object* v_val_385_; lean_object* v_kind_386_; lean_object* v_fetchFn_387_; uint8_t v_memoize_388_; uint8_t v___x_389_; 
lean_inc(v_kind_380_);
v_val_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_val_385_);
lean_dec_ref(v___x_384_);
v_kind_386_ = lean_ctor_get(v_val_385_, 0);
lean_inc(v_kind_386_);
v_fetchFn_387_ = lean_ctor_get(v_val_385_, 1);
lean_inc_ref(v_fetchFn_387_);
v_memoize_388_ = lean_ctor_get_uint8(v_val_385_, sizeof(void*)*4 + 1);
lean_dec(v_val_385_);
v___x_389_ = lean_name_eq(v_kind_386_, v_kind_380_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; uint8_t v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
lean_dec_ref(v_fetchFn_387_);
lean_dec_ref(v_a_318_);
v___x_390_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__4));
v___x_391_ = l_Lake_BuildInfo_key(v_info_317_);
v___x_392_ = l_Lake_BuildKey_toString(v___x_391_);
v___x_393_ = lean_string_append(v___x_390_, v___x_392_);
lean_dec_ref(v___x_392_);
v___x_394_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__6));
v___x_395_ = lean_string_append(v___x_393_, v___x_394_);
v___x_396_ = 1;
v___x_397_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_380_, v___x_396_);
v___x_398_ = lean_string_append(v___x_395_, v___x_397_);
lean_dec_ref(v___x_397_);
v___x_399_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__7));
v___x_400_ = lean_string_append(v___x_398_, v___x_399_);
v___x_401_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_386_, v___x_396_);
v___x_402_ = lean_string_append(v___x_400_, v___x_401_);
lean_dec_ref(v___x_401_);
v___x_403_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__8));
v___x_404_ = lean_string_append(v___x_402_, v___x_403_);
v___x_405_ = 3;
v___x_406_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_406_, 0, v___x_404_);
lean_ctor_set_uint8(v___x_406_, sizeof(void*)*1, v___x_405_);
v___x_407_ = lean_array_get_size(v_a_323_);
v___x_408_ = lean_array_push(v_a_323_, v___x_406_);
v___x_409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_407_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
return v___x_409_;
}
else
{
lean_inc(v_facet_382_);
lean_inc(v_data_381_);
lean_inc_ref(v_target_379_);
lean_dec(v_kind_386_);
lean_dec(v_kind_380_);
lean_dec_ref(v_info_317_);
if (v_memoize_388_ == 0)
{
lean_object* v___x_410_; 
lean_dec(v_facet_382_);
lean_dec_ref(v_target_379_);
lean_inc_ref(v_a_322_);
lean_inc(v_a_321_);
lean_inc(v_a_320_);
lean_inc(v_a_319_);
v___x_410_ = lean_apply_8(v_fetchFn_387_, v_data_381_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, lean_box(0));
return v___x_410_;
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_411_ = lean_st_ref_take(v_a_321_);
lean_inc(v___x_411_);
v___x_412_ = lean_st_ref_set(v_a_321_, v___x_411_);
v___x_413_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_413_, 0, v_target_379_);
lean_ctor_set(v___x_413_, 1, v_facet_382_);
v___x_414_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg(v___x_411_, v___x_413_);
lean_dec(v___x_411_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v___x_415_; 
lean_inc_ref(v_a_322_);
lean_inc(v_a_321_);
lean_inc(v_a_320_);
lean_inc(v_a_319_);
v___x_415_ = lean_apply_8(v_fetchFn_387_, v_data_381_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, lean_box(0));
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_a_416_);
v___x_417_ = lean_st_ref_take(v_a_321_);
v___x_418_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(v___x_413_, v_a_416_, v___x_417_);
v___x_419_ = lean_st_ref_set(v_a_321_, v___x_418_);
return v___x_415_;
}
else
{
lean_dec_ref(v___x_413_);
return v___x_415_;
}
}
else
{
lean_object* v_val_420_; lean_object* v___x_421_; 
lean_dec_ref(v___x_413_);
lean_dec_ref(v_fetchFn_387_);
lean_dec(v_data_381_);
lean_dec_ref(v_a_318_);
v_val_420_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_val_420_);
lean_dec_ref(v___x_414_);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v_val_420_);
lean_ctor_set(v___x_421_, 1, v_a_323_);
return v___x_421_;
}
}
}
}
else
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
lean_inc(v_facet_382_);
lean_dec(v___x_384_);
lean_dec_ref(v_a_318_);
v___x_422_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__4));
v___x_423_ = l_Lake_BuildInfo_key(v_info_317_);
v___x_424_ = l_Lake_BuildKey_toString(v___x_423_);
v___x_425_ = lean_string_append(v___x_422_, v___x_424_);
lean_dec_ref(v___x_424_);
v___x_426_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__9));
v___x_427_ = lean_string_append(v___x_425_, v___x_426_);
v___x_428_ = 1;
v___x_429_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_facet_382_, v___x_428_);
v___x_430_ = lean_string_append(v___x_427_, v___x_429_);
lean_dec_ref(v___x_429_);
v___x_431_ = ((lean_object*)(l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___closed__8));
v___x_432_ = lean_string_append(v___x_430_, v___x_431_);
v___x_433_ = 3;
v___x_434_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_434_, 0, v___x_432_);
lean_ctor_set_uint8(v___x_434_, sizeof(void*)*1, v___x_433_);
v___x_435_ = lean_array_get_size(v_a_323_);
v___x_436_ = lean_array_push(v_a_323_, v___x_434_);
v___x_437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_435_);
lean_ctor_set(v___x_437_, 1, v___x_436_);
return v___x_437_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recBuildWithIndex___boxed(lean_object* v_info_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l___private_Lake_Build_Index_0__Lake_recBuildWithIndex(v_info_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_);
lean_dec_ref(v_a_443_);
lean_dec(v_a_442_);
lean_dec(v_a_441_);
lean_dec(v_a_440_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0(lean_object* v_00_u03b2_447_, lean_object* v_inst_448_, lean_object* v_t_449_, lean_object* v_k_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___redArg(v_t_449_, v_k_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0___boxed(lean_object* v_00_u03b2_452_, lean_object* v_inst_453_, lean_object* v_t_454_, lean_object* v_k_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__0(v_00_u03b2_452_, v_inst_453_, v_t_454_, v_k_455_);
lean_dec_ref(v_k_455_);
lean_dec(v_t_454_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1(lean_object* v_00_u03b2_457_, lean_object* v_k_458_, lean_object* v_v_459_, lean_object* v_t_460_, lean_object* v_hl_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Index_0__Lake_recBuildWithIndex_spec__1___redArg(v_k_458_, v_v_459_, v_t_460_);
return v___x_462_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__0(lean_object* v_a_463_, lean_object* v_x_464_){
_start:
{
if (lean_obj_tag(v_x_464_) == 0)
{
uint8_t v___x_465_; 
v___x_465_ = 0;
return v___x_465_;
}
else
{
lean_object* v_head_466_; lean_object* v_tail_467_; uint8_t v___x_468_; 
v_head_466_ = lean_ctor_get(v_x_464_, 0);
v_tail_467_ = lean_ctor_get(v_x_464_, 1);
v___x_468_ = l_Lake_instDecidableEqBuildKey_decEq(v_a_463_, v_head_466_);
if (v___x_468_ == 0)
{
v_x_464_ = v_tail_467_;
goto _start;
}
else
{
return v___x_468_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__0___boxed(lean_object* v_a_470_, lean_object* v_x_471_){
_start:
{
uint8_t v_res_472_; lean_object* v_r_473_; 
v_res_472_ = l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__0(v_a_470_, v_x_471_);
lean_dec(v_x_471_);
lean_dec_ref(v_a_470_);
v_r_473_ = lean_box(v_res_472_);
return v_r_473_;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__1(lean_object* v___x_474_, uint8_t v___x_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
if (lean_obj_tag(v_a_476_) == 0)
{
lean_object* v_fst_478_; lean_object* v_snd_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_488_; 
v_fst_478_ = lean_ctor_get(v_a_477_, 0);
v_snd_479_ = lean_ctor_get(v_a_477_, 1);
v_isSharedCheck_488_ = !lean_is_exclusive(v_a_477_);
if (v_isSharedCheck_488_ == 0)
{
v___x_481_ = v_a_477_;
v_isShared_482_ = v_isSharedCheck_488_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_snd_479_);
lean_inc(v_fst_478_);
lean_dec(v_a_477_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_488_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_483_ = l_List_reverse___redArg(v_fst_478_);
v___x_484_ = l_List_reverse___redArg(v_snd_479_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 1, v___x_484_);
lean_ctor_set(v___x_481_, 0, v___x_483_);
v___x_486_ = v___x_481_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
else
{
lean_object* v_head_489_; lean_object* v_tail_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_512_; 
v_head_489_ = lean_ctor_get(v_a_476_, 0);
v_tail_490_ = lean_ctor_get(v_a_476_, 1);
v_isSharedCheck_512_ = !lean_is_exclusive(v_a_476_);
if (v_isSharedCheck_512_ == 0)
{
v___x_492_ = v_a_476_;
v_isShared_493_ = v_isSharedCheck_512_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_tail_490_);
lean_inc(v_head_489_);
lean_dec(v_a_476_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_512_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v_fst_494_; lean_object* v_snd_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_511_; 
v_fst_494_ = lean_ctor_get(v_a_477_, 0);
v_snd_495_ = lean_ctor_get(v_a_477_, 1);
v_isSharedCheck_511_ = !lean_is_exclusive(v_a_477_);
if (v_isSharedCheck_511_ == 0)
{
v___x_497_ = v_a_477_;
v_isShared_498_ = v_isSharedCheck_511_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_snd_495_);
lean_inc(v_fst_494_);
lean_dec(v_a_477_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_511_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
uint8_t v___x_507_; 
v___x_507_ = l_Lake_instDecidableEqBuildKey_decEq(v_head_489_, v___x_474_);
if (v___x_507_ == 0)
{
if (v___x_475_ == 0)
{
goto v___jp_499_;
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; 
lean_del_object(v___x_497_);
lean_del_object(v___x_492_);
v___x_508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_508_, 0, v_head_489_);
lean_ctor_set(v___x_508_, 1, v_fst_494_);
v___x_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
lean_ctor_set(v___x_509_, 1, v_snd_495_);
v_a_476_ = v_tail_490_;
v_a_477_ = v___x_509_;
goto _start;
}
}
else
{
goto v___jp_499_;
}
v___jp_499_:
{
lean_object* v___x_501_; 
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 1, v_snd_495_);
v___x_501_ = v___x_492_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_head_489_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v_snd_495_);
v___x_501_ = v_reuseFailAlloc_506_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
lean_object* v___x_503_; 
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 1, v___x_501_);
v___x_503_ = v___x_497_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_fst_494_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v___x_501_);
v___x_503_ = v_reuseFailAlloc_505_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
v_a_476_ = v_tail_490_;
v_a_477_ = v___x_503_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__1___boxed(lean_object* v___x_513_, lean_object* v___x_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
uint8_t v___x_3055__boxed_517_; lean_object* v_res_518_; 
v___x_3055__boxed_517_ = lean_unbox(v___x_514_);
v_res_518_ = l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__1(v___x_513_, v___x_3055__boxed_517_, v_a_515_, v_a_516_);
lean_dec_ref(v___x_513_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___lam__0___boxed(lean_object* v___x_519_, lean_object* v_a_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___lam__0(v___x_519_, v_a_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec(v___y_522_);
lean_dec(v___y_521_);
lean_dec(v___x_519_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(lean_object* v_a_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v___x_537_; uint8_t v___x_538_; 
lean_inc_ref(v_a_530_);
v___x_537_ = l_Lake_BuildInfo_key(v_a_530_);
v___x_538_ = l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__0(v___x_537_, v___y_532_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; lean_object* v___f_540_; lean_object* v___x_541_; 
lean_inc(v___y_532_);
v___x_539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_ctor_set(v___x_539_, 1, v___y_532_);
lean_inc_ref(v___x_539_);
v___f_540_ = lean_alloc_closure((void*)(l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_540_, 0, v___x_539_);
v___x_541_ = l___private_Lake_Build_Index_0__Lake_recBuildWithIndex(v_a_530_, v___f_540_, v___y_531_, v___x_539_, v___y_533_, v___y_534_, v___y_535_);
lean_dec_ref(v___x_539_);
return v___x_541_;
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v_fst_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_560_; 
lean_dec_ref(v_a_530_);
v___x_542_ = lean_box(0);
v___x_543_ = ((lean_object*)(l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___closed__0));
lean_inc(v___y_532_);
v___x_544_ = l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__1(v___x_537_, v___x_538_, v___y_532_, v___x_543_);
v_fst_545_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_560_ == 0)
{
lean_object* v_unused_561_; 
v_unused_561_ = lean_ctor_get(v___x_544_, 1);
lean_dec(v_unused_561_);
v___x_547_ = v___x_544_;
v_isShared_548_ = v_isSharedCheck_560_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_fst_545_);
lean_dec(v___x_544_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_560_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
lean_inc_ref(v___x_537_);
if (v_isShared_548_ == 0)
{
lean_ctor_set_tag(v___x_547_, 1);
lean_ctor_set(v___x_547_, 1, v_fst_545_);
lean_ctor_set(v___x_547_, 0, v___x_537_);
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_537_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_fst_545_);
v___x_550_ = v_reuseFailAlloc_559_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_537_);
lean_ctor_set(v___x_551_, 1, v___x_542_);
v___x_552_ = l_List_appendTR___redArg(v___x_550_, v___x_551_);
v___x_553_ = l_Lake_buildCycleError(v___x_552_);
v___x_554_ = 3;
v___x_555_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_555_, 0, v___x_553_);
lean_ctor_set_uint8(v___x_555_, sizeof(void*)*1, v___x_554_);
v___x_556_ = lean_array_get_size(v___y_535_);
v___x_557_ = lean_array_push(v___y_535_, v___x_555_);
v___x_558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_556_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
return v___x_558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___lam__0(lean_object* v___x_562_, lean_object* v_a_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(v_a_563_, v___y_564_, v___x_562_, v___y_566_, v___y_567_, v___y_568_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg___boxed(lean_object* v_a_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(v_a_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec(v___y_573_);
lean_dec(v___y_572_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recFetchWithIndex(lean_object* v_info_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(v_info_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Index_0__Lake_recFetchWithIndex___boxed(lean_object* v_info_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l___private_Lake_Build_Index_0__Lake_recFetchWithIndex(v_info_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
lean_dec_ref(v_a_591_);
lean_dec(v_a_590_);
lean_dec(v_a_589_);
lean_dec(v_a_588_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0(lean_object* v_a_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(v_a_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0___boxed(lean_object* v_a_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0(v_a_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec(v___y_605_);
lean_dec(v___y_604_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2(lean_object* v_inst_611_, lean_object* v_a_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___redArg(v_a_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2___boxed(lean_object* v_inst_620_, lean_object* v_a_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Build_Index_0__Lake_recFetchWithIndex_spec__0_spec__2(v_inst_620_, v_a_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec(v___y_623_);
lean_dec(v___y_622_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchT_run___redArg(lean_object* v_x_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = ((lean_object*)(l_Lake_FetchT_run___redArg___closed__0));
lean_inc_ref(v_a_634_);
lean_inc(v_a_633_);
lean_inc(v_a_632_);
lean_inc(v_a_631_);
v___x_636_ = lean_apply_5(v_x_630_, v___x_635_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchT_run___redArg___boxed(lean_object* v_x_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lake_FetchT_run___redArg(v_x_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
lean_dec_ref(v_a_641_);
lean_dec(v_a_640_);
lean_dec(v_a_639_);
lean_dec(v_a_638_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchT_run(lean_object* v_m_643_, lean_object* v_00_u03b1_644_, lean_object* v_x_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = ((lean_object*)(l_Lake_FetchT_run___redArg___closed__0));
lean_inc_ref(v_a_649_);
lean_inc(v_a_648_);
lean_inc(v_a_647_);
lean_inc(v_a_646_);
v___x_651_ = lean_apply_5(v_x_645_, v___x_650_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchT_run___boxed(lean_object* v_m_652_, lean_object* v_00_u03b1_653_, lean_object* v_x_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lake_FetchT_run(v_m_652_, v_00_u03b1_653_, v_x_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_);
lean_dec_ref(v_a_658_);
lean_dec(v_a_657_);
lean_dec(v_a_656_);
lean_dec(v_a_655_);
return v_res_659_;
}
}
lean_object* runtime_initialize_Lake_Build_Fetch(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Topological(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_StoreInsts(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Index(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
