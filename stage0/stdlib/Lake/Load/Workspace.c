// Lean compiler output
// Module: Lake.Load.Workspace
// Imports: public import Lake.Load.Config public import Lake.Config.Workspace import Lake.Load.Resolve import Lake.Load.Package import Lake.Load.Lean.Eval import Lake.Load.Toml import Lake.Build.InitFacets
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
lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_searchPathRef;
lean_object* l_Lake_Env_leanSearchPath(lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Lake_loadLakeConfig(lean_object*, lean_object*);
lean_object* l_Lake_resolveConfigFile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_loadConfigFile___redArg(lean_object*, lean_object*);
lean_object* l_Lake_mkPackage(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_computeLakeCache(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lake_initFacetConfigs;
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lake_FacetConfigMap_insert(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* l_Lake_Manifest_load_x3f(lean_object*);
lean_object* l_Lake_Workspace_materializeDeps(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspaceRoot_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspaceRoot_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadWorkspaceRoot_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_loadWorkspaceRoot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "[root]"};
static const lean_object* l_Lake_loadWorkspaceRoot___closed__0 = (const lean_object*)&l_Lake_loadWorkspaceRoot___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_loadWorkspaceRoot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspaceRoot___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadWorkspaceRoot_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_loadWorkspace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_loadWorkspace___closed__0 = (const lean_object*)&l_Lake_loadWorkspace___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_loadWorkspace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateManifest(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateManifest___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspaceRoot_spec__1(lean_object* v_as_1_, size_t v_i_2_, size_t v_stop_3_, lean_object* v_b_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_usize_dec_eq(v_i_2_, v_stop_3_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; lean_object* v_name_7_; lean_object* v_config_8_; lean_object* v___x_9_; size_t v___x_10_; size_t v___x_11_; 
v___x_6_ = lean_array_uget_borrowed(v_as_1_, v_i_2_);
v_name_7_ = lean_ctor_get(v___x_6_, 0);
v_config_8_ = lean_ctor_get(v___x_6_, 1);
lean_inc(v_config_8_);
lean_inc(v_name_7_);
v___x_9_ = l_Lake_FacetConfigMap_insert(v_name_7_, v_config_8_, v_b_4_);
v___x_10_ = ((size_t)1ULL);
v___x_11_ = lean_usize_add(v_i_2_, v___x_10_);
v_i_2_ = v___x_11_;
v_b_4_ = v___x_9_;
goto _start;
}
else
{
return v_b_4_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspaceRoot_spec__1___boxed(lean_object* v_as_13_, lean_object* v_i_14_, lean_object* v_stop_15_, lean_object* v_b_16_){
_start:
{
size_t v_i_boxed_17_; size_t v_stop_boxed_18_; lean_object* v_res_19_; 
v_i_boxed_17_ = lean_unbox_usize(v_i_14_);
lean_dec(v_i_14_);
v_stop_boxed_18_ = lean_unbox_usize(v_stop_15_);
lean_dec(v_stop_15_);
v_res_19_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspaceRoot_spec__1(v_as_13_, v_i_boxed_17_, v_stop_boxed_18_, v_b_16_);
lean_dec_ref(v_as_13_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadWorkspaceRoot_spec__0___redArg(lean_object* v_k_20_, lean_object* v_v_21_, lean_object* v_t_22_){
_start:
{
if (lean_obj_tag(v_t_22_) == 0)
{
lean_object* v_size_23_; lean_object* v_k_24_; lean_object* v_v_25_; lean_object* v_l_26_; lean_object* v_r_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_307_; 
v_size_23_ = lean_ctor_get(v_t_22_, 0);
v_k_24_ = lean_ctor_get(v_t_22_, 1);
v_v_25_ = lean_ctor_get(v_t_22_, 2);
v_l_26_ = lean_ctor_get(v_t_22_, 3);
v_r_27_ = lean_ctor_get(v_t_22_, 4);
v_isSharedCheck_307_ = !lean_is_exclusive(v_t_22_);
if (v_isSharedCheck_307_ == 0)
{
v___x_29_ = v_t_22_;
v_isShared_30_ = v_isSharedCheck_307_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_r_27_);
lean_inc(v_l_26_);
lean_inc(v_v_25_);
lean_inc(v_k_24_);
lean_inc(v_size_23_);
lean_dec(v_t_22_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_307_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
uint8_t v___x_31_; 
v___x_31_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_20_, v_k_24_);
switch(v___x_31_)
{
case 0:
{
lean_object* v_impl_32_; lean_object* v___x_33_; 
lean_dec(v_size_23_);
v_impl_32_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadWorkspaceRoot_spec__0___redArg(v_k_20_, v_v_21_, v_l_26_);
v___x_33_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_27_) == 0)
{
lean_object* v_size_34_; lean_object* v_size_35_; lean_object* v_k_36_; lean_object* v_v_37_; lean_object* v_l_38_; lean_object* v_r_39_; lean_object* v___x_40_; lean_object* v___x_41_; uint8_t v___x_42_; 
v_size_34_ = lean_ctor_get(v_r_27_, 0);
v_size_35_ = lean_ctor_get(v_impl_32_, 0);
v_k_36_ = lean_ctor_get(v_impl_32_, 1);
v_v_37_ = lean_ctor_get(v_impl_32_, 2);
v_l_38_ = lean_ctor_get(v_impl_32_, 3);
v_r_39_ = lean_ctor_get(v_impl_32_, 4);
lean_inc(v_r_39_);
v___x_40_ = lean_unsigned_to_nat(3u);
v___x_41_ = lean_nat_mul(v___x_40_, v_size_34_);
v___x_42_ = lean_nat_dec_lt(v___x_41_, v_size_35_);
lean_dec(v___x_41_);
if (v___x_42_ == 0)
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_46_; 
lean_dec(v_r_39_);
v___x_43_ = lean_nat_add(v___x_33_, v_size_35_);
v___x_44_ = lean_nat_add(v___x_43_, v_size_34_);
lean_dec(v___x_43_);
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 3, v_impl_32_);
lean_ctor_set(v___x_29_, 0, v___x_44_);
v___x_46_ = v___x_29_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v___x_44_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v_k_24_);
lean_ctor_set(v_reuseFailAlloc_47_, 2, v_v_25_);
lean_ctor_set(v_reuseFailAlloc_47_, 3, v_impl_32_);
lean_ctor_set(v_reuseFailAlloc_47_, 4, v_r_27_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
else
{
lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_113_; 
lean_inc(v_l_38_);
lean_inc(v_v_37_);
lean_inc(v_k_36_);
lean_inc(v_size_35_);
v_isSharedCheck_113_ = !lean_is_exclusive(v_impl_32_);
if (v_isSharedCheck_113_ == 0)
{
lean_object* v_unused_114_; lean_object* v_unused_115_; lean_object* v_unused_116_; lean_object* v_unused_117_; lean_object* v_unused_118_; 
v_unused_114_ = lean_ctor_get(v_impl_32_, 4);
lean_dec(v_unused_114_);
v_unused_115_ = lean_ctor_get(v_impl_32_, 3);
lean_dec(v_unused_115_);
v_unused_116_ = lean_ctor_get(v_impl_32_, 2);
lean_dec(v_unused_116_);
v_unused_117_ = lean_ctor_get(v_impl_32_, 1);
lean_dec(v_unused_117_);
v_unused_118_ = lean_ctor_get(v_impl_32_, 0);
lean_dec(v_unused_118_);
v___x_49_ = v_impl_32_;
v_isShared_50_ = v_isSharedCheck_113_;
goto v_resetjp_48_;
}
else
{
lean_dec(v_impl_32_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_113_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v_size_51_; lean_object* v_size_52_; lean_object* v_k_53_; lean_object* v_v_54_; lean_object* v_l_55_; lean_object* v_r_56_; lean_object* v___x_57_; lean_object* v___x_58_; uint8_t v___x_59_; 
v_size_51_ = lean_ctor_get(v_l_38_, 0);
v_size_52_ = lean_ctor_get(v_r_39_, 0);
v_k_53_ = lean_ctor_get(v_r_39_, 1);
v_v_54_ = lean_ctor_get(v_r_39_, 2);
v_l_55_ = lean_ctor_get(v_r_39_, 3);
v_r_56_ = lean_ctor_get(v_r_39_, 4);
v___x_57_ = lean_unsigned_to_nat(2u);
v___x_58_ = lean_nat_mul(v___x_57_, v_size_51_);
v___x_59_ = lean_nat_dec_lt(v_size_52_, v___x_58_);
lean_dec(v___x_58_);
if (v___x_59_ == 0)
{
lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_88_; 
lean_inc(v_r_56_);
lean_inc(v_l_55_);
lean_inc(v_v_54_);
lean_inc(v_k_53_);
v_isSharedCheck_88_ = !lean_is_exclusive(v_r_39_);
if (v_isSharedCheck_88_ == 0)
{
lean_object* v_unused_89_; lean_object* v_unused_90_; lean_object* v_unused_91_; lean_object* v_unused_92_; lean_object* v_unused_93_; 
v_unused_89_ = lean_ctor_get(v_r_39_, 4);
lean_dec(v_unused_89_);
v_unused_90_ = lean_ctor_get(v_r_39_, 3);
lean_dec(v_unused_90_);
v_unused_91_ = lean_ctor_get(v_r_39_, 2);
lean_dec(v_unused_91_);
v_unused_92_ = lean_ctor_get(v_r_39_, 1);
lean_dec(v_unused_92_);
v_unused_93_ = lean_ctor_get(v_r_39_, 0);
lean_dec(v_unused_93_);
v___x_61_ = v_r_39_;
v_isShared_62_ = v_isSharedCheck_88_;
goto v_resetjp_60_;
}
else
{
lean_dec(v_r_39_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_88_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___y_66_; lean_object* v___y_67_; lean_object* v___y_68_; lean_object* v___x_76_; lean_object* v___y_78_; 
v___x_63_ = lean_nat_add(v___x_33_, v_size_35_);
lean_dec(v_size_35_);
v___x_64_ = lean_nat_add(v___x_63_, v_size_34_);
lean_dec(v___x_63_);
v___x_76_ = lean_nat_add(v___x_33_, v_size_51_);
if (lean_obj_tag(v_l_55_) == 0)
{
lean_object* v_size_86_; 
v_size_86_ = lean_ctor_get(v_l_55_, 0);
lean_inc(v_size_86_);
v___y_78_ = v_size_86_;
goto v___jp_77_;
}
else
{
lean_object* v___x_87_; 
v___x_87_ = lean_unsigned_to_nat(0u);
v___y_78_ = v___x_87_;
goto v___jp_77_;
}
v___jp_65_:
{
lean_object* v___x_69_; lean_object* v___x_71_; 
v___x_69_ = lean_nat_add(v___y_66_, v___y_68_);
lean_dec(v___y_68_);
lean_dec(v___y_66_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 4, v_r_27_);
lean_ctor_set(v___x_61_, 3, v_r_56_);
lean_ctor_set(v___x_61_, 2, v_v_25_);
lean_ctor_set(v___x_61_, 1, v_k_24_);
lean_ctor_set(v___x_61_, 0, v___x_69_);
v___x_71_ = v___x_61_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v___x_69_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v_k_24_);
lean_ctor_set(v_reuseFailAlloc_75_, 2, v_v_25_);
lean_ctor_set(v_reuseFailAlloc_75_, 3, v_r_56_);
lean_ctor_set(v_reuseFailAlloc_75_, 4, v_r_27_);
v___x_71_ = v_reuseFailAlloc_75_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
lean_object* v___x_73_; 
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 4, v___x_71_);
lean_ctor_set(v___x_49_, 3, v___y_67_);
lean_ctor_set(v___x_49_, 2, v_v_54_);
lean_ctor_set(v___x_49_, 1, v_k_53_);
lean_ctor_set(v___x_49_, 0, v___x_64_);
v___x_73_ = v___x_49_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_64_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v_k_53_);
lean_ctor_set(v_reuseFailAlloc_74_, 2, v_v_54_);
lean_ctor_set(v_reuseFailAlloc_74_, 3, v___y_67_);
lean_ctor_set(v_reuseFailAlloc_74_, 4, v___x_71_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
v___jp_77_:
{
lean_object* v___x_79_; lean_object* v___x_81_; 
v___x_79_ = lean_nat_add(v___x_76_, v___y_78_);
lean_dec(v___y_78_);
lean_dec(v___x_76_);
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 4, v_l_55_);
lean_ctor_set(v___x_29_, 3, v_l_38_);
lean_ctor_set(v___x_29_, 2, v_v_37_);
lean_ctor_set(v___x_29_, 1, v_k_36_);
lean_ctor_set(v___x_29_, 0, v___x_79_);
v___x_81_ = v___x_29_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v___x_79_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v_k_36_);
lean_ctor_set(v_reuseFailAlloc_85_, 2, v_v_37_);
lean_ctor_set(v_reuseFailAlloc_85_, 3, v_l_38_);
lean_ctor_set(v_reuseFailAlloc_85_, 4, v_l_55_);
v___x_81_ = v_reuseFailAlloc_85_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
lean_object* v___x_82_; 
v___x_82_ = lean_nat_add(v___x_33_, v_size_34_);
if (lean_obj_tag(v_r_56_) == 0)
{
lean_object* v_size_83_; 
v_size_83_ = lean_ctor_get(v_r_56_, 0);
lean_inc(v_size_83_);
v___y_66_ = v___x_82_;
v___y_67_ = v___x_81_;
v___y_68_ = v_size_83_;
goto v___jp_65_;
}
else
{
lean_object* v___x_84_; 
v___x_84_ = lean_unsigned_to_nat(0u);
v___y_66_ = v___x_82_;
v___y_67_ = v___x_81_;
v___y_68_ = v___x_84_;
goto v___jp_65_;
}
}
}
}
}
else
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_99_; 
lean_del_object(v___x_29_);
v___x_94_ = lean_nat_add(v___x_33_, v_size_35_);
lean_dec(v_size_35_);
v___x_95_ = lean_nat_add(v___x_94_, v_size_34_);
lean_dec(v___x_94_);
v___x_96_ = lean_nat_add(v___x_33_, v_size_34_);
v___x_97_ = lean_nat_add(v___x_96_, v_size_52_);
lean_dec(v___x_96_);
lean_inc_ref(v_r_27_);
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 4, v_r_27_);
lean_ctor_set(v___x_49_, 3, v_r_39_);
lean_ctor_set(v___x_49_, 2, v_v_25_);
lean_ctor_set(v___x_49_, 1, v_k_24_);
lean_ctor_set(v___x_49_, 0, v___x_97_);
v___x_99_ = v___x_49_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_97_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v_k_24_);
lean_ctor_set(v_reuseFailAlloc_112_, 2, v_v_25_);
lean_ctor_set(v_reuseFailAlloc_112_, 3, v_r_39_);
lean_ctor_set(v_reuseFailAlloc_112_, 4, v_r_27_);
v___x_99_ = v_reuseFailAlloc_112_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_106_; 
v_isSharedCheck_106_ = !lean_is_exclusive(v_r_27_);
if (v_isSharedCheck_106_ == 0)
{
lean_object* v_unused_107_; lean_object* v_unused_108_; lean_object* v_unused_109_; lean_object* v_unused_110_; lean_object* v_unused_111_; 
v_unused_107_ = lean_ctor_get(v_r_27_, 4);
lean_dec(v_unused_107_);
v_unused_108_ = lean_ctor_get(v_r_27_, 3);
lean_dec(v_unused_108_);
v_unused_109_ = lean_ctor_get(v_r_27_, 2);
lean_dec(v_unused_109_);
v_unused_110_ = lean_ctor_get(v_r_27_, 1);
lean_dec(v_unused_110_);
v_unused_111_ = lean_ctor_get(v_r_27_, 0);
lean_dec(v_unused_111_);
v___x_101_ = v_r_27_;
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
else
{
lean_dec(v_r_27_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_104_; 
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 4, v___x_99_);
lean_ctor_set(v___x_101_, 3, v_l_38_);
lean_ctor_set(v___x_101_, 2, v_v_37_);
lean_ctor_set(v___x_101_, 1, v_k_36_);
lean_ctor_set(v___x_101_, 0, v___x_95_);
v___x_104_ = v___x_101_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_95_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v_k_36_);
lean_ctor_set(v_reuseFailAlloc_105_, 2, v_v_37_);
lean_ctor_set(v_reuseFailAlloc_105_, 3, v_l_38_);
lean_ctor_set(v_reuseFailAlloc_105_, 4, v___x_99_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_119_; 
v_l_119_ = lean_ctor_get(v_impl_32_, 3);
if (lean_obj_tag(v_l_119_) == 0)
{
lean_object* v_r_120_; lean_object* v_k_121_; lean_object* v_v_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_133_; 
lean_inc_ref(v_l_119_);
v_r_120_ = lean_ctor_get(v_impl_32_, 4);
v_k_121_ = lean_ctor_get(v_impl_32_, 1);
v_v_122_ = lean_ctor_get(v_impl_32_, 2);
v_isSharedCheck_133_ = !lean_is_exclusive(v_impl_32_);
if (v_isSharedCheck_133_ == 0)
{
lean_object* v_unused_134_; lean_object* v_unused_135_; 
v_unused_134_ = lean_ctor_get(v_impl_32_, 3);
lean_dec(v_unused_134_);
v_unused_135_ = lean_ctor_get(v_impl_32_, 0);
lean_dec(v_unused_135_);
v___x_124_ = v_impl_32_;
v_isShared_125_ = v_isSharedCheck_133_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_r_120_);
lean_inc(v_v_122_);
lean_inc(v_k_121_);
lean_dec(v_impl_32_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_133_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_126_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_120_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 3, v_r_120_);
lean_ctor_set(v___x_124_, 2, v_v_25_);
lean_ctor_set(v___x_124_, 1, v_k_24_);
lean_ctor_set(v___x_124_, 0, v___x_33_);
v___x_128_ = v___x_124_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_33_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v_k_24_);
lean_ctor_set(v_reuseFailAlloc_132_, 2, v_v_25_);
lean_ctor_set(v_reuseFailAlloc_132_, 3, v_r_120_);
lean_ctor_set(v_reuseFailAlloc_132_, 4, v_r_120_);
v___x_128_ = v_reuseFailAlloc_132_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
lean_object* v___x_130_; 
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 4, v___x_128_);
lean_ctor_set(v___x_29_, 3, v_l_119_);
lean_ctor_set(v___x_29_, 2, v_v_122_);
lean_ctor_set(v___x_29_, 1, v_k_121_);
lean_ctor_set(v___x_29_, 0, v___x_126_);
v___x_130_ = v___x_29_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_126_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v_k_121_);
lean_ctor_set(v_reuseFailAlloc_131_, 2, v_v_122_);
lean_ctor_set(v_reuseFailAlloc_131_, 3, v_l_119_);
lean_ctor_set(v_reuseFailAlloc_131_, 4, v___x_128_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
else
{
lean_object* v_r_136_; 
v_r_136_ = lean_ctor_get(v_impl_32_, 4);
lean_inc(v_r_136_);
if (lean_obj_tag(v_r_136_) == 0)
{
lean_object* v_k_137_; lean_object* v_v_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_161_; 
lean_inc(v_l_119_);
v_k_137_ = lean_ctor_get(v_impl_32_, 1);
v_v_138_ = lean_ctor_get(v_impl_32_, 2);
v_isSharedCheck_161_ = !lean_is_exclusive(v_impl_32_);
if (v_isSharedCheck_161_ == 0)
{
lean_object* v_unused_162_; lean_object* v_unused_163_; lean_object* v_unused_164_; 
v_unused_162_ = lean_ctor_get(v_impl_32_, 4);
lean_dec(v_unused_162_);
v_unused_163_ = lean_ctor_get(v_impl_32_, 3);
lean_dec(v_unused_163_);
v_unused_164_ = lean_ctor_get(v_impl_32_, 0);
lean_dec(v_unused_164_);
v___x_140_ = v_impl_32_;
v_isShared_141_ = v_isSharedCheck_161_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_v_138_);
lean_inc(v_k_137_);
lean_dec(v_impl_32_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_161_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v_k_142_; lean_object* v_v_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_157_; 
v_k_142_ = lean_ctor_get(v_r_136_, 1);
v_v_143_ = lean_ctor_get(v_r_136_, 2);
v_isSharedCheck_157_ = !lean_is_exclusive(v_r_136_);
if (v_isSharedCheck_157_ == 0)
{
lean_object* v_unused_158_; lean_object* v_unused_159_; lean_object* v_unused_160_; 
v_unused_158_ = lean_ctor_get(v_r_136_, 4);
lean_dec(v_unused_158_);
v_unused_159_ = lean_ctor_get(v_r_136_, 3);
lean_dec(v_unused_159_);
v_unused_160_ = lean_ctor_get(v_r_136_, 0);
lean_dec(v_unused_160_);
v___x_145_ = v_r_136_;
v_isShared_146_ = v_isSharedCheck_157_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_v_143_);
lean_inc(v_k_142_);
lean_dec(v_r_136_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_157_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_147_; lean_object* v___x_149_; 
v___x_147_ = lean_unsigned_to_nat(3u);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 4, v_l_119_);
lean_ctor_set(v___x_145_, 3, v_l_119_);
lean_ctor_set(v___x_145_, 2, v_v_138_);
lean_ctor_set(v___x_145_, 1, v_k_137_);
lean_ctor_set(v___x_145_, 0, v___x_33_);
v___x_149_ = v___x_145_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_33_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_k_137_);
lean_ctor_set(v_reuseFailAlloc_156_, 2, v_v_138_);
lean_ctor_set(v_reuseFailAlloc_156_, 3, v_l_119_);
lean_ctor_set(v_reuseFailAlloc_156_, 4, v_l_119_);
v___x_149_ = v_reuseFailAlloc_156_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
lean_object* v___x_151_; 
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 4, v_l_119_);
lean_ctor_set(v___x_140_, 2, v_v_25_);
lean_ctor_set(v___x_140_, 1, v_k_24_);
lean_ctor_set(v___x_140_, 0, v___x_33_);
v___x_151_ = v___x_140_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_33_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_k_24_);
lean_ctor_set(v_reuseFailAlloc_155_, 2, v_v_25_);
lean_ctor_set(v_reuseFailAlloc_155_, 3, v_l_119_);
lean_ctor_set(v_reuseFailAlloc_155_, 4, v_l_119_);
v___x_151_ = v_reuseFailAlloc_155_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_153_; 
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 4, v___x_151_);
lean_ctor_set(v___x_29_, 3, v___x_149_);
lean_ctor_set(v___x_29_, 2, v_v_143_);
lean_ctor_set(v___x_29_, 1, v_k_142_);
lean_ctor_set(v___x_29_, 0, v___x_147_);
v___x_153_ = v___x_29_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_147_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_k_142_);
lean_ctor_set(v_reuseFailAlloc_154_, 2, v_v_143_);
lean_ctor_set(v_reuseFailAlloc_154_, 3, v___x_149_);
lean_ctor_set(v_reuseFailAlloc_154_, 4, v___x_151_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
}
}
else
{
lean_object* v___x_165_; lean_object* v___x_167_; 
v___x_165_ = lean_unsigned_to_nat(2u);
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 4, v_r_136_);
lean_ctor_set(v___x_29_, 3, v_impl_32_);
lean_ctor_set(v___x_29_, 0, v___x_165_);
v___x_167_ = v___x_29_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_k_24_);
lean_ctor_set(v_reuseFailAlloc_168_, 2, v_v_25_);
lean_ctor_set(v_reuseFailAlloc_168_, 3, v_impl_32_);
lean_ctor_set(v_reuseFailAlloc_168_, 4, v_r_136_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
}
case 1:
{
lean_object* v___x_170_; 
lean_dec(v_v_25_);
lean_dec(v_k_24_);
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 2, v_v_21_);
lean_ctor_set(v___x_29_, 1, v_k_20_);
v___x_170_ = v___x_29_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_size_23_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_k_20_);
lean_ctor_set(v_reuseFailAlloc_171_, 2, v_v_21_);
lean_ctor_set(v_reuseFailAlloc_171_, 3, v_l_26_);
lean_ctor_set(v_reuseFailAlloc_171_, 4, v_r_27_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
default: 
{
lean_object* v_impl_172_; lean_object* v___x_173_; 
lean_dec(v_size_23_);
v_impl_172_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadWorkspaceRoot_spec__0___redArg(v_k_20_, v_v_21_, v_r_27_);
v___x_173_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_26_) == 0)
{
lean_object* v_size_174_; lean_object* v_size_175_; lean_object* v_k_176_; lean_object* v_v_177_; lean_object* v_l_178_; lean_object* v_r_179_; lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; 
v_size_174_ = lean_ctor_get(v_l_26_, 0);
v_size_175_ = lean_ctor_get(v_impl_172_, 0);
v_k_176_ = lean_ctor_get(v_impl_172_, 1);
v_v_177_ = lean_ctor_get(v_impl_172_, 2);
v_l_178_ = lean_ctor_get(v_impl_172_, 3);
lean_inc(v_l_178_);
v_r_179_ = lean_ctor_get(v_impl_172_, 4);
v___x_180_ = lean_unsigned_to_nat(3u);
v___x_181_ = lean_nat_mul(v___x_180_, v_size_174_);
v___x_182_ = lean_nat_dec_lt(v___x_181_, v_size_175_);
lean_dec(v___x_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_186_; 
lean_dec(v_l_178_);
v___x_183_ = lean_nat_add(v___x_173_, v_size_174_);
v___x_184_ = lean_nat_add(v___x_183_, v_size_175_);
lean_dec(v___x_183_);
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 4, v_impl_172_);
lean_ctor_set(v___x_29_, 0, v___x_184_);
v___x_186_ = v___x_29_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v_k_24_);
lean_ctor_set(v_reuseFailAlloc_187_, 2, v_v_25_);
lean_ctor_set(v_reuseFailAlloc_187_, 3, v_l_26_);
lean_ctor_set(v_reuseFailAlloc_187_, 4, v_impl_172_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
else
{
lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_251_; 
lean_inc(v_r_179_);
lean_inc(v_v_177_);
lean_inc(v_k_176_);
lean_inc(v_size_175_);
v_isSharedCheck_251_ = !lean_is_exclusive(v_impl_172_);
if (v_isSharedCheck_251_ == 0)
{
lean_object* v_unused_252_; lean_object* v_unused_253_; lean_object* v_unused_254_; lean_object* v_unused_255_; lean_object* v_unused_256_; 
v_unused_252_ = lean_ctor_get(v_impl_172_, 4);
lean_dec(v_unused_252_);
v_unused_253_ = lean_ctor_get(v_impl_172_, 3);
lean_dec(v_unused_253_);
v_unused_254_ = lean_ctor_get(v_impl_172_, 2);
lean_dec(v_unused_254_);
v_unused_255_ = lean_ctor_get(v_impl_172_, 1);
lean_dec(v_unused_255_);
v_unused_256_ = lean_ctor_get(v_impl_172_, 0);
lean_dec(v_unused_256_);
v___x_189_ = v_impl_172_;
v_isShared_190_ = v_isSharedCheck_251_;
goto v_resetjp_188_;
}
else
{
lean_dec(v_impl_172_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_251_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v_size_191_; lean_object* v_k_192_; lean_object* v_v_193_; lean_object* v_l_194_; lean_object* v_r_195_; lean_object* v_size_196_; lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v_size_191_ = lean_ctor_get(v_l_178_, 0);
v_k_192_ = lean_ctor_get(v_l_178_, 1);
v_v_193_ = lean_ctor_get(v_l_178_, 2);
v_l_194_ = lean_ctor_get(v_l_178_, 3);
v_r_195_ = lean_ctor_get(v_l_178_, 4);
v_size_196_ = lean_ctor_get(v_r_179_, 0);
v___x_197_ = lean_unsigned_to_nat(2u);
v___x_198_ = lean_nat_mul(v___x_197_, v_size_196_);
v___x_199_ = lean_nat_dec_lt(v_size_191_, v___x_198_);
lean_dec(v___x_198_);
if (v___x_199_ == 0)
{
lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_227_; 
lean_inc(v_r_195_);
lean_inc(v_l_194_);
lean_inc(v_v_193_);
lean_inc(v_k_192_);
v_isSharedCheck_227_ = !lean_is_exclusive(v_l_178_);
if (v_isSharedCheck_227_ == 0)
{
lean_object* v_unused_228_; lean_object* v_unused_229_; lean_object* v_unused_230_; lean_object* v_unused_231_; lean_object* v_unused_232_; 
v_unused_228_ = lean_ctor_get(v_l_178_, 4);
lean_dec(v_unused_228_);
v_unused_229_ = lean_ctor_get(v_l_178_, 3);
lean_dec(v_unused_229_);
v_unused_230_ = lean_ctor_get(v_l_178_, 2);
lean_dec(v_unused_230_);
v_unused_231_ = lean_ctor_get(v_l_178_, 1);
lean_dec(v_unused_231_);
v_unused_232_ = lean_ctor_get(v_l_178_, 0);
lean_dec(v_unused_232_);
v___x_201_ = v_l_178_;
v_isShared_202_ = v_isSharedCheck_227_;
goto v_resetjp_200_;
}
else
{
lean_dec(v_l_178_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_227_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___y_206_; lean_object* v___y_207_; lean_object* v___y_208_; lean_object* v___y_217_; 
v___x_203_ = lean_nat_add(v___x_173_, v_size_174_);
v___x_204_ = lean_nat_add(v___x_203_, v_size_175_);
lean_dec(v_size_175_);
if (lean_obj_tag(v_l_194_) == 0)
{
lean_object* v_size_225_; 
v_size_225_ = lean_ctor_get(v_l_194_, 0);
lean_inc(v_size_225_);
v___y_217_ = v_size_225_;
goto v___jp_216_;
}
else
{
lean_object* v___x_226_; 
v___x_226_ = lean_unsigned_to_nat(0u);
v___y_217_ = v___x_226_;
goto v___jp_216_;
}
v___jp_205_:
{
lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_209_ = lean_nat_add(v___y_206_, v___y_208_);
lean_dec(v___y_208_);
lean_dec(v___y_206_);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 4, v_r_179_);
lean_ctor_set(v___x_201_, 3, v_r_195_);
lean_ctor_set(v___x_201_, 2, v_v_177_);
lean_ctor_set(v___x_201_, 1, v_k_176_);
lean_ctor_set(v___x_201_, 0, v___x_209_);
v___x_211_ = v___x_201_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_209_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_k_176_);
lean_ctor_set(v_reuseFailAlloc_215_, 2, v_v_177_);
lean_ctor_set(v_reuseFailAlloc_215_, 3, v_r_195_);
lean_ctor_set(v_reuseFailAlloc_215_, 4, v_r_179_);
v___x_211_ = v_reuseFailAlloc_215_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_object* v___x_213_; 
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 4, v___x_211_);
lean_ctor_set(v___x_189_, 3, v___y_207_);
lean_ctor_set(v___x_189_, 2, v_v_193_);
lean_ctor_set(v___x_189_, 1, v_k_192_);
lean_ctor_set(v___x_189_, 0, v___x_204_);
v___x_213_ = v___x_189_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_204_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_k_192_);
lean_ctor_set(v_reuseFailAlloc_214_, 2, v_v_193_);
lean_ctor_set(v_reuseFailAlloc_214_, 3, v___y_207_);
lean_ctor_set(v_reuseFailAlloc_214_, 4, v___x_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
v___jp_216_:
{
lean_object* v___x_218_; lean_object* v___x_220_; 
v___x_218_ = lean_nat_add(v___x_203_, v___y_217_);
lean_dec(v___y_217_);
lean_dec(v___x_203_);
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 4, v_l_194_);
lean_ctor_set(v___x_29_, 0, v___x_218_);
v___x_220_ = v___x_29_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_218_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_k_24_);
lean_ctor_set(v_reuseFailAlloc_224_, 2, v_v_25_);
lean_ctor_set(v_reuseFailAlloc_224_, 3, v_l_26_);
lean_ctor_set(v_reuseFailAlloc_224_, 4, v_l_194_);
v___x_220_ = v_reuseFailAlloc_224_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
lean_object* v___x_221_; 
v___x_221_ = lean_nat_add(v___x_173_, v_size_196_);
if (lean_obj_tag(v_r_195_) == 0)
{
lean_object* v_size_222_; 
v_size_222_ = lean_ctor_get(v_r_195_, 0);
lean_inc(v_size_222_);
v___y_206_ = v___x_221_;
v___y_207_ = v___x_220_;
v___y_208_ = v_size_222_;
goto v___jp_205_;
}
else
{
lean_object* v___x_223_; 
v___x_223_ = lean_unsigned_to_nat(0u);
v___y_206_ = v___x_221_;
v___y_207_ = v___x_220_;
v___y_208_ = v___x_223_;
goto v___jp_205_;
}
}
}
}
}
else
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_237_; 
lean_del_object(v___x_29_);
v___x_233_ = lean_nat_add(v___x_173_, v_size_174_);
v___x_234_ = lean_nat_add(v___x_233_, v_size_175_);
lean_dec(v_size_175_);
v___x_235_ = lean_nat_add(v___x_233_, v_size_191_);
lean_dec(v___x_233_);
lean_inc_ref(v_l_26_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 4, v_l_178_);
lean_ctor_set(v___x_189_, 3, v_l_26_);
lean_ctor_set(v___x_189_, 2, v_v_25_);
lean_ctor_set(v___x_189_, 1, v_k_24_);
lean_ctor_set(v___x_189_, 0, v___x_235_);
v___x_237_ = v___x_189_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_k_24_);
lean_ctor_set(v_reuseFailAlloc_250_, 2, v_v_25_);
lean_ctor_set(v_reuseFailAlloc_250_, 3, v_l_26_);
lean_ctor_set(v_reuseFailAlloc_250_, 4, v_l_178_);
v___x_237_ = v_reuseFailAlloc_250_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
v_isSharedCheck_244_ = !lean_is_exclusive(v_l_26_);
if (v_isSharedCheck_244_ == 0)
{
lean_object* v_unused_245_; lean_object* v_unused_246_; lean_object* v_unused_247_; lean_object* v_unused_248_; lean_object* v_unused_249_; 
v_unused_245_ = lean_ctor_get(v_l_26_, 4);
lean_dec(v_unused_245_);
v_unused_246_ = lean_ctor_get(v_l_26_, 3);
lean_dec(v_unused_246_);
v_unused_247_ = lean_ctor_get(v_l_26_, 2);
lean_dec(v_unused_247_);
v_unused_248_ = lean_ctor_get(v_l_26_, 1);
lean_dec(v_unused_248_);
v_unused_249_ = lean_ctor_get(v_l_26_, 0);
lean_dec(v_unused_249_);
v___x_239_ = v_l_26_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_dec(v_l_26_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 4, v_r_179_);
lean_ctor_set(v___x_239_, 3, v___x_237_);
lean_ctor_set(v___x_239_, 2, v_v_177_);
lean_ctor_set(v___x_239_, 1, v_k_176_);
lean_ctor_set(v___x_239_, 0, v___x_234_);
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_k_176_);
lean_ctor_set(v_reuseFailAlloc_243_, 2, v_v_177_);
lean_ctor_set(v_reuseFailAlloc_243_, 3, v___x_237_);
lean_ctor_set(v_reuseFailAlloc_243_, 4, v_r_179_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_257_; 
v_l_257_ = lean_ctor_get(v_impl_172_, 3);
lean_inc(v_l_257_);
if (lean_obj_tag(v_l_257_) == 0)
{
lean_object* v_r_258_; lean_object* v_k_259_; lean_object* v_v_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_283_; 
v_r_258_ = lean_ctor_get(v_impl_172_, 4);
v_k_259_ = lean_ctor_get(v_impl_172_, 1);
v_v_260_ = lean_ctor_get(v_impl_172_, 2);
v_isSharedCheck_283_ = !lean_is_exclusive(v_impl_172_);
if (v_isSharedCheck_283_ == 0)
{
lean_object* v_unused_284_; lean_object* v_unused_285_; 
v_unused_284_ = lean_ctor_get(v_impl_172_, 3);
lean_dec(v_unused_284_);
v_unused_285_ = lean_ctor_get(v_impl_172_, 0);
lean_dec(v_unused_285_);
v___x_262_ = v_impl_172_;
v_isShared_263_ = v_isSharedCheck_283_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_r_258_);
lean_inc(v_v_260_);
lean_inc(v_k_259_);
lean_dec(v_impl_172_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_283_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v_k_264_; lean_object* v_v_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_279_; 
v_k_264_ = lean_ctor_get(v_l_257_, 1);
v_v_265_ = lean_ctor_get(v_l_257_, 2);
v_isSharedCheck_279_ = !lean_is_exclusive(v_l_257_);
if (v_isSharedCheck_279_ == 0)
{
lean_object* v_unused_280_; lean_object* v_unused_281_; lean_object* v_unused_282_; 
v_unused_280_ = lean_ctor_get(v_l_257_, 4);
lean_dec(v_unused_280_);
v_unused_281_ = lean_ctor_get(v_l_257_, 3);
lean_dec(v_unused_281_);
v_unused_282_ = lean_ctor_get(v_l_257_, 0);
lean_dec(v_unused_282_);
v___x_267_ = v_l_257_;
v_isShared_268_ = v_isSharedCheck_279_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_v_265_);
lean_inc(v_k_264_);
lean_dec(v_l_257_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_279_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_269_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_258_, 2);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 4, v_r_258_);
lean_ctor_set(v___x_267_, 3, v_r_258_);
lean_ctor_set(v___x_267_, 2, v_v_25_);
lean_ctor_set(v___x_267_, 1, v_k_24_);
lean_ctor_set(v___x_267_, 0, v___x_173_);
v___x_271_ = v___x_267_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_173_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_k_24_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v_v_25_);
lean_ctor_set(v_reuseFailAlloc_278_, 3, v_r_258_);
lean_ctor_set(v_reuseFailAlloc_278_, 4, v_r_258_);
v___x_271_ = v_reuseFailAlloc_278_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_273_; 
lean_inc(v_r_258_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 3, v_r_258_);
lean_ctor_set(v___x_262_, 0, v___x_173_);
v___x_273_ = v___x_262_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_173_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_k_259_);
lean_ctor_set(v_reuseFailAlloc_277_, 2, v_v_260_);
lean_ctor_set(v_reuseFailAlloc_277_, 3, v_r_258_);
lean_ctor_set(v_reuseFailAlloc_277_, 4, v_r_258_);
v___x_273_ = v_reuseFailAlloc_277_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
lean_object* v___x_275_; 
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 4, v___x_273_);
lean_ctor_set(v___x_29_, 3, v___x_271_);
lean_ctor_set(v___x_29_, 2, v_v_265_);
lean_ctor_set(v___x_29_, 1, v_k_264_);
lean_ctor_set(v___x_29_, 0, v___x_269_);
v___x_275_ = v___x_29_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_269_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v_k_264_);
lean_ctor_set(v_reuseFailAlloc_276_, 2, v_v_265_);
lean_ctor_set(v_reuseFailAlloc_276_, 3, v___x_271_);
lean_ctor_set(v_reuseFailAlloc_276_, 4, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
}
}
else
{
lean_object* v_r_286_; 
v_r_286_ = lean_ctor_get(v_impl_172_, 4);
lean_inc(v_r_286_);
if (lean_obj_tag(v_r_286_) == 0)
{
lean_object* v_k_287_; lean_object* v_v_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_299_; 
v_k_287_ = lean_ctor_get(v_impl_172_, 1);
v_v_288_ = lean_ctor_get(v_impl_172_, 2);
v_isSharedCheck_299_ = !lean_is_exclusive(v_impl_172_);
if (v_isSharedCheck_299_ == 0)
{
lean_object* v_unused_300_; lean_object* v_unused_301_; lean_object* v_unused_302_; 
v_unused_300_ = lean_ctor_get(v_impl_172_, 4);
lean_dec(v_unused_300_);
v_unused_301_ = lean_ctor_get(v_impl_172_, 3);
lean_dec(v_unused_301_);
v_unused_302_ = lean_ctor_get(v_impl_172_, 0);
lean_dec(v_unused_302_);
v___x_290_ = v_impl_172_;
v_isShared_291_ = v_isSharedCheck_299_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_v_288_);
lean_inc(v_k_287_);
lean_dec(v_impl_172_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_299_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_292_; lean_object* v___x_294_; 
v___x_292_ = lean_unsigned_to_nat(3u);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 4, v_l_257_);
lean_ctor_set(v___x_290_, 2, v_v_25_);
lean_ctor_set(v___x_290_, 1, v_k_24_);
lean_ctor_set(v___x_290_, 0, v___x_173_);
v___x_294_ = v___x_290_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_173_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v_k_24_);
lean_ctor_set(v_reuseFailAlloc_298_, 2, v_v_25_);
lean_ctor_set(v_reuseFailAlloc_298_, 3, v_l_257_);
lean_ctor_set(v_reuseFailAlloc_298_, 4, v_l_257_);
v___x_294_ = v_reuseFailAlloc_298_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
lean_object* v___x_296_; 
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 4, v_r_286_);
lean_ctor_set(v___x_29_, 3, v___x_294_);
lean_ctor_set(v___x_29_, 2, v_v_288_);
lean_ctor_set(v___x_29_, 1, v_k_287_);
lean_ctor_set(v___x_29_, 0, v___x_292_);
v___x_296_ = v___x_29_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_292_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_k_287_);
lean_ctor_set(v_reuseFailAlloc_297_, 2, v_v_288_);
lean_ctor_set(v_reuseFailAlloc_297_, 3, v___x_294_);
lean_ctor_set(v_reuseFailAlloc_297_, 4, v_r_286_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
else
{
lean_object* v___x_303_; lean_object* v___x_305_; 
v___x_303_ = lean_unsigned_to_nat(2u);
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 4, v_impl_172_);
lean_ctor_set(v___x_29_, 3, v_r_286_);
lean_ctor_set(v___x_29_, 0, v___x_303_);
v___x_305_ = v___x_29_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_303_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v_k_24_);
lean_ctor_set(v_reuseFailAlloc_306_, 2, v_v_25_);
lean_ctor_set(v_reuseFailAlloc_306_, 3, v_r_286_);
lean_ctor_set(v_reuseFailAlloc_306_, 4, v_impl_172_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
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
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_unsigned_to_nat(1u);
v___x_309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v_k_20_);
lean_ctor_set(v___x_309_, 2, v_v_21_);
lean_ctor_set(v___x_309_, 3, v_t_22_);
lean_ctor_set(v___x_309_, 4, v_t_22_);
return v___x_309_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspaceRoot(lean_object* v_config_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_lakeEnv_314_; lean_object* v_lakeArgs_x3f_315_; lean_object* v_wsDir_316_; lean_object* v_pkgName_317_; lean_object* v_relPkgDir_318_; lean_object* v_pkgDir_319_; lean_object* v_relConfigFile_320_; lean_object* v_configFile_321_; lean_object* v_configLang_x3f_322_; lean_object* v_relManifestFile_323_; lean_object* v_packageOverrides_324_; lean_object* v_lakeOpts_325_; lean_object* v_leanOpts_326_; uint8_t v_reconfigure_327_; uint8_t v_updateDeps_328_; uint8_t v_updateToolchain_329_; lean_object* v_scope_330_; lean_object* v_remoteUrl_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_406_; 
v_lakeEnv_314_ = lean_ctor_get(v_config_311_, 0);
v_lakeArgs_x3f_315_ = lean_ctor_get(v_config_311_, 1);
v_wsDir_316_ = lean_ctor_get(v_config_311_, 2);
v_pkgName_317_ = lean_ctor_get(v_config_311_, 4);
v_relPkgDir_318_ = lean_ctor_get(v_config_311_, 5);
v_pkgDir_319_ = lean_ctor_get(v_config_311_, 6);
v_relConfigFile_320_ = lean_ctor_get(v_config_311_, 7);
v_configFile_321_ = lean_ctor_get(v_config_311_, 8);
v_configLang_x3f_322_ = lean_ctor_get(v_config_311_, 9);
v_relManifestFile_323_ = lean_ctor_get(v_config_311_, 10);
v_packageOverrides_324_ = lean_ctor_get(v_config_311_, 11);
v_lakeOpts_325_ = lean_ctor_get(v_config_311_, 12);
v_leanOpts_326_ = lean_ctor_get(v_config_311_, 13);
v_reconfigure_327_ = lean_ctor_get_uint8(v_config_311_, sizeof(void*)*16);
v_updateDeps_328_ = lean_ctor_get_uint8(v_config_311_, sizeof(void*)*16 + 1);
v_updateToolchain_329_ = lean_ctor_get_uint8(v_config_311_, sizeof(void*)*16 + 2);
v_scope_330_ = lean_ctor_get(v_config_311_, 14);
v_remoteUrl_331_ = lean_ctor_get(v_config_311_, 15);
v_isSharedCheck_406_ = !lean_is_exclusive(v_config_311_);
if (v_isSharedCheck_406_ == 0)
{
lean_object* v_unused_407_; 
v_unused_407_ = lean_ctor_get(v_config_311_, 3);
lean_dec(v_unused_407_);
v___x_333_ = v_config_311_;
v_isShared_334_ = v_isSharedCheck_406_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_remoteUrl_331_);
lean_inc(v_scope_330_);
lean_inc(v_leanOpts_326_);
lean_inc(v_lakeOpts_325_);
lean_inc(v_packageOverrides_324_);
lean_inc(v_relManifestFile_323_);
lean_inc(v_configLang_x3f_322_);
lean_inc(v_configFile_321_);
lean_inc(v_relConfigFile_320_);
lean_inc(v_pkgDir_319_);
lean_inc(v_relPkgDir_318_);
lean_inc(v_pkgName_317_);
lean_inc(v_wsDir_316_);
lean_inc(v_lakeArgs_x3f_315_);
lean_inc(v_lakeEnv_314_);
lean_dec(v_config_311_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_406_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_335_ = l_Lean_searchPathRef;
v___x_336_ = l_Lake_Env_leanSearchPath(v_lakeEnv_314_);
v___x_337_ = lean_st_ref_swap(v___x_335_, v___x_336_);
lean_dec(v___x_337_);
lean_inc_ref(v_lakeEnv_314_);
v___x_338_ = l_Lake_loadLakeConfig(v_lakeEnv_314_, v_a_312_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; lean_object* v_a_340_; lean_object* v___x_341_; lean_object* v___x_343_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_a_339_);
v_a_340_ = lean_ctor_get(v___x_338_, 1);
lean_inc(v_a_340_);
lean_dec_ref_known(v___x_338_, 2);
v___x_341_ = lean_unsigned_to_nat(0u);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 3, v___x_341_);
v___x_343_ = v___x_333_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_lakeEnv_314_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_lakeArgs_x3f_315_);
lean_ctor_set(v_reuseFailAlloc_396_, 2, v_wsDir_316_);
lean_ctor_set(v_reuseFailAlloc_396_, 3, v___x_341_);
lean_ctor_set(v_reuseFailAlloc_396_, 4, v_pkgName_317_);
lean_ctor_set(v_reuseFailAlloc_396_, 5, v_relPkgDir_318_);
lean_ctor_set(v_reuseFailAlloc_396_, 6, v_pkgDir_319_);
lean_ctor_set(v_reuseFailAlloc_396_, 7, v_relConfigFile_320_);
lean_ctor_set(v_reuseFailAlloc_396_, 8, v_configFile_321_);
lean_ctor_set(v_reuseFailAlloc_396_, 9, v_configLang_x3f_322_);
lean_ctor_set(v_reuseFailAlloc_396_, 10, v_relManifestFile_323_);
lean_ctor_set(v_reuseFailAlloc_396_, 11, v_packageOverrides_324_);
lean_ctor_set(v_reuseFailAlloc_396_, 12, v_lakeOpts_325_);
lean_ctor_set(v_reuseFailAlloc_396_, 13, v_leanOpts_326_);
lean_ctor_set(v_reuseFailAlloc_396_, 14, v_scope_330_);
lean_ctor_set(v_reuseFailAlloc_396_, 15, v_remoteUrl_331_);
lean_ctor_set_uint8(v_reuseFailAlloc_396_, sizeof(void*)*16, v_reconfigure_327_);
lean_ctor_set_uint8(v_reuseFailAlloc_396_, sizeof(void*)*16 + 1, v_updateDeps_328_);
lean_ctor_set_uint8(v_reuseFailAlloc_396_, sizeof(void*)*16 + 2, v_updateToolchain_329_);
v___x_343_ = v_reuseFailAlloc_396_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = ((lean_object*)(l_Lake_loadWorkspaceRoot___closed__0));
v___x_345_ = l_Lake_resolveConfigFile(v___x_344_, v___x_343_, v_a_340_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; lean_object* v_a_347_; lean_object* v___x_348_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc_n(v_a_346_, 2);
v_a_347_ = lean_ctor_get(v___x_345_, 1);
lean_inc(v_a_347_);
lean_dec_ref_known(v___x_345_, 2);
v___x_348_ = l_Lake_loadConfigFile___redArg(v_a_346_, v_a_347_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_377_; 
v_a_349_ = lean_ctor_get(v___x_348_, 0);
v_a_350_ = lean_ctor_get(v___x_348_, 1);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_377_ == 0)
{
v___x_352_ = v___x_348_;
v_isShared_353_ = v_isSharedCheck_377_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_inc(v_a_349_);
lean_dec(v___x_348_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_377_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v_facetDecls_354_; lean_object* v___x_355_; lean_object* v___y_357_; lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v_facetDecls_354_ = lean_ctor_get(v_a_349_, 2);
lean_inc_ref(v_facetDecls_354_);
v___x_355_ = l_Lake_mkPackage(v_a_346_, v_a_349_, v___x_341_);
v___x_371_ = l_Lake_initFacetConfigs;
v___x_372_ = lean_array_get_size(v_facetDecls_354_);
v___x_373_ = lean_nat_dec_lt(v___x_341_, v___x_372_);
if (v___x_373_ == 0)
{
lean_dec_ref(v_facetDecls_354_);
v___y_357_ = v___x_371_;
goto v___jp_356_;
}
else
{
size_t v___x_374_; size_t v___x_375_; lean_object* v___x_376_; 
v___x_374_ = ((size_t)0ULL);
v___x_375_ = lean_usize_of_nat(v___x_372_);
v___x_376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspaceRoot_spec__1(v_facetDecls_354_, v___x_374_, v___x_375_, v___x_371_);
lean_dec_ref(v_facetDecls_354_);
v___y_357_ = v___x_376_;
goto v___jp_356_;
}
v___jp_356_:
{
lean_object* v_lakeEnv_358_; lean_object* v_lakeArgs_x3f_359_; lean_object* v_keyName_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_369_; 
v_lakeEnv_358_ = lean_ctor_get(v_a_346_, 0);
lean_inc_ref(v_lakeEnv_358_);
v_lakeArgs_x3f_359_ = lean_ctor_get(v_a_346_, 1);
lean_inc(v_lakeArgs_x3f_359_);
lean_dec(v_a_346_);
v_keyName_360_ = lean_ctor_get(v___x_355_, 2);
lean_inc(v_keyName_360_);
lean_inc_ref_n(v___x_355_, 2);
v___x_361_ = l_Lake_computeLakeCache(v___x_355_, v_lakeEnv_358_);
v___x_362_ = lean_unsigned_to_nat(1u);
v___x_363_ = lean_mk_empty_array_with_capacity(v___x_362_);
v___x_364_ = lean_array_push(v___x_363_, v___x_355_);
v___x_365_ = lean_box(1);
v___x_366_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadWorkspaceRoot_spec__0___redArg(v_keyName_360_, v___x_355_, v___x_365_);
v___x_367_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_367_, 0, v_lakeEnv_358_);
lean_ctor_set(v___x_367_, 1, v_a_339_);
lean_ctor_set(v___x_367_, 2, v___x_361_);
lean_ctor_set(v___x_367_, 3, v_lakeArgs_x3f_359_);
lean_ctor_set(v___x_367_, 4, v___x_364_);
lean_ctor_set(v___x_367_, 5, v___x_366_);
lean_ctor_set(v___x_367_, 6, v___y_357_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 0, v___x_367_);
v___x_369_ = v___x_352_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_a_350_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
else
{
lean_object* v_a_378_; lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_386_; 
lean_dec(v_a_346_);
lean_dec(v_a_339_);
v_a_378_ = lean_ctor_get(v___x_348_, 0);
v_a_379_ = lean_ctor_get(v___x_348_, 1);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_386_ == 0)
{
v___x_381_ = v___x_348_;
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_inc(v_a_378_);
lean_dec(v___x_348_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
if (v_isShared_382_ == 0)
{
v___x_384_ = v___x_381_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_378_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v_a_379_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
else
{
lean_object* v_a_387_; lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
lean_dec(v_a_339_);
v_a_387_ = lean_ctor_get(v___x_345_, 0);
v_a_388_ = lean_ctor_get(v___x_345_, 1);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___x_345_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_inc(v_a_387_);
lean_dec(v___x_345_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_387_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_a_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
}
else
{
lean_object* v_a_397_; lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
lean_del_object(v___x_333_);
lean_dec_ref(v_remoteUrl_331_);
lean_dec_ref(v_scope_330_);
lean_dec_ref(v_leanOpts_326_);
lean_dec(v_lakeOpts_325_);
lean_dec_ref(v_packageOverrides_324_);
lean_dec_ref(v_relManifestFile_323_);
lean_dec(v_configLang_x3f_322_);
lean_dec_ref(v_configFile_321_);
lean_dec_ref(v_relConfigFile_320_);
lean_dec_ref(v_pkgDir_319_);
lean_dec_ref(v_relPkgDir_318_);
lean_dec(v_pkgName_317_);
lean_dec_ref(v_wsDir_316_);
lean_dec(v_lakeArgs_x3f_315_);
lean_dec_ref(v_lakeEnv_314_);
v_a_397_ = lean_ctor_get(v___x_338_, 0);
v_a_398_ = lean_ctor_get(v___x_338_, 1);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v___x_338_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_inc(v_a_397_);
lean_dec(v___x_338_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_397_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_a_398_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspaceRoot___boxed(lean_object* v_config_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lake_loadWorkspaceRoot(v_config_408_, v_a_409_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadWorkspaceRoot_spec__0(lean_object* v_00_u03b2_412_, lean_object* v_k_413_, lean_object* v_v_414_, lean_object* v_t_415_, lean_object* v_hl_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadWorkspaceRoot_spec__0___redArg(v_k_413_, v_v_414_, v_t_415_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(lean_object* v_as_418_, size_t v_i_419_, size_t v_stop_420_, lean_object* v_b_421_, lean_object* v___y_422_){
_start:
{
uint8_t v___x_424_; 
v___x_424_ = lean_usize_dec_eq(v_i_419_, v_stop_420_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; size_t v___x_427_; size_t v___x_428_; 
v___x_425_ = lean_array_uget_borrowed(v_as_418_, v_i_419_);
lean_inc_ref(v___y_422_);
lean_inc(v___x_425_);
v___x_426_ = lean_apply_2(v___y_422_, v___x_425_, lean_box(0));
v___x_427_ = ((size_t)1ULL);
v___x_428_ = lean_usize_add(v_i_419_, v___x_427_);
v_i_419_ = v___x_428_;
v_b_421_ = v___x_426_;
goto _start;
}
else
{
lean_object* v___x_430_; 
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v_b_421_);
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0___boxed(lean_object* v_as_431_, lean_object* v_i_432_, lean_object* v_stop_433_, lean_object* v_b_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
size_t v_i_boxed_437_; size_t v_stop_boxed_438_; lean_object* v_res_439_; 
v_i_boxed_437_ = lean_unbox_usize(v_i_432_);
lean_dec(v_i_432_);
v_stop_boxed_438_ = lean_unbox_usize(v_stop_433_);
lean_dec(v_stop_433_);
v_res_439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_as_431_, v_i_boxed_437_, v_stop_boxed_438_, v_b_434_, v___y_435_);
lean_dec_ref(v___y_435_);
lean_dec_ref(v_as_431_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace(lean_object* v_config_442_, lean_object* v_a_443_){
_start:
{
lean_object* v_packageOverrides_445_; lean_object* v_leanOpts_446_; uint8_t v_reconfigure_447_; uint8_t v_updateDeps_448_; uint8_t v_updateToolchain_449_; lean_object* v_a_451_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v_packageOverrides_445_ = lean_ctor_get(v_config_442_, 11);
lean_inc_ref(v_packageOverrides_445_);
v_leanOpts_446_ = lean_ctor_get(v_config_442_, 13);
lean_inc_ref(v_leanOpts_446_);
v_reconfigure_447_ = lean_ctor_get_uint8(v_config_442_, sizeof(void*)*16);
v_updateDeps_448_ = lean_ctor_get_uint8(v_config_442_, sizeof(void*)*16 + 1);
v_updateToolchain_449_ = lean_ctor_get_uint8(v_config_442_, sizeof(void*)*16 + 2);
v___x_479_ = lean_unsigned_to_nat(0u);
v___x_480_ = ((lean_object*)(l_Lake_loadWorkspace___closed__0));
v___x_481_ = l_Lake_loadWorkspaceRoot(v_config_442_, v___x_480_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v_a_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_a_482_);
v_a_483_ = lean_ctor_get(v___x_481_, 1);
lean_inc(v_a_483_);
lean_dec_ref_known(v___x_481_, 2);
v___x_484_ = lean_array_get_size(v_a_483_);
v___x_485_ = lean_nat_dec_lt(v___x_479_, v___x_484_);
if (v___x_485_ == 0)
{
lean_dec(v_a_483_);
v_a_451_ = v_a_482_;
goto v___jp_450_;
}
else
{
lean_object* v___x_486_; size_t v___x_487_; size_t v___x_488_; lean_object* v___x_489_; 
v___x_486_ = lean_box(0);
v___x_487_ = ((size_t)0ULL);
v___x_488_ = lean_usize_of_nat(v___x_484_);
v___x_489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_a_483_, v___x_487_, v___x_488_, v___x_486_, v_a_443_);
lean_dec(v_a_483_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_dec_ref_known(v___x_489_, 1);
v_a_451_ = v_a_482_;
goto v___jp_450_;
}
else
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_dec(v_a_482_);
lean_dec_ref(v_leanOpts_446_);
lean_dec_ref(v_packageOverrides_445_);
v_a_490_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_489_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_489_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
}
else
{
lean_object* v_a_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
lean_dec_ref(v_leanOpts_446_);
lean_dec_ref(v_packageOverrides_445_);
v_a_498_ = lean_ctor_get(v___x_481_, 1);
lean_inc(v_a_498_);
lean_dec_ref_known(v___x_481_, 2);
v___x_499_ = lean_array_get_size(v_a_498_);
v___x_500_ = lean_nat_dec_lt(v___x_479_, v___x_499_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; lean_object* v___x_502_; 
lean_dec(v_a_498_);
v___x_501_ = lean_box(0);
v___x_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
return v___x_502_;
}
else
{
lean_object* v___x_503_; size_t v___x_504_; size_t v___x_505_; lean_object* v___x_506_; 
v___x_503_ = lean_box(0);
v___x_504_ = ((size_t)0ULL);
v___x_505_ = lean_usize_of_nat(v___x_499_);
v___x_506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_a_498_, v___x_504_, v___x_505_, v___x_503_, v_a_443_);
lean_dec(v_a_498_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_513_ == 0)
{
lean_object* v_unused_514_; 
v_unused_514_ = lean_ctor_get(v___x_506_, 0);
lean_dec(v_unused_514_);
v___x_508_ = v___x_506_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_dec(v___x_506_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
lean_ctor_set_tag(v___x_508_, 1);
lean_ctor_set(v___x_508_, 0, v___x_503_);
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_503_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
else
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
v_a_515_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_506_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_506_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_515_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
}
v___jp_450_:
{
if (v_updateDeps_448_ == 0)
{
lean_object* v_packages_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v_dir_455_; lean_object* v_relManifestFile_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v_packages_452_ = lean_ctor_get(v_a_451_, 4);
v___x_453_ = lean_unsigned_to_nat(0u);
v___x_454_ = lean_array_fget_borrowed(v_packages_452_, v___x_453_);
v_dir_455_ = lean_ctor_get(v___x_454_, 4);
v_relManifestFile_456_ = lean_ctor_get(v___x_454_, 9);
lean_inc_ref(v_relManifestFile_456_);
lean_inc_ref(v_dir_455_);
v___x_457_ = l_Lake_joinRelative(v_dir_455_, v_relManifestFile_456_);
v___x_458_ = l_Lake_Manifest_load_x3f(v___x_457_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_a_459_);
lean_dec_ref_known(v___x_458_, 1);
if (lean_obj_tag(v_a_459_) == 1)
{
lean_object* v_val_460_; lean_object* v___x_461_; 
v_val_460_ = lean_ctor_get(v_a_459_, 0);
lean_inc(v_val_460_);
lean_dec_ref_known(v_a_459_, 1);
v___x_461_ = l_Lake_Workspace_materializeDeps(v_a_451_, v_val_460_, v_leanOpts_446_, v_reconfigure_447_, v_packageOverrides_445_, v_a_443_);
lean_dec_ref(v_packageOverrides_445_);
return v___x_461_;
}
else
{
lean_object* v___x_462_; lean_object* v___x_463_; 
lean_dec(v_a_459_);
lean_dec_ref(v_packageOverrides_445_);
v___x_462_ = l_Lean_NameSet_empty;
v___x_463_ = l_Lake_Workspace_updateAndMaterialize(v_a_451_, v___x_462_, v_leanOpts_446_, v_updateToolchain_449_, v_a_443_);
return v___x_463_;
}
}
else
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_476_; 
lean_dec_ref(v_a_451_);
lean_dec_ref(v_leanOpts_446_);
lean_dec_ref(v_packageOverrides_445_);
v_a_464_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_476_ == 0)
{
v___x_466_ = v___x_458_;
v_isShared_467_ = v_isSharedCheck_476_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_458_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_476_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_468_; uint8_t v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_468_ = lean_io_error_to_string(v_a_464_);
v___x_469_ = 3;
v___x_470_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_470_, 0, v___x_468_);
lean_ctor_set_uint8(v___x_470_, sizeof(void*)*1, v___x_469_);
lean_inc_ref(v_a_443_);
v___x_471_ = lean_apply_2(v_a_443_, v___x_470_, lean_box(0));
v___x_472_ = lean_box(0);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v___x_472_);
v___x_474_ = v___x_466_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_472_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec_ref(v_packageOverrides_445_);
v___x_477_ = l_Lean_NameSet_empty;
v___x_478_ = l_Lake_Workspace_updateAndMaterialize(v_a_451_, v___x_477_, v_leanOpts_446_, v_updateToolchain_449_, v_a_443_);
return v___x_478_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___boxed(lean_object* v_config_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lake_loadWorkspace(v_config_523_, v_a_524_);
lean_dec_ref(v_a_524_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lake_updateManifest(lean_object* v_config_527_, lean_object* v_toUpdate_528_, lean_object* v_a_529_){
_start:
{
lean_object* v_leanOpts_531_; uint8_t v_updateToolchain_532_; lean_object* v_a_534_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v_leanOpts_531_ = lean_ctor_get(v_config_527_, 13);
lean_inc_ref(v_leanOpts_531_);
v_updateToolchain_532_ = lean_ctor_get_uint8(v_config_527_, sizeof(void*)*16 + 2);
v___x_553_ = lean_unsigned_to_nat(0u);
v___x_554_ = ((lean_object*)(l_Lake_loadWorkspace___closed__0));
v___x_555_ = l_Lake_loadWorkspaceRoot(v_config_527_, v___x_554_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v_a_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_a_556_);
v_a_557_ = lean_ctor_get(v___x_555_, 1);
lean_inc(v_a_557_);
lean_dec_ref_known(v___x_555_, 2);
v___x_558_ = lean_array_get_size(v_a_557_);
v___x_559_ = lean_nat_dec_lt(v___x_553_, v___x_558_);
if (v___x_559_ == 0)
{
lean_dec(v_a_557_);
v_a_534_ = v_a_556_;
goto v___jp_533_;
}
else
{
lean_object* v___x_560_; size_t v___x_561_; size_t v___x_562_; lean_object* v___x_563_; 
v___x_560_ = lean_box(0);
v___x_561_ = ((size_t)0ULL);
v___x_562_ = lean_usize_of_nat(v___x_558_);
v___x_563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_a_557_, v___x_561_, v___x_562_, v___x_560_, v_a_529_);
lean_dec(v_a_557_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_dec_ref_known(v___x_563_, 1);
v_a_534_ = v_a_556_;
goto v___jp_533_;
}
else
{
lean_dec(v_a_556_);
lean_dec_ref(v_leanOpts_531_);
lean_dec(v_toUpdate_528_);
return v___x_563_;
}
}
}
else
{
lean_object* v_a_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
lean_dec_ref(v_leanOpts_531_);
lean_dec(v_toUpdate_528_);
v_a_564_ = lean_ctor_get(v___x_555_, 1);
lean_inc(v_a_564_);
lean_dec_ref_known(v___x_555_, 2);
v___x_565_ = lean_array_get_size(v_a_564_);
v___x_566_ = lean_nat_dec_lt(v___x_553_, v___x_565_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec(v_a_564_);
v___x_567_ = lean_box(0);
v___x_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
else
{
lean_object* v___x_569_; size_t v___x_570_; size_t v___x_571_; lean_object* v___x_572_; 
v___x_569_ = lean_box(0);
v___x_570_ = ((size_t)0ULL);
v___x_571_ = lean_usize_of_nat(v___x_565_);
v___x_572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_a_564_, v___x_570_, v___x_571_, v___x_569_, v_a_529_);
lean_dec(v_a_564_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_579_ == 0)
{
lean_object* v_unused_580_; 
v_unused_580_ = lean_ctor_get(v___x_572_, 0);
lean_dec(v_unused_580_);
v___x_574_ = v___x_572_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_dec(v___x_572_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
lean_ctor_set_tag(v___x_574_, 1);
lean_ctor_set(v___x_574_, 0, v___x_569_);
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_569_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
else
{
return v___x_572_;
}
}
}
v___jp_533_:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_box(0);
v___x_536_ = l_Lake_Workspace_updateAndMaterialize(v_a_534_, v_toUpdate_528_, v_leanOpts_531_, v_updateToolchain_532_, v_a_529_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_543_ == 0)
{
lean_object* v_unused_544_; 
v_unused_544_ = lean_ctor_get(v___x_536_, 0);
lean_dec(v_unused_544_);
v___x_538_ = v___x_536_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_dec(v___x_536_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 0, v___x_535_);
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_535_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
v_a_545_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_536_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_536_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateManifest___boxed(lean_object* v_config_581_, lean_object* v_toUpdate_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lake_updateManifest(v_config_581_, v_toUpdate_582_, v_a_583_);
lean_dec_ref(v_a_583_);
return v_res_585_;
}
}
lean_object* runtime_initialize_Lake_Load_Config(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Workspace(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Resolve(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Package(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Lean_Eval(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Toml(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_InitFacets(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Load_Workspace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Load_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Resolve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Lean_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Toml(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_InitFacets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Load_Workspace(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Load_Config(uint8_t builtin);
lean_object* initialize_Lake_Config_Workspace(uint8_t builtin);
lean_object* initialize_Lake_Load_Resolve(uint8_t builtin);
lean_object* initialize_Lake_Load_Package(uint8_t builtin);
lean_object* initialize_Lake_Load_Lean_Eval(uint8_t builtin);
lean_object* initialize_Lake_Load_Toml(uint8_t builtin);
lean_object* initialize_Lake_Build_InitFacets(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Workspace(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Load_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Resolve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Lean_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Toml(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_InitFacets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Load_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Load_Workspace(builtin);
}
#ifdef __cplusplus
}
#endif
