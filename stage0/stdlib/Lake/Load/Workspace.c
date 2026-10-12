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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspaceRoot_spec__1(lean_object* v_as_1_, size_t v_i_2_, size_t v_stop_3_, lean_object* v_b_4_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspaceRoot_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1_ = stack[0].m_obj;
size_t v_i_2_ = stack[1].m_num;
size_t v_stop_3_ = stack[2].m_num;
lean_object* v_b_4_ = stack[3].m_obj;
lean_object* v_res_13_;
v_res_13_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspaceRoot_spec__1(v_as_1_, v_i_2_, v_stop_3_, v_b_4_);
stack->m_obj
 = v_res_13_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspaceRoot_spec__1___boxed(lean_object* v_as_14_, lean_object* v_i_15_, lean_object* v_stop_16_, lean_object* v_b_17_){
_start:
{
size_t v_i_boxed_18_; size_t v_stop_boxed_19_; lean_object* v_res_20_; 
v_i_boxed_18_ = lean_unbox_usize(v_i_15_);
lean_dec(v_i_15_);
v_stop_boxed_19_ = lean_unbox_usize(v_stop_16_);
lean_dec(v_stop_16_);
v_res_20_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspaceRoot_spec__1(v_as_14_, v_i_boxed_18_, v_stop_boxed_19_, v_b_17_);
lean_dec_ref(v_as_14_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadWorkspaceRoot_spec__0___redArg(lean_object* v_k_21_, lean_object* v_v_22_, lean_object* v_t_23_){
_start:
{
if (lean_obj_tag(v_t_23_) == 0)
{
lean_object* v_size_24_; lean_object* v_k_25_; lean_object* v_v_26_; lean_object* v_l_27_; lean_object* v_r_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_308_; 
v_size_24_ = lean_ctor_get(v_t_23_, 0);
v_k_25_ = lean_ctor_get(v_t_23_, 1);
v_v_26_ = lean_ctor_get(v_t_23_, 2);
v_l_27_ = lean_ctor_get(v_t_23_, 3);
v_r_28_ = lean_ctor_get(v_t_23_, 4);
v_isSharedCheck_308_ = !lean_is_exclusive(v_t_23_);
if (v_isSharedCheck_308_ == 0)
{
v___x_30_ = v_t_23_;
v_isShared_31_ = v_isSharedCheck_308_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_r_28_);
lean_inc(v_l_27_);
lean_inc(v_v_26_);
lean_inc(v_k_25_);
lean_inc(v_size_24_);
lean_dec(v_t_23_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_308_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
uint8_t v___x_32_; 
v___x_32_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_21_, v_k_25_);
switch(v___x_32_)
{
case 0:
{
lean_object* v_impl_33_; lean_object* v___x_34_; 
lean_dec(v_size_24_);
v_impl_33_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadWorkspaceRoot_spec__0___redArg(v_k_21_, v_v_22_, v_l_27_);
v___x_34_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_28_) == 0)
{
lean_object* v_size_35_; lean_object* v_size_36_; lean_object* v_k_37_; lean_object* v_v_38_; lean_object* v_l_39_; lean_object* v_r_40_; lean_object* v___x_41_; lean_object* v___x_42_; uint8_t v___x_43_; 
v_size_35_ = lean_ctor_get(v_r_28_, 0);
v_size_36_ = lean_ctor_get(v_impl_33_, 0);
v_k_37_ = lean_ctor_get(v_impl_33_, 1);
v_v_38_ = lean_ctor_get(v_impl_33_, 2);
v_l_39_ = lean_ctor_get(v_impl_33_, 3);
v_r_40_ = lean_ctor_get(v_impl_33_, 4);
lean_inc(v_r_40_);
v___x_41_ = lean_unsigned_to_nat(3u);
v___x_42_ = lean_nat_mul(v___x_41_, v_size_35_);
v___x_43_ = lean_nat_dec_lt(v___x_42_, v_size_36_);
lean_dec(v___x_42_);
if (v___x_43_ == 0)
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_47_; 
lean_dec(v_r_40_);
v___x_44_ = lean_nat_add(v___x_34_, v_size_36_);
v___x_45_ = lean_nat_add(v___x_44_, v_size_35_);
lean_dec(v___x_44_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 3, v_impl_33_);
lean_ctor_set(v___x_30_, 0, v___x_45_);
v___x_47_ = v___x_30_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v___x_45_);
lean_ctor_set(v_reuseFailAlloc_48_, 1, v_k_25_);
lean_ctor_set(v_reuseFailAlloc_48_, 2, v_v_26_);
lean_ctor_set(v_reuseFailAlloc_48_, 3, v_impl_33_);
lean_ctor_set(v_reuseFailAlloc_48_, 4, v_r_28_);
v___x_47_ = v_reuseFailAlloc_48_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
return v___x_47_;
}
}
else
{
lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_114_; 
lean_inc(v_l_39_);
lean_inc(v_v_38_);
lean_inc(v_k_37_);
lean_inc(v_size_36_);
v_isSharedCheck_114_ = !lean_is_exclusive(v_impl_33_);
if (v_isSharedCheck_114_ == 0)
{
lean_object* v_unused_115_; lean_object* v_unused_116_; lean_object* v_unused_117_; lean_object* v_unused_118_; lean_object* v_unused_119_; 
v_unused_115_ = lean_ctor_get(v_impl_33_, 4);
lean_dec(v_unused_115_);
v_unused_116_ = lean_ctor_get(v_impl_33_, 3);
lean_dec(v_unused_116_);
v_unused_117_ = lean_ctor_get(v_impl_33_, 2);
lean_dec(v_unused_117_);
v_unused_118_ = lean_ctor_get(v_impl_33_, 1);
lean_dec(v_unused_118_);
v_unused_119_ = lean_ctor_get(v_impl_33_, 0);
lean_dec(v_unused_119_);
v___x_50_ = v_impl_33_;
v_isShared_51_ = v_isSharedCheck_114_;
goto v_resetjp_49_;
}
else
{
lean_dec(v_impl_33_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_114_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v_size_52_; lean_object* v_size_53_; lean_object* v_k_54_; lean_object* v_v_55_; lean_object* v_l_56_; lean_object* v_r_57_; lean_object* v___x_58_; lean_object* v___x_59_; uint8_t v___x_60_; 
v_size_52_ = lean_ctor_get(v_l_39_, 0);
v_size_53_ = lean_ctor_get(v_r_40_, 0);
v_k_54_ = lean_ctor_get(v_r_40_, 1);
v_v_55_ = lean_ctor_get(v_r_40_, 2);
v_l_56_ = lean_ctor_get(v_r_40_, 3);
v_r_57_ = lean_ctor_get(v_r_40_, 4);
v___x_58_ = lean_unsigned_to_nat(2u);
v___x_59_ = lean_nat_mul(v___x_58_, v_size_52_);
v___x_60_ = lean_nat_dec_lt(v_size_53_, v___x_59_);
lean_dec(v___x_59_);
if (v___x_60_ == 0)
{
lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_89_; 
lean_inc(v_r_57_);
lean_inc(v_l_56_);
lean_inc(v_v_55_);
lean_inc(v_k_54_);
v_isSharedCheck_89_ = !lean_is_exclusive(v_r_40_);
if (v_isSharedCheck_89_ == 0)
{
lean_object* v_unused_90_; lean_object* v_unused_91_; lean_object* v_unused_92_; lean_object* v_unused_93_; lean_object* v_unused_94_; 
v_unused_90_ = lean_ctor_get(v_r_40_, 4);
lean_dec(v_unused_90_);
v_unused_91_ = lean_ctor_get(v_r_40_, 3);
lean_dec(v_unused_91_);
v_unused_92_ = lean_ctor_get(v_r_40_, 2);
lean_dec(v_unused_92_);
v_unused_93_ = lean_ctor_get(v_r_40_, 1);
lean_dec(v_unused_93_);
v_unused_94_ = lean_ctor_get(v_r_40_, 0);
lean_dec(v_unused_94_);
v___x_62_ = v_r_40_;
v_isShared_63_ = v_isSharedCheck_89_;
goto v_resetjp_61_;
}
else
{
lean_dec(v_r_40_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_89_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___y_67_; lean_object* v___y_68_; lean_object* v___y_69_; lean_object* v___x_77_; lean_object* v___y_79_; 
v___x_64_ = lean_nat_add(v___x_34_, v_size_36_);
lean_dec(v_size_36_);
v___x_65_ = lean_nat_add(v___x_64_, v_size_35_);
lean_dec(v___x_64_);
v___x_77_ = lean_nat_add(v___x_34_, v_size_52_);
if (lean_obj_tag(v_l_56_) == 0)
{
lean_object* v_size_87_; 
v_size_87_ = lean_ctor_get(v_l_56_, 0);
lean_inc(v_size_87_);
v___y_79_ = v_size_87_;
goto v___jp_78_;
}
else
{
lean_object* v___x_88_; 
v___x_88_ = lean_unsigned_to_nat(0u);
v___y_79_ = v___x_88_;
goto v___jp_78_;
}
v___jp_66_:
{
lean_object* v___x_70_; lean_object* v___x_72_; 
v___x_70_ = lean_nat_add(v___y_67_, v___y_69_);
lean_dec(v___y_69_);
lean_dec(v___y_67_);
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 4, v_r_28_);
lean_ctor_set(v___x_62_, 3, v_r_57_);
lean_ctor_set(v___x_62_, 2, v_v_26_);
lean_ctor_set(v___x_62_, 1, v_k_25_);
lean_ctor_set(v___x_62_, 0, v___x_70_);
v___x_72_ = v___x_62_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v___x_70_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v_k_25_);
lean_ctor_set(v_reuseFailAlloc_76_, 2, v_v_26_);
lean_ctor_set(v_reuseFailAlloc_76_, 3, v_r_57_);
lean_ctor_set(v_reuseFailAlloc_76_, 4, v_r_28_);
v___x_72_ = v_reuseFailAlloc_76_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
lean_object* v___x_74_; 
if (v_isShared_51_ == 0)
{
lean_ctor_set(v___x_50_, 4, v___x_72_);
lean_ctor_set(v___x_50_, 3, v___y_68_);
lean_ctor_set(v___x_50_, 2, v_v_55_);
lean_ctor_set(v___x_50_, 1, v_k_54_);
lean_ctor_set(v___x_50_, 0, v___x_65_);
v___x_74_ = v___x_50_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v___x_65_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v_k_54_);
lean_ctor_set(v_reuseFailAlloc_75_, 2, v_v_55_);
lean_ctor_set(v_reuseFailAlloc_75_, 3, v___y_68_);
lean_ctor_set(v_reuseFailAlloc_75_, 4, v___x_72_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
v___jp_78_:
{
lean_object* v___x_80_; lean_object* v___x_82_; 
v___x_80_ = lean_nat_add(v___x_77_, v___y_79_);
lean_dec(v___y_79_);
lean_dec(v___x_77_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 4, v_l_56_);
lean_ctor_set(v___x_30_, 3, v_l_39_);
lean_ctor_set(v___x_30_, 2, v_v_38_);
lean_ctor_set(v___x_30_, 1, v_k_37_);
lean_ctor_set(v___x_30_, 0, v___x_80_);
v___x_82_ = v___x_30_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v___x_80_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v_k_37_);
lean_ctor_set(v_reuseFailAlloc_86_, 2, v_v_38_);
lean_ctor_set(v_reuseFailAlloc_86_, 3, v_l_39_);
lean_ctor_set(v_reuseFailAlloc_86_, 4, v_l_56_);
v___x_82_ = v_reuseFailAlloc_86_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
lean_object* v___x_83_; 
v___x_83_ = lean_nat_add(v___x_34_, v_size_35_);
if (lean_obj_tag(v_r_57_) == 0)
{
lean_object* v_size_84_; 
v_size_84_ = lean_ctor_get(v_r_57_, 0);
lean_inc(v_size_84_);
v___y_67_ = v___x_83_;
v___y_68_ = v___x_82_;
v___y_69_ = v_size_84_;
goto v___jp_66_;
}
else
{
lean_object* v___x_85_; 
v___x_85_ = lean_unsigned_to_nat(0u);
v___y_67_ = v___x_83_;
v___y_68_ = v___x_82_;
v___y_69_ = v___x_85_;
goto v___jp_66_;
}
}
}
}
}
else
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_100_; 
lean_del_object(v___x_30_);
v___x_95_ = lean_nat_add(v___x_34_, v_size_36_);
lean_dec(v_size_36_);
v___x_96_ = lean_nat_add(v___x_95_, v_size_35_);
lean_dec(v___x_95_);
v___x_97_ = lean_nat_add(v___x_34_, v_size_35_);
v___x_98_ = lean_nat_add(v___x_97_, v_size_53_);
lean_dec(v___x_97_);
lean_inc_ref(v_r_28_);
if (v_isShared_51_ == 0)
{
lean_ctor_set(v___x_50_, 4, v_r_28_);
lean_ctor_set(v___x_50_, 3, v_r_40_);
lean_ctor_set(v___x_50_, 2, v_v_26_);
lean_ctor_set(v___x_50_, 1, v_k_25_);
lean_ctor_set(v___x_50_, 0, v___x_98_);
v___x_100_ = v___x_50_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_98_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_k_25_);
lean_ctor_set(v_reuseFailAlloc_113_, 2, v_v_26_);
lean_ctor_set(v_reuseFailAlloc_113_, 3, v_r_40_);
lean_ctor_set(v_reuseFailAlloc_113_, 4, v_r_28_);
v___x_100_ = v_reuseFailAlloc_113_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_107_; 
v_isSharedCheck_107_ = !lean_is_exclusive(v_r_28_);
if (v_isSharedCheck_107_ == 0)
{
lean_object* v_unused_108_; lean_object* v_unused_109_; lean_object* v_unused_110_; lean_object* v_unused_111_; lean_object* v_unused_112_; 
v_unused_108_ = lean_ctor_get(v_r_28_, 4);
lean_dec(v_unused_108_);
v_unused_109_ = lean_ctor_get(v_r_28_, 3);
lean_dec(v_unused_109_);
v_unused_110_ = lean_ctor_get(v_r_28_, 2);
lean_dec(v_unused_110_);
v_unused_111_ = lean_ctor_get(v_r_28_, 1);
lean_dec(v_unused_111_);
v_unused_112_ = lean_ctor_get(v_r_28_, 0);
lean_dec(v_unused_112_);
v___x_102_ = v_r_28_;
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
else
{
lean_dec(v_r_28_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_105_; 
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 4, v___x_100_);
lean_ctor_set(v___x_102_, 3, v_l_39_);
lean_ctor_set(v___x_102_, 2, v_v_38_);
lean_ctor_set(v___x_102_, 1, v_k_37_);
lean_ctor_set(v___x_102_, 0, v___x_96_);
v___x_105_ = v___x_102_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_96_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v_k_37_);
lean_ctor_set(v_reuseFailAlloc_106_, 2, v_v_38_);
lean_ctor_set(v_reuseFailAlloc_106_, 3, v_l_39_);
lean_ctor_set(v_reuseFailAlloc_106_, 4, v___x_100_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_120_; 
v_l_120_ = lean_ctor_get(v_impl_33_, 3);
if (lean_obj_tag(v_l_120_) == 0)
{
lean_object* v_r_121_; lean_object* v_k_122_; lean_object* v_v_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_134_; 
lean_inc_ref(v_l_120_);
v_r_121_ = lean_ctor_get(v_impl_33_, 4);
v_k_122_ = lean_ctor_get(v_impl_33_, 1);
v_v_123_ = lean_ctor_get(v_impl_33_, 2);
v_isSharedCheck_134_ = !lean_is_exclusive(v_impl_33_);
if (v_isSharedCheck_134_ == 0)
{
lean_object* v_unused_135_; lean_object* v_unused_136_; 
v_unused_135_ = lean_ctor_get(v_impl_33_, 3);
lean_dec(v_unused_135_);
v_unused_136_ = lean_ctor_get(v_impl_33_, 0);
lean_dec(v_unused_136_);
v___x_125_ = v_impl_33_;
v_isShared_126_ = v_isSharedCheck_134_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_r_121_);
lean_inc(v_v_123_);
lean_inc(v_k_122_);
lean_dec(v_impl_33_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_134_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_127_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_121_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 3, v_r_121_);
lean_ctor_set(v___x_125_, 2, v_v_26_);
lean_ctor_set(v___x_125_, 1, v_k_25_);
lean_ctor_set(v___x_125_, 0, v___x_34_);
v___x_129_ = v___x_125_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_34_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v_k_25_);
lean_ctor_set(v_reuseFailAlloc_133_, 2, v_v_26_);
lean_ctor_set(v_reuseFailAlloc_133_, 3, v_r_121_);
lean_ctor_set(v_reuseFailAlloc_133_, 4, v_r_121_);
v___x_129_ = v_reuseFailAlloc_133_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
lean_object* v___x_131_; 
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 4, v___x_129_);
lean_ctor_set(v___x_30_, 3, v_l_120_);
lean_ctor_set(v___x_30_, 2, v_v_123_);
lean_ctor_set(v___x_30_, 1, v_k_122_);
lean_ctor_set(v___x_30_, 0, v___x_127_);
v___x_131_ = v___x_30_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v_k_122_);
lean_ctor_set(v_reuseFailAlloc_132_, 2, v_v_123_);
lean_ctor_set(v_reuseFailAlloc_132_, 3, v_l_120_);
lean_ctor_set(v_reuseFailAlloc_132_, 4, v___x_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
}
else
{
lean_object* v_r_137_; 
v_r_137_ = lean_ctor_get(v_impl_33_, 4);
lean_inc(v_r_137_);
if (lean_obj_tag(v_r_137_) == 0)
{
lean_object* v_k_138_; lean_object* v_v_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_162_; 
lean_inc(v_l_120_);
v_k_138_ = lean_ctor_get(v_impl_33_, 1);
v_v_139_ = lean_ctor_get(v_impl_33_, 2);
v_isSharedCheck_162_ = !lean_is_exclusive(v_impl_33_);
if (v_isSharedCheck_162_ == 0)
{
lean_object* v_unused_163_; lean_object* v_unused_164_; lean_object* v_unused_165_; 
v_unused_163_ = lean_ctor_get(v_impl_33_, 4);
lean_dec(v_unused_163_);
v_unused_164_ = lean_ctor_get(v_impl_33_, 3);
lean_dec(v_unused_164_);
v_unused_165_ = lean_ctor_get(v_impl_33_, 0);
lean_dec(v_unused_165_);
v___x_141_ = v_impl_33_;
v_isShared_142_ = v_isSharedCheck_162_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_v_139_);
lean_inc(v_k_138_);
lean_dec(v_impl_33_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_162_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v_k_143_; lean_object* v_v_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_158_; 
v_k_143_ = lean_ctor_get(v_r_137_, 1);
v_v_144_ = lean_ctor_get(v_r_137_, 2);
v_isSharedCheck_158_ = !lean_is_exclusive(v_r_137_);
if (v_isSharedCheck_158_ == 0)
{
lean_object* v_unused_159_; lean_object* v_unused_160_; lean_object* v_unused_161_; 
v_unused_159_ = lean_ctor_get(v_r_137_, 4);
lean_dec(v_unused_159_);
v_unused_160_ = lean_ctor_get(v_r_137_, 3);
lean_dec(v_unused_160_);
v_unused_161_ = lean_ctor_get(v_r_137_, 0);
lean_dec(v_unused_161_);
v___x_146_ = v_r_137_;
v_isShared_147_ = v_isSharedCheck_158_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_v_144_);
lean_inc(v_k_143_);
lean_dec(v_r_137_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_158_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; lean_object* v___x_150_; 
v___x_148_ = lean_unsigned_to_nat(3u);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 4, v_l_120_);
lean_ctor_set(v___x_146_, 3, v_l_120_);
lean_ctor_set(v___x_146_, 2, v_v_139_);
lean_ctor_set(v___x_146_, 1, v_k_138_);
lean_ctor_set(v___x_146_, 0, v___x_34_);
v___x_150_ = v___x_146_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_34_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_k_138_);
lean_ctor_set(v_reuseFailAlloc_157_, 2, v_v_139_);
lean_ctor_set(v_reuseFailAlloc_157_, 3, v_l_120_);
lean_ctor_set(v_reuseFailAlloc_157_, 4, v_l_120_);
v___x_150_ = v_reuseFailAlloc_157_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_152_; 
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 4, v_l_120_);
lean_ctor_set(v___x_141_, 2, v_v_26_);
lean_ctor_set(v___x_141_, 1, v_k_25_);
lean_ctor_set(v___x_141_, 0, v___x_34_);
v___x_152_ = v___x_141_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_34_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_k_25_);
lean_ctor_set(v_reuseFailAlloc_156_, 2, v_v_26_);
lean_ctor_set(v_reuseFailAlloc_156_, 3, v_l_120_);
lean_ctor_set(v_reuseFailAlloc_156_, 4, v_l_120_);
v___x_152_ = v_reuseFailAlloc_156_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_154_; 
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 4, v___x_152_);
lean_ctor_set(v___x_30_, 3, v___x_150_);
lean_ctor_set(v___x_30_, 2, v_v_144_);
lean_ctor_set(v___x_30_, 1, v_k_143_);
lean_ctor_set(v___x_30_, 0, v___x_148_);
v___x_154_ = v___x_30_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_148_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_k_143_);
lean_ctor_set(v_reuseFailAlloc_155_, 2, v_v_144_);
lean_ctor_set(v_reuseFailAlloc_155_, 3, v___x_150_);
lean_ctor_set(v_reuseFailAlloc_155_, 4, v___x_152_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
}
}
else
{
lean_object* v___x_166_; lean_object* v___x_168_; 
v___x_166_ = lean_unsigned_to_nat(2u);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 4, v_r_137_);
lean_ctor_set(v___x_30_, 3, v_impl_33_);
lean_ctor_set(v___x_30_, 0, v___x_166_);
v___x_168_ = v___x_30_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_166_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v_k_25_);
lean_ctor_set(v_reuseFailAlloc_169_, 2, v_v_26_);
lean_ctor_set(v_reuseFailAlloc_169_, 3, v_impl_33_);
lean_ctor_set(v_reuseFailAlloc_169_, 4, v_r_137_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
}
}
case 1:
{
lean_object* v___x_171_; 
lean_dec(v_v_26_);
lean_dec(v_k_25_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 2, v_v_22_);
lean_ctor_set(v___x_30_, 1, v_k_21_);
v___x_171_ = v___x_30_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_size_24_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_k_21_);
lean_ctor_set(v_reuseFailAlloc_172_, 2, v_v_22_);
lean_ctor_set(v_reuseFailAlloc_172_, 3, v_l_27_);
lean_ctor_set(v_reuseFailAlloc_172_, 4, v_r_28_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
default: 
{
lean_object* v_impl_173_; lean_object* v___x_174_; 
lean_dec(v_size_24_);
v_impl_173_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadWorkspaceRoot_spec__0___redArg(v_k_21_, v_v_22_, v_r_28_);
v___x_174_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_27_) == 0)
{
lean_object* v_size_175_; lean_object* v_size_176_; lean_object* v_k_177_; lean_object* v_v_178_; lean_object* v_l_179_; lean_object* v_r_180_; lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v_size_175_ = lean_ctor_get(v_l_27_, 0);
v_size_176_ = lean_ctor_get(v_impl_173_, 0);
v_k_177_ = lean_ctor_get(v_impl_173_, 1);
v_v_178_ = lean_ctor_get(v_impl_173_, 2);
v_l_179_ = lean_ctor_get(v_impl_173_, 3);
lean_inc(v_l_179_);
v_r_180_ = lean_ctor_get(v_impl_173_, 4);
v___x_181_ = lean_unsigned_to_nat(3u);
v___x_182_ = lean_nat_mul(v___x_181_, v_size_175_);
v___x_183_ = lean_nat_dec_lt(v___x_182_, v_size_176_);
lean_dec(v___x_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
lean_dec(v_l_179_);
v___x_184_ = lean_nat_add(v___x_174_, v_size_175_);
v___x_185_ = lean_nat_add(v___x_184_, v_size_176_);
lean_dec(v___x_184_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 4, v_impl_173_);
lean_ctor_set(v___x_30_, 0, v___x_185_);
v___x_187_ = v___x_30_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_185_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v_k_25_);
lean_ctor_set(v_reuseFailAlloc_188_, 2, v_v_26_);
lean_ctor_set(v_reuseFailAlloc_188_, 3, v_l_27_);
lean_ctor_set(v_reuseFailAlloc_188_, 4, v_impl_173_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
else
{
lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_252_; 
lean_inc(v_r_180_);
lean_inc(v_v_178_);
lean_inc(v_k_177_);
lean_inc(v_size_176_);
v_isSharedCheck_252_ = !lean_is_exclusive(v_impl_173_);
if (v_isSharedCheck_252_ == 0)
{
lean_object* v_unused_253_; lean_object* v_unused_254_; lean_object* v_unused_255_; lean_object* v_unused_256_; lean_object* v_unused_257_; 
v_unused_253_ = lean_ctor_get(v_impl_173_, 4);
lean_dec(v_unused_253_);
v_unused_254_ = lean_ctor_get(v_impl_173_, 3);
lean_dec(v_unused_254_);
v_unused_255_ = lean_ctor_get(v_impl_173_, 2);
lean_dec(v_unused_255_);
v_unused_256_ = lean_ctor_get(v_impl_173_, 1);
lean_dec(v_unused_256_);
v_unused_257_ = lean_ctor_get(v_impl_173_, 0);
lean_dec(v_unused_257_);
v___x_190_ = v_impl_173_;
v_isShared_191_ = v_isSharedCheck_252_;
goto v_resetjp_189_;
}
else
{
lean_dec(v_impl_173_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_252_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v_size_192_; lean_object* v_k_193_; lean_object* v_v_194_; lean_object* v_l_195_; lean_object* v_r_196_; lean_object* v_size_197_; lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v_size_192_ = lean_ctor_get(v_l_179_, 0);
v_k_193_ = lean_ctor_get(v_l_179_, 1);
v_v_194_ = lean_ctor_get(v_l_179_, 2);
v_l_195_ = lean_ctor_get(v_l_179_, 3);
v_r_196_ = lean_ctor_get(v_l_179_, 4);
v_size_197_ = lean_ctor_get(v_r_180_, 0);
v___x_198_ = lean_unsigned_to_nat(2u);
v___x_199_ = lean_nat_mul(v___x_198_, v_size_197_);
v___x_200_ = lean_nat_dec_lt(v_size_192_, v___x_199_);
lean_dec(v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_228_; 
lean_inc(v_r_196_);
lean_inc(v_l_195_);
lean_inc(v_v_194_);
lean_inc(v_k_193_);
v_isSharedCheck_228_ = !lean_is_exclusive(v_l_179_);
if (v_isSharedCheck_228_ == 0)
{
lean_object* v_unused_229_; lean_object* v_unused_230_; lean_object* v_unused_231_; lean_object* v_unused_232_; lean_object* v_unused_233_; 
v_unused_229_ = lean_ctor_get(v_l_179_, 4);
lean_dec(v_unused_229_);
v_unused_230_ = lean_ctor_get(v_l_179_, 3);
lean_dec(v_unused_230_);
v_unused_231_ = lean_ctor_get(v_l_179_, 2);
lean_dec(v_unused_231_);
v_unused_232_ = lean_ctor_get(v_l_179_, 1);
lean_dec(v_unused_232_);
v_unused_233_ = lean_ctor_get(v_l_179_, 0);
lean_dec(v_unused_233_);
v___x_202_ = v_l_179_;
v_isShared_203_ = v_isSharedCheck_228_;
goto v_resetjp_201_;
}
else
{
lean_dec(v_l_179_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_228_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___y_207_; lean_object* v___y_208_; lean_object* v___y_209_; lean_object* v___y_218_; 
v___x_204_ = lean_nat_add(v___x_174_, v_size_175_);
v___x_205_ = lean_nat_add(v___x_204_, v_size_176_);
lean_dec(v_size_176_);
if (lean_obj_tag(v_l_195_) == 0)
{
lean_object* v_size_226_; 
v_size_226_ = lean_ctor_get(v_l_195_, 0);
lean_inc(v_size_226_);
v___y_218_ = v_size_226_;
goto v___jp_217_;
}
else
{
lean_object* v___x_227_; 
v___x_227_ = lean_unsigned_to_nat(0u);
v___y_218_ = v___x_227_;
goto v___jp_217_;
}
v___jp_206_:
{
lean_object* v___x_210_; lean_object* v___x_212_; 
v___x_210_ = lean_nat_add(v___y_207_, v___y_209_);
lean_dec(v___y_209_);
lean_dec(v___y_207_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 4, v_r_180_);
lean_ctor_set(v___x_202_, 3, v_r_196_);
lean_ctor_set(v___x_202_, 2, v_v_178_);
lean_ctor_set(v___x_202_, 1, v_k_177_);
lean_ctor_set(v___x_202_, 0, v___x_210_);
v___x_212_ = v___x_202_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_210_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v_k_177_);
lean_ctor_set(v_reuseFailAlloc_216_, 2, v_v_178_);
lean_ctor_set(v_reuseFailAlloc_216_, 3, v_r_196_);
lean_ctor_set(v_reuseFailAlloc_216_, 4, v_r_180_);
v___x_212_ = v_reuseFailAlloc_216_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_214_; 
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 4, v___x_212_);
lean_ctor_set(v___x_190_, 3, v___y_208_);
lean_ctor_set(v___x_190_, 2, v_v_194_);
lean_ctor_set(v___x_190_, 1, v_k_193_);
lean_ctor_set(v___x_190_, 0, v___x_205_);
v___x_214_ = v___x_190_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_205_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_k_193_);
lean_ctor_set(v_reuseFailAlloc_215_, 2, v_v_194_);
lean_ctor_set(v_reuseFailAlloc_215_, 3, v___y_208_);
lean_ctor_set(v_reuseFailAlloc_215_, 4, v___x_212_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
v___jp_217_:
{
lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_219_ = lean_nat_add(v___x_204_, v___y_218_);
lean_dec(v___y_218_);
lean_dec(v___x_204_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 4, v_l_195_);
lean_ctor_set(v___x_30_, 0, v___x_219_);
v___x_221_ = v___x_30_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_219_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_k_25_);
lean_ctor_set(v_reuseFailAlloc_225_, 2, v_v_26_);
lean_ctor_set(v_reuseFailAlloc_225_, 3, v_l_27_);
lean_ctor_set(v_reuseFailAlloc_225_, 4, v_l_195_);
v___x_221_ = v_reuseFailAlloc_225_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v___x_222_; 
v___x_222_ = lean_nat_add(v___x_174_, v_size_197_);
if (lean_obj_tag(v_r_196_) == 0)
{
lean_object* v_size_223_; 
v_size_223_ = lean_ctor_get(v_r_196_, 0);
lean_inc(v_size_223_);
v___y_207_ = v___x_222_;
v___y_208_ = v___x_221_;
v___y_209_ = v_size_223_;
goto v___jp_206_;
}
else
{
lean_object* v___x_224_; 
v___x_224_ = lean_unsigned_to_nat(0u);
v___y_207_ = v___x_222_;
v___y_208_ = v___x_221_;
v___y_209_ = v___x_224_;
goto v___jp_206_;
}
}
}
}
}
else
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_238_; 
lean_del_object(v___x_30_);
v___x_234_ = lean_nat_add(v___x_174_, v_size_175_);
v___x_235_ = lean_nat_add(v___x_234_, v_size_176_);
lean_dec(v_size_176_);
v___x_236_ = lean_nat_add(v___x_234_, v_size_192_);
lean_dec(v___x_234_);
lean_inc_ref(v_l_27_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 4, v_l_179_);
lean_ctor_set(v___x_190_, 3, v_l_27_);
lean_ctor_set(v___x_190_, 2, v_v_26_);
lean_ctor_set(v___x_190_, 1, v_k_25_);
lean_ctor_set(v___x_190_, 0, v___x_236_);
v___x_238_ = v___x_190_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_k_25_);
lean_ctor_set(v_reuseFailAlloc_251_, 2, v_v_26_);
lean_ctor_set(v_reuseFailAlloc_251_, 3, v_l_27_);
lean_ctor_set(v_reuseFailAlloc_251_, 4, v_l_179_);
v___x_238_ = v_reuseFailAlloc_251_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
v_isSharedCheck_245_ = !lean_is_exclusive(v_l_27_);
if (v_isSharedCheck_245_ == 0)
{
lean_object* v_unused_246_; lean_object* v_unused_247_; lean_object* v_unused_248_; lean_object* v_unused_249_; lean_object* v_unused_250_; 
v_unused_246_ = lean_ctor_get(v_l_27_, 4);
lean_dec(v_unused_246_);
v_unused_247_ = lean_ctor_get(v_l_27_, 3);
lean_dec(v_unused_247_);
v_unused_248_ = lean_ctor_get(v_l_27_, 2);
lean_dec(v_unused_248_);
v_unused_249_ = lean_ctor_get(v_l_27_, 1);
lean_dec(v_unused_249_);
v_unused_250_ = lean_ctor_get(v_l_27_, 0);
lean_dec(v_unused_250_);
v___x_240_ = v_l_27_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_dec(v_l_27_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 4, v_r_180_);
lean_ctor_set(v___x_240_, 3, v___x_238_);
lean_ctor_set(v___x_240_, 2, v_v_178_);
lean_ctor_set(v___x_240_, 1, v_k_177_);
lean_ctor_set(v___x_240_, 0, v___x_235_);
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_k_177_);
lean_ctor_set(v_reuseFailAlloc_244_, 2, v_v_178_);
lean_ctor_set(v_reuseFailAlloc_244_, 3, v___x_238_);
lean_ctor_set(v_reuseFailAlloc_244_, 4, v_r_180_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_258_; 
v_l_258_ = lean_ctor_get(v_impl_173_, 3);
lean_inc(v_l_258_);
if (lean_obj_tag(v_l_258_) == 0)
{
lean_object* v_r_259_; lean_object* v_k_260_; lean_object* v_v_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_284_; 
v_r_259_ = lean_ctor_get(v_impl_173_, 4);
v_k_260_ = lean_ctor_get(v_impl_173_, 1);
v_v_261_ = lean_ctor_get(v_impl_173_, 2);
v_isSharedCheck_284_ = !lean_is_exclusive(v_impl_173_);
if (v_isSharedCheck_284_ == 0)
{
lean_object* v_unused_285_; lean_object* v_unused_286_; 
v_unused_285_ = lean_ctor_get(v_impl_173_, 3);
lean_dec(v_unused_285_);
v_unused_286_ = lean_ctor_get(v_impl_173_, 0);
lean_dec(v_unused_286_);
v___x_263_ = v_impl_173_;
v_isShared_264_ = v_isSharedCheck_284_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_r_259_);
lean_inc(v_v_261_);
lean_inc(v_k_260_);
lean_dec(v_impl_173_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_284_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v_k_265_; lean_object* v_v_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_280_; 
v_k_265_ = lean_ctor_get(v_l_258_, 1);
v_v_266_ = lean_ctor_get(v_l_258_, 2);
v_isSharedCheck_280_ = !lean_is_exclusive(v_l_258_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; lean_object* v_unused_282_; lean_object* v_unused_283_; 
v_unused_281_ = lean_ctor_get(v_l_258_, 4);
lean_dec(v_unused_281_);
v_unused_282_ = lean_ctor_get(v_l_258_, 3);
lean_dec(v_unused_282_);
v_unused_283_ = lean_ctor_get(v_l_258_, 0);
lean_dec(v_unused_283_);
v___x_268_ = v_l_258_;
v_isShared_269_ = v_isSharedCheck_280_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_v_266_);
lean_inc(v_k_265_);
lean_dec(v_l_258_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_280_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_270_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_259_, 2);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 4, v_r_259_);
lean_ctor_set(v___x_268_, 3, v_r_259_);
lean_ctor_set(v___x_268_, 2, v_v_26_);
lean_ctor_set(v___x_268_, 1, v_k_25_);
lean_ctor_set(v___x_268_, 0, v___x_174_);
v___x_272_ = v___x_268_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_k_25_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_v_26_);
lean_ctor_set(v_reuseFailAlloc_279_, 3, v_r_259_);
lean_ctor_set(v_reuseFailAlloc_279_, 4, v_r_259_);
v___x_272_ = v_reuseFailAlloc_279_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
lean_object* v___x_274_; 
lean_inc(v_r_259_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 3, v_r_259_);
lean_ctor_set(v___x_263_, 0, v___x_174_);
v___x_274_ = v___x_263_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_k_260_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v_v_261_);
lean_ctor_set(v_reuseFailAlloc_278_, 3, v_r_259_);
lean_ctor_set(v_reuseFailAlloc_278_, 4, v_r_259_);
v___x_274_ = v_reuseFailAlloc_278_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_276_; 
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 4, v___x_274_);
lean_ctor_set(v___x_30_, 3, v___x_272_);
lean_ctor_set(v___x_30_, 2, v_v_266_);
lean_ctor_set(v___x_30_, 1, v_k_265_);
lean_ctor_set(v___x_30_, 0, v___x_270_);
v___x_276_ = v___x_30_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_270_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_k_265_);
lean_ctor_set(v_reuseFailAlloc_277_, 2, v_v_266_);
lean_ctor_set(v_reuseFailAlloc_277_, 3, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_277_, 4, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
}
}
else
{
lean_object* v_r_287_; 
v_r_287_ = lean_ctor_get(v_impl_173_, 4);
lean_inc(v_r_287_);
if (lean_obj_tag(v_r_287_) == 0)
{
lean_object* v_k_288_; lean_object* v_v_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_300_; 
v_k_288_ = lean_ctor_get(v_impl_173_, 1);
v_v_289_ = lean_ctor_get(v_impl_173_, 2);
v_isSharedCheck_300_ = !lean_is_exclusive(v_impl_173_);
if (v_isSharedCheck_300_ == 0)
{
lean_object* v_unused_301_; lean_object* v_unused_302_; lean_object* v_unused_303_; 
v_unused_301_ = lean_ctor_get(v_impl_173_, 4);
lean_dec(v_unused_301_);
v_unused_302_ = lean_ctor_get(v_impl_173_, 3);
lean_dec(v_unused_302_);
v_unused_303_ = lean_ctor_get(v_impl_173_, 0);
lean_dec(v_unused_303_);
v___x_291_ = v_impl_173_;
v_isShared_292_ = v_isSharedCheck_300_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_v_289_);
lean_inc(v_k_288_);
lean_dec(v_impl_173_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_300_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_293_ = lean_unsigned_to_nat(3u);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 4, v_l_258_);
lean_ctor_set(v___x_291_, 2, v_v_26_);
lean_ctor_set(v___x_291_, 1, v_k_25_);
lean_ctor_set(v___x_291_, 0, v___x_174_);
v___x_295_ = v___x_291_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_k_25_);
lean_ctor_set(v_reuseFailAlloc_299_, 2, v_v_26_);
lean_ctor_set(v_reuseFailAlloc_299_, 3, v_l_258_);
lean_ctor_set(v_reuseFailAlloc_299_, 4, v_l_258_);
v___x_295_ = v_reuseFailAlloc_299_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_297_; 
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 4, v_r_287_);
lean_ctor_set(v___x_30_, 3, v___x_295_);
lean_ctor_set(v___x_30_, 2, v_v_289_);
lean_ctor_set(v___x_30_, 1, v_k_288_);
lean_ctor_set(v___x_30_, 0, v___x_293_);
v___x_297_ = v___x_30_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v_k_288_);
lean_ctor_set(v_reuseFailAlloc_298_, 2, v_v_289_);
lean_ctor_set(v_reuseFailAlloc_298_, 3, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_298_, 4, v_r_287_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
else
{
lean_object* v___x_304_; lean_object* v___x_306_; 
v___x_304_ = lean_unsigned_to_nat(2u);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 4, v_impl_173_);
lean_ctor_set(v___x_30_, 3, v_r_287_);
lean_ctor_set(v___x_30_, 0, v___x_304_);
v___x_306_ = v___x_30_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_304_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v_k_25_);
lean_ctor_set(v_reuseFailAlloc_307_, 2, v_v_26_);
lean_ctor_set(v_reuseFailAlloc_307_, 3, v_r_287_);
lean_ctor_set(v_reuseFailAlloc_307_, 4, v_impl_173_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
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
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = lean_unsigned_to_nat(1u);
v___x_310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
lean_ctor_set(v___x_310_, 1, v_k_21_);
lean_ctor_set(v___x_310_, 2, v_v_22_);
lean_ctor_set(v___x_310_, 3, v_t_23_);
lean_ctor_set(v___x_310_, 4, v_t_23_);
return v___x_310_;
}
}
}
lean_object* l_Lake_loadWorkspaceRoot(lean_object* v_config_312_, lean_object* v_a_313_){
_start:
{
lean_object* v_lakeEnv_315_; lean_object* v_lakeArgs_x3f_316_; lean_object* v_wsDir_317_; lean_object* v_pkgName_318_; lean_object* v_relPkgDir_319_; lean_object* v_pkgDir_320_; lean_object* v_relConfigFile_321_; lean_object* v_configFile_322_; lean_object* v_configLang_x3f_323_; lean_object* v_relManifestFile_324_; lean_object* v_packageOverrides_325_; lean_object* v_lakeOpts_326_; lean_object* v_leanOpts_327_; uint8_t v_reconfigure_328_; uint8_t v_updateDeps_329_; uint8_t v_updateToolchain_330_; lean_object* v_scope_331_; lean_object* v_remoteUrl_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_411_; 
v_lakeEnv_315_ = lean_ctor_get(v_config_312_, 0);
v_lakeArgs_x3f_316_ = lean_ctor_get(v_config_312_, 1);
v_wsDir_317_ = lean_ctor_get(v_config_312_, 2);
v_pkgName_318_ = lean_ctor_get(v_config_312_, 4);
v_relPkgDir_319_ = lean_ctor_get(v_config_312_, 5);
v_pkgDir_320_ = lean_ctor_get(v_config_312_, 6);
v_relConfigFile_321_ = lean_ctor_get(v_config_312_, 7);
v_configFile_322_ = lean_ctor_get(v_config_312_, 8);
v_configLang_x3f_323_ = lean_ctor_get(v_config_312_, 9);
v_relManifestFile_324_ = lean_ctor_get(v_config_312_, 10);
v_packageOverrides_325_ = lean_ctor_get(v_config_312_, 11);
v_lakeOpts_326_ = lean_ctor_get(v_config_312_, 12);
v_leanOpts_327_ = lean_ctor_get(v_config_312_, 13);
v_reconfigure_328_ = lean_ctor_get_uint8(v_config_312_, sizeof(void*)*16);
v_updateDeps_329_ = lean_ctor_get_uint8(v_config_312_, sizeof(void*)*16 + 1);
v_updateToolchain_330_ = lean_ctor_get_uint8(v_config_312_, sizeof(void*)*16 + 2);
v_scope_331_ = lean_ctor_get(v_config_312_, 14);
v_remoteUrl_332_ = lean_ctor_get(v_config_312_, 15);
v_isSharedCheck_411_ = !lean_is_exclusive(v_config_312_);
if (v_isSharedCheck_411_ == 0)
{
lean_object* v_unused_412_; 
v_unused_412_ = lean_ctor_get(v_config_312_, 3);
lean_dec(v_unused_412_);
v___x_334_ = v_config_312_;
v_isShared_335_ = v_isSharedCheck_411_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_remoteUrl_332_);
lean_inc(v_scope_331_);
lean_inc(v_leanOpts_327_);
lean_inc(v_lakeOpts_326_);
lean_inc(v_packageOverrides_325_);
lean_inc(v_relManifestFile_324_);
lean_inc(v_configLang_x3f_323_);
lean_inc(v_configFile_322_);
lean_inc(v_relConfigFile_321_);
lean_inc(v_pkgDir_320_);
lean_inc(v_relPkgDir_319_);
lean_inc(v_pkgName_318_);
lean_inc(v_wsDir_317_);
lean_inc(v_lakeArgs_x3f_316_);
lean_inc(v_lakeEnv_315_);
lean_dec(v_config_312_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_411_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_336_ = l_Lean_searchPathRef;
v___x_337_ = l_Lake_Env_leanSearchPath(v_lakeEnv_315_);
v___x_338_ = lean_st_ref_swap(v___x_336_, v___x_337_);
lean_dec(v___x_338_);
lean_inc_ref(v_lakeEnv_315_);
v___x_339_ = l_Lake_loadLakeConfig(v_lakeEnv_315_, v_a_313_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v_a_341_; lean_object* v___x_342_; lean_object* v___x_344_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_a_340_);
v_a_341_ = lean_ctor_get(v___x_339_, 1);
lean_inc(v_a_341_);
lean_dec_ref_known(v___x_339_, 2);
v___x_342_ = lean_unsigned_to_nat(0u);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 3, v___x_342_);
v___x_344_ = v___x_334_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_lakeEnv_315_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_lakeArgs_x3f_316_);
lean_ctor_set(v_reuseFailAlloc_401_, 2, v_wsDir_317_);
lean_ctor_set(v_reuseFailAlloc_401_, 3, v___x_342_);
lean_ctor_set(v_reuseFailAlloc_401_, 4, v_pkgName_318_);
lean_ctor_set(v_reuseFailAlloc_401_, 5, v_relPkgDir_319_);
lean_ctor_set(v_reuseFailAlloc_401_, 6, v_pkgDir_320_);
lean_ctor_set(v_reuseFailAlloc_401_, 7, v_relConfigFile_321_);
lean_ctor_set(v_reuseFailAlloc_401_, 8, v_configFile_322_);
lean_ctor_set(v_reuseFailAlloc_401_, 9, v_configLang_x3f_323_);
lean_ctor_set(v_reuseFailAlloc_401_, 10, v_relManifestFile_324_);
lean_ctor_set(v_reuseFailAlloc_401_, 11, v_packageOverrides_325_);
lean_ctor_set(v_reuseFailAlloc_401_, 12, v_lakeOpts_326_);
lean_ctor_set(v_reuseFailAlloc_401_, 13, v_leanOpts_327_);
lean_ctor_set(v_reuseFailAlloc_401_, 14, v_scope_331_);
lean_ctor_set(v_reuseFailAlloc_401_, 15, v_remoteUrl_332_);
lean_ctor_set_uint8(v_reuseFailAlloc_401_, sizeof(void*)*16, v_reconfigure_328_);
lean_ctor_set_uint8(v_reuseFailAlloc_401_, sizeof(void*)*16 + 1, v_updateDeps_329_);
lean_ctor_set_uint8(v_reuseFailAlloc_401_, sizeof(void*)*16 + 2, v_updateToolchain_330_);
v___x_344_ = v_reuseFailAlloc_401_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = ((lean_object*)(l_Lake_loadWorkspaceRoot___closed__0));
v___x_346_ = l_Lake_resolveConfigFile(v___x_345_, v___x_344_, v_a_341_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v_a_348_; lean_object* v___x_349_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc_n(v_a_347_, 2);
v_a_348_ = lean_ctor_get(v___x_346_, 1);
lean_inc(v_a_348_);
lean_dec_ref_known(v___x_346_, 2);
v___x_349_ = l_Lake_loadConfigFile___redArg(v_a_347_, v_a_348_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_382_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
v_a_351_ = lean_ctor_get(v___x_349_, 1);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_382_ == 0)
{
v___x_353_ = v___x_349_;
v_isShared_354_ = v_isSharedCheck_382_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_inc(v_a_350_);
lean_dec(v___x_349_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_382_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v_facetDecls_355_; lean_object* v___x_356_; lean_object* v___y_358_; lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___x_374_; 
v_facetDecls_355_ = lean_ctor_get(v_a_350_, 2);
lean_inc_ref(v_facetDecls_355_);
v___x_356_ = l_Lake_mkPackage(v_a_347_, v_a_350_, v___x_342_);
v___x_372_ = l_Lake_initFacetConfigs;
v___x_373_ = lean_array_get_size(v_facetDecls_355_);
v___x_374_ = lean_nat_dec_lt(v___x_342_, v___x_373_);
if (v___x_374_ == 0)
{
lean_dec_ref(v_facetDecls_355_);
v___y_358_ = v___x_372_;
goto v___jp_357_;
}
else
{
uint8_t v___x_375_; 
v___x_375_ = lean_nat_dec_le(v___x_373_, v___x_373_);
if (v___x_375_ == 0)
{
if (v___x_374_ == 0)
{
lean_dec_ref(v_facetDecls_355_);
v___y_358_ = v___x_372_;
goto v___jp_357_;
}
else
{
size_t v___x_376_; size_t v___x_377_; lean_object* v___x_378_; 
v___x_376_ = ((size_t)0ULL);
v___x_377_ = lean_usize_of_nat(v___x_373_);
v___x_378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspaceRoot_spec__1(v_facetDecls_355_, v___x_376_, v___x_377_, v___x_372_);
lean_dec_ref(v_facetDecls_355_);
v___y_358_ = v___x_378_;
goto v___jp_357_;
}
}
else
{
size_t v___x_379_; size_t v___x_380_; lean_object* v___x_381_; 
v___x_379_ = ((size_t)0ULL);
v___x_380_ = lean_usize_of_nat(v___x_373_);
v___x_381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspaceRoot_spec__1(v_facetDecls_355_, v___x_379_, v___x_380_, v___x_372_);
lean_dec_ref(v_facetDecls_355_);
v___y_358_ = v___x_381_;
goto v___jp_357_;
}
}
v___jp_357_:
{
lean_object* v_lakeEnv_359_; lean_object* v_lakeArgs_x3f_360_; lean_object* v_keyName_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_370_; 
v_lakeEnv_359_ = lean_ctor_get(v_a_347_, 0);
lean_inc_ref(v_lakeEnv_359_);
v_lakeArgs_x3f_360_ = lean_ctor_get(v_a_347_, 1);
lean_inc(v_lakeArgs_x3f_360_);
lean_dec(v_a_347_);
v_keyName_361_ = lean_ctor_get(v___x_356_, 2);
lean_inc(v_keyName_361_);
lean_inc_ref_n(v___x_356_, 2);
v___x_362_ = l_Lake_computeLakeCache(v___x_356_, v_lakeEnv_359_);
v___x_363_ = lean_unsigned_to_nat(1u);
v___x_364_ = lean_mk_empty_array_with_capacity(v___x_363_);
v___x_365_ = lean_array_push(v___x_364_, v___x_356_);
v___x_366_ = lean_box(1);
v___x_367_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadWorkspaceRoot_spec__0___redArg(v_keyName_361_, v___x_356_, v___x_366_);
v___x_368_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_368_, 0, v_lakeEnv_359_);
lean_ctor_set(v___x_368_, 1, v_a_340_);
lean_ctor_set(v___x_368_, 2, v___x_362_);
lean_ctor_set(v___x_368_, 3, v_lakeArgs_x3f_360_);
lean_ctor_set(v___x_368_, 4, v___x_365_);
lean_ctor_set(v___x_368_, 5, v___x_367_);
lean_ctor_set(v___x_368_, 6, v___y_358_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_368_);
v___x_370_ = v___x_353_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_a_351_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
else
{
lean_object* v_a_383_; lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
lean_dec(v_a_347_);
lean_dec(v_a_340_);
v_a_383_ = lean_ctor_get(v___x_349_, 0);
v_a_384_ = lean_ctor_get(v___x_349_, 1);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_349_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_inc(v_a_383_);
lean_dec(v___x_349_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_383_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_a_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
else
{
lean_object* v_a_392_; lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec(v_a_340_);
v_a_392_ = lean_ctor_get(v___x_346_, 0);
v_a_393_ = lean_ctor_get(v___x_346_, 1);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_346_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_inc(v_a_392_);
lean_dec(v___x_346_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_392_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
}
else
{
lean_object* v_a_402_; lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
lean_del_object(v___x_334_);
lean_dec_ref(v_remoteUrl_332_);
lean_dec_ref(v_scope_331_);
lean_dec_ref(v_leanOpts_327_);
lean_dec(v_lakeOpts_326_);
lean_dec_ref(v_packageOverrides_325_);
lean_dec_ref(v_relManifestFile_324_);
lean_dec(v_configLang_x3f_323_);
lean_dec_ref(v_configFile_322_);
lean_dec_ref(v_relConfigFile_321_);
lean_dec_ref(v_pkgDir_320_);
lean_dec_ref(v_relPkgDir_319_);
lean_dec(v_pkgName_318_);
lean_dec_ref(v_wsDir_317_);
lean_dec(v_lakeArgs_x3f_316_);
lean_dec_ref(v_lakeEnv_315_);
v_a_402_ = lean_ctor_get(v___x_339_, 0);
v_a_403_ = lean_ctor_get(v___x_339_, 1);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_339_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_inc(v_a_402_);
lean_dec(v___x_339_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_402_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_a_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_loadWorkspaceRoot_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_312_ = stack[0].m_obj;
lean_object* v_a_313_ = stack[1].m_obj;
lean_object* v_res_413_;
v_res_413_ = l_Lake_loadWorkspaceRoot(v_config_312_, v_a_313_);
stack->m_obj
 = v_res_413_;
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspaceRoot___boxed(lean_object* v_config_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lake_loadWorkspaceRoot(v_config_414_, v_a_415_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadWorkspaceRoot_spec__0(lean_object* v_00_u03b2_418_, lean_object* v_k_419_, lean_object* v_v_420_, lean_object* v_t_421_, lean_object* v_hl_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_loadWorkspaceRoot_spec__0___redArg(v_k_419_, v_v_420_, v_t_421_);
return v___x_423_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(lean_object* v_as_424_, size_t v_i_425_, size_t v_stop_426_, lean_object* v_b_427_, lean_object* v___y_428_){
_start:
{
uint8_t v___x_430_; 
v___x_430_ = lean_usize_dec_eq(v_i_425_, v_stop_426_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; lean_object* v___x_432_; size_t v___x_433_; size_t v___x_434_; 
v___x_431_ = lean_array_uget_borrowed(v_as_424_, v_i_425_);
lean_inc_ref(v___y_428_);
lean_inc(v___x_431_);
v___x_432_ = lean_apply_2(v___y_428_, v___x_431_, lean_box(0));
v___x_433_ = ((size_t)1ULL);
v___x_434_ = lean_usize_add(v_i_425_, v___x_433_);
v_i_425_ = v___x_434_;
v_b_427_ = v___x_432_;
goto _start;
}
else
{
lean_object* v___x_436_; 
v___x_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_436_, 0, v_b_427_);
return v___x_436_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_424_ = stack[0].m_obj;
size_t v_i_425_ = stack[1].m_num;
size_t v_stop_426_ = stack[2].m_num;
lean_object* v_b_427_ = stack[3].m_obj;
lean_object* v___y_428_ = stack[4].m_obj;
lean_object* v_res_437_;
v_res_437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_as_424_, v_i_425_, v_stop_426_, v_b_427_, v___y_428_);
stack->m_obj
 = v_res_437_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0___boxed(lean_object* v_as_438_, lean_object* v_i_439_, lean_object* v_stop_440_, lean_object* v_b_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
size_t v_i_boxed_444_; size_t v_stop_boxed_445_; lean_object* v_res_446_; 
v_i_boxed_444_ = lean_unbox_usize(v_i_439_);
lean_dec(v_i_439_);
v_stop_boxed_445_ = lean_unbox_usize(v_stop_440_);
lean_dec(v_stop_440_);
v_res_446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_as_438_, v_i_boxed_444_, v_stop_boxed_445_, v_b_441_, v___y_442_);
lean_dec_ref(v___y_442_);
lean_dec_ref(v_as_438_);
return v_res_446_;
}
}
lean_object* l_Lake_loadWorkspace(lean_object* v_config_449_, lean_object* v_a_450_){
_start:
{
lean_object* v_packageOverrides_452_; lean_object* v_leanOpts_453_; uint8_t v_reconfigure_454_; uint8_t v_updateDeps_455_; uint8_t v_updateToolchain_456_; lean_object* v_a_458_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v_packageOverrides_452_ = lean_ctor_get(v_config_449_, 11);
lean_inc_ref(v_packageOverrides_452_);
v_leanOpts_453_ = lean_ctor_get(v_config_449_, 13);
lean_inc_ref(v_leanOpts_453_);
v_reconfigure_454_ = lean_ctor_get_uint8(v_config_449_, sizeof(void*)*16);
v_updateDeps_455_ = lean_ctor_get_uint8(v_config_449_, sizeof(void*)*16 + 1);
v_updateToolchain_456_ = lean_ctor_get_uint8(v_config_449_, sizeof(void*)*16 + 2);
v___x_486_ = lean_unsigned_to_nat(0u);
v___x_487_ = ((lean_object*)(l_Lake_loadWorkspace___closed__0));
v___x_488_ = l_Lake_loadWorkspaceRoot(v_config_449_, v___x_487_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v_a_490_; lean_object* v___x_491_; uint8_t v___x_492_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
v_a_490_ = lean_ctor_get(v___x_488_, 1);
lean_inc(v_a_490_);
lean_dec_ref_known(v___x_488_, 2);
v___x_491_ = lean_array_get_size(v_a_490_);
v___x_492_ = lean_nat_dec_lt(v___x_486_, v___x_491_);
if (v___x_492_ == 0)
{
lean_dec(v_a_490_);
v_a_458_ = v_a_489_;
goto v___jp_457_;
}
else
{
lean_object* v___x_493_; size_t v___x_494_; size_t v___x_495_; lean_object* v___x_496_; 
v___x_493_ = lean_box(0);
v___x_494_ = ((size_t)0ULL);
v___x_495_ = lean_usize_of_nat(v___x_491_);
v___x_496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_a_490_, v___x_494_, v___x_495_, v___x_493_, v_a_450_);
lean_dec(v_a_490_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_dec_ref_known(v___x_496_, 1);
v_a_458_ = v_a_489_;
goto v___jp_457_;
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_dec(v_a_489_);
lean_dec_ref(v_leanOpts_453_);
lean_dec_ref(v_packageOverrides_452_);
v_a_497_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_496_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
else
{
lean_object* v_a_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
lean_dec_ref(v_leanOpts_453_);
lean_dec_ref(v_packageOverrides_452_);
v_a_505_ = lean_ctor_get(v___x_488_, 1);
lean_inc(v_a_505_);
lean_dec_ref_known(v___x_488_, 2);
v___x_506_ = lean_array_get_size(v_a_505_);
v___x_507_ = lean_nat_dec_lt(v___x_486_, v___x_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; 
lean_dec(v_a_505_);
v___x_508_ = lean_box(0);
v___x_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
return v___x_509_;
}
else
{
lean_object* v___x_510_; size_t v___x_511_; size_t v___x_512_; lean_object* v___x_513_; 
v___x_510_ = lean_box(0);
v___x_511_ = ((size_t)0ULL);
v___x_512_ = lean_usize_of_nat(v___x_506_);
v___x_513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_a_505_, v___x_511_, v___x_512_, v___x_510_, v_a_450_);
lean_dec(v_a_505_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_520_ == 0)
{
lean_object* v_unused_521_; 
v_unused_521_ = lean_ctor_get(v___x_513_, 0);
lean_dec(v_unused_521_);
v___x_515_ = v___x_513_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_dec(v___x_513_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
lean_ctor_set_tag(v___x_515_, 1);
lean_ctor_set(v___x_515_, 0, v___x_510_);
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_510_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
v_a_522_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_513_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_513_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
}
v___jp_457_:
{
if (v_updateDeps_455_ == 0)
{
lean_object* v_packages_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v_dir_462_; lean_object* v_relManifestFile_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v_packages_459_ = lean_ctor_get(v_a_458_, 4);
v___x_460_ = lean_unsigned_to_nat(0u);
v___x_461_ = lean_array_fget_borrowed(v_packages_459_, v___x_460_);
v_dir_462_ = lean_ctor_get(v___x_461_, 4);
v_relManifestFile_463_ = lean_ctor_get(v___x_461_, 9);
lean_inc_ref(v_relManifestFile_463_);
lean_inc_ref(v_dir_462_);
v___x_464_ = l_Lake_joinRelative(v_dir_462_, v_relManifestFile_463_);
v___x_465_ = l_Lake_Manifest_load_x3f(v___x_464_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_a_466_);
lean_dec_ref_known(v___x_465_, 1);
if (lean_obj_tag(v_a_466_) == 1)
{
lean_object* v_val_467_; lean_object* v___x_468_; 
v_val_467_ = lean_ctor_get(v_a_466_, 0);
lean_inc(v_val_467_);
lean_dec_ref_known(v_a_466_, 1);
v___x_468_ = l_Lake_Workspace_materializeDeps(v_a_458_, v_val_467_, v_leanOpts_453_, v_reconfigure_454_, v_packageOverrides_452_, v_a_450_);
lean_dec_ref(v_packageOverrides_452_);
return v___x_468_;
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; 
lean_dec(v_a_466_);
lean_dec_ref(v_packageOverrides_452_);
v___x_469_ = l_Lean_NameSet_empty;
v___x_470_ = l_Lake_Workspace_updateAndMaterialize(v_a_458_, v___x_469_, v_leanOpts_453_, v_updateToolchain_456_, v_a_450_);
return v___x_470_;
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_483_; 
lean_dec_ref(v_a_458_);
lean_dec_ref(v_leanOpts_453_);
lean_dec_ref(v_packageOverrides_452_);
v_a_471_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_483_ == 0)
{
v___x_473_ = v___x_465_;
v_isShared_474_ = v_isSharedCheck_483_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_465_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_483_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; uint8_t v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_481_; 
v___x_475_ = lean_io_error_to_string(v_a_471_);
v___x_476_ = 3;
v___x_477_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_477_, 0, v___x_475_);
lean_ctor_set_uint8(v___x_477_, sizeof(void*)*1, v___x_476_);
lean_inc_ref(v_a_450_);
v___x_478_ = lean_apply_2(v_a_450_, v___x_477_, lean_box(0));
v___x_479_ = lean_box(0);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 0, v___x_479_);
v___x_481_ = v___x_473_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
else
{
lean_object* v___x_484_; lean_object* v___x_485_; 
lean_dec_ref(v_packageOverrides_452_);
v___x_484_ = l_Lean_NameSet_empty;
v___x_485_ = l_Lake_Workspace_updateAndMaterialize(v_a_458_, v___x_484_, v_leanOpts_453_, v_updateToolchain_456_, v_a_450_);
return v___x_485_;
}
}
}
}
LEAN_EXPORT void l_Lake_loadWorkspace_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_449_ = stack[0].m_obj;
lean_object* v_a_450_ = stack[1].m_obj;
lean_object* v_res_530_;
v_res_530_ = l_Lake_loadWorkspace(v_config_449_, v_a_450_);
stack->m_obj
 = v_res_530_;
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___boxed(lean_object* v_config_531_, lean_object* v_a_532_, lean_object* v_a_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lake_loadWorkspace(v_config_531_, v_a_532_);
lean_dec_ref(v_a_532_);
return v_res_534_;
}
}
lean_object* l_Lake_updateManifest(lean_object* v_config_535_, lean_object* v_toUpdate_536_, lean_object* v_a_537_){
_start:
{
lean_object* v_leanOpts_539_; uint8_t v_updateToolchain_540_; lean_object* v_a_542_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v_leanOpts_539_ = lean_ctor_get(v_config_535_, 13);
lean_inc_ref(v_leanOpts_539_);
v_updateToolchain_540_ = lean_ctor_get_uint8(v_config_535_, sizeof(void*)*16 + 2);
v___x_561_ = lean_unsigned_to_nat(0u);
v___x_562_ = ((lean_object*)(l_Lake_loadWorkspace___closed__0));
v___x_563_ = l_Lake_loadWorkspaceRoot(v_config_535_, v___x_562_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v_a_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_a_564_);
v_a_565_ = lean_ctor_get(v___x_563_, 1);
lean_inc(v_a_565_);
lean_dec_ref_known(v___x_563_, 2);
v___x_566_ = lean_array_get_size(v_a_565_);
v___x_567_ = lean_nat_dec_lt(v___x_561_, v___x_566_);
if (v___x_567_ == 0)
{
lean_dec(v_a_565_);
v_a_542_ = v_a_564_;
goto v___jp_541_;
}
else
{
lean_object* v___x_568_; size_t v___x_569_; size_t v___x_570_; lean_object* v___x_571_; 
v___x_568_ = lean_box(0);
v___x_569_ = ((size_t)0ULL);
v___x_570_ = lean_usize_of_nat(v___x_566_);
v___x_571_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_a_565_, v___x_569_, v___x_570_, v___x_568_, v_a_537_);
lean_dec(v_a_565_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_dec_ref_known(v___x_571_, 1);
v_a_542_ = v_a_564_;
goto v___jp_541_;
}
else
{
lean_dec(v_a_564_);
lean_dec_ref(v_leanOpts_539_);
lean_dec(v_toUpdate_536_);
return v___x_571_;
}
}
}
else
{
lean_object* v_a_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
lean_dec_ref(v_leanOpts_539_);
lean_dec(v_toUpdate_536_);
v_a_572_ = lean_ctor_get(v___x_563_, 1);
lean_inc(v_a_572_);
lean_dec_ref_known(v___x_563_, 2);
v___x_573_ = lean_array_get_size(v_a_572_);
v___x_574_ = lean_nat_dec_lt(v___x_561_, v___x_573_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; lean_object* v___x_576_; 
lean_dec(v_a_572_);
v___x_575_ = lean_box(0);
v___x_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
return v___x_576_;
}
else
{
lean_object* v___x_577_; size_t v___x_578_; size_t v___x_579_; lean_object* v___x_580_; 
v___x_577_ = lean_box(0);
v___x_578_ = ((size_t)0ULL);
v___x_579_ = lean_usize_of_nat(v___x_573_);
v___x_580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_a_572_, v___x_578_, v___x_579_, v___x_577_, v_a_537_);
lean_dec(v_a_572_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_587_ == 0)
{
lean_object* v_unused_588_; 
v_unused_588_ = lean_ctor_get(v___x_580_, 0);
lean_dec(v_unused_588_);
v___x_582_ = v___x_580_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_dec(v___x_580_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set_tag(v___x_582_, 1);
lean_ctor_set(v___x_582_, 0, v___x_577_);
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_577_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
else
{
return v___x_580_;
}
}
}
v___jp_541_:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_box(0);
v___x_544_ = l_Lake_Workspace_updateAndMaterialize(v_a_542_, v_toUpdate_536_, v_leanOpts_539_, v_updateToolchain_540_, v_a_537_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_551_ == 0)
{
lean_object* v_unused_552_; 
v_unused_552_ = lean_ctor_get(v___x_544_, 0);
lean_dec(v_unused_552_);
v___x_546_ = v___x_544_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_dec(v___x_544_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_543_);
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_543_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
v_a_553_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_544_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_544_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_updateManifest_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_535_ = stack[0].m_obj;
lean_object* v_toUpdate_536_ = stack[1].m_obj;
lean_object* v_a_537_ = stack[2].m_obj;
lean_object* v_res_589_;
v_res_589_ = l_Lake_updateManifest(v_config_535_, v_toUpdate_536_, v_a_537_);
stack->m_obj
 = v_res_589_;
}
LEAN_EXPORT lean_object* l_Lake_updateManifest___boxed(lean_object* v_config_590_, lean_object* v_toUpdate_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lake_updateManifest(v_config_590_, v_toUpdate_591_, v_a_592_);
lean_dec_ref(v_a_592_);
return v_res_594_;
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
