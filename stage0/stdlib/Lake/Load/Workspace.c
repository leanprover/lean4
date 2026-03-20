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
lean_object* lean_mk_io_user_error(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_searchPathRef;
lean_object* l_Lake_Env_leanSearchPath(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lake_loadLakeConfig(lean_object*, lean_object*);
lean_object* l_Lake_loadPackageCore(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lake_initFacetConfigs;
lean_object* l_Lake_Workspace_addFacetsFromEnv(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lake_Manifest_load_x3f(lean_object*);
lean_object* l_Lake_Workspace_materializeDeps(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_loadWorkspaceRoot_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_loadWorkspaceRoot_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_loadWorkspaceRoot_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_loadWorkspaceRoot_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_loadWorkspaceRoot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "[root]"};
static const lean_object* l_Lake_loadWorkspaceRoot___closed__0 = (const lean_object*)&l_Lake_loadWorkspaceRoot___closed__0_value;
static const lean_array_object l_Lake_loadWorkspaceRoot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_loadWorkspaceRoot___closed__1 = (const lean_object*)&l_Lake_loadWorkspaceRoot___closed__1_value;
static const lean_string_object l_Lake_loadWorkspaceRoot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cache"};
static const lean_object* l_Lake_loadWorkspaceRoot___closed__2 = (const lean_object*)&l_Lake_loadWorkspaceRoot___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_loadWorkspaceRoot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspaceRoot___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_loadWorkspace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_loadWorkspace___closed__0 = (const lean_object*)&l_Lake_loadWorkspace___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_loadWorkspace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateManifest(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateManifest___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_loadWorkspaceRoot_spec__0___redArg(lean_object* v_e_1_){
_start:
{
if (lean_obj_tag(v_e_1_) == 0)
{
lean_object* v_a_3_; lean_object* v___x_5_; uint8_t v_isShared_6_; uint8_t v_isSharedCheck_11_; 
v_a_3_ = lean_ctor_get(v_e_1_, 0);
v_isSharedCheck_11_ = !lean_is_exclusive(v_e_1_);
if (v_isSharedCheck_11_ == 0)
{
v___x_5_ = v_e_1_;
v_isShared_6_ = v_isSharedCheck_11_;
goto v_resetjp_4_;
}
else
{
lean_inc(v_a_3_);
lean_dec(v_e_1_);
v___x_5_ = lean_box(0);
v_isShared_6_ = v_isSharedCheck_11_;
goto v_resetjp_4_;
}
v_resetjp_4_:
{
lean_object* v___x_7_; lean_object* v___x_9_; 
v___x_7_ = lean_mk_io_user_error(v_a_3_);
if (v_isShared_6_ == 0)
{
lean_ctor_set_tag(v___x_5_, 1);
lean_ctor_set(v___x_5_, 0, v___x_7_);
v___x_9_ = v___x_5_;
goto v_reusejp_8_;
}
else
{
lean_object* v_reuseFailAlloc_10_; 
v_reuseFailAlloc_10_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_10_, 0, v___x_7_);
v___x_9_ = v_reuseFailAlloc_10_;
goto v_reusejp_8_;
}
v_reusejp_8_:
{
return v___x_9_;
}
}
}
else
{
lean_object* v_a_12_; lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_19_; 
v_a_12_ = lean_ctor_get(v_e_1_, 0);
v_isSharedCheck_19_ = !lean_is_exclusive(v_e_1_);
if (v_isSharedCheck_19_ == 0)
{
v___x_14_ = v_e_1_;
v_isShared_15_ = v_isSharedCheck_19_;
goto v_resetjp_13_;
}
else
{
lean_inc(v_a_12_);
lean_dec(v_e_1_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_19_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
lean_object* v___x_17_; 
if (v_isShared_15_ == 0)
{
lean_ctor_set_tag(v___x_14_, 0);
v___x_17_ = v___x_14_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v_a_12_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_loadWorkspaceRoot_spec__0___redArg___boxed(lean_object* v_e_20_, lean_object* v_a_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_IO_ofExcept___at___00Lake_loadWorkspaceRoot_spec__0___redArg(v_e_20_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_loadWorkspaceRoot_spec__0(lean_object* v_00_u03b1_23_, lean_object* v_e_24_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_IO_ofExcept___at___00Lake_loadWorkspaceRoot_spec__0___redArg(v_e_24_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_loadWorkspaceRoot_spec__0___boxed(lean_object* v_00_u03b1_27_, lean_object* v_e_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_IO_ofExcept___at___00Lake_loadWorkspaceRoot_spec__0(v_00_u03b1_27_, v_e_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspaceRoot(lean_object* v_config_35_, lean_object* v_a_36_){
_start:
{
lean_object* v_lakeEnv_38_; lean_object* v_lakeArgs_x3f_39_; lean_object* v_wsDir_40_; lean_object* v_pkgName_41_; lean_object* v_relPkgDir_42_; lean_object* v_pkgDir_43_; lean_object* v_relConfigFile_44_; lean_object* v_configFile_45_; lean_object* v_packageOverrides_46_; lean_object* v_lakeOpts_47_; lean_object* v_leanOpts_48_; uint8_t v_reconfigure_49_; uint8_t v_updateDeps_50_; uint8_t v_updateToolchain_51_; lean_object* v_scope_52_; lean_object* v_remoteUrl_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_136_; 
v_lakeEnv_38_ = lean_ctor_get(v_config_35_, 0);
v_lakeArgs_x3f_39_ = lean_ctor_get(v_config_35_, 1);
v_wsDir_40_ = lean_ctor_get(v_config_35_, 2);
v_pkgName_41_ = lean_ctor_get(v_config_35_, 4);
v_relPkgDir_42_ = lean_ctor_get(v_config_35_, 5);
v_pkgDir_43_ = lean_ctor_get(v_config_35_, 6);
v_relConfigFile_44_ = lean_ctor_get(v_config_35_, 7);
v_configFile_45_ = lean_ctor_get(v_config_35_, 8);
v_packageOverrides_46_ = lean_ctor_get(v_config_35_, 9);
v_lakeOpts_47_ = lean_ctor_get(v_config_35_, 10);
v_leanOpts_48_ = lean_ctor_get(v_config_35_, 11);
v_reconfigure_49_ = lean_ctor_get_uint8(v_config_35_, sizeof(void*)*14);
v_updateDeps_50_ = lean_ctor_get_uint8(v_config_35_, sizeof(void*)*14 + 1);
v_updateToolchain_51_ = lean_ctor_get_uint8(v_config_35_, sizeof(void*)*14 + 2);
v_scope_52_ = lean_ctor_get(v_config_35_, 12);
v_remoteUrl_53_ = lean_ctor_get(v_config_35_, 13);
v_isSharedCheck_136_ = !lean_is_exclusive(v_config_35_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; 
v_unused_137_ = lean_ctor_get(v_config_35_, 3);
lean_dec(v_unused_137_);
v___x_55_ = v_config_35_;
v_isShared_56_ = v_isSharedCheck_136_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_remoteUrl_53_);
lean_inc(v_scope_52_);
lean_inc(v_leanOpts_48_);
lean_inc(v_lakeOpts_47_);
lean_inc(v_packageOverrides_46_);
lean_inc(v_configFile_45_);
lean_inc(v_relConfigFile_44_);
lean_inc(v_pkgDir_43_);
lean_inc(v_relPkgDir_42_);
lean_inc(v_pkgName_41_);
lean_inc(v_wsDir_40_);
lean_inc(v_lakeArgs_x3f_39_);
lean_inc(v_lakeEnv_38_);
lean_dec(v_config_35_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_136_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_57_ = l_Lean_searchPathRef;
v___x_58_ = l_Lake_Env_leanSearchPath(v_lakeEnv_38_);
v___x_59_ = lean_st_ref_set(v___x_57_, v___x_58_);
lean_inc_ref(v_lakeEnv_38_);
v___x_60_ = l_Lake_loadLakeConfig(v_lakeEnv_38_, v_a_36_);
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v_a_61_; lean_object* v_a_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_66_; 
v_a_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc(v_a_61_);
v_a_62_ = lean_ctor_get(v___x_60_, 1);
lean_inc(v_a_62_);
lean_dec_ref(v___x_60_);
v___x_63_ = ((lean_object*)(l_Lake_loadWorkspaceRoot___closed__0));
v___x_64_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_leanOpts_48_);
lean_inc(v_lakeArgs_x3f_39_);
lean_inc_ref(v_lakeEnv_38_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 3, v___x_64_);
v___x_66_ = v___x_55_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 14, 3);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_lakeEnv_38_);
lean_ctor_set(v_reuseFailAlloc_126_, 1, v_lakeArgs_x3f_39_);
lean_ctor_set(v_reuseFailAlloc_126_, 2, v_wsDir_40_);
lean_ctor_set(v_reuseFailAlloc_126_, 3, v___x_64_);
lean_ctor_set(v_reuseFailAlloc_126_, 4, v_pkgName_41_);
lean_ctor_set(v_reuseFailAlloc_126_, 5, v_relPkgDir_42_);
lean_ctor_set(v_reuseFailAlloc_126_, 6, v_pkgDir_43_);
lean_ctor_set(v_reuseFailAlloc_126_, 7, v_relConfigFile_44_);
lean_ctor_set(v_reuseFailAlloc_126_, 8, v_configFile_45_);
lean_ctor_set(v_reuseFailAlloc_126_, 9, v_packageOverrides_46_);
lean_ctor_set(v_reuseFailAlloc_126_, 10, v_lakeOpts_47_);
lean_ctor_set(v_reuseFailAlloc_126_, 11, v_leanOpts_48_);
lean_ctor_set(v_reuseFailAlloc_126_, 12, v_scope_52_);
lean_ctor_set(v_reuseFailAlloc_126_, 13, v_remoteUrl_53_);
lean_ctor_set_uint8(v_reuseFailAlloc_126_, sizeof(void*)*14, v_reconfigure_49_);
lean_ctor_set_uint8(v_reuseFailAlloc_126_, sizeof(void*)*14 + 1, v_updateDeps_50_);
lean_ctor_set_uint8(v_reuseFailAlloc_126_, sizeof(void*)*14 + 2, v_updateToolchain_51_);
v___x_66_ = v_reuseFailAlloc_126_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lake_loadPackageCore(v___x_63_, v___x_66_, v_a_62_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v_a_68_; lean_object* v_a_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_116_; 
v_a_68_ = lean_ctor_get(v___x_67_, 0);
v_a_69_ = lean_ctor_get(v___x_67_, 1);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_116_ == 0)
{
v___x_71_ = v___x_67_;
v_isShared_72_ = v_isSharedCheck_116_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_a_69_);
lean_inc(v_a_68_);
lean_dec(v___x_67_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_116_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v_fst_73_; lean_object* v_snd_74_; lean_object* v___y_76_; lean_object* v_config_100_; uint8_t v_bootstrap_101_; 
v_fst_73_ = lean_ctor_get(v_a_68_, 0);
lean_inc(v_fst_73_);
v_snd_74_ = lean_ctor_get(v_a_68_, 1);
lean_inc(v_snd_74_);
lean_dec(v_a_68_);
v_config_100_ = lean_ctor_get(v_fst_73_, 6);
v_bootstrap_101_ = lean_ctor_get_uint8(v_config_100_, sizeof(void*)*26);
if (v_bootstrap_101_ == 0)
{
lean_object* v_lakeCache_x3f_102_; 
v_lakeCache_x3f_102_ = lean_ctor_get(v_lakeEnv_38_, 7);
if (lean_obj_tag(v_lakeCache_x3f_102_) == 0)
{
lean_object* v_dir_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v_dir_103_ = lean_ctor_get(v_fst_73_, 4);
v___x_104_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_103_);
v___x_105_ = l_Lake_joinRelative(v_dir_103_, v___x_104_);
v___x_106_ = ((lean_object*)(l_Lake_loadWorkspaceRoot___closed__2));
v___x_107_ = l_Lake_joinRelative(v___x_105_, v___x_106_);
v___y_76_ = v___x_107_;
goto v___jp_75_;
}
else
{
lean_object* v_val_108_; 
v_val_108_ = lean_ctor_get(v_lakeCache_x3f_102_, 0);
lean_inc(v_val_108_);
v___y_76_ = v_val_108_;
goto v___jp_75_;
}
}
else
{
lean_object* v_lakeSystemCache_x3f_109_; 
v_lakeSystemCache_x3f_109_ = lean_ctor_get(v_lakeEnv_38_, 8);
if (lean_obj_tag(v_lakeSystemCache_x3f_109_) == 0)
{
lean_object* v_dir_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v_dir_110_ = lean_ctor_get(v_fst_73_, 4);
v___x_111_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_110_);
v___x_112_ = l_Lake_joinRelative(v_dir_110_, v___x_111_);
v___x_113_ = ((lean_object*)(l_Lake_loadWorkspaceRoot___closed__2));
v___x_114_ = l_Lake_joinRelative(v___x_112_, v___x_113_);
v___y_76_ = v___x_114_;
goto v___jp_75_;
}
else
{
lean_object* v_val_115_; 
v_val_115_ = lean_ctor_get(v_lakeSystemCache_x3f_109_, 0);
lean_inc(v_val_115_);
v___y_76_ = v_val_115_;
goto v___jp_75_;
}
}
v___jp_75_:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_77_ = ((lean_object*)(l_Lake_loadWorkspaceRoot___closed__1));
v___x_78_ = lean_box(1);
v___x_79_ = l_Lake_initFacetConfigs;
v___x_80_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_80_, 0, v_fst_73_);
lean_ctor_set(v___x_80_, 1, v_lakeEnv_38_);
lean_ctor_set(v___x_80_, 2, v_a_61_);
lean_ctor_set(v___x_80_, 3, v___y_76_);
lean_ctor_set(v___x_80_, 4, v_lakeArgs_x3f_39_);
lean_ctor_set(v___x_80_, 5, v___x_77_);
lean_ctor_set(v___x_80_, 6, v___x_78_);
lean_ctor_set(v___x_80_, 7, v___x_79_);
if (lean_obj_tag(v_snd_74_) == 1)
{
lean_object* v_val_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v_val_81_ = lean_ctor_get(v_snd_74_, 0);
lean_inc(v_val_81_);
lean_dec_ref(v_snd_74_);
v___x_82_ = l_Lake_Workspace_addFacetsFromEnv(v_val_81_, v_leanOpts_48_, v___x_80_);
lean_dec_ref(v_leanOpts_48_);
v___x_83_ = l_IO_ofExcept___at___00Lake_loadWorkspaceRoot_spec__0___redArg(v___x_82_);
if (lean_obj_tag(v___x_83_) == 0)
{
lean_object* v_a_84_; lean_object* v___x_86_; 
v_a_84_ = lean_ctor_get(v___x_83_, 0);
lean_inc(v_a_84_);
lean_dec_ref(v___x_83_);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 0, v_a_84_);
v___x_86_ = v___x_71_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_a_84_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v_a_69_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
else
{
lean_object* v_a_88_; lean_object* v___x_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_95_; 
v_a_88_ = lean_ctor_get(v___x_83_, 0);
lean_inc(v_a_88_);
lean_dec_ref(v___x_83_);
v___x_89_ = lean_io_error_to_string(v_a_88_);
v___x_90_ = 3;
v___x_91_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set_uint8(v___x_91_, sizeof(void*)*1, v___x_90_);
v___x_92_ = lean_array_get_size(v_a_69_);
v___x_93_ = lean_array_push(v_a_69_, v___x_91_);
if (v_isShared_72_ == 0)
{
lean_ctor_set_tag(v___x_71_, 1);
lean_ctor_set(v___x_71_, 1, v___x_93_);
lean_ctor_set(v___x_71_, 0, v___x_92_);
v___x_95_ = v___x_71_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_92_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v___x_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
else
{
lean_object* v___x_98_; 
lean_dec(v_snd_74_);
lean_dec_ref(v_leanOpts_48_);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 0, v___x_80_);
v___x_98_ = v___x_71_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_80_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v_a_69_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
}
else
{
lean_object* v_a_117_; lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_125_; 
lean_dec(v_a_61_);
lean_dec_ref(v_leanOpts_48_);
lean_dec(v_lakeArgs_x3f_39_);
lean_dec_ref(v_lakeEnv_38_);
v_a_117_ = lean_ctor_get(v___x_67_, 0);
v_a_118_ = lean_ctor_get(v___x_67_, 1);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_125_ == 0)
{
v___x_120_ = v___x_67_;
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_inc(v_a_117_);
lean_dec(v___x_67_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
if (v_isShared_121_ == 0)
{
v___x_123_ = v___x_120_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_a_117_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v_a_118_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
}
else
{
lean_object* v_a_127_; lean_object* v_a_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_135_; 
lean_del_object(v___x_55_);
lean_dec_ref(v_remoteUrl_53_);
lean_dec_ref(v_scope_52_);
lean_dec_ref(v_leanOpts_48_);
lean_dec(v_lakeOpts_47_);
lean_dec_ref(v_packageOverrides_46_);
lean_dec_ref(v_configFile_45_);
lean_dec_ref(v_relConfigFile_44_);
lean_dec_ref(v_pkgDir_43_);
lean_dec_ref(v_relPkgDir_42_);
lean_dec(v_pkgName_41_);
lean_dec_ref(v_wsDir_40_);
lean_dec(v_lakeArgs_x3f_39_);
lean_dec_ref(v_lakeEnv_38_);
v_a_127_ = lean_ctor_get(v___x_60_, 0);
v_a_128_ = lean_ctor_get(v___x_60_, 1);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_135_ == 0)
{
v___x_130_ = v___x_60_;
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_a_128_);
lean_inc(v_a_127_);
lean_dec(v___x_60_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_133_; 
if (v_isShared_131_ == 0)
{
v___x_133_ = v___x_130_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_a_127_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_a_128_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspaceRoot___boxed(lean_object* v_config_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lake_loadWorkspaceRoot(v_config_138_, v_a_139_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___redArg(lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = lean_apply_2(v___y_143_, v___y_142_, lean_box(0));
v___x_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___redArg___boxed(lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lake_loadWorkspace___elam__0___redArg(v___y_147_, v___y_148_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0(lean_object* v_x_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lake_loadWorkspace___elam__0___redArg(v___y_152_, v___y_153_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___boxed(lean_object* v_x_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lake_loadWorkspace___elam__0(v_x_156_, v___y_157_, v___y_158_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1___redArg(lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_apply_2(v___y_161_, v___y_162_, lean_box(0));
v___x_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1___redArg___boxed(lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1___redArg(v___y_166_, v___y_167_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(lean_object* v_as_170_, size_t v_i_171_, size_t v_stop_172_, lean_object* v_b_173_, lean_object* v___y_174_){
_start:
{
uint8_t v___x_176_; 
v___x_176_ = lean_usize_dec_eq(v_i_171_, v_stop_172_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = lean_array_uget_borrowed(v_as_170_, v_i_171_);
lean_inc(v___x_177_);
lean_inc_ref(v___y_174_);
v___x_178_ = l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1___redArg(v___y_174_, v___x_177_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; size_t v___x_180_; size_t v___x_181_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_179_);
lean_dec_ref(v___x_178_);
v___x_180_ = ((size_t)1ULL);
v___x_181_ = lean_usize_add(v_i_171_, v___x_180_);
v_i_171_ = v___x_181_;
v_b_173_ = v_a_179_;
goto _start;
}
else
{
lean_dec_ref(v___y_174_);
return v___x_178_;
}
}
else
{
lean_object* v___x_183_; 
lean_dec_ref(v___y_174_);
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v_b_173_);
return v___x_183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1___boxed(lean_object* v_as_184_, lean_object* v_i_185_, lean_object* v_stop_186_, lean_object* v_b_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
size_t v_i_boxed_190_; size_t v_stop_boxed_191_; lean_object* v_res_192_; 
v_i_boxed_190_ = lean_unbox_usize(v_i_185_);
lean_dec(v_i_185_);
v_stop_boxed_191_ = lean_unbox_usize(v_stop_186_);
lean_dec(v_stop_186_);
v_res_192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(v_as_184_, v_i_boxed_190_, v_stop_boxed_191_, v_b_187_, v___y_188_);
lean_dec_ref(v_as_184_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace(lean_object* v_config_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_packageOverrides_201_; lean_object* v_leanOpts_202_; uint8_t v_reconfigure_203_; uint8_t v_updateDeps_204_; uint8_t v_updateToolchain_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v_packageOverrides_201_ = lean_ctor_get(v_config_195_, 9);
lean_inc_ref(v_packageOverrides_201_);
v_leanOpts_202_ = lean_ctor_get(v_config_195_, 11);
lean_inc_ref(v_leanOpts_202_);
v_reconfigure_203_ = lean_ctor_get_uint8(v_config_195_, sizeof(void*)*14);
v_updateDeps_204_ = lean_ctor_get_uint8(v_config_195_, sizeof(void*)*14 + 1);
v_updateToolchain_205_ = lean_ctor_get_uint8(v_config_195_, sizeof(void*)*14 + 2);
v___x_206_ = lean_unsigned_to_nat(0u);
v___x_207_ = ((lean_object*)(l_Lake_loadWorkspace___closed__0));
v___x_208_ = l_Lake_loadWorkspaceRoot(v_config_195_, v___x_207_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; lean_object* v_a_210_; lean_object* v___x_237_; uint8_t v___x_238_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_a_209_);
v_a_210_ = lean_ctor_get(v___x_208_, 1);
lean_inc(v_a_210_);
lean_dec_ref(v___x_208_);
v___x_237_ = lean_array_get_size(v_a_210_);
v___x_238_ = lean_nat_dec_lt(v___x_206_, v___x_237_);
if (v___x_238_ == 0)
{
lean_dec(v_a_210_);
goto v___jp_211_;
}
else
{
lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_239_ = lean_box(0);
v___x_240_ = lean_nat_dec_le(v___x_237_, v___x_237_);
if (v___x_240_ == 0)
{
if (v___x_238_ == 0)
{
lean_dec(v_a_210_);
goto v___jp_211_;
}
else
{
size_t v___x_241_; size_t v___x_242_; lean_object* v___x_243_; 
v___x_241_ = ((size_t)0ULL);
v___x_242_ = lean_usize_of_nat(v___x_237_);
lean_inc_ref(v_a_196_);
v___x_243_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(v_a_210_, v___x_241_, v___x_242_, v___x_239_, v_a_196_);
lean_dec(v_a_210_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_dec_ref(v___x_243_);
goto v___jp_211_;
}
else
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
lean_dec(v_a_209_);
lean_dec_ref(v_leanOpts_202_);
lean_dec_ref(v_packageOverrides_201_);
lean_dec_ref(v_a_196_);
v_a_244_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_243_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_243_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
}
else
{
size_t v___x_252_; size_t v___x_253_; lean_object* v___x_254_; 
v___x_252_ = ((size_t)0ULL);
v___x_253_ = lean_usize_of_nat(v___x_237_);
lean_inc_ref(v_a_196_);
v___x_254_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(v_a_210_, v___x_252_, v___x_253_, v___x_239_, v_a_196_);
lean_dec(v_a_210_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_dec_ref(v___x_254_);
goto v___jp_211_;
}
else
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
lean_dec(v_a_209_);
lean_dec_ref(v_leanOpts_202_);
lean_dec_ref(v_packageOverrides_201_);
lean_dec_ref(v_a_196_);
v_a_255_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_254_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_254_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
}
v___jp_211_:
{
if (v_updateDeps_204_ == 0)
{
lean_object* v_root_212_; lean_object* v_dir_213_; lean_object* v_relManifestFile_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v_root_212_ = lean_ctor_get(v_a_209_, 0);
v_dir_213_ = lean_ctor_get(v_root_212_, 4);
v_relManifestFile_214_ = lean_ctor_get(v_root_212_, 9);
lean_inc_ref(v_relManifestFile_214_);
lean_inc_ref(v_dir_213_);
v___x_215_ = l_Lake_joinRelative(v_dir_213_, v_relManifestFile_214_);
v___x_216_ = l_Lake_Manifest_load_x3f(v___x_215_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_a_217_);
lean_dec_ref(v___x_216_);
if (lean_obj_tag(v_a_217_) == 1)
{
lean_object* v_val_218_; lean_object* v___x_219_; 
v_val_218_ = lean_ctor_get(v_a_217_, 0);
lean_inc(v_val_218_);
lean_dec_ref(v_a_217_);
v___x_219_ = l_Lake_Workspace_materializeDeps(v_a_209_, v_val_218_, v_leanOpts_202_, v_reconfigure_203_, v_packageOverrides_201_, v_a_196_);
lean_dec_ref(v_packageOverrides_201_);
return v___x_219_;
}
else
{
lean_object* v___x_220_; lean_object* v___x_221_; 
lean_dec(v_a_217_);
lean_dec_ref(v_packageOverrides_201_);
v___x_220_ = l_Lean_NameSet_empty;
v___x_221_ = l_Lake_Workspace_updateAndMaterialize(v_a_209_, v___x_220_, v_leanOpts_202_, v_updateToolchain_205_, v_a_196_);
return v___x_221_;
}
}
else
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_234_; 
lean_dec(v_a_209_);
lean_dec_ref(v_leanOpts_202_);
lean_dec_ref(v_packageOverrides_201_);
v_a_222_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_234_ == 0)
{
v___x_224_ = v___x_216_;
v_isShared_225_ = v_isSharedCheck_234_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_216_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_234_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; uint8_t v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_226_ = lean_io_error_to_string(v_a_222_);
v___x_227_ = 3;
v___x_228_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_228_, 0, v___x_226_);
lean_ctor_set_uint8(v___x_228_, sizeof(void*)*1, v___x_227_);
v___x_229_ = lean_apply_2(v_a_196_, v___x_228_, lean_box(0));
v___x_230_ = lean_box(0);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_230_);
v___x_232_ = v___x_224_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_230_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
else
{
lean_object* v___x_235_; lean_object* v___x_236_; 
lean_dec_ref(v_packageOverrides_201_);
v___x_235_ = l_Lean_NameSet_empty;
v___x_236_ = l_Lake_Workspace_updateAndMaterialize(v_a_209_, v___x_235_, v_leanOpts_202_, v_updateToolchain_205_, v_a_196_);
return v___x_236_;
}
}
}
else
{
lean_object* v_a_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
lean_dec_ref(v_leanOpts_202_);
lean_dec_ref(v_packageOverrides_201_);
v_a_263_ = lean_ctor_get(v___x_208_, 1);
lean_inc(v_a_263_);
lean_dec_ref(v___x_208_);
v___x_264_ = lean_array_get_size(v_a_263_);
v___x_265_ = lean_nat_dec_lt(v___x_206_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_267_; 
lean_dec(v_a_263_);
lean_dec_ref(v_a_196_);
v___x_266_ = lean_box(0);
v___x_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
return v___x_267_;
}
else
{
lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_268_ = lean_box(0);
v___x_269_ = lean_nat_dec_le(v___x_264_, v___x_264_);
if (v___x_269_ == 0)
{
if (v___x_265_ == 0)
{
lean_dec(v_a_263_);
lean_dec_ref(v_a_196_);
goto v___jp_198_;
}
else
{
size_t v___x_270_; size_t v___x_271_; lean_object* v___x_272_; 
v___x_270_ = ((size_t)0ULL);
v___x_271_ = lean_usize_of_nat(v___x_264_);
v___x_272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(v_a_263_, v___x_270_, v___x_271_, v___x_268_, v_a_196_);
lean_dec(v_a_263_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_dec_ref(v___x_272_);
goto v___jp_198_;
}
else
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
v_a_273_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_272_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_272_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_a_273_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
}
else
{
size_t v___x_281_; size_t v___x_282_; lean_object* v___x_283_; 
v___x_281_ = ((size_t)0ULL);
v___x_282_ = lean_usize_of_nat(v___x_264_);
v___x_283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(v_a_263_, v___x_281_, v___x_282_, v___x_268_, v_a_196_);
lean_dec(v_a_263_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_dec_ref(v___x_283_);
goto v___jp_198_;
}
else
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v___x_283_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_283_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
}
}
v___jp_198_:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_box(0);
v___x_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
return v___x_200_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___boxed(lean_object* v_config_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lake_loadWorkspace(v_config_292_, v_a_293_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1(lean_object* v___y_296_, lean_object* v_x_297_, lean_object* v___y_298_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1___redArg(v___y_296_, v___y_298_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1___boxed(lean_object* v___y_301_, lean_object* v_x_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1(v___y_301_, v_x_302_, v___y_303_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lake_updateManifest(lean_object* v_config_306_, lean_object* v_toUpdate_307_, lean_object* v_a_308_){
_start:
{
lean_object* v_leanOpts_313_; uint8_t v_updateToolchain_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v_leanOpts_313_ = lean_ctor_get(v_config_306_, 11);
lean_inc_ref(v_leanOpts_313_);
v_updateToolchain_314_ = lean_ctor_get_uint8(v_config_306_, sizeof(void*)*14 + 2);
v___x_315_ = lean_unsigned_to_nat(0u);
v___x_316_ = ((lean_object*)(l_Lake_loadWorkspace___closed__0));
v___x_317_ = l_Lake_loadWorkspaceRoot(v_config_306_, v___x_316_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v_a_318_; lean_object* v_a_319_; lean_object* v___x_339_; uint8_t v___x_340_; 
v_a_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_a_318_);
v_a_319_ = lean_ctor_get(v___x_317_, 1);
lean_inc(v_a_319_);
lean_dec_ref(v___x_317_);
v___x_339_ = lean_array_get_size(v_a_319_);
v___x_340_ = lean_nat_dec_lt(v___x_315_, v___x_339_);
if (v___x_340_ == 0)
{
lean_dec(v_a_319_);
goto v___jp_320_;
}
else
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = lean_box(0);
v___x_342_ = lean_nat_dec_le(v___x_339_, v___x_339_);
if (v___x_342_ == 0)
{
if (v___x_340_ == 0)
{
lean_dec(v_a_319_);
goto v___jp_320_;
}
else
{
size_t v___x_343_; size_t v___x_344_; lean_object* v___x_345_; 
v___x_343_ = ((size_t)0ULL);
v___x_344_ = lean_usize_of_nat(v___x_339_);
lean_inc_ref(v_a_308_);
v___x_345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(v_a_319_, v___x_343_, v___x_344_, v___x_341_, v_a_308_);
lean_dec(v_a_319_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_dec_ref(v___x_345_);
goto v___jp_320_;
}
else
{
lean_dec(v_a_318_);
lean_dec_ref(v_leanOpts_313_);
lean_dec_ref(v_a_308_);
return v___x_345_;
}
}
}
else
{
size_t v___x_346_; size_t v___x_347_; lean_object* v___x_348_; 
v___x_346_ = ((size_t)0ULL);
v___x_347_ = lean_usize_of_nat(v___x_339_);
lean_inc_ref(v_a_308_);
v___x_348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(v_a_319_, v___x_346_, v___x_347_, v___x_341_, v_a_308_);
lean_dec(v_a_319_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_dec_ref(v___x_348_);
goto v___jp_320_;
}
else
{
lean_dec(v_a_318_);
lean_dec_ref(v_leanOpts_313_);
lean_dec_ref(v_a_308_);
return v___x_348_;
}
}
}
v___jp_320_:
{
lean_object* v___x_321_; 
v___x_321_ = l_Lake_Workspace_updateAndMaterialize(v_a_318_, v_toUpdate_307_, v_leanOpts_313_, v_updateToolchain_314_, v_a_308_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_329_; 
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_329_ == 0)
{
lean_object* v_unused_330_; 
v_unused_330_ = lean_ctor_get(v___x_321_, 0);
lean_dec(v_unused_330_);
v___x_323_ = v___x_321_;
v_isShared_324_ = v_isSharedCheck_329_;
goto v_resetjp_322_;
}
else
{
lean_dec(v___x_321_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_329_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_325_ = lean_box(0);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___x_325_);
v___x_327_ = v___x_323_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
else
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_338_; 
v_a_331_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_338_ == 0)
{
v___x_333_ = v___x_321_;
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_321_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_331_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
}
else
{
lean_object* v_a_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
lean_dec_ref(v_leanOpts_313_);
v_a_349_ = lean_ctor_get(v___x_317_, 1);
lean_inc(v_a_349_);
lean_dec_ref(v___x_317_);
v___x_350_ = lean_array_get_size(v_a_349_);
v___x_351_ = lean_nat_dec_lt(v___x_315_, v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; lean_object* v___x_353_; 
lean_dec(v_a_349_);
lean_dec_ref(v_a_308_);
v___x_352_ = lean_box(0);
v___x_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
return v___x_353_;
}
else
{
lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_354_ = lean_box(0);
v___x_355_ = lean_nat_dec_le(v___x_350_, v___x_350_);
if (v___x_355_ == 0)
{
if (v___x_351_ == 0)
{
lean_dec(v_a_349_);
lean_dec_ref(v_a_308_);
goto v___jp_310_;
}
else
{
size_t v___x_356_; size_t v___x_357_; lean_object* v___x_358_; 
v___x_356_ = ((size_t)0ULL);
v___x_357_ = lean_usize_of_nat(v___x_350_);
v___x_358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(v_a_349_, v___x_356_, v___x_357_, v___x_354_, v_a_308_);
lean_dec(v_a_349_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_dec_ref(v___x_358_);
goto v___jp_310_;
}
else
{
return v___x_358_;
}
}
}
else
{
size_t v___x_359_; size_t v___x_360_; lean_object* v___x_361_; 
v___x_359_ = ((size_t)0ULL);
v___x_360_ = lean_usize_of_nat(v___x_350_);
v___x_361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(v_a_349_, v___x_359_, v___x_360_, v___x_354_, v_a_308_);
lean_dec(v_a_349_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_dec_ref(v___x_361_);
goto v___jp_310_;
}
else
{
return v___x_361_;
}
}
}
}
v___jp_310_:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = lean_box(0);
v___x_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
return v___x_312_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateManifest___boxed(lean_object* v_config_362_, lean_object* v_toUpdate_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lake_updateManifest(v_config_362_, v_toUpdate_363_, v_a_364_);
lean_dec(v_toUpdate_363_);
return v_res_366_;
}
}
lean_object* runtime_initialize_Lake_Load_Config(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Workspace(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Resolve(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Package(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Lean_Eval(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Toml(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_InitFacets(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Load_Workspace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
