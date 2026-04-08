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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_searchPathRef;
lean_object* l_Lake_Env_leanSearchPath(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lake_loadLakeConfig(lean_object*, lean_object*);
lean_object* l_Lake_loadPackageCore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_computeLakeCache(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lake_initFacetConfigs;
lean_object* l_Lake_Workspace_addFacetsFromEnv(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_loadWorkspaceRoot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspaceRoot___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_loadWorkspace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_loadWorkspace___closed__0 = (const lean_object*)&l_Lake_loadWorkspace___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_loadWorkspace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_loadWorkspaceRoot(lean_object* v_config_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_lakeEnv_37_; lean_object* v_lakeArgs_x3f_38_; lean_object* v_wsDir_39_; lean_object* v_pkgName_40_; lean_object* v_relPkgDir_41_; lean_object* v_pkgDir_42_; lean_object* v_relConfigFile_43_; lean_object* v_configFile_44_; lean_object* v_packageOverrides_45_; lean_object* v_lakeOpts_46_; lean_object* v_leanOpts_47_; uint8_t v_reconfigure_48_; uint8_t v_updateDeps_49_; uint8_t v_updateToolchain_50_; lean_object* v_scope_51_; lean_object* v_remoteUrl_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_118_; 
v_lakeEnv_37_ = lean_ctor_get(v_config_34_, 0);
v_lakeArgs_x3f_38_ = lean_ctor_get(v_config_34_, 1);
v_wsDir_39_ = lean_ctor_get(v_config_34_, 2);
v_pkgName_40_ = lean_ctor_get(v_config_34_, 4);
v_relPkgDir_41_ = lean_ctor_get(v_config_34_, 5);
v_pkgDir_42_ = lean_ctor_get(v_config_34_, 6);
v_relConfigFile_43_ = lean_ctor_get(v_config_34_, 7);
v_configFile_44_ = lean_ctor_get(v_config_34_, 8);
v_packageOverrides_45_ = lean_ctor_get(v_config_34_, 9);
v_lakeOpts_46_ = lean_ctor_get(v_config_34_, 10);
v_leanOpts_47_ = lean_ctor_get(v_config_34_, 11);
v_reconfigure_48_ = lean_ctor_get_uint8(v_config_34_, sizeof(void*)*14);
v_updateDeps_49_ = lean_ctor_get_uint8(v_config_34_, sizeof(void*)*14 + 1);
v_updateToolchain_50_ = lean_ctor_get_uint8(v_config_34_, sizeof(void*)*14 + 2);
v_scope_51_ = lean_ctor_get(v_config_34_, 12);
v_remoteUrl_52_ = lean_ctor_get(v_config_34_, 13);
v_isSharedCheck_118_ = !lean_is_exclusive(v_config_34_);
if (v_isSharedCheck_118_ == 0)
{
lean_object* v_unused_119_; 
v_unused_119_ = lean_ctor_get(v_config_34_, 3);
lean_dec(v_unused_119_);
v___x_54_ = v_config_34_;
v_isShared_55_ = v_isSharedCheck_118_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_remoteUrl_52_);
lean_inc(v_scope_51_);
lean_inc(v_leanOpts_47_);
lean_inc(v_lakeOpts_46_);
lean_inc(v_packageOverrides_45_);
lean_inc(v_configFile_44_);
lean_inc(v_relConfigFile_43_);
lean_inc(v_pkgDir_42_);
lean_inc(v_relPkgDir_41_);
lean_inc(v_pkgName_40_);
lean_inc(v_wsDir_39_);
lean_inc(v_lakeArgs_x3f_38_);
lean_inc(v_lakeEnv_37_);
lean_dec(v_config_34_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_118_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = l_Lean_searchPathRef;
v___x_57_ = l_Lake_Env_leanSearchPath(v_lakeEnv_37_);
v___x_58_ = lean_st_ref_set(v___x_56_, v___x_57_);
lean_inc_ref(v_lakeEnv_37_);
v___x_59_ = l_Lake_loadLakeConfig(v_lakeEnv_37_, v_a_35_);
if (lean_obj_tag(v___x_59_) == 0)
{
lean_object* v_a_60_; lean_object* v_a_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_65_; 
v_a_60_ = lean_ctor_get(v___x_59_, 0);
lean_inc(v_a_60_);
v_a_61_ = lean_ctor_get(v___x_59_, 1);
lean_inc(v_a_61_);
lean_dec_ref(v___x_59_);
v___x_62_ = ((lean_object*)(l_Lake_loadWorkspaceRoot___closed__0));
v___x_63_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_leanOpts_47_);
lean_inc(v_lakeArgs_x3f_38_);
lean_inc_ref(v_lakeEnv_37_);
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 3, v___x_63_);
v___x_65_ = v___x_54_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 14, 3);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_lakeEnv_37_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v_lakeArgs_x3f_38_);
lean_ctor_set(v_reuseFailAlloc_108_, 2, v_wsDir_39_);
lean_ctor_set(v_reuseFailAlloc_108_, 3, v___x_63_);
lean_ctor_set(v_reuseFailAlloc_108_, 4, v_pkgName_40_);
lean_ctor_set(v_reuseFailAlloc_108_, 5, v_relPkgDir_41_);
lean_ctor_set(v_reuseFailAlloc_108_, 6, v_pkgDir_42_);
lean_ctor_set(v_reuseFailAlloc_108_, 7, v_relConfigFile_43_);
lean_ctor_set(v_reuseFailAlloc_108_, 8, v_configFile_44_);
lean_ctor_set(v_reuseFailAlloc_108_, 9, v_packageOverrides_45_);
lean_ctor_set(v_reuseFailAlloc_108_, 10, v_lakeOpts_46_);
lean_ctor_set(v_reuseFailAlloc_108_, 11, v_leanOpts_47_);
lean_ctor_set(v_reuseFailAlloc_108_, 12, v_scope_51_);
lean_ctor_set(v_reuseFailAlloc_108_, 13, v_remoteUrl_52_);
lean_ctor_set_uint8(v_reuseFailAlloc_108_, sizeof(void*)*14, v_reconfigure_48_);
lean_ctor_set_uint8(v_reuseFailAlloc_108_, sizeof(void*)*14 + 1, v_updateDeps_49_);
lean_ctor_set_uint8(v_reuseFailAlloc_108_, sizeof(void*)*14 + 2, v_updateToolchain_50_);
v___x_65_ = v_reuseFailAlloc_108_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lake_loadPackageCore(v___x_62_, v___x_65_, v_a_61_);
if (lean_obj_tag(v___x_66_) == 0)
{
lean_object* v_a_67_; lean_object* v_a_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_98_; 
v_a_67_ = lean_ctor_get(v___x_66_, 0);
v_a_68_ = lean_ctor_get(v___x_66_, 1);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_98_ == 0)
{
v___x_70_ = v___x_66_;
v_isShared_71_ = v_isSharedCheck_98_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_a_68_);
lean_inc(v_a_67_);
lean_dec(v___x_66_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_98_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v_fst_72_; lean_object* v_snd_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v_fst_72_ = lean_ctor_get(v_a_67_, 0);
lean_inc_n(v_fst_72_, 2);
v_snd_73_ = lean_ctor_get(v_a_67_, 1);
lean_inc(v_snd_73_);
lean_dec(v_a_67_);
v___x_74_ = l_Lake_computeLakeCache(v_fst_72_, v_lakeEnv_37_);
v___x_75_ = ((lean_object*)(l_Lake_loadWorkspaceRoot___closed__1));
v___x_76_ = lean_box(1);
v___x_77_ = l_Lake_initFacetConfigs;
v___x_78_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_78_, 0, v_fst_72_);
lean_ctor_set(v___x_78_, 1, v_lakeEnv_37_);
lean_ctor_set(v___x_78_, 2, v_a_60_);
lean_ctor_set(v___x_78_, 3, v___x_74_);
lean_ctor_set(v___x_78_, 4, v_lakeArgs_x3f_38_);
lean_ctor_set(v___x_78_, 5, v___x_75_);
lean_ctor_set(v___x_78_, 6, v___x_76_);
lean_ctor_set(v___x_78_, 7, v___x_77_);
if (lean_obj_tag(v_snd_73_) == 1)
{
lean_object* v_val_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v_val_79_ = lean_ctor_get(v_snd_73_, 0);
lean_inc(v_val_79_);
lean_dec_ref(v_snd_73_);
v___x_80_ = l_Lake_Workspace_addFacetsFromEnv(v_val_79_, v_leanOpts_47_, v___x_78_);
lean_dec_ref(v_leanOpts_47_);
v___x_81_ = l_IO_ofExcept___at___00Lake_loadWorkspaceRoot_spec__0___redArg(v___x_80_);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_object* v_a_82_; lean_object* v___x_84_; 
v_a_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc(v_a_82_);
lean_dec_ref(v___x_81_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 0, v_a_82_);
v___x_84_ = v___x_70_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_a_82_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v_a_68_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
else
{
lean_object* v_a_86_; lean_object* v___x_87_; uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_93_; 
v_a_86_ = lean_ctor_get(v___x_81_, 0);
lean_inc(v_a_86_);
lean_dec_ref(v___x_81_);
v___x_87_ = lean_io_error_to_string(v_a_86_);
v___x_88_ = 3;
v___x_89_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_89_, 0, v___x_87_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*1, v___x_88_);
v___x_90_ = lean_array_get_size(v_a_68_);
v___x_91_ = lean_array_push(v_a_68_, v___x_89_);
if (v_isShared_71_ == 0)
{
lean_ctor_set_tag(v___x_70_, 1);
lean_ctor_set(v___x_70_, 1, v___x_91_);
lean_ctor_set(v___x_70_, 0, v___x_90_);
v___x_93_ = v___x_70_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_90_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v___x_91_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
else
{
lean_object* v___x_96_; 
lean_dec(v_snd_73_);
lean_dec_ref(v_leanOpts_47_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 0, v___x_78_);
v___x_96_ = v___x_70_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v___x_78_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v_a_68_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
}
else
{
lean_object* v_a_99_; lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_107_; 
lean_dec(v_a_60_);
lean_dec_ref(v_leanOpts_47_);
lean_dec(v_lakeArgs_x3f_38_);
lean_dec_ref(v_lakeEnv_37_);
v_a_99_ = lean_ctor_get(v___x_66_, 0);
v_a_100_ = lean_ctor_get(v___x_66_, 1);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_107_ == 0)
{
v___x_102_ = v___x_66_;
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_inc(v_a_99_);
lean_dec(v___x_66_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_105_; 
if (v_isShared_103_ == 0)
{
v___x_105_ = v___x_102_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_a_99_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v_a_100_);
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
else
{
lean_object* v_a_109_; lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
lean_del_object(v___x_54_);
lean_dec_ref(v_remoteUrl_52_);
lean_dec_ref(v_scope_51_);
lean_dec_ref(v_leanOpts_47_);
lean_dec(v_lakeOpts_46_);
lean_dec_ref(v_packageOverrides_45_);
lean_dec_ref(v_configFile_44_);
lean_dec_ref(v_relConfigFile_43_);
lean_dec_ref(v_pkgDir_42_);
lean_dec_ref(v_relPkgDir_41_);
lean_dec(v_pkgName_40_);
lean_dec_ref(v_wsDir_39_);
lean_dec(v_lakeArgs_x3f_38_);
lean_dec_ref(v_lakeEnv_37_);
v_a_109_ = lean_ctor_get(v___x_59_, 0);
v_a_110_ = lean_ctor_get(v___x_59_, 1);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_59_);
if (v_isSharedCheck_117_ == 0)
{
v___x_112_ = v___x_59_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_inc(v_a_109_);
lean_dec(v___x_59_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_a_109_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v_a_110_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspaceRoot___boxed(lean_object* v_config_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lake_loadWorkspaceRoot(v_config_120_, v_a_121_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(lean_object* v_as_124_, size_t v_i_125_, size_t v_stop_126_, lean_object* v_b_127_, lean_object* v___y_128_){
_start:
{
uint8_t v___x_130_; 
v___x_130_ = lean_usize_dec_eq(v_i_125_, v_stop_126_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; lean_object* v___x_132_; size_t v___x_133_; size_t v___x_134_; 
v___x_131_ = lean_array_uget_borrowed(v_as_124_, v_i_125_);
lean_inc_ref(v___y_128_);
lean_inc(v___x_131_);
v___x_132_ = lean_apply_2(v___y_128_, v___x_131_, lean_box(0));
v___x_133_ = ((size_t)1ULL);
v___x_134_ = lean_usize_add(v_i_125_, v___x_133_);
v_i_125_ = v___x_134_;
v_b_127_ = v___x_132_;
goto _start;
}
else
{
lean_object* v___x_136_; 
v___x_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_136_, 0, v_b_127_);
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0___boxed(lean_object* v_as_137_, lean_object* v_i_138_, lean_object* v_stop_139_, lean_object* v_b_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
size_t v_i_boxed_143_; size_t v_stop_boxed_144_; lean_object* v_res_145_; 
v_i_boxed_143_ = lean_unbox_usize(v_i_138_);
lean_dec(v_i_138_);
v_stop_boxed_144_ = lean_unbox_usize(v_stop_139_);
lean_dec(v_stop_139_);
v_res_145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_as_137_, v_i_boxed_143_, v_stop_boxed_144_, v_b_140_, v___y_141_);
lean_dec_ref(v___y_141_);
lean_dec_ref(v_as_137_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace(lean_object* v_config_148_, lean_object* v_a_149_){
_start:
{
lean_object* v_packageOverrides_154_; lean_object* v_leanOpts_155_; uint8_t v_reconfigure_156_; uint8_t v_updateDeps_157_; uint8_t v_updateToolchain_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_packageOverrides_154_ = lean_ctor_get(v_config_148_, 9);
lean_inc_ref(v_packageOverrides_154_);
v_leanOpts_155_ = lean_ctor_get(v_config_148_, 11);
lean_inc_ref(v_leanOpts_155_);
v_reconfigure_156_ = lean_ctor_get_uint8(v_config_148_, sizeof(void*)*14);
v_updateDeps_157_ = lean_ctor_get_uint8(v_config_148_, sizeof(void*)*14 + 1);
v_updateToolchain_158_ = lean_ctor_get_uint8(v_config_148_, sizeof(void*)*14 + 2);
v___x_159_ = lean_unsigned_to_nat(0u);
v___x_160_ = ((lean_object*)(l_Lake_loadWorkspace___closed__0));
v___x_161_ = l_Lake_loadWorkspaceRoot(v_config_148_, v___x_160_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v_a_163_; lean_object* v___x_190_; uint8_t v___x_191_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_a_162_);
v_a_163_ = lean_ctor_get(v___x_161_, 1);
lean_inc(v_a_163_);
lean_dec_ref(v___x_161_);
v___x_190_ = lean_array_get_size(v_a_163_);
v___x_191_ = lean_nat_dec_lt(v___x_159_, v___x_190_);
if (v___x_191_ == 0)
{
lean_dec(v_a_163_);
goto v___jp_164_;
}
else
{
lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_192_ = lean_box(0);
v___x_193_ = lean_nat_dec_le(v___x_190_, v___x_190_);
if (v___x_193_ == 0)
{
if (v___x_191_ == 0)
{
lean_dec(v_a_163_);
goto v___jp_164_;
}
else
{
size_t v___x_194_; size_t v___x_195_; lean_object* v___x_196_; 
v___x_194_ = ((size_t)0ULL);
v___x_195_ = lean_usize_of_nat(v___x_190_);
v___x_196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_a_163_, v___x_194_, v___x_195_, v___x_192_, v_a_149_);
lean_dec(v_a_163_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_dec_ref(v___x_196_);
goto v___jp_164_;
}
else
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
lean_dec(v_a_162_);
lean_dec_ref(v_leanOpts_155_);
lean_dec_ref(v_packageOverrides_154_);
v_a_197_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_196_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_196_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
else
{
size_t v___x_205_; size_t v___x_206_; lean_object* v___x_207_; 
v___x_205_ = ((size_t)0ULL);
v___x_206_ = lean_usize_of_nat(v___x_190_);
v___x_207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_a_163_, v___x_205_, v___x_206_, v___x_192_, v_a_149_);
lean_dec(v_a_163_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_dec_ref(v___x_207_);
goto v___jp_164_;
}
else
{
lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_215_; 
lean_dec(v_a_162_);
lean_dec_ref(v_leanOpts_155_);
lean_dec_ref(v_packageOverrides_154_);
v_a_208_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_215_ == 0)
{
v___x_210_ = v___x_207_;
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_207_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_a_208_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
}
v___jp_164_:
{
if (v_updateDeps_157_ == 0)
{
lean_object* v_root_165_; lean_object* v_dir_166_; lean_object* v_relManifestFile_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v_root_165_ = lean_ctor_get(v_a_162_, 0);
v_dir_166_ = lean_ctor_get(v_root_165_, 4);
v_relManifestFile_167_ = lean_ctor_get(v_root_165_, 9);
lean_inc_ref(v_relManifestFile_167_);
lean_inc_ref(v_dir_166_);
v___x_168_ = l_Lake_joinRelative(v_dir_166_, v_relManifestFile_167_);
v___x_169_ = l_Lake_Manifest_load_x3f(v___x_168_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v_a_170_; 
v_a_170_ = lean_ctor_get(v___x_169_, 0);
lean_inc(v_a_170_);
lean_dec_ref(v___x_169_);
if (lean_obj_tag(v_a_170_) == 1)
{
lean_object* v_val_171_; lean_object* v___x_172_; 
v_val_171_ = lean_ctor_get(v_a_170_, 0);
lean_inc(v_val_171_);
lean_dec_ref(v_a_170_);
v___x_172_ = l_Lake_Workspace_materializeDeps(v_a_162_, v_val_171_, v_leanOpts_155_, v_reconfigure_156_, v_packageOverrides_154_, v_a_149_);
lean_dec_ref(v_packageOverrides_154_);
return v___x_172_;
}
else
{
lean_object* v___x_173_; lean_object* v___x_174_; 
lean_dec(v_a_170_);
lean_dec_ref(v_packageOverrides_154_);
v___x_173_ = l_Lean_NameSet_empty;
v___x_174_ = l_Lake_Workspace_updateAndMaterialize(v_a_162_, v___x_173_, v_leanOpts_155_, v_updateToolchain_158_, v_a_149_);
return v___x_174_;
}
}
else
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_187_; 
lean_dec(v_a_162_);
lean_dec_ref(v_leanOpts_155_);
lean_dec_ref(v_packageOverrides_154_);
v_a_175_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_187_ == 0)
{
v___x_177_ = v___x_169_;
v_isShared_178_ = v_isSharedCheck_187_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_169_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_187_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; uint8_t v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_185_; 
v___x_179_ = lean_io_error_to_string(v_a_175_);
v___x_180_ = 3;
v___x_181_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_181_, 0, v___x_179_);
lean_ctor_set_uint8(v___x_181_, sizeof(void*)*1, v___x_180_);
lean_inc_ref(v_a_149_);
v___x_182_ = lean_apply_2(v_a_149_, v___x_181_, lean_box(0));
v___x_183_ = lean_box(0);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___x_183_);
v___x_185_ = v___x_177_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_183_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
else
{
lean_object* v___x_188_; lean_object* v___x_189_; 
lean_dec_ref(v_packageOverrides_154_);
v___x_188_ = l_Lean_NameSet_empty;
v___x_189_ = l_Lake_Workspace_updateAndMaterialize(v_a_162_, v___x_188_, v_leanOpts_155_, v_updateToolchain_158_, v_a_149_);
return v___x_189_;
}
}
}
else
{
lean_object* v_a_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
lean_dec_ref(v_leanOpts_155_);
lean_dec_ref(v_packageOverrides_154_);
v_a_216_ = lean_ctor_get(v___x_161_, 1);
lean_inc(v_a_216_);
lean_dec_ref(v___x_161_);
v___x_217_ = lean_array_get_size(v_a_216_);
v___x_218_ = lean_nat_dec_lt(v___x_159_, v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; 
lean_dec(v_a_216_);
v___x_219_ = lean_box(0);
v___x_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
return v___x_220_;
}
else
{
lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_221_ = lean_box(0);
v___x_222_ = lean_nat_dec_le(v___x_217_, v___x_217_);
if (v___x_222_ == 0)
{
if (v___x_218_ == 0)
{
lean_dec(v_a_216_);
goto v___jp_151_;
}
else
{
size_t v___x_223_; size_t v___x_224_; lean_object* v___x_225_; 
v___x_223_ = ((size_t)0ULL);
v___x_224_ = lean_usize_of_nat(v___x_217_);
v___x_225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_a_216_, v___x_223_, v___x_224_, v___x_221_, v_a_149_);
lean_dec(v_a_216_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_dec_ref(v___x_225_);
goto v___jp_151_;
}
else
{
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_233_; 
v_a_226_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_233_ == 0)
{
v___x_228_ = v___x_225_;
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___x_225_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_231_; 
if (v_isShared_229_ == 0)
{
v___x_231_ = v___x_228_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_a_226_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
}
else
{
size_t v___x_234_; size_t v___x_235_; lean_object* v___x_236_; 
v___x_234_ = ((size_t)0ULL);
v___x_235_ = lean_usize_of_nat(v___x_217_);
v___x_236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_a_216_, v___x_234_, v___x_235_, v___x_221_, v_a_149_);
lean_dec(v_a_216_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_dec_ref(v___x_236_);
goto v___jp_151_;
}
else
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_244_ == 0)
{
v___x_239_ = v___x_236_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_236_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_a_237_);
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
v___jp_151_:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_box(0);
v___x_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
return v___x_153_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___boxed(lean_object* v_config_245_, lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lake_loadWorkspace(v_config_245_, v_a_246_);
lean_dec_ref(v_a_246_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lake_updateManifest(lean_object* v_config_249_, lean_object* v_toUpdate_250_, lean_object* v_a_251_){
_start:
{
lean_object* v_leanOpts_256_; uint8_t v_updateToolchain_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v_leanOpts_256_ = lean_ctor_get(v_config_249_, 11);
lean_inc_ref(v_leanOpts_256_);
v_updateToolchain_257_ = lean_ctor_get_uint8(v_config_249_, sizeof(void*)*14 + 2);
v___x_258_ = lean_unsigned_to_nat(0u);
v___x_259_ = ((lean_object*)(l_Lake_loadWorkspace___closed__0));
v___x_260_ = l_Lake_loadWorkspaceRoot(v_config_249_, v___x_259_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_a_261_; lean_object* v_a_262_; lean_object* v___x_282_; uint8_t v___x_283_; 
v_a_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_a_261_);
v_a_262_ = lean_ctor_get(v___x_260_, 1);
lean_inc(v_a_262_);
lean_dec_ref(v___x_260_);
v___x_282_ = lean_array_get_size(v_a_262_);
v___x_283_ = lean_nat_dec_lt(v___x_258_, v___x_282_);
if (v___x_283_ == 0)
{
lean_dec(v_a_262_);
goto v___jp_263_;
}
else
{
lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_284_ = lean_box(0);
v___x_285_ = lean_nat_dec_le(v___x_282_, v___x_282_);
if (v___x_285_ == 0)
{
if (v___x_283_ == 0)
{
lean_dec(v_a_262_);
goto v___jp_263_;
}
else
{
size_t v___x_286_; size_t v___x_287_; lean_object* v___x_288_; 
v___x_286_ = ((size_t)0ULL);
v___x_287_ = lean_usize_of_nat(v___x_282_);
v___x_288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_a_262_, v___x_286_, v___x_287_, v___x_284_, v_a_251_);
lean_dec(v_a_262_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_dec_ref(v___x_288_);
goto v___jp_263_;
}
else
{
lean_dec(v_a_261_);
lean_dec_ref(v_leanOpts_256_);
return v___x_288_;
}
}
}
else
{
size_t v___x_289_; size_t v___x_290_; lean_object* v___x_291_; 
v___x_289_ = ((size_t)0ULL);
v___x_290_ = lean_usize_of_nat(v___x_282_);
v___x_291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_a_262_, v___x_289_, v___x_290_, v___x_284_, v_a_251_);
lean_dec(v_a_262_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_dec_ref(v___x_291_);
goto v___jp_263_;
}
else
{
lean_dec(v_a_261_);
lean_dec_ref(v_leanOpts_256_);
return v___x_291_;
}
}
}
v___jp_263_:
{
lean_object* v___x_264_; 
v___x_264_ = l_Lake_Workspace_updateAndMaterialize(v_a_261_, v_toUpdate_250_, v_leanOpts_256_, v_updateToolchain_257_, v_a_251_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_272_; 
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_272_ == 0)
{
lean_object* v_unused_273_; 
v_unused_273_ = lean_ctor_get(v___x_264_, 0);
lean_dec(v_unused_273_);
v___x_266_ = v___x_264_;
v_isShared_267_ = v_isSharedCheck_272_;
goto v_resetjp_265_;
}
else
{
lean_dec(v___x_264_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_272_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; lean_object* v___x_270_; 
v___x_268_ = lean_box(0);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 0, v___x_268_);
v___x_270_ = v___x_266_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_268_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
v_a_274_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_264_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_264_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
else
{
lean_object* v_a_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
lean_dec_ref(v_leanOpts_256_);
v_a_292_ = lean_ctor_get(v___x_260_, 1);
lean_inc(v_a_292_);
lean_dec_ref(v___x_260_);
v___x_293_ = lean_array_get_size(v_a_292_);
v___x_294_ = lean_nat_dec_lt(v___x_258_, v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; 
lean_dec(v_a_292_);
v___x_295_ = lean_box(0);
v___x_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
else
{
lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = lean_box(0);
v___x_298_ = lean_nat_dec_le(v___x_293_, v___x_293_);
if (v___x_298_ == 0)
{
if (v___x_294_ == 0)
{
lean_dec(v_a_292_);
goto v___jp_253_;
}
else
{
size_t v___x_299_; size_t v___x_300_; lean_object* v___x_301_; 
v___x_299_ = ((size_t)0ULL);
v___x_300_ = lean_usize_of_nat(v___x_293_);
v___x_301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_a_292_, v___x_299_, v___x_300_, v___x_297_, v_a_251_);
lean_dec(v_a_292_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_dec_ref(v___x_301_);
goto v___jp_253_;
}
else
{
return v___x_301_;
}
}
}
else
{
size_t v___x_302_; size_t v___x_303_; lean_object* v___x_304_; 
v___x_302_ = ((size_t)0ULL);
v___x_303_ = lean_usize_of_nat(v___x_293_);
v___x_304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__0(v_a_292_, v___x_302_, v___x_303_, v___x_297_, v_a_251_);
lean_dec(v_a_292_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_dec_ref(v___x_304_);
goto v___jp_253_;
}
else
{
return v___x_304_;
}
}
}
}
v___jp_253_:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_box(0);
v___x_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
return v___x_255_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateManifest___boxed(lean_object* v_config_305_, lean_object* v_toUpdate_306_, lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lake_updateManifest(v_config_305_, v_toUpdate_306_, v_a_307_);
lean_dec_ref(v_a_307_);
lean_dec(v_toUpdate_306_);
return v_res_309_;
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
