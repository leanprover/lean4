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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
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
static lean_once_cell_t l_Lake_loadWorkspaceRoot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_loadWorkspaceRoot___closed__1;
static lean_once_cell_t l_Lake_loadWorkspaceRoot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_loadWorkspaceRoot___closed__2;
static const lean_array_object l_Lake_loadWorkspaceRoot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_loadWorkspaceRoot___closed__3 = (const lean_object*)&l_Lake_loadWorkspaceRoot___closed__3_value;
static const lean_string_object l_Lake_loadWorkspaceRoot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cache"};
static const lean_object* l_Lake_loadWorkspaceRoot___closed__4 = (const lean_object*)&l_Lake_loadWorkspaceRoot___closed__4_value;
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
static lean_object* _init_l_Lake_loadWorkspaceRoot___closed__1(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_32_ = lean_box(0);
v___x_33_ = lean_unsigned_to_nat(16u);
v___x_34_ = lean_mk_array(v___x_33_, v___x_32_);
return v___x_34_;
}
}
static lean_object* _init_l_Lake_loadWorkspaceRoot___closed__2(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_35_ = lean_obj_once(&l_Lake_loadWorkspaceRoot___closed__1, &l_Lake_loadWorkspaceRoot___closed__1_once, _init_l_Lake_loadWorkspaceRoot___closed__1);
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
lean_ctor_set(v___x_37_, 1, v___x_35_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspaceRoot(lean_object* v_config_41_, lean_object* v_a_42_){
_start:
{
lean_object* v_lakeEnv_44_; lean_object* v_lakeArgs_x3f_45_; lean_object* v_wsDir_46_; lean_object* v_pkgName_47_; lean_object* v_relPkgDir_48_; lean_object* v_pkgDir_49_; lean_object* v_relConfigFile_50_; lean_object* v_configFile_51_; lean_object* v_packageOverrides_52_; lean_object* v_lakeOpts_53_; lean_object* v_leanOpts_54_; uint8_t v_reconfigure_55_; uint8_t v_updateDeps_56_; uint8_t v_updateToolchain_57_; lean_object* v_scope_58_; lean_object* v_remoteUrl_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_173_; 
v_lakeEnv_44_ = lean_ctor_get(v_config_41_, 0);
v_lakeArgs_x3f_45_ = lean_ctor_get(v_config_41_, 1);
v_wsDir_46_ = lean_ctor_get(v_config_41_, 2);
v_pkgName_47_ = lean_ctor_get(v_config_41_, 4);
v_relPkgDir_48_ = lean_ctor_get(v_config_41_, 5);
v_pkgDir_49_ = lean_ctor_get(v_config_41_, 6);
v_relConfigFile_50_ = lean_ctor_get(v_config_41_, 7);
v_configFile_51_ = lean_ctor_get(v_config_41_, 8);
v_packageOverrides_52_ = lean_ctor_get(v_config_41_, 9);
v_lakeOpts_53_ = lean_ctor_get(v_config_41_, 10);
v_leanOpts_54_ = lean_ctor_get(v_config_41_, 11);
v_reconfigure_55_ = lean_ctor_get_uint8(v_config_41_, sizeof(void*)*14);
v_updateDeps_56_ = lean_ctor_get_uint8(v_config_41_, sizeof(void*)*14 + 1);
v_updateToolchain_57_ = lean_ctor_get_uint8(v_config_41_, sizeof(void*)*14 + 2);
v_scope_58_ = lean_ctor_get(v_config_41_, 12);
v_remoteUrl_59_ = lean_ctor_get(v_config_41_, 13);
v_isSharedCheck_173_ = !lean_is_exclusive(v_config_41_);
if (v_isSharedCheck_173_ == 0)
{
lean_object* v_unused_174_; 
v_unused_174_ = lean_ctor_get(v_config_41_, 3);
lean_dec(v_unused_174_);
v___x_61_ = v_config_41_;
v_isShared_62_ = v_isSharedCheck_173_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_remoteUrl_59_);
lean_inc(v_scope_58_);
lean_inc(v_leanOpts_54_);
lean_inc(v_lakeOpts_53_);
lean_inc(v_packageOverrides_52_);
lean_inc(v_configFile_51_);
lean_inc(v_relConfigFile_50_);
lean_inc(v_pkgDir_49_);
lean_inc(v_relPkgDir_48_);
lean_inc(v_pkgName_47_);
lean_inc(v_wsDir_46_);
lean_inc(v_lakeArgs_x3f_45_);
lean_inc(v_lakeEnv_44_);
lean_dec(v_config_41_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_173_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_63_ = l_Lean_searchPathRef;
v___x_64_ = l_Lake_Env_leanSearchPath(v_lakeEnv_44_);
v___x_65_ = lean_st_ref_set(v___x_63_, v___x_64_);
lean_inc_ref(v_lakeEnv_44_);
v___x_66_ = l_Lake_loadLakeConfig(v_lakeEnv_44_, v_a_42_);
if (lean_obj_tag(v___x_66_) == 0)
{
lean_object* v_a_67_; lean_object* v_a_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_72_; 
v_a_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_a_67_);
v_a_68_ = lean_ctor_get(v___x_66_, 1);
lean_inc(v_a_68_);
lean_dec_ref(v___x_66_);
v___x_69_ = ((lean_object*)(l_Lake_loadWorkspaceRoot___closed__0));
v___x_70_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_leanOpts_54_);
lean_inc(v_lakeArgs_x3f_45_);
lean_inc_ref(v_lakeEnv_44_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 3, v___x_70_);
v___x_72_ = v___x_61_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 14, 3);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_lakeEnv_44_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v_lakeArgs_x3f_45_);
lean_ctor_set(v_reuseFailAlloc_163_, 2, v_wsDir_46_);
lean_ctor_set(v_reuseFailAlloc_163_, 3, v___x_70_);
lean_ctor_set(v_reuseFailAlloc_163_, 4, v_pkgName_47_);
lean_ctor_set(v_reuseFailAlloc_163_, 5, v_relPkgDir_48_);
lean_ctor_set(v_reuseFailAlloc_163_, 6, v_pkgDir_49_);
lean_ctor_set(v_reuseFailAlloc_163_, 7, v_relConfigFile_50_);
lean_ctor_set(v_reuseFailAlloc_163_, 8, v_configFile_51_);
lean_ctor_set(v_reuseFailAlloc_163_, 9, v_packageOverrides_52_);
lean_ctor_set(v_reuseFailAlloc_163_, 10, v_lakeOpts_53_);
lean_ctor_set(v_reuseFailAlloc_163_, 11, v_leanOpts_54_);
lean_ctor_set(v_reuseFailAlloc_163_, 12, v_scope_58_);
lean_ctor_set(v_reuseFailAlloc_163_, 13, v_remoteUrl_59_);
lean_ctor_set_uint8(v_reuseFailAlloc_163_, sizeof(void*)*14, v_reconfigure_55_);
lean_ctor_set_uint8(v_reuseFailAlloc_163_, sizeof(void*)*14 + 1, v_updateDeps_56_);
lean_ctor_set_uint8(v_reuseFailAlloc_163_, sizeof(void*)*14 + 2, v_updateToolchain_57_);
v___x_72_ = v_reuseFailAlloc_163_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lake_loadPackageCore(v___x_69_, v___x_72_, v_a_68_);
if (lean_obj_tag(v___x_73_) == 0)
{
lean_object* v_a_74_; lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_153_; 
v_a_74_ = lean_ctor_get(v___x_73_, 0);
v_a_75_ = lean_ctor_get(v___x_73_, 1);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_153_ == 0)
{
v___x_77_ = v___x_73_;
v_isShared_78_ = v_isSharedCheck_153_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_inc(v_a_74_);
lean_dec(v___x_73_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_153_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v_fst_79_; lean_object* v_snd_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v_config_83_; lean_object* v_wsIdx_84_; lean_object* v_baseName_85_; lean_object* v_keyName_86_; lean_object* v_origName_87_; lean_object* v_dir_88_; lean_object* v_relDir_89_; lean_object* v_configFile_90_; lean_object* v_relConfigFile_91_; lean_object* v_relManifestFile_92_; lean_object* v_scope_93_; lean_object* v_remoteUrl_94_; lean_object* v_depConfigs_95_; lean_object* v_targetDecls_96_; lean_object* v_targetDeclMap_97_; lean_object* v_defaultTargets_98_; lean_object* v_scripts_99_; lean_object* v_defaultScripts_100_; lean_object* v_postUpdateHooks_101_; lean_object* v_buildArchive_102_; lean_object* v_testDriver_103_; lean_object* v_lintDriver_104_; lean_object* v_inputsRef_x3f_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_151_; 
v_fst_79_ = lean_ctor_get(v_a_74_, 0);
lean_inc(v_fst_79_);
v_snd_80_ = lean_ctor_get(v_a_74_, 1);
lean_inc(v_snd_80_);
lean_dec(v_a_74_);
v___x_81_ = lean_obj_once(&l_Lake_loadWorkspaceRoot___closed__2, &l_Lake_loadWorkspaceRoot___closed__2_once, _init_l_Lake_loadWorkspaceRoot___closed__2);
v___x_82_ = lean_st_mk_ref(v___x_81_);
v_config_83_ = lean_ctor_get(v_fst_79_, 6);
v_wsIdx_84_ = lean_ctor_get(v_fst_79_, 0);
v_baseName_85_ = lean_ctor_get(v_fst_79_, 1);
v_keyName_86_ = lean_ctor_get(v_fst_79_, 2);
v_origName_87_ = lean_ctor_get(v_fst_79_, 3);
v_dir_88_ = lean_ctor_get(v_fst_79_, 4);
v_relDir_89_ = lean_ctor_get(v_fst_79_, 5);
v_configFile_90_ = lean_ctor_get(v_fst_79_, 7);
v_relConfigFile_91_ = lean_ctor_get(v_fst_79_, 8);
v_relManifestFile_92_ = lean_ctor_get(v_fst_79_, 9);
v_scope_93_ = lean_ctor_get(v_fst_79_, 10);
v_remoteUrl_94_ = lean_ctor_get(v_fst_79_, 11);
v_depConfigs_95_ = lean_ctor_get(v_fst_79_, 12);
v_targetDecls_96_ = lean_ctor_get(v_fst_79_, 13);
v_targetDeclMap_97_ = lean_ctor_get(v_fst_79_, 14);
v_defaultTargets_98_ = lean_ctor_get(v_fst_79_, 15);
v_scripts_99_ = lean_ctor_get(v_fst_79_, 16);
v_defaultScripts_100_ = lean_ctor_get(v_fst_79_, 17);
v_postUpdateHooks_101_ = lean_ctor_get(v_fst_79_, 18);
v_buildArchive_102_ = lean_ctor_get(v_fst_79_, 19);
v_testDriver_103_ = lean_ctor_get(v_fst_79_, 20);
v_lintDriver_104_ = lean_ctor_get(v_fst_79_, 21);
v_inputsRef_x3f_105_ = lean_ctor_get(v_fst_79_, 22);
v_isSharedCheck_151_ = !lean_is_exclusive(v_fst_79_);
if (v_isSharedCheck_151_ == 0)
{
lean_object* v_unused_152_; 
v_unused_152_ = lean_ctor_get(v_fst_79_, 23);
lean_dec(v_unused_152_);
v___x_107_ = v_fst_79_;
v_isShared_108_ = v_isSharedCheck_151_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_inputsRef_x3f_105_);
lean_inc(v_lintDriver_104_);
lean_inc(v_testDriver_103_);
lean_inc(v_buildArchive_102_);
lean_inc(v_postUpdateHooks_101_);
lean_inc(v_defaultScripts_100_);
lean_inc(v_scripts_99_);
lean_inc(v_defaultTargets_98_);
lean_inc(v_targetDeclMap_97_);
lean_inc(v_targetDecls_96_);
lean_inc(v_depConfigs_95_);
lean_inc(v_remoteUrl_94_);
lean_inc(v_scope_93_);
lean_inc(v_relManifestFile_92_);
lean_inc(v_relConfigFile_91_);
lean_inc(v_configFile_90_);
lean_inc(v_config_83_);
lean_inc(v_relDir_89_);
lean_inc(v_dir_88_);
lean_inc(v_origName_87_);
lean_inc(v_keyName_86_);
lean_inc(v_baseName_85_);
lean_inc(v_wsIdx_84_);
lean_dec(v_fst_79_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_151_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
uint8_t v_bootstrap_109_; lean_object* v___x_110_; lean_object* v___x_112_; 
v_bootstrap_109_ = lean_ctor_get_uint8(v_config_83_, sizeof(void*)*27);
v___x_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_82_);
lean_inc_ref(v_dir_88_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 23, v___x_110_);
v___x_112_ = v___x_107_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 24, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_wsIdx_84_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v_baseName_85_);
lean_ctor_set(v_reuseFailAlloc_150_, 2, v_keyName_86_);
lean_ctor_set(v_reuseFailAlloc_150_, 3, v_origName_87_);
lean_ctor_set(v_reuseFailAlloc_150_, 4, v_dir_88_);
lean_ctor_set(v_reuseFailAlloc_150_, 5, v_relDir_89_);
lean_ctor_set(v_reuseFailAlloc_150_, 6, v_config_83_);
lean_ctor_set(v_reuseFailAlloc_150_, 7, v_configFile_90_);
lean_ctor_set(v_reuseFailAlloc_150_, 8, v_relConfigFile_91_);
lean_ctor_set(v_reuseFailAlloc_150_, 9, v_relManifestFile_92_);
lean_ctor_set(v_reuseFailAlloc_150_, 10, v_scope_93_);
lean_ctor_set(v_reuseFailAlloc_150_, 11, v_remoteUrl_94_);
lean_ctor_set(v_reuseFailAlloc_150_, 12, v_depConfigs_95_);
lean_ctor_set(v_reuseFailAlloc_150_, 13, v_targetDecls_96_);
lean_ctor_set(v_reuseFailAlloc_150_, 14, v_targetDeclMap_97_);
lean_ctor_set(v_reuseFailAlloc_150_, 15, v_defaultTargets_98_);
lean_ctor_set(v_reuseFailAlloc_150_, 16, v_scripts_99_);
lean_ctor_set(v_reuseFailAlloc_150_, 17, v_defaultScripts_100_);
lean_ctor_set(v_reuseFailAlloc_150_, 18, v_postUpdateHooks_101_);
lean_ctor_set(v_reuseFailAlloc_150_, 19, v_buildArchive_102_);
lean_ctor_set(v_reuseFailAlloc_150_, 20, v_testDriver_103_);
lean_ctor_set(v_reuseFailAlloc_150_, 21, v_lintDriver_104_);
lean_ctor_set(v_reuseFailAlloc_150_, 22, v_inputsRef_x3f_105_);
lean_ctor_set(v_reuseFailAlloc_150_, 23, v___x_110_);
v___x_112_ = v_reuseFailAlloc_150_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
lean_object* v___y_114_; 
if (v_bootstrap_109_ == 0)
{
lean_object* v_lakeCache_x3f_138_; 
v_lakeCache_x3f_138_ = lean_ctor_get(v_lakeEnv_44_, 7);
if (lean_obj_tag(v_lakeCache_x3f_138_) == 0)
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_139_ = l_Lake_defaultLakeDir;
v___x_140_ = l_Lake_joinRelative(v_dir_88_, v___x_139_);
v___x_141_ = ((lean_object*)(l_Lake_loadWorkspaceRoot___closed__4));
v___x_142_ = l_Lake_joinRelative(v___x_140_, v___x_141_);
v___y_114_ = v___x_142_;
goto v___jp_113_;
}
else
{
lean_object* v_val_143_; 
lean_dec_ref(v_dir_88_);
v_val_143_ = lean_ctor_get(v_lakeCache_x3f_138_, 0);
lean_inc(v_val_143_);
v___y_114_ = v_val_143_;
goto v___jp_113_;
}
}
else
{
lean_object* v_lakeSystemCache_x3f_144_; 
v_lakeSystemCache_x3f_144_ = lean_ctor_get(v_lakeEnv_44_, 8);
if (lean_obj_tag(v_lakeSystemCache_x3f_144_) == 0)
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_145_ = l_Lake_defaultLakeDir;
v___x_146_ = l_Lake_joinRelative(v_dir_88_, v___x_145_);
v___x_147_ = ((lean_object*)(l_Lake_loadWorkspaceRoot___closed__4));
v___x_148_ = l_Lake_joinRelative(v___x_146_, v___x_147_);
v___y_114_ = v___x_148_;
goto v___jp_113_;
}
else
{
lean_object* v_val_149_; 
lean_dec_ref(v_dir_88_);
v_val_149_ = lean_ctor_get(v_lakeSystemCache_x3f_144_, 0);
lean_inc(v_val_149_);
v___y_114_ = v_val_149_;
goto v___jp_113_;
}
}
v___jp_113_:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_115_ = ((lean_object*)(l_Lake_loadWorkspaceRoot___closed__3));
v___x_116_ = lean_box(1);
v___x_117_ = l_Lake_initFacetConfigs;
v___x_118_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_118_, 0, v___x_112_);
lean_ctor_set(v___x_118_, 1, v_lakeEnv_44_);
lean_ctor_set(v___x_118_, 2, v_a_67_);
lean_ctor_set(v___x_118_, 3, v___y_114_);
lean_ctor_set(v___x_118_, 4, v_lakeArgs_x3f_45_);
lean_ctor_set(v___x_118_, 5, v___x_115_);
lean_ctor_set(v___x_118_, 6, v___x_116_);
lean_ctor_set(v___x_118_, 7, v___x_117_);
if (lean_obj_tag(v_snd_80_) == 1)
{
lean_object* v_val_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v_val_119_ = lean_ctor_get(v_snd_80_, 0);
lean_inc(v_val_119_);
lean_dec_ref(v_snd_80_);
v___x_120_ = l_Lake_Workspace_addFacetsFromEnv(v_val_119_, v_leanOpts_54_, v___x_118_);
lean_dec_ref(v_leanOpts_54_);
v___x_121_ = l_IO_ofExcept___at___00Lake_loadWorkspaceRoot_spec__0___redArg(v___x_120_);
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v_a_122_; lean_object* v___x_124_; 
v_a_122_ = lean_ctor_get(v___x_121_, 0);
lean_inc(v_a_122_);
lean_dec_ref(v___x_121_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 0, v_a_122_);
v___x_124_ = v___x_77_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_a_122_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v_a_75_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
else
{
lean_object* v_a_126_; lean_object* v___x_127_; uint8_t v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
v_a_126_ = lean_ctor_get(v___x_121_, 0);
lean_inc(v_a_126_);
lean_dec_ref(v___x_121_);
v___x_127_ = lean_io_error_to_string(v_a_126_);
v___x_128_ = 3;
v___x_129_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_129_, 0, v___x_127_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*1, v___x_128_);
v___x_130_ = lean_array_get_size(v_a_75_);
v___x_131_ = lean_array_push(v_a_75_, v___x_129_);
if (v_isShared_78_ == 0)
{
lean_ctor_set_tag(v___x_77_, 1);
lean_ctor_set(v___x_77_, 1, v___x_131_);
lean_ctor_set(v___x_77_, 0, v___x_130_);
v___x_133_ = v___x_77_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_130_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v___x_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
else
{
lean_object* v___x_136_; 
lean_dec(v_snd_80_);
lean_dec_ref(v_leanOpts_54_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 0, v___x_118_);
v___x_136_ = v___x_77_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_118_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_a_75_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_154_; lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_162_; 
lean_dec(v_a_67_);
lean_dec_ref(v_leanOpts_54_);
lean_dec(v_lakeArgs_x3f_45_);
lean_dec_ref(v_lakeEnv_44_);
v_a_154_ = lean_ctor_get(v___x_73_, 0);
v_a_155_ = lean_ctor_get(v___x_73_, 1);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_162_ == 0)
{
v___x_157_ = v___x_73_;
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_inc(v_a_154_);
lean_dec(v___x_73_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
if (v_isShared_158_ == 0)
{
v___x_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_a_154_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v_a_155_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
}
}
else
{
lean_object* v_a_164_; lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
lean_del_object(v___x_61_);
lean_dec_ref(v_remoteUrl_59_);
lean_dec_ref(v_scope_58_);
lean_dec_ref(v_leanOpts_54_);
lean_dec(v_lakeOpts_53_);
lean_dec_ref(v_packageOverrides_52_);
lean_dec_ref(v_configFile_51_);
lean_dec_ref(v_relConfigFile_50_);
lean_dec_ref(v_pkgDir_49_);
lean_dec_ref(v_relPkgDir_48_);
lean_dec(v_pkgName_47_);
lean_dec_ref(v_wsDir_46_);
lean_dec(v_lakeArgs_x3f_45_);
lean_dec_ref(v_lakeEnv_44_);
v_a_164_ = lean_ctor_get(v___x_66_, 0);
v_a_165_ = lean_ctor_get(v___x_66_, 1);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_172_ == 0)
{
v___x_167_ = v___x_66_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_inc(v_a_164_);
lean_dec(v___x_66_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_a_164_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_a_165_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspaceRoot___boxed(lean_object* v_config_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lake_loadWorkspaceRoot(v_config_175_, v_a_176_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___redArg(lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_apply_2(v___y_180_, v___y_179_, lean_box(0));
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___redArg___boxed(lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lake_loadWorkspace___elam__0___redArg(v___y_184_, v___y_185_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0(lean_object* v_x_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Lake_loadWorkspace___elam__0___redArg(v___y_189_, v___y_190_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___boxed(lean_object* v_x_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lake_loadWorkspace___elam__0(v_x_193_, v___y_194_, v___y_195_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1___redArg(lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_apply_2(v___y_198_, v___y_199_, lean_box(0));
v___x_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1___redArg___boxed(lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1___redArg(v___y_203_, v___y_204_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(lean_object* v_as_207_, size_t v_i_208_, size_t v_stop_209_, lean_object* v_b_210_, lean_object* v___y_211_){
_start:
{
uint8_t v___x_213_; 
v___x_213_ = lean_usize_dec_eq(v_i_208_, v_stop_209_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = lean_array_uget_borrowed(v_as_207_, v_i_208_);
lean_inc(v___x_214_);
lean_inc_ref(v___y_211_);
v___x_215_ = l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1___redArg(v___y_211_, v___x_214_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v_a_216_; size_t v___x_217_; size_t v___x_218_; 
v_a_216_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_a_216_);
lean_dec_ref(v___x_215_);
v___x_217_ = ((size_t)1ULL);
v___x_218_ = lean_usize_add(v_i_208_, v___x_217_);
v_i_208_ = v___x_218_;
v_b_210_ = v_a_216_;
goto _start;
}
else
{
lean_dec_ref(v___y_211_);
return v___x_215_;
}
}
else
{
lean_object* v___x_220_; 
lean_dec_ref(v___y_211_);
v___x_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_220_, 0, v_b_210_);
return v___x_220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1___boxed(lean_object* v_as_221_, lean_object* v_i_222_, lean_object* v_stop_223_, lean_object* v_b_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
size_t v_i_boxed_227_; size_t v_stop_boxed_228_; lean_object* v_res_229_; 
v_i_boxed_227_ = lean_unbox_usize(v_i_222_);
lean_dec(v_i_222_);
v_stop_boxed_228_ = lean_unbox_usize(v_stop_223_);
lean_dec(v_stop_223_);
v_res_229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(v_as_221_, v_i_boxed_227_, v_stop_boxed_228_, v_b_224_, v___y_225_);
lean_dec_ref(v_as_221_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace(lean_object* v_config_232_, lean_object* v_a_233_){
_start:
{
lean_object* v_packageOverrides_238_; lean_object* v_leanOpts_239_; uint8_t v_reconfigure_240_; uint8_t v_updateDeps_241_; uint8_t v_updateToolchain_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_packageOverrides_238_ = lean_ctor_get(v_config_232_, 9);
lean_inc_ref(v_packageOverrides_238_);
v_leanOpts_239_ = lean_ctor_get(v_config_232_, 11);
lean_inc_ref(v_leanOpts_239_);
v_reconfigure_240_ = lean_ctor_get_uint8(v_config_232_, sizeof(void*)*14);
v_updateDeps_241_ = lean_ctor_get_uint8(v_config_232_, sizeof(void*)*14 + 1);
v_updateToolchain_242_ = lean_ctor_get_uint8(v_config_232_, sizeof(void*)*14 + 2);
v___x_243_ = lean_unsigned_to_nat(0u);
v___x_244_ = ((lean_object*)(l_Lake_loadWorkspace___closed__0));
v___x_245_ = l_Lake_loadWorkspaceRoot(v_config_232_, v___x_244_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_a_246_; lean_object* v_a_247_; lean_object* v___x_274_; uint8_t v___x_275_; 
v_a_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_a_246_);
v_a_247_ = lean_ctor_get(v___x_245_, 1);
lean_inc(v_a_247_);
lean_dec_ref(v___x_245_);
v___x_274_ = lean_array_get_size(v_a_247_);
v___x_275_ = lean_nat_dec_lt(v___x_243_, v___x_274_);
if (v___x_275_ == 0)
{
lean_dec(v_a_247_);
goto v___jp_248_;
}
else
{
lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_276_ = lean_box(0);
v___x_277_ = lean_nat_dec_le(v___x_274_, v___x_274_);
if (v___x_277_ == 0)
{
if (v___x_275_ == 0)
{
lean_dec(v_a_247_);
goto v___jp_248_;
}
else
{
size_t v___x_278_; size_t v___x_279_; lean_object* v___x_280_; 
v___x_278_ = ((size_t)0ULL);
v___x_279_ = lean_usize_of_nat(v___x_274_);
lean_inc_ref(v_a_233_);
v___x_280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(v_a_247_, v___x_278_, v___x_279_, v___x_276_, v_a_233_);
lean_dec(v_a_247_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_dec_ref(v___x_280_);
goto v___jp_248_;
}
else
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
lean_dec(v_a_246_);
lean_dec_ref(v_leanOpts_239_);
lean_dec_ref(v_packageOverrides_238_);
lean_dec_ref(v_a_233_);
v_a_281_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_288_ == 0)
{
v___x_283_ = v___x_280_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_280_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_a_281_);
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
else
{
size_t v___x_289_; size_t v___x_290_; lean_object* v___x_291_; 
v___x_289_ = ((size_t)0ULL);
v___x_290_ = lean_usize_of_nat(v___x_274_);
lean_inc_ref(v_a_233_);
v___x_291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(v_a_247_, v___x_289_, v___x_290_, v___x_276_, v_a_233_);
lean_dec(v_a_247_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_dec_ref(v___x_291_);
goto v___jp_248_;
}
else
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
lean_dec(v_a_246_);
lean_dec_ref(v_leanOpts_239_);
lean_dec_ref(v_packageOverrides_238_);
lean_dec_ref(v_a_233_);
v_a_292_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_291_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_291_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_292_);
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
}
v___jp_248_:
{
if (v_updateDeps_241_ == 0)
{
lean_object* v_root_249_; lean_object* v_dir_250_; lean_object* v_relManifestFile_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v_root_249_ = lean_ctor_get(v_a_246_, 0);
v_dir_250_ = lean_ctor_get(v_root_249_, 4);
v_relManifestFile_251_ = lean_ctor_get(v_root_249_, 9);
lean_inc_ref(v_relManifestFile_251_);
lean_inc_ref(v_dir_250_);
v___x_252_ = l_Lake_joinRelative(v_dir_250_, v_relManifestFile_251_);
v___x_253_ = l_Lake_Manifest_load_x3f(v___x_252_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc(v_a_254_);
lean_dec_ref(v___x_253_);
if (lean_obj_tag(v_a_254_) == 1)
{
lean_object* v_val_255_; lean_object* v___x_256_; 
v_val_255_ = lean_ctor_get(v_a_254_, 0);
lean_inc(v_val_255_);
lean_dec_ref(v_a_254_);
v___x_256_ = l_Lake_Workspace_materializeDeps(v_a_246_, v_val_255_, v_leanOpts_239_, v_reconfigure_240_, v_packageOverrides_238_, v_a_233_);
lean_dec_ref(v_packageOverrides_238_);
return v___x_256_;
}
else
{
lean_object* v___x_257_; lean_object* v___x_258_; 
lean_dec(v_a_254_);
lean_dec_ref(v_packageOverrides_238_);
v___x_257_ = l_Lean_NameSet_empty;
v___x_258_ = l_Lake_Workspace_updateAndMaterialize(v_a_246_, v___x_257_, v_leanOpts_239_, v_updateToolchain_242_, v_a_233_);
return v___x_258_;
}
}
else
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_271_; 
lean_dec(v_a_246_);
lean_dec_ref(v_leanOpts_239_);
lean_dec_ref(v_packageOverrides_238_);
v_a_259_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_271_ == 0)
{
v___x_261_ = v___x_253_;
v_isShared_262_ = v_isSharedCheck_271_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_253_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_271_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; uint8_t v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_263_ = lean_io_error_to_string(v_a_259_);
v___x_264_ = 3;
v___x_265_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set_uint8(v___x_265_, sizeof(void*)*1, v___x_264_);
v___x_266_ = lean_apply_2(v_a_233_, v___x_265_, lean_box(0));
v___x_267_ = lean_box(0);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_267_);
v___x_269_ = v___x_261_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_267_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
else
{
lean_object* v___x_272_; lean_object* v___x_273_; 
lean_dec_ref(v_packageOverrides_238_);
v___x_272_ = l_Lean_NameSet_empty;
v___x_273_ = l_Lake_Workspace_updateAndMaterialize(v_a_246_, v___x_272_, v_leanOpts_239_, v_updateToolchain_242_, v_a_233_);
return v___x_273_;
}
}
}
else
{
lean_object* v_a_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
lean_dec_ref(v_leanOpts_239_);
lean_dec_ref(v_packageOverrides_238_);
v_a_300_ = lean_ctor_get(v___x_245_, 1);
lean_inc(v_a_300_);
lean_dec_ref(v___x_245_);
v___x_301_ = lean_array_get_size(v_a_300_);
v___x_302_ = lean_nat_dec_lt(v___x_243_, v___x_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; 
lean_dec(v_a_300_);
lean_dec_ref(v_a_233_);
v___x_303_ = lean_box(0);
v___x_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
return v___x_304_;
}
else
{
lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_305_ = lean_box(0);
v___x_306_ = lean_nat_dec_le(v___x_301_, v___x_301_);
if (v___x_306_ == 0)
{
if (v___x_302_ == 0)
{
lean_dec(v_a_300_);
lean_dec_ref(v_a_233_);
goto v___jp_235_;
}
else
{
size_t v___x_307_; size_t v___x_308_; lean_object* v___x_309_; 
v___x_307_ = ((size_t)0ULL);
v___x_308_ = lean_usize_of_nat(v___x_301_);
v___x_309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(v_a_300_, v___x_307_, v___x_308_, v___x_305_, v_a_233_);
lean_dec(v_a_300_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_dec_ref(v___x_309_);
goto v___jp_235_;
}
else
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_317_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_317_ == 0)
{
v___x_312_ = v___x_309_;
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_309_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_310_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
}
else
{
size_t v___x_318_; size_t v___x_319_; lean_object* v___x_320_; 
v___x_318_ = ((size_t)0ULL);
v___x_319_ = lean_usize_of_nat(v___x_301_);
v___x_320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(v_a_300_, v___x_318_, v___x_319_, v___x_305_, v_a_233_);
lean_dec(v_a_300_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_dec_ref(v___x_320_);
goto v___jp_235_;
}
else
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v___x_320_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_320_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
}
v___jp_235_:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_box(0);
v___x_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___boxed(lean_object* v_config_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lake_loadWorkspace(v_config_329_, v_a_330_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1(lean_object* v___y_333_, lean_object* v_x_334_, lean_object* v___y_335_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1___redArg(v___y_333_, v___y_335_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1___boxed(lean_object* v___y_338_, lean_object* v_x_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lake_loadWorkspace___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1_spec__1(v___y_338_, v_x_339_, v___y_340_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lake_updateManifest(lean_object* v_config_343_, lean_object* v_toUpdate_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_leanOpts_350_; uint8_t v_updateToolchain_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v_leanOpts_350_ = lean_ctor_get(v_config_343_, 11);
lean_inc_ref(v_leanOpts_350_);
v_updateToolchain_351_ = lean_ctor_get_uint8(v_config_343_, sizeof(void*)*14 + 2);
v___x_352_ = lean_unsigned_to_nat(0u);
v___x_353_ = ((lean_object*)(l_Lake_loadWorkspace___closed__0));
v___x_354_ = l_Lake_loadWorkspaceRoot(v_config_343_, v___x_353_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; lean_object* v_a_356_; lean_object* v___x_376_; uint8_t v___x_377_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_a_355_);
v_a_356_ = lean_ctor_get(v___x_354_, 1);
lean_inc(v_a_356_);
lean_dec_ref(v___x_354_);
v___x_376_ = lean_array_get_size(v_a_356_);
v___x_377_ = lean_nat_dec_lt(v___x_352_, v___x_376_);
if (v___x_377_ == 0)
{
lean_dec(v_a_356_);
goto v___jp_357_;
}
else
{
lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_378_ = lean_box(0);
v___x_379_ = lean_nat_dec_le(v___x_376_, v___x_376_);
if (v___x_379_ == 0)
{
if (v___x_377_ == 0)
{
lean_dec(v_a_356_);
goto v___jp_357_;
}
else
{
size_t v___x_380_; size_t v___x_381_; lean_object* v___x_382_; 
v___x_380_ = ((size_t)0ULL);
v___x_381_ = lean_usize_of_nat(v___x_376_);
lean_inc_ref(v_a_345_);
v___x_382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(v_a_356_, v___x_380_, v___x_381_, v___x_378_, v_a_345_);
lean_dec(v_a_356_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_dec_ref(v___x_382_);
goto v___jp_357_;
}
else
{
lean_dec(v_a_355_);
lean_dec_ref(v_leanOpts_350_);
lean_dec_ref(v_a_345_);
return v___x_382_;
}
}
}
else
{
size_t v___x_383_; size_t v___x_384_; lean_object* v___x_385_; 
v___x_383_ = ((size_t)0ULL);
v___x_384_ = lean_usize_of_nat(v___x_376_);
lean_inc_ref(v_a_345_);
v___x_385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(v_a_356_, v___x_383_, v___x_384_, v___x_378_, v_a_345_);
lean_dec(v_a_356_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_dec_ref(v___x_385_);
goto v___jp_357_;
}
else
{
lean_dec(v_a_355_);
lean_dec_ref(v_leanOpts_350_);
lean_dec_ref(v_a_345_);
return v___x_385_;
}
}
}
v___jp_357_:
{
lean_object* v___x_358_; 
v___x_358_ = l_Lake_Workspace_updateAndMaterialize(v_a_355_, v_toUpdate_344_, v_leanOpts_350_, v_updateToolchain_351_, v_a_345_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_366_; 
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_366_ == 0)
{
lean_object* v_unused_367_; 
v_unused_367_ = lean_ctor_get(v___x_358_, 0);
lean_dec(v_unused_367_);
v___x_360_ = v___x_358_;
v_isShared_361_ = v_isSharedCheck_366_;
goto v_resetjp_359_;
}
else
{
lean_dec(v___x_358_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_366_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_364_; 
v___x_362_ = lean_box(0);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v___x_362_);
v___x_364_ = v___x_360_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_362_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
else
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
v_a_368_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___x_358_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_358_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_a_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
}
else
{
lean_object* v_a_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
lean_dec_ref(v_leanOpts_350_);
v_a_386_ = lean_ctor_get(v___x_354_, 1);
lean_inc(v_a_386_);
lean_dec_ref(v___x_354_);
v___x_387_ = lean_array_get_size(v_a_386_);
v___x_388_ = lean_nat_dec_lt(v___x_352_, v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; lean_object* v___x_390_; 
lean_dec(v_a_386_);
lean_dec_ref(v_a_345_);
v___x_389_ = lean_box(0);
v___x_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
return v___x_390_;
}
else
{
lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_391_ = lean_box(0);
v___x_392_ = lean_nat_dec_le(v___x_387_, v___x_387_);
if (v___x_392_ == 0)
{
if (v___x_388_ == 0)
{
lean_dec(v_a_386_);
lean_dec_ref(v_a_345_);
goto v___jp_347_;
}
else
{
size_t v___x_393_; size_t v___x_394_; lean_object* v___x_395_; 
v___x_393_ = ((size_t)0ULL);
v___x_394_ = lean_usize_of_nat(v___x_387_);
v___x_395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(v_a_386_, v___x_393_, v___x_394_, v___x_391_, v_a_345_);
lean_dec(v_a_386_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_dec_ref(v___x_395_);
goto v___jp_347_;
}
else
{
return v___x_395_;
}
}
}
else
{
size_t v___x_396_; size_t v___x_397_; lean_object* v___x_398_; 
v___x_396_ = ((size_t)0ULL);
v___x_397_ = lean_usize_of_nat(v___x_387_);
v___x_398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_loadWorkspace_spec__1(v_a_386_, v___x_396_, v___x_397_, v___x_391_, v_a_345_);
lean_dec(v_a_386_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_dec_ref(v___x_398_);
goto v___jp_347_;
}
else
{
return v___x_398_;
}
}
}
}
v___jp_347_:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_box(0);
v___x_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateManifest___boxed(lean_object* v_config_399_, lean_object* v_toUpdate_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lake_updateManifest(v_config_399_, v_toUpdate_400_, v_a_401_);
lean_dec(v_toUpdate_400_);
return v_res_403_;
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
