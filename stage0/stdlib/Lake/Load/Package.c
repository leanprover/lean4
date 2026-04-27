// Lean compiler output
// Module: Lake.Load.Package
// Imports: public import Lake.Load.Config public import Lake.Config.Package public import Lake.Config.LakefileConfig import Lake.Util.IO import Lake.Load.Lean import Lake.Load.Toml
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
lean_object* l_System_FilePath_extension(lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* l_Lake_resolvePath(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_searchPathRef;
lean_object* l_Lake_Env_leanSearchPath(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* l_Lake_loadLeanConfig(lean_object*, lean_object*);
lean_object* l_Lake_loadTomlConfig(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
extern lean_object* l_System_Platform_target;
static const lean_array_object l_Lake_mkPackage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_mkPackage___closed__0 = (const lean_object*)&l_Lake_mkPackage___closed__0_value;
static const lean_string_object l_Lake_mkPackage___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lake_mkPackage___closed__1 = (const lean_object*)&l_Lake_mkPackage___closed__1_value;
static const lean_string_object l_Lake_mkPackage___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ".tar.gz"};
static const lean_object* l_Lake_mkPackage___closed__2 = (const lean_object*)&l_Lake_mkPackage___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_mkPackage(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkPackage___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_configFileExists___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lake_configFileExists___closed__0 = (const lean_object*)&l_Lake_configFileExists___closed__0_value;
static const lean_string_object l_Lake_configFileExists___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "toml"};
static const lean_object* l_Lake_configFileExists___closed__1 = (const lean_object*)&l_Lake_configFileExists___closed__1_value;
LEAN_EXPORT uint8_t l_Lake_configFileExists(lean_object*);
LEAN_EXPORT lean_object* l_Lake_configFileExists___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_realConfigFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_realConfigFile___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_resolveConfigFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = ": configuration has unsupported file extension: "};
static const lean_object* l_Lake_resolveConfigFile___closed__0 = (const lean_object*)&l_Lake_resolveConfigFile___closed__0_value;
static const lean_ctor_object l_Lake_resolveConfigFile___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_resolveConfigFile___closed__1 = (const lean_object*)&l_Lake_resolveConfigFile___closed__1_value;
static const lean_ctor_object l_Lake_resolveConfigFile___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_resolveConfigFile___closed__2 = (const lean_object*)&l_Lake_resolveConfigFile___closed__2_value;
static const lean_string_object l_Lake_resolveConfigFile___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = ": configuration file not found: "};
static const lean_object* l_Lake_resolveConfigFile___closed__3 = (const lean_object*)&l_Lake_resolveConfigFile___closed__3_value;
static const lean_string_object l_Lake_resolveConfigFile___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lake_resolveConfigFile___closed__4 = (const lean_object*)&l_Lake_resolveConfigFile___closed__4_value;
static const lean_string_object l_Lake_resolveConfigFile___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " and "};
static const lean_object* l_Lake_resolveConfigFile___closed__5 = (const lean_object*)&l_Lake_resolveConfigFile___closed__5_value;
static const lean_string_object l_Lake_resolveConfigFile___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = " are both present; using "};
static const lean_object* l_Lake_resolveConfigFile___closed__6 = (const lean_object*)&l_Lake_resolveConfigFile___closed__6_value;
static const lean_string_object l_Lake_resolveConfigFile___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = ": no configuration file with a supported extension:\n"};
static const lean_object* l_Lake_resolveConfigFile___closed__7 = (const lean_object*)&l_Lake_resolveConfigFile___closed__7_value;
static const lean_string_object l_Lake_resolveConfigFile___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lake_resolveConfigFile___closed__8 = (const lean_object*)&l_Lake_resolveConfigFile___closed__8_value;
LEAN_EXPORT lean_object* l_Lake_resolveConfigFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveConfigFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadConfigFile___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadConfigFile___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadConfigFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadConfigFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_loadPackage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "[root]"};
static const lean_object* l_Lake_loadPackage___closed__0 = (const lean_object*)&l_Lake_loadPackage___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_loadPackage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackage___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkPackage(lean_object* v_loadCfg_5_, lean_object* v_fileCfg_6_, lean_object* v_wsIdx_7_){
_start:
{
lean_object* v_pkgDecl_8_; lean_object* v_config_9_; lean_object* v_relPkgDir_10_; lean_object* v_pkgDir_11_; lean_object* v_relConfigFile_12_; lean_object* v_configFile_13_; lean_object* v_relManifestFile_14_; lean_object* v_scope_15_; lean_object* v_remoteUrl_16_; lean_object* v_depConfigs_17_; lean_object* v_targetDecls_18_; lean_object* v_targetDeclMap_19_; lean_object* v_defaultTargets_20_; lean_object* v_scripts_21_; lean_object* v_defaultScripts_22_; lean_object* v_postUpdateHooks_23_; lean_object* v_testDriver_24_; lean_object* v_lintDriver_25_; lean_object* v_baseName_26_; lean_object* v_keyName_27_; lean_object* v_origName_28_; lean_object* v_buildArchive_29_; lean_object* v___x_30_; 
v_pkgDecl_8_ = lean_ctor_get(v_fileCfg_6_, 0);
lean_inc_ref(v_pkgDecl_8_);
v_config_9_ = lean_ctor_get(v_pkgDecl_8_, 3);
lean_inc_ref(v_config_9_);
v_relPkgDir_10_ = lean_ctor_get(v_loadCfg_5_, 5);
v_pkgDir_11_ = lean_ctor_get(v_loadCfg_5_, 6);
v_relConfigFile_12_ = lean_ctor_get(v_loadCfg_5_, 7);
v_configFile_13_ = lean_ctor_get(v_loadCfg_5_, 8);
v_relManifestFile_14_ = lean_ctor_get(v_loadCfg_5_, 10);
v_scope_15_ = lean_ctor_get(v_loadCfg_5_, 14);
v_remoteUrl_16_ = lean_ctor_get(v_loadCfg_5_, 15);
v_depConfigs_17_ = lean_ctor_get(v_fileCfg_6_, 1);
lean_inc_ref(v_depConfigs_17_);
v_targetDecls_18_ = lean_ctor_get(v_fileCfg_6_, 3);
lean_inc_ref(v_targetDecls_18_);
v_targetDeclMap_19_ = lean_ctor_get(v_fileCfg_6_, 4);
lean_inc(v_targetDeclMap_19_);
v_defaultTargets_20_ = lean_ctor_get(v_fileCfg_6_, 5);
lean_inc_ref(v_defaultTargets_20_);
v_scripts_21_ = lean_ctor_get(v_fileCfg_6_, 6);
lean_inc(v_scripts_21_);
v_defaultScripts_22_ = lean_ctor_get(v_fileCfg_6_, 7);
lean_inc_ref(v_defaultScripts_22_);
v_postUpdateHooks_23_ = lean_ctor_get(v_fileCfg_6_, 8);
lean_inc_ref(v_postUpdateHooks_23_);
v_testDriver_24_ = lean_ctor_get(v_fileCfg_6_, 9);
lean_inc_ref(v_testDriver_24_);
v_lintDriver_25_ = lean_ctor_get(v_fileCfg_6_, 10);
lean_inc_ref(v_lintDriver_25_);
lean_dec_ref(v_fileCfg_6_);
v_baseName_26_ = lean_ctor_get(v_pkgDecl_8_, 0);
lean_inc(v_baseName_26_);
v_keyName_27_ = lean_ctor_get(v_pkgDecl_8_, 1);
lean_inc(v_keyName_27_);
v_origName_28_ = lean_ctor_get(v_pkgDecl_8_, 2);
lean_inc(v_origName_28_);
lean_dec_ref(v_pkgDecl_8_);
v_buildArchive_29_ = lean_ctor_get(v_config_9_, 11);
v___x_30_ = ((lean_object*)(l_Lake_mkPackage___closed__0));
if (lean_obj_tag(v_buildArchive_29_) == 1)
{
lean_object* v_val_31_; lean_object* v___x_32_; 
v_val_31_ = lean_ctor_get(v_buildArchive_29_, 0);
lean_inc(v_val_31_);
lean_inc_ref(v_remoteUrl_16_);
lean_inc_ref(v_scope_15_);
lean_inc_ref(v_relManifestFile_14_);
lean_inc_ref(v_relConfigFile_12_);
lean_inc_ref(v_configFile_13_);
lean_inc_ref(v_relPkgDir_10_);
lean_inc_ref(v_pkgDir_11_);
v___x_32_ = lean_alloc_ctor(0, 23, 0);
lean_ctor_set(v___x_32_, 0, v_wsIdx_7_);
lean_ctor_set(v___x_32_, 1, v_baseName_26_);
lean_ctor_set(v___x_32_, 2, v_keyName_27_);
lean_ctor_set(v___x_32_, 3, v_origName_28_);
lean_ctor_set(v___x_32_, 4, v_pkgDir_11_);
lean_ctor_set(v___x_32_, 5, v_relPkgDir_10_);
lean_ctor_set(v___x_32_, 6, v_config_9_);
lean_ctor_set(v___x_32_, 7, v_configFile_13_);
lean_ctor_set(v___x_32_, 8, v_relConfigFile_12_);
lean_ctor_set(v___x_32_, 9, v_relManifestFile_14_);
lean_ctor_set(v___x_32_, 10, v_scope_15_);
lean_ctor_set(v___x_32_, 11, v_remoteUrl_16_);
lean_ctor_set(v___x_32_, 12, v_depConfigs_17_);
lean_ctor_set(v___x_32_, 13, v___x_30_);
lean_ctor_set(v___x_32_, 14, v_targetDecls_18_);
lean_ctor_set(v___x_32_, 15, v_targetDeclMap_19_);
lean_ctor_set(v___x_32_, 16, v_defaultTargets_20_);
lean_ctor_set(v___x_32_, 17, v_scripts_21_);
lean_ctor_set(v___x_32_, 18, v_defaultScripts_22_);
lean_ctor_set(v___x_32_, 19, v_postUpdateHooks_23_);
lean_ctor_set(v___x_32_, 20, v_val_31_);
lean_ctor_set(v___x_32_, 21, v_testDriver_24_);
lean_ctor_set(v___x_32_, 22, v_lintDriver_25_);
return v___x_32_;
}
else
{
uint8_t v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_33_ = 0;
lean_inc(v_baseName_26_);
v___x_34_ = l_Lean_Name_toString(v_baseName_26_, v___x_33_);
v___x_35_ = ((lean_object*)(l_Lake_mkPackage___closed__1));
v___x_36_ = lean_string_append(v___x_34_, v___x_35_);
v___x_37_ = l_System_Platform_target;
v___x_38_ = lean_string_append(v___x_36_, v___x_37_);
v___x_39_ = ((lean_object*)(l_Lake_mkPackage___closed__2));
v___x_40_ = lean_string_append(v___x_38_, v___x_39_);
lean_inc_ref(v_remoteUrl_16_);
lean_inc_ref(v_scope_15_);
lean_inc_ref(v_relManifestFile_14_);
lean_inc_ref(v_relConfigFile_12_);
lean_inc_ref(v_configFile_13_);
lean_inc_ref(v_relPkgDir_10_);
lean_inc_ref(v_pkgDir_11_);
v___x_41_ = lean_alloc_ctor(0, 23, 0);
lean_ctor_set(v___x_41_, 0, v_wsIdx_7_);
lean_ctor_set(v___x_41_, 1, v_baseName_26_);
lean_ctor_set(v___x_41_, 2, v_keyName_27_);
lean_ctor_set(v___x_41_, 3, v_origName_28_);
lean_ctor_set(v___x_41_, 4, v_pkgDir_11_);
lean_ctor_set(v___x_41_, 5, v_relPkgDir_10_);
lean_ctor_set(v___x_41_, 6, v_config_9_);
lean_ctor_set(v___x_41_, 7, v_configFile_13_);
lean_ctor_set(v___x_41_, 8, v_relConfigFile_12_);
lean_ctor_set(v___x_41_, 9, v_relManifestFile_14_);
lean_ctor_set(v___x_41_, 10, v_scope_15_);
lean_ctor_set(v___x_41_, 11, v_remoteUrl_16_);
lean_ctor_set(v___x_41_, 12, v_depConfigs_17_);
lean_ctor_set(v___x_41_, 13, v___x_30_);
lean_ctor_set(v___x_41_, 14, v_targetDecls_18_);
lean_ctor_set(v___x_41_, 15, v_targetDeclMap_19_);
lean_ctor_set(v___x_41_, 16, v_defaultTargets_20_);
lean_ctor_set(v___x_41_, 17, v_scripts_21_);
lean_ctor_set(v___x_41_, 18, v_defaultScripts_22_);
lean_ctor_set(v___x_41_, 19, v_postUpdateHooks_23_);
lean_ctor_set(v___x_41_, 20, v___x_40_);
lean_ctor_set(v___x_41_, 21, v_testDriver_24_);
lean_ctor_set(v___x_41_, 22, v_lintDriver_25_);
return v___x_41_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkPackage___boxed(lean_object* v_loadCfg_42_, lean_object* v_fileCfg_43_, lean_object* v_wsIdx_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lake_mkPackage(v_loadCfg_42_, v_fileCfg_43_, v_wsIdx_44_);
lean_dec_ref(v_loadCfg_42_);
return v_res_45_;
}
}
LEAN_EXPORT uint8_t l_Lake_configFileExists(lean_object* v_cfgFile_48_){
_start:
{
lean_object* v___x_50_; 
lean_inc_ref(v_cfgFile_48_);
v___x_50_ = l_System_FilePath_extension(v_cfgFile_48_);
if (lean_obj_tag(v___x_50_) == 0)
{
lean_object* v___x_51_; lean_object* v_leanFile_52_; uint8_t v___x_53_; 
v___x_51_ = ((lean_object*)(l_Lake_configFileExists___closed__0));
lean_inc_ref(v_cfgFile_48_);
v_leanFile_52_ = l_System_FilePath_addExtension(v_cfgFile_48_, v___x_51_);
v___x_53_ = l_System_FilePath_pathExists(v_leanFile_52_);
lean_dec_ref(v_leanFile_52_);
if (v___x_53_ == 0)
{
lean_object* v___x_54_; lean_object* v_tomlFile_55_; uint8_t v___x_56_; 
v___x_54_ = ((lean_object*)(l_Lake_configFileExists___closed__1));
v_tomlFile_55_ = l_System_FilePath_addExtension(v_cfgFile_48_, v___x_54_);
v___x_56_ = l_System_FilePath_pathExists(v_tomlFile_55_);
lean_dec_ref(v_tomlFile_55_);
return v___x_56_;
}
else
{
lean_dec_ref(v_cfgFile_48_);
return v___x_53_;
}
}
else
{
uint8_t v___x_57_; 
lean_dec_ref(v___x_50_);
v___x_57_ = l_System_FilePath_pathExists(v_cfgFile_48_);
lean_dec_ref(v_cfgFile_48_);
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_configFileExists___boxed(lean_object* v_cfgFile_58_, lean_object* v_a_59_){
_start:
{
uint8_t v_res_60_; lean_object* v_r_61_; 
v_res_60_ = l_Lake_configFileExists(v_cfgFile_58_);
v_r_61_ = lean_box(v_res_60_);
return v_r_61_;
}
}
LEAN_EXPORT lean_object* l_Lake_realConfigFile(lean_object* v_cfgFile_62_){
_start:
{
lean_object* v___x_64_; 
lean_inc_ref(v_cfgFile_62_);
v___x_64_ = l_System_FilePath_extension(v_cfgFile_62_);
if (lean_obj_tag(v___x_64_) == 0)
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; uint8_t v___x_70_; 
v___x_65_ = ((lean_object*)(l_Lake_configFileExists___closed__0));
lean_inc_ref(v_cfgFile_62_);
v___x_66_ = l_System_FilePath_addExtension(v_cfgFile_62_, v___x_65_);
v___x_67_ = l_Lake_resolvePath(v___x_66_);
v___x_68_ = lean_string_utf8_byte_size(v___x_67_);
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = lean_nat_dec_eq(v___x_68_, v___x_69_);
if (v___x_70_ == 0)
{
lean_dec_ref(v_cfgFile_62_);
return v___x_67_;
}
else
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec_ref(v___x_67_);
v___x_71_ = ((lean_object*)(l_Lake_configFileExists___closed__1));
v___x_72_ = l_System_FilePath_addExtension(v_cfgFile_62_, v___x_71_);
v___x_73_ = l_Lake_resolvePath(v___x_72_);
return v___x_73_;
}
}
else
{
lean_object* v___x_74_; 
lean_dec_ref(v___x_64_);
v___x_74_ = l_Lake_resolvePath(v_cfgFile_62_);
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_realConfigFile___boxed(lean_object* v_cfgFile_75_, lean_object* v_a_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lake_realConfigFile(v_cfgFile_75_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveConfigFile(lean_object* v_name_91_, lean_object* v_cfg_92_, lean_object* v_a_93_){
_start:
{
lean_object* v_configLang_x3f_95_; 
v_configLang_x3f_95_ = lean_ctor_get(v_cfg_92_, 9);
if (lean_obj_tag(v_configLang_x3f_95_) == 0)
{
lean_object* v_lakeEnv_96_; lean_object* v_lakeArgs_x3f_97_; lean_object* v_wsDir_98_; lean_object* v_pkgIdx_99_; lean_object* v_pkgName_100_; lean_object* v_relPkgDir_101_; lean_object* v_pkgDir_102_; lean_object* v_relConfigFile_103_; lean_object* v_configFile_104_; lean_object* v_relManifestFile_105_; lean_object* v_packageOverrides_106_; lean_object* v_lakeOpts_107_; lean_object* v_leanOpts_108_; uint8_t v_reconfigure_109_; uint8_t v_updateDeps_110_; uint8_t v_updateToolchain_111_; lean_object* v_scope_112_; lean_object* v_remoteUrl_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_202_; 
v_lakeEnv_96_ = lean_ctor_get(v_cfg_92_, 0);
v_lakeArgs_x3f_97_ = lean_ctor_get(v_cfg_92_, 1);
v_wsDir_98_ = lean_ctor_get(v_cfg_92_, 2);
v_pkgIdx_99_ = lean_ctor_get(v_cfg_92_, 3);
v_pkgName_100_ = lean_ctor_get(v_cfg_92_, 4);
v_relPkgDir_101_ = lean_ctor_get(v_cfg_92_, 5);
v_pkgDir_102_ = lean_ctor_get(v_cfg_92_, 6);
v_relConfigFile_103_ = lean_ctor_get(v_cfg_92_, 7);
v_configFile_104_ = lean_ctor_get(v_cfg_92_, 8);
v_relManifestFile_105_ = lean_ctor_get(v_cfg_92_, 10);
v_packageOverrides_106_ = lean_ctor_get(v_cfg_92_, 11);
v_lakeOpts_107_ = lean_ctor_get(v_cfg_92_, 12);
v_leanOpts_108_ = lean_ctor_get(v_cfg_92_, 13);
v_reconfigure_109_ = lean_ctor_get_uint8(v_cfg_92_, sizeof(void*)*16);
v_updateDeps_110_ = lean_ctor_get_uint8(v_cfg_92_, sizeof(void*)*16 + 1);
v_updateToolchain_111_ = lean_ctor_get_uint8(v_cfg_92_, sizeof(void*)*16 + 2);
v_scope_112_ = lean_ctor_get(v_cfg_92_, 14);
v_remoteUrl_113_ = lean_ctor_get(v_cfg_92_, 15);
v_isSharedCheck_202_ = !lean_is_exclusive(v_cfg_92_);
if (v_isSharedCheck_202_ == 0)
{
lean_object* v_unused_203_; 
v_unused_203_ = lean_ctor_get(v_cfg_92_, 9);
lean_dec(v_unused_203_);
v___x_115_ = v_cfg_92_;
v_isShared_116_ = v_isSharedCheck_202_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_remoteUrl_113_);
lean_inc(v_scope_112_);
lean_inc(v_leanOpts_108_);
lean_inc(v_lakeOpts_107_);
lean_inc(v_packageOverrides_106_);
lean_inc(v_relManifestFile_105_);
lean_inc(v_configFile_104_);
lean_inc(v_relConfigFile_103_);
lean_inc(v_pkgDir_102_);
lean_inc(v_relPkgDir_101_);
lean_inc(v_pkgName_100_);
lean_inc(v_pkgIdx_99_);
lean_inc(v_wsDir_98_);
lean_inc(v_lakeArgs_x3f_97_);
lean_inc(v_lakeEnv_96_);
lean_dec(v_cfg_92_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_202_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_117_; 
lean_inc_ref(v_relConfigFile_103_);
v___x_117_ = l_System_FilePath_extension(v_relConfigFile_103_);
if (lean_obj_tag(v___x_117_) == 1)
{
lean_object* v_val_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v_val_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_val_118_);
lean_dec_ref(v___x_117_);
lean_inc_ref(v_configFile_104_);
v___x_119_ = l_Lake_resolvePath(v_configFile_104_);
v___x_120_ = lean_string_utf8_byte_size(v___x_119_);
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_nat_dec_eq(v___x_120_, v___x_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; uint8_t v___x_124_; 
lean_dec_ref(v_configFile_104_);
v___x_123_ = ((lean_object*)(l_Lake_configFileExists___closed__0));
v___x_124_ = lean_string_dec_eq(v_val_118_, v___x_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_125_ = ((lean_object*)(l_Lake_configFileExists___closed__1));
v___x_126_ = lean_string_dec_eq(v_val_118_, v___x_125_);
lean_dec(v_val_118_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
lean_del_object(v___x_115_);
lean_dec_ref(v_remoteUrl_113_);
lean_dec_ref(v_scope_112_);
lean_dec_ref(v_leanOpts_108_);
lean_dec(v_lakeOpts_107_);
lean_dec_ref(v_packageOverrides_106_);
lean_dec_ref(v_relManifestFile_105_);
lean_dec_ref(v_relConfigFile_103_);
lean_dec_ref(v_pkgDir_102_);
lean_dec_ref(v_relPkgDir_101_);
lean_dec(v_pkgName_100_);
lean_dec(v_pkgIdx_99_);
lean_dec_ref(v_wsDir_98_);
lean_dec(v_lakeArgs_x3f_97_);
lean_dec_ref(v_lakeEnv_96_);
v___x_127_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__0));
v___x_128_ = lean_string_append(v_name_91_, v___x_127_);
v___x_129_ = lean_string_append(v___x_128_, v___x_119_);
lean_dec_ref(v___x_119_);
v___x_130_ = 3;
v___x_131_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_131_, 0, v___x_129_);
lean_ctor_set_uint8(v___x_131_, sizeof(void*)*1, v___x_130_);
v___x_132_ = lean_array_get_size(v_a_93_);
v___x_133_ = lean_array_push(v_a_93_, v___x_131_);
v___x_134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_132_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
return v___x_134_;
}
else
{
lean_object* v___x_135_; lean_object* v___x_137_; 
lean_dec_ref(v_name_91_);
v___x_135_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__1));
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 9, v___x_135_);
lean_ctor_set(v___x_115_, 8, v___x_119_);
v___x_137_ = v___x_115_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_lakeEnv_96_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_lakeArgs_x3f_97_);
lean_ctor_set(v_reuseFailAlloc_139_, 2, v_wsDir_98_);
lean_ctor_set(v_reuseFailAlloc_139_, 3, v_pkgIdx_99_);
lean_ctor_set(v_reuseFailAlloc_139_, 4, v_pkgName_100_);
lean_ctor_set(v_reuseFailAlloc_139_, 5, v_relPkgDir_101_);
lean_ctor_set(v_reuseFailAlloc_139_, 6, v_pkgDir_102_);
lean_ctor_set(v_reuseFailAlloc_139_, 7, v_relConfigFile_103_);
lean_ctor_set(v_reuseFailAlloc_139_, 8, v___x_119_);
lean_ctor_set(v_reuseFailAlloc_139_, 9, v___x_135_);
lean_ctor_set(v_reuseFailAlloc_139_, 10, v_relManifestFile_105_);
lean_ctor_set(v_reuseFailAlloc_139_, 11, v_packageOverrides_106_);
lean_ctor_set(v_reuseFailAlloc_139_, 12, v_lakeOpts_107_);
lean_ctor_set(v_reuseFailAlloc_139_, 13, v_leanOpts_108_);
lean_ctor_set(v_reuseFailAlloc_139_, 14, v_scope_112_);
lean_ctor_set(v_reuseFailAlloc_139_, 15, v_remoteUrl_113_);
lean_ctor_set_uint8(v_reuseFailAlloc_139_, sizeof(void*)*16, v_reconfigure_109_);
lean_ctor_set_uint8(v_reuseFailAlloc_139_, sizeof(void*)*16 + 1, v_updateDeps_110_);
lean_ctor_set_uint8(v_reuseFailAlloc_139_, sizeof(void*)*16 + 2, v_updateToolchain_111_);
v___x_137_ = v_reuseFailAlloc_139_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
lean_object* v___x_138_; 
v___x_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v_a_93_);
return v___x_138_;
}
}
}
else
{
lean_object* v___x_140_; lean_object* v___x_142_; 
lean_dec(v_val_118_);
lean_dec_ref(v_name_91_);
v___x_140_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__2));
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 9, v___x_140_);
lean_ctor_set(v___x_115_, 8, v___x_119_);
v___x_142_ = v___x_115_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_lakeEnv_96_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_lakeArgs_x3f_97_);
lean_ctor_set(v_reuseFailAlloc_144_, 2, v_wsDir_98_);
lean_ctor_set(v_reuseFailAlloc_144_, 3, v_pkgIdx_99_);
lean_ctor_set(v_reuseFailAlloc_144_, 4, v_pkgName_100_);
lean_ctor_set(v_reuseFailAlloc_144_, 5, v_relPkgDir_101_);
lean_ctor_set(v_reuseFailAlloc_144_, 6, v_pkgDir_102_);
lean_ctor_set(v_reuseFailAlloc_144_, 7, v_relConfigFile_103_);
lean_ctor_set(v_reuseFailAlloc_144_, 8, v___x_119_);
lean_ctor_set(v_reuseFailAlloc_144_, 9, v___x_140_);
lean_ctor_set(v_reuseFailAlloc_144_, 10, v_relManifestFile_105_);
lean_ctor_set(v_reuseFailAlloc_144_, 11, v_packageOverrides_106_);
lean_ctor_set(v_reuseFailAlloc_144_, 12, v_lakeOpts_107_);
lean_ctor_set(v_reuseFailAlloc_144_, 13, v_leanOpts_108_);
lean_ctor_set(v_reuseFailAlloc_144_, 14, v_scope_112_);
lean_ctor_set(v_reuseFailAlloc_144_, 15, v_remoteUrl_113_);
lean_ctor_set_uint8(v_reuseFailAlloc_144_, sizeof(void*)*16, v_reconfigure_109_);
lean_ctor_set_uint8(v_reuseFailAlloc_144_, sizeof(void*)*16 + 1, v_updateDeps_110_);
lean_ctor_set_uint8(v_reuseFailAlloc_144_, sizeof(void*)*16 + 2, v_updateToolchain_111_);
v___x_142_ = v_reuseFailAlloc_144_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_143_; 
v___x_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v_a_93_);
return v___x_143_;
}
}
}
else
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
lean_dec_ref(v___x_119_);
lean_dec(v_val_118_);
lean_del_object(v___x_115_);
lean_dec_ref(v_remoteUrl_113_);
lean_dec_ref(v_scope_112_);
lean_dec_ref(v_leanOpts_108_);
lean_dec(v_lakeOpts_107_);
lean_dec_ref(v_packageOverrides_106_);
lean_dec_ref(v_relManifestFile_105_);
lean_dec_ref(v_relConfigFile_103_);
lean_dec_ref(v_pkgDir_102_);
lean_dec_ref(v_relPkgDir_101_);
lean_dec(v_pkgName_100_);
lean_dec(v_pkgIdx_99_);
lean_dec_ref(v_wsDir_98_);
lean_dec(v_lakeArgs_x3f_97_);
lean_dec_ref(v_lakeEnv_96_);
v___x_145_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__3));
v___x_146_ = lean_string_append(v_name_91_, v___x_145_);
v___x_147_ = lean_string_append(v___x_146_, v_configFile_104_);
lean_dec_ref(v_configFile_104_);
v___x_148_ = 3;
v___x_149_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_149_, 0, v___x_147_);
lean_ctor_set_uint8(v___x_149_, sizeof(void*)*1, v___x_148_);
v___x_150_ = lean_array_get_size(v_a_93_);
v___x_151_ = lean_array_push(v_a_93_, v___x_149_);
v___x_152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_150_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
return v___x_152_;
}
}
else
{
lean_object* v___x_153_; lean_object* v_relLeanFile_154_; lean_object* v_leanFile_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v_relTomlFile_158_; lean_object* v_tomlFile_159_; lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
lean_dec(v___x_117_);
lean_dec_ref(v_configFile_104_);
v___x_153_ = ((lean_object*)(l_Lake_configFileExists___closed__0));
lean_inc_ref(v_relConfigFile_103_);
v_relLeanFile_154_ = l_System_FilePath_addExtension(v_relConfigFile_103_, v___x_153_);
lean_inc_ref(v_relLeanFile_154_);
lean_inc_ref_n(v_pkgDir_102_, 2);
v_leanFile_155_ = l_Lake_joinRelative(v_pkgDir_102_, v_relLeanFile_154_);
lean_inc_ref(v_leanFile_155_);
v___x_156_ = l_Lake_resolvePath(v_leanFile_155_);
v___x_157_ = ((lean_object*)(l_Lake_configFileExists___closed__1));
v_relTomlFile_158_ = l_System_FilePath_addExtension(v_relConfigFile_103_, v___x_157_);
lean_inc_ref(v_relTomlFile_158_);
v_tomlFile_159_ = l_Lake_joinRelative(v_pkgDir_102_, v_relTomlFile_158_);
v___x_160_ = lean_string_utf8_byte_size(v___x_156_);
v___x_161_ = lean_unsigned_to_nat(0u);
v___x_162_ = lean_nat_dec_eq(v___x_160_, v___x_161_);
if (v___x_162_ == 0)
{
uint8_t v___x_163_; lean_object* v___y_165_; 
lean_dec_ref(v_leanFile_155_);
v___x_163_ = l_System_FilePath_pathExists(v_tomlFile_159_);
lean_dec_ref(v_tomlFile_159_);
if (v___x_163_ == 0)
{
lean_dec_ref(v_relTomlFile_158_);
lean_dec_ref(v_name_91_);
v___y_165_ = v_a_93_;
goto v___jp_164_;
}
else
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_171_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__4));
v___x_172_ = lean_string_append(v_name_91_, v___x_171_);
v___x_173_ = lean_string_append(v___x_172_, v_relLeanFile_154_);
v___x_174_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__5));
v___x_175_ = lean_string_append(v___x_173_, v___x_174_);
v___x_176_ = lean_string_append(v___x_175_, v_relTomlFile_158_);
lean_dec_ref(v_relTomlFile_158_);
v___x_177_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__6));
v___x_178_ = lean_string_append(v___x_176_, v___x_177_);
v___x_179_ = lean_string_append(v___x_178_, v_relLeanFile_154_);
v___x_180_ = 1;
v___x_181_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_181_, 0, v___x_179_);
lean_ctor_set_uint8(v___x_181_, sizeof(void*)*1, v___x_180_);
v___x_182_ = lean_array_push(v_a_93_, v___x_181_);
v___y_165_ = v___x_182_;
goto v___jp_164_;
}
v___jp_164_:
{
lean_object* v___x_166_; lean_object* v___x_168_; 
v___x_166_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__2));
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 9, v___x_166_);
lean_ctor_set(v___x_115_, 8, v___x_156_);
lean_ctor_set(v___x_115_, 7, v_relLeanFile_154_);
v___x_168_ = v___x_115_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_lakeEnv_96_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_lakeArgs_x3f_97_);
lean_ctor_set(v_reuseFailAlloc_170_, 2, v_wsDir_98_);
lean_ctor_set(v_reuseFailAlloc_170_, 3, v_pkgIdx_99_);
lean_ctor_set(v_reuseFailAlloc_170_, 4, v_pkgName_100_);
lean_ctor_set(v_reuseFailAlloc_170_, 5, v_relPkgDir_101_);
lean_ctor_set(v_reuseFailAlloc_170_, 6, v_pkgDir_102_);
lean_ctor_set(v_reuseFailAlloc_170_, 7, v_relLeanFile_154_);
lean_ctor_set(v_reuseFailAlloc_170_, 8, v___x_156_);
lean_ctor_set(v_reuseFailAlloc_170_, 9, v___x_166_);
lean_ctor_set(v_reuseFailAlloc_170_, 10, v_relManifestFile_105_);
lean_ctor_set(v_reuseFailAlloc_170_, 11, v_packageOverrides_106_);
lean_ctor_set(v_reuseFailAlloc_170_, 12, v_lakeOpts_107_);
lean_ctor_set(v_reuseFailAlloc_170_, 13, v_leanOpts_108_);
lean_ctor_set(v_reuseFailAlloc_170_, 14, v_scope_112_);
lean_ctor_set(v_reuseFailAlloc_170_, 15, v_remoteUrl_113_);
lean_ctor_set_uint8(v_reuseFailAlloc_170_, sizeof(void*)*16, v_reconfigure_109_);
lean_ctor_set_uint8(v_reuseFailAlloc_170_, sizeof(void*)*16 + 1, v_updateDeps_110_);
lean_ctor_set_uint8(v_reuseFailAlloc_170_, sizeof(void*)*16 + 2, v_updateToolchain_111_);
v___x_168_ = v_reuseFailAlloc_170_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
lean_object* v___x_169_; 
v___x_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v___y_165_);
return v___x_169_;
}
}
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
lean_dec_ref(v___x_156_);
lean_dec_ref(v_relLeanFile_154_);
lean_inc_ref(v_tomlFile_159_);
v___x_183_ = l_Lake_resolvePath(v_tomlFile_159_);
v___x_184_ = lean_string_utf8_byte_size(v___x_183_);
v___x_185_ = lean_nat_dec_eq(v___x_184_, v___x_161_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; lean_object* v___x_188_; 
lean_dec_ref(v_tomlFile_159_);
lean_dec_ref(v_leanFile_155_);
lean_dec_ref(v_name_91_);
v___x_186_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__1));
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 9, v___x_186_);
lean_ctor_set(v___x_115_, 8, v___x_183_);
lean_ctor_set(v___x_115_, 7, v_relTomlFile_158_);
v___x_188_ = v___x_115_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_lakeEnv_96_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v_lakeArgs_x3f_97_);
lean_ctor_set(v_reuseFailAlloc_190_, 2, v_wsDir_98_);
lean_ctor_set(v_reuseFailAlloc_190_, 3, v_pkgIdx_99_);
lean_ctor_set(v_reuseFailAlloc_190_, 4, v_pkgName_100_);
lean_ctor_set(v_reuseFailAlloc_190_, 5, v_relPkgDir_101_);
lean_ctor_set(v_reuseFailAlloc_190_, 6, v_pkgDir_102_);
lean_ctor_set(v_reuseFailAlloc_190_, 7, v_relTomlFile_158_);
lean_ctor_set(v_reuseFailAlloc_190_, 8, v___x_183_);
lean_ctor_set(v_reuseFailAlloc_190_, 9, v___x_186_);
lean_ctor_set(v_reuseFailAlloc_190_, 10, v_relManifestFile_105_);
lean_ctor_set(v_reuseFailAlloc_190_, 11, v_packageOverrides_106_);
lean_ctor_set(v_reuseFailAlloc_190_, 12, v_lakeOpts_107_);
lean_ctor_set(v_reuseFailAlloc_190_, 13, v_leanOpts_108_);
lean_ctor_set(v_reuseFailAlloc_190_, 14, v_scope_112_);
lean_ctor_set(v_reuseFailAlloc_190_, 15, v_remoteUrl_113_);
lean_ctor_set_uint8(v_reuseFailAlloc_190_, sizeof(void*)*16, v_reconfigure_109_);
lean_ctor_set_uint8(v_reuseFailAlloc_190_, sizeof(void*)*16 + 1, v_updateDeps_110_);
lean_ctor_set_uint8(v_reuseFailAlloc_190_, sizeof(void*)*16 + 2, v_updateToolchain_111_);
v___x_188_ = v_reuseFailAlloc_190_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_189_; 
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v_a_93_);
return v___x_189_;
}
}
else
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
lean_dec_ref(v___x_183_);
lean_dec_ref(v_relTomlFile_158_);
lean_del_object(v___x_115_);
lean_dec_ref(v_remoteUrl_113_);
lean_dec_ref(v_scope_112_);
lean_dec_ref(v_leanOpts_108_);
lean_dec(v_lakeOpts_107_);
lean_dec_ref(v_packageOverrides_106_);
lean_dec_ref(v_relManifestFile_105_);
lean_dec_ref(v_pkgDir_102_);
lean_dec_ref(v_relPkgDir_101_);
lean_dec(v_pkgName_100_);
lean_dec(v_pkgIdx_99_);
lean_dec_ref(v_wsDir_98_);
lean_dec(v_lakeArgs_x3f_97_);
lean_dec_ref(v_lakeEnv_96_);
v___x_191_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__7));
v___x_192_ = lean_string_append(v_name_91_, v___x_191_);
v___x_193_ = lean_string_append(v___x_192_, v_leanFile_155_);
lean_dec_ref(v_leanFile_155_);
v___x_194_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__8));
v___x_195_ = lean_string_append(v___x_193_, v___x_194_);
v___x_196_ = lean_string_append(v___x_195_, v_tomlFile_159_);
lean_dec_ref(v_tomlFile_159_);
v___x_197_ = 3;
v___x_198_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_198_, 0, v___x_196_);
lean_ctor_set_uint8(v___x_198_, sizeof(void*)*1, v___x_197_);
v___x_199_ = lean_array_get_size(v_a_93_);
v___x_200_ = lean_array_push(v_a_93_, v___x_198_);
v___x_201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_199_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
return v___x_201_;
}
}
}
}
}
else
{
lean_object* v_lakeEnv_204_; lean_object* v_lakeArgs_x3f_205_; lean_object* v_wsDir_206_; lean_object* v_pkgIdx_207_; lean_object* v_pkgName_208_; lean_object* v_relPkgDir_209_; lean_object* v_pkgDir_210_; lean_object* v_relConfigFile_211_; lean_object* v_configFile_212_; lean_object* v_relManifestFile_213_; lean_object* v_packageOverrides_214_; lean_object* v_lakeOpts_215_; lean_object* v_leanOpts_216_; uint8_t v_reconfigure_217_; uint8_t v_updateDeps_218_; uint8_t v_updateToolchain_219_; lean_object* v_scope_220_; lean_object* v_remoteUrl_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_241_; 
lean_inc_ref(v_configLang_x3f_95_);
v_lakeEnv_204_ = lean_ctor_get(v_cfg_92_, 0);
v_lakeArgs_x3f_205_ = lean_ctor_get(v_cfg_92_, 1);
v_wsDir_206_ = lean_ctor_get(v_cfg_92_, 2);
v_pkgIdx_207_ = lean_ctor_get(v_cfg_92_, 3);
v_pkgName_208_ = lean_ctor_get(v_cfg_92_, 4);
v_relPkgDir_209_ = lean_ctor_get(v_cfg_92_, 5);
v_pkgDir_210_ = lean_ctor_get(v_cfg_92_, 6);
v_relConfigFile_211_ = lean_ctor_get(v_cfg_92_, 7);
v_configFile_212_ = lean_ctor_get(v_cfg_92_, 8);
v_relManifestFile_213_ = lean_ctor_get(v_cfg_92_, 10);
v_packageOverrides_214_ = lean_ctor_get(v_cfg_92_, 11);
v_lakeOpts_215_ = lean_ctor_get(v_cfg_92_, 12);
v_leanOpts_216_ = lean_ctor_get(v_cfg_92_, 13);
v_reconfigure_217_ = lean_ctor_get_uint8(v_cfg_92_, sizeof(void*)*16);
v_updateDeps_218_ = lean_ctor_get_uint8(v_cfg_92_, sizeof(void*)*16 + 1);
v_updateToolchain_219_ = lean_ctor_get_uint8(v_cfg_92_, sizeof(void*)*16 + 2);
v_scope_220_ = lean_ctor_get(v_cfg_92_, 14);
v_remoteUrl_221_ = lean_ctor_get(v_cfg_92_, 15);
v_isSharedCheck_241_ = !lean_is_exclusive(v_cfg_92_);
if (v_isSharedCheck_241_ == 0)
{
lean_object* v_unused_242_; 
v_unused_242_ = lean_ctor_get(v_cfg_92_, 9);
lean_dec(v_unused_242_);
v___x_223_ = v_cfg_92_;
v_isShared_224_ = v_isSharedCheck_241_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_remoteUrl_221_);
lean_inc(v_scope_220_);
lean_inc(v_leanOpts_216_);
lean_inc(v_lakeOpts_215_);
lean_inc(v_packageOverrides_214_);
lean_inc(v_relManifestFile_213_);
lean_inc(v_configFile_212_);
lean_inc(v_relConfigFile_211_);
lean_inc(v_pkgDir_210_);
lean_inc(v_relPkgDir_209_);
lean_inc(v_pkgName_208_);
lean_inc(v_pkgIdx_207_);
lean_inc(v_wsDir_206_);
lean_inc(v_lakeArgs_x3f_205_);
lean_inc(v_lakeEnv_204_);
lean_dec(v_cfg_92_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_241_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
lean_inc_ref(v_configFile_212_);
v___x_225_ = l_Lake_resolvePath(v_configFile_212_);
v___x_226_ = lean_string_utf8_byte_size(v___x_225_);
v___x_227_ = lean_unsigned_to_nat(0u);
v___x_228_ = lean_nat_dec_eq(v___x_226_, v___x_227_);
if (v___x_228_ == 0)
{
lean_object* v___x_230_; 
lean_dec_ref(v_configFile_212_);
lean_dec_ref(v_name_91_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 8, v___x_225_);
v___x_230_ = v___x_223_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_lakeEnv_204_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v_lakeArgs_x3f_205_);
lean_ctor_set(v_reuseFailAlloc_232_, 2, v_wsDir_206_);
lean_ctor_set(v_reuseFailAlloc_232_, 3, v_pkgIdx_207_);
lean_ctor_set(v_reuseFailAlloc_232_, 4, v_pkgName_208_);
lean_ctor_set(v_reuseFailAlloc_232_, 5, v_relPkgDir_209_);
lean_ctor_set(v_reuseFailAlloc_232_, 6, v_pkgDir_210_);
lean_ctor_set(v_reuseFailAlloc_232_, 7, v_relConfigFile_211_);
lean_ctor_set(v_reuseFailAlloc_232_, 8, v___x_225_);
lean_ctor_set(v_reuseFailAlloc_232_, 9, v_configLang_x3f_95_);
lean_ctor_set(v_reuseFailAlloc_232_, 10, v_relManifestFile_213_);
lean_ctor_set(v_reuseFailAlloc_232_, 11, v_packageOverrides_214_);
lean_ctor_set(v_reuseFailAlloc_232_, 12, v_lakeOpts_215_);
lean_ctor_set(v_reuseFailAlloc_232_, 13, v_leanOpts_216_);
lean_ctor_set(v_reuseFailAlloc_232_, 14, v_scope_220_);
lean_ctor_set(v_reuseFailAlloc_232_, 15, v_remoteUrl_221_);
lean_ctor_set_uint8(v_reuseFailAlloc_232_, sizeof(void*)*16, v_reconfigure_217_);
lean_ctor_set_uint8(v_reuseFailAlloc_232_, sizeof(void*)*16 + 1, v_updateDeps_218_);
lean_ctor_set_uint8(v_reuseFailAlloc_232_, sizeof(void*)*16 + 2, v_updateToolchain_219_);
v___x_230_ = v_reuseFailAlloc_232_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_231_; 
v___x_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v_a_93_);
return v___x_231_;
}
}
else
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
lean_dec_ref(v___x_225_);
lean_del_object(v___x_223_);
lean_dec_ref(v_remoteUrl_221_);
lean_dec_ref(v_scope_220_);
lean_dec_ref(v_leanOpts_216_);
lean_dec(v_lakeOpts_215_);
lean_dec_ref(v_packageOverrides_214_);
lean_dec_ref(v_relManifestFile_213_);
lean_dec_ref(v_relConfigFile_211_);
lean_dec_ref(v_pkgDir_210_);
lean_dec_ref(v_relPkgDir_209_);
lean_dec(v_pkgName_208_);
lean_dec(v_pkgIdx_207_);
lean_dec_ref(v_wsDir_206_);
lean_dec(v_lakeArgs_x3f_205_);
lean_dec_ref(v_configLang_x3f_95_);
lean_dec_ref(v_lakeEnv_204_);
v___x_233_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__3));
v___x_234_ = lean_string_append(v_name_91_, v___x_233_);
v___x_235_ = lean_string_append(v___x_234_, v_configFile_212_);
lean_dec_ref(v_configFile_212_);
v___x_236_ = 3;
v___x_237_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_237_, 0, v___x_235_);
lean_ctor_set_uint8(v___x_237_, sizeof(void*)*1, v___x_236_);
v___x_238_ = lean_array_get_size(v_a_93_);
v___x_239_ = lean_array_push(v_a_93_, v___x_237_);
v___x_240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_238_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
return v___x_240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveConfigFile___boxed(lean_object* v_name_243_, lean_object* v_cfg_244_, lean_object* v_a_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lake_resolveConfigFile(v_name_243_, v_cfg_244_, v_a_245_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadConfigFile___redArg(lean_object* v_cfg_248_, lean_object* v_a_249_){
_start:
{
lean_object* v_configLang_x3f_251_; lean_object* v_val_252_; uint8_t v___x_253_; 
v_configLang_x3f_251_ = lean_ctor_get(v_cfg_248_, 9);
v_val_252_ = lean_ctor_get(v_configLang_x3f_251_, 0);
v___x_253_ = lean_unbox(v_val_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; 
v___x_254_ = l_Lake_loadLeanConfig(v_cfg_248_, v_a_249_);
return v___x_254_;
}
else
{
lean_object* v___x_255_; 
v___x_255_ = l_Lake_loadTomlConfig(v_cfg_248_, v_a_249_);
return v___x_255_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadConfigFile___redArg___boxed(lean_object* v_cfg_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lake_loadConfigFile___redArg(v_cfg_256_, v_a_257_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadConfigFile(lean_object* v_cfg_260_, lean_object* v_h_261_, lean_object* v_a_262_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Lake_loadConfigFile___redArg(v_cfg_260_, v_a_262_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadConfigFile___boxed(lean_object* v_cfg_265_, lean_object* v_h_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lake_loadConfigFile(v_cfg_265_, v_h_266_, v_a_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackage(lean_object* v_cfg_271_, lean_object* v_a_272_){
_start:
{
lean_object* v_lakeEnv_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v_lakeEnv_274_ = lean_ctor_get(v_cfg_271_, 0);
v___x_275_ = l_Lean_searchPathRef;
v___x_276_ = l_Lake_Env_leanSearchPath(v_lakeEnv_274_);
v___x_277_ = lean_st_ref_set(v___x_275_, v___x_276_);
v___x_278_ = ((lean_object*)(l_Lake_loadPackage___closed__0));
v___x_279_ = l_Lake_resolveConfigFile(v___x_278_, v_cfg_271_, v_a_272_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v_a_280_; lean_object* v_a_281_; lean_object* v___x_282_; 
v_a_280_ = lean_ctor_get(v___x_279_, 0);
lean_inc_n(v_a_280_, 2);
v_a_281_ = lean_ctor_get(v___x_279_, 1);
lean_inc(v_a_281_);
lean_dec_ref(v___x_279_);
v___x_282_ = l_Lake_loadConfigFile___redArg(v_a_280_, v_a_281_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_293_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
v_a_284_ = lean_ctor_get(v___x_282_, 1);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_293_ == 0)
{
v___x_286_ = v___x_282_;
v_isShared_287_ = v_isSharedCheck_293_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_inc(v_a_283_);
lean_dec(v___x_282_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_293_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v_pkgIdx_288_; lean_object* v___x_289_; lean_object* v___x_291_; 
v_pkgIdx_288_ = lean_ctor_get(v_a_280_, 3);
lean_inc(v_pkgIdx_288_);
v___x_289_ = l_Lake_mkPackage(v_a_280_, v_a_283_, v_pkgIdx_288_);
lean_dec(v_a_280_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_289_);
v___x_291_ = v___x_286_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_289_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_a_284_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
else
{
lean_object* v_a_294_; lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_302_; 
lean_dec(v_a_280_);
v_a_294_ = lean_ctor_get(v___x_282_, 0);
v_a_295_ = lean_ctor_get(v___x_282_, 1);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_302_ == 0)
{
v___x_297_ = v___x_282_;
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_inc(v_a_294_);
lean_dec(v___x_282_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_298_ == 0)
{
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_a_294_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v_a_295_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
else
{
lean_object* v_a_303_; lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
v_a_303_ = lean_ctor_get(v___x_279_, 0);
v_a_304_ = lean_ctor_get(v___x_279_, 1);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_311_ == 0)
{
v___x_306_ = v___x_279_;
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_inc(v_a_303_);
lean_dec(v___x_279_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_307_ == 0)
{
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_a_303_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_a_304_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackage___boxed(lean_object* v_cfg_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lake_loadPackage(v_cfg_312_, v_a_313_);
return v_res_315_;
}
}
lean_object* runtime_initialize_Lake_Load_Config(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Package(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_LakefileConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_IO(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Lean(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Toml(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Load_Package(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Load_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_LakefileConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Toml(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Load_Package(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Load_Config(uint8_t builtin);
lean_object* initialize_Lake_Config_Package(uint8_t builtin);
lean_object* initialize_Lake_Config_LakefileConfig(uint8_t builtin);
lean_object* initialize_Lake_Util_IO(uint8_t builtin);
lean_object* initialize_Lake_Load_Lean(uint8_t builtin);
lean_object* initialize_Lake_Load_Toml(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Package(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Load_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_LakefileConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Toml(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Load_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Load_Package(builtin);
}
#ifdef __cplusplus
}
#endif
