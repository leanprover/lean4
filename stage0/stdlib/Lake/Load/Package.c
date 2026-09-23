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
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
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
v___x_32_ = lean_alloc_ctor(0, 24, 0);
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
lean_ctor_set(v___x_32_, 14, v___x_30_);
lean_ctor_set(v___x_32_, 15, v_targetDecls_18_);
lean_ctor_set(v___x_32_, 16, v_targetDeclMap_19_);
lean_ctor_set(v___x_32_, 17, v_defaultTargets_20_);
lean_ctor_set(v___x_32_, 18, v_scripts_21_);
lean_ctor_set(v___x_32_, 19, v_defaultScripts_22_);
lean_ctor_set(v___x_32_, 20, v_postUpdateHooks_23_);
lean_ctor_set(v___x_32_, 21, v_val_31_);
lean_ctor_set(v___x_32_, 22, v_testDriver_24_);
lean_ctor_set(v___x_32_, 23, v_lintDriver_25_);
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
v___x_41_ = lean_alloc_ctor(0, 24, 0);
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
lean_ctor_set(v___x_41_, 14, v___x_30_);
lean_ctor_set(v___x_41_, 15, v_targetDecls_18_);
lean_ctor_set(v___x_41_, 16, v_targetDeclMap_19_);
lean_ctor_set(v___x_41_, 17, v_defaultTargets_20_);
lean_ctor_set(v___x_41_, 18, v_scripts_21_);
lean_ctor_set(v___x_41_, 19, v_defaultScripts_22_);
lean_ctor_set(v___x_41_, 20, v_postUpdateHooks_23_);
lean_ctor_set(v___x_41_, 21, v___x_40_);
lean_ctor_set(v___x_41_, 22, v_testDriver_24_);
lean_ctor_set(v___x_41_, 23, v_lintDriver_25_);
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
lean_object* v___x_51_; lean_object* v_leanFile_52_; lean_object* v___x_53_; lean_object* v_tomlFile_54_; uint8_t v___x_55_; 
v___x_51_ = ((lean_object*)(l_Lake_configFileExists___closed__0));
lean_inc_ref(v_cfgFile_48_);
v_leanFile_52_ = l_System_FilePath_addExtension(v_cfgFile_48_, v___x_51_);
v___x_53_ = ((lean_object*)(l_Lake_configFileExists___closed__1));
v_tomlFile_54_ = l_System_FilePath_addExtension(v_cfgFile_48_, v___x_53_);
v___x_55_ = l_System_FilePath_pathExists(v_leanFile_52_);
lean_dec_ref(v_leanFile_52_);
if (v___x_55_ == 0)
{
uint8_t v___x_56_; 
v___x_56_ = l_System_FilePath_pathExists(v_tomlFile_54_);
lean_dec_ref(v_tomlFile_54_);
return v___x_56_;
}
else
{
lean_dec_ref(v_tomlFile_54_);
return v___x_55_;
}
}
else
{
uint8_t v___x_57_; 
lean_dec_ref_known(v___x_50_, 1);
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
lean_dec_ref_known(v___x_64_, 1);
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
lean_object* v_lakeEnv_96_; lean_object* v_lakeArgs_x3f_97_; lean_object* v_wsDir_98_; lean_object* v_pkgIdx_99_; lean_object* v_pkgName_100_; lean_object* v_relPkgDir_101_; lean_object* v_pkgDir_102_; lean_object* v_relConfigFile_103_; lean_object* v_configFile_104_; lean_object* v_relManifestFile_105_; lean_object* v_packageOverrides_106_; lean_object* v_lakeOpts_107_; lean_object* v_leanOpts_108_; uint8_t v_reconfigure_109_; uint8_t v_updateDeps_110_; uint8_t v_updateToolchain_111_; lean_object* v_scope_112_; lean_object* v_remoteUrl_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_200_; 
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
v_isSharedCheck_200_ = !lean_is_exclusive(v_cfg_92_);
if (v_isSharedCheck_200_ == 0)
{
lean_object* v_unused_201_; 
v_unused_201_ = lean_ctor_get(v_cfg_92_, 9);
lean_dec(v_unused_201_);
v___x_115_ = v_cfg_92_;
v_isShared_116_ = v_isSharedCheck_200_;
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
v_isShared_116_ = v_isSharedCheck_200_;
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
lean_dec_ref_known(v___x_117_, 1);
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
lean_object* v___x_153_; lean_object* v_relLeanFile_154_; lean_object* v___x_155_; lean_object* v_relTomlFile_156_; lean_object* v_leanFile_157_; lean_object* v_tomlFile_158_; lean_object* v___x_159_; lean_object* v___y_161_; lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
lean_dec(v___x_117_);
lean_dec_ref(v_configFile_104_);
v___x_153_ = ((lean_object*)(l_Lake_configFileExists___closed__0));
lean_inc_ref(v_relConfigFile_103_);
v_relLeanFile_154_ = l_System_FilePath_addExtension(v_relConfigFile_103_, v___x_153_);
v___x_155_ = ((lean_object*)(l_Lake_configFileExists___closed__1));
v_relTomlFile_156_ = l_System_FilePath_addExtension(v_relConfigFile_103_, v___x_155_);
lean_inc_ref(v_relLeanFile_154_);
lean_inc_ref_n(v_pkgDir_102_, 2);
v_leanFile_157_ = l_Lake_joinRelative(v_pkgDir_102_, v_relLeanFile_154_);
lean_inc_ref(v_relTomlFile_156_);
v_tomlFile_158_ = l_Lake_joinRelative(v_pkgDir_102_, v_relTomlFile_156_);
lean_inc_ref(v_leanFile_157_);
v___x_159_ = l_Lake_resolvePath(v_leanFile_157_);
v___x_167_ = lean_string_utf8_byte_size(v___x_159_);
v___x_168_ = lean_unsigned_to_nat(0u);
v___x_169_ = lean_nat_dec_eq(v___x_167_, v___x_168_);
if (v___x_169_ == 0)
{
uint8_t v___x_170_; 
lean_dec_ref(v_leanFile_157_);
v___x_170_ = l_System_FilePath_pathExists(v_tomlFile_158_);
lean_dec_ref(v_tomlFile_158_);
if (v___x_170_ == 0)
{
lean_dec_ref(v_relTomlFile_156_);
lean_dec_ref(v_name_91_);
v___y_161_ = v_a_93_;
goto v___jp_160_;
}
else
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_171_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__4));
v___x_172_ = lean_string_append(v_name_91_, v___x_171_);
v___x_173_ = lean_string_append(v___x_172_, v_relLeanFile_154_);
v___x_174_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__5));
v___x_175_ = lean_string_append(v___x_173_, v___x_174_);
v___x_176_ = lean_string_append(v___x_175_, v_relTomlFile_156_);
lean_dec_ref(v_relTomlFile_156_);
v___x_177_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__6));
v___x_178_ = lean_string_append(v___x_176_, v___x_177_);
v___x_179_ = lean_string_append(v___x_178_, v_relLeanFile_154_);
v___x_180_ = 1;
v___x_181_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_181_, 0, v___x_179_);
lean_ctor_set_uint8(v___x_181_, sizeof(void*)*1, v___x_180_);
v___x_182_ = lean_array_push(v_a_93_, v___x_181_);
v___y_161_ = v___x_182_;
goto v___jp_160_;
}
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
lean_dec_ref(v___x_159_);
lean_dec_ref(v_relLeanFile_154_);
lean_del_object(v___x_115_);
lean_inc_ref(v_tomlFile_158_);
v___x_183_ = l_Lake_resolvePath(v_tomlFile_158_);
v___x_184_ = lean_string_utf8_byte_size(v___x_183_);
v___x_185_ = lean_nat_dec_eq(v___x_184_, v___x_168_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
lean_dec_ref(v_tomlFile_158_);
lean_dec_ref(v_leanFile_157_);
lean_dec_ref(v_name_91_);
v___x_186_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__1));
v___x_187_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v___x_187_, 0, v_lakeEnv_96_);
lean_ctor_set(v___x_187_, 1, v_lakeArgs_x3f_97_);
lean_ctor_set(v___x_187_, 2, v_wsDir_98_);
lean_ctor_set(v___x_187_, 3, v_pkgIdx_99_);
lean_ctor_set(v___x_187_, 4, v_pkgName_100_);
lean_ctor_set(v___x_187_, 5, v_relPkgDir_101_);
lean_ctor_set(v___x_187_, 6, v_pkgDir_102_);
lean_ctor_set(v___x_187_, 7, v_relTomlFile_156_);
lean_ctor_set(v___x_187_, 8, v___x_183_);
lean_ctor_set(v___x_187_, 9, v___x_186_);
lean_ctor_set(v___x_187_, 10, v_relManifestFile_105_);
lean_ctor_set(v___x_187_, 11, v_packageOverrides_106_);
lean_ctor_set(v___x_187_, 12, v_lakeOpts_107_);
lean_ctor_set(v___x_187_, 13, v_leanOpts_108_);
lean_ctor_set(v___x_187_, 14, v_scope_112_);
lean_ctor_set(v___x_187_, 15, v_remoteUrl_113_);
lean_ctor_set_uint8(v___x_187_, sizeof(void*)*16, v_reconfigure_109_);
lean_ctor_set_uint8(v___x_187_, sizeof(void*)*16 + 1, v_updateDeps_110_);
lean_ctor_set_uint8(v___x_187_, sizeof(void*)*16 + 2, v_updateToolchain_111_);
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v_a_93_);
return v___x_188_;
}
else
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
lean_dec_ref(v___x_183_);
lean_dec_ref(v_relTomlFile_156_);
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
v___x_189_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__7));
v___x_190_ = lean_string_append(v_name_91_, v___x_189_);
v___x_191_ = lean_string_append(v___x_190_, v_leanFile_157_);
lean_dec_ref(v_leanFile_157_);
v___x_192_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__8));
v___x_193_ = lean_string_append(v___x_191_, v___x_192_);
v___x_194_ = lean_string_append(v___x_193_, v_tomlFile_158_);
lean_dec_ref(v_tomlFile_158_);
v___x_195_ = 3;
v___x_196_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_196_, 0, v___x_194_);
lean_ctor_set_uint8(v___x_196_, sizeof(void*)*1, v___x_195_);
v___x_197_ = lean_array_get_size(v_a_93_);
v___x_198_ = lean_array_push(v_a_93_, v___x_196_);
v___x_199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_197_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
return v___x_199_;
}
}
v___jp_160_:
{
lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_162_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__2));
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 9, v___x_162_);
lean_ctor_set(v___x_115_, 8, v___x_159_);
lean_ctor_set(v___x_115_, 7, v_relLeanFile_154_);
v___x_164_ = v___x_115_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_lakeEnv_96_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v_lakeArgs_x3f_97_);
lean_ctor_set(v_reuseFailAlloc_166_, 2, v_wsDir_98_);
lean_ctor_set(v_reuseFailAlloc_166_, 3, v_pkgIdx_99_);
lean_ctor_set(v_reuseFailAlloc_166_, 4, v_pkgName_100_);
lean_ctor_set(v_reuseFailAlloc_166_, 5, v_relPkgDir_101_);
lean_ctor_set(v_reuseFailAlloc_166_, 6, v_pkgDir_102_);
lean_ctor_set(v_reuseFailAlloc_166_, 7, v_relLeanFile_154_);
lean_ctor_set(v_reuseFailAlloc_166_, 8, v___x_159_);
lean_ctor_set(v_reuseFailAlloc_166_, 9, v___x_162_);
lean_ctor_set(v_reuseFailAlloc_166_, 10, v_relManifestFile_105_);
lean_ctor_set(v_reuseFailAlloc_166_, 11, v_packageOverrides_106_);
lean_ctor_set(v_reuseFailAlloc_166_, 12, v_lakeOpts_107_);
lean_ctor_set(v_reuseFailAlloc_166_, 13, v_leanOpts_108_);
lean_ctor_set(v_reuseFailAlloc_166_, 14, v_scope_112_);
lean_ctor_set(v_reuseFailAlloc_166_, 15, v_remoteUrl_113_);
lean_ctor_set_uint8(v_reuseFailAlloc_166_, sizeof(void*)*16, v_reconfigure_109_);
lean_ctor_set_uint8(v_reuseFailAlloc_166_, sizeof(void*)*16 + 1, v_updateDeps_110_);
lean_ctor_set_uint8(v_reuseFailAlloc_166_, sizeof(void*)*16 + 2, v_updateToolchain_111_);
v___x_164_ = v_reuseFailAlloc_166_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v___x_165_; 
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v___y_161_);
return v___x_165_;
}
}
}
}
}
else
{
lean_object* v_lakeEnv_202_; lean_object* v_lakeArgs_x3f_203_; lean_object* v_wsDir_204_; lean_object* v_pkgIdx_205_; lean_object* v_pkgName_206_; lean_object* v_relPkgDir_207_; lean_object* v_pkgDir_208_; lean_object* v_relConfigFile_209_; lean_object* v_configFile_210_; lean_object* v_relManifestFile_211_; lean_object* v_packageOverrides_212_; lean_object* v_lakeOpts_213_; lean_object* v_leanOpts_214_; uint8_t v_reconfigure_215_; uint8_t v_updateDeps_216_; uint8_t v_updateToolchain_217_; lean_object* v_scope_218_; lean_object* v_remoteUrl_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_239_; 
lean_inc_ref(v_configLang_x3f_95_);
v_lakeEnv_202_ = lean_ctor_get(v_cfg_92_, 0);
v_lakeArgs_x3f_203_ = lean_ctor_get(v_cfg_92_, 1);
v_wsDir_204_ = lean_ctor_get(v_cfg_92_, 2);
v_pkgIdx_205_ = lean_ctor_get(v_cfg_92_, 3);
v_pkgName_206_ = lean_ctor_get(v_cfg_92_, 4);
v_relPkgDir_207_ = lean_ctor_get(v_cfg_92_, 5);
v_pkgDir_208_ = lean_ctor_get(v_cfg_92_, 6);
v_relConfigFile_209_ = lean_ctor_get(v_cfg_92_, 7);
v_configFile_210_ = lean_ctor_get(v_cfg_92_, 8);
v_relManifestFile_211_ = lean_ctor_get(v_cfg_92_, 10);
v_packageOverrides_212_ = lean_ctor_get(v_cfg_92_, 11);
v_lakeOpts_213_ = lean_ctor_get(v_cfg_92_, 12);
v_leanOpts_214_ = lean_ctor_get(v_cfg_92_, 13);
v_reconfigure_215_ = lean_ctor_get_uint8(v_cfg_92_, sizeof(void*)*16);
v_updateDeps_216_ = lean_ctor_get_uint8(v_cfg_92_, sizeof(void*)*16 + 1);
v_updateToolchain_217_ = lean_ctor_get_uint8(v_cfg_92_, sizeof(void*)*16 + 2);
v_scope_218_ = lean_ctor_get(v_cfg_92_, 14);
v_remoteUrl_219_ = lean_ctor_get(v_cfg_92_, 15);
v_isSharedCheck_239_ = !lean_is_exclusive(v_cfg_92_);
if (v_isSharedCheck_239_ == 0)
{
lean_object* v_unused_240_; 
v_unused_240_ = lean_ctor_get(v_cfg_92_, 9);
lean_dec(v_unused_240_);
v___x_221_ = v_cfg_92_;
v_isShared_222_ = v_isSharedCheck_239_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_remoteUrl_219_);
lean_inc(v_scope_218_);
lean_inc(v_leanOpts_214_);
lean_inc(v_lakeOpts_213_);
lean_inc(v_packageOverrides_212_);
lean_inc(v_relManifestFile_211_);
lean_inc(v_configFile_210_);
lean_inc(v_relConfigFile_209_);
lean_inc(v_pkgDir_208_);
lean_inc(v_relPkgDir_207_);
lean_inc(v_pkgName_206_);
lean_inc(v_pkgIdx_205_);
lean_inc(v_wsDir_204_);
lean_inc(v_lakeArgs_x3f_203_);
lean_inc(v_lakeEnv_202_);
lean_dec(v_cfg_92_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_239_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
lean_inc_ref(v_configFile_210_);
v___x_223_ = l_Lake_resolvePath(v_configFile_210_);
v___x_224_ = lean_string_utf8_byte_size(v___x_223_);
v___x_225_ = lean_unsigned_to_nat(0u);
v___x_226_ = lean_nat_dec_eq(v___x_224_, v___x_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_228_; 
lean_dec_ref(v_configFile_210_);
lean_dec_ref(v_name_91_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 8, v___x_223_);
v___x_228_ = v___x_221_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_lakeEnv_202_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v_lakeArgs_x3f_203_);
lean_ctor_set(v_reuseFailAlloc_230_, 2, v_wsDir_204_);
lean_ctor_set(v_reuseFailAlloc_230_, 3, v_pkgIdx_205_);
lean_ctor_set(v_reuseFailAlloc_230_, 4, v_pkgName_206_);
lean_ctor_set(v_reuseFailAlloc_230_, 5, v_relPkgDir_207_);
lean_ctor_set(v_reuseFailAlloc_230_, 6, v_pkgDir_208_);
lean_ctor_set(v_reuseFailAlloc_230_, 7, v_relConfigFile_209_);
lean_ctor_set(v_reuseFailAlloc_230_, 8, v___x_223_);
lean_ctor_set(v_reuseFailAlloc_230_, 9, v_configLang_x3f_95_);
lean_ctor_set(v_reuseFailAlloc_230_, 10, v_relManifestFile_211_);
lean_ctor_set(v_reuseFailAlloc_230_, 11, v_packageOverrides_212_);
lean_ctor_set(v_reuseFailAlloc_230_, 12, v_lakeOpts_213_);
lean_ctor_set(v_reuseFailAlloc_230_, 13, v_leanOpts_214_);
lean_ctor_set(v_reuseFailAlloc_230_, 14, v_scope_218_);
lean_ctor_set(v_reuseFailAlloc_230_, 15, v_remoteUrl_219_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, sizeof(void*)*16, v_reconfigure_215_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, sizeof(void*)*16 + 1, v_updateDeps_216_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, sizeof(void*)*16 + 2, v_updateToolchain_217_);
v___x_228_ = v_reuseFailAlloc_230_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_229_; 
v___x_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v_a_93_);
return v___x_229_;
}
}
else
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
lean_dec_ref(v___x_223_);
lean_del_object(v___x_221_);
lean_dec_ref(v_remoteUrl_219_);
lean_dec_ref(v_scope_218_);
lean_dec_ref(v_leanOpts_214_);
lean_dec(v_lakeOpts_213_);
lean_dec_ref(v_packageOverrides_212_);
lean_dec_ref(v_relManifestFile_211_);
lean_dec_ref(v_relConfigFile_209_);
lean_dec_ref(v_pkgDir_208_);
lean_dec_ref(v_relPkgDir_207_);
lean_dec(v_pkgName_206_);
lean_dec(v_pkgIdx_205_);
lean_dec_ref(v_wsDir_204_);
lean_dec(v_lakeArgs_x3f_203_);
lean_dec_ref(v_lakeEnv_202_);
lean_dec_ref_known(v_configLang_x3f_95_, 1);
v___x_231_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__3));
v___x_232_ = lean_string_append(v_name_91_, v___x_231_);
v___x_233_ = lean_string_append(v___x_232_, v_configFile_210_);
lean_dec_ref(v_configFile_210_);
v___x_234_ = 3;
v___x_235_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_235_, 0, v___x_233_);
lean_ctor_set_uint8(v___x_235_, sizeof(void*)*1, v___x_234_);
v___x_236_ = lean_array_get_size(v_a_93_);
v___x_237_ = lean_array_push(v_a_93_, v___x_235_);
v___x_238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_236_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
return v___x_238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveConfigFile___boxed(lean_object* v_name_241_, lean_object* v_cfg_242_, lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lake_resolveConfigFile(v_name_241_, v_cfg_242_, v_a_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadConfigFile___redArg(lean_object* v_cfg_246_, lean_object* v_a_247_){
_start:
{
lean_object* v_configLang_x3f_249_; lean_object* v_val_250_; uint8_t v___x_251_; 
v_configLang_x3f_249_ = lean_ctor_get(v_cfg_246_, 9);
v_val_250_ = lean_ctor_get(v_configLang_x3f_249_, 0);
v___x_251_ = lean_unbox(v_val_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; 
v___x_252_ = l_Lake_loadLeanConfig(v_cfg_246_, v_a_247_);
return v___x_252_;
}
else
{
lean_object* v___x_253_; 
v___x_253_ = l_Lake_loadTomlConfig(v_cfg_246_, v_a_247_);
return v___x_253_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadConfigFile___redArg___boxed(lean_object* v_cfg_254_, lean_object* v_a_255_, lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lake_loadConfigFile___redArg(v_cfg_254_, v_a_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadConfigFile(lean_object* v_cfg_258_, lean_object* v_h_259_, lean_object* v_a_260_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_Lake_loadConfigFile___redArg(v_cfg_258_, v_a_260_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadConfigFile___boxed(lean_object* v_cfg_263_, lean_object* v_h_264_, lean_object* v_a_265_, lean_object* v_a_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lake_loadConfigFile(v_cfg_263_, v_h_264_, v_a_265_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackage(lean_object* v_cfg_269_, lean_object* v_a_270_){
_start:
{
lean_object* v_lakeEnv_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v_lakeEnv_272_ = lean_ctor_get(v_cfg_269_, 0);
v___x_273_ = l_Lean_searchPathRef;
v___x_274_ = l_Lake_Env_leanSearchPath(v_lakeEnv_272_);
v___x_275_ = lean_st_ref_swap(v___x_273_, v___x_274_);
lean_dec(v___x_275_);
v___x_276_ = ((lean_object*)(l_Lake_loadPackage___closed__0));
v___x_277_ = l_Lake_resolveConfigFile(v___x_276_, v_cfg_269_, v_a_270_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v_a_278_; lean_object* v_a_279_; lean_object* v___x_280_; 
v_a_278_ = lean_ctor_get(v___x_277_, 0);
lean_inc_n(v_a_278_, 2);
v_a_279_ = lean_ctor_get(v___x_277_, 1);
lean_inc(v_a_279_);
lean_dec_ref_known(v___x_277_, 2);
v___x_280_ = l_Lake_loadConfigFile___redArg(v_a_278_, v_a_279_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_291_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
v_a_282_ = lean_ctor_get(v___x_280_, 1);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_291_ == 0)
{
v___x_284_ = v___x_280_;
v_isShared_285_ = v_isSharedCheck_291_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_inc(v_a_281_);
lean_dec(v___x_280_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_291_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v_pkgIdx_286_; lean_object* v___x_287_; lean_object* v___x_289_; 
v_pkgIdx_286_ = lean_ctor_get(v_a_278_, 3);
lean_inc(v_pkgIdx_286_);
v___x_287_ = l_Lake_mkPackage(v_a_278_, v_a_281_, v_pkgIdx_286_);
lean_dec(v_a_278_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 0, v___x_287_);
v___x_289_ = v___x_284_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_287_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_a_282_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
else
{
lean_object* v_a_292_; lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_300_; 
lean_dec(v_a_278_);
v_a_292_ = lean_ctor_get(v___x_280_, 0);
v_a_293_ = lean_ctor_get(v___x_280_, 1);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_300_ == 0)
{
v___x_295_ = v___x_280_;
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_inc(v_a_292_);
lean_dec(v___x_280_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
if (v_isShared_296_ == 0)
{
v___x_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_a_292_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_a_293_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
else
{
lean_object* v_a_301_; lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
v_a_301_ = lean_ctor_get(v___x_277_, 0);
v_a_302_ = lean_ctor_get(v___x_277_, 1);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_277_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_inc(v_a_301_);
lean_dec(v___x_277_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_301_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_a_302_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackage___boxed(lean_object* v_cfg_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lake_loadPackage(v_cfg_310_, v_a_311_);
return v_res_313_;
}
}
lean_object* runtime_initialize_Lake_Load_Config(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Package(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_LakefileConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_IO(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Lean(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Toml(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Load_Package(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
