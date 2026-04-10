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
static const lean_string_object l_Lake_mkPackage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lake_mkPackage___closed__0 = (const lean_object*)&l_Lake_mkPackage___closed__0_value;
static const lean_string_object l_Lake_mkPackage___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ".tar.gz"};
static const lean_object* l_Lake_mkPackage___closed__1 = (const lean_object*)&l_Lake_mkPackage___closed__1_value;
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
LEAN_EXPORT lean_object* l_Lake_mkPackage(lean_object* v_loadCfg_3_, lean_object* v_fileCfg_4_, lean_object* v_wsIdx_5_){
_start:
{
lean_object* v_pkgDecl_6_; lean_object* v_config_7_; lean_object* v_buildArchive_8_; 
v_pkgDecl_6_ = lean_ctor_get(v_fileCfg_4_, 0);
lean_inc_ref(v_pkgDecl_6_);
v_config_7_ = lean_ctor_get(v_pkgDecl_6_, 3);
lean_inc_ref(v_config_7_);
v_buildArchive_8_ = lean_ctor_get(v_config_7_, 11);
if (lean_obj_tag(v_buildArchive_8_) == 1)
{
lean_object* v_relPkgDir_9_; lean_object* v_pkgDir_10_; lean_object* v_relConfigFile_11_; lean_object* v_configFile_12_; lean_object* v_relManifestFile_13_; lean_object* v_scope_14_; lean_object* v_remoteUrl_15_; lean_object* v_depConfigs_16_; lean_object* v_targetDecls_17_; lean_object* v_targetDeclMap_18_; lean_object* v_defaultTargets_19_; lean_object* v_scripts_20_; lean_object* v_defaultScripts_21_; lean_object* v_postUpdateHooks_22_; lean_object* v_testDriver_23_; lean_object* v_lintDriver_24_; lean_object* v_baseName_25_; lean_object* v_keyName_26_; lean_object* v_origName_27_; lean_object* v_val_28_; lean_object* v___x_29_; 
v_relPkgDir_9_ = lean_ctor_get(v_loadCfg_3_, 5);
v_pkgDir_10_ = lean_ctor_get(v_loadCfg_3_, 6);
v_relConfigFile_11_ = lean_ctor_get(v_loadCfg_3_, 7);
v_configFile_12_ = lean_ctor_get(v_loadCfg_3_, 8);
v_relManifestFile_13_ = lean_ctor_get(v_loadCfg_3_, 10);
v_scope_14_ = lean_ctor_get(v_loadCfg_3_, 14);
v_remoteUrl_15_ = lean_ctor_get(v_loadCfg_3_, 15);
v_depConfigs_16_ = lean_ctor_get(v_fileCfg_4_, 1);
lean_inc_ref(v_depConfigs_16_);
v_targetDecls_17_ = lean_ctor_get(v_fileCfg_4_, 3);
lean_inc_ref(v_targetDecls_17_);
v_targetDeclMap_18_ = lean_ctor_get(v_fileCfg_4_, 4);
lean_inc(v_targetDeclMap_18_);
v_defaultTargets_19_ = lean_ctor_get(v_fileCfg_4_, 5);
lean_inc_ref(v_defaultTargets_19_);
v_scripts_20_ = lean_ctor_get(v_fileCfg_4_, 6);
lean_inc(v_scripts_20_);
v_defaultScripts_21_ = lean_ctor_get(v_fileCfg_4_, 7);
lean_inc_ref(v_defaultScripts_21_);
v_postUpdateHooks_22_ = lean_ctor_get(v_fileCfg_4_, 8);
lean_inc_ref(v_postUpdateHooks_22_);
v_testDriver_23_ = lean_ctor_get(v_fileCfg_4_, 9);
lean_inc_ref(v_testDriver_23_);
v_lintDriver_24_ = lean_ctor_get(v_fileCfg_4_, 10);
lean_inc_ref(v_lintDriver_24_);
lean_dec_ref(v_fileCfg_4_);
v_baseName_25_ = lean_ctor_get(v_pkgDecl_6_, 0);
lean_inc(v_baseName_25_);
v_keyName_26_ = lean_ctor_get(v_pkgDecl_6_, 1);
lean_inc(v_keyName_26_);
v_origName_27_ = lean_ctor_get(v_pkgDecl_6_, 2);
lean_inc(v_origName_27_);
lean_dec_ref(v_pkgDecl_6_);
v_val_28_ = lean_ctor_get(v_buildArchive_8_, 0);
lean_inc(v_val_28_);
lean_inc_ref(v_remoteUrl_15_);
lean_inc_ref(v_scope_14_);
lean_inc_ref(v_relManifestFile_13_);
lean_inc_ref(v_relConfigFile_11_);
lean_inc_ref(v_configFile_12_);
lean_inc_ref(v_relPkgDir_9_);
lean_inc_ref(v_pkgDir_10_);
v___x_29_ = lean_alloc_ctor(0, 22, 0);
lean_ctor_set(v___x_29_, 0, v_wsIdx_5_);
lean_ctor_set(v___x_29_, 1, v_baseName_25_);
lean_ctor_set(v___x_29_, 2, v_keyName_26_);
lean_ctor_set(v___x_29_, 3, v_origName_27_);
lean_ctor_set(v___x_29_, 4, v_pkgDir_10_);
lean_ctor_set(v___x_29_, 5, v_relPkgDir_9_);
lean_ctor_set(v___x_29_, 6, v_config_7_);
lean_ctor_set(v___x_29_, 7, v_configFile_12_);
lean_ctor_set(v___x_29_, 8, v_relConfigFile_11_);
lean_ctor_set(v___x_29_, 9, v_relManifestFile_13_);
lean_ctor_set(v___x_29_, 10, v_scope_14_);
lean_ctor_set(v___x_29_, 11, v_remoteUrl_15_);
lean_ctor_set(v___x_29_, 12, v_depConfigs_16_);
lean_ctor_set(v___x_29_, 13, v_targetDecls_17_);
lean_ctor_set(v___x_29_, 14, v_targetDeclMap_18_);
lean_ctor_set(v___x_29_, 15, v_defaultTargets_19_);
lean_ctor_set(v___x_29_, 16, v_scripts_20_);
lean_ctor_set(v___x_29_, 17, v_defaultScripts_21_);
lean_ctor_set(v___x_29_, 18, v_postUpdateHooks_22_);
lean_ctor_set(v___x_29_, 19, v_val_28_);
lean_ctor_set(v___x_29_, 20, v_testDriver_23_);
lean_ctor_set(v___x_29_, 21, v_lintDriver_24_);
return v___x_29_;
}
else
{
lean_object* v_relPkgDir_30_; lean_object* v_pkgDir_31_; lean_object* v_relConfigFile_32_; lean_object* v_configFile_33_; lean_object* v_relManifestFile_34_; lean_object* v_scope_35_; lean_object* v_remoteUrl_36_; lean_object* v_depConfigs_37_; lean_object* v_targetDecls_38_; lean_object* v_targetDeclMap_39_; lean_object* v_defaultTargets_40_; lean_object* v_scripts_41_; lean_object* v_defaultScripts_42_; lean_object* v_postUpdateHooks_43_; lean_object* v_testDriver_44_; lean_object* v_lintDriver_45_; lean_object* v_baseName_46_; lean_object* v_keyName_47_; lean_object* v_origName_48_; uint8_t v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v_relPkgDir_30_ = lean_ctor_get(v_loadCfg_3_, 5);
v_pkgDir_31_ = lean_ctor_get(v_loadCfg_3_, 6);
v_relConfigFile_32_ = lean_ctor_get(v_loadCfg_3_, 7);
v_configFile_33_ = lean_ctor_get(v_loadCfg_3_, 8);
v_relManifestFile_34_ = lean_ctor_get(v_loadCfg_3_, 10);
v_scope_35_ = lean_ctor_get(v_loadCfg_3_, 14);
v_remoteUrl_36_ = lean_ctor_get(v_loadCfg_3_, 15);
v_depConfigs_37_ = lean_ctor_get(v_fileCfg_4_, 1);
lean_inc_ref(v_depConfigs_37_);
v_targetDecls_38_ = lean_ctor_get(v_fileCfg_4_, 3);
lean_inc_ref(v_targetDecls_38_);
v_targetDeclMap_39_ = lean_ctor_get(v_fileCfg_4_, 4);
lean_inc(v_targetDeclMap_39_);
v_defaultTargets_40_ = lean_ctor_get(v_fileCfg_4_, 5);
lean_inc_ref(v_defaultTargets_40_);
v_scripts_41_ = lean_ctor_get(v_fileCfg_4_, 6);
lean_inc(v_scripts_41_);
v_defaultScripts_42_ = lean_ctor_get(v_fileCfg_4_, 7);
lean_inc_ref(v_defaultScripts_42_);
v_postUpdateHooks_43_ = lean_ctor_get(v_fileCfg_4_, 8);
lean_inc_ref(v_postUpdateHooks_43_);
v_testDriver_44_ = lean_ctor_get(v_fileCfg_4_, 9);
lean_inc_ref(v_testDriver_44_);
v_lintDriver_45_ = lean_ctor_get(v_fileCfg_4_, 10);
lean_inc_ref(v_lintDriver_45_);
lean_dec_ref(v_fileCfg_4_);
v_baseName_46_ = lean_ctor_get(v_pkgDecl_6_, 0);
lean_inc_n(v_baseName_46_, 2);
v_keyName_47_ = lean_ctor_get(v_pkgDecl_6_, 1);
lean_inc(v_keyName_47_);
v_origName_48_ = lean_ctor_get(v_pkgDecl_6_, 2);
lean_inc(v_origName_48_);
lean_dec_ref(v_pkgDecl_6_);
v___x_49_ = 0;
v___x_50_ = l_Lean_Name_toString(v_baseName_46_, v___x_49_);
v___x_51_ = ((lean_object*)(l_Lake_mkPackage___closed__0));
v___x_52_ = lean_string_append(v___x_50_, v___x_51_);
v___x_53_ = l_System_Platform_target;
v___x_54_ = lean_string_append(v___x_52_, v___x_53_);
v___x_55_ = ((lean_object*)(l_Lake_mkPackage___closed__1));
v___x_56_ = lean_string_append(v___x_54_, v___x_55_);
lean_inc_ref(v_remoteUrl_36_);
lean_inc_ref(v_scope_35_);
lean_inc_ref(v_relManifestFile_34_);
lean_inc_ref(v_relConfigFile_32_);
lean_inc_ref(v_configFile_33_);
lean_inc_ref(v_relPkgDir_30_);
lean_inc_ref(v_pkgDir_31_);
v___x_57_ = lean_alloc_ctor(0, 22, 0);
lean_ctor_set(v___x_57_, 0, v_wsIdx_5_);
lean_ctor_set(v___x_57_, 1, v_baseName_46_);
lean_ctor_set(v___x_57_, 2, v_keyName_47_);
lean_ctor_set(v___x_57_, 3, v_origName_48_);
lean_ctor_set(v___x_57_, 4, v_pkgDir_31_);
lean_ctor_set(v___x_57_, 5, v_relPkgDir_30_);
lean_ctor_set(v___x_57_, 6, v_config_7_);
lean_ctor_set(v___x_57_, 7, v_configFile_33_);
lean_ctor_set(v___x_57_, 8, v_relConfigFile_32_);
lean_ctor_set(v___x_57_, 9, v_relManifestFile_34_);
lean_ctor_set(v___x_57_, 10, v_scope_35_);
lean_ctor_set(v___x_57_, 11, v_remoteUrl_36_);
lean_ctor_set(v___x_57_, 12, v_depConfigs_37_);
lean_ctor_set(v___x_57_, 13, v_targetDecls_38_);
lean_ctor_set(v___x_57_, 14, v_targetDeclMap_39_);
lean_ctor_set(v___x_57_, 15, v_defaultTargets_40_);
lean_ctor_set(v___x_57_, 16, v_scripts_41_);
lean_ctor_set(v___x_57_, 17, v_defaultScripts_42_);
lean_ctor_set(v___x_57_, 18, v_postUpdateHooks_43_);
lean_ctor_set(v___x_57_, 19, v___x_56_);
lean_ctor_set(v___x_57_, 20, v_testDriver_44_);
lean_ctor_set(v___x_57_, 21, v_lintDriver_45_);
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkPackage___boxed(lean_object* v_loadCfg_58_, lean_object* v_fileCfg_59_, lean_object* v_wsIdx_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Lake_mkPackage(v_loadCfg_58_, v_fileCfg_59_, v_wsIdx_60_);
lean_dec_ref(v_loadCfg_58_);
return v_res_61_;
}
}
LEAN_EXPORT uint8_t l_Lake_configFileExists(lean_object* v_cfgFile_64_){
_start:
{
lean_object* v___x_66_; 
lean_inc_ref(v_cfgFile_64_);
v___x_66_ = l_System_FilePath_extension(v_cfgFile_64_);
if (lean_obj_tag(v___x_66_) == 0)
{
lean_object* v___x_67_; lean_object* v_leanFile_68_; uint8_t v___x_69_; 
v___x_67_ = ((lean_object*)(l_Lake_configFileExists___closed__0));
lean_inc_ref(v_cfgFile_64_);
v_leanFile_68_ = l_System_FilePath_addExtension(v_cfgFile_64_, v___x_67_);
v___x_69_ = l_System_FilePath_pathExists(v_leanFile_68_);
lean_dec_ref(v_leanFile_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; lean_object* v_tomlFile_71_; uint8_t v___x_72_; 
v___x_70_ = ((lean_object*)(l_Lake_configFileExists___closed__1));
v_tomlFile_71_ = l_System_FilePath_addExtension(v_cfgFile_64_, v___x_70_);
v___x_72_ = l_System_FilePath_pathExists(v_tomlFile_71_);
lean_dec_ref(v_tomlFile_71_);
return v___x_72_;
}
else
{
lean_dec_ref(v_cfgFile_64_);
return v___x_69_;
}
}
else
{
uint8_t v___x_73_; 
lean_dec_ref(v___x_66_);
v___x_73_ = l_System_FilePath_pathExists(v_cfgFile_64_);
lean_dec_ref(v_cfgFile_64_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_configFileExists___boxed(lean_object* v_cfgFile_74_, lean_object* v_a_75_){
_start:
{
uint8_t v_res_76_; lean_object* v_r_77_; 
v_res_76_ = l_Lake_configFileExists(v_cfgFile_74_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
LEAN_EXPORT lean_object* l_Lake_realConfigFile(lean_object* v_cfgFile_78_){
_start:
{
lean_object* v___x_80_; 
lean_inc_ref(v_cfgFile_78_);
v___x_80_ = l_System_FilePath_extension(v_cfgFile_78_);
if (lean_obj_tag(v___x_80_) == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_81_ = ((lean_object*)(l_Lake_configFileExists___closed__0));
lean_inc_ref(v_cfgFile_78_);
v___x_82_ = l_System_FilePath_addExtension(v_cfgFile_78_, v___x_81_);
v___x_83_ = l_Lake_resolvePath(v___x_82_);
v___x_84_ = lean_string_utf8_byte_size(v___x_83_);
v___x_85_ = lean_unsigned_to_nat(0u);
v___x_86_ = lean_nat_dec_eq(v___x_84_, v___x_85_);
if (v___x_86_ == 0)
{
lean_dec_ref(v_cfgFile_78_);
return v___x_83_;
}
else
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
lean_dec_ref(v___x_83_);
v___x_87_ = ((lean_object*)(l_Lake_configFileExists___closed__1));
v___x_88_ = l_System_FilePath_addExtension(v_cfgFile_78_, v___x_87_);
v___x_89_ = l_Lake_resolvePath(v___x_88_);
return v___x_89_;
}
}
else
{
lean_object* v___x_90_; 
lean_dec_ref(v___x_80_);
v___x_90_ = l_Lake_resolvePath(v_cfgFile_78_);
return v___x_90_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_realConfigFile___boxed(lean_object* v_cfgFile_91_, lean_object* v_a_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lake_realConfigFile(v_cfgFile_91_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveConfigFile(lean_object* v_name_107_, lean_object* v_cfg_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_configLang_x3f_111_; 
v_configLang_x3f_111_ = lean_ctor_get(v_cfg_108_, 9);
if (lean_obj_tag(v_configLang_x3f_111_) == 0)
{
lean_object* v_lakeEnv_112_; lean_object* v_lakeArgs_x3f_113_; lean_object* v_wsDir_114_; lean_object* v_pkgIdx_115_; lean_object* v_pkgName_116_; lean_object* v_relPkgDir_117_; lean_object* v_pkgDir_118_; lean_object* v_relConfigFile_119_; lean_object* v_configFile_120_; lean_object* v_relManifestFile_121_; lean_object* v_packageOverrides_122_; lean_object* v_lakeOpts_123_; lean_object* v_leanOpts_124_; uint8_t v_reconfigure_125_; uint8_t v_updateDeps_126_; uint8_t v_updateToolchain_127_; lean_object* v_scope_128_; lean_object* v_remoteUrl_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_218_; 
v_lakeEnv_112_ = lean_ctor_get(v_cfg_108_, 0);
v_lakeArgs_x3f_113_ = lean_ctor_get(v_cfg_108_, 1);
v_wsDir_114_ = lean_ctor_get(v_cfg_108_, 2);
v_pkgIdx_115_ = lean_ctor_get(v_cfg_108_, 3);
v_pkgName_116_ = lean_ctor_get(v_cfg_108_, 4);
v_relPkgDir_117_ = lean_ctor_get(v_cfg_108_, 5);
v_pkgDir_118_ = lean_ctor_get(v_cfg_108_, 6);
v_relConfigFile_119_ = lean_ctor_get(v_cfg_108_, 7);
v_configFile_120_ = lean_ctor_get(v_cfg_108_, 8);
v_relManifestFile_121_ = lean_ctor_get(v_cfg_108_, 10);
v_packageOverrides_122_ = lean_ctor_get(v_cfg_108_, 11);
v_lakeOpts_123_ = lean_ctor_get(v_cfg_108_, 12);
v_leanOpts_124_ = lean_ctor_get(v_cfg_108_, 13);
v_reconfigure_125_ = lean_ctor_get_uint8(v_cfg_108_, sizeof(void*)*16);
v_updateDeps_126_ = lean_ctor_get_uint8(v_cfg_108_, sizeof(void*)*16 + 1);
v_updateToolchain_127_ = lean_ctor_get_uint8(v_cfg_108_, sizeof(void*)*16 + 2);
v_scope_128_ = lean_ctor_get(v_cfg_108_, 14);
v_remoteUrl_129_ = lean_ctor_get(v_cfg_108_, 15);
v_isSharedCheck_218_ = !lean_is_exclusive(v_cfg_108_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; 
v_unused_219_ = lean_ctor_get(v_cfg_108_, 9);
lean_dec(v_unused_219_);
v___x_131_ = v_cfg_108_;
v_isShared_132_ = v_isSharedCheck_218_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_remoteUrl_129_);
lean_inc(v_scope_128_);
lean_inc(v_leanOpts_124_);
lean_inc(v_lakeOpts_123_);
lean_inc(v_packageOverrides_122_);
lean_inc(v_relManifestFile_121_);
lean_inc(v_configFile_120_);
lean_inc(v_relConfigFile_119_);
lean_inc(v_pkgDir_118_);
lean_inc(v_relPkgDir_117_);
lean_inc(v_pkgName_116_);
lean_inc(v_pkgIdx_115_);
lean_inc(v_wsDir_114_);
lean_inc(v_lakeArgs_x3f_113_);
lean_inc(v_lakeEnv_112_);
lean_dec(v_cfg_108_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_218_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_133_; 
lean_inc_ref(v_relConfigFile_119_);
v___x_133_ = l_System_FilePath_extension(v_relConfigFile_119_);
if (lean_obj_tag(v___x_133_) == 1)
{
lean_object* v_val_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v_val_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_val_134_);
lean_dec_ref(v___x_133_);
lean_inc_ref(v_configFile_120_);
v___x_135_ = l_Lake_resolvePath(v_configFile_120_);
v___x_136_ = lean_string_utf8_byte_size(v___x_135_);
v___x_137_ = lean_unsigned_to_nat(0u);
v___x_138_ = lean_nat_dec_eq(v___x_136_, v___x_137_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; uint8_t v___x_140_; 
lean_dec_ref(v_configFile_120_);
v___x_139_ = ((lean_object*)(l_Lake_configFileExists___closed__0));
v___x_140_ = lean_string_dec_eq(v_val_134_, v___x_139_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_141_ = ((lean_object*)(l_Lake_configFileExists___closed__1));
v___x_142_ = lean_string_dec_eq(v_val_134_, v___x_141_);
lean_dec(v_val_134_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; uint8_t v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
lean_del_object(v___x_131_);
lean_dec_ref(v_remoteUrl_129_);
lean_dec_ref(v_scope_128_);
lean_dec_ref(v_leanOpts_124_);
lean_dec(v_lakeOpts_123_);
lean_dec_ref(v_packageOverrides_122_);
lean_dec_ref(v_relManifestFile_121_);
lean_dec_ref(v_relConfigFile_119_);
lean_dec_ref(v_pkgDir_118_);
lean_dec_ref(v_relPkgDir_117_);
lean_dec(v_pkgName_116_);
lean_dec(v_pkgIdx_115_);
lean_dec_ref(v_wsDir_114_);
lean_dec(v_lakeArgs_x3f_113_);
lean_dec_ref(v_lakeEnv_112_);
v___x_143_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__0));
v___x_144_ = lean_string_append(v_name_107_, v___x_143_);
v___x_145_ = lean_string_append(v___x_144_, v___x_135_);
lean_dec_ref(v___x_135_);
v___x_146_ = 3;
v___x_147_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_147_, 0, v___x_145_);
lean_ctor_set_uint8(v___x_147_, sizeof(void*)*1, v___x_146_);
v___x_148_ = lean_array_get_size(v_a_109_);
v___x_149_ = lean_array_push(v_a_109_, v___x_147_);
v___x_150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_148_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
return v___x_150_;
}
else
{
lean_object* v___x_151_; lean_object* v___x_153_; 
lean_dec_ref(v_name_107_);
v___x_151_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__1));
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 9, v___x_151_);
lean_ctor_set(v___x_131_, 8, v___x_135_);
v___x_153_ = v___x_131_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_lakeEnv_112_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_lakeArgs_x3f_113_);
lean_ctor_set(v_reuseFailAlloc_155_, 2, v_wsDir_114_);
lean_ctor_set(v_reuseFailAlloc_155_, 3, v_pkgIdx_115_);
lean_ctor_set(v_reuseFailAlloc_155_, 4, v_pkgName_116_);
lean_ctor_set(v_reuseFailAlloc_155_, 5, v_relPkgDir_117_);
lean_ctor_set(v_reuseFailAlloc_155_, 6, v_pkgDir_118_);
lean_ctor_set(v_reuseFailAlloc_155_, 7, v_relConfigFile_119_);
lean_ctor_set(v_reuseFailAlloc_155_, 8, v___x_135_);
lean_ctor_set(v_reuseFailAlloc_155_, 9, v___x_151_);
lean_ctor_set(v_reuseFailAlloc_155_, 10, v_relManifestFile_121_);
lean_ctor_set(v_reuseFailAlloc_155_, 11, v_packageOverrides_122_);
lean_ctor_set(v_reuseFailAlloc_155_, 12, v_lakeOpts_123_);
lean_ctor_set(v_reuseFailAlloc_155_, 13, v_leanOpts_124_);
lean_ctor_set(v_reuseFailAlloc_155_, 14, v_scope_128_);
lean_ctor_set(v_reuseFailAlloc_155_, 15, v_remoteUrl_129_);
lean_ctor_set_uint8(v_reuseFailAlloc_155_, sizeof(void*)*16, v_reconfigure_125_);
lean_ctor_set_uint8(v_reuseFailAlloc_155_, sizeof(void*)*16 + 1, v_updateDeps_126_);
lean_ctor_set_uint8(v_reuseFailAlloc_155_, sizeof(void*)*16 + 2, v_updateToolchain_127_);
v___x_153_ = v_reuseFailAlloc_155_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v___x_154_; 
v___x_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v_a_109_);
return v___x_154_;
}
}
}
else
{
lean_object* v___x_156_; lean_object* v___x_158_; 
lean_dec(v_val_134_);
lean_dec_ref(v_name_107_);
v___x_156_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__2));
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 9, v___x_156_);
lean_ctor_set(v___x_131_, 8, v___x_135_);
v___x_158_ = v___x_131_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_lakeEnv_112_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v_lakeArgs_x3f_113_);
lean_ctor_set(v_reuseFailAlloc_160_, 2, v_wsDir_114_);
lean_ctor_set(v_reuseFailAlloc_160_, 3, v_pkgIdx_115_);
lean_ctor_set(v_reuseFailAlloc_160_, 4, v_pkgName_116_);
lean_ctor_set(v_reuseFailAlloc_160_, 5, v_relPkgDir_117_);
lean_ctor_set(v_reuseFailAlloc_160_, 6, v_pkgDir_118_);
lean_ctor_set(v_reuseFailAlloc_160_, 7, v_relConfigFile_119_);
lean_ctor_set(v_reuseFailAlloc_160_, 8, v___x_135_);
lean_ctor_set(v_reuseFailAlloc_160_, 9, v___x_156_);
lean_ctor_set(v_reuseFailAlloc_160_, 10, v_relManifestFile_121_);
lean_ctor_set(v_reuseFailAlloc_160_, 11, v_packageOverrides_122_);
lean_ctor_set(v_reuseFailAlloc_160_, 12, v_lakeOpts_123_);
lean_ctor_set(v_reuseFailAlloc_160_, 13, v_leanOpts_124_);
lean_ctor_set(v_reuseFailAlloc_160_, 14, v_scope_128_);
lean_ctor_set(v_reuseFailAlloc_160_, 15, v_remoteUrl_129_);
lean_ctor_set_uint8(v_reuseFailAlloc_160_, sizeof(void*)*16, v_reconfigure_125_);
lean_ctor_set_uint8(v_reuseFailAlloc_160_, sizeof(void*)*16 + 1, v_updateDeps_126_);
lean_ctor_set_uint8(v_reuseFailAlloc_160_, sizeof(void*)*16 + 2, v_updateToolchain_127_);
v___x_158_ = v_reuseFailAlloc_160_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
lean_object* v___x_159_; 
v___x_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v_a_109_);
return v___x_159_;
}
}
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
lean_dec_ref(v___x_135_);
lean_dec(v_val_134_);
lean_del_object(v___x_131_);
lean_dec_ref(v_remoteUrl_129_);
lean_dec_ref(v_scope_128_);
lean_dec_ref(v_leanOpts_124_);
lean_dec(v_lakeOpts_123_);
lean_dec_ref(v_packageOverrides_122_);
lean_dec_ref(v_relManifestFile_121_);
lean_dec_ref(v_relConfigFile_119_);
lean_dec_ref(v_pkgDir_118_);
lean_dec_ref(v_relPkgDir_117_);
lean_dec(v_pkgName_116_);
lean_dec(v_pkgIdx_115_);
lean_dec_ref(v_wsDir_114_);
lean_dec(v_lakeArgs_x3f_113_);
lean_dec_ref(v_lakeEnv_112_);
v___x_161_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__3));
v___x_162_ = lean_string_append(v_name_107_, v___x_161_);
v___x_163_ = lean_string_append(v___x_162_, v_configFile_120_);
lean_dec_ref(v_configFile_120_);
v___x_164_ = 3;
v___x_165_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_165_, 0, v___x_163_);
lean_ctor_set_uint8(v___x_165_, sizeof(void*)*1, v___x_164_);
v___x_166_ = lean_array_get_size(v_a_109_);
v___x_167_ = lean_array_push(v_a_109_, v___x_165_);
v___x_168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_166_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
return v___x_168_;
}
}
else
{
lean_object* v___x_169_; lean_object* v_relLeanFile_170_; lean_object* v_leanFile_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v_relTomlFile_174_; lean_object* v_tomlFile_175_; lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; 
lean_dec(v___x_133_);
lean_dec_ref(v_configFile_120_);
v___x_169_ = ((lean_object*)(l_Lake_configFileExists___closed__0));
lean_inc_ref(v_relConfigFile_119_);
v_relLeanFile_170_ = l_System_FilePath_addExtension(v_relConfigFile_119_, v___x_169_);
lean_inc_ref(v_relLeanFile_170_);
lean_inc_ref_n(v_pkgDir_118_, 2);
v_leanFile_171_ = l_Lake_joinRelative(v_pkgDir_118_, v_relLeanFile_170_);
lean_inc_ref(v_leanFile_171_);
v___x_172_ = l_Lake_resolvePath(v_leanFile_171_);
v___x_173_ = ((lean_object*)(l_Lake_configFileExists___closed__1));
v_relTomlFile_174_ = l_System_FilePath_addExtension(v_relConfigFile_119_, v___x_173_);
lean_inc_ref(v_relTomlFile_174_);
v_tomlFile_175_ = l_Lake_joinRelative(v_pkgDir_118_, v_relTomlFile_174_);
v___x_176_ = lean_string_utf8_byte_size(v___x_172_);
v___x_177_ = lean_unsigned_to_nat(0u);
v___x_178_ = lean_nat_dec_eq(v___x_176_, v___x_177_);
if (v___x_178_ == 0)
{
uint8_t v___x_179_; lean_object* v___y_181_; 
lean_dec_ref(v_leanFile_171_);
v___x_179_ = l_System_FilePath_pathExists(v_tomlFile_175_);
lean_dec_ref(v_tomlFile_175_);
if (v___x_179_ == 0)
{
lean_dec_ref(v_relTomlFile_174_);
lean_dec_ref(v_name_107_);
v___y_181_ = v_a_109_;
goto v___jp_180_;
}
else
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_187_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__4));
v___x_188_ = lean_string_append(v_name_107_, v___x_187_);
v___x_189_ = lean_string_append(v___x_188_, v_relLeanFile_170_);
v___x_190_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__5));
v___x_191_ = lean_string_append(v___x_189_, v___x_190_);
v___x_192_ = lean_string_append(v___x_191_, v_relTomlFile_174_);
lean_dec_ref(v_relTomlFile_174_);
v___x_193_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__6));
v___x_194_ = lean_string_append(v___x_192_, v___x_193_);
v___x_195_ = lean_string_append(v___x_194_, v_relLeanFile_170_);
v___x_196_ = 1;
v___x_197_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_197_, 0, v___x_195_);
lean_ctor_set_uint8(v___x_197_, sizeof(void*)*1, v___x_196_);
v___x_198_ = lean_array_push(v_a_109_, v___x_197_);
v___y_181_ = v___x_198_;
goto v___jp_180_;
}
v___jp_180_:
{
lean_object* v___x_182_; lean_object* v___x_184_; 
v___x_182_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__2));
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 9, v___x_182_);
lean_ctor_set(v___x_131_, 8, v___x_172_);
lean_ctor_set(v___x_131_, 7, v_relLeanFile_170_);
v___x_184_ = v___x_131_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_lakeEnv_112_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v_lakeArgs_x3f_113_);
lean_ctor_set(v_reuseFailAlloc_186_, 2, v_wsDir_114_);
lean_ctor_set(v_reuseFailAlloc_186_, 3, v_pkgIdx_115_);
lean_ctor_set(v_reuseFailAlloc_186_, 4, v_pkgName_116_);
lean_ctor_set(v_reuseFailAlloc_186_, 5, v_relPkgDir_117_);
lean_ctor_set(v_reuseFailAlloc_186_, 6, v_pkgDir_118_);
lean_ctor_set(v_reuseFailAlloc_186_, 7, v_relLeanFile_170_);
lean_ctor_set(v_reuseFailAlloc_186_, 8, v___x_172_);
lean_ctor_set(v_reuseFailAlloc_186_, 9, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_186_, 10, v_relManifestFile_121_);
lean_ctor_set(v_reuseFailAlloc_186_, 11, v_packageOverrides_122_);
lean_ctor_set(v_reuseFailAlloc_186_, 12, v_lakeOpts_123_);
lean_ctor_set(v_reuseFailAlloc_186_, 13, v_leanOpts_124_);
lean_ctor_set(v_reuseFailAlloc_186_, 14, v_scope_128_);
lean_ctor_set(v_reuseFailAlloc_186_, 15, v_remoteUrl_129_);
lean_ctor_set_uint8(v_reuseFailAlloc_186_, sizeof(void*)*16, v_reconfigure_125_);
lean_ctor_set_uint8(v_reuseFailAlloc_186_, sizeof(void*)*16 + 1, v_updateDeps_126_);
lean_ctor_set_uint8(v_reuseFailAlloc_186_, sizeof(void*)*16 + 2, v_updateToolchain_127_);
v___x_184_ = v_reuseFailAlloc_186_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v___x_185_; 
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v___y_181_);
return v___x_185_;
}
}
}
else
{
lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
lean_dec_ref(v___x_172_);
lean_dec_ref(v_relLeanFile_170_);
lean_inc_ref(v_tomlFile_175_);
v___x_199_ = l_Lake_resolvePath(v_tomlFile_175_);
v___x_200_ = lean_string_utf8_byte_size(v___x_199_);
v___x_201_ = lean_nat_dec_eq(v___x_200_, v___x_177_);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; lean_object* v___x_204_; 
lean_dec_ref(v_tomlFile_175_);
lean_dec_ref(v_leanFile_171_);
lean_dec_ref(v_name_107_);
v___x_202_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__1));
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 9, v___x_202_);
lean_ctor_set(v___x_131_, 8, v___x_199_);
lean_ctor_set(v___x_131_, 7, v_relTomlFile_174_);
v___x_204_ = v___x_131_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_lakeEnv_112_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v_lakeArgs_x3f_113_);
lean_ctor_set(v_reuseFailAlloc_206_, 2, v_wsDir_114_);
lean_ctor_set(v_reuseFailAlloc_206_, 3, v_pkgIdx_115_);
lean_ctor_set(v_reuseFailAlloc_206_, 4, v_pkgName_116_);
lean_ctor_set(v_reuseFailAlloc_206_, 5, v_relPkgDir_117_);
lean_ctor_set(v_reuseFailAlloc_206_, 6, v_pkgDir_118_);
lean_ctor_set(v_reuseFailAlloc_206_, 7, v_relTomlFile_174_);
lean_ctor_set(v_reuseFailAlloc_206_, 8, v___x_199_);
lean_ctor_set(v_reuseFailAlloc_206_, 9, v___x_202_);
lean_ctor_set(v_reuseFailAlloc_206_, 10, v_relManifestFile_121_);
lean_ctor_set(v_reuseFailAlloc_206_, 11, v_packageOverrides_122_);
lean_ctor_set(v_reuseFailAlloc_206_, 12, v_lakeOpts_123_);
lean_ctor_set(v_reuseFailAlloc_206_, 13, v_leanOpts_124_);
lean_ctor_set(v_reuseFailAlloc_206_, 14, v_scope_128_);
lean_ctor_set(v_reuseFailAlloc_206_, 15, v_remoteUrl_129_);
lean_ctor_set_uint8(v_reuseFailAlloc_206_, sizeof(void*)*16, v_reconfigure_125_);
lean_ctor_set_uint8(v_reuseFailAlloc_206_, sizeof(void*)*16 + 1, v_updateDeps_126_);
lean_ctor_set_uint8(v_reuseFailAlloc_206_, sizeof(void*)*16 + 2, v_updateToolchain_127_);
v___x_204_ = v_reuseFailAlloc_206_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
lean_object* v___x_205_; 
v___x_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v_a_109_);
return v___x_205_;
}
}
else
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
lean_dec_ref(v___x_199_);
lean_dec_ref(v_relTomlFile_174_);
lean_del_object(v___x_131_);
lean_dec_ref(v_remoteUrl_129_);
lean_dec_ref(v_scope_128_);
lean_dec_ref(v_leanOpts_124_);
lean_dec(v_lakeOpts_123_);
lean_dec_ref(v_packageOverrides_122_);
lean_dec_ref(v_relManifestFile_121_);
lean_dec_ref(v_pkgDir_118_);
lean_dec_ref(v_relPkgDir_117_);
lean_dec(v_pkgName_116_);
lean_dec(v_pkgIdx_115_);
lean_dec_ref(v_wsDir_114_);
lean_dec(v_lakeArgs_x3f_113_);
lean_dec_ref(v_lakeEnv_112_);
v___x_207_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__7));
v___x_208_ = lean_string_append(v_name_107_, v___x_207_);
v___x_209_ = lean_string_append(v___x_208_, v_leanFile_171_);
lean_dec_ref(v_leanFile_171_);
v___x_210_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__8));
v___x_211_ = lean_string_append(v___x_209_, v___x_210_);
v___x_212_ = lean_string_append(v___x_211_, v_tomlFile_175_);
lean_dec_ref(v_tomlFile_175_);
v___x_213_ = 3;
v___x_214_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_214_, 0, v___x_212_);
lean_ctor_set_uint8(v___x_214_, sizeof(void*)*1, v___x_213_);
v___x_215_ = lean_array_get_size(v_a_109_);
v___x_216_ = lean_array_push(v_a_109_, v___x_214_);
v___x_217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_215_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
return v___x_217_;
}
}
}
}
}
else
{
lean_object* v_lakeEnv_220_; lean_object* v_lakeArgs_x3f_221_; lean_object* v_wsDir_222_; lean_object* v_pkgIdx_223_; lean_object* v_pkgName_224_; lean_object* v_relPkgDir_225_; lean_object* v_pkgDir_226_; lean_object* v_relConfigFile_227_; lean_object* v_configFile_228_; lean_object* v_relManifestFile_229_; lean_object* v_packageOverrides_230_; lean_object* v_lakeOpts_231_; lean_object* v_leanOpts_232_; uint8_t v_reconfigure_233_; uint8_t v_updateDeps_234_; uint8_t v_updateToolchain_235_; lean_object* v_scope_236_; lean_object* v_remoteUrl_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_257_; 
lean_inc_ref(v_configLang_x3f_111_);
v_lakeEnv_220_ = lean_ctor_get(v_cfg_108_, 0);
v_lakeArgs_x3f_221_ = lean_ctor_get(v_cfg_108_, 1);
v_wsDir_222_ = lean_ctor_get(v_cfg_108_, 2);
v_pkgIdx_223_ = lean_ctor_get(v_cfg_108_, 3);
v_pkgName_224_ = lean_ctor_get(v_cfg_108_, 4);
v_relPkgDir_225_ = lean_ctor_get(v_cfg_108_, 5);
v_pkgDir_226_ = lean_ctor_get(v_cfg_108_, 6);
v_relConfigFile_227_ = lean_ctor_get(v_cfg_108_, 7);
v_configFile_228_ = lean_ctor_get(v_cfg_108_, 8);
v_relManifestFile_229_ = lean_ctor_get(v_cfg_108_, 10);
v_packageOverrides_230_ = lean_ctor_get(v_cfg_108_, 11);
v_lakeOpts_231_ = lean_ctor_get(v_cfg_108_, 12);
v_leanOpts_232_ = lean_ctor_get(v_cfg_108_, 13);
v_reconfigure_233_ = lean_ctor_get_uint8(v_cfg_108_, sizeof(void*)*16);
v_updateDeps_234_ = lean_ctor_get_uint8(v_cfg_108_, sizeof(void*)*16 + 1);
v_updateToolchain_235_ = lean_ctor_get_uint8(v_cfg_108_, sizeof(void*)*16 + 2);
v_scope_236_ = lean_ctor_get(v_cfg_108_, 14);
v_remoteUrl_237_ = lean_ctor_get(v_cfg_108_, 15);
v_isSharedCheck_257_ = !lean_is_exclusive(v_cfg_108_);
if (v_isSharedCheck_257_ == 0)
{
lean_object* v_unused_258_; 
v_unused_258_ = lean_ctor_get(v_cfg_108_, 9);
lean_dec(v_unused_258_);
v___x_239_ = v_cfg_108_;
v_isShared_240_ = v_isSharedCheck_257_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_remoteUrl_237_);
lean_inc(v_scope_236_);
lean_inc(v_leanOpts_232_);
lean_inc(v_lakeOpts_231_);
lean_inc(v_packageOverrides_230_);
lean_inc(v_relManifestFile_229_);
lean_inc(v_configFile_228_);
lean_inc(v_relConfigFile_227_);
lean_inc(v_pkgDir_226_);
lean_inc(v_relPkgDir_225_);
lean_inc(v_pkgName_224_);
lean_inc(v_pkgIdx_223_);
lean_inc(v_wsDir_222_);
lean_inc(v_lakeArgs_x3f_221_);
lean_inc(v_lakeEnv_220_);
lean_dec(v_cfg_108_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_257_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
lean_inc_ref(v_configFile_228_);
v___x_241_ = l_Lake_resolvePath(v_configFile_228_);
v___x_242_ = lean_string_utf8_byte_size(v___x_241_);
v___x_243_ = lean_unsigned_to_nat(0u);
v___x_244_ = lean_nat_dec_eq(v___x_242_, v___x_243_);
if (v___x_244_ == 0)
{
lean_object* v___x_246_; 
lean_dec_ref(v_configFile_228_);
lean_dec_ref(v_name_107_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 8, v___x_241_);
v___x_246_ = v___x_239_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_lakeEnv_220_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v_lakeArgs_x3f_221_);
lean_ctor_set(v_reuseFailAlloc_248_, 2, v_wsDir_222_);
lean_ctor_set(v_reuseFailAlloc_248_, 3, v_pkgIdx_223_);
lean_ctor_set(v_reuseFailAlloc_248_, 4, v_pkgName_224_);
lean_ctor_set(v_reuseFailAlloc_248_, 5, v_relPkgDir_225_);
lean_ctor_set(v_reuseFailAlloc_248_, 6, v_pkgDir_226_);
lean_ctor_set(v_reuseFailAlloc_248_, 7, v_relConfigFile_227_);
lean_ctor_set(v_reuseFailAlloc_248_, 8, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_248_, 9, v_configLang_x3f_111_);
lean_ctor_set(v_reuseFailAlloc_248_, 10, v_relManifestFile_229_);
lean_ctor_set(v_reuseFailAlloc_248_, 11, v_packageOverrides_230_);
lean_ctor_set(v_reuseFailAlloc_248_, 12, v_lakeOpts_231_);
lean_ctor_set(v_reuseFailAlloc_248_, 13, v_leanOpts_232_);
lean_ctor_set(v_reuseFailAlloc_248_, 14, v_scope_236_);
lean_ctor_set(v_reuseFailAlloc_248_, 15, v_remoteUrl_237_);
lean_ctor_set_uint8(v_reuseFailAlloc_248_, sizeof(void*)*16, v_reconfigure_233_);
lean_ctor_set_uint8(v_reuseFailAlloc_248_, sizeof(void*)*16 + 1, v_updateDeps_234_);
lean_ctor_set_uint8(v_reuseFailAlloc_248_, sizeof(void*)*16 + 2, v_updateToolchain_235_);
v___x_246_ = v_reuseFailAlloc_248_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
lean_object* v___x_247_; 
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v_a_109_);
return v___x_247_;
}
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
lean_dec_ref(v___x_241_);
lean_del_object(v___x_239_);
lean_dec_ref(v_remoteUrl_237_);
lean_dec_ref(v_scope_236_);
lean_dec_ref(v_leanOpts_232_);
lean_dec(v_lakeOpts_231_);
lean_dec_ref(v_packageOverrides_230_);
lean_dec_ref(v_relManifestFile_229_);
lean_dec_ref(v_relConfigFile_227_);
lean_dec_ref(v_pkgDir_226_);
lean_dec_ref(v_relPkgDir_225_);
lean_dec(v_pkgName_224_);
lean_dec(v_pkgIdx_223_);
lean_dec_ref(v_wsDir_222_);
lean_dec(v_lakeArgs_x3f_221_);
lean_dec_ref(v_configLang_x3f_111_);
lean_dec_ref(v_lakeEnv_220_);
v___x_249_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__3));
v___x_250_ = lean_string_append(v_name_107_, v___x_249_);
v___x_251_ = lean_string_append(v___x_250_, v_configFile_228_);
lean_dec_ref(v_configFile_228_);
v___x_252_ = 3;
v___x_253_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_253_, 0, v___x_251_);
lean_ctor_set_uint8(v___x_253_, sizeof(void*)*1, v___x_252_);
v___x_254_ = lean_array_get_size(v_a_109_);
v___x_255_ = lean_array_push(v_a_109_, v___x_253_);
v___x_256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_254_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
return v___x_256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveConfigFile___boxed(lean_object* v_name_259_, lean_object* v_cfg_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lake_resolveConfigFile(v_name_259_, v_cfg_260_, v_a_261_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadConfigFile___redArg(lean_object* v_cfg_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_configLang_x3f_267_; lean_object* v_val_268_; uint8_t v___x_269_; 
v_configLang_x3f_267_ = lean_ctor_get(v_cfg_264_, 9);
v_val_268_ = lean_ctor_get(v_configLang_x3f_267_, 0);
v___x_269_ = lean_unbox(v_val_268_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; 
v___x_270_ = l_Lake_loadLeanConfig(v_cfg_264_, v_a_265_);
return v___x_270_;
}
else
{
lean_object* v___x_271_; 
v___x_271_ = l_Lake_loadTomlConfig(v_cfg_264_, v_a_265_);
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadConfigFile___redArg___boxed(lean_object* v_cfg_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lake_loadConfigFile___redArg(v_cfg_272_, v_a_273_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadConfigFile(lean_object* v_cfg_276_, lean_object* v_h_277_, lean_object* v_a_278_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Lake_loadConfigFile___redArg(v_cfg_276_, v_a_278_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadConfigFile___boxed(lean_object* v_cfg_281_, lean_object* v_h_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lake_loadConfigFile(v_cfg_281_, v_h_282_, v_a_283_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackage(lean_object* v_cfg_287_, lean_object* v_a_288_){
_start:
{
lean_object* v_lakeEnv_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v_lakeEnv_290_ = lean_ctor_get(v_cfg_287_, 0);
v___x_291_ = l_Lean_searchPathRef;
v___x_292_ = l_Lake_Env_leanSearchPath(v_lakeEnv_290_);
v___x_293_ = lean_st_ref_set(v___x_291_, v___x_292_);
v___x_294_ = ((lean_object*)(l_Lake_loadPackage___closed__0));
v___x_295_ = l_Lake_resolveConfigFile(v___x_294_, v_cfg_287_, v_a_288_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_a_296_; lean_object* v_a_297_; lean_object* v___x_298_; 
v_a_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc_n(v_a_296_, 2);
v_a_297_ = lean_ctor_get(v___x_295_, 1);
lean_inc(v_a_297_);
lean_dec_ref(v___x_295_);
v___x_298_ = l_Lake_loadConfigFile___redArg(v_a_296_, v_a_297_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v_a_299_; lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_309_; 
v_a_299_ = lean_ctor_get(v___x_298_, 0);
v_a_300_ = lean_ctor_get(v___x_298_, 1);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_309_ == 0)
{
v___x_302_ = v___x_298_;
v_isShared_303_ = v_isSharedCheck_309_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_inc(v_a_299_);
lean_dec(v___x_298_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_309_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v_pkgIdx_304_; lean_object* v___x_305_; lean_object* v___x_307_; 
v_pkgIdx_304_ = lean_ctor_get(v_a_296_, 3);
lean_inc(v_pkgIdx_304_);
v___x_305_ = l_Lake_mkPackage(v_a_296_, v_a_299_, v_pkgIdx_304_);
lean_dec(v_a_296_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v___x_305_);
v___x_307_ = v___x_302_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_a_300_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
else
{
lean_object* v_a_310_; lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
lean_dec(v_a_296_);
v_a_310_ = lean_ctor_get(v___x_298_, 0);
v_a_311_ = lean_ctor_get(v___x_298_, 1);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_318_ == 0)
{
v___x_313_ = v___x_298_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_inc(v_a_310_);
lean_dec(v___x_298_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_a_310_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_a_311_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
else
{
lean_object* v_a_319_; lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
v_a_319_ = lean_ctor_get(v___x_295_, 0);
v_a_320_ = lean_ctor_get(v___x_295_, 1);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v___x_295_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_inc(v_a_319_);
lean_dec(v___x_295_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_319_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_a_320_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackage___boxed(lean_object* v_cfg_328_, lean_object* v_a_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lake_loadPackage(v_cfg_328_, v_a_329_);
return v_res_331_;
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
