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
lean_object* v_pkgDecl_8_; lean_object* v_config_9_; lean_object* v_relPkgDir_10_; lean_object* v_pkgDir_11_; lean_object* v_relConfigFile_12_; lean_object* v_configFile_13_; lean_object* v_relManifestFile_14_; lean_object* v_scope_15_; lean_object* v_remoteUrl_16_; lean_object* v_depConfigs_17_; lean_object* v_targetDecls_18_; lean_object* v_targetDeclMap_19_; lean_object* v_defaultTargets_20_; lean_object* v_cacheServices_21_; lean_object* v_scripts_22_; lean_object* v_defaultScripts_23_; lean_object* v_postUpdateHooks_24_; lean_object* v_testDriver_25_; lean_object* v_lintDriver_26_; lean_object* v_baseName_27_; lean_object* v_keyName_28_; lean_object* v_origName_29_; lean_object* v_buildArchive_30_; lean_object* v___x_31_; 
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
v_cacheServices_21_ = lean_ctor_get(v_fileCfg_6_, 6);
lean_inc(v_cacheServices_21_);
v_scripts_22_ = lean_ctor_get(v_fileCfg_6_, 7);
lean_inc(v_scripts_22_);
v_defaultScripts_23_ = lean_ctor_get(v_fileCfg_6_, 8);
lean_inc_ref(v_defaultScripts_23_);
v_postUpdateHooks_24_ = lean_ctor_get(v_fileCfg_6_, 9);
lean_inc_ref(v_postUpdateHooks_24_);
v_testDriver_25_ = lean_ctor_get(v_fileCfg_6_, 10);
lean_inc_ref(v_testDriver_25_);
v_lintDriver_26_ = lean_ctor_get(v_fileCfg_6_, 11);
lean_inc_ref(v_lintDriver_26_);
lean_dec_ref(v_fileCfg_6_);
v_baseName_27_ = lean_ctor_get(v_pkgDecl_8_, 0);
lean_inc(v_baseName_27_);
v_keyName_28_ = lean_ctor_get(v_pkgDecl_8_, 1);
lean_inc(v_keyName_28_);
v_origName_29_ = lean_ctor_get(v_pkgDecl_8_, 2);
lean_inc(v_origName_29_);
lean_dec_ref(v_pkgDecl_8_);
v_buildArchive_30_ = lean_ctor_get(v_config_9_, 11);
v___x_31_ = ((lean_object*)(l_Lake_mkPackage___closed__0));
if (lean_obj_tag(v_buildArchive_30_) == 1)
{
lean_object* v_val_32_; lean_object* v___x_33_; 
v_val_32_ = lean_ctor_get(v_buildArchive_30_, 0);
lean_inc(v_val_32_);
lean_inc_ref(v_remoteUrl_16_);
lean_inc_ref(v_scope_15_);
lean_inc_ref(v_relManifestFile_14_);
lean_inc_ref(v_relConfigFile_12_);
lean_inc_ref(v_configFile_13_);
lean_inc_ref(v_relPkgDir_10_);
lean_inc_ref(v_pkgDir_11_);
v___x_33_ = lean_alloc_ctor(0, 25, 0);
lean_ctor_set(v___x_33_, 0, v_wsIdx_7_);
lean_ctor_set(v___x_33_, 1, v_baseName_27_);
lean_ctor_set(v___x_33_, 2, v_keyName_28_);
lean_ctor_set(v___x_33_, 3, v_origName_29_);
lean_ctor_set(v___x_33_, 4, v_pkgDir_11_);
lean_ctor_set(v___x_33_, 5, v_relPkgDir_10_);
lean_ctor_set(v___x_33_, 6, v_config_9_);
lean_ctor_set(v___x_33_, 7, v_configFile_13_);
lean_ctor_set(v___x_33_, 8, v_relConfigFile_12_);
lean_ctor_set(v___x_33_, 9, v_relManifestFile_14_);
lean_ctor_set(v___x_33_, 10, v_scope_15_);
lean_ctor_set(v___x_33_, 11, v_remoteUrl_16_);
lean_ctor_set(v___x_33_, 12, v_depConfigs_17_);
lean_ctor_set(v___x_33_, 13, v___x_31_);
lean_ctor_set(v___x_33_, 14, v___x_31_);
lean_ctor_set(v___x_33_, 15, v_targetDecls_18_);
lean_ctor_set(v___x_33_, 16, v_targetDeclMap_19_);
lean_ctor_set(v___x_33_, 17, v_defaultTargets_20_);
lean_ctor_set(v___x_33_, 18, v_cacheServices_21_);
lean_ctor_set(v___x_33_, 19, v_scripts_22_);
lean_ctor_set(v___x_33_, 20, v_defaultScripts_23_);
lean_ctor_set(v___x_33_, 21, v_postUpdateHooks_24_);
lean_ctor_set(v___x_33_, 22, v_val_32_);
lean_ctor_set(v___x_33_, 23, v_testDriver_25_);
lean_ctor_set(v___x_33_, 24, v_lintDriver_26_);
return v___x_33_;
}
else
{
uint8_t v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_34_ = 0;
lean_inc(v_baseName_27_);
v___x_35_ = l_Lean_Name_toString(v_baseName_27_, v___x_34_);
v___x_36_ = ((lean_object*)(l_Lake_mkPackage___closed__1));
v___x_37_ = lean_string_append(v___x_35_, v___x_36_);
v___x_38_ = l_System_Platform_target;
v___x_39_ = lean_string_append(v___x_37_, v___x_38_);
v___x_40_ = ((lean_object*)(l_Lake_mkPackage___closed__2));
v___x_41_ = lean_string_append(v___x_39_, v___x_40_);
lean_inc_ref(v_remoteUrl_16_);
lean_inc_ref(v_scope_15_);
lean_inc_ref(v_relManifestFile_14_);
lean_inc_ref(v_relConfigFile_12_);
lean_inc_ref(v_configFile_13_);
lean_inc_ref(v_relPkgDir_10_);
lean_inc_ref(v_pkgDir_11_);
v___x_42_ = lean_alloc_ctor(0, 25, 0);
lean_ctor_set(v___x_42_, 0, v_wsIdx_7_);
lean_ctor_set(v___x_42_, 1, v_baseName_27_);
lean_ctor_set(v___x_42_, 2, v_keyName_28_);
lean_ctor_set(v___x_42_, 3, v_origName_29_);
lean_ctor_set(v___x_42_, 4, v_pkgDir_11_);
lean_ctor_set(v___x_42_, 5, v_relPkgDir_10_);
lean_ctor_set(v___x_42_, 6, v_config_9_);
lean_ctor_set(v___x_42_, 7, v_configFile_13_);
lean_ctor_set(v___x_42_, 8, v_relConfigFile_12_);
lean_ctor_set(v___x_42_, 9, v_relManifestFile_14_);
lean_ctor_set(v___x_42_, 10, v_scope_15_);
lean_ctor_set(v___x_42_, 11, v_remoteUrl_16_);
lean_ctor_set(v___x_42_, 12, v_depConfigs_17_);
lean_ctor_set(v___x_42_, 13, v___x_31_);
lean_ctor_set(v___x_42_, 14, v___x_31_);
lean_ctor_set(v___x_42_, 15, v_targetDecls_18_);
lean_ctor_set(v___x_42_, 16, v_targetDeclMap_19_);
lean_ctor_set(v___x_42_, 17, v_defaultTargets_20_);
lean_ctor_set(v___x_42_, 18, v_cacheServices_21_);
lean_ctor_set(v___x_42_, 19, v_scripts_22_);
lean_ctor_set(v___x_42_, 20, v_defaultScripts_23_);
lean_ctor_set(v___x_42_, 21, v_postUpdateHooks_24_);
lean_ctor_set(v___x_42_, 22, v___x_41_);
lean_ctor_set(v___x_42_, 23, v_testDriver_25_);
lean_ctor_set(v___x_42_, 24, v_lintDriver_26_);
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkPackage___boxed(lean_object* v_loadCfg_43_, lean_object* v_fileCfg_44_, lean_object* v_wsIdx_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lake_mkPackage(v_loadCfg_43_, v_fileCfg_44_, v_wsIdx_45_);
lean_dec_ref(v_loadCfg_43_);
return v_res_46_;
}
}
LEAN_EXPORT uint8_t l_Lake_configFileExists(lean_object* v_cfgFile_49_){
_start:
{
lean_object* v___x_51_; 
lean_inc_ref(v_cfgFile_49_);
v___x_51_ = l_System_FilePath_extension(v_cfgFile_49_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v___x_52_; lean_object* v_leanFile_53_; lean_object* v___x_54_; lean_object* v_tomlFile_55_; uint8_t v___x_56_; 
v___x_52_ = ((lean_object*)(l_Lake_configFileExists___closed__0));
lean_inc_ref(v_cfgFile_49_);
v_leanFile_53_ = l_System_FilePath_addExtension(v_cfgFile_49_, v___x_52_);
v___x_54_ = ((lean_object*)(l_Lake_configFileExists___closed__1));
v_tomlFile_55_ = l_System_FilePath_addExtension(v_cfgFile_49_, v___x_54_);
v___x_56_ = l_System_FilePath_pathExists(v_leanFile_53_);
lean_dec_ref(v_leanFile_53_);
if (v___x_56_ == 0)
{
uint8_t v___x_57_; 
v___x_57_ = l_System_FilePath_pathExists(v_tomlFile_55_);
lean_dec_ref(v_tomlFile_55_);
return v___x_57_;
}
else
{
lean_dec_ref(v_tomlFile_55_);
return v___x_56_;
}
}
else
{
uint8_t v___x_58_; 
lean_dec_ref_known(v___x_51_, 1);
v___x_58_ = l_System_FilePath_pathExists(v_cfgFile_49_);
lean_dec_ref(v_cfgFile_49_);
return v___x_58_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_configFileExists___boxed(lean_object* v_cfgFile_59_, lean_object* v_a_60_){
_start:
{
uint8_t v_res_61_; lean_object* v_r_62_; 
v_res_61_ = l_Lake_configFileExists(v_cfgFile_59_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
LEAN_EXPORT lean_object* l_Lake_realConfigFile(lean_object* v_cfgFile_63_){
_start:
{
lean_object* v___x_65_; 
lean_inc_ref(v_cfgFile_63_);
v___x_65_ = l_System_FilePath_extension(v_cfgFile_63_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_66_ = ((lean_object*)(l_Lake_configFileExists___closed__0));
lean_inc_ref(v_cfgFile_63_);
v___x_67_ = l_System_FilePath_addExtension(v_cfgFile_63_, v___x_66_);
v___x_68_ = l_Lake_resolvePath(v___x_67_);
v___x_69_ = lean_string_utf8_byte_size(v___x_68_);
v___x_70_ = lean_unsigned_to_nat(0u);
v___x_71_ = lean_nat_dec_eq(v___x_69_, v___x_70_);
if (v___x_71_ == 0)
{
lean_dec_ref(v_cfgFile_63_);
return v___x_68_;
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
lean_dec_ref(v___x_68_);
v___x_72_ = ((lean_object*)(l_Lake_configFileExists___closed__1));
v___x_73_ = l_System_FilePath_addExtension(v_cfgFile_63_, v___x_72_);
v___x_74_ = l_Lake_resolvePath(v___x_73_);
return v___x_74_;
}
}
else
{
lean_object* v___x_75_; 
lean_dec_ref_known(v___x_65_, 1);
v___x_75_ = l_Lake_resolvePath(v_cfgFile_63_);
return v___x_75_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_realConfigFile___boxed(lean_object* v_cfgFile_76_, lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lake_realConfigFile(v_cfgFile_76_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveConfigFile(lean_object* v_name_92_, lean_object* v_cfg_93_, lean_object* v_a_94_){
_start:
{
lean_object* v_configLang_x3f_96_; 
v_configLang_x3f_96_ = lean_ctor_get(v_cfg_93_, 9);
if (lean_obj_tag(v_configLang_x3f_96_) == 0)
{
lean_object* v_lakeEnv_97_; lean_object* v_lakeArgs_x3f_98_; lean_object* v_wsDir_99_; lean_object* v_pkgIdx_100_; lean_object* v_pkgName_101_; lean_object* v_relPkgDir_102_; lean_object* v_pkgDir_103_; lean_object* v_relConfigFile_104_; lean_object* v_configFile_105_; lean_object* v_relManifestFile_106_; lean_object* v_packageOverrides_107_; lean_object* v_lakeOpts_108_; lean_object* v_leanOpts_109_; uint8_t v_reconfigure_110_; uint8_t v_updateDeps_111_; uint8_t v_updateToolchain_112_; lean_object* v_scope_113_; lean_object* v_remoteUrl_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_201_; 
v_lakeEnv_97_ = lean_ctor_get(v_cfg_93_, 0);
v_lakeArgs_x3f_98_ = lean_ctor_get(v_cfg_93_, 1);
v_wsDir_99_ = lean_ctor_get(v_cfg_93_, 2);
v_pkgIdx_100_ = lean_ctor_get(v_cfg_93_, 3);
v_pkgName_101_ = lean_ctor_get(v_cfg_93_, 4);
v_relPkgDir_102_ = lean_ctor_get(v_cfg_93_, 5);
v_pkgDir_103_ = lean_ctor_get(v_cfg_93_, 6);
v_relConfigFile_104_ = lean_ctor_get(v_cfg_93_, 7);
v_configFile_105_ = lean_ctor_get(v_cfg_93_, 8);
v_relManifestFile_106_ = lean_ctor_get(v_cfg_93_, 10);
v_packageOverrides_107_ = lean_ctor_get(v_cfg_93_, 11);
v_lakeOpts_108_ = lean_ctor_get(v_cfg_93_, 12);
v_leanOpts_109_ = lean_ctor_get(v_cfg_93_, 13);
v_reconfigure_110_ = lean_ctor_get_uint8(v_cfg_93_, sizeof(void*)*16);
v_updateDeps_111_ = lean_ctor_get_uint8(v_cfg_93_, sizeof(void*)*16 + 1);
v_updateToolchain_112_ = lean_ctor_get_uint8(v_cfg_93_, sizeof(void*)*16 + 2);
v_scope_113_ = lean_ctor_get(v_cfg_93_, 14);
v_remoteUrl_114_ = lean_ctor_get(v_cfg_93_, 15);
v_isSharedCheck_201_ = !lean_is_exclusive(v_cfg_93_);
if (v_isSharedCheck_201_ == 0)
{
lean_object* v_unused_202_; 
v_unused_202_ = lean_ctor_get(v_cfg_93_, 9);
lean_dec(v_unused_202_);
v___x_116_ = v_cfg_93_;
v_isShared_117_ = v_isSharedCheck_201_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_remoteUrl_114_);
lean_inc(v_scope_113_);
lean_inc(v_leanOpts_109_);
lean_inc(v_lakeOpts_108_);
lean_inc(v_packageOverrides_107_);
lean_inc(v_relManifestFile_106_);
lean_inc(v_configFile_105_);
lean_inc(v_relConfigFile_104_);
lean_inc(v_pkgDir_103_);
lean_inc(v_relPkgDir_102_);
lean_inc(v_pkgName_101_);
lean_inc(v_pkgIdx_100_);
lean_inc(v_wsDir_99_);
lean_inc(v_lakeArgs_x3f_98_);
lean_inc(v_lakeEnv_97_);
lean_dec(v_cfg_93_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_201_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_118_; 
lean_inc_ref(v_relConfigFile_104_);
v___x_118_ = l_System_FilePath_extension(v_relConfigFile_104_);
if (lean_obj_tag(v___x_118_) == 1)
{
lean_object* v_val_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v_val_119_ = lean_ctor_get(v___x_118_, 0);
lean_inc(v_val_119_);
lean_dec_ref_known(v___x_118_, 1);
lean_inc_ref(v_configFile_105_);
v___x_120_ = l_Lake_resolvePath(v_configFile_105_);
v___x_121_ = lean_string_utf8_byte_size(v___x_120_);
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = lean_nat_dec_eq(v___x_121_, v___x_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; uint8_t v___x_125_; 
lean_dec_ref(v_configFile_105_);
v___x_124_ = ((lean_object*)(l_Lake_configFileExists___closed__0));
v___x_125_ = lean_string_dec_eq(v_val_119_, v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = ((lean_object*)(l_Lake_configFileExists___closed__1));
v___x_127_ = lean_string_dec_eq(v_val_119_, v___x_126_);
lean_dec(v_val_119_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
lean_del_object(v___x_116_);
lean_dec_ref(v_remoteUrl_114_);
lean_dec_ref(v_scope_113_);
lean_dec_ref(v_leanOpts_109_);
lean_dec(v_lakeOpts_108_);
lean_dec_ref(v_packageOverrides_107_);
lean_dec_ref(v_relManifestFile_106_);
lean_dec_ref(v_relConfigFile_104_);
lean_dec_ref(v_pkgDir_103_);
lean_dec_ref(v_relPkgDir_102_);
lean_dec(v_pkgName_101_);
lean_dec(v_pkgIdx_100_);
lean_dec_ref(v_wsDir_99_);
lean_dec(v_lakeArgs_x3f_98_);
lean_dec_ref(v_lakeEnv_97_);
v___x_128_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__0));
v___x_129_ = lean_string_append(v_name_92_, v___x_128_);
v___x_130_ = lean_string_append(v___x_129_, v___x_120_);
lean_dec_ref(v___x_120_);
v___x_131_ = 3;
v___x_132_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_132_, 0, v___x_130_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*1, v___x_131_);
v___x_133_ = lean_array_get_size(v_a_94_);
v___x_134_ = lean_array_push(v_a_94_, v___x_132_);
v___x_135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_133_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
return v___x_135_;
}
else
{
lean_object* v___x_136_; lean_object* v___x_138_; 
lean_dec_ref(v_name_92_);
v___x_136_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__1));
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 9, v___x_136_);
lean_ctor_set(v___x_116_, 8, v___x_120_);
v___x_138_ = v___x_116_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_lakeEnv_97_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v_lakeArgs_x3f_98_);
lean_ctor_set(v_reuseFailAlloc_140_, 2, v_wsDir_99_);
lean_ctor_set(v_reuseFailAlloc_140_, 3, v_pkgIdx_100_);
lean_ctor_set(v_reuseFailAlloc_140_, 4, v_pkgName_101_);
lean_ctor_set(v_reuseFailAlloc_140_, 5, v_relPkgDir_102_);
lean_ctor_set(v_reuseFailAlloc_140_, 6, v_pkgDir_103_);
lean_ctor_set(v_reuseFailAlloc_140_, 7, v_relConfigFile_104_);
lean_ctor_set(v_reuseFailAlloc_140_, 8, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_140_, 9, v___x_136_);
lean_ctor_set(v_reuseFailAlloc_140_, 10, v_relManifestFile_106_);
lean_ctor_set(v_reuseFailAlloc_140_, 11, v_packageOverrides_107_);
lean_ctor_set(v_reuseFailAlloc_140_, 12, v_lakeOpts_108_);
lean_ctor_set(v_reuseFailAlloc_140_, 13, v_leanOpts_109_);
lean_ctor_set(v_reuseFailAlloc_140_, 14, v_scope_113_);
lean_ctor_set(v_reuseFailAlloc_140_, 15, v_remoteUrl_114_);
lean_ctor_set_uint8(v_reuseFailAlloc_140_, sizeof(void*)*16, v_reconfigure_110_);
lean_ctor_set_uint8(v_reuseFailAlloc_140_, sizeof(void*)*16 + 1, v_updateDeps_111_);
lean_ctor_set_uint8(v_reuseFailAlloc_140_, sizeof(void*)*16 + 2, v_updateToolchain_112_);
v___x_138_ = v_reuseFailAlloc_140_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
lean_object* v___x_139_; 
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v_a_94_);
return v___x_139_;
}
}
}
else
{
lean_object* v___x_141_; lean_object* v___x_143_; 
lean_dec(v_val_119_);
lean_dec_ref(v_name_92_);
v___x_141_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__2));
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 9, v___x_141_);
lean_ctor_set(v___x_116_, 8, v___x_120_);
v___x_143_ = v___x_116_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_lakeEnv_97_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v_lakeArgs_x3f_98_);
lean_ctor_set(v_reuseFailAlloc_145_, 2, v_wsDir_99_);
lean_ctor_set(v_reuseFailAlloc_145_, 3, v_pkgIdx_100_);
lean_ctor_set(v_reuseFailAlloc_145_, 4, v_pkgName_101_);
lean_ctor_set(v_reuseFailAlloc_145_, 5, v_relPkgDir_102_);
lean_ctor_set(v_reuseFailAlloc_145_, 6, v_pkgDir_103_);
lean_ctor_set(v_reuseFailAlloc_145_, 7, v_relConfigFile_104_);
lean_ctor_set(v_reuseFailAlloc_145_, 8, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_145_, 9, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_145_, 10, v_relManifestFile_106_);
lean_ctor_set(v_reuseFailAlloc_145_, 11, v_packageOverrides_107_);
lean_ctor_set(v_reuseFailAlloc_145_, 12, v_lakeOpts_108_);
lean_ctor_set(v_reuseFailAlloc_145_, 13, v_leanOpts_109_);
lean_ctor_set(v_reuseFailAlloc_145_, 14, v_scope_113_);
lean_ctor_set(v_reuseFailAlloc_145_, 15, v_remoteUrl_114_);
lean_ctor_set_uint8(v_reuseFailAlloc_145_, sizeof(void*)*16, v_reconfigure_110_);
lean_ctor_set_uint8(v_reuseFailAlloc_145_, sizeof(void*)*16 + 1, v_updateDeps_111_);
lean_ctor_set_uint8(v_reuseFailAlloc_145_, sizeof(void*)*16 + 2, v_updateToolchain_112_);
v___x_143_ = v_reuseFailAlloc_145_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_144_; 
v___x_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v_a_94_);
return v___x_144_;
}
}
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
lean_dec_ref(v___x_120_);
lean_dec(v_val_119_);
lean_del_object(v___x_116_);
lean_dec_ref(v_remoteUrl_114_);
lean_dec_ref(v_scope_113_);
lean_dec_ref(v_leanOpts_109_);
lean_dec(v_lakeOpts_108_);
lean_dec_ref(v_packageOverrides_107_);
lean_dec_ref(v_relManifestFile_106_);
lean_dec_ref(v_relConfigFile_104_);
lean_dec_ref(v_pkgDir_103_);
lean_dec_ref(v_relPkgDir_102_);
lean_dec(v_pkgName_101_);
lean_dec(v_pkgIdx_100_);
lean_dec_ref(v_wsDir_99_);
lean_dec(v_lakeArgs_x3f_98_);
lean_dec_ref(v_lakeEnv_97_);
v___x_146_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__3));
v___x_147_ = lean_string_append(v_name_92_, v___x_146_);
v___x_148_ = lean_string_append(v___x_147_, v_configFile_105_);
lean_dec_ref(v_configFile_105_);
v___x_149_ = 3;
v___x_150_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_150_, 0, v___x_148_);
lean_ctor_set_uint8(v___x_150_, sizeof(void*)*1, v___x_149_);
v___x_151_ = lean_array_get_size(v_a_94_);
v___x_152_ = lean_array_push(v_a_94_, v___x_150_);
v___x_153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_151_);
lean_ctor_set(v___x_153_, 1, v___x_152_);
return v___x_153_;
}
}
else
{
lean_object* v___x_154_; lean_object* v_relLeanFile_155_; lean_object* v___x_156_; lean_object* v_relTomlFile_157_; lean_object* v_leanFile_158_; lean_object* v_tomlFile_159_; lean_object* v___x_160_; lean_object* v___y_162_; lean_object* v___x_168_; lean_object* v___x_169_; uint8_t v___x_170_; 
lean_dec(v___x_118_);
lean_dec_ref(v_configFile_105_);
v___x_154_ = ((lean_object*)(l_Lake_configFileExists___closed__0));
lean_inc_ref(v_relConfigFile_104_);
v_relLeanFile_155_ = l_System_FilePath_addExtension(v_relConfigFile_104_, v___x_154_);
v___x_156_ = ((lean_object*)(l_Lake_configFileExists___closed__1));
v_relTomlFile_157_ = l_System_FilePath_addExtension(v_relConfigFile_104_, v___x_156_);
lean_inc_ref(v_relLeanFile_155_);
lean_inc_ref_n(v_pkgDir_103_, 2);
v_leanFile_158_ = l_Lake_joinRelative(v_pkgDir_103_, v_relLeanFile_155_);
lean_inc_ref(v_relTomlFile_157_);
v_tomlFile_159_ = l_Lake_joinRelative(v_pkgDir_103_, v_relTomlFile_157_);
lean_inc_ref(v_leanFile_158_);
v___x_160_ = l_Lake_resolvePath(v_leanFile_158_);
v___x_168_ = lean_string_utf8_byte_size(v___x_160_);
v___x_169_ = lean_unsigned_to_nat(0u);
v___x_170_ = lean_nat_dec_eq(v___x_168_, v___x_169_);
if (v___x_170_ == 0)
{
uint8_t v___x_171_; 
lean_dec_ref(v_leanFile_158_);
v___x_171_ = l_System_FilePath_pathExists(v_tomlFile_159_);
lean_dec_ref(v_tomlFile_159_);
if (v___x_171_ == 0)
{
lean_dec_ref(v_relTomlFile_157_);
lean_dec_ref(v_name_92_);
v___y_162_ = v_a_94_;
goto v___jp_161_;
}
else
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; uint8_t v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_172_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__4));
v___x_173_ = lean_string_append(v_name_92_, v___x_172_);
v___x_174_ = lean_string_append(v___x_173_, v_relLeanFile_155_);
v___x_175_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__5));
v___x_176_ = lean_string_append(v___x_174_, v___x_175_);
v___x_177_ = lean_string_append(v___x_176_, v_relTomlFile_157_);
lean_dec_ref(v_relTomlFile_157_);
v___x_178_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__6));
v___x_179_ = lean_string_append(v___x_177_, v___x_178_);
v___x_180_ = lean_string_append(v___x_179_, v_relLeanFile_155_);
v___x_181_ = 1;
v___x_182_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_182_, 0, v___x_180_);
lean_ctor_set_uint8(v___x_182_, sizeof(void*)*1, v___x_181_);
v___x_183_ = lean_array_push(v_a_94_, v___x_182_);
v___y_162_ = v___x_183_;
goto v___jp_161_;
}
}
else
{
lean_object* v___x_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
lean_dec_ref(v___x_160_);
lean_dec_ref(v_relLeanFile_155_);
lean_del_object(v___x_116_);
lean_inc_ref(v_tomlFile_159_);
v___x_184_ = l_Lake_resolvePath(v_tomlFile_159_);
v___x_185_ = lean_string_utf8_byte_size(v___x_184_);
v___x_186_ = lean_nat_dec_eq(v___x_185_, v___x_169_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
lean_dec_ref(v_tomlFile_159_);
lean_dec_ref(v_leanFile_158_);
lean_dec_ref(v_name_92_);
v___x_187_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__1));
v___x_188_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v___x_188_, 0, v_lakeEnv_97_);
lean_ctor_set(v___x_188_, 1, v_lakeArgs_x3f_98_);
lean_ctor_set(v___x_188_, 2, v_wsDir_99_);
lean_ctor_set(v___x_188_, 3, v_pkgIdx_100_);
lean_ctor_set(v___x_188_, 4, v_pkgName_101_);
lean_ctor_set(v___x_188_, 5, v_relPkgDir_102_);
lean_ctor_set(v___x_188_, 6, v_pkgDir_103_);
lean_ctor_set(v___x_188_, 7, v_relTomlFile_157_);
lean_ctor_set(v___x_188_, 8, v___x_184_);
lean_ctor_set(v___x_188_, 9, v___x_187_);
lean_ctor_set(v___x_188_, 10, v_relManifestFile_106_);
lean_ctor_set(v___x_188_, 11, v_packageOverrides_107_);
lean_ctor_set(v___x_188_, 12, v_lakeOpts_108_);
lean_ctor_set(v___x_188_, 13, v_leanOpts_109_);
lean_ctor_set(v___x_188_, 14, v_scope_113_);
lean_ctor_set(v___x_188_, 15, v_remoteUrl_114_);
lean_ctor_set_uint8(v___x_188_, sizeof(void*)*16, v_reconfigure_110_);
lean_ctor_set_uint8(v___x_188_, sizeof(void*)*16 + 1, v_updateDeps_111_);
lean_ctor_set_uint8(v___x_188_, sizeof(void*)*16 + 2, v_updateToolchain_112_);
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v_a_94_);
return v___x_189_;
}
else
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
lean_dec_ref(v___x_184_);
lean_dec_ref(v_relTomlFile_157_);
lean_dec_ref(v_remoteUrl_114_);
lean_dec_ref(v_scope_113_);
lean_dec_ref(v_leanOpts_109_);
lean_dec(v_lakeOpts_108_);
lean_dec_ref(v_packageOverrides_107_);
lean_dec_ref(v_relManifestFile_106_);
lean_dec_ref(v_pkgDir_103_);
lean_dec_ref(v_relPkgDir_102_);
lean_dec(v_pkgName_101_);
lean_dec(v_pkgIdx_100_);
lean_dec_ref(v_wsDir_99_);
lean_dec(v_lakeArgs_x3f_98_);
lean_dec_ref(v_lakeEnv_97_);
v___x_190_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__7));
v___x_191_ = lean_string_append(v_name_92_, v___x_190_);
v___x_192_ = lean_string_append(v___x_191_, v_leanFile_158_);
lean_dec_ref(v_leanFile_158_);
v___x_193_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__8));
v___x_194_ = lean_string_append(v___x_192_, v___x_193_);
v___x_195_ = lean_string_append(v___x_194_, v_tomlFile_159_);
lean_dec_ref(v_tomlFile_159_);
v___x_196_ = 3;
v___x_197_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_197_, 0, v___x_195_);
lean_ctor_set_uint8(v___x_197_, sizeof(void*)*1, v___x_196_);
v___x_198_ = lean_array_get_size(v_a_94_);
v___x_199_ = lean_array_push(v_a_94_, v___x_197_);
v___x_200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_198_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
return v___x_200_;
}
}
v___jp_161_:
{
lean_object* v___x_163_; lean_object* v___x_165_; 
v___x_163_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__2));
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 9, v___x_163_);
lean_ctor_set(v___x_116_, 8, v___x_160_);
lean_ctor_set(v___x_116_, 7, v_relLeanFile_155_);
v___x_165_ = v___x_116_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_lakeEnv_97_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v_lakeArgs_x3f_98_);
lean_ctor_set(v_reuseFailAlloc_167_, 2, v_wsDir_99_);
lean_ctor_set(v_reuseFailAlloc_167_, 3, v_pkgIdx_100_);
lean_ctor_set(v_reuseFailAlloc_167_, 4, v_pkgName_101_);
lean_ctor_set(v_reuseFailAlloc_167_, 5, v_relPkgDir_102_);
lean_ctor_set(v_reuseFailAlloc_167_, 6, v_pkgDir_103_);
lean_ctor_set(v_reuseFailAlloc_167_, 7, v_relLeanFile_155_);
lean_ctor_set(v_reuseFailAlloc_167_, 8, v___x_160_);
lean_ctor_set(v_reuseFailAlloc_167_, 9, v___x_163_);
lean_ctor_set(v_reuseFailAlloc_167_, 10, v_relManifestFile_106_);
lean_ctor_set(v_reuseFailAlloc_167_, 11, v_packageOverrides_107_);
lean_ctor_set(v_reuseFailAlloc_167_, 12, v_lakeOpts_108_);
lean_ctor_set(v_reuseFailAlloc_167_, 13, v_leanOpts_109_);
lean_ctor_set(v_reuseFailAlloc_167_, 14, v_scope_113_);
lean_ctor_set(v_reuseFailAlloc_167_, 15, v_remoteUrl_114_);
lean_ctor_set_uint8(v_reuseFailAlloc_167_, sizeof(void*)*16, v_reconfigure_110_);
lean_ctor_set_uint8(v_reuseFailAlloc_167_, sizeof(void*)*16 + 1, v_updateDeps_111_);
lean_ctor_set_uint8(v_reuseFailAlloc_167_, sizeof(void*)*16 + 2, v_updateToolchain_112_);
v___x_165_ = v_reuseFailAlloc_167_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_166_; 
v___x_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v___y_162_);
return v___x_166_;
}
}
}
}
}
else
{
lean_object* v_lakeEnv_203_; lean_object* v_lakeArgs_x3f_204_; lean_object* v_wsDir_205_; lean_object* v_pkgIdx_206_; lean_object* v_pkgName_207_; lean_object* v_relPkgDir_208_; lean_object* v_pkgDir_209_; lean_object* v_relConfigFile_210_; lean_object* v_configFile_211_; lean_object* v_relManifestFile_212_; lean_object* v_packageOverrides_213_; lean_object* v_lakeOpts_214_; lean_object* v_leanOpts_215_; uint8_t v_reconfigure_216_; uint8_t v_updateDeps_217_; uint8_t v_updateToolchain_218_; lean_object* v_scope_219_; lean_object* v_remoteUrl_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_240_; 
lean_inc_ref(v_configLang_x3f_96_);
v_lakeEnv_203_ = lean_ctor_get(v_cfg_93_, 0);
v_lakeArgs_x3f_204_ = lean_ctor_get(v_cfg_93_, 1);
v_wsDir_205_ = lean_ctor_get(v_cfg_93_, 2);
v_pkgIdx_206_ = lean_ctor_get(v_cfg_93_, 3);
v_pkgName_207_ = lean_ctor_get(v_cfg_93_, 4);
v_relPkgDir_208_ = lean_ctor_get(v_cfg_93_, 5);
v_pkgDir_209_ = lean_ctor_get(v_cfg_93_, 6);
v_relConfigFile_210_ = lean_ctor_get(v_cfg_93_, 7);
v_configFile_211_ = lean_ctor_get(v_cfg_93_, 8);
v_relManifestFile_212_ = lean_ctor_get(v_cfg_93_, 10);
v_packageOverrides_213_ = lean_ctor_get(v_cfg_93_, 11);
v_lakeOpts_214_ = lean_ctor_get(v_cfg_93_, 12);
v_leanOpts_215_ = lean_ctor_get(v_cfg_93_, 13);
v_reconfigure_216_ = lean_ctor_get_uint8(v_cfg_93_, sizeof(void*)*16);
v_updateDeps_217_ = lean_ctor_get_uint8(v_cfg_93_, sizeof(void*)*16 + 1);
v_updateToolchain_218_ = lean_ctor_get_uint8(v_cfg_93_, sizeof(void*)*16 + 2);
v_scope_219_ = lean_ctor_get(v_cfg_93_, 14);
v_remoteUrl_220_ = lean_ctor_get(v_cfg_93_, 15);
v_isSharedCheck_240_ = !lean_is_exclusive(v_cfg_93_);
if (v_isSharedCheck_240_ == 0)
{
lean_object* v_unused_241_; 
v_unused_241_ = lean_ctor_get(v_cfg_93_, 9);
lean_dec(v_unused_241_);
v___x_222_ = v_cfg_93_;
v_isShared_223_ = v_isSharedCheck_240_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_remoteUrl_220_);
lean_inc(v_scope_219_);
lean_inc(v_leanOpts_215_);
lean_inc(v_lakeOpts_214_);
lean_inc(v_packageOverrides_213_);
lean_inc(v_relManifestFile_212_);
lean_inc(v_configFile_211_);
lean_inc(v_relConfigFile_210_);
lean_inc(v_pkgDir_209_);
lean_inc(v_relPkgDir_208_);
lean_inc(v_pkgName_207_);
lean_inc(v_pkgIdx_206_);
lean_inc(v_wsDir_205_);
lean_inc(v_lakeArgs_x3f_204_);
lean_inc(v_lakeEnv_203_);
lean_dec(v_cfg_93_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_240_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
lean_inc_ref(v_configFile_211_);
v___x_224_ = l_Lake_resolvePath(v_configFile_211_);
v___x_225_ = lean_string_utf8_byte_size(v___x_224_);
v___x_226_ = lean_unsigned_to_nat(0u);
v___x_227_ = lean_nat_dec_eq(v___x_225_, v___x_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_229_; 
lean_dec_ref(v_configFile_211_);
lean_dec_ref(v_name_92_);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 8, v___x_224_);
v___x_229_ = v___x_222_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_lakeEnv_203_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v_lakeArgs_x3f_204_);
lean_ctor_set(v_reuseFailAlloc_231_, 2, v_wsDir_205_);
lean_ctor_set(v_reuseFailAlloc_231_, 3, v_pkgIdx_206_);
lean_ctor_set(v_reuseFailAlloc_231_, 4, v_pkgName_207_);
lean_ctor_set(v_reuseFailAlloc_231_, 5, v_relPkgDir_208_);
lean_ctor_set(v_reuseFailAlloc_231_, 6, v_pkgDir_209_);
lean_ctor_set(v_reuseFailAlloc_231_, 7, v_relConfigFile_210_);
lean_ctor_set(v_reuseFailAlloc_231_, 8, v___x_224_);
lean_ctor_set(v_reuseFailAlloc_231_, 9, v_configLang_x3f_96_);
lean_ctor_set(v_reuseFailAlloc_231_, 10, v_relManifestFile_212_);
lean_ctor_set(v_reuseFailAlloc_231_, 11, v_packageOverrides_213_);
lean_ctor_set(v_reuseFailAlloc_231_, 12, v_lakeOpts_214_);
lean_ctor_set(v_reuseFailAlloc_231_, 13, v_leanOpts_215_);
lean_ctor_set(v_reuseFailAlloc_231_, 14, v_scope_219_);
lean_ctor_set(v_reuseFailAlloc_231_, 15, v_remoteUrl_220_);
lean_ctor_set_uint8(v_reuseFailAlloc_231_, sizeof(void*)*16, v_reconfigure_216_);
lean_ctor_set_uint8(v_reuseFailAlloc_231_, sizeof(void*)*16 + 1, v_updateDeps_217_);
lean_ctor_set_uint8(v_reuseFailAlloc_231_, sizeof(void*)*16 + 2, v_updateToolchain_218_);
v___x_229_ = v_reuseFailAlloc_231_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_230_; 
v___x_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set(v___x_230_, 1, v_a_94_);
return v___x_230_;
}
}
else
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; uint8_t v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
lean_dec_ref(v___x_224_);
lean_del_object(v___x_222_);
lean_dec_ref(v_remoteUrl_220_);
lean_dec_ref(v_scope_219_);
lean_dec_ref(v_leanOpts_215_);
lean_dec(v_lakeOpts_214_);
lean_dec_ref(v_packageOverrides_213_);
lean_dec_ref(v_relManifestFile_212_);
lean_dec_ref(v_relConfigFile_210_);
lean_dec_ref(v_pkgDir_209_);
lean_dec_ref(v_relPkgDir_208_);
lean_dec(v_pkgName_207_);
lean_dec(v_pkgIdx_206_);
lean_dec_ref(v_wsDir_205_);
lean_dec(v_lakeArgs_x3f_204_);
lean_dec_ref(v_lakeEnv_203_);
lean_dec_ref_known(v_configLang_x3f_96_, 1);
v___x_232_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__3));
v___x_233_ = lean_string_append(v_name_92_, v___x_232_);
v___x_234_ = lean_string_append(v___x_233_, v_configFile_211_);
lean_dec_ref(v_configFile_211_);
v___x_235_ = 3;
v___x_236_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_236_, 0, v___x_234_);
lean_ctor_set_uint8(v___x_236_, sizeof(void*)*1, v___x_235_);
v___x_237_ = lean_array_get_size(v_a_94_);
v___x_238_ = lean_array_push(v_a_94_, v___x_236_);
v___x_239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_237_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
return v___x_239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveConfigFile___boxed(lean_object* v_name_242_, lean_object* v_cfg_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lake_resolveConfigFile(v_name_242_, v_cfg_243_, v_a_244_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadConfigFile___redArg(lean_object* v_cfg_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_configLang_x3f_250_; lean_object* v_val_251_; uint8_t v___x_252_; 
v_configLang_x3f_250_ = lean_ctor_get(v_cfg_247_, 9);
v_val_251_ = lean_ctor_get(v_configLang_x3f_250_, 0);
v___x_252_ = lean_unbox(v_val_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
v___x_253_ = l_Lake_loadLeanConfig(v_cfg_247_, v_a_248_);
return v___x_253_;
}
else
{
lean_object* v___x_254_; 
v___x_254_ = l_Lake_loadTomlConfig(v_cfg_247_, v_a_248_);
return v___x_254_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadConfigFile___redArg___boxed(lean_object* v_cfg_255_, lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lake_loadConfigFile___redArg(v_cfg_255_, v_a_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadConfigFile(lean_object* v_cfg_259_, lean_object* v_h_260_, lean_object* v_a_261_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lake_loadConfigFile___redArg(v_cfg_259_, v_a_261_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadConfigFile___boxed(lean_object* v_cfg_264_, lean_object* v_h_265_, lean_object* v_a_266_, lean_object* v_a_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lake_loadConfigFile(v_cfg_264_, v_h_265_, v_a_266_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackage(lean_object* v_cfg_270_, lean_object* v_a_271_){
_start:
{
lean_object* v_lakeEnv_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v_lakeEnv_273_ = lean_ctor_get(v_cfg_270_, 0);
v___x_274_ = l_Lean_searchPathRef;
v___x_275_ = l_Lake_Env_leanSearchPath(v_lakeEnv_273_);
v___x_276_ = lean_st_ref_swap(v___x_274_, v___x_275_);
lean_dec(v___x_276_);
v___x_277_ = ((lean_object*)(l_Lake_loadPackage___closed__0));
v___x_278_ = l_Lake_resolveConfigFile(v___x_277_, v_cfg_270_, v_a_271_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v_a_280_; lean_object* v___x_281_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc_n(v_a_279_, 2);
v_a_280_ = lean_ctor_get(v___x_278_, 1);
lean_inc(v_a_280_);
lean_dec_ref_known(v___x_278_, 2);
v___x_281_ = l_Lake_loadConfigFile___redArg(v_a_279_, v_a_280_);
if (lean_obj_tag(v___x_281_) == 0)
{
lean_object* v_a_282_; lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_292_; 
v_a_282_ = lean_ctor_get(v___x_281_, 0);
v_a_283_ = lean_ctor_get(v___x_281_, 1);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_292_ == 0)
{
v___x_285_ = v___x_281_;
v_isShared_286_ = v_isSharedCheck_292_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_inc(v_a_282_);
lean_dec(v___x_281_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_292_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v_pkgIdx_287_; lean_object* v___x_288_; lean_object* v___x_290_; 
v_pkgIdx_287_ = lean_ctor_get(v_a_279_, 3);
lean_inc(v_pkgIdx_287_);
v___x_288_ = l_Lake_mkPackage(v_a_279_, v_a_282_, v_pkgIdx_287_);
lean_dec(v_a_279_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v___x_288_);
v___x_290_ = v___x_285_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_288_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_a_283_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
else
{
lean_object* v_a_293_; lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_301_; 
lean_dec(v_a_279_);
v_a_293_ = lean_ctor_get(v___x_281_, 0);
v_a_294_ = lean_ctor_get(v___x_281_, 1);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_301_ == 0)
{
v___x_296_ = v___x_281_;
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_inc(v_a_293_);
lean_dec(v___x_281_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_a_293_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v_a_294_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
else
{
lean_object* v_a_302_; lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
v_a_302_ = lean_ctor_get(v___x_278_, 0);
v_a_303_ = lean_ctor_get(v___x_278_, 1);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v___x_278_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_inc(v_a_302_);
lean_dec(v___x_278_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_302_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackage___boxed(lean_object* v_cfg_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lake_loadPackage(v_cfg_311_, v_a_312_);
return v_res_314_;
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
