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
uint8_t l_Lake_configFileExists(lean_object* v_cfgFile_48_){
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
LEAN_EXPORT void l_Lake_configFileExists_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfgFile_48_ = stack[0].m_obj;
uint8_t v_res_58_;
v_res_58_ = l_Lake_configFileExists(v_cfgFile_48_);
stack->m_num = v_res_58_;
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
lean_object* l_Lake_realConfigFile(lean_object* v_cfgFile_63_){
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
LEAN_EXPORT void l_Lake_realConfigFile_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfgFile_63_ = stack[0].m_obj;
lean_object* v_res_76_;
v_res_76_ = l_Lake_realConfigFile(v_cfgFile_63_);
stack->m_obj
 = v_res_76_;
}
LEAN_EXPORT lean_object* l_Lake_realConfigFile___boxed(lean_object* v_cfgFile_77_, lean_object* v_a_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lake_realConfigFile(v_cfgFile_77_);
return v_res_79_;
}
}
lean_object* l_Lake_resolveConfigFile(lean_object* v_name_93_, lean_object* v_cfg_94_, lean_object* v_a_95_){
_start:
{
lean_object* v_configLang_x3f_97_; 
v_configLang_x3f_97_ = lean_ctor_get(v_cfg_94_, 9);
if (lean_obj_tag(v_configLang_x3f_97_) == 0)
{
lean_object* v_lakeEnv_98_; lean_object* v_lakeArgs_x3f_99_; lean_object* v_wsDir_100_; lean_object* v_pkgIdx_101_; lean_object* v_pkgName_102_; lean_object* v_relPkgDir_103_; lean_object* v_pkgDir_104_; lean_object* v_relConfigFile_105_; lean_object* v_configFile_106_; lean_object* v_relManifestFile_107_; lean_object* v_packageOverrides_108_; lean_object* v_lakeOpts_109_; lean_object* v_leanOpts_110_; uint8_t v_reconfigure_111_; uint8_t v_updateDeps_112_; uint8_t v_updateToolchain_113_; lean_object* v_scope_114_; lean_object* v_remoteUrl_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_202_; 
v_lakeEnv_98_ = lean_ctor_get(v_cfg_94_, 0);
v_lakeArgs_x3f_99_ = lean_ctor_get(v_cfg_94_, 1);
v_wsDir_100_ = lean_ctor_get(v_cfg_94_, 2);
v_pkgIdx_101_ = lean_ctor_get(v_cfg_94_, 3);
v_pkgName_102_ = lean_ctor_get(v_cfg_94_, 4);
v_relPkgDir_103_ = lean_ctor_get(v_cfg_94_, 5);
v_pkgDir_104_ = lean_ctor_get(v_cfg_94_, 6);
v_relConfigFile_105_ = lean_ctor_get(v_cfg_94_, 7);
v_configFile_106_ = lean_ctor_get(v_cfg_94_, 8);
v_relManifestFile_107_ = lean_ctor_get(v_cfg_94_, 10);
v_packageOverrides_108_ = lean_ctor_get(v_cfg_94_, 11);
v_lakeOpts_109_ = lean_ctor_get(v_cfg_94_, 12);
v_leanOpts_110_ = lean_ctor_get(v_cfg_94_, 13);
v_reconfigure_111_ = lean_ctor_get_uint8(v_cfg_94_, sizeof(void*)*16);
v_updateDeps_112_ = lean_ctor_get_uint8(v_cfg_94_, sizeof(void*)*16 + 1);
v_updateToolchain_113_ = lean_ctor_get_uint8(v_cfg_94_, sizeof(void*)*16 + 2);
v_scope_114_ = lean_ctor_get(v_cfg_94_, 14);
v_remoteUrl_115_ = lean_ctor_get(v_cfg_94_, 15);
v_isSharedCheck_202_ = !lean_is_exclusive(v_cfg_94_);
if (v_isSharedCheck_202_ == 0)
{
lean_object* v_unused_203_; 
v_unused_203_ = lean_ctor_get(v_cfg_94_, 9);
lean_dec(v_unused_203_);
v___x_117_ = v_cfg_94_;
v_isShared_118_ = v_isSharedCheck_202_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_remoteUrl_115_);
lean_inc(v_scope_114_);
lean_inc(v_leanOpts_110_);
lean_inc(v_lakeOpts_109_);
lean_inc(v_packageOverrides_108_);
lean_inc(v_relManifestFile_107_);
lean_inc(v_configFile_106_);
lean_inc(v_relConfigFile_105_);
lean_inc(v_pkgDir_104_);
lean_inc(v_relPkgDir_103_);
lean_inc(v_pkgName_102_);
lean_inc(v_pkgIdx_101_);
lean_inc(v_wsDir_100_);
lean_inc(v_lakeArgs_x3f_99_);
lean_inc(v_lakeEnv_98_);
lean_dec(v_cfg_94_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_202_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_119_; 
lean_inc_ref(v_relConfigFile_105_);
v___x_119_ = l_System_FilePath_extension(v_relConfigFile_105_);
if (lean_obj_tag(v___x_119_) == 1)
{
lean_object* v_val_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v_val_120_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_val_120_);
lean_dec_ref_known(v___x_119_, 1);
lean_inc_ref(v_configFile_106_);
v___x_121_ = l_Lake_resolvePath(v_configFile_106_);
v___x_122_ = lean_string_utf8_byte_size(v___x_121_);
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = lean_nat_dec_eq(v___x_122_, v___x_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; uint8_t v___x_126_; 
lean_dec_ref(v_configFile_106_);
v___x_125_ = ((lean_object*)(l_Lake_configFileExists___closed__0));
v___x_126_ = lean_string_dec_eq(v_val_120_, v___x_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_127_ = ((lean_object*)(l_Lake_configFileExists___closed__1));
v___x_128_ = lean_string_dec_eq(v_val_120_, v___x_127_);
lean_dec(v_val_120_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
lean_del_object(v___x_117_);
lean_dec_ref(v_remoteUrl_115_);
lean_dec_ref(v_scope_114_);
lean_dec_ref(v_leanOpts_110_);
lean_dec(v_lakeOpts_109_);
lean_dec_ref(v_packageOverrides_108_);
lean_dec_ref(v_relManifestFile_107_);
lean_dec_ref(v_relConfigFile_105_);
lean_dec_ref(v_pkgDir_104_);
lean_dec_ref(v_relPkgDir_103_);
lean_dec(v_pkgName_102_);
lean_dec(v_pkgIdx_101_);
lean_dec_ref(v_wsDir_100_);
lean_dec(v_lakeArgs_x3f_99_);
lean_dec_ref(v_lakeEnv_98_);
v___x_129_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__0));
v___x_130_ = lean_string_append(v_name_93_, v___x_129_);
v___x_131_ = lean_string_append(v___x_130_, v___x_121_);
lean_dec_ref(v___x_121_);
v___x_132_ = 3;
v___x_133_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_133_, 0, v___x_131_);
lean_ctor_set_uint8(v___x_133_, sizeof(void*)*1, v___x_132_);
v___x_134_ = lean_array_get_size(v_a_95_);
v___x_135_ = lean_array_push(v_a_95_, v___x_133_);
v___x_136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_134_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
return v___x_136_;
}
else
{
lean_object* v___x_137_; lean_object* v___x_139_; 
lean_dec_ref(v_name_93_);
v___x_137_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__1));
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 9, v___x_137_);
lean_ctor_set(v___x_117_, 8, v___x_121_);
v___x_139_ = v___x_117_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_lakeEnv_98_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v_lakeArgs_x3f_99_);
lean_ctor_set(v_reuseFailAlloc_141_, 2, v_wsDir_100_);
lean_ctor_set(v_reuseFailAlloc_141_, 3, v_pkgIdx_101_);
lean_ctor_set(v_reuseFailAlloc_141_, 4, v_pkgName_102_);
lean_ctor_set(v_reuseFailAlloc_141_, 5, v_relPkgDir_103_);
lean_ctor_set(v_reuseFailAlloc_141_, 6, v_pkgDir_104_);
lean_ctor_set(v_reuseFailAlloc_141_, 7, v_relConfigFile_105_);
lean_ctor_set(v_reuseFailAlloc_141_, 8, v___x_121_);
lean_ctor_set(v_reuseFailAlloc_141_, 9, v___x_137_);
lean_ctor_set(v_reuseFailAlloc_141_, 10, v_relManifestFile_107_);
lean_ctor_set(v_reuseFailAlloc_141_, 11, v_packageOverrides_108_);
lean_ctor_set(v_reuseFailAlloc_141_, 12, v_lakeOpts_109_);
lean_ctor_set(v_reuseFailAlloc_141_, 13, v_leanOpts_110_);
lean_ctor_set(v_reuseFailAlloc_141_, 14, v_scope_114_);
lean_ctor_set(v_reuseFailAlloc_141_, 15, v_remoteUrl_115_);
lean_ctor_set_uint8(v_reuseFailAlloc_141_, sizeof(void*)*16, v_reconfigure_111_);
lean_ctor_set_uint8(v_reuseFailAlloc_141_, sizeof(void*)*16 + 1, v_updateDeps_112_);
lean_ctor_set_uint8(v_reuseFailAlloc_141_, sizeof(void*)*16 + 2, v_updateToolchain_113_);
v___x_139_ = v_reuseFailAlloc_141_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v___x_140_; 
v___x_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v_a_95_);
return v___x_140_;
}
}
}
else
{
lean_object* v___x_142_; lean_object* v___x_144_; 
lean_dec(v_val_120_);
lean_dec_ref(v_name_93_);
v___x_142_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__2));
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 9, v___x_142_);
lean_ctor_set(v___x_117_, 8, v___x_121_);
v___x_144_ = v___x_117_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_lakeEnv_98_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_lakeArgs_x3f_99_);
lean_ctor_set(v_reuseFailAlloc_146_, 2, v_wsDir_100_);
lean_ctor_set(v_reuseFailAlloc_146_, 3, v_pkgIdx_101_);
lean_ctor_set(v_reuseFailAlloc_146_, 4, v_pkgName_102_);
lean_ctor_set(v_reuseFailAlloc_146_, 5, v_relPkgDir_103_);
lean_ctor_set(v_reuseFailAlloc_146_, 6, v_pkgDir_104_);
lean_ctor_set(v_reuseFailAlloc_146_, 7, v_relConfigFile_105_);
lean_ctor_set(v_reuseFailAlloc_146_, 8, v___x_121_);
lean_ctor_set(v_reuseFailAlloc_146_, 9, v___x_142_);
lean_ctor_set(v_reuseFailAlloc_146_, 10, v_relManifestFile_107_);
lean_ctor_set(v_reuseFailAlloc_146_, 11, v_packageOverrides_108_);
lean_ctor_set(v_reuseFailAlloc_146_, 12, v_lakeOpts_109_);
lean_ctor_set(v_reuseFailAlloc_146_, 13, v_leanOpts_110_);
lean_ctor_set(v_reuseFailAlloc_146_, 14, v_scope_114_);
lean_ctor_set(v_reuseFailAlloc_146_, 15, v_remoteUrl_115_);
lean_ctor_set_uint8(v_reuseFailAlloc_146_, sizeof(void*)*16, v_reconfigure_111_);
lean_ctor_set_uint8(v_reuseFailAlloc_146_, sizeof(void*)*16 + 1, v_updateDeps_112_);
lean_ctor_set_uint8(v_reuseFailAlloc_146_, sizeof(void*)*16 + 2, v_updateToolchain_113_);
v___x_144_ = v_reuseFailAlloc_146_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v___x_145_; 
v___x_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v_a_95_);
return v___x_145_;
}
}
}
else
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; uint8_t v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
lean_dec_ref(v___x_121_);
lean_dec(v_val_120_);
lean_del_object(v___x_117_);
lean_dec_ref(v_remoteUrl_115_);
lean_dec_ref(v_scope_114_);
lean_dec_ref(v_leanOpts_110_);
lean_dec(v_lakeOpts_109_);
lean_dec_ref(v_packageOverrides_108_);
lean_dec_ref(v_relManifestFile_107_);
lean_dec_ref(v_relConfigFile_105_);
lean_dec_ref(v_pkgDir_104_);
lean_dec_ref(v_relPkgDir_103_);
lean_dec(v_pkgName_102_);
lean_dec(v_pkgIdx_101_);
lean_dec_ref(v_wsDir_100_);
lean_dec(v_lakeArgs_x3f_99_);
lean_dec_ref(v_lakeEnv_98_);
v___x_147_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__3));
v___x_148_ = lean_string_append(v_name_93_, v___x_147_);
v___x_149_ = lean_string_append(v___x_148_, v_configFile_106_);
lean_dec_ref(v_configFile_106_);
v___x_150_ = 3;
v___x_151_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_151_, 0, v___x_149_);
lean_ctor_set_uint8(v___x_151_, sizeof(void*)*1, v___x_150_);
v___x_152_ = lean_array_get_size(v_a_95_);
v___x_153_ = lean_array_push(v_a_95_, v___x_151_);
v___x_154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_152_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
return v___x_154_;
}
}
else
{
lean_object* v___x_155_; lean_object* v_relLeanFile_156_; lean_object* v___x_157_; lean_object* v_relTomlFile_158_; lean_object* v_leanFile_159_; lean_object* v_tomlFile_160_; lean_object* v___x_161_; lean_object* v___y_163_; lean_object* v___x_169_; lean_object* v___x_170_; uint8_t v___x_171_; 
lean_dec(v___x_119_);
lean_dec_ref(v_configFile_106_);
v___x_155_ = ((lean_object*)(l_Lake_configFileExists___closed__0));
lean_inc_ref(v_relConfigFile_105_);
v_relLeanFile_156_ = l_System_FilePath_addExtension(v_relConfigFile_105_, v___x_155_);
v___x_157_ = ((lean_object*)(l_Lake_configFileExists___closed__1));
v_relTomlFile_158_ = l_System_FilePath_addExtension(v_relConfigFile_105_, v___x_157_);
lean_inc_ref(v_relLeanFile_156_);
lean_inc_ref_n(v_pkgDir_104_, 2);
v_leanFile_159_ = l_Lake_joinRelative(v_pkgDir_104_, v_relLeanFile_156_);
lean_inc_ref(v_relTomlFile_158_);
v_tomlFile_160_ = l_Lake_joinRelative(v_pkgDir_104_, v_relTomlFile_158_);
lean_inc_ref(v_leanFile_159_);
v___x_161_ = l_Lake_resolvePath(v_leanFile_159_);
v___x_169_ = lean_string_utf8_byte_size(v___x_161_);
v___x_170_ = lean_unsigned_to_nat(0u);
v___x_171_ = lean_nat_dec_eq(v___x_169_, v___x_170_);
if (v___x_171_ == 0)
{
uint8_t v___x_172_; 
lean_dec_ref(v_leanFile_159_);
v___x_172_ = l_System_FilePath_pathExists(v_tomlFile_160_);
lean_dec_ref(v_tomlFile_160_);
if (v___x_172_ == 0)
{
lean_dec_ref(v_relTomlFile_158_);
lean_dec_ref(v_name_93_);
v___y_163_ = v_a_95_;
goto v___jp_162_;
}
else
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_173_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__4));
v___x_174_ = lean_string_append(v_name_93_, v___x_173_);
v___x_175_ = lean_string_append(v___x_174_, v_relLeanFile_156_);
v___x_176_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__5));
v___x_177_ = lean_string_append(v___x_175_, v___x_176_);
v___x_178_ = lean_string_append(v___x_177_, v_relTomlFile_158_);
lean_dec_ref(v_relTomlFile_158_);
v___x_179_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__6));
v___x_180_ = lean_string_append(v___x_178_, v___x_179_);
v___x_181_ = lean_string_append(v___x_180_, v_relLeanFile_156_);
v___x_182_ = 1;
v___x_183_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_183_, 0, v___x_181_);
lean_ctor_set_uint8(v___x_183_, sizeof(void*)*1, v___x_182_);
v___x_184_ = lean_array_push(v_a_95_, v___x_183_);
v___y_163_ = v___x_184_;
goto v___jp_162_;
}
}
else
{
lean_object* v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
lean_dec_ref(v___x_161_);
lean_dec_ref(v_relLeanFile_156_);
lean_del_object(v___x_117_);
lean_inc_ref(v_tomlFile_160_);
v___x_185_ = l_Lake_resolvePath(v_tomlFile_160_);
v___x_186_ = lean_string_utf8_byte_size(v___x_185_);
v___x_187_ = lean_nat_dec_eq(v___x_186_, v___x_170_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
lean_dec_ref(v_tomlFile_160_);
lean_dec_ref(v_leanFile_159_);
lean_dec_ref(v_name_93_);
v___x_188_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__1));
v___x_189_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v___x_189_, 0, v_lakeEnv_98_);
lean_ctor_set(v___x_189_, 1, v_lakeArgs_x3f_99_);
lean_ctor_set(v___x_189_, 2, v_wsDir_100_);
lean_ctor_set(v___x_189_, 3, v_pkgIdx_101_);
lean_ctor_set(v___x_189_, 4, v_pkgName_102_);
lean_ctor_set(v___x_189_, 5, v_relPkgDir_103_);
lean_ctor_set(v___x_189_, 6, v_pkgDir_104_);
lean_ctor_set(v___x_189_, 7, v_relTomlFile_158_);
lean_ctor_set(v___x_189_, 8, v___x_185_);
lean_ctor_set(v___x_189_, 9, v___x_188_);
lean_ctor_set(v___x_189_, 10, v_relManifestFile_107_);
lean_ctor_set(v___x_189_, 11, v_packageOverrides_108_);
lean_ctor_set(v___x_189_, 12, v_lakeOpts_109_);
lean_ctor_set(v___x_189_, 13, v_leanOpts_110_);
lean_ctor_set(v___x_189_, 14, v_scope_114_);
lean_ctor_set(v___x_189_, 15, v_remoteUrl_115_);
lean_ctor_set_uint8(v___x_189_, sizeof(void*)*16, v_reconfigure_111_);
lean_ctor_set_uint8(v___x_189_, sizeof(void*)*16 + 1, v_updateDeps_112_);
lean_ctor_set_uint8(v___x_189_, sizeof(void*)*16 + 2, v_updateToolchain_113_);
v___x_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v_a_95_);
return v___x_190_;
}
else
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
lean_dec_ref(v___x_185_);
lean_dec_ref(v_relTomlFile_158_);
lean_dec_ref(v_remoteUrl_115_);
lean_dec_ref(v_scope_114_);
lean_dec_ref(v_leanOpts_110_);
lean_dec(v_lakeOpts_109_);
lean_dec_ref(v_packageOverrides_108_);
lean_dec_ref(v_relManifestFile_107_);
lean_dec_ref(v_pkgDir_104_);
lean_dec_ref(v_relPkgDir_103_);
lean_dec(v_pkgName_102_);
lean_dec(v_pkgIdx_101_);
lean_dec_ref(v_wsDir_100_);
lean_dec(v_lakeArgs_x3f_99_);
lean_dec_ref(v_lakeEnv_98_);
v___x_191_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__7));
v___x_192_ = lean_string_append(v_name_93_, v___x_191_);
v___x_193_ = lean_string_append(v___x_192_, v_leanFile_159_);
lean_dec_ref(v_leanFile_159_);
v___x_194_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__8));
v___x_195_ = lean_string_append(v___x_193_, v___x_194_);
v___x_196_ = lean_string_append(v___x_195_, v_tomlFile_160_);
lean_dec_ref(v_tomlFile_160_);
v___x_197_ = 3;
v___x_198_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_198_, 0, v___x_196_);
lean_ctor_set_uint8(v___x_198_, sizeof(void*)*1, v___x_197_);
v___x_199_ = lean_array_get_size(v_a_95_);
v___x_200_ = lean_array_push(v_a_95_, v___x_198_);
v___x_201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_199_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
return v___x_201_;
}
}
v___jp_162_:
{
lean_object* v___x_164_; lean_object* v___x_166_; 
v___x_164_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__2));
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 9, v___x_164_);
lean_ctor_set(v___x_117_, 8, v___x_161_);
lean_ctor_set(v___x_117_, 7, v_relLeanFile_156_);
v___x_166_ = v___x_117_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_lakeEnv_98_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_lakeArgs_x3f_99_);
lean_ctor_set(v_reuseFailAlloc_168_, 2, v_wsDir_100_);
lean_ctor_set(v_reuseFailAlloc_168_, 3, v_pkgIdx_101_);
lean_ctor_set(v_reuseFailAlloc_168_, 4, v_pkgName_102_);
lean_ctor_set(v_reuseFailAlloc_168_, 5, v_relPkgDir_103_);
lean_ctor_set(v_reuseFailAlloc_168_, 6, v_pkgDir_104_);
lean_ctor_set(v_reuseFailAlloc_168_, 7, v_relLeanFile_156_);
lean_ctor_set(v_reuseFailAlloc_168_, 8, v___x_161_);
lean_ctor_set(v_reuseFailAlloc_168_, 9, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_168_, 10, v_relManifestFile_107_);
lean_ctor_set(v_reuseFailAlloc_168_, 11, v_packageOverrides_108_);
lean_ctor_set(v_reuseFailAlloc_168_, 12, v_lakeOpts_109_);
lean_ctor_set(v_reuseFailAlloc_168_, 13, v_leanOpts_110_);
lean_ctor_set(v_reuseFailAlloc_168_, 14, v_scope_114_);
lean_ctor_set(v_reuseFailAlloc_168_, 15, v_remoteUrl_115_);
lean_ctor_set_uint8(v_reuseFailAlloc_168_, sizeof(void*)*16, v_reconfigure_111_);
lean_ctor_set_uint8(v_reuseFailAlloc_168_, sizeof(void*)*16 + 1, v_updateDeps_112_);
lean_ctor_set_uint8(v_reuseFailAlloc_168_, sizeof(void*)*16 + 2, v_updateToolchain_113_);
v___x_166_ = v_reuseFailAlloc_168_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_167_; 
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v___y_163_);
return v___x_167_;
}
}
}
}
}
else
{
lean_object* v_lakeEnv_204_; lean_object* v_lakeArgs_x3f_205_; lean_object* v_wsDir_206_; lean_object* v_pkgIdx_207_; lean_object* v_pkgName_208_; lean_object* v_relPkgDir_209_; lean_object* v_pkgDir_210_; lean_object* v_relConfigFile_211_; lean_object* v_configFile_212_; lean_object* v_relManifestFile_213_; lean_object* v_packageOverrides_214_; lean_object* v_lakeOpts_215_; lean_object* v_leanOpts_216_; uint8_t v_reconfigure_217_; uint8_t v_updateDeps_218_; uint8_t v_updateToolchain_219_; lean_object* v_scope_220_; lean_object* v_remoteUrl_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_241_; 
lean_inc_ref(v_configLang_x3f_97_);
v_lakeEnv_204_ = lean_ctor_get(v_cfg_94_, 0);
v_lakeArgs_x3f_205_ = lean_ctor_get(v_cfg_94_, 1);
v_wsDir_206_ = lean_ctor_get(v_cfg_94_, 2);
v_pkgIdx_207_ = lean_ctor_get(v_cfg_94_, 3);
v_pkgName_208_ = lean_ctor_get(v_cfg_94_, 4);
v_relPkgDir_209_ = lean_ctor_get(v_cfg_94_, 5);
v_pkgDir_210_ = lean_ctor_get(v_cfg_94_, 6);
v_relConfigFile_211_ = lean_ctor_get(v_cfg_94_, 7);
v_configFile_212_ = lean_ctor_get(v_cfg_94_, 8);
v_relManifestFile_213_ = lean_ctor_get(v_cfg_94_, 10);
v_packageOverrides_214_ = lean_ctor_get(v_cfg_94_, 11);
v_lakeOpts_215_ = lean_ctor_get(v_cfg_94_, 12);
v_leanOpts_216_ = lean_ctor_get(v_cfg_94_, 13);
v_reconfigure_217_ = lean_ctor_get_uint8(v_cfg_94_, sizeof(void*)*16);
v_updateDeps_218_ = lean_ctor_get_uint8(v_cfg_94_, sizeof(void*)*16 + 1);
v_updateToolchain_219_ = lean_ctor_get_uint8(v_cfg_94_, sizeof(void*)*16 + 2);
v_scope_220_ = lean_ctor_get(v_cfg_94_, 14);
v_remoteUrl_221_ = lean_ctor_get(v_cfg_94_, 15);
v_isSharedCheck_241_ = !lean_is_exclusive(v_cfg_94_);
if (v_isSharedCheck_241_ == 0)
{
lean_object* v_unused_242_; 
v_unused_242_ = lean_ctor_get(v_cfg_94_, 9);
lean_dec(v_unused_242_);
v___x_223_ = v_cfg_94_;
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
lean_dec(v_cfg_94_);
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
lean_dec_ref(v_name_93_);
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
lean_ctor_set(v_reuseFailAlloc_232_, 9, v_configLang_x3f_97_);
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
lean_ctor_set(v___x_231_, 1, v_a_95_);
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
lean_dec_ref_known(v_configLang_x3f_97_, 1);
lean_dec_ref(v_lakeEnv_204_);
v___x_233_ = ((lean_object*)(l_Lake_resolveConfigFile___closed__3));
v___x_234_ = lean_string_append(v_name_93_, v___x_233_);
v___x_235_ = lean_string_append(v___x_234_, v_configFile_212_);
lean_dec_ref(v_configFile_212_);
v___x_236_ = 3;
v___x_237_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_237_, 0, v___x_235_);
lean_ctor_set_uint8(v___x_237_, sizeof(void*)*1, v___x_236_);
v___x_238_ = lean_array_get_size(v_a_95_);
v___x_239_ = lean_array_push(v_a_95_, v___x_237_);
v___x_240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_238_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
return v___x_240_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_resolveConfigFile_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_93_ = stack[0].m_obj;
lean_object* v_cfg_94_ = stack[1].m_obj;
lean_object* v_a_95_ = stack[2].m_obj;
lean_object* v_res_243_;
v_res_243_ = l_Lake_resolveConfigFile(v_name_93_, v_cfg_94_, v_a_95_);
stack->m_obj
 = v_res_243_;
}
LEAN_EXPORT lean_object* l_Lake_resolveConfigFile___boxed(lean_object* v_name_244_, lean_object* v_cfg_245_, lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lake_resolveConfigFile(v_name_244_, v_cfg_245_, v_a_246_);
return v_res_248_;
}
}
lean_object* l_Lake_loadConfigFile___redArg(lean_object* v_cfg_249_, lean_object* v_a_250_){
_start:
{
lean_object* v_configLang_x3f_252_; lean_object* v_val_253_; uint8_t v___x_254_; 
v_configLang_x3f_252_ = lean_ctor_get(v_cfg_249_, 9);
v_val_253_ = lean_ctor_get(v_configLang_x3f_252_, 0);
v___x_254_ = lean_unbox(v_val_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; 
v___x_255_ = l_Lake_loadLeanConfig(v_cfg_249_, v_a_250_);
return v___x_255_;
}
else
{
lean_object* v___x_256_; 
v___x_256_ = l_Lake_loadTomlConfig(v_cfg_249_, v_a_250_);
return v___x_256_;
}
}
}
LEAN_EXPORT void l_Lake_loadConfigFile___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_249_ = stack[0].m_obj;
lean_object* v_a_250_ = stack[1].m_obj;
lean_object* v_res_257_;
v_res_257_ = l_Lake_loadConfigFile___redArg(v_cfg_249_, v_a_250_);
stack->m_obj
 = v_res_257_;
}
LEAN_EXPORT lean_object* l_Lake_loadConfigFile___redArg___boxed(lean_object* v_cfg_258_, lean_object* v_a_259_, lean_object* v_a_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lake_loadConfigFile___redArg(v_cfg_258_, v_a_259_);
return v_res_261_;
}
}
lean_object* l_Lake_loadConfigFile(lean_object* v_cfg_262_, lean_object* v_h_263_, lean_object* v_a_264_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lake_loadConfigFile___redArg(v_cfg_262_, v_a_264_);
return v___x_266_;
}
}
LEAN_EXPORT void l_Lake_loadConfigFile_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_262_ = stack[0].m_obj;
lean_object* v_a_264_ = stack[2].m_obj;
lean_object* v_res_267_;
v_res_267_ = l_Lake_loadConfigFile(v_cfg_262_, lean_box(0), v_a_264_);
stack->m_obj
 = v_res_267_;
}
LEAN_EXPORT lean_object* l_Lake_loadConfigFile___boxed(lean_object* v_cfg_268_, lean_object* v_h_269_, lean_object* v_a_270_, lean_object* v_a_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lake_loadConfigFile(v_cfg_268_, v_h_269_, v_a_270_);
return v_res_272_;
}
}
lean_object* l_Lake_loadPackage(lean_object* v_cfg_274_, lean_object* v_a_275_){
_start:
{
lean_object* v_lakeEnv_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v_lakeEnv_277_ = lean_ctor_get(v_cfg_274_, 0);
v___x_278_ = l_Lean_searchPathRef;
v___x_279_ = l_Lake_Env_leanSearchPath(v_lakeEnv_277_);
v___x_280_ = lean_st_ref_swap(v___x_278_, v___x_279_);
lean_dec(v___x_280_);
v___x_281_ = ((lean_object*)(l_Lake_loadPackage___closed__0));
v___x_282_ = l_Lake_resolveConfigFile(v___x_281_, v_cfg_274_, v_a_275_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; lean_object* v_a_284_; lean_object* v___x_285_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc_n(v_a_283_, 2);
v_a_284_ = lean_ctor_get(v___x_282_, 1);
lean_inc(v_a_284_);
lean_dec_ref_known(v___x_282_, 2);
v___x_285_ = l_Lake_loadConfigFile___redArg(v_a_283_, v_a_284_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_296_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
v_a_287_ = lean_ctor_get(v___x_285_, 1);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_296_ == 0)
{
v___x_289_ = v___x_285_;
v_isShared_290_ = v_isSharedCheck_296_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_inc(v_a_286_);
lean_dec(v___x_285_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_296_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v_pkgIdx_291_; lean_object* v___x_292_; lean_object* v___x_294_; 
v_pkgIdx_291_ = lean_ctor_get(v_a_283_, 3);
lean_inc(v_pkgIdx_291_);
v___x_292_ = l_Lake_mkPackage(v_a_283_, v_a_286_, v_pkgIdx_291_);
lean_dec(v_a_283_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_292_);
v___x_294_ = v___x_289_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_a_287_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
else
{
lean_object* v_a_297_; lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
lean_dec(v_a_283_);
v_a_297_ = lean_ctor_get(v___x_285_, 0);
v_a_298_ = lean_ctor_get(v___x_285_, 1);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_285_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_inc(v_a_297_);
lean_dec(v___x_285_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_297_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v_a_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
else
{
lean_object* v_a_306_; lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
v_a_306_ = lean_ctor_get(v___x_282_, 0);
v_a_307_ = lean_ctor_get(v___x_282_, 1);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_314_ == 0)
{
v___x_309_ = v___x_282_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_inc(v_a_306_);
lean_dec(v___x_282_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_306_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_a_307_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_loadPackage_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_274_ = stack[0].m_obj;
lean_object* v_a_275_ = stack[1].m_obj;
lean_object* v_res_315_;
v_res_315_ = l_Lake_loadPackage(v_cfg_274_, v_a_275_);
stack->m_obj
 = v_res_315_;
}
LEAN_EXPORT lean_object* l_Lake_loadPackage___boxed(lean_object* v_cfg_316_, lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lake_loadPackage(v_cfg_316_, v_a_317_);
return v_res_319_;
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
