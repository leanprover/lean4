// Lean compiler output
// Module: Lake.Load.Package
// Imports: public import Lake.Load.Config public import Lake.Config.Package import Lake.Util.IO import Lake.Load.Lean import Lake.Load.Toml
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
lean_object* l_Lake_resolvePath(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_loadTomlConfig(lean_object*, lean_object*);
lean_object* l_Lake_loadLeanConfig(lean_object*, lean_object*);
lean_object* l_Prod_map___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
extern lean_object* l_Lean_searchPathRef;
lean_object* l_Lake_Env_leanSearchPath(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
static const lean_string_object l_Lake_configFileExists___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lake_configFileExists___closed__0 = (const lean_object*)&l_Lake_configFileExists___closed__0_value;
static const lean_string_object l_Lake_configFileExists___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "toml"};
static const lean_object* l_Lake_configFileExists___closed__1 = (const lean_object*)&l_Lake_configFileExists___closed__1_value;
LEAN_EXPORT uint8_t l_Lake_configFileExists(lean_object*);
LEAN_EXPORT lean_object* l_Lake_configFileExists___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_realConfigFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_realConfigFile___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__1(lean_object*);
static const lean_string_object l_Lake_loadPackageCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = ": configuration has unsupported file extension: "};
static const lean_object* l_Lake_loadPackageCore___closed__0 = (const lean_object*)&l_Lake_loadPackageCore___closed__0_value;
static const lean_closure_object l_Lake_loadPackageCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_loadPackageCore___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_loadPackageCore___closed__1 = (const lean_object*)&l_Lake_loadPackageCore___closed__1_value;
static const lean_closure_object l_Lake_loadPackageCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_loadPackageCore___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_loadPackageCore___closed__2 = (const lean_object*)&l_Lake_loadPackageCore___closed__2_value;
static const lean_string_object l_Lake_loadPackageCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = ": configuration file not found: "};
static const lean_object* l_Lake_loadPackageCore___closed__3 = (const lean_object*)&l_Lake_loadPackageCore___closed__3_value;
static const lean_string_object l_Lake_loadPackageCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lake_loadPackageCore___closed__4 = (const lean_object*)&l_Lake_loadPackageCore___closed__4_value;
static const lean_string_object l_Lake_loadPackageCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " and "};
static const lean_object* l_Lake_loadPackageCore___closed__5 = (const lean_object*)&l_Lake_loadPackageCore___closed__5_value;
static const lean_string_object l_Lake_loadPackageCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = " are both present; using "};
static const lean_object* l_Lake_loadPackageCore___closed__6 = (const lean_object*)&l_Lake_loadPackageCore___closed__6_value;
static const lean_string_object l_Lake_loadPackageCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = ": no configuration file with a supported extension:\n"};
static const lean_object* l_Lake_loadPackageCore___closed__7 = (const lean_object*)&l_Lake_loadPackageCore___closed__7_value;
static const lean_string_object l_Lake_loadPackageCore___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lake_loadPackageCore___closed__8 = (const lean_object*)&l_Lake_loadPackageCore___closed__8_value;
LEAN_EXPORT lean_object* l_Lake_loadPackageCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_loadPackage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "[root]"};
static const lean_object* l_Lake_loadPackage___closed__0 = (const lean_object*)&l_Lake_loadPackage___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_loadPackage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackage___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_configFileExists(lean_object* v_cfgFile_3_){
_start:
{
lean_object* v___x_5_; 
lean_inc_ref(v_cfgFile_3_);
v___x_5_ = l_System_FilePath_extension(v_cfgFile_3_);
if (lean_obj_tag(v___x_5_) == 0)
{
lean_object* v___x_6_; lean_object* v_leanFile_7_; uint8_t v___x_8_; 
v___x_6_ = ((lean_object*)(l_Lake_configFileExists___closed__0));
lean_inc_ref(v_cfgFile_3_);
v_leanFile_7_ = l_System_FilePath_addExtension(v_cfgFile_3_, v___x_6_);
v___x_8_ = l_System_FilePath_pathExists(v_leanFile_7_);
lean_dec_ref(v_leanFile_7_);
if (v___x_8_ == 0)
{
lean_object* v___x_9_; lean_object* v_tomlFile_10_; uint8_t v___x_11_; 
v___x_9_ = ((lean_object*)(l_Lake_configFileExists___closed__1));
v_tomlFile_10_ = l_System_FilePath_addExtension(v_cfgFile_3_, v___x_9_);
v___x_11_ = l_System_FilePath_pathExists(v_tomlFile_10_);
lean_dec_ref(v_tomlFile_10_);
return v___x_11_;
}
else
{
lean_dec_ref(v_cfgFile_3_);
return v___x_8_;
}
}
else
{
uint8_t v___x_12_; 
lean_dec_ref(v___x_5_);
v___x_12_ = l_System_FilePath_pathExists(v_cfgFile_3_);
lean_dec_ref(v_cfgFile_3_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_configFileExists___boxed(lean_object* v_cfgFile_13_, lean_object* v_a_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l_Lake_configFileExists(v_cfgFile_13_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
LEAN_EXPORT lean_object* l_Lake_realConfigFile(lean_object* v_cfgFile_17_){
_start:
{
lean_object* v___x_19_; 
lean_inc_ref(v_cfgFile_17_);
v___x_19_ = l_System_FilePath_extension(v_cfgFile_17_);
if (lean_obj_tag(v___x_19_) == 0)
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; uint8_t v___x_25_; 
v___x_20_ = ((lean_object*)(l_Lake_configFileExists___closed__0));
lean_inc_ref(v_cfgFile_17_);
v___x_21_ = l_System_FilePath_addExtension(v_cfgFile_17_, v___x_20_);
v___x_22_ = l_Lake_resolvePath(v___x_21_);
v___x_23_ = lean_string_utf8_byte_size(v___x_22_);
v___x_24_ = lean_unsigned_to_nat(0u);
v___x_25_ = lean_nat_dec_eq(v___x_23_, v___x_24_);
if (v___x_25_ == 0)
{
lean_dec_ref(v_cfgFile_17_);
return v___x_22_;
}
else
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
lean_dec_ref(v___x_22_);
v___x_26_ = ((lean_object*)(l_Lake_configFileExists___closed__1));
v___x_27_ = l_System_FilePath_addExtension(v_cfgFile_17_, v___x_26_);
v___x_28_ = l_Lake_resolvePath(v___x_27_);
return v___x_28_;
}
}
else
{
lean_object* v___x_29_; 
lean_dec_ref(v___x_19_);
v___x_29_ = l_Lake_resolvePath(v_cfgFile_17_);
return v___x_29_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_realConfigFile___boxed(lean_object* v_cfgFile_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lake_realConfigFile(v_cfgFile_30_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__0(lean_object* v___y_33_){
_start:
{
lean_inc_ref(v___y_33_);
return v___y_33_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__0___boxed(lean_object* v___y_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lake_loadPackageCore___lam__0(v___y_34_);
lean_dec_ref(v___y_34_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__1(lean_object* v_val_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_37_, 0, v_val_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore(lean_object* v_name_47_, lean_object* v_cfg_48_, lean_object* v_a_49_){
_start:
{
lean_object* v_lakeEnv_51_; lean_object* v_lakeArgs_x3f_52_; lean_object* v_wsDir_53_; lean_object* v_pkgIdx_54_; lean_object* v_pkgName_55_; lean_object* v_relPkgDir_56_; lean_object* v_pkgDir_57_; lean_object* v_relConfigFile_58_; lean_object* v_configFile_59_; lean_object* v_packageOverrides_60_; lean_object* v_lakeOpts_61_; lean_object* v_leanOpts_62_; uint8_t v_reconfigure_63_; uint8_t v_updateDeps_64_; uint8_t v_updateToolchain_65_; lean_object* v_scope_66_; lean_object* v_remoteUrl_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_238_; 
v_lakeEnv_51_ = lean_ctor_get(v_cfg_48_, 0);
v_lakeArgs_x3f_52_ = lean_ctor_get(v_cfg_48_, 1);
v_wsDir_53_ = lean_ctor_get(v_cfg_48_, 2);
v_pkgIdx_54_ = lean_ctor_get(v_cfg_48_, 3);
v_pkgName_55_ = lean_ctor_get(v_cfg_48_, 4);
v_relPkgDir_56_ = lean_ctor_get(v_cfg_48_, 5);
v_pkgDir_57_ = lean_ctor_get(v_cfg_48_, 6);
v_relConfigFile_58_ = lean_ctor_get(v_cfg_48_, 7);
v_configFile_59_ = lean_ctor_get(v_cfg_48_, 8);
v_packageOverrides_60_ = lean_ctor_get(v_cfg_48_, 9);
v_lakeOpts_61_ = lean_ctor_get(v_cfg_48_, 10);
v_leanOpts_62_ = lean_ctor_get(v_cfg_48_, 11);
v_reconfigure_63_ = lean_ctor_get_uint8(v_cfg_48_, sizeof(void*)*14);
v_updateDeps_64_ = lean_ctor_get_uint8(v_cfg_48_, sizeof(void*)*14 + 1);
v_updateToolchain_65_ = lean_ctor_get_uint8(v_cfg_48_, sizeof(void*)*14 + 2);
v_scope_66_ = lean_ctor_get(v_cfg_48_, 12);
v_remoteUrl_67_ = lean_ctor_get(v_cfg_48_, 13);
v_isSharedCheck_238_ = !lean_is_exclusive(v_cfg_48_);
if (v_isSharedCheck_238_ == 0)
{
v___x_69_ = v_cfg_48_;
v_isShared_70_ = v_isSharedCheck_238_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_remoteUrl_67_);
lean_inc(v_scope_66_);
lean_inc(v_leanOpts_62_);
lean_inc(v_lakeOpts_61_);
lean_inc(v_packageOverrides_60_);
lean_inc(v_configFile_59_);
lean_inc(v_relConfigFile_58_);
lean_inc(v_pkgDir_57_);
lean_inc(v_relPkgDir_56_);
lean_inc(v_pkgName_55_);
lean_inc(v_pkgIdx_54_);
lean_inc(v_wsDir_53_);
lean_inc(v_lakeArgs_x3f_52_);
lean_inc(v_lakeEnv_51_);
lean_dec(v_cfg_48_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_238_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_71_; 
lean_inc_ref(v_relConfigFile_58_);
v___x_71_ = l_System_FilePath_extension(v_relConfigFile_58_);
if (lean_obj_tag(v___x_71_) == 1)
{
lean_object* v_val_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v_val_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc(v_val_72_);
lean_dec_ref(v___x_71_);
lean_inc_ref(v_configFile_59_);
v___x_73_ = l_Lake_resolvePath(v_configFile_59_);
v___x_74_ = lean_string_utf8_byte_size(v___x_73_);
v___x_75_ = lean_unsigned_to_nat(0u);
v___x_76_ = lean_nat_dec_eq(v___x_74_, v___x_75_);
if (v___x_76_ == 0)
{
lean_object* v___x_78_; 
lean_dec_ref(v_configFile_59_);
lean_inc_ref(v___x_73_);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 8, v___x_73_);
v___x_78_ = v___x_69_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 14, 3);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_lakeEnv_51_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_lakeArgs_x3f_52_);
lean_ctor_set(v_reuseFailAlloc_134_, 2, v_wsDir_53_);
lean_ctor_set(v_reuseFailAlloc_134_, 3, v_pkgIdx_54_);
lean_ctor_set(v_reuseFailAlloc_134_, 4, v_pkgName_55_);
lean_ctor_set(v_reuseFailAlloc_134_, 5, v_relPkgDir_56_);
lean_ctor_set(v_reuseFailAlloc_134_, 6, v_pkgDir_57_);
lean_ctor_set(v_reuseFailAlloc_134_, 7, v_relConfigFile_58_);
lean_ctor_set(v_reuseFailAlloc_134_, 8, v___x_73_);
lean_ctor_set(v_reuseFailAlloc_134_, 9, v_packageOverrides_60_);
lean_ctor_set(v_reuseFailAlloc_134_, 10, v_lakeOpts_61_);
lean_ctor_set(v_reuseFailAlloc_134_, 11, v_leanOpts_62_);
lean_ctor_set(v_reuseFailAlloc_134_, 12, v_scope_66_);
lean_ctor_set(v_reuseFailAlloc_134_, 13, v_remoteUrl_67_);
lean_ctor_set_uint8(v_reuseFailAlloc_134_, sizeof(void*)*14, v_reconfigure_63_);
lean_ctor_set_uint8(v_reuseFailAlloc_134_, sizeof(void*)*14 + 1, v_updateDeps_64_);
lean_ctor_set_uint8(v_reuseFailAlloc_134_, sizeof(void*)*14 + 2, v_updateToolchain_65_);
v___x_78_ = v_reuseFailAlloc_134_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = ((lean_object*)(l_Lake_configFileExists___closed__0));
v___x_80_ = lean_string_dec_eq(v_val_72_, v___x_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_81_ = ((lean_object*)(l_Lake_configFileExists___closed__1));
v___x_82_ = lean_string_dec_eq(v_val_72_, v___x_81_);
lean_dec(v_val_72_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
lean_dec_ref(v___x_78_);
v___x_83_ = ((lean_object*)(l_Lake_loadPackageCore___closed__0));
v___x_84_ = lean_string_append(v_name_47_, v___x_83_);
v___x_85_ = lean_string_append(v___x_84_, v___x_73_);
lean_dec_ref(v___x_73_);
v___x_86_ = 3;
v___x_87_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_87_, 0, v___x_85_);
lean_ctor_set_uint8(v___x_87_, sizeof(void*)*1, v___x_86_);
v___x_88_ = lean_array_get_size(v_a_49_);
v___x_89_ = lean_array_push(v_a_49_, v___x_87_);
v___x_90_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_88_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
return v___x_90_;
}
else
{
lean_object* v___x_91_; 
lean_dec_ref(v___x_73_);
lean_dec_ref(v_name_47_);
v___x_91_ = l_Lake_loadTomlConfig(v___x_78_, v_a_49_);
if (lean_obj_tag(v___x_91_) == 0)
{
lean_object* v_a_92_; lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_102_; 
v_a_92_ = lean_ctor_get(v___x_91_, 0);
v_a_93_ = lean_ctor_get(v___x_91_, 1);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_102_ == 0)
{
v___x_95_ = v___x_91_;
v_isShared_96_ = v_isSharedCheck_102_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_inc(v_a_92_);
lean_dec(v___x_91_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_102_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_100_; 
v___x_97_ = lean_box(0);
v___x_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_98_, 0, v_a_92_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 0, v___x_98_);
v___x_100_ = v___x_95_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v___x_98_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_a_93_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
else
{
lean_object* v_a_103_; lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_111_; 
v_a_103_ = lean_ctor_get(v___x_91_, 0);
v_a_104_ = lean_ctor_get(v___x_91_, 1);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_111_ == 0)
{
v___x_106_ = v___x_91_;
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_inc(v_a_103_);
lean_dec(v___x_91_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_109_; 
if (v_isShared_107_ == 0)
{
v___x_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_a_103_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v_a_104_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
}
else
{
lean_object* v___x_112_; 
lean_dec_ref(v___x_73_);
lean_dec(v_val_72_);
lean_dec_ref(v_name_47_);
v___x_112_ = l_Lake_loadLeanConfig(v___x_78_, v_a_49_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v_a_113_; lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_124_; 
v_a_113_ = lean_ctor_get(v___x_112_, 0);
v_a_114_ = lean_ctor_get(v___x_112_, 1);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_124_ == 0)
{
v___x_116_ = v___x_112_;
v_isShared_117_ = v_isSharedCheck_124_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_inc(v_a_113_);
lean_dec(v___x_112_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_124_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___f_118_; lean_object* v___f_119_; lean_object* v___x_120_; lean_object* v___x_122_; 
v___f_118_ = ((lean_object*)(l_Lake_loadPackageCore___closed__1));
v___f_119_ = ((lean_object*)(l_Lake_loadPackageCore___closed__2));
v___x_120_ = l_Prod_map___redArg(v___f_118_, v___f_119_, v_a_113_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 0, v___x_120_);
v___x_122_ = v___x_116_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v_a_114_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
else
{
lean_object* v_a_125_; lean_object* v_a_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_133_; 
v_a_125_ = lean_ctor_get(v___x_112_, 0);
v_a_126_ = lean_ctor_get(v___x_112_, 1);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_133_ == 0)
{
v___x_128_ = v___x_112_;
v_isShared_129_ = v_isSharedCheck_133_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_a_126_);
lean_inc(v_a_125_);
lean_dec(v___x_112_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_133_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_131_; 
if (v_isShared_129_ == 0)
{
v___x_131_ = v___x_128_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_a_125_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v_a_126_);
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
}
}
else
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
lean_dec_ref(v___x_73_);
lean_dec(v_val_72_);
lean_del_object(v___x_69_);
lean_dec_ref(v_remoteUrl_67_);
lean_dec_ref(v_scope_66_);
lean_dec_ref(v_leanOpts_62_);
lean_dec(v_lakeOpts_61_);
lean_dec_ref(v_packageOverrides_60_);
lean_dec_ref(v_relConfigFile_58_);
lean_dec_ref(v_pkgDir_57_);
lean_dec_ref(v_relPkgDir_56_);
lean_dec(v_pkgName_55_);
lean_dec(v_pkgIdx_54_);
lean_dec_ref(v_wsDir_53_);
lean_dec(v_lakeArgs_x3f_52_);
lean_dec_ref(v_lakeEnv_51_);
v___x_135_ = ((lean_object*)(l_Lake_loadPackageCore___closed__3));
v___x_136_ = lean_string_append(v_name_47_, v___x_135_);
v___x_137_ = lean_string_append(v___x_136_, v_configFile_59_);
lean_dec_ref(v_configFile_59_);
v___x_138_ = 3;
v___x_139_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_139_, 0, v___x_137_);
lean_ctor_set_uint8(v___x_139_, sizeof(void*)*1, v___x_138_);
v___x_140_ = lean_array_get_size(v_a_49_);
v___x_141_ = lean_array_push(v_a_49_, v___x_139_);
v___x_142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_140_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
return v___x_142_;
}
}
else
{
lean_object* v___x_143_; lean_object* v_relLeanFile_144_; lean_object* v_leanFile_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v_relTomlFile_148_; lean_object* v_tomlFile_149_; lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
lean_dec(v___x_71_);
lean_dec_ref(v_configFile_59_);
v___x_143_ = ((lean_object*)(l_Lake_configFileExists___closed__0));
lean_inc_ref(v_relConfigFile_58_);
v_relLeanFile_144_ = l_System_FilePath_addExtension(v_relConfigFile_58_, v___x_143_);
lean_inc_ref(v_relLeanFile_144_);
lean_inc_ref(v_pkgDir_57_);
v_leanFile_145_ = l_Lake_joinRelative(v_pkgDir_57_, v_relLeanFile_144_);
lean_inc_ref(v_leanFile_145_);
v___x_146_ = l_Lake_resolvePath(v_leanFile_145_);
v___x_147_ = ((lean_object*)(l_Lake_configFileExists___closed__1));
v_relTomlFile_148_ = l_System_FilePath_addExtension(v_relConfigFile_58_, v___x_147_);
lean_inc_ref(v_relTomlFile_148_);
lean_inc_ref(v_pkgDir_57_);
v_tomlFile_149_ = l_Lake_joinRelative(v_pkgDir_57_, v_relTomlFile_148_);
v___x_150_ = lean_string_utf8_byte_size(v___x_146_);
v___x_151_ = lean_unsigned_to_nat(0u);
v___x_152_ = lean_nat_dec_eq(v___x_150_, v___x_151_);
if (v___x_152_ == 0)
{
uint8_t v___x_153_; lean_object* v___y_155_; 
lean_dec_ref(v_leanFile_145_);
v___x_153_ = l_System_FilePath_pathExists(v_tomlFile_149_);
lean_dec_ref(v_tomlFile_149_);
if (v___x_153_ == 0)
{
lean_dec_ref(v_relTomlFile_148_);
lean_dec_ref(v_name_47_);
v___y_155_ = v_a_49_;
goto v___jp_154_;
}
else
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_188_ = ((lean_object*)(l_Lake_loadPackageCore___closed__4));
v___x_189_ = lean_string_append(v_name_47_, v___x_188_);
v___x_190_ = lean_string_append(v___x_189_, v_relLeanFile_144_);
v___x_191_ = ((lean_object*)(l_Lake_loadPackageCore___closed__5));
v___x_192_ = lean_string_append(v___x_190_, v___x_191_);
v___x_193_ = lean_string_append(v___x_192_, v_relTomlFile_148_);
lean_dec_ref(v_relTomlFile_148_);
v___x_194_ = ((lean_object*)(l_Lake_loadPackageCore___closed__6));
v___x_195_ = lean_string_append(v___x_193_, v___x_194_);
v___x_196_ = lean_string_append(v___x_195_, v_relLeanFile_144_);
v___x_197_ = 1;
v___x_198_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_198_, 0, v___x_196_);
lean_ctor_set_uint8(v___x_198_, sizeof(void*)*1, v___x_197_);
v___x_199_ = lean_array_push(v_a_49_, v___x_198_);
v___y_155_ = v___x_199_;
goto v___jp_154_;
}
v___jp_154_:
{
lean_object* v___x_157_; 
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 8, v___x_146_);
lean_ctor_set(v___x_69_, 7, v_relLeanFile_144_);
v___x_157_ = v___x_69_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 14, 3);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_lakeEnv_51_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v_lakeArgs_x3f_52_);
lean_ctor_set(v_reuseFailAlloc_187_, 2, v_wsDir_53_);
lean_ctor_set(v_reuseFailAlloc_187_, 3, v_pkgIdx_54_);
lean_ctor_set(v_reuseFailAlloc_187_, 4, v_pkgName_55_);
lean_ctor_set(v_reuseFailAlloc_187_, 5, v_relPkgDir_56_);
lean_ctor_set(v_reuseFailAlloc_187_, 6, v_pkgDir_57_);
lean_ctor_set(v_reuseFailAlloc_187_, 7, v_relLeanFile_144_);
lean_ctor_set(v_reuseFailAlloc_187_, 8, v___x_146_);
lean_ctor_set(v_reuseFailAlloc_187_, 9, v_packageOverrides_60_);
lean_ctor_set(v_reuseFailAlloc_187_, 10, v_lakeOpts_61_);
lean_ctor_set(v_reuseFailAlloc_187_, 11, v_leanOpts_62_);
lean_ctor_set(v_reuseFailAlloc_187_, 12, v_scope_66_);
lean_ctor_set(v_reuseFailAlloc_187_, 13, v_remoteUrl_67_);
lean_ctor_set_uint8(v_reuseFailAlloc_187_, sizeof(void*)*14, v_reconfigure_63_);
lean_ctor_set_uint8(v_reuseFailAlloc_187_, sizeof(void*)*14 + 1, v_updateDeps_64_);
lean_ctor_set_uint8(v_reuseFailAlloc_187_, sizeof(void*)*14 + 2, v_updateToolchain_65_);
v___x_157_ = v_reuseFailAlloc_187_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
lean_object* v___x_158_; 
v___x_158_ = l_Lake_loadLeanConfig(v___x_157_, v___y_155_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_177_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
v_a_160_ = lean_ctor_get(v___x_158_, 1);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_177_ == 0)
{
v___x_162_ = v___x_158_;
v_isShared_163_ = v_isSharedCheck_177_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_inc(v_a_159_);
lean_dec(v___x_158_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_177_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v_fst_164_; lean_object* v_snd_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_176_; 
v_fst_164_ = lean_ctor_get(v_a_159_, 0);
v_snd_165_ = lean_ctor_get(v_a_159_, 1);
v_isSharedCheck_176_ = !lean_is_exclusive(v_a_159_);
if (v_isSharedCheck_176_ == 0)
{
v___x_167_ = v_a_159_;
v_isShared_168_ = v_isSharedCheck_176_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_snd_165_);
lean_inc(v_fst_164_);
lean_dec(v_a_159_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_176_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_169_; lean_object* v___x_171_; 
v___x_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_169_, 0, v_snd_165_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 1, v___x_169_);
v___x_171_ = v___x_167_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_fst_164_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v___x_169_);
v___x_171_ = v_reuseFailAlloc_175_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
lean_object* v___x_173_; 
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v___x_171_);
v___x_173_ = v___x_162_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_171_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v_a_160_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
}
else
{
lean_object* v_a_178_; lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
v_a_178_ = lean_ctor_get(v___x_158_, 0);
v_a_179_ = lean_ctor_get(v___x_158_, 1);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v___x_158_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_inc(v_a_178_);
lean_dec(v___x_158_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_178_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
}
}
else
{
lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
lean_dec_ref(v___x_146_);
lean_dec_ref(v_relLeanFile_144_);
lean_inc_ref(v_tomlFile_149_);
v___x_200_ = l_Lake_resolvePath(v_tomlFile_149_);
v___x_201_ = lean_string_utf8_byte_size(v___x_200_);
v___x_202_ = lean_nat_dec_eq(v___x_201_, v___x_151_);
if (v___x_202_ == 0)
{
lean_object* v___x_204_; 
lean_dec_ref(v_tomlFile_149_);
lean_dec_ref(v_leanFile_145_);
lean_dec_ref(v_name_47_);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 8, v___x_200_);
lean_ctor_set(v___x_69_, 7, v_relTomlFile_148_);
v___x_204_ = v___x_69_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 14, 3);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_lakeEnv_51_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v_lakeArgs_x3f_52_);
lean_ctor_set(v_reuseFailAlloc_226_, 2, v_wsDir_53_);
lean_ctor_set(v_reuseFailAlloc_226_, 3, v_pkgIdx_54_);
lean_ctor_set(v_reuseFailAlloc_226_, 4, v_pkgName_55_);
lean_ctor_set(v_reuseFailAlloc_226_, 5, v_relPkgDir_56_);
lean_ctor_set(v_reuseFailAlloc_226_, 6, v_pkgDir_57_);
lean_ctor_set(v_reuseFailAlloc_226_, 7, v_relTomlFile_148_);
lean_ctor_set(v_reuseFailAlloc_226_, 8, v___x_200_);
lean_ctor_set(v_reuseFailAlloc_226_, 9, v_packageOverrides_60_);
lean_ctor_set(v_reuseFailAlloc_226_, 10, v_lakeOpts_61_);
lean_ctor_set(v_reuseFailAlloc_226_, 11, v_leanOpts_62_);
lean_ctor_set(v_reuseFailAlloc_226_, 12, v_scope_66_);
lean_ctor_set(v_reuseFailAlloc_226_, 13, v_remoteUrl_67_);
lean_ctor_set_uint8(v_reuseFailAlloc_226_, sizeof(void*)*14, v_reconfigure_63_);
lean_ctor_set_uint8(v_reuseFailAlloc_226_, sizeof(void*)*14 + 1, v_updateDeps_64_);
lean_ctor_set_uint8(v_reuseFailAlloc_226_, sizeof(void*)*14 + 2, v_updateToolchain_65_);
v___x_204_ = v_reuseFailAlloc_226_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lake_loadTomlConfig(v___x_204_, v_a_49_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_a_206_; lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_216_; 
v_a_206_ = lean_ctor_get(v___x_205_, 0);
v_a_207_ = lean_ctor_get(v___x_205_, 1);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_216_ == 0)
{
v___x_209_ = v___x_205_;
v_isShared_210_ = v_isSharedCheck_216_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_inc(v_a_206_);
lean_dec(v___x_205_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_216_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_214_; 
v___x_211_ = lean_box(0);
v___x_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_212_, 0, v_a_206_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 0, v___x_212_);
v___x_214_ = v___x_209_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_212_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_a_207_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
else
{
lean_object* v_a_217_; lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
v_a_217_ = lean_ctor_get(v___x_205_, 0);
v_a_218_ = lean_ctor_get(v___x_205_, 1);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_225_ == 0)
{
v___x_220_ = v___x_205_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_inc(v_a_217_);
lean_dec(v___x_205_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_217_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_a_218_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
}
else
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
lean_dec_ref(v___x_200_);
lean_dec_ref(v_relTomlFile_148_);
lean_del_object(v___x_69_);
lean_dec_ref(v_remoteUrl_67_);
lean_dec_ref(v_scope_66_);
lean_dec_ref(v_leanOpts_62_);
lean_dec(v_lakeOpts_61_);
lean_dec_ref(v_packageOverrides_60_);
lean_dec_ref(v_pkgDir_57_);
lean_dec_ref(v_relPkgDir_56_);
lean_dec(v_pkgName_55_);
lean_dec(v_pkgIdx_54_);
lean_dec_ref(v_wsDir_53_);
lean_dec(v_lakeArgs_x3f_52_);
lean_dec_ref(v_lakeEnv_51_);
v___x_227_ = ((lean_object*)(l_Lake_loadPackageCore___closed__7));
v___x_228_ = lean_string_append(v_name_47_, v___x_227_);
v___x_229_ = lean_string_append(v___x_228_, v_leanFile_145_);
lean_dec_ref(v_leanFile_145_);
v___x_230_ = ((lean_object*)(l_Lake_loadPackageCore___closed__8));
v___x_231_ = lean_string_append(v___x_229_, v___x_230_);
v___x_232_ = lean_string_append(v___x_231_, v_tomlFile_149_);
lean_dec_ref(v_tomlFile_149_);
v___x_233_ = 3;
v___x_234_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_234_, 0, v___x_232_);
lean_ctor_set_uint8(v___x_234_, sizeof(void*)*1, v___x_233_);
v___x_235_ = lean_array_get_size(v_a_49_);
v___x_236_ = lean_array_push(v_a_49_, v___x_234_);
v___x_237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_235_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
return v___x_237_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___boxed(lean_object* v_name_239_, lean_object* v_cfg_240_, lean_object* v_a_241_, lean_object* v_a_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lake_loadPackageCore(v_name_239_, v_cfg_240_, v_a_241_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackage(lean_object* v_config_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_lakeEnv_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v_lakeEnv_248_ = lean_ctor_get(v_config_245_, 0);
v___x_249_ = l_Lean_searchPathRef;
v___x_250_ = l_Lake_Env_leanSearchPath(v_lakeEnv_248_);
v___x_251_ = lean_st_ref_set(v___x_249_, v___x_250_);
v___x_252_ = ((lean_object*)(l_Lake_loadPackage___closed__0));
v___x_253_ = l_Lake_loadPackageCore(v___x_252_, v_config_245_, v_a_246_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_263_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
v_a_255_ = lean_ctor_get(v___x_253_, 1);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_263_ == 0)
{
v___x_257_ = v___x_253_;
v_isShared_258_ = v_isSharedCheck_263_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_inc(v_a_254_);
lean_dec(v___x_253_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_263_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v_fst_259_; lean_object* v___x_261_; 
v_fst_259_ = lean_ctor_get(v_a_254_, 0);
lean_inc(v_fst_259_);
lean_dec(v_a_254_);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 0, v_fst_259_);
v___x_261_ = v___x_257_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_fst_259_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_a_255_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
else
{
lean_object* v_a_264_; lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
v_a_264_ = lean_ctor_get(v___x_253_, 0);
v_a_265_ = lean_ctor_get(v___x_253_, 1);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v___x_253_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_inc(v_a_264_);
lean_dec(v___x_253_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_264_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_a_265_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackage___boxed(lean_object* v_config_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lake_loadPackage(v_config_273_, v_a_274_);
return v_res_276_;
}
}
lean_object* runtime_initialize_Lake_Load_Config(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Package(uint8_t builtin);
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
