// Lean compiler output
// Module: Lake.Build.Context
// Imports: public import Lake.Config.Cache public import Lake.Config.Context public import Lake.Build.Job.Basic
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
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT uint8_t l_Lake_BuildConfig_showProgress(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildConfig_showProgress___boxed(lean_object*);
static const lean_array_object l_Lake_mkJobQueue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_mkJobQueue___closed__0 = (const lean_object*)&l_Lake_mkJobQueue___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_mkJobQueue();
LEAN_EXPORT lean_object* l_Lake_mkJobQueue___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLakeMBuildTOfPure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLakeMBuildTOfPure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getBuildContext___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getBuildContext___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getBuildContext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getBuildContext___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanTrace___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanTrace___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getLeanTrace___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getLeanTrace___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLeanTrace___redArg___closed__0 = (const lean_object*)&l_Lake_getLeanTrace___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLeanTrace___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanTrace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getBuildConfig___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getBuildConfig___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getBuildConfig___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getBuildConfig___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getBuildConfig___redArg___closed__0 = (const lean_object*)&l_Lake_getBuildConfig___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getBuildConfig___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getBuildConfig(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_getIsOldMode___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getIsOldMode___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getIsOldMode___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getIsOldMode___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getIsOldMode___redArg___closed__0 = (const lean_object*)&l_Lake_getIsOldMode___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getIsOldMode___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getIsOldMode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_getTrustHash___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getTrustHash___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getTrustHash___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getTrustHash___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getTrustHash___redArg___closed__0 = (const lean_object*)&l_Lake_getTrustHash___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getTrustHash___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getTrustHash(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_getNoBuild___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getNoBuild___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getNoBuild___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getNoBuild___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getNoBuild___redArg___closed__0 = (const lean_object*)&l_Lake_getNoBuild___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getNoBuild___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getNoBuild(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_getVerbosity___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getVerbosity___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getVerbosity___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getVerbosity___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getVerbosity___redArg___closed__0 = (const lean_object*)&l_Lake_getVerbosity___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getVerbosity___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getVerbosity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_getIsVerbose___redArg___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lake_getIsVerbose___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getIsVerbose___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getIsVerbose___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getIsVerbose___redArg___closed__0 = (const lean_object*)&l_Lake_getIsVerbose___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getIsVerbose___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getIsVerbose(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_getIsQuiet___redArg___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lake_getIsQuiet___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getIsQuiet___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getIsQuiet___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getIsQuiet___redArg___closed__0 = (const lean_object*)&l_Lake_getIsQuiet___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getIsQuiet___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getIsQuiet(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanOptOverrides___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanOptOverrides___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getLeanOptOverrides___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getLeanOptOverrides___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLeanOptOverrides___redArg___closed__0 = (const lean_object*)&l_Lake_getLeanOptOverrides___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLeanOptOverrides___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanOptOverrides(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getMacOSXDeploymentTarget_x3f___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getMacOSXDeploymentTarget_x3f___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getMacOSXDeploymentTarget_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getMacOSXDeploymentTarget_x3f___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getMacOSXDeploymentTarget_x3f___redArg___closed__0 = (const lean_object*)&l_Lake_getMacOSXDeploymentTarget_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getMacOSXDeploymentTarget_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getMacOSXDeploymentTarget_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_BuildConfig_showProgress(lean_object* v_cfg_1_){
_start:
{
uint8_t v_noBuild_2_; uint8_t v_verbosity_3_; 
v_noBuild_2_ = lean_ctor_get_uint8(v_cfg_1_, sizeof(void*)*5 + 2);
v_verbosity_3_ = lean_ctor_get_uint8(v_cfg_1_, sizeof(void*)*5 + 4);
if (v_noBuild_2_ == 0)
{
goto v___jp_4_;
}
else
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; uint8_t v___x_14_; 
v___x_11_ = lean_box(v_verbosity_3_);
v___x_12_ = lean_obj_tag_nat(v___x_11_);
lean_dec(v___x_11_);
v___x_13_ = lean_unsigned_to_nat(2u);
v___x_14_ = lean_nat_dec_eq(v___x_12_, v___x_13_);
if (v___x_14_ == 0)
{
goto v___jp_4_;
}
else
{
return v___x_14_;
}
}
v___jp_4_:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; uint8_t v___x_8_; 
v___x_5_ = lean_box(v_verbosity_3_);
v___x_6_ = lean_obj_tag_nat(v___x_5_);
lean_dec(v___x_5_);
v___x_7_ = lean_unsigned_to_nat(0u);
v___x_8_ = lean_nat_dec_eq(v___x_6_, v___x_7_);
if (v___x_8_ == 0)
{
uint8_t v___x_9_; 
v___x_9_ = 1;
return v___x_9_;
}
else
{
uint8_t v___x_10_; 
v___x_10_ = 0;
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildConfig_showProgress___boxed(lean_object* v_cfg_15_){
_start:
{
uint8_t v_res_16_; lean_object* v_r_17_; 
v_res_16_ = l_Lake_BuildConfig_showProgress(v_cfg_15_);
lean_dec_ref(v_cfg_15_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkJobQueue(){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = ((lean_object*)(l_Lake_mkJobQueue___closed__0));
v___x_22_ = lean_st_mk_ref(v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkJobQueue___boxed(lean_object* v_a_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lake_mkJobQueue();
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0(lean_object* v_inst_25_, lean_object* v_00_u03b1_26_, lean_object* v_x_27_, lean_object* v_ctx_28_){
_start:
{
lean_object* v_toContext_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v_toContext_29_ = lean_ctor_get(v_ctx_28_, 1);
lean_inc(v_toContext_29_);
lean_dec_ref(v_ctx_28_);
v___x_30_ = lean_apply_1(v_x_27_, v_toContext_29_);
v___x_31_ = lean_apply_2(v_inst_25_, lean_box(0), v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLakeMBuildTOfPure___redArg(lean_object* v_inst_32_){
_start:
{
lean_object* v___f_33_; 
v___f_33_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_33_, 0, v_inst_32_);
return v___f_33_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLakeMBuildTOfPure(lean_object* v_m_34_, lean_object* v_inst_35_){
_start:
{
lean_object* v___f_36_; 
v___f_36_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_36_, 0, v_inst_35_);
return v___f_36_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildContext___redArg(lean_object* v_inst_37_){
_start:
{
lean_inc(v_inst_37_);
return v_inst_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildContext___redArg___boxed(lean_object* v_inst_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lake_getBuildContext___redArg(v_inst_38_);
lean_dec(v_inst_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildContext(lean_object* v_m_40_, lean_object* v_inst_41_){
_start:
{
lean_inc(v_inst_41_);
return v_inst_41_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildContext___boxed(lean_object* v_m_42_, lean_object* v_inst_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lake_getBuildContext(v_m_42_, v_inst_43_);
lean_dec(v_inst_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanTrace___redArg___lam__0(lean_object* v_x_45_){
_start:
{
lean_object* v_leanTrace_46_; 
v_leanTrace_46_ = lean_ctor_get(v_x_45_, 2);
lean_inc_ref(v_leanTrace_46_);
return v_leanTrace_46_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanTrace___redArg___lam__0___boxed(lean_object* v_x_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lake_getLeanTrace___redArg___lam__0(v_x_47_);
lean_dec_ref(v_x_47_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanTrace___redArg(lean_object* v_inst_50_, lean_object* v_inst_51_){
_start:
{
lean_object* v_map_52_; lean_object* v___f_53_; lean_object* v___x_54_; 
v_map_52_ = lean_ctor_get(v_inst_50_, 0);
lean_inc(v_map_52_);
lean_dec_ref(v_inst_50_);
v___f_53_ = ((lean_object*)(l_Lake_getLeanTrace___redArg___closed__0));
v___x_54_ = lean_apply_4(v_map_52_, lean_box(0), lean_box(0), v___f_53_, v_inst_51_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanTrace(lean_object* v_m_55_, lean_object* v_inst_56_, lean_object* v_inst_57_){
_start:
{
lean_object* v_map_58_; lean_object* v___f_59_; lean_object* v___x_60_; 
v_map_58_ = lean_ctor_get(v_inst_56_, 0);
lean_inc(v_map_58_);
lean_dec_ref(v_inst_56_);
v___f_59_ = ((lean_object*)(l_Lake_getLeanTrace___redArg___closed__0));
v___x_60_ = lean_apply_4(v_map_58_, lean_box(0), lean_box(0), v___f_59_, v_inst_57_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildConfig___redArg___lam__0(lean_object* v_x_61_){
_start:
{
lean_object* v_toBuildConfig_62_; 
v_toBuildConfig_62_ = lean_ctor_get(v_x_61_, 0);
lean_inc_ref(v_toBuildConfig_62_);
return v_toBuildConfig_62_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildConfig___redArg___lam__0___boxed(lean_object* v_x_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lake_getBuildConfig___redArg___lam__0(v_x_63_);
lean_dec_ref(v_x_63_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildConfig___redArg(lean_object* v_inst_66_, lean_object* v_inst_67_){
_start:
{
lean_object* v_map_68_; lean_object* v___f_69_; lean_object* v___x_70_; 
v_map_68_ = lean_ctor_get(v_inst_66_, 0);
lean_inc(v_map_68_);
lean_dec_ref(v_inst_66_);
v___f_69_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_70_ = lean_apply_4(v_map_68_, lean_box(0), lean_box(0), v___f_69_, v_inst_67_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildConfig(lean_object* v_m_71_, lean_object* v_inst_72_, lean_object* v_inst_73_){
_start:
{
lean_object* v_map_74_; lean_object* v___f_75_; lean_object* v___x_76_; 
v_map_74_ = lean_ctor_get(v_inst_72_, 0);
lean_inc(v_map_74_);
lean_dec_ref(v_inst_72_);
v___f_75_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_76_ = lean_apply_4(v_map_74_, lean_box(0), lean_box(0), v___f_75_, v_inst_73_);
return v___x_76_;
}
}
LEAN_EXPORT uint8_t l_Lake_getIsOldMode___redArg___lam__0(lean_object* v_x_77_){
_start:
{
uint8_t v_oldMode_78_; 
v_oldMode_78_ = lean_ctor_get_uint8(v_x_77_, sizeof(void*)*5);
return v_oldMode_78_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsOldMode___redArg___lam__0___boxed(lean_object* v_x_79_){
_start:
{
uint8_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = l_Lake_getIsOldMode___redArg___lam__0(v_x_79_);
lean_dec_ref(v_x_79_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsOldMode___redArg(lean_object* v_inst_83_, lean_object* v_inst_84_){
_start:
{
lean_object* v_map_85_; lean_object* v___f_86_; lean_object* v___f_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v_map_85_ = lean_ctor_get(v_inst_83_, 0);
lean_inc_n(v_map_85_, 2);
lean_dec_ref(v_inst_83_);
v___f_86_ = ((lean_object*)(l_Lake_getIsOldMode___redArg___closed__0));
v___f_87_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_88_ = lean_apply_4(v_map_85_, lean_box(0), lean_box(0), v___f_87_, v_inst_84_);
v___x_89_ = lean_apply_4(v_map_85_, lean_box(0), lean_box(0), v___f_86_, v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsOldMode(lean_object* v_m_90_, lean_object* v_inst_91_, lean_object* v_inst_92_){
_start:
{
lean_object* v_map_93_; lean_object* v___f_94_; lean_object* v___f_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v_map_93_ = lean_ctor_get(v_inst_91_, 0);
lean_inc_n(v_map_93_, 2);
lean_dec_ref(v_inst_91_);
v___f_94_ = ((lean_object*)(l_Lake_getIsOldMode___redArg___closed__0));
v___f_95_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_96_ = lean_apply_4(v_map_93_, lean_box(0), lean_box(0), v___f_95_, v_inst_92_);
v___x_97_ = lean_apply_4(v_map_93_, lean_box(0), lean_box(0), v___f_94_, v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT uint8_t l_Lake_getTrustHash___redArg___lam__0(lean_object* v_x_98_){
_start:
{
uint8_t v_trustHash_99_; 
v_trustHash_99_ = lean_ctor_get_uint8(v_x_98_, sizeof(void*)*5 + 1);
return v_trustHash_99_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrustHash___redArg___lam__0___boxed(lean_object* v_x_100_){
_start:
{
uint8_t v_res_101_; lean_object* v_r_102_; 
v_res_101_ = l_Lake_getTrustHash___redArg___lam__0(v_x_100_);
lean_dec_ref(v_x_100_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrustHash___redArg(lean_object* v_inst_104_, lean_object* v_inst_105_){
_start:
{
lean_object* v_map_106_; lean_object* v___f_107_; lean_object* v___f_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v_map_106_ = lean_ctor_get(v_inst_104_, 0);
lean_inc_n(v_map_106_, 2);
lean_dec_ref(v_inst_104_);
v___f_107_ = ((lean_object*)(l_Lake_getTrustHash___redArg___closed__0));
v___f_108_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_109_ = lean_apply_4(v_map_106_, lean_box(0), lean_box(0), v___f_108_, v_inst_105_);
v___x_110_ = lean_apply_4(v_map_106_, lean_box(0), lean_box(0), v___f_107_, v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrustHash(lean_object* v_m_111_, lean_object* v_inst_112_, lean_object* v_inst_113_){
_start:
{
lean_object* v_map_114_; lean_object* v___f_115_; lean_object* v___f_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v_map_114_ = lean_ctor_get(v_inst_112_, 0);
lean_inc_n(v_map_114_, 2);
lean_dec_ref(v_inst_112_);
v___f_115_ = ((lean_object*)(l_Lake_getTrustHash___redArg___closed__0));
v___f_116_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_117_ = lean_apply_4(v_map_114_, lean_box(0), lean_box(0), v___f_116_, v_inst_113_);
v___x_118_ = lean_apply_4(v_map_114_, lean_box(0), lean_box(0), v___f_115_, v___x_117_);
return v___x_118_;
}
}
LEAN_EXPORT uint8_t l_Lake_getNoBuild___redArg___lam__0(lean_object* v_x_119_){
_start:
{
uint8_t v_noBuild_120_; 
v_noBuild_120_ = lean_ctor_get_uint8(v_x_119_, sizeof(void*)*5 + 2);
return v_noBuild_120_;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoBuild___redArg___lam__0___boxed(lean_object* v_x_121_){
_start:
{
uint8_t v_res_122_; lean_object* v_r_123_; 
v_res_122_ = l_Lake_getNoBuild___redArg___lam__0(v_x_121_);
lean_dec_ref(v_x_121_);
v_r_123_ = lean_box(v_res_122_);
return v_r_123_;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoBuild___redArg(lean_object* v_inst_125_, lean_object* v_inst_126_){
_start:
{
lean_object* v_map_127_; lean_object* v___f_128_; lean_object* v___f_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v_map_127_ = lean_ctor_get(v_inst_125_, 0);
lean_inc_n(v_map_127_, 2);
lean_dec_ref(v_inst_125_);
v___f_128_ = ((lean_object*)(l_Lake_getNoBuild___redArg___closed__0));
v___f_129_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_130_ = lean_apply_4(v_map_127_, lean_box(0), lean_box(0), v___f_129_, v_inst_126_);
v___x_131_ = lean_apply_4(v_map_127_, lean_box(0), lean_box(0), v___f_128_, v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoBuild(lean_object* v_m_132_, lean_object* v_inst_133_, lean_object* v_inst_134_){
_start:
{
lean_object* v_map_135_; lean_object* v___f_136_; lean_object* v___f_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v_map_135_ = lean_ctor_get(v_inst_133_, 0);
lean_inc_n(v_map_135_, 2);
lean_dec_ref(v_inst_133_);
v___f_136_ = ((lean_object*)(l_Lake_getNoBuild___redArg___closed__0));
v___f_137_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_138_ = lean_apply_4(v_map_135_, lean_box(0), lean_box(0), v___f_137_, v_inst_134_);
v___x_139_ = lean_apply_4(v_map_135_, lean_box(0), lean_box(0), v___f_136_, v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT uint8_t l_Lake_getVerbosity___redArg___lam__0(lean_object* v_x_140_){
_start:
{
uint8_t v_verbosity_141_; 
v_verbosity_141_ = lean_ctor_get_uint8(v_x_140_, sizeof(void*)*5 + 4);
return v_verbosity_141_;
}
}
LEAN_EXPORT lean_object* l_Lake_getVerbosity___redArg___lam__0___boxed(lean_object* v_x_142_){
_start:
{
uint8_t v_res_143_; lean_object* v_r_144_; 
v_res_143_ = l_Lake_getVerbosity___redArg___lam__0(v_x_142_);
lean_dec_ref(v_x_142_);
v_r_144_ = lean_box(v_res_143_);
return v_r_144_;
}
}
LEAN_EXPORT lean_object* l_Lake_getVerbosity___redArg(lean_object* v_inst_146_, lean_object* v_inst_147_){
_start:
{
lean_object* v_map_148_; lean_object* v___f_149_; lean_object* v___f_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_map_148_ = lean_ctor_get(v_inst_146_, 0);
lean_inc_n(v_map_148_, 2);
lean_dec_ref(v_inst_146_);
v___f_149_ = ((lean_object*)(l_Lake_getVerbosity___redArg___closed__0));
v___f_150_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_151_ = lean_apply_4(v_map_148_, lean_box(0), lean_box(0), v___f_150_, v_inst_147_);
v___x_152_ = lean_apply_4(v_map_148_, lean_box(0), lean_box(0), v___f_149_, v___x_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lake_getVerbosity(lean_object* v_m_153_, lean_object* v_inst_154_, lean_object* v_inst_155_){
_start:
{
lean_object* v_map_156_; lean_object* v___f_157_; lean_object* v___f_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v_map_156_ = lean_ctor_get(v_inst_154_, 0);
lean_inc_n(v_map_156_, 2);
lean_dec_ref(v_inst_154_);
v___f_157_ = ((lean_object*)(l_Lake_getVerbosity___redArg___closed__0));
v___f_158_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_159_ = lean_apply_4(v_map_156_, lean_box(0), lean_box(0), v___f_158_, v_inst_155_);
v___x_160_ = lean_apply_4(v_map_156_, lean_box(0), lean_box(0), v___f_157_, v___x_159_);
return v___x_160_;
}
}
LEAN_EXPORT uint8_t l_Lake_getIsVerbose___redArg___lam__0(uint8_t v_x_161_){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_162_ = lean_box(v_x_161_);
v___x_163_ = lean_obj_tag_nat(v___x_162_);
lean_dec(v___x_162_);
v___x_164_ = lean_unsigned_to_nat(2u);
v___x_165_ = lean_nat_dec_eq(v___x_163_, v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsVerbose___redArg___lam__0___boxed(lean_object* v_x_166_){
_start:
{
uint8_t v_x_67__boxed_167_; uint8_t v_res_168_; lean_object* v_r_169_; 
v_x_67__boxed_167_ = lean_unbox(v_x_166_);
v_res_168_ = l_Lake_getIsVerbose___redArg___lam__0(v_x_67__boxed_167_);
v_r_169_ = lean_box(v_res_168_);
return v_r_169_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsVerbose___redArg(lean_object* v_inst_171_, lean_object* v_inst_172_){
_start:
{
lean_object* v_map_173_; lean_object* v___f_174_; lean_object* v___f_175_; lean_object* v___f_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_map_173_ = lean_ctor_get(v_inst_171_, 0);
lean_inc_n(v_map_173_, 3);
lean_dec_ref(v_inst_171_);
v___f_174_ = ((lean_object*)(l_Lake_getIsVerbose___redArg___closed__0));
v___f_175_ = ((lean_object*)(l_Lake_getVerbosity___redArg___closed__0));
v___f_176_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_177_ = lean_apply_4(v_map_173_, lean_box(0), lean_box(0), v___f_176_, v_inst_172_);
v___x_178_ = lean_apply_4(v_map_173_, lean_box(0), lean_box(0), v___f_175_, v___x_177_);
v___x_179_ = lean_apply_4(v_map_173_, lean_box(0), lean_box(0), v___f_174_, v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsVerbose(lean_object* v_m_180_, lean_object* v_inst_181_, lean_object* v_inst_182_){
_start:
{
lean_object* v_map_183_; lean_object* v___f_184_; lean_object* v___f_185_; lean_object* v___f_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v_map_183_ = lean_ctor_get(v_inst_181_, 0);
lean_inc_n(v_map_183_, 3);
lean_dec_ref(v_inst_181_);
v___f_184_ = ((lean_object*)(l_Lake_getIsVerbose___redArg___closed__0));
v___f_185_ = ((lean_object*)(l_Lake_getVerbosity___redArg___closed__0));
v___f_186_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_187_ = lean_apply_4(v_map_183_, lean_box(0), lean_box(0), v___f_186_, v_inst_182_);
v___x_188_ = lean_apply_4(v_map_183_, lean_box(0), lean_box(0), v___f_185_, v___x_187_);
v___x_189_ = lean_apply_4(v_map_183_, lean_box(0), lean_box(0), v___f_184_, v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT uint8_t l_Lake_getIsQuiet___redArg___lam__0(uint8_t v_x_190_){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_191_ = lean_box(v_x_190_);
v___x_192_ = lean_obj_tag_nat(v___x_191_);
lean_dec(v___x_191_);
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = lean_nat_dec_eq(v___x_192_, v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsQuiet___redArg___lam__0___boxed(lean_object* v_x_195_){
_start:
{
uint8_t v_x_67__boxed_196_; uint8_t v_res_197_; lean_object* v_r_198_; 
v_x_67__boxed_196_ = lean_unbox(v_x_195_);
v_res_197_ = l_Lake_getIsQuiet___redArg___lam__0(v_x_67__boxed_196_);
v_r_198_ = lean_box(v_res_197_);
return v_r_198_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsQuiet___redArg(lean_object* v_inst_200_, lean_object* v_inst_201_){
_start:
{
lean_object* v_map_202_; lean_object* v___f_203_; lean_object* v___f_204_; lean_object* v___f_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v_map_202_ = lean_ctor_get(v_inst_200_, 0);
lean_inc_n(v_map_202_, 3);
lean_dec_ref(v_inst_200_);
v___f_203_ = ((lean_object*)(l_Lake_getIsQuiet___redArg___closed__0));
v___f_204_ = ((lean_object*)(l_Lake_getVerbosity___redArg___closed__0));
v___f_205_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_206_ = lean_apply_4(v_map_202_, lean_box(0), lean_box(0), v___f_205_, v_inst_201_);
v___x_207_ = lean_apply_4(v_map_202_, lean_box(0), lean_box(0), v___f_204_, v___x_206_);
v___x_208_ = lean_apply_4(v_map_202_, lean_box(0), lean_box(0), v___f_203_, v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsQuiet(lean_object* v_m_209_, lean_object* v_inst_210_, lean_object* v_inst_211_){
_start:
{
lean_object* v_map_212_; lean_object* v___f_213_; lean_object* v___f_214_; lean_object* v___f_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v_map_212_ = lean_ctor_get(v_inst_210_, 0);
lean_inc_n(v_map_212_, 3);
lean_dec_ref(v_inst_210_);
v___f_213_ = ((lean_object*)(l_Lake_getIsQuiet___redArg___closed__0));
v___f_214_ = ((lean_object*)(l_Lake_getVerbosity___redArg___closed__0));
v___f_215_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_216_ = lean_apply_4(v_map_212_, lean_box(0), lean_box(0), v___f_215_, v_inst_211_);
v___x_217_ = lean_apply_4(v_map_212_, lean_box(0), lean_box(0), v___f_214_, v___x_216_);
v___x_218_ = lean_apply_4(v_map_212_, lean_box(0), lean_box(0), v___f_213_, v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanOptOverrides___redArg___lam__0(lean_object* v_x_219_){
_start:
{
lean_object* v_leanOptOverrides_220_; 
v_leanOptOverrides_220_ = lean_ctor_get(v_x_219_, 3);
lean_inc(v_leanOptOverrides_220_);
return v_leanOptOverrides_220_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanOptOverrides___redArg___lam__0___boxed(lean_object* v_x_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lake_getLeanOptOverrides___redArg___lam__0(v_x_221_);
lean_dec_ref(v_x_221_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanOptOverrides___redArg(lean_object* v_inst_224_, lean_object* v_inst_225_){
_start:
{
lean_object* v_map_226_; lean_object* v___f_227_; lean_object* v___f_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v_map_226_ = lean_ctor_get(v_inst_224_, 0);
lean_inc_n(v_map_226_, 2);
lean_dec_ref(v_inst_224_);
v___f_227_ = ((lean_object*)(l_Lake_getLeanOptOverrides___redArg___closed__0));
v___f_228_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_229_ = lean_apply_4(v_map_226_, lean_box(0), lean_box(0), v___f_228_, v_inst_225_);
v___x_230_ = lean_apply_4(v_map_226_, lean_box(0), lean_box(0), v___f_227_, v___x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanOptOverrides(lean_object* v_m_231_, lean_object* v_inst_232_, lean_object* v_inst_233_){
_start:
{
lean_object* v_map_234_; lean_object* v___f_235_; lean_object* v___f_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v_map_234_ = lean_ctor_get(v_inst_232_, 0);
lean_inc_n(v_map_234_, 2);
lean_dec_ref(v_inst_232_);
v___f_235_ = ((lean_object*)(l_Lake_getLeanOptOverrides___redArg___closed__0));
v___f_236_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_237_ = lean_apply_4(v_map_234_, lean_box(0), lean_box(0), v___f_236_, v_inst_233_);
v___x_238_ = lean_apply_4(v_map_234_, lean_box(0), lean_box(0), v___f_235_, v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lake_getMacOSXDeploymentTarget_x3f___redArg___lam__0(lean_object* v_x_239_){
_start:
{
lean_object* v_macosxDeploymentTarget_x3f_240_; 
v_macosxDeploymentTarget_x3f_240_ = lean_ctor_get(v_x_239_, 4);
lean_inc(v_macosxDeploymentTarget_x3f_240_);
return v_macosxDeploymentTarget_x3f_240_;
}
}
LEAN_EXPORT lean_object* l_Lake_getMacOSXDeploymentTarget_x3f___redArg___lam__0___boxed(lean_object* v_x_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lake_getMacOSXDeploymentTarget_x3f___redArg___lam__0(v_x_241_);
lean_dec_ref(v_x_241_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lake_getMacOSXDeploymentTarget_x3f___redArg(lean_object* v_inst_244_, lean_object* v_inst_245_){
_start:
{
lean_object* v_map_246_; lean_object* v___f_247_; lean_object* v___f_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v_map_246_ = lean_ctor_get(v_inst_244_, 0);
lean_inc_n(v_map_246_, 2);
lean_dec_ref(v_inst_244_);
v___f_247_ = ((lean_object*)(l_Lake_getMacOSXDeploymentTarget_x3f___redArg___closed__0));
v___f_248_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_249_ = lean_apply_4(v_map_246_, lean_box(0), lean_box(0), v___f_248_, v_inst_245_);
v___x_250_ = lean_apply_4(v_map_246_, lean_box(0), lean_box(0), v___f_247_, v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lake_getMacOSXDeploymentTarget_x3f(lean_object* v_m_251_, lean_object* v_inst_252_, lean_object* v_inst_253_){
_start:
{
lean_object* v_map_254_; lean_object* v___f_255_; lean_object* v___f_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_map_254_ = lean_ctor_get(v_inst_252_, 0);
lean_inc_n(v_map_254_, 2);
lean_dec_ref(v_inst_252_);
v___f_255_ = ((lean_object*)(l_Lake_getMacOSXDeploymentTarget_x3f___redArg___closed__0));
v___f_256_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_257_ = lean_apply_4(v_map_254_, lean_box(0), lean_box(0), v___f_256_, v_inst_253_);
v___x_258_ = lean_apply_4(v_map_254_, lean_box(0), lean_box(0), v___f_255_, v___x_257_);
return v___x_258_;
}
}
lean_object* runtime_initialize_Lake_Config_Cache(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Context(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Job_Basic(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Context(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Config_Cache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Job_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_Context(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_Cache(uint8_t builtin);
lean_object* initialize_Lake_Config_Context(uint8_t builtin);
lean_object* initialize_Lake_Build_Job_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Context(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Cache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_Context(builtin);
}
#ifdef __cplusplus
}
#endif
