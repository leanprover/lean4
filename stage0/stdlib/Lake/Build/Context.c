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
uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
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
LEAN_EXPORT uint8_t l_Lake_BuildConfig_showProgress(lean_object* v_cfg_1_){
_start:
{
uint8_t v_noBuild_2_; uint8_t v_verbosity_3_; 
v_noBuild_2_ = lean_ctor_get_uint8(v_cfg_1_, sizeof(void*)*3 + 2);
v_verbosity_3_ = lean_ctor_get_uint8(v_cfg_1_, sizeof(void*)*3 + 3);
if (v_noBuild_2_ == 0)
{
goto v___jp_4_;
}
else
{
uint8_t v___x_9_; uint8_t v___x_10_; 
v___x_9_ = 2;
v___x_10_ = l_Lake_instDecidableEqVerbosity(v_verbosity_3_, v___x_9_);
if (v___x_10_ == 0)
{
goto v___jp_4_;
}
else
{
return v___x_10_;
}
}
v___jp_4_:
{
uint8_t v___x_5_; uint8_t v___x_6_; 
v___x_5_ = 0;
v___x_6_ = l_Lake_instDecidableEqVerbosity(v_verbosity_3_, v___x_5_);
if (v___x_6_ == 0)
{
uint8_t v___x_7_; 
v___x_7_ = 1;
return v___x_7_;
}
else
{
uint8_t v___x_8_; 
v___x_8_ = 0;
return v___x_8_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildConfig_showProgress___boxed(lean_object* v_cfg_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_Lake_BuildConfig_showProgress(v_cfg_11_);
lean_dec_ref(v_cfg_11_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkJobQueue(){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = ((lean_object*)(l_Lake_mkJobQueue___closed__0));
v___x_18_ = lean_st_mk_ref(v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkJobQueue___boxed(lean_object* v_a_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lake_mkJobQueue();
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0(lean_object* v_inst_21_, lean_object* v_00_u03b1_22_, lean_object* v_x_23_, lean_object* v_ctx_24_){
_start:
{
lean_object* v_toContext_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v_toContext_25_ = lean_ctor_get(v_ctx_24_, 1);
lean_inc(v_toContext_25_);
lean_dec_ref(v_ctx_24_);
v___x_26_ = lean_apply_1(v_x_23_, v_toContext_25_);
v___x_27_ = lean_apply_2(v_inst_21_, lean_box(0), v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLakeMBuildTOfPure___redArg(lean_object* v_inst_28_){
_start:
{
lean_object* v___f_29_; 
v___f_29_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_29_, 0, v_inst_28_);
return v___f_29_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLakeMBuildTOfPure(lean_object* v_m_30_, lean_object* v_inst_31_){
_start:
{
lean_object* v___f_32_; 
v___f_32_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_32_, 0, v_inst_31_);
return v___f_32_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildContext___redArg(lean_object* v_inst_33_){
_start:
{
lean_inc(v_inst_33_);
return v_inst_33_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildContext___redArg___boxed(lean_object* v_inst_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lake_getBuildContext___redArg(v_inst_34_);
lean_dec(v_inst_34_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildContext(lean_object* v_m_36_, lean_object* v_inst_37_){
_start:
{
lean_inc(v_inst_37_);
return v_inst_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildContext___boxed(lean_object* v_m_38_, lean_object* v_inst_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lake_getBuildContext(v_m_38_, v_inst_39_);
lean_dec(v_inst_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanTrace___redArg___lam__0(lean_object* v_x_41_){
_start:
{
lean_object* v_leanTrace_42_; 
v_leanTrace_42_ = lean_ctor_get(v_x_41_, 2);
lean_inc_ref(v_leanTrace_42_);
return v_leanTrace_42_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanTrace___redArg___lam__0___boxed(lean_object* v_x_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lake_getLeanTrace___redArg___lam__0(v_x_43_);
lean_dec_ref(v_x_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanTrace___redArg(lean_object* v_inst_46_, lean_object* v_inst_47_){
_start:
{
lean_object* v_map_48_; lean_object* v___f_49_; lean_object* v___x_50_; 
v_map_48_ = lean_ctor_get(v_inst_46_, 0);
lean_inc(v_map_48_);
lean_dec_ref(v_inst_46_);
v___f_49_ = ((lean_object*)(l_Lake_getLeanTrace___redArg___closed__0));
v___x_50_ = lean_apply_4(v_map_48_, lean_box(0), lean_box(0), v___f_49_, v_inst_47_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanTrace(lean_object* v_m_51_, lean_object* v_inst_52_, lean_object* v_inst_53_){
_start:
{
lean_object* v_map_54_; lean_object* v___f_55_; lean_object* v___x_56_; 
v_map_54_ = lean_ctor_get(v_inst_52_, 0);
lean_inc(v_map_54_);
lean_dec_ref(v_inst_52_);
v___f_55_ = ((lean_object*)(l_Lake_getLeanTrace___redArg___closed__0));
v___x_56_ = lean_apply_4(v_map_54_, lean_box(0), lean_box(0), v___f_55_, v_inst_53_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildConfig___redArg___lam__0(lean_object* v_x_57_){
_start:
{
lean_object* v_toBuildConfig_58_; 
v_toBuildConfig_58_ = lean_ctor_get(v_x_57_, 0);
lean_inc_ref(v_toBuildConfig_58_);
return v_toBuildConfig_58_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildConfig___redArg___lam__0___boxed(lean_object* v_x_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lake_getBuildConfig___redArg___lam__0(v_x_59_);
lean_dec_ref(v_x_59_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildConfig___redArg(lean_object* v_inst_62_, lean_object* v_inst_63_){
_start:
{
lean_object* v_map_64_; lean_object* v___f_65_; lean_object* v___x_66_; 
v_map_64_ = lean_ctor_get(v_inst_62_, 0);
lean_inc(v_map_64_);
lean_dec_ref(v_inst_62_);
v___f_65_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_66_ = lean_apply_4(v_map_64_, lean_box(0), lean_box(0), v___f_65_, v_inst_63_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildConfig(lean_object* v_m_67_, lean_object* v_inst_68_, lean_object* v_inst_69_){
_start:
{
lean_object* v_map_70_; lean_object* v___f_71_; lean_object* v___x_72_; 
v_map_70_ = lean_ctor_get(v_inst_68_, 0);
lean_inc(v_map_70_);
lean_dec_ref(v_inst_68_);
v___f_71_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_72_ = lean_apply_4(v_map_70_, lean_box(0), lean_box(0), v___f_71_, v_inst_69_);
return v___x_72_;
}
}
LEAN_EXPORT uint8_t l_Lake_getIsOldMode___redArg___lam__0(lean_object* v_x_73_){
_start:
{
uint8_t v_oldMode_74_; 
v_oldMode_74_ = lean_ctor_get_uint8(v_x_73_, sizeof(void*)*3);
return v_oldMode_74_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsOldMode___redArg___lam__0___boxed(lean_object* v_x_75_){
_start:
{
uint8_t v_res_76_; lean_object* v_r_77_; 
v_res_76_ = l_Lake_getIsOldMode___redArg___lam__0(v_x_75_);
lean_dec_ref(v_x_75_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsOldMode___redArg(lean_object* v_inst_79_, lean_object* v_inst_80_){
_start:
{
lean_object* v_map_81_; lean_object* v___f_82_; lean_object* v___f_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v_map_81_ = lean_ctor_get(v_inst_79_, 0);
lean_inc_n(v_map_81_, 2);
lean_dec_ref(v_inst_79_);
v___f_82_ = ((lean_object*)(l_Lake_getIsOldMode___redArg___closed__0));
v___f_83_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_84_ = lean_apply_4(v_map_81_, lean_box(0), lean_box(0), v___f_83_, v_inst_80_);
v___x_85_ = lean_apply_4(v_map_81_, lean_box(0), lean_box(0), v___f_82_, v___x_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsOldMode(lean_object* v_m_86_, lean_object* v_inst_87_, lean_object* v_inst_88_){
_start:
{
lean_object* v_map_89_; lean_object* v___f_90_; lean_object* v___f_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v_map_89_ = lean_ctor_get(v_inst_87_, 0);
lean_inc_n(v_map_89_, 2);
lean_dec_ref(v_inst_87_);
v___f_90_ = ((lean_object*)(l_Lake_getIsOldMode___redArg___closed__0));
v___f_91_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_92_ = lean_apply_4(v_map_89_, lean_box(0), lean_box(0), v___f_91_, v_inst_88_);
v___x_93_ = lean_apply_4(v_map_89_, lean_box(0), lean_box(0), v___f_90_, v___x_92_);
return v___x_93_;
}
}
LEAN_EXPORT uint8_t l_Lake_getTrustHash___redArg___lam__0(lean_object* v_x_94_){
_start:
{
uint8_t v_trustHash_95_; 
v_trustHash_95_ = lean_ctor_get_uint8(v_x_94_, sizeof(void*)*3 + 1);
return v_trustHash_95_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrustHash___redArg___lam__0___boxed(lean_object* v_x_96_){
_start:
{
uint8_t v_res_97_; lean_object* v_r_98_; 
v_res_97_ = l_Lake_getTrustHash___redArg___lam__0(v_x_96_);
lean_dec_ref(v_x_96_);
v_r_98_ = lean_box(v_res_97_);
return v_r_98_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrustHash___redArg(lean_object* v_inst_100_, lean_object* v_inst_101_){
_start:
{
lean_object* v_map_102_; lean_object* v___f_103_; lean_object* v___f_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v_map_102_ = lean_ctor_get(v_inst_100_, 0);
lean_inc_n(v_map_102_, 2);
lean_dec_ref(v_inst_100_);
v___f_103_ = ((lean_object*)(l_Lake_getTrustHash___redArg___closed__0));
v___f_104_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_105_ = lean_apply_4(v_map_102_, lean_box(0), lean_box(0), v___f_104_, v_inst_101_);
v___x_106_ = lean_apply_4(v_map_102_, lean_box(0), lean_box(0), v___f_103_, v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrustHash(lean_object* v_m_107_, lean_object* v_inst_108_, lean_object* v_inst_109_){
_start:
{
lean_object* v_map_110_; lean_object* v___f_111_; lean_object* v___f_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v_map_110_ = lean_ctor_get(v_inst_108_, 0);
lean_inc_n(v_map_110_, 2);
lean_dec_ref(v_inst_108_);
v___f_111_ = ((lean_object*)(l_Lake_getTrustHash___redArg___closed__0));
v___f_112_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_113_ = lean_apply_4(v_map_110_, lean_box(0), lean_box(0), v___f_112_, v_inst_109_);
v___x_114_ = lean_apply_4(v_map_110_, lean_box(0), lean_box(0), v___f_111_, v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT uint8_t l_Lake_getNoBuild___redArg___lam__0(lean_object* v_x_115_){
_start:
{
uint8_t v_noBuild_116_; 
v_noBuild_116_ = lean_ctor_get_uint8(v_x_115_, sizeof(void*)*3 + 2);
return v_noBuild_116_;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoBuild___redArg___lam__0___boxed(lean_object* v_x_117_){
_start:
{
uint8_t v_res_118_; lean_object* v_r_119_; 
v_res_118_ = l_Lake_getNoBuild___redArg___lam__0(v_x_117_);
lean_dec_ref(v_x_117_);
v_r_119_ = lean_box(v_res_118_);
return v_r_119_;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoBuild___redArg(lean_object* v_inst_121_, lean_object* v_inst_122_){
_start:
{
lean_object* v_map_123_; lean_object* v___f_124_; lean_object* v___f_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v_map_123_ = lean_ctor_get(v_inst_121_, 0);
lean_inc_n(v_map_123_, 2);
lean_dec_ref(v_inst_121_);
v___f_124_ = ((lean_object*)(l_Lake_getNoBuild___redArg___closed__0));
v___f_125_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_126_ = lean_apply_4(v_map_123_, lean_box(0), lean_box(0), v___f_125_, v_inst_122_);
v___x_127_ = lean_apply_4(v_map_123_, lean_box(0), lean_box(0), v___f_124_, v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoBuild(lean_object* v_m_128_, lean_object* v_inst_129_, lean_object* v_inst_130_){
_start:
{
lean_object* v_map_131_; lean_object* v___f_132_; lean_object* v___f_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v_map_131_ = lean_ctor_get(v_inst_129_, 0);
lean_inc_n(v_map_131_, 2);
lean_dec_ref(v_inst_129_);
v___f_132_ = ((lean_object*)(l_Lake_getNoBuild___redArg___closed__0));
v___f_133_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_134_ = lean_apply_4(v_map_131_, lean_box(0), lean_box(0), v___f_133_, v_inst_130_);
v___x_135_ = lean_apply_4(v_map_131_, lean_box(0), lean_box(0), v___f_132_, v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT uint8_t l_Lake_getVerbosity___redArg___lam__0(lean_object* v_x_136_){
_start:
{
uint8_t v_verbosity_137_; 
v_verbosity_137_ = lean_ctor_get_uint8(v_x_136_, sizeof(void*)*3 + 3);
return v_verbosity_137_;
}
}
LEAN_EXPORT lean_object* l_Lake_getVerbosity___redArg___lam__0___boxed(lean_object* v_x_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l_Lake_getVerbosity___redArg___lam__0(v_x_138_);
lean_dec_ref(v_x_138_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT lean_object* l_Lake_getVerbosity___redArg(lean_object* v_inst_142_, lean_object* v_inst_143_){
_start:
{
lean_object* v_map_144_; lean_object* v___f_145_; lean_object* v___f_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v_map_144_ = lean_ctor_get(v_inst_142_, 0);
lean_inc_n(v_map_144_, 2);
lean_dec_ref(v_inst_142_);
v___f_145_ = ((lean_object*)(l_Lake_getVerbosity___redArg___closed__0));
v___f_146_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_147_ = lean_apply_4(v_map_144_, lean_box(0), lean_box(0), v___f_146_, v_inst_143_);
v___x_148_ = lean_apply_4(v_map_144_, lean_box(0), lean_box(0), v___f_145_, v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lake_getVerbosity(lean_object* v_m_149_, lean_object* v_inst_150_, lean_object* v_inst_151_){
_start:
{
lean_object* v_map_152_; lean_object* v___f_153_; lean_object* v___f_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v_map_152_ = lean_ctor_get(v_inst_150_, 0);
lean_inc_n(v_map_152_, 2);
lean_dec_ref(v_inst_150_);
v___f_153_ = ((lean_object*)(l_Lake_getVerbosity___redArg___closed__0));
v___f_154_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_155_ = lean_apply_4(v_map_152_, lean_box(0), lean_box(0), v___f_154_, v_inst_151_);
v___x_156_ = lean_apply_4(v_map_152_, lean_box(0), lean_box(0), v___f_153_, v___x_155_);
return v___x_156_;
}
}
LEAN_EXPORT uint8_t l_Lake_getIsVerbose___redArg___lam__0(uint8_t v_x_157_){
_start:
{
uint8_t v___x_158_; uint8_t v___x_159_; 
v___x_158_ = 2;
v___x_159_ = l_Lake_instDecidableEqVerbosity(v_x_157_, v___x_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsVerbose___redArg___lam__0___boxed(lean_object* v_x_160_){
_start:
{
uint8_t v_x_54__boxed_161_; uint8_t v_res_162_; lean_object* v_r_163_; 
v_x_54__boxed_161_ = lean_unbox(v_x_160_);
v_res_162_ = l_Lake_getIsVerbose___redArg___lam__0(v_x_54__boxed_161_);
v_r_163_ = lean_box(v_res_162_);
return v_r_163_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsVerbose___redArg(lean_object* v_inst_165_, lean_object* v_inst_166_){
_start:
{
lean_object* v_map_167_; lean_object* v___f_168_; lean_object* v___f_169_; lean_object* v___f_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v_map_167_ = lean_ctor_get(v_inst_165_, 0);
lean_inc_n(v_map_167_, 3);
lean_dec_ref(v_inst_165_);
v___f_168_ = ((lean_object*)(l_Lake_getIsVerbose___redArg___closed__0));
v___f_169_ = ((lean_object*)(l_Lake_getVerbosity___redArg___closed__0));
v___f_170_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_171_ = lean_apply_4(v_map_167_, lean_box(0), lean_box(0), v___f_170_, v_inst_166_);
v___x_172_ = lean_apply_4(v_map_167_, lean_box(0), lean_box(0), v___f_169_, v___x_171_);
v___x_173_ = lean_apply_4(v_map_167_, lean_box(0), lean_box(0), v___f_168_, v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsVerbose(lean_object* v_m_174_, lean_object* v_inst_175_, lean_object* v_inst_176_){
_start:
{
lean_object* v_map_177_; lean_object* v___f_178_; lean_object* v___f_179_; lean_object* v___f_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v_map_177_ = lean_ctor_get(v_inst_175_, 0);
lean_inc_n(v_map_177_, 3);
lean_dec_ref(v_inst_175_);
v___f_178_ = ((lean_object*)(l_Lake_getIsVerbose___redArg___closed__0));
v___f_179_ = ((lean_object*)(l_Lake_getVerbosity___redArg___closed__0));
v___f_180_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_181_ = lean_apply_4(v_map_177_, lean_box(0), lean_box(0), v___f_180_, v_inst_176_);
v___x_182_ = lean_apply_4(v_map_177_, lean_box(0), lean_box(0), v___f_179_, v___x_181_);
v___x_183_ = lean_apply_4(v_map_177_, lean_box(0), lean_box(0), v___f_178_, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT uint8_t l_Lake_getIsQuiet___redArg___lam__0(uint8_t v_x_184_){
_start:
{
uint8_t v___x_185_; uint8_t v___x_186_; 
v___x_185_ = 0;
v___x_186_ = l_Lake_instDecidableEqVerbosity(v_x_184_, v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsQuiet___redArg___lam__0___boxed(lean_object* v_x_187_){
_start:
{
uint8_t v_x_54__boxed_188_; uint8_t v_res_189_; lean_object* v_r_190_; 
v_x_54__boxed_188_ = lean_unbox(v_x_187_);
v_res_189_ = l_Lake_getIsQuiet___redArg___lam__0(v_x_54__boxed_188_);
v_r_190_ = lean_box(v_res_189_);
return v_r_190_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsQuiet___redArg(lean_object* v_inst_192_, lean_object* v_inst_193_){
_start:
{
lean_object* v_map_194_; lean_object* v___f_195_; lean_object* v___f_196_; lean_object* v___f_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v_map_194_ = lean_ctor_get(v_inst_192_, 0);
lean_inc_n(v_map_194_, 3);
lean_dec_ref(v_inst_192_);
v___f_195_ = ((lean_object*)(l_Lake_getIsQuiet___redArg___closed__0));
v___f_196_ = ((lean_object*)(l_Lake_getVerbosity___redArg___closed__0));
v___f_197_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_198_ = lean_apply_4(v_map_194_, lean_box(0), lean_box(0), v___f_197_, v_inst_193_);
v___x_199_ = lean_apply_4(v_map_194_, lean_box(0), lean_box(0), v___f_196_, v___x_198_);
v___x_200_ = lean_apply_4(v_map_194_, lean_box(0), lean_box(0), v___f_195_, v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsQuiet(lean_object* v_m_201_, lean_object* v_inst_202_, lean_object* v_inst_203_){
_start:
{
lean_object* v_map_204_; lean_object* v___f_205_; lean_object* v___f_206_; lean_object* v___f_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_map_204_ = lean_ctor_get(v_inst_202_, 0);
lean_inc_n(v_map_204_, 3);
lean_dec_ref(v_inst_202_);
v___f_205_ = ((lean_object*)(l_Lake_getIsQuiet___redArg___closed__0));
v___f_206_ = ((lean_object*)(l_Lake_getVerbosity___redArg___closed__0));
v___f_207_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_208_ = lean_apply_4(v_map_204_, lean_box(0), lean_box(0), v___f_207_, v_inst_203_);
v___x_209_ = lean_apply_4(v_map_204_, lean_box(0), lean_box(0), v___f_206_, v___x_208_);
v___x_210_ = lean_apply_4(v_map_204_, lean_box(0), lean_box(0), v___f_205_, v___x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanOptOverrides___redArg___lam__0(lean_object* v_x_211_){
_start:
{
lean_object* v_leanOptOverrides_212_; 
v_leanOptOverrides_212_ = lean_ctor_get(v_x_211_, 2);
lean_inc(v_leanOptOverrides_212_);
return v_leanOptOverrides_212_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanOptOverrides___redArg___lam__0___boxed(lean_object* v_x_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lake_getLeanOptOverrides___redArg___lam__0(v_x_213_);
lean_dec_ref(v_x_213_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanOptOverrides___redArg(lean_object* v_inst_216_, lean_object* v_inst_217_){
_start:
{
lean_object* v_map_218_; lean_object* v___f_219_; lean_object* v___f_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v_map_218_ = lean_ctor_get(v_inst_216_, 0);
lean_inc_n(v_map_218_, 2);
lean_dec_ref(v_inst_216_);
v___f_219_ = ((lean_object*)(l_Lake_getLeanOptOverrides___redArg___closed__0));
v___f_220_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_221_ = lean_apply_4(v_map_218_, lean_box(0), lean_box(0), v___f_220_, v_inst_217_);
v___x_222_ = lean_apply_4(v_map_218_, lean_box(0), lean_box(0), v___f_219_, v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanOptOverrides(lean_object* v_m_223_, lean_object* v_inst_224_, lean_object* v_inst_225_){
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
lean_object* runtime_initialize_Lake_Config_Cache(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Context(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Job_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Context(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
