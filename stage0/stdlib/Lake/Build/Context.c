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
uint8_t lean_bool_not(uint8_t);
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
uint8_t v___x_8_; uint8_t v___x_9_; 
v___x_8_ = 2;
v___x_9_ = l_Lake_instDecidableEqVerbosity(v_verbosity_3_, v___x_8_);
if (v___x_9_ == 0)
{
goto v___jp_4_;
}
else
{
return v___x_9_;
}
}
v___jp_4_:
{
uint8_t v___x_5_; uint8_t v___x_6_; uint8_t v___x_7_; 
v___x_5_ = 0;
v___x_6_ = l_Lake_instDecidableEqVerbosity(v_verbosity_3_, v___x_5_);
v___x_7_ = lean_bool_not(v___x_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildConfig_showProgress___boxed(lean_object* v_cfg_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Lake_BuildConfig_showProgress(v_cfg_10_);
lean_dec_ref(v_cfg_10_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkJobQueue(){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = ((lean_object*)(l_Lake_mkJobQueue___closed__0));
v___x_17_ = lean_st_mk_ref(v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkJobQueue___boxed(lean_object* v_a_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Lake_mkJobQueue();
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0(lean_object* v_inst_20_, lean_object* v_00_u03b1_21_, lean_object* v_x_22_, lean_object* v_ctx_23_){
_start:
{
lean_object* v_toContext_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v_toContext_24_ = lean_ctor_get(v_ctx_23_, 1);
lean_inc(v_toContext_24_);
lean_dec_ref(v_ctx_23_);
v___x_25_ = lean_apply_1(v_x_22_, v_toContext_24_);
v___x_26_ = lean_apply_2(v_inst_20_, lean_box(0), v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLakeMBuildTOfPure___redArg(lean_object* v_inst_27_){
_start:
{
lean_object* v___f_28_; 
v___f_28_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_28_, 0, v_inst_27_);
return v___f_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLakeMBuildTOfPure(lean_object* v_m_29_, lean_object* v_inst_30_){
_start:
{
lean_object* v___f_31_; 
v___f_31_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_31_, 0, v_inst_30_);
return v___f_31_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildContext___redArg(lean_object* v_inst_32_){
_start:
{
lean_inc(v_inst_32_);
return v_inst_32_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildContext___redArg___boxed(lean_object* v_inst_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lake_getBuildContext___redArg(v_inst_33_);
lean_dec(v_inst_33_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildContext(lean_object* v_m_35_, lean_object* v_inst_36_){
_start:
{
lean_inc(v_inst_36_);
return v_inst_36_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildContext___boxed(lean_object* v_m_37_, lean_object* v_inst_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lake_getBuildContext(v_m_37_, v_inst_38_);
lean_dec(v_inst_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanTrace___redArg___lam__0(lean_object* v_x_40_){
_start:
{
lean_object* v_leanTrace_41_; 
v_leanTrace_41_ = lean_ctor_get(v_x_40_, 2);
lean_inc_ref(v_leanTrace_41_);
return v_leanTrace_41_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanTrace___redArg___lam__0___boxed(lean_object* v_x_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lake_getLeanTrace___redArg___lam__0(v_x_42_);
lean_dec_ref(v_x_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanTrace___redArg(lean_object* v_inst_45_, lean_object* v_inst_46_){
_start:
{
lean_object* v_map_47_; lean_object* v___f_48_; lean_object* v___x_49_; 
v_map_47_ = lean_ctor_get(v_inst_45_, 0);
lean_inc(v_map_47_);
lean_dec_ref(v_inst_45_);
v___f_48_ = ((lean_object*)(l_Lake_getLeanTrace___redArg___closed__0));
v___x_49_ = lean_apply_4(v_map_47_, lean_box(0), lean_box(0), v___f_48_, v_inst_46_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanTrace(lean_object* v_m_50_, lean_object* v_inst_51_, lean_object* v_inst_52_){
_start:
{
lean_object* v_map_53_; lean_object* v___f_54_; lean_object* v___x_55_; 
v_map_53_ = lean_ctor_get(v_inst_51_, 0);
lean_inc(v_map_53_);
lean_dec_ref(v_inst_51_);
v___f_54_ = ((lean_object*)(l_Lake_getLeanTrace___redArg___closed__0));
v___x_55_ = lean_apply_4(v_map_53_, lean_box(0), lean_box(0), v___f_54_, v_inst_52_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildConfig___redArg___lam__0(lean_object* v_x_56_){
_start:
{
lean_object* v_toBuildConfig_57_; 
v_toBuildConfig_57_ = lean_ctor_get(v_x_56_, 0);
lean_inc_ref(v_toBuildConfig_57_);
return v_toBuildConfig_57_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildConfig___redArg___lam__0___boxed(lean_object* v_x_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lake_getBuildConfig___redArg___lam__0(v_x_58_);
lean_dec_ref(v_x_58_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildConfig___redArg(lean_object* v_inst_61_, lean_object* v_inst_62_){
_start:
{
lean_object* v_map_63_; lean_object* v___f_64_; lean_object* v___x_65_; 
v_map_63_ = lean_ctor_get(v_inst_61_, 0);
lean_inc(v_map_63_);
lean_dec_ref(v_inst_61_);
v___f_64_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_65_ = lean_apply_4(v_map_63_, lean_box(0), lean_box(0), v___f_64_, v_inst_62_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildConfig(lean_object* v_m_66_, lean_object* v_inst_67_, lean_object* v_inst_68_){
_start:
{
lean_object* v_map_69_; lean_object* v___f_70_; lean_object* v___x_71_; 
v_map_69_ = lean_ctor_get(v_inst_67_, 0);
lean_inc(v_map_69_);
lean_dec_ref(v_inst_67_);
v___f_70_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_71_ = lean_apply_4(v_map_69_, lean_box(0), lean_box(0), v___f_70_, v_inst_68_);
return v___x_71_;
}
}
LEAN_EXPORT uint8_t l_Lake_getIsOldMode___redArg___lam__0(lean_object* v_x_72_){
_start:
{
uint8_t v_oldMode_73_; 
v_oldMode_73_ = lean_ctor_get_uint8(v_x_72_, sizeof(void*)*3);
return v_oldMode_73_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsOldMode___redArg___lam__0___boxed(lean_object* v_x_74_){
_start:
{
uint8_t v_res_75_; lean_object* v_r_76_; 
v_res_75_ = l_Lake_getIsOldMode___redArg___lam__0(v_x_74_);
lean_dec_ref(v_x_74_);
v_r_76_ = lean_box(v_res_75_);
return v_r_76_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsOldMode___redArg(lean_object* v_inst_78_, lean_object* v_inst_79_){
_start:
{
lean_object* v_map_80_; lean_object* v___f_81_; lean_object* v___f_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v_map_80_ = lean_ctor_get(v_inst_78_, 0);
lean_inc_n(v_map_80_, 2);
lean_dec_ref(v_inst_78_);
v___f_81_ = ((lean_object*)(l_Lake_getIsOldMode___redArg___closed__0));
v___f_82_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_83_ = lean_apply_4(v_map_80_, lean_box(0), lean_box(0), v___f_82_, v_inst_79_);
v___x_84_ = lean_apply_4(v_map_80_, lean_box(0), lean_box(0), v___f_81_, v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsOldMode(lean_object* v_m_85_, lean_object* v_inst_86_, lean_object* v_inst_87_){
_start:
{
lean_object* v_map_88_; lean_object* v___f_89_; lean_object* v___f_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v_map_88_ = lean_ctor_get(v_inst_86_, 0);
lean_inc_n(v_map_88_, 2);
lean_dec_ref(v_inst_86_);
v___f_89_ = ((lean_object*)(l_Lake_getIsOldMode___redArg___closed__0));
v___f_90_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_91_ = lean_apply_4(v_map_88_, lean_box(0), lean_box(0), v___f_90_, v_inst_87_);
v___x_92_ = lean_apply_4(v_map_88_, lean_box(0), lean_box(0), v___f_89_, v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT uint8_t l_Lake_getTrustHash___redArg___lam__0(lean_object* v_x_93_){
_start:
{
uint8_t v_trustHash_94_; 
v_trustHash_94_ = lean_ctor_get_uint8(v_x_93_, sizeof(void*)*3 + 1);
return v_trustHash_94_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrustHash___redArg___lam__0___boxed(lean_object* v_x_95_){
_start:
{
uint8_t v_res_96_; lean_object* v_r_97_; 
v_res_96_ = l_Lake_getTrustHash___redArg___lam__0(v_x_95_);
lean_dec_ref(v_x_95_);
v_r_97_ = lean_box(v_res_96_);
return v_r_97_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrustHash___redArg(lean_object* v_inst_99_, lean_object* v_inst_100_){
_start:
{
lean_object* v_map_101_; lean_object* v___f_102_; lean_object* v___f_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v_map_101_ = lean_ctor_get(v_inst_99_, 0);
lean_inc_n(v_map_101_, 2);
lean_dec_ref(v_inst_99_);
v___f_102_ = ((lean_object*)(l_Lake_getTrustHash___redArg___closed__0));
v___f_103_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_104_ = lean_apply_4(v_map_101_, lean_box(0), lean_box(0), v___f_103_, v_inst_100_);
v___x_105_ = lean_apply_4(v_map_101_, lean_box(0), lean_box(0), v___f_102_, v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrustHash(lean_object* v_m_106_, lean_object* v_inst_107_, lean_object* v_inst_108_){
_start:
{
lean_object* v_map_109_; lean_object* v___f_110_; lean_object* v___f_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v_map_109_ = lean_ctor_get(v_inst_107_, 0);
lean_inc_n(v_map_109_, 2);
lean_dec_ref(v_inst_107_);
v___f_110_ = ((lean_object*)(l_Lake_getTrustHash___redArg___closed__0));
v___f_111_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_112_ = lean_apply_4(v_map_109_, lean_box(0), lean_box(0), v___f_111_, v_inst_108_);
v___x_113_ = lean_apply_4(v_map_109_, lean_box(0), lean_box(0), v___f_110_, v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT uint8_t l_Lake_getNoBuild___redArg___lam__0(lean_object* v_x_114_){
_start:
{
uint8_t v_noBuild_115_; 
v_noBuild_115_ = lean_ctor_get_uint8(v_x_114_, sizeof(void*)*3 + 2);
return v_noBuild_115_;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoBuild___redArg___lam__0___boxed(lean_object* v_x_116_){
_start:
{
uint8_t v_res_117_; lean_object* v_r_118_; 
v_res_117_ = l_Lake_getNoBuild___redArg___lam__0(v_x_116_);
lean_dec_ref(v_x_116_);
v_r_118_ = lean_box(v_res_117_);
return v_r_118_;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoBuild___redArg(lean_object* v_inst_120_, lean_object* v_inst_121_){
_start:
{
lean_object* v_map_122_; lean_object* v___f_123_; lean_object* v___f_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v_map_122_ = lean_ctor_get(v_inst_120_, 0);
lean_inc_n(v_map_122_, 2);
lean_dec_ref(v_inst_120_);
v___f_123_ = ((lean_object*)(l_Lake_getNoBuild___redArg___closed__0));
v___f_124_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_125_ = lean_apply_4(v_map_122_, lean_box(0), lean_box(0), v___f_124_, v_inst_121_);
v___x_126_ = lean_apply_4(v_map_122_, lean_box(0), lean_box(0), v___f_123_, v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoBuild(lean_object* v_m_127_, lean_object* v_inst_128_, lean_object* v_inst_129_){
_start:
{
lean_object* v_map_130_; lean_object* v___f_131_; lean_object* v___f_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v_map_130_ = lean_ctor_get(v_inst_128_, 0);
lean_inc_n(v_map_130_, 2);
lean_dec_ref(v_inst_128_);
v___f_131_ = ((lean_object*)(l_Lake_getNoBuild___redArg___closed__0));
v___f_132_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_133_ = lean_apply_4(v_map_130_, lean_box(0), lean_box(0), v___f_132_, v_inst_129_);
v___x_134_ = lean_apply_4(v_map_130_, lean_box(0), lean_box(0), v___f_131_, v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT uint8_t l_Lake_getVerbosity___redArg___lam__0(lean_object* v_x_135_){
_start:
{
uint8_t v_verbosity_136_; 
v_verbosity_136_ = lean_ctor_get_uint8(v_x_135_, sizeof(void*)*3 + 3);
return v_verbosity_136_;
}
}
LEAN_EXPORT lean_object* l_Lake_getVerbosity___redArg___lam__0___boxed(lean_object* v_x_137_){
_start:
{
uint8_t v_res_138_; lean_object* v_r_139_; 
v_res_138_ = l_Lake_getVerbosity___redArg___lam__0(v_x_137_);
lean_dec_ref(v_x_137_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT lean_object* l_Lake_getVerbosity___redArg(lean_object* v_inst_141_, lean_object* v_inst_142_){
_start:
{
lean_object* v_map_143_; lean_object* v___f_144_; lean_object* v___f_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v_map_143_ = lean_ctor_get(v_inst_141_, 0);
lean_inc_n(v_map_143_, 2);
lean_dec_ref(v_inst_141_);
v___f_144_ = ((lean_object*)(l_Lake_getVerbosity___redArg___closed__0));
v___f_145_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_146_ = lean_apply_4(v_map_143_, lean_box(0), lean_box(0), v___f_145_, v_inst_142_);
v___x_147_ = lean_apply_4(v_map_143_, lean_box(0), lean_box(0), v___f_144_, v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lake_getVerbosity(lean_object* v_m_148_, lean_object* v_inst_149_, lean_object* v_inst_150_){
_start:
{
lean_object* v_map_151_; lean_object* v___f_152_; lean_object* v___f_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v_map_151_ = lean_ctor_get(v_inst_149_, 0);
lean_inc_n(v_map_151_, 2);
lean_dec_ref(v_inst_149_);
v___f_152_ = ((lean_object*)(l_Lake_getVerbosity___redArg___closed__0));
v___f_153_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_154_ = lean_apply_4(v_map_151_, lean_box(0), lean_box(0), v___f_153_, v_inst_150_);
v___x_155_ = lean_apply_4(v_map_151_, lean_box(0), lean_box(0), v___f_152_, v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT uint8_t l_Lake_getIsVerbose___redArg___lam__0(uint8_t v_x_156_){
_start:
{
uint8_t v___x_157_; uint8_t v___x_158_; 
v___x_157_ = 2;
v___x_158_ = l_Lake_instDecidableEqVerbosity(v_x_156_, v___x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsVerbose___redArg___lam__0___boxed(lean_object* v_x_159_){
_start:
{
uint8_t v_x_54__boxed_160_; uint8_t v_res_161_; lean_object* v_r_162_; 
v_x_54__boxed_160_ = lean_unbox(v_x_159_);
v_res_161_ = l_Lake_getIsVerbose___redArg___lam__0(v_x_54__boxed_160_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsVerbose___redArg(lean_object* v_inst_164_, lean_object* v_inst_165_){
_start:
{
lean_object* v_map_166_; lean_object* v___f_167_; lean_object* v___f_168_; lean_object* v___f_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_map_166_ = lean_ctor_get(v_inst_164_, 0);
lean_inc_n(v_map_166_, 3);
lean_dec_ref(v_inst_164_);
v___f_167_ = ((lean_object*)(l_Lake_getIsVerbose___redArg___closed__0));
v___f_168_ = ((lean_object*)(l_Lake_getVerbosity___redArg___closed__0));
v___f_169_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_170_ = lean_apply_4(v_map_166_, lean_box(0), lean_box(0), v___f_169_, v_inst_165_);
v___x_171_ = lean_apply_4(v_map_166_, lean_box(0), lean_box(0), v___f_168_, v___x_170_);
v___x_172_ = lean_apply_4(v_map_166_, lean_box(0), lean_box(0), v___f_167_, v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsVerbose(lean_object* v_m_173_, lean_object* v_inst_174_, lean_object* v_inst_175_){
_start:
{
lean_object* v_map_176_; lean_object* v___f_177_; lean_object* v___f_178_; lean_object* v___f_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_map_176_ = lean_ctor_get(v_inst_174_, 0);
lean_inc_n(v_map_176_, 3);
lean_dec_ref(v_inst_174_);
v___f_177_ = ((lean_object*)(l_Lake_getIsVerbose___redArg___closed__0));
v___f_178_ = ((lean_object*)(l_Lake_getVerbosity___redArg___closed__0));
v___f_179_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_180_ = lean_apply_4(v_map_176_, lean_box(0), lean_box(0), v___f_179_, v_inst_175_);
v___x_181_ = lean_apply_4(v_map_176_, lean_box(0), lean_box(0), v___f_178_, v___x_180_);
v___x_182_ = lean_apply_4(v_map_176_, lean_box(0), lean_box(0), v___f_177_, v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT uint8_t l_Lake_getIsQuiet___redArg___lam__0(uint8_t v_x_183_){
_start:
{
uint8_t v___x_184_; uint8_t v___x_185_; 
v___x_184_ = 0;
v___x_185_ = l_Lake_instDecidableEqVerbosity(v_x_183_, v___x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsQuiet___redArg___lam__0___boxed(lean_object* v_x_186_){
_start:
{
uint8_t v_x_54__boxed_187_; uint8_t v_res_188_; lean_object* v_r_189_; 
v_x_54__boxed_187_ = lean_unbox(v_x_186_);
v_res_188_ = l_Lake_getIsQuiet___redArg___lam__0(v_x_54__boxed_187_);
v_r_189_ = lean_box(v_res_188_);
return v_r_189_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsQuiet___redArg(lean_object* v_inst_191_, lean_object* v_inst_192_){
_start:
{
lean_object* v_map_193_; lean_object* v___f_194_; lean_object* v___f_195_; lean_object* v___f_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v_map_193_ = lean_ctor_get(v_inst_191_, 0);
lean_inc_n(v_map_193_, 3);
lean_dec_ref(v_inst_191_);
v___f_194_ = ((lean_object*)(l_Lake_getIsQuiet___redArg___closed__0));
v___f_195_ = ((lean_object*)(l_Lake_getVerbosity___redArg___closed__0));
v___f_196_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_197_ = lean_apply_4(v_map_193_, lean_box(0), lean_box(0), v___f_196_, v_inst_192_);
v___x_198_ = lean_apply_4(v_map_193_, lean_box(0), lean_box(0), v___f_195_, v___x_197_);
v___x_199_ = lean_apply_4(v_map_193_, lean_box(0), lean_box(0), v___f_194_, v___x_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsQuiet(lean_object* v_m_200_, lean_object* v_inst_201_, lean_object* v_inst_202_){
_start:
{
lean_object* v_map_203_; lean_object* v___f_204_; lean_object* v___f_205_; lean_object* v___f_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v_map_203_ = lean_ctor_get(v_inst_201_, 0);
lean_inc_n(v_map_203_, 3);
lean_dec_ref(v_inst_201_);
v___f_204_ = ((lean_object*)(l_Lake_getIsQuiet___redArg___closed__0));
v___f_205_ = ((lean_object*)(l_Lake_getVerbosity___redArg___closed__0));
v___f_206_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_207_ = lean_apply_4(v_map_203_, lean_box(0), lean_box(0), v___f_206_, v_inst_202_);
v___x_208_ = lean_apply_4(v_map_203_, lean_box(0), lean_box(0), v___f_205_, v___x_207_);
v___x_209_ = lean_apply_4(v_map_203_, lean_box(0), lean_box(0), v___f_204_, v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanOptOverrides___redArg___lam__0(lean_object* v_x_210_){
_start:
{
lean_object* v_leanOptOverrides_211_; 
v_leanOptOverrides_211_ = lean_ctor_get(v_x_210_, 2);
lean_inc(v_leanOptOverrides_211_);
return v_leanOptOverrides_211_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanOptOverrides___redArg___lam__0___boxed(lean_object* v_x_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lake_getLeanOptOverrides___redArg___lam__0(v_x_212_);
lean_dec_ref(v_x_212_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanOptOverrides___redArg(lean_object* v_inst_215_, lean_object* v_inst_216_){
_start:
{
lean_object* v_map_217_; lean_object* v___f_218_; lean_object* v___f_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_map_217_ = lean_ctor_get(v_inst_215_, 0);
lean_inc_n(v_map_217_, 2);
lean_dec_ref(v_inst_215_);
v___f_218_ = ((lean_object*)(l_Lake_getLeanOptOverrides___redArg___closed__0));
v___f_219_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_220_ = lean_apply_4(v_map_217_, lean_box(0), lean_box(0), v___f_219_, v_inst_216_);
v___x_221_ = lean_apply_4(v_map_217_, lean_box(0), lean_box(0), v___f_218_, v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanOptOverrides(lean_object* v_m_222_, lean_object* v_inst_223_, lean_object* v_inst_224_){
_start:
{
lean_object* v_map_225_; lean_object* v___f_226_; lean_object* v___f_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_map_225_ = lean_ctor_get(v_inst_223_, 0);
lean_inc_n(v_map_225_, 2);
lean_dec_ref(v_inst_223_);
v___f_226_ = ((lean_object*)(l_Lake_getLeanOptOverrides___redArg___closed__0));
v___f_227_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_228_ = lean_apply_4(v_map_225_, lean_box(0), lean_box(0), v___f_227_, v_inst_224_);
v___x_229_ = lean_apply_4(v_map_225_, lean_box(0), lean_box(0), v___f_226_, v___x_228_);
return v___x_229_;
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
