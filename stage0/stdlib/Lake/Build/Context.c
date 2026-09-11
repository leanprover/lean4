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
lean_object* l_Lake_Verbosity_ctorIdx(uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
static lean_once_cell_t l_Lake_BuildConfig_showProgress___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_BuildConfig_showProgress___closed__0;
static lean_once_cell_t l_Lake_BuildConfig_showProgress___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_BuildConfig_showProgress___closed__1;
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
static lean_object* _init_l_Lake_BuildConfig_showProgress___closed__0(void){
_start:
{
uint8_t v___x_1_; lean_object* v___x_2_; 
v___x_1_ = 0;
v___x_2_ = l_Lake_Verbosity_ctorIdx(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Lake_BuildConfig_showProgress___closed__1(void){
_start:
{
uint8_t v___x_3_; lean_object* v___x_4_; 
v___x_3_ = 2;
v___x_4_ = l_Lake_Verbosity_ctorIdx(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildConfig_showProgress(lean_object* v_cfg_5_){
_start:
{
uint8_t v_noBuild_6_; uint8_t v_verbosity_7_; lean_object* v___x_8_; uint8_t v___y_10_; 
v_noBuild_6_ = lean_ctor_get_uint8(v_cfg_5_, sizeof(void*)*4 + 2);
v_verbosity_7_ = lean_ctor_get_uint8(v_cfg_5_, sizeof(void*)*4 + 4);
v___x_8_ = l_Lake_Verbosity_ctorIdx(v_verbosity_7_);
if (v_noBuild_6_ == 0)
{
v___y_10_ = v_noBuild_6_;
goto v___jp_9_;
}
else
{
lean_object* v___x_14_; uint8_t v___x_15_; 
v___x_14_ = lean_obj_once(&l_Lake_BuildConfig_showProgress___closed__1, &l_Lake_BuildConfig_showProgress___closed__1_once, _init_l_Lake_BuildConfig_showProgress___closed__1);
v___x_15_ = lean_nat_dec_eq(v___x_8_, v___x_14_);
v___y_10_ = v___x_15_;
goto v___jp_9_;
}
v___jp_9_:
{
lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_11_ = lean_obj_once(&l_Lake_BuildConfig_showProgress___closed__0, &l_Lake_BuildConfig_showProgress___closed__0_once, _init_l_Lake_BuildConfig_showProgress___closed__0);
v___x_12_ = lean_nat_dec_eq(v___x_8_, v___x_11_);
lean_dec(v___x_8_);
if (v___x_12_ == 0)
{
if (v___y_10_ == 0)
{
uint8_t v___x_13_; 
v___x_13_ = 1;
return v___x_13_;
}
else
{
return v___y_10_;
}
}
else
{
return v___y_10_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildConfig_showProgress___boxed(lean_object* v_cfg_16_){
_start:
{
uint8_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = l_Lake_BuildConfig_showProgress(v_cfg_16_);
lean_dec_ref(v_cfg_16_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkJobQueue(){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = ((lean_object*)(l_Lake_mkJobQueue___closed__0));
v___x_23_ = lean_st_mk_ref(v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkJobQueue___boxed(lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lake_mkJobQueue();
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0(lean_object* v_inst_26_, lean_object* v_00_u03b1_27_, lean_object* v_x_28_, lean_object* v_ctx_29_){
_start:
{
lean_object* v_toContext_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v_toContext_30_ = lean_ctor_get(v_ctx_29_, 1);
lean_inc(v_toContext_30_);
lean_dec_ref(v_ctx_29_);
v___x_31_ = lean_apply_1(v_x_28_, v_toContext_30_);
v___x_32_ = lean_apply_2(v_inst_26_, lean_box(0), v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLakeMBuildTOfPure___redArg(lean_object* v_inst_33_){
_start:
{
lean_object* v___f_34_; 
v___f_34_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_34_, 0, v_inst_33_);
return v___f_34_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLakeMBuildTOfPure(lean_object* v_m_35_, lean_object* v_inst_36_){
_start:
{
lean_object* v___f_37_; 
v___f_37_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_37_, 0, v_inst_36_);
return v___f_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildContext___redArg(lean_object* v_inst_38_){
_start:
{
lean_inc(v_inst_38_);
return v_inst_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildContext___redArg___boxed(lean_object* v_inst_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lake_getBuildContext___redArg(v_inst_39_);
lean_dec(v_inst_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildContext(lean_object* v_m_41_, lean_object* v_inst_42_){
_start:
{
lean_inc(v_inst_42_);
return v_inst_42_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildContext___boxed(lean_object* v_m_43_, lean_object* v_inst_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lake_getBuildContext(v_m_43_, v_inst_44_);
lean_dec(v_inst_44_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanTrace___redArg___lam__0(lean_object* v_x_46_){
_start:
{
lean_object* v_leanTrace_47_; 
v_leanTrace_47_ = lean_ctor_get(v_x_46_, 2);
lean_inc_ref(v_leanTrace_47_);
return v_leanTrace_47_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanTrace___redArg___lam__0___boxed(lean_object* v_x_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lake_getLeanTrace___redArg___lam__0(v_x_48_);
lean_dec_ref(v_x_48_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanTrace___redArg(lean_object* v_inst_51_, lean_object* v_inst_52_){
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
LEAN_EXPORT lean_object* l_Lake_getLeanTrace(lean_object* v_m_56_, lean_object* v_inst_57_, lean_object* v_inst_58_){
_start:
{
lean_object* v_map_59_; lean_object* v___f_60_; lean_object* v___x_61_; 
v_map_59_ = lean_ctor_get(v_inst_57_, 0);
lean_inc(v_map_59_);
lean_dec_ref(v_inst_57_);
v___f_60_ = ((lean_object*)(l_Lake_getLeanTrace___redArg___closed__0));
v___x_61_ = lean_apply_4(v_map_59_, lean_box(0), lean_box(0), v___f_60_, v_inst_58_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildConfig___redArg___lam__0(lean_object* v_x_62_){
_start:
{
lean_object* v_toBuildConfig_63_; 
v_toBuildConfig_63_ = lean_ctor_get(v_x_62_, 0);
lean_inc_ref(v_toBuildConfig_63_);
return v_toBuildConfig_63_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildConfig___redArg___lam__0___boxed(lean_object* v_x_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lake_getBuildConfig___redArg___lam__0(v_x_64_);
lean_dec_ref(v_x_64_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildConfig___redArg(lean_object* v_inst_67_, lean_object* v_inst_68_){
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
LEAN_EXPORT lean_object* l_Lake_getBuildConfig(lean_object* v_m_72_, lean_object* v_inst_73_, lean_object* v_inst_74_){
_start:
{
lean_object* v_map_75_; lean_object* v___f_76_; lean_object* v___x_77_; 
v_map_75_ = lean_ctor_get(v_inst_73_, 0);
lean_inc(v_map_75_);
lean_dec_ref(v_inst_73_);
v___f_76_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_77_ = lean_apply_4(v_map_75_, lean_box(0), lean_box(0), v___f_76_, v_inst_74_);
return v___x_77_;
}
}
LEAN_EXPORT uint8_t l_Lake_getIsOldMode___redArg___lam__0(lean_object* v_x_78_){
_start:
{
uint8_t v_oldMode_79_; 
v_oldMode_79_ = lean_ctor_get_uint8(v_x_78_, sizeof(void*)*4);
return v_oldMode_79_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsOldMode___redArg___lam__0___boxed(lean_object* v_x_80_){
_start:
{
uint8_t v_res_81_; lean_object* v_r_82_; 
v_res_81_ = l_Lake_getIsOldMode___redArg___lam__0(v_x_80_);
lean_dec_ref(v_x_80_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsOldMode___redArg(lean_object* v_inst_84_, lean_object* v_inst_85_){
_start:
{
lean_object* v_map_86_; lean_object* v___f_87_; lean_object* v___f_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v_map_86_ = lean_ctor_get(v_inst_84_, 0);
lean_inc_n(v_map_86_, 2);
lean_dec_ref(v_inst_84_);
v___f_87_ = ((lean_object*)(l_Lake_getIsOldMode___redArg___closed__0));
v___f_88_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_89_ = lean_apply_4(v_map_86_, lean_box(0), lean_box(0), v___f_88_, v_inst_85_);
v___x_90_ = lean_apply_4(v_map_86_, lean_box(0), lean_box(0), v___f_87_, v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsOldMode(lean_object* v_m_91_, lean_object* v_inst_92_, lean_object* v_inst_93_){
_start:
{
lean_object* v_map_94_; lean_object* v___f_95_; lean_object* v___f_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v_map_94_ = lean_ctor_get(v_inst_92_, 0);
lean_inc_n(v_map_94_, 2);
lean_dec_ref(v_inst_92_);
v___f_95_ = ((lean_object*)(l_Lake_getIsOldMode___redArg___closed__0));
v___f_96_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_97_ = lean_apply_4(v_map_94_, lean_box(0), lean_box(0), v___f_96_, v_inst_93_);
v___x_98_ = lean_apply_4(v_map_94_, lean_box(0), lean_box(0), v___f_95_, v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT uint8_t l_Lake_getTrustHash___redArg___lam__0(lean_object* v_x_99_){
_start:
{
uint8_t v_trustHash_100_; 
v_trustHash_100_ = lean_ctor_get_uint8(v_x_99_, sizeof(void*)*4 + 1);
return v_trustHash_100_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrustHash___redArg___lam__0___boxed(lean_object* v_x_101_){
_start:
{
uint8_t v_res_102_; lean_object* v_r_103_; 
v_res_102_ = l_Lake_getTrustHash___redArg___lam__0(v_x_101_);
lean_dec_ref(v_x_101_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrustHash___redArg(lean_object* v_inst_105_, lean_object* v_inst_106_){
_start:
{
lean_object* v_map_107_; lean_object* v___f_108_; lean_object* v___f_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v_map_107_ = lean_ctor_get(v_inst_105_, 0);
lean_inc_n(v_map_107_, 2);
lean_dec_ref(v_inst_105_);
v___f_108_ = ((lean_object*)(l_Lake_getTrustHash___redArg___closed__0));
v___f_109_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_110_ = lean_apply_4(v_map_107_, lean_box(0), lean_box(0), v___f_109_, v_inst_106_);
v___x_111_ = lean_apply_4(v_map_107_, lean_box(0), lean_box(0), v___f_108_, v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrustHash(lean_object* v_m_112_, lean_object* v_inst_113_, lean_object* v_inst_114_){
_start:
{
lean_object* v_map_115_; lean_object* v___f_116_; lean_object* v___f_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v_map_115_ = lean_ctor_get(v_inst_113_, 0);
lean_inc_n(v_map_115_, 2);
lean_dec_ref(v_inst_113_);
v___f_116_ = ((lean_object*)(l_Lake_getTrustHash___redArg___closed__0));
v___f_117_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_118_ = lean_apply_4(v_map_115_, lean_box(0), lean_box(0), v___f_117_, v_inst_114_);
v___x_119_ = lean_apply_4(v_map_115_, lean_box(0), lean_box(0), v___f_116_, v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT uint8_t l_Lake_getNoBuild___redArg___lam__0(lean_object* v_x_120_){
_start:
{
uint8_t v_noBuild_121_; 
v_noBuild_121_ = lean_ctor_get_uint8(v_x_120_, sizeof(void*)*4 + 2);
return v_noBuild_121_;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoBuild___redArg___lam__0___boxed(lean_object* v_x_122_){
_start:
{
uint8_t v_res_123_; lean_object* v_r_124_; 
v_res_123_ = l_Lake_getNoBuild___redArg___lam__0(v_x_122_);
lean_dec_ref(v_x_122_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoBuild___redArg(lean_object* v_inst_126_, lean_object* v_inst_127_){
_start:
{
lean_object* v_map_128_; lean_object* v___f_129_; lean_object* v___f_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v_map_128_ = lean_ctor_get(v_inst_126_, 0);
lean_inc_n(v_map_128_, 2);
lean_dec_ref(v_inst_126_);
v___f_129_ = ((lean_object*)(l_Lake_getNoBuild___redArg___closed__0));
v___f_130_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_131_ = lean_apply_4(v_map_128_, lean_box(0), lean_box(0), v___f_130_, v_inst_127_);
v___x_132_ = lean_apply_4(v_map_128_, lean_box(0), lean_box(0), v___f_129_, v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoBuild(lean_object* v_m_133_, lean_object* v_inst_134_, lean_object* v_inst_135_){
_start:
{
lean_object* v_map_136_; lean_object* v___f_137_; lean_object* v___f_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v_map_136_ = lean_ctor_get(v_inst_134_, 0);
lean_inc_n(v_map_136_, 2);
lean_dec_ref(v_inst_134_);
v___f_137_ = ((lean_object*)(l_Lake_getNoBuild___redArg___closed__0));
v___f_138_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_139_ = lean_apply_4(v_map_136_, lean_box(0), lean_box(0), v___f_138_, v_inst_135_);
v___x_140_ = lean_apply_4(v_map_136_, lean_box(0), lean_box(0), v___f_137_, v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT uint8_t l_Lake_getVerbosity___redArg___lam__0(lean_object* v_x_141_){
_start:
{
uint8_t v_verbosity_142_; 
v_verbosity_142_ = lean_ctor_get_uint8(v_x_141_, sizeof(void*)*4 + 4);
return v_verbosity_142_;
}
}
LEAN_EXPORT lean_object* l_Lake_getVerbosity___redArg___lam__0___boxed(lean_object* v_x_143_){
_start:
{
uint8_t v_res_144_; lean_object* v_r_145_; 
v_res_144_ = l_Lake_getVerbosity___redArg___lam__0(v_x_143_);
lean_dec_ref(v_x_143_);
v_r_145_ = lean_box(v_res_144_);
return v_r_145_;
}
}
LEAN_EXPORT lean_object* l_Lake_getVerbosity___redArg(lean_object* v_inst_147_, lean_object* v_inst_148_){
_start:
{
lean_object* v_map_149_; lean_object* v___f_150_; lean_object* v___f_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v_map_149_ = lean_ctor_get(v_inst_147_, 0);
lean_inc_n(v_map_149_, 2);
lean_dec_ref(v_inst_147_);
v___f_150_ = ((lean_object*)(l_Lake_getVerbosity___redArg___closed__0));
v___f_151_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_152_ = lean_apply_4(v_map_149_, lean_box(0), lean_box(0), v___f_151_, v_inst_148_);
v___x_153_ = lean_apply_4(v_map_149_, lean_box(0), lean_box(0), v___f_150_, v___x_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lake_getVerbosity(lean_object* v_m_154_, lean_object* v_inst_155_, lean_object* v_inst_156_){
_start:
{
lean_object* v_map_157_; lean_object* v___f_158_; lean_object* v___f_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_map_157_ = lean_ctor_get(v_inst_155_, 0);
lean_inc_n(v_map_157_, 2);
lean_dec_ref(v_inst_155_);
v___f_158_ = ((lean_object*)(l_Lake_getVerbosity___redArg___closed__0));
v___f_159_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_160_ = lean_apply_4(v_map_157_, lean_box(0), lean_box(0), v___f_159_, v_inst_156_);
v___x_161_ = lean_apply_4(v_map_157_, lean_box(0), lean_box(0), v___f_158_, v___x_160_);
return v___x_161_;
}
}
LEAN_EXPORT uint8_t l_Lake_getIsVerbose___redArg___lam__0(uint8_t v_x_162_){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_163_ = l_Lake_Verbosity_ctorIdx(v_x_162_);
v___x_164_ = lean_obj_once(&l_Lake_BuildConfig_showProgress___closed__1, &l_Lake_BuildConfig_showProgress___closed__1_once, _init_l_Lake_BuildConfig_showProgress___closed__1);
v___x_165_ = lean_nat_dec_eq(v___x_163_, v___x_164_);
lean_dec(v___x_163_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsVerbose___redArg___lam__0___boxed(lean_object* v_x_166_){
_start:
{
uint8_t v_x_71__boxed_167_; uint8_t v_res_168_; lean_object* v_r_169_; 
v_x_71__boxed_167_ = lean_unbox(v_x_166_);
v_res_168_ = l_Lake_getIsVerbose___redArg___lam__0(v_x_71__boxed_167_);
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
lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_191_ = l_Lake_Verbosity_ctorIdx(v_x_190_);
v___x_192_ = lean_obj_once(&l_Lake_BuildConfig_showProgress___closed__0, &l_Lake_BuildConfig_showProgress___closed__0_once, _init_l_Lake_BuildConfig_showProgress___closed__0);
v___x_193_ = lean_nat_dec_eq(v___x_191_, v___x_192_);
lean_dec(v___x_191_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsQuiet___redArg___lam__0___boxed(lean_object* v_x_194_){
_start:
{
uint8_t v_x_71__boxed_195_; uint8_t v_res_196_; lean_object* v_r_197_; 
v_x_71__boxed_195_ = lean_unbox(v_x_194_);
v_res_196_ = l_Lake_getIsQuiet___redArg___lam__0(v_x_71__boxed_195_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsQuiet___redArg(lean_object* v_inst_199_, lean_object* v_inst_200_){
_start:
{
lean_object* v_map_201_; lean_object* v___f_202_; lean_object* v___f_203_; lean_object* v___f_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v_map_201_ = lean_ctor_get(v_inst_199_, 0);
lean_inc_n(v_map_201_, 3);
lean_dec_ref(v_inst_199_);
v___f_202_ = ((lean_object*)(l_Lake_getIsQuiet___redArg___closed__0));
v___f_203_ = ((lean_object*)(l_Lake_getVerbosity___redArg___closed__0));
v___f_204_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_205_ = lean_apply_4(v_map_201_, lean_box(0), lean_box(0), v___f_204_, v_inst_200_);
v___x_206_ = lean_apply_4(v_map_201_, lean_box(0), lean_box(0), v___f_203_, v___x_205_);
v___x_207_ = lean_apply_4(v_map_201_, lean_box(0), lean_box(0), v___f_202_, v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsQuiet(lean_object* v_m_208_, lean_object* v_inst_209_, lean_object* v_inst_210_){
_start:
{
lean_object* v_map_211_; lean_object* v___f_212_; lean_object* v___f_213_; lean_object* v___f_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v_map_211_ = lean_ctor_get(v_inst_209_, 0);
lean_inc_n(v_map_211_, 3);
lean_dec_ref(v_inst_209_);
v___f_212_ = ((lean_object*)(l_Lake_getIsQuiet___redArg___closed__0));
v___f_213_ = ((lean_object*)(l_Lake_getVerbosity___redArg___closed__0));
v___f_214_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_215_ = lean_apply_4(v_map_211_, lean_box(0), lean_box(0), v___f_214_, v_inst_210_);
v___x_216_ = lean_apply_4(v_map_211_, lean_box(0), lean_box(0), v___f_213_, v___x_215_);
v___x_217_ = lean_apply_4(v_map_211_, lean_box(0), lean_box(0), v___f_212_, v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanOptOverrides___redArg___lam__0(lean_object* v_x_218_){
_start:
{
lean_object* v_leanOptOverrides_219_; 
v_leanOptOverrides_219_ = lean_ctor_get(v_x_218_, 2);
lean_inc(v_leanOptOverrides_219_);
return v_leanOptOverrides_219_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanOptOverrides___redArg___lam__0___boxed(lean_object* v_x_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lake_getLeanOptOverrides___redArg___lam__0(v_x_220_);
lean_dec_ref(v_x_220_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanOptOverrides___redArg(lean_object* v_inst_223_, lean_object* v_inst_224_){
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
LEAN_EXPORT lean_object* l_Lake_getLeanOptOverrides(lean_object* v_m_230_, lean_object* v_inst_231_, lean_object* v_inst_232_){
_start:
{
lean_object* v_map_233_; lean_object* v___f_234_; lean_object* v___f_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v_map_233_ = lean_ctor_get(v_inst_231_, 0);
lean_inc_n(v_map_233_, 2);
lean_dec_ref(v_inst_231_);
v___f_234_ = ((lean_object*)(l_Lake_getLeanOptOverrides___redArg___closed__0));
v___f_235_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_236_ = lean_apply_4(v_map_233_, lean_box(0), lean_box(0), v___f_235_, v_inst_232_);
v___x_237_ = lean_apply_4(v_map_233_, lean_box(0), lean_box(0), v___f_234_, v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lake_getMacOSXDeploymentTarget_x3f___redArg___lam__0(lean_object* v_x_238_){
_start:
{
lean_object* v_macosxDeploymentTarget_x3f_239_; 
v_macosxDeploymentTarget_x3f_239_ = lean_ctor_get(v_x_238_, 3);
lean_inc(v_macosxDeploymentTarget_x3f_239_);
return v_macosxDeploymentTarget_x3f_239_;
}
}
LEAN_EXPORT lean_object* l_Lake_getMacOSXDeploymentTarget_x3f___redArg___lam__0___boxed(lean_object* v_x_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lake_getMacOSXDeploymentTarget_x3f___redArg___lam__0(v_x_240_);
lean_dec_ref(v_x_240_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lake_getMacOSXDeploymentTarget_x3f___redArg(lean_object* v_inst_243_, lean_object* v_inst_244_){
_start:
{
lean_object* v_map_245_; lean_object* v___f_246_; lean_object* v___f_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v_map_245_ = lean_ctor_get(v_inst_243_, 0);
lean_inc_n(v_map_245_, 2);
lean_dec_ref(v_inst_243_);
v___f_246_ = ((lean_object*)(l_Lake_getMacOSXDeploymentTarget_x3f___redArg___closed__0));
v___f_247_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_248_ = lean_apply_4(v_map_245_, lean_box(0), lean_box(0), v___f_247_, v_inst_244_);
v___x_249_ = lean_apply_4(v_map_245_, lean_box(0), lean_box(0), v___f_246_, v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lake_getMacOSXDeploymentTarget_x3f(lean_object* v_m_250_, lean_object* v_inst_251_, lean_object* v_inst_252_){
_start:
{
lean_object* v_map_253_; lean_object* v___f_254_; lean_object* v___f_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v_map_253_ = lean_ctor_get(v_inst_251_, 0);
lean_inc_n(v_map_253_, 2);
lean_dec_ref(v_inst_251_);
v___f_254_ = ((lean_object*)(l_Lake_getMacOSXDeploymentTarget_x3f___redArg___closed__0));
v___f_255_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_256_ = lean_apply_4(v_map_253_, lean_box(0), lean_box(0), v___f_255_, v_inst_252_);
v___x_257_ = lean_apply_4(v_map_253_, lean_box(0), lean_box(0), v___f_254_, v___x_256_);
return v___x_257_;
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
