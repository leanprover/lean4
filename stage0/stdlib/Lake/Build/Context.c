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
uint8_t l_Lake_BuildConfig_showProgress(lean_object* v_cfg_1_){
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
LEAN_EXPORT void l_Lake_BuildConfig_showProgress_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_1_ = stack[0].m_obj;
uint8_t v_res_15_;
v_res_15_ = l_Lake_BuildConfig_showProgress(v_cfg_1_);
stack->m_num = v_res_15_;
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
lean_object* l_Lake_mkJobQueue(){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = ((lean_object*)(l_Lake_mkJobQueue___closed__0));
v___x_23_ = lean_st_mk_ref(v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT void l_Lake_mkJobQueue_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_24_;
v_res_24_ = l_Lake_mkJobQueue();
stack->m_obj
 = v_res_24_;
}
LEAN_EXPORT lean_object* l_Lake_mkJobQueue___boxed(lean_object* v_a_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lake_mkJobQueue();
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0(lean_object* v_inst_27_, lean_object* v_00_u03b1_28_, lean_object* v_x_29_, lean_object* v_ctx_30_){
_start:
{
lean_object* v_toContext_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v_toContext_31_ = lean_ctor_get(v_ctx_30_, 1);
lean_inc(v_toContext_31_);
lean_dec_ref(v_ctx_30_);
v___x_32_ = lean_apply_1(v_x_29_, v_toContext_31_);
v___x_33_ = lean_apply_2(v_inst_27_, lean_box(0), v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLakeMBuildTOfPure___redArg(lean_object* v_inst_34_){
_start:
{
lean_object* v___f_35_; 
v___f_35_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_35_, 0, v_inst_34_);
return v___f_35_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLakeMBuildTOfPure(lean_object* v_m_36_, lean_object* v_inst_37_){
_start:
{
lean_object* v___f_38_; 
v___f_38_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_38_, 0, v_inst_37_);
return v___f_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildContext___redArg(lean_object* v_inst_39_){
_start:
{
lean_inc(v_inst_39_);
return v_inst_39_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildContext___redArg___boxed(lean_object* v_inst_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lake_getBuildContext___redArg(v_inst_40_);
lean_dec(v_inst_40_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildContext(lean_object* v_m_42_, lean_object* v_inst_43_){
_start:
{
lean_inc(v_inst_43_);
return v_inst_43_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildContext___boxed(lean_object* v_m_44_, lean_object* v_inst_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lake_getBuildContext(v_m_44_, v_inst_45_);
lean_dec(v_inst_45_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanTrace___redArg___lam__0(lean_object* v_x_47_){
_start:
{
lean_object* v_leanTrace_48_; 
v_leanTrace_48_ = lean_ctor_get(v_x_47_, 2);
lean_inc_ref(v_leanTrace_48_);
return v_leanTrace_48_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanTrace___redArg___lam__0___boxed(lean_object* v_x_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lake_getLeanTrace___redArg___lam__0(v_x_49_);
lean_dec_ref(v_x_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanTrace___redArg(lean_object* v_inst_52_, lean_object* v_inst_53_){
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
LEAN_EXPORT lean_object* l_Lake_getLeanTrace(lean_object* v_m_57_, lean_object* v_inst_58_, lean_object* v_inst_59_){
_start:
{
lean_object* v_map_60_; lean_object* v___f_61_; lean_object* v___x_62_; 
v_map_60_ = lean_ctor_get(v_inst_58_, 0);
lean_inc(v_map_60_);
lean_dec_ref(v_inst_58_);
v___f_61_ = ((lean_object*)(l_Lake_getLeanTrace___redArg___closed__0));
v___x_62_ = lean_apply_4(v_map_60_, lean_box(0), lean_box(0), v___f_61_, v_inst_59_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildConfig___redArg___lam__0(lean_object* v_x_63_){
_start:
{
lean_object* v_toBuildConfig_64_; 
v_toBuildConfig_64_ = lean_ctor_get(v_x_63_, 0);
lean_inc_ref(v_toBuildConfig_64_);
return v_toBuildConfig_64_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildConfig___redArg___lam__0___boxed(lean_object* v_x_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lake_getBuildConfig___redArg___lam__0(v_x_65_);
lean_dec_ref(v_x_65_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildConfig___redArg(lean_object* v_inst_68_, lean_object* v_inst_69_){
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
LEAN_EXPORT lean_object* l_Lake_getBuildConfig(lean_object* v_m_73_, lean_object* v_inst_74_, lean_object* v_inst_75_){
_start:
{
lean_object* v_map_76_; lean_object* v___f_77_; lean_object* v___x_78_; 
v_map_76_ = lean_ctor_get(v_inst_74_, 0);
lean_inc(v_map_76_);
lean_dec_ref(v_inst_74_);
v___f_77_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_78_ = lean_apply_4(v_map_76_, lean_box(0), lean_box(0), v___f_77_, v_inst_75_);
return v___x_78_;
}
}
uint8_t l_Lake_getIsOldMode___redArg___lam__0(lean_object* v_x_79_){
_start:
{
uint8_t v_oldMode_80_; 
v_oldMode_80_ = lean_ctor_get_uint8(v_x_79_, sizeof(void*)*5);
return v_oldMode_80_;
}
}
LEAN_EXPORT void l_Lake_getIsOldMode___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_79_ = stack[0].m_obj;
uint8_t v_res_81_;
v_res_81_ = l_Lake_getIsOldMode___redArg___lam__0(v_x_79_);
stack->m_num = v_res_81_;
}
LEAN_EXPORT lean_object* l_Lake_getIsOldMode___redArg___lam__0___boxed(lean_object* v_x_82_){
_start:
{
uint8_t v_res_83_; lean_object* v_r_84_; 
v_res_83_ = l_Lake_getIsOldMode___redArg___lam__0(v_x_82_);
lean_dec_ref(v_x_82_);
v_r_84_ = lean_box(v_res_83_);
return v_r_84_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsOldMode___redArg(lean_object* v_inst_86_, lean_object* v_inst_87_){
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
LEAN_EXPORT lean_object* l_Lake_getIsOldMode(lean_object* v_m_93_, lean_object* v_inst_94_, lean_object* v_inst_95_){
_start:
{
lean_object* v_map_96_; lean_object* v___f_97_; lean_object* v___f_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v_map_96_ = lean_ctor_get(v_inst_94_, 0);
lean_inc_n(v_map_96_, 2);
lean_dec_ref(v_inst_94_);
v___f_97_ = ((lean_object*)(l_Lake_getIsOldMode___redArg___closed__0));
v___f_98_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_99_ = lean_apply_4(v_map_96_, lean_box(0), lean_box(0), v___f_98_, v_inst_95_);
v___x_100_ = lean_apply_4(v_map_96_, lean_box(0), lean_box(0), v___f_97_, v___x_99_);
return v___x_100_;
}
}
uint8_t l_Lake_getTrustHash___redArg___lam__0(lean_object* v_x_101_){
_start:
{
uint8_t v_trustHash_102_; 
v_trustHash_102_ = lean_ctor_get_uint8(v_x_101_, sizeof(void*)*5 + 1);
return v_trustHash_102_;
}
}
LEAN_EXPORT void l_Lake_getTrustHash___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_101_ = stack[0].m_obj;
uint8_t v_res_103_;
v_res_103_ = l_Lake_getTrustHash___redArg___lam__0(v_x_101_);
stack->m_num = v_res_103_;
}
LEAN_EXPORT lean_object* l_Lake_getTrustHash___redArg___lam__0___boxed(lean_object* v_x_104_){
_start:
{
uint8_t v_res_105_; lean_object* v_r_106_; 
v_res_105_ = l_Lake_getTrustHash___redArg___lam__0(v_x_104_);
lean_dec_ref(v_x_104_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrustHash___redArg(lean_object* v_inst_108_, lean_object* v_inst_109_){
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
LEAN_EXPORT lean_object* l_Lake_getTrustHash(lean_object* v_m_115_, lean_object* v_inst_116_, lean_object* v_inst_117_){
_start:
{
lean_object* v_map_118_; lean_object* v___f_119_; lean_object* v___f_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v_map_118_ = lean_ctor_get(v_inst_116_, 0);
lean_inc_n(v_map_118_, 2);
lean_dec_ref(v_inst_116_);
v___f_119_ = ((lean_object*)(l_Lake_getTrustHash___redArg___closed__0));
v___f_120_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_121_ = lean_apply_4(v_map_118_, lean_box(0), lean_box(0), v___f_120_, v_inst_117_);
v___x_122_ = lean_apply_4(v_map_118_, lean_box(0), lean_box(0), v___f_119_, v___x_121_);
return v___x_122_;
}
}
uint8_t l_Lake_getNoBuild___redArg___lam__0(lean_object* v_x_123_){
_start:
{
uint8_t v_noBuild_124_; 
v_noBuild_124_ = lean_ctor_get_uint8(v_x_123_, sizeof(void*)*5 + 2);
return v_noBuild_124_;
}
}
LEAN_EXPORT void l_Lake_getNoBuild___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_123_ = stack[0].m_obj;
uint8_t v_res_125_;
v_res_125_ = l_Lake_getNoBuild___redArg___lam__0(v_x_123_);
stack->m_num = v_res_125_;
}
LEAN_EXPORT lean_object* l_Lake_getNoBuild___redArg___lam__0___boxed(lean_object* v_x_126_){
_start:
{
uint8_t v_res_127_; lean_object* v_r_128_; 
v_res_127_ = l_Lake_getNoBuild___redArg___lam__0(v_x_126_);
lean_dec_ref(v_x_126_);
v_r_128_ = lean_box(v_res_127_);
return v_r_128_;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoBuild___redArg(lean_object* v_inst_130_, lean_object* v_inst_131_){
_start:
{
lean_object* v_map_132_; lean_object* v___f_133_; lean_object* v___f_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v_map_132_ = lean_ctor_get(v_inst_130_, 0);
lean_inc_n(v_map_132_, 2);
lean_dec_ref(v_inst_130_);
v___f_133_ = ((lean_object*)(l_Lake_getNoBuild___redArg___closed__0));
v___f_134_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_135_ = lean_apply_4(v_map_132_, lean_box(0), lean_box(0), v___f_134_, v_inst_131_);
v___x_136_ = lean_apply_4(v_map_132_, lean_box(0), lean_box(0), v___f_133_, v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoBuild(lean_object* v_m_137_, lean_object* v_inst_138_, lean_object* v_inst_139_){
_start:
{
lean_object* v_map_140_; lean_object* v___f_141_; lean_object* v___f_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v_map_140_ = lean_ctor_get(v_inst_138_, 0);
lean_inc_n(v_map_140_, 2);
lean_dec_ref(v_inst_138_);
v___f_141_ = ((lean_object*)(l_Lake_getNoBuild___redArg___closed__0));
v___f_142_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_143_ = lean_apply_4(v_map_140_, lean_box(0), lean_box(0), v___f_142_, v_inst_139_);
v___x_144_ = lean_apply_4(v_map_140_, lean_box(0), lean_box(0), v___f_141_, v___x_143_);
return v___x_144_;
}
}
uint8_t l_Lake_getVerbosity___redArg___lam__0(lean_object* v_x_145_){
_start:
{
uint8_t v_verbosity_146_; 
v_verbosity_146_ = lean_ctor_get_uint8(v_x_145_, sizeof(void*)*5 + 4);
return v_verbosity_146_;
}
}
LEAN_EXPORT void l_Lake_getVerbosity___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_145_ = stack[0].m_obj;
uint8_t v_res_147_;
v_res_147_ = l_Lake_getVerbosity___redArg___lam__0(v_x_145_);
stack->m_num = v_res_147_;
}
LEAN_EXPORT lean_object* l_Lake_getVerbosity___redArg___lam__0___boxed(lean_object* v_x_148_){
_start:
{
uint8_t v_res_149_; lean_object* v_r_150_; 
v_res_149_ = l_Lake_getVerbosity___redArg___lam__0(v_x_148_);
lean_dec_ref(v_x_148_);
v_r_150_ = lean_box(v_res_149_);
return v_r_150_;
}
}
LEAN_EXPORT lean_object* l_Lake_getVerbosity___redArg(lean_object* v_inst_152_, lean_object* v_inst_153_){
_start:
{
lean_object* v_map_154_; lean_object* v___f_155_; lean_object* v___f_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v_map_154_ = lean_ctor_get(v_inst_152_, 0);
lean_inc_n(v_map_154_, 2);
lean_dec_ref(v_inst_152_);
v___f_155_ = ((lean_object*)(l_Lake_getVerbosity___redArg___closed__0));
v___f_156_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_157_ = lean_apply_4(v_map_154_, lean_box(0), lean_box(0), v___f_156_, v_inst_153_);
v___x_158_ = lean_apply_4(v_map_154_, lean_box(0), lean_box(0), v___f_155_, v___x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lake_getVerbosity(lean_object* v_m_159_, lean_object* v_inst_160_, lean_object* v_inst_161_){
_start:
{
lean_object* v_map_162_; lean_object* v___f_163_; lean_object* v___f_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v_map_162_ = lean_ctor_get(v_inst_160_, 0);
lean_inc_n(v_map_162_, 2);
lean_dec_ref(v_inst_160_);
v___f_163_ = ((lean_object*)(l_Lake_getVerbosity___redArg___closed__0));
v___f_164_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_165_ = lean_apply_4(v_map_162_, lean_box(0), lean_box(0), v___f_164_, v_inst_161_);
v___x_166_ = lean_apply_4(v_map_162_, lean_box(0), lean_box(0), v___f_163_, v___x_165_);
return v___x_166_;
}
}
uint8_t l_Lake_getIsVerbose___redArg___lam__0(uint8_t v_x_167_){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_168_ = lean_box(v_x_167_);
v___x_169_ = lean_obj_tag_nat(v___x_168_);
lean_dec(v___x_168_);
v___x_170_ = lean_unsigned_to_nat(2u);
v___x_171_ = lean_nat_dec_eq(v___x_169_, v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT void l_Lake_getIsVerbose___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_167_ = stack[0].m_num;
uint8_t v_res_172_;
v_res_172_ = l_Lake_getIsVerbose___redArg___lam__0(v_x_167_);
stack->m_num = v_res_172_;
}
LEAN_EXPORT lean_object* l_Lake_getIsVerbose___redArg___lam__0___boxed(lean_object* v_x_173_){
_start:
{
uint8_t v_x_67__boxed_174_; uint8_t v_res_175_; lean_object* v_r_176_; 
v_x_67__boxed_174_ = lean_unbox(v_x_173_);
v_res_175_ = l_Lake_getIsVerbose___redArg___lam__0(v_x_67__boxed_174_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsVerbose___redArg(lean_object* v_inst_178_, lean_object* v_inst_179_){
_start:
{
lean_object* v_map_180_; lean_object* v___f_181_; lean_object* v___f_182_; lean_object* v___f_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v_map_180_ = lean_ctor_get(v_inst_178_, 0);
lean_inc_n(v_map_180_, 3);
lean_dec_ref(v_inst_178_);
v___f_181_ = ((lean_object*)(l_Lake_getIsVerbose___redArg___closed__0));
v___f_182_ = ((lean_object*)(l_Lake_getVerbosity___redArg___closed__0));
v___f_183_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_184_ = lean_apply_4(v_map_180_, lean_box(0), lean_box(0), v___f_183_, v_inst_179_);
v___x_185_ = lean_apply_4(v_map_180_, lean_box(0), lean_box(0), v___f_182_, v___x_184_);
v___x_186_ = lean_apply_4(v_map_180_, lean_box(0), lean_box(0), v___f_181_, v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsVerbose(lean_object* v_m_187_, lean_object* v_inst_188_, lean_object* v_inst_189_){
_start:
{
lean_object* v_map_190_; lean_object* v___f_191_; lean_object* v___f_192_; lean_object* v___f_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_map_190_ = lean_ctor_get(v_inst_188_, 0);
lean_inc_n(v_map_190_, 3);
lean_dec_ref(v_inst_188_);
v___f_191_ = ((lean_object*)(l_Lake_getIsVerbose___redArg___closed__0));
v___f_192_ = ((lean_object*)(l_Lake_getVerbosity___redArg___closed__0));
v___f_193_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_194_ = lean_apply_4(v_map_190_, lean_box(0), lean_box(0), v___f_193_, v_inst_189_);
v___x_195_ = lean_apply_4(v_map_190_, lean_box(0), lean_box(0), v___f_192_, v___x_194_);
v___x_196_ = lean_apply_4(v_map_190_, lean_box(0), lean_box(0), v___f_191_, v___x_195_);
return v___x_196_;
}
}
uint8_t l_Lake_getIsQuiet___redArg___lam__0(uint8_t v_x_197_){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_198_ = lean_box(v_x_197_);
v___x_199_ = lean_obj_tag_nat(v___x_198_);
lean_dec(v___x_198_);
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = lean_nat_dec_eq(v___x_199_, v___x_200_);
return v___x_201_;
}
}
LEAN_EXPORT void l_Lake_getIsQuiet___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_197_ = stack[0].m_num;
uint8_t v_res_202_;
v_res_202_ = l_Lake_getIsQuiet___redArg___lam__0(v_x_197_);
stack->m_num = v_res_202_;
}
LEAN_EXPORT lean_object* l_Lake_getIsQuiet___redArg___lam__0___boxed(lean_object* v_x_203_){
_start:
{
uint8_t v_x_67__boxed_204_; uint8_t v_res_205_; lean_object* v_r_206_; 
v_x_67__boxed_204_ = lean_unbox(v_x_203_);
v_res_205_ = l_Lake_getIsQuiet___redArg___lam__0(v_x_67__boxed_204_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsQuiet___redArg(lean_object* v_inst_208_, lean_object* v_inst_209_){
_start:
{
lean_object* v_map_210_; lean_object* v___f_211_; lean_object* v___f_212_; lean_object* v___f_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v_map_210_ = lean_ctor_get(v_inst_208_, 0);
lean_inc_n(v_map_210_, 3);
lean_dec_ref(v_inst_208_);
v___f_211_ = ((lean_object*)(l_Lake_getIsQuiet___redArg___closed__0));
v___f_212_ = ((lean_object*)(l_Lake_getVerbosity___redArg___closed__0));
v___f_213_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_214_ = lean_apply_4(v_map_210_, lean_box(0), lean_box(0), v___f_213_, v_inst_209_);
v___x_215_ = lean_apply_4(v_map_210_, lean_box(0), lean_box(0), v___f_212_, v___x_214_);
v___x_216_ = lean_apply_4(v_map_210_, lean_box(0), lean_box(0), v___f_211_, v___x_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsQuiet(lean_object* v_m_217_, lean_object* v_inst_218_, lean_object* v_inst_219_){
_start:
{
lean_object* v_map_220_; lean_object* v___f_221_; lean_object* v___f_222_; lean_object* v___f_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_map_220_ = lean_ctor_get(v_inst_218_, 0);
lean_inc_n(v_map_220_, 3);
lean_dec_ref(v_inst_218_);
v___f_221_ = ((lean_object*)(l_Lake_getIsQuiet___redArg___closed__0));
v___f_222_ = ((lean_object*)(l_Lake_getVerbosity___redArg___closed__0));
v___f_223_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_224_ = lean_apply_4(v_map_220_, lean_box(0), lean_box(0), v___f_223_, v_inst_219_);
v___x_225_ = lean_apply_4(v_map_220_, lean_box(0), lean_box(0), v___f_222_, v___x_224_);
v___x_226_ = lean_apply_4(v_map_220_, lean_box(0), lean_box(0), v___f_221_, v___x_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanOptOverrides___redArg___lam__0(lean_object* v_x_227_){
_start:
{
lean_object* v_leanOptOverrides_228_; 
v_leanOptOverrides_228_ = lean_ctor_get(v_x_227_, 3);
lean_inc(v_leanOptOverrides_228_);
return v_leanOptOverrides_228_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanOptOverrides___redArg___lam__0___boxed(lean_object* v_x_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lake_getLeanOptOverrides___redArg___lam__0(v_x_229_);
lean_dec_ref(v_x_229_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanOptOverrides___redArg(lean_object* v_inst_232_, lean_object* v_inst_233_){
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
LEAN_EXPORT lean_object* l_Lake_getLeanOptOverrides(lean_object* v_m_239_, lean_object* v_inst_240_, lean_object* v_inst_241_){
_start:
{
lean_object* v_map_242_; lean_object* v___f_243_; lean_object* v___f_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v_map_242_ = lean_ctor_get(v_inst_240_, 0);
lean_inc_n(v_map_242_, 2);
lean_dec_ref(v_inst_240_);
v___f_243_ = ((lean_object*)(l_Lake_getLeanOptOverrides___redArg___closed__0));
v___f_244_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_245_ = lean_apply_4(v_map_242_, lean_box(0), lean_box(0), v___f_244_, v_inst_241_);
v___x_246_ = lean_apply_4(v_map_242_, lean_box(0), lean_box(0), v___f_243_, v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lake_getMacOSXDeploymentTarget_x3f___redArg___lam__0(lean_object* v_x_247_){
_start:
{
lean_object* v_macosxDeploymentTarget_x3f_248_; 
v_macosxDeploymentTarget_x3f_248_ = lean_ctor_get(v_x_247_, 4);
lean_inc(v_macosxDeploymentTarget_x3f_248_);
return v_macosxDeploymentTarget_x3f_248_;
}
}
LEAN_EXPORT lean_object* l_Lake_getMacOSXDeploymentTarget_x3f___redArg___lam__0___boxed(lean_object* v_x_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lake_getMacOSXDeploymentTarget_x3f___redArg___lam__0(v_x_249_);
lean_dec_ref(v_x_249_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lake_getMacOSXDeploymentTarget_x3f___redArg(lean_object* v_inst_252_, lean_object* v_inst_253_){
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
LEAN_EXPORT lean_object* l_Lake_getMacOSXDeploymentTarget_x3f(lean_object* v_m_259_, lean_object* v_inst_260_, lean_object* v_inst_261_){
_start:
{
lean_object* v_map_262_; lean_object* v___f_263_; lean_object* v___f_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v_map_262_ = lean_ctor_get(v_inst_260_, 0);
lean_inc_n(v_map_262_, 2);
lean_dec_ref(v_inst_260_);
v___f_263_ = ((lean_object*)(l_Lake_getMacOSXDeploymentTarget_x3f___redArg___closed__0));
v___f_264_ = ((lean_object*)(l_Lake_getBuildConfig___redArg___closed__0));
v___x_265_ = lean_apply_4(v_map_262_, lean_box(0), lean_box(0), v___f_264_, v_inst_261_);
v___x_266_ = lean_apply_4(v_map_262_, lean_box(0), lean_box(0), v___f_263_, v___x_265_);
return v___x_266_;
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
