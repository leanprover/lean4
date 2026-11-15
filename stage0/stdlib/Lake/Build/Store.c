// Lean compiler output
// Module: Lake.Build.Store
// Imports: public import Lake.Util.Store public import Lake.Build.Job.Basic public import Std.Sync.Mutex
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
extern lean_object* l_instMonadBaseIO;
lean_object* l_instMonadLiftT___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadFinallyBaseIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Mutex_atomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lake_BuildKey_quickCmp___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Mutex_new___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStore_empty;
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_new(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_new___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_modify___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_modify___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_BuildStoreRef_modify___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_BuildStoreRef_modify___closed__0 = (const lean_object*)&l_Lake_BuildStoreRef_modify___closed__0_value;
static const lean_closure_object l_Lake_BuildStoreRef_modify___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadFinallyBaseIO___aux__1___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_BuildStoreRef_modify___closed__1 = (const lean_object*)&l_Lake_BuildStoreRef_modify___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_modify(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_modify___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_modifyGet___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_modifyGet___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_modifyGet___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_modifyGet___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_modifyGet(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_modifyGet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_get___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_get___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_BuildStoreRef_get___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_BuildStoreRef_get___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_BuildStoreRef_get___closed__0 = (const lean_object*)&l_Lake_BuildStoreRef_get___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_get(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_getMap___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_getMap___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_getMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_getMap___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_getMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_getMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_BuildStoreRef_fetch_x3f___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_BuildKey_quickCmp___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_BuildStoreRef_fetch_x3f___redArg___lam__0___closed__0 = (const lean_object*)&l_Lake_BuildStoreRef_fetch_x3f___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_fetch_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_fetch_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_fetch_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_fetch_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_fetch_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_fetch_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_store___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_store___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_store___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_store___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_store(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_store___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreT_run___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreT_run___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreT_run___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreT_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreT_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadBuildStoreBuildStoreTOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadBuildStoreBuildStoreTOfMonadOfMonadLiftTBaseIO___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadBuildStoreBuildStoreTOfMonadOfMonadLiftTBaseIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadBuildStoreBuildStoreTOfMonadOfMonadLiftTBaseIO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadBuildStoreBuildStoreTOfMonadOfMonadLiftTBaseIO___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lake_BuildStore_empty(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(1);
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_new(lean_object* v_s_2_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = l_Std_Mutex_new___redArg(v_s_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_new___boxed(lean_object* v_s_5_, lean_object* v_a_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Lake_BuildStoreRef_new(v_s_5_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_modify___lam__0(lean_object* v_f_8_, lean_object* v_x_9_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_11_ = lean_st_ref_take(v_x_9_);
v___x_12_ = lean_apply_1(v_f_8_, v___x_11_);
v___x_13_ = lean_st_ref_put(v_x_9_, v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_modify___lam__0___boxed(lean_object* v_f_14_, lean_object* v_x_15_, lean_object* v___y_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Lake_BuildStoreRef_modify___lam__0(v_f_14_, v_x_15_);
lean_dec(v_x_15_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_modify(lean_object* v_f_20_, lean_object* v_r_21_){
_start:
{
lean_object* v___f_23_; lean_object* v___x_24_; lean_object* v___f_25_; lean_object* v___x_26_; lean_object* v___x_45__overap_27_; lean_object* v___x_28_; 
v___f_23_ = lean_alloc_closure((void*)(l_Lake_BuildStoreRef_modify___lam__0___boxed), 3, 1);
lean_closure_set(v___f_23_, 0, v_f_20_);
v___x_24_ = l_instMonadBaseIO;
v___f_25_ = ((lean_object*)(l_Lake_BuildStoreRef_modify___closed__0));
v___x_26_ = ((lean_object*)(l_Lake_BuildStoreRef_modify___closed__1));
v___x_45__overap_27_ = l_Std_Mutex_atomically___redArg(v___x_24_, v___f_25_, v___x_26_, v_r_21_, v___f_23_);
v___x_28_ = lean_apply_1(v___x_45__overap_27_, lean_box(0));
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_modify___boxed(lean_object* v_f_29_, lean_object* v_r_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lake_BuildStoreRef_modify(v_f_29_, v_r_30_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_modifyGet___redArg___lam__0(lean_object* v_f_33_, lean_object* v_x_34_){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v_fst_38_; lean_object* v_snd_39_; lean_object* v___x_40_; 
v___x_36_ = lean_st_ref_take(v_x_34_);
v___x_37_ = lean_apply_1(v_f_33_, v___x_36_);
v_fst_38_ = lean_ctor_get(v___x_37_, 0);
lean_inc(v_fst_38_);
v_snd_39_ = lean_ctor_get(v___x_37_, 1);
lean_inc(v_snd_39_);
lean_dec_ref(v___x_37_);
v___x_40_ = lean_st_ref_put(v_x_34_, v_snd_39_);
return v_fst_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_modifyGet___redArg___lam__0___boxed(lean_object* v_f_41_, lean_object* v_x_42_, lean_object* v___y_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lake_BuildStoreRef_modifyGet___redArg___lam__0(v_f_41_, v_x_42_);
lean_dec(v_x_42_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_modifyGet___redArg(lean_object* v_f_45_, lean_object* v_r_46_){
_start:
{
lean_object* v___f_48_; lean_object* v___x_49_; lean_object* v___f_50_; lean_object* v___x_51_; lean_object* v___x_55__overap_52_; lean_object* v___x_53_; 
v___f_48_ = lean_alloc_closure((void*)(l_Lake_BuildStoreRef_modifyGet___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_48_, 0, v_f_45_);
v___x_49_ = l_instMonadBaseIO;
v___f_50_ = ((lean_object*)(l_Lake_BuildStoreRef_modify___closed__0));
v___x_51_ = ((lean_object*)(l_Lake_BuildStoreRef_modify___closed__1));
v___x_55__overap_52_ = l_Std_Mutex_atomically___redArg(v___x_49_, v___f_50_, v___x_51_, v_r_46_, v___f_48_);
v___x_53_ = lean_apply_1(v___x_55__overap_52_, lean_box(0));
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_modifyGet___redArg___boxed(lean_object* v_f_54_, lean_object* v_r_55_, lean_object* v_a_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lake_BuildStoreRef_modifyGet___redArg(v_f_54_, v_r_55_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_modifyGet(lean_object* v_00_u03b1_58_, lean_object* v_f_59_, lean_object* v_r_60_){
_start:
{
lean_object* v___f_62_; lean_object* v___x_63_; lean_object* v___f_64_; lean_object* v___x_65_; lean_object* v___x_74__overap_66_; lean_object* v___x_67_; 
v___f_62_ = lean_alloc_closure((void*)(l_Lake_BuildStoreRef_modifyGet___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_62_, 0, v_f_59_);
v___x_63_ = l_instMonadBaseIO;
v___f_64_ = ((lean_object*)(l_Lake_BuildStoreRef_modify___closed__0));
v___x_65_ = ((lean_object*)(l_Lake_BuildStoreRef_modify___closed__1));
v___x_74__overap_66_ = l_Std_Mutex_atomically___redArg(v___x_63_, v___f_64_, v___x_65_, v_r_60_, v___f_62_);
v___x_67_ = lean_apply_1(v___x_74__overap_66_, lean_box(0));
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_modifyGet___boxed(lean_object* v_00_u03b1_68_, lean_object* v_f_69_, lean_object* v_r_70_, lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lake_BuildStoreRef_modifyGet(v_00_u03b1_68_, v_f_69_, v_r_70_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_get___lam__0(lean_object* v_x_73_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_st_ref_get(v_x_73_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_get___lam__0___boxed(lean_object* v_x_76_, lean_object* v___y_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lake_BuildStoreRef_get___lam__0(v_x_76_);
lean_dec(v_x_76_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_get(lean_object* v_r_80_){
_start:
{
lean_object* v___f_82_; lean_object* v___x_83_; lean_object* v___f_84_; lean_object* v___x_85_; lean_object* v___x_36__overap_86_; lean_object* v___x_87_; 
v___f_82_ = ((lean_object*)(l_Lake_BuildStoreRef_get___closed__0));
v___x_83_ = l_instMonadBaseIO;
v___f_84_ = ((lean_object*)(l_Lake_BuildStoreRef_modify___closed__0));
v___x_85_ = ((lean_object*)(l_Lake_BuildStoreRef_modify___closed__1));
v___x_36__overap_86_ = l_Std_Mutex_atomically___redArg(v___x_83_, v___f_84_, v___x_85_, v_r_80_, v___f_82_);
v___x_87_ = lean_apply_1(v___x_36__overap_86_, lean_box(0));
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_get___boxed(lean_object* v_r_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lake_BuildStoreRef_get(v_r_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_getMap___redArg___lam__0(lean_object* v_f_91_, lean_object* v_ref_92_){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_st_ref_get(v_ref_92_);
v___x_95_ = lean_apply_1(v_f_91_, v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_getMap___redArg___lam__0___boxed(lean_object* v_f_96_, lean_object* v_ref_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lake_BuildStoreRef_getMap___redArg___lam__0(v_f_96_, v_ref_97_);
lean_dec(v_ref_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_getMap___redArg(lean_object* v_f_100_, lean_object* v_r_101_){
_start:
{
lean_object* v___f_103_; lean_object* v___x_104_; lean_object* v___f_105_; lean_object* v___x_106_; lean_object* v___x_84__overap_107_; lean_object* v___x_108_; 
v___f_103_ = lean_alloc_closure((void*)(l_Lake_BuildStoreRef_getMap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_103_, 0, v_f_100_);
v___x_104_ = l_instMonadBaseIO;
v___f_105_ = ((lean_object*)(l_Lake_BuildStoreRef_modify___closed__0));
v___x_106_ = ((lean_object*)(l_Lake_BuildStoreRef_modify___closed__1));
v___x_84__overap_107_ = l_Std_Mutex_atomically___redArg(v___x_104_, v___f_105_, v___x_106_, v_r_101_, v___f_103_);
v___x_108_ = lean_apply_1(v___x_84__overap_107_, lean_box(0));
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_getMap___redArg___boxed(lean_object* v_f_109_, lean_object* v_r_110_, lean_object* v_a_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lake_BuildStoreRef_getMap___redArg(v_f_109_, v_r_110_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_getMap(lean_object* v_00_u03b1_113_, lean_object* v_f_114_, lean_object* v_r_115_){
_start:
{
lean_object* v___f_117_; lean_object* v___x_118_; lean_object* v___f_119_; lean_object* v___x_120_; lean_object* v___x_97__overap_121_; lean_object* v___x_122_; 
v___f_117_ = lean_alloc_closure((void*)(l_Lake_BuildStoreRef_getMap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_117_, 0, v_f_114_);
v___x_118_ = l_instMonadBaseIO;
v___f_119_ = ((lean_object*)(l_Lake_BuildStoreRef_modify___closed__0));
v___x_120_ = ((lean_object*)(l_Lake_BuildStoreRef_modify___closed__1));
v___x_97__overap_121_ = l_Std_Mutex_atomically___redArg(v___x_118_, v___f_119_, v___x_120_, v_r_115_, v___f_117_);
v___x_122_ = lean_apply_1(v___x_97__overap_121_, lean_box(0));
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_getMap___boxed(lean_object* v_00_u03b1_123_, lean_object* v_f_124_, lean_object* v_r_125_, lean_object* v_a_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lake_BuildStoreRef_getMap(v_00_u03b1_123_, v_f_124_, v_r_125_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_fetch_x3f___redArg___lam__0(lean_object* v_k_129_, lean_object* v_ref_130_){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_132_ = lean_st_ref_get(v_ref_130_);
v___x_133_ = ((lean_object*)(l_Lake_BuildStoreRef_fetch_x3f___redArg___lam__0___closed__0));
v___x_134_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_133_, v___x_132_, v_k_129_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_fetch_x3f___redArg___lam__0___boxed(lean_object* v_k_135_, lean_object* v_ref_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lake_BuildStoreRef_fetch_x3f___redArg___lam__0(v_k_135_, v_ref_136_);
lean_dec(v_ref_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_fetch_x3f___redArg(lean_object* v_k_139_, lean_object* v_r_140_){
_start:
{
lean_object* v___f_142_; lean_object* v___x_143_; lean_object* v___f_144_; lean_object* v___x_145_; lean_object* v___x_30__overap_146_; lean_object* v___x_147_; 
v___f_142_ = lean_alloc_closure((void*)(l_Lake_BuildStoreRef_fetch_x3f___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_142_, 0, v_k_139_);
v___x_143_ = l_instMonadBaseIO;
v___f_144_ = ((lean_object*)(l_Lake_BuildStoreRef_modify___closed__0));
v___x_145_ = ((lean_object*)(l_Lake_BuildStoreRef_modify___closed__1));
v___x_30__overap_146_ = l_Std_Mutex_atomically___redArg(v___x_143_, v___f_144_, v___x_145_, v_r_140_, v___f_142_);
v___x_147_ = lean_apply_1(v___x_30__overap_146_, lean_box(0));
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_fetch_x3f___redArg___boxed(lean_object* v_k_148_, lean_object* v_r_149_, lean_object* v_a_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lake_BuildStoreRef_fetch_x3f___redArg(v_k_148_, v_r_149_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_fetch_x3f(lean_object* v_00_u03b1_152_, lean_object* v_k_153_, lean_object* v_inst_154_, lean_object* v_r_155_){
_start:
{
lean_object* v___f_157_; lean_object* v___x_158_; lean_object* v___f_159_; lean_object* v___x_160_; lean_object* v___x_45__overap_161_; lean_object* v___x_162_; 
v___f_157_ = lean_alloc_closure((void*)(l_Lake_BuildStoreRef_fetch_x3f___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_157_, 0, v_k_153_);
v___x_158_ = l_instMonadBaseIO;
v___f_159_ = ((lean_object*)(l_Lake_BuildStoreRef_modify___closed__0));
v___x_160_ = ((lean_object*)(l_Lake_BuildStoreRef_modify___closed__1));
v___x_45__overap_161_ = l_Std_Mutex_atomically___redArg(v___x_158_, v___f_159_, v___x_160_, v_r_155_, v___f_157_);
v___x_162_ = lean_apply_1(v___x_45__overap_161_, lean_box(0));
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_fetch_x3f___boxed(lean_object* v_00_u03b1_163_, lean_object* v_k_164_, lean_object* v_inst_165_, lean_object* v_r_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lake_BuildStoreRef_fetch_x3f(v_00_u03b1_163_, v_k_164_, v_inst_165_, v_r_166_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_store___redArg___lam__0(lean_object* v_k_169_, lean_object* v_v_170_, lean_object* v_x_171_){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_173_ = lean_st_ref_take(v_x_171_);
v___x_174_ = ((lean_object*)(l_Lake_BuildStoreRef_fetch_x3f___redArg___lam__0___closed__0));
v___x_175_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_174_, v_k_169_, v_v_170_, v___x_173_);
v___x_176_ = lean_st_ref_put(v_x_171_, v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_store___redArg___lam__0___boxed(lean_object* v_k_177_, lean_object* v_v_178_, lean_object* v_x_179_, lean_object* v___y_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lake_BuildStoreRef_store___redArg___lam__0(v_k_177_, v_v_178_, v_x_179_);
lean_dec(v_x_179_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_store___redArg(lean_object* v_k_182_, lean_object* v_v_183_, lean_object* v_r_184_){
_start:
{
lean_object* v___f_186_; lean_object* v___x_187_; lean_object* v___f_188_; lean_object* v___x_189_; lean_object* v___x_36__overap_190_; lean_object* v___x_191_; 
v___f_186_ = lean_alloc_closure((void*)(l_Lake_BuildStoreRef_store___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_186_, 0, v_k_182_);
lean_closure_set(v___f_186_, 1, v_v_183_);
v___x_187_ = l_instMonadBaseIO;
v___f_188_ = ((lean_object*)(l_Lake_BuildStoreRef_modify___closed__0));
v___x_189_ = ((lean_object*)(l_Lake_BuildStoreRef_modify___closed__1));
v___x_36__overap_190_ = l_Std_Mutex_atomically___redArg(v___x_187_, v___f_188_, v___x_189_, v_r_184_, v___f_186_);
v___x_191_ = lean_apply_1(v___x_36__overap_190_, lean_box(0));
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_store___redArg___boxed(lean_object* v_k_192_, lean_object* v_v_193_, lean_object* v_r_194_, lean_object* v_a_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lake_BuildStoreRef_store___redArg(v_k_192_, v_v_193_, v_r_194_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_store(lean_object* v_00_u03b1_197_, lean_object* v_k_198_, lean_object* v_inst_199_, lean_object* v_v_200_, lean_object* v_r_201_){
_start:
{
lean_object* v___f_203_; lean_object* v___x_204_; lean_object* v___f_205_; lean_object* v___x_206_; lean_object* v___x_52__overap_207_; lean_object* v___x_208_; 
v___f_203_ = lean_alloc_closure((void*)(l_Lake_BuildStoreRef_store___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_203_, 0, v_k_198_);
lean_closure_set(v___f_203_, 1, v_v_200_);
v___x_204_ = l_instMonadBaseIO;
v___f_205_ = ((lean_object*)(l_Lake_BuildStoreRef_modify___closed__0));
v___x_206_ = ((lean_object*)(l_Lake_BuildStoreRef_modify___closed__1));
v___x_52__overap_207_ = l_Std_Mutex_atomically___redArg(v___x_204_, v___f_205_, v___x_206_, v_r_201_, v___f_203_);
v___x_208_ = lean_apply_1(v___x_52__overap_207_, lean_box(0));
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_store___boxed(lean_object* v_00_u03b1_209_, lean_object* v_k_210_, lean_object* v_inst_211_, lean_object* v_v_212_, lean_object* v_r_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lake_BuildStoreRef_store(v_00_u03b1_209_, v_k_210_, v_inst_211_, v_v_212_, v_r_213_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreT_run___redArg___lam__0(lean_object* v_a_216_, lean_object* v_toPure_217_, lean_object* v_s_218_){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v_a_216_);
lean_ctor_set(v___x_219_, 1, v_s_218_);
v___x_220_ = lean_apply_2(v_toPure_217_, lean_box(0), v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreT_run___redArg___lam__1(lean_object* v_toPure_221_, lean_object* v_ref_222_, lean_object* v_inst_223_, lean_object* v_toBind_224_, lean_object* v_a_225_){
_start:
{
lean_object* v___f_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___f_226_ = lean_alloc_closure((void*)(l_Lake_BuildStoreT_run___redArg___lam__0), 3, 2);
lean_closure_set(v___f_226_, 0, v_a_225_);
lean_closure_set(v___f_226_, 1, v_toPure_221_);
v___x_227_ = lean_alloc_closure((void*)(l_Lake_BuildStoreRef_get___boxed), 2, 1);
lean_closure_set(v___x_227_, 0, v_ref_222_);
v___x_228_ = lean_apply_2(v_inst_223_, lean_box(0), v___x_227_);
v___x_229_ = lean_apply_4(v_toBind_224_, lean_box(0), lean_box(0), v___x_228_, v___f_226_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreT_run___redArg___lam__2(lean_object* v_toPure_230_, lean_object* v_inst_231_, lean_object* v_toBind_232_, lean_object* v_x_233_, lean_object* v_ref_234_){
_start:
{
lean_object* v___f_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
lean_inc(v_toBind_232_);
lean_inc_ref(v_ref_234_);
v___f_235_ = lean_alloc_closure((void*)(l_Lake_BuildStoreT_run___redArg___lam__1), 5, 4);
lean_closure_set(v___f_235_, 0, v_toPure_230_);
lean_closure_set(v___f_235_, 1, v_ref_234_);
lean_closure_set(v___f_235_, 2, v_inst_231_);
lean_closure_set(v___f_235_, 3, v_toBind_232_);
v___x_236_ = lean_apply_1(v_x_233_, v_ref_234_);
v___x_237_ = lean_apply_4(v_toBind_232_, lean_box(0), lean_box(0), v___x_236_, v___f_235_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreT_run___redArg(lean_object* v_inst_238_, lean_object* v_inst_239_, lean_object* v_s_240_, lean_object* v_x_241_){
_start:
{
lean_object* v_toApplicative_242_; lean_object* v_toBind_243_; lean_object* v_toPure_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___f_247_; lean_object* v___x_248_; 
v_toApplicative_242_ = lean_ctor_get(v_inst_238_, 0);
lean_inc_ref(v_toApplicative_242_);
v_toBind_243_ = lean_ctor_get(v_inst_238_, 1);
lean_inc_n(v_toBind_243_, 2);
lean_dec_ref(v_inst_238_);
v_toPure_244_ = lean_ctor_get(v_toApplicative_242_, 1);
lean_inc(v_toPure_244_);
lean_dec_ref(v_toApplicative_242_);
v___x_245_ = lean_alloc_closure((void*)(l_Lake_BuildStoreRef_new___boxed), 2, 1);
lean_closure_set(v___x_245_, 0, v_s_240_);
lean_inc(v_inst_239_);
v___x_246_ = lean_apply_2(v_inst_239_, lean_box(0), v___x_245_);
v___f_247_ = lean_alloc_closure((void*)(l_Lake_BuildStoreT_run___redArg___lam__2), 5, 4);
lean_closure_set(v___f_247_, 0, v_toPure_244_);
lean_closure_set(v___f_247_, 1, v_inst_239_);
lean_closure_set(v___f_247_, 2, v_toBind_243_);
lean_closure_set(v___f_247_, 3, v_x_241_);
v___x_248_ = lean_apply_4(v_toBind_243_, lean_box(0), lean_box(0), v___x_246_, v___f_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreT_run(lean_object* v_m_249_, lean_object* v_00_u03b1_250_, lean_object* v_inst_251_, lean_object* v_inst_252_, lean_object* v_s_253_, lean_object* v_x_254_){
_start:
{
lean_object* v_toApplicative_255_; lean_object* v_toBind_256_; lean_object* v_toPure_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___f_260_; lean_object* v___x_261_; 
v_toApplicative_255_ = lean_ctor_get(v_inst_251_, 0);
lean_inc_ref(v_toApplicative_255_);
v_toBind_256_ = lean_ctor_get(v_inst_251_, 1);
lean_inc_n(v_toBind_256_, 2);
lean_dec_ref(v_inst_251_);
v_toPure_257_ = lean_ctor_get(v_toApplicative_255_, 1);
lean_inc(v_toPure_257_);
lean_dec_ref(v_toApplicative_255_);
v___x_258_ = lean_alloc_closure((void*)(l_Lake_BuildStoreRef_new___boxed), 2, 1);
lean_closure_set(v___x_258_, 0, v_s_253_);
lean_inc(v_inst_252_);
v___x_259_ = lean_apply_2(v_inst_252_, lean_box(0), v___x_258_);
v___f_260_ = lean_alloc_closure((void*)(l_Lake_BuildStoreT_run___redArg___lam__2), 5, 4);
lean_closure_set(v___f_260_, 0, v_toPure_257_);
lean_closure_set(v___f_260_, 1, v_inst_252_);
lean_closure_set(v___f_260_, 2, v_toBind_256_);
lean_closure_set(v___f_260_, 3, v_x_254_);
v___x_261_ = lean_apply_4(v_toBind_256_, lean_box(0), lean_box(0), v___x_259_, v___f_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadBuildStoreBuildStoreTOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_262_, lean_object* v_k_263_, lean_object* v_r_264_){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_alloc_closure((void*)(l_Lake_BuildStoreRef_fetch_x3f___boxed), 5, 4);
lean_closure_set(v___x_265_, 0, lean_box(0));
lean_closure_set(v___x_265_, 1, v_k_263_);
lean_closure_set(v___x_265_, 2, lean_box(0));
lean_closure_set(v___x_265_, 3, v_r_264_);
v___x_266_ = lean_apply_2(v_inst_262_, lean_box(0), v___x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadBuildStoreBuildStoreTOfMonadOfMonadLiftTBaseIO___redArg___lam__1(lean_object* v_inst_267_, lean_object* v_k_268_, lean_object* v_v_269_, lean_object* v_r_270_){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = lean_alloc_closure((void*)(l_Lake_BuildStoreRef_store___boxed), 6, 5);
lean_closure_set(v___x_271_, 0, lean_box(0));
lean_closure_set(v___x_271_, 1, v_k_268_);
lean_closure_set(v___x_271_, 2, lean_box(0));
lean_closure_set(v___x_271_, 3, v_v_269_);
lean_closure_set(v___x_271_, 4, v_r_270_);
v___x_272_ = lean_apply_2(v_inst_267_, lean_box(0), v___x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadBuildStoreBuildStoreTOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_273_){
_start:
{
lean_object* v___f_274_; lean_object* v___f_275_; lean_object* v___x_276_; 
lean_inc(v_inst_273_);
v___f_274_ = lean_alloc_closure((void*)(l_Lake_instMonadBuildStoreBuildStoreTOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 3, 1);
lean_closure_set(v___f_274_, 0, v_inst_273_);
v___f_275_ = lean_alloc_closure((void*)(l_Lake_instMonadBuildStoreBuildStoreTOfMonadOfMonadLiftTBaseIO___redArg___lam__1), 4, 1);
lean_closure_set(v___f_275_, 0, v_inst_273_);
v___x_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_276_, 0, v___f_274_);
lean_ctor_set(v___x_276_, 1, v___f_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadBuildStoreBuildStoreTOfMonadOfMonadLiftTBaseIO(lean_object* v_m_277_, lean_object* v_inst_278_, lean_object* v_inst_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Lake_instMonadBuildStoreBuildStoreTOfMonadOfMonadLiftTBaseIO___redArg(v_inst_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadBuildStoreBuildStoreTOfMonadOfMonadLiftTBaseIO___boxed(lean_object* v_m_281_, lean_object* v_inst_282_, lean_object* v_inst_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lake_instMonadBuildStoreBuildStoreTOfMonadOfMonadLiftTBaseIO(v_m_281_, v_inst_282_, v_inst_283_);
lean_dec_ref(v_inst_282_);
return v_res_284_;
}
}
lean_object* runtime_initialize_Lake_Util_Store(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Job_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Sync_Mutex(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Store(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Util_Store(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Job_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sync_Mutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_BuildStore_empty = _init_l_Lake_BuildStore_empty();
lean_mark_persistent(l_Lake_BuildStore_empty);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_Store(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Util_Store(uint8_t builtin);
lean_object* initialize_Lake_Build_Job_Basic(uint8_t builtin);
lean_object* initialize_Std_Sync_Mutex(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Store(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Store(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sync_Mutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Store(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_Store(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_Store(builtin);
}
#ifdef __cplusplus
}
#endif
