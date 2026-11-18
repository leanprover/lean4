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
uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Store_0__Lake_BuildStoreRef_storeAndReturn___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Store_0__Lake_BuildStoreRef_storeAndReturn___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Store_0__Lake_BuildStoreRef_storeAndReturn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Store_0__Lake_BuildStoreRef_storeAndReturn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Store_0__Lake_BuildStoreRef_storeAndReturn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Store_0__Lake_BuildStoreRef_storeAndReturn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_fetchOrCreate___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_fetchOrCreate___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_fetchOrCreate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_fetchOrCreate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_173_ = lean_st_ref_take(v_x_171_);
v___x_174_ = ((lean_object*)(l_Lake_BuildStoreRef_fetch_x3f___redArg___lam__0___closed__0));
lean_inc(v___x_173_);
lean_inc_ref(v_k_169_);
v___x_175_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___x_174_, v_k_169_, v___x_173_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_174_, v_k_169_, v_v_170_, v___x_173_);
v___x_177_ = lean_st_ref_put(v_x_171_, v___x_176_);
return v___x_177_;
}
else
{
lean_object* v___x_178_; 
lean_dec_ref(v_v_170_);
lean_dec_ref(v_k_169_);
v___x_178_ = lean_st_ref_put(v_x_171_, v___x_173_);
return v___x_178_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_store___redArg___lam__0___boxed(lean_object* v_k_179_, lean_object* v_v_180_, lean_object* v_x_181_, lean_object* v___y_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lake_BuildStoreRef_store___redArg___lam__0(v_k_179_, v_v_180_, v_x_181_);
lean_dec(v_x_181_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_store___redArg(lean_object* v_k_184_, lean_object* v_v_185_, lean_object* v_r_186_){
_start:
{
lean_object* v___f_188_; lean_object* v___x_189_; lean_object* v___f_190_; lean_object* v___x_191_; lean_object* v___x_72__overap_192_; lean_object* v___x_193_; 
v___f_188_ = lean_alloc_closure((void*)(l_Lake_BuildStoreRef_store___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_188_, 0, v_k_184_);
lean_closure_set(v___f_188_, 1, v_v_185_);
v___x_189_ = l_instMonadBaseIO;
v___f_190_ = ((lean_object*)(l_Lake_BuildStoreRef_modify___closed__0));
v___x_191_ = ((lean_object*)(l_Lake_BuildStoreRef_modify___closed__1));
v___x_72__overap_192_ = l_Std_Mutex_atomically___redArg(v___x_189_, v___f_190_, v___x_191_, v_r_186_, v___f_188_);
v___x_193_ = lean_apply_1(v___x_72__overap_192_, lean_box(0));
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_store___redArg___boxed(lean_object* v_k_194_, lean_object* v_v_195_, lean_object* v_r_196_, lean_object* v_a_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lake_BuildStoreRef_store___redArg(v_k_194_, v_v_195_, v_r_196_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_store(lean_object* v_00_u03b1_199_, lean_object* v_k_200_, lean_object* v_inst_201_, lean_object* v_v_202_, lean_object* v_r_203_){
_start:
{
lean_object* v___f_205_; lean_object* v___x_206_; lean_object* v___f_207_; lean_object* v___x_208_; lean_object* v___x_90__overap_209_; lean_object* v___x_210_; 
v___f_205_ = lean_alloc_closure((void*)(l_Lake_BuildStoreRef_store___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_205_, 0, v_k_200_);
lean_closure_set(v___f_205_, 1, v_v_202_);
v___x_206_ = l_instMonadBaseIO;
v___f_207_ = ((lean_object*)(l_Lake_BuildStoreRef_modify___closed__0));
v___x_208_ = ((lean_object*)(l_Lake_BuildStoreRef_modify___closed__1));
v___x_90__overap_209_ = l_Std_Mutex_atomically___redArg(v___x_206_, v___f_207_, v___x_208_, v_r_203_, v___f_205_);
v___x_210_ = lean_apply_1(v___x_90__overap_209_, lean_box(0));
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_store___boxed(lean_object* v_00_u03b1_211_, lean_object* v_k_212_, lean_object* v_inst_213_, lean_object* v_v_214_, lean_object* v_r_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lake_BuildStoreRef_store(v_00_u03b1_211_, v_k_212_, v_inst_213_, v_v_214_, v_r_215_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Store_0__Lake_BuildStoreRef_storeAndReturn___redArg___lam__0(lean_object* v_k_218_, lean_object* v_v_219_, lean_object* v_x_220_){
_start:
{
lean_object* v___x_222_; lean_object* v_fst_224_; lean_object* v_snd_225_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_222_ = lean_st_ref_take(v_x_220_);
v___x_227_ = ((lean_object*)(l_Lake_BuildStoreRef_fetch_x3f___redArg___lam__0___closed__0));
lean_inc_ref(v_k_218_);
lean_inc(v___x_222_);
v___x_228_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_227_, v___x_222_, v_k_218_);
if (lean_obj_tag(v___x_228_) == 0)
{
uint8_t v___x_229_; 
lean_inc(v___x_222_);
lean_inc_ref(v_k_218_);
v___x_229_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___x_227_, v_k_218_, v___x_222_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; 
lean_inc_ref(v_v_219_);
v___x_230_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_227_, v_k_218_, v_v_219_, v___x_222_);
v_fst_224_ = v_v_219_;
v_snd_225_ = v___x_230_;
goto v___jp_223_;
}
else
{
lean_dec_ref(v_k_218_);
v_fst_224_ = v_v_219_;
v_snd_225_ = v___x_222_;
goto v___jp_223_;
}
}
else
{
lean_object* v_val_231_; 
lean_dec_ref(v_v_219_);
lean_dec_ref(v_k_218_);
v_val_231_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_val_231_);
lean_dec_ref_known(v___x_228_, 1);
v_fst_224_ = v_val_231_;
v_snd_225_ = v___x_222_;
goto v___jp_223_;
}
v___jp_223_:
{
lean_object* v___x_226_; 
v___x_226_ = lean_st_ref_put(v_x_220_, v_snd_225_);
return v_fst_224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Store_0__Lake_BuildStoreRef_storeAndReturn___redArg___lam__0___boxed(lean_object* v_k_232_, lean_object* v_v_233_, lean_object* v_x_234_, lean_object* v___y_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l___private_Lake_Build_Store_0__Lake_BuildStoreRef_storeAndReturn___redArg___lam__0(v_k_232_, v_v_233_, v_x_234_);
lean_dec(v_x_234_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Store_0__Lake_BuildStoreRef_storeAndReturn___redArg(lean_object* v_k_237_, lean_object* v_v_238_, lean_object* v_r_239_){
_start:
{
lean_object* v___f_241_; lean_object* v___x_242_; lean_object* v___f_243_; lean_object* v___x_244_; lean_object* v___x_151__overap_245_; lean_object* v___x_246_; 
v___f_241_ = lean_alloc_closure((void*)(l___private_Lake_Build_Store_0__Lake_BuildStoreRef_storeAndReturn___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_241_, 0, v_k_237_);
lean_closure_set(v___f_241_, 1, v_v_238_);
v___x_242_ = l_instMonadBaseIO;
v___f_243_ = ((lean_object*)(l_Lake_BuildStoreRef_modify___closed__0));
v___x_244_ = ((lean_object*)(l_Lake_BuildStoreRef_modify___closed__1));
v___x_151__overap_245_ = l_Std_Mutex_atomically___redArg(v___x_242_, v___f_243_, v___x_244_, v_r_239_, v___f_241_);
v___x_246_ = lean_apply_1(v___x_151__overap_245_, lean_box(0));
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Store_0__Lake_BuildStoreRef_storeAndReturn___redArg___boxed(lean_object* v_k_247_, lean_object* v_v_248_, lean_object* v_r_249_, lean_object* v_a_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l___private_Lake_Build_Store_0__Lake_BuildStoreRef_storeAndReturn___redArg(v_k_247_, v_v_248_, v_r_249_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Store_0__Lake_BuildStoreRef_storeAndReturn(lean_object* v_00_u03b1_252_, lean_object* v_k_253_, lean_object* v_inst_254_, lean_object* v_v_255_, lean_object* v_r_256_){
_start:
{
lean_object* v___f_258_; lean_object* v___x_259_; lean_object* v___f_260_; lean_object* v___x_261_; lean_object* v___x_188__overap_262_; lean_object* v___x_263_; 
v___f_258_ = lean_alloc_closure((void*)(l___private_Lake_Build_Store_0__Lake_BuildStoreRef_storeAndReturn___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_258_, 0, v_k_253_);
lean_closure_set(v___f_258_, 1, v_v_255_);
v___x_259_ = l_instMonadBaseIO;
v___f_260_ = ((lean_object*)(l_Lake_BuildStoreRef_modify___closed__0));
v___x_261_ = ((lean_object*)(l_Lake_BuildStoreRef_modify___closed__1));
v___x_188__overap_262_ = l_Std_Mutex_atomically___redArg(v___x_259_, v___f_260_, v___x_261_, v_r_256_, v___f_258_);
v___x_263_ = lean_apply_1(v___x_188__overap_262_, lean_box(0));
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Store_0__Lake_BuildStoreRef_storeAndReturn___boxed(lean_object* v_00_u03b1_264_, lean_object* v_k_265_, lean_object* v_inst_266_, lean_object* v_v_267_, lean_object* v_r_268_, lean_object* v_a_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l___private_Lake_Build_Store_0__Lake_BuildStoreRef_storeAndReturn(v_00_u03b1_264_, v_k_265_, v_inst_266_, v_v_267_, v_r_268_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_fetchOrCreate___redArg___lam__0(lean_object* v_k_271_, lean_object* v_r_272_, lean_object* v_inst_273_, lean_object* v_val_274_){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_alloc_closure((void*)(l___private_Lake_Build_Store_0__Lake_BuildStoreRef_storeAndReturn___boxed), 6, 5);
lean_closure_set(v___x_275_, 0, lean_box(0));
lean_closure_set(v___x_275_, 1, v_k_271_);
lean_closure_set(v___x_275_, 2, lean_box(0));
lean_closure_set(v___x_275_, 3, v_val_274_);
lean_closure_set(v___x_275_, 4, v_r_272_);
v___x_276_ = lean_apply_2(v_inst_273_, lean_box(0), v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_fetchOrCreate___redArg___lam__1(lean_object* v_toPure_277_, lean_object* v_toBind_278_, lean_object* v_create_279_, lean_object* v___f_280_, lean_object* v_____do__lift_281_){
_start:
{
if (lean_obj_tag(v_____do__lift_281_) == 1)
{
lean_object* v_val_282_; lean_object* v___x_283_; 
lean_dec(v___f_280_);
lean_dec(v_create_279_);
lean_dec(v_toBind_278_);
v_val_282_ = lean_ctor_get(v_____do__lift_281_, 0);
lean_inc(v_val_282_);
lean_dec_ref_known(v_____do__lift_281_, 1);
v___x_283_ = lean_apply_2(v_toPure_277_, lean_box(0), v_val_282_);
return v___x_283_;
}
else
{
lean_object* v___x_284_; 
lean_dec(v_____do__lift_281_);
lean_dec(v_toPure_277_);
v___x_284_ = lean_apply_4(v_toBind_278_, lean_box(0), lean_box(0), v_create_279_, v___f_280_);
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_fetchOrCreate___redArg(lean_object* v_inst_285_, lean_object* v_inst_286_, lean_object* v_k_287_, lean_object* v_create_288_, lean_object* v_r_289_){
_start:
{
lean_object* v_toApplicative_290_; lean_object* v_toBind_291_; lean_object* v_toPure_292_; lean_object* v___f_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___f_296_; lean_object* v___x_297_; 
v_toApplicative_290_ = lean_ctor_get(v_inst_285_, 0);
lean_inc_ref(v_toApplicative_290_);
v_toBind_291_ = lean_ctor_get(v_inst_285_, 1);
lean_inc_n(v_toBind_291_, 2);
lean_dec_ref(v_inst_285_);
v_toPure_292_ = lean_ctor_get(v_toApplicative_290_, 1);
lean_inc(v_toPure_292_);
lean_dec_ref(v_toApplicative_290_);
lean_inc(v_inst_286_);
lean_inc_ref(v_r_289_);
lean_inc_ref(v_k_287_);
v___f_293_ = lean_alloc_closure((void*)(l_Lake_BuildStoreRef_fetchOrCreate___redArg___lam__0), 4, 3);
lean_closure_set(v___f_293_, 0, v_k_287_);
lean_closure_set(v___f_293_, 1, v_r_289_);
lean_closure_set(v___f_293_, 2, v_inst_286_);
v___x_294_ = lean_alloc_closure((void*)(l_Lake_BuildStoreRef_fetch_x3f___boxed), 5, 4);
lean_closure_set(v___x_294_, 0, lean_box(0));
lean_closure_set(v___x_294_, 1, v_k_287_);
lean_closure_set(v___x_294_, 2, lean_box(0));
lean_closure_set(v___x_294_, 3, v_r_289_);
v___x_295_ = lean_apply_2(v_inst_286_, lean_box(0), v___x_294_);
v___f_296_ = lean_alloc_closure((void*)(l_Lake_BuildStoreRef_fetchOrCreate___redArg___lam__1), 5, 4);
lean_closure_set(v___f_296_, 0, v_toPure_292_);
lean_closure_set(v___f_296_, 1, v_toBind_291_);
lean_closure_set(v___f_296_, 2, v_create_288_);
lean_closure_set(v___f_296_, 3, v___f_293_);
v___x_297_ = lean_apply_4(v_toBind_291_, lean_box(0), lean_box(0), v___x_295_, v___f_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreRef_fetchOrCreate(lean_object* v_m_298_, lean_object* v_00_u03b1_299_, lean_object* v_inst_300_, lean_object* v_inst_301_, lean_object* v_k_302_, lean_object* v_inst_303_, lean_object* v_create_304_, lean_object* v_r_305_){
_start:
{
lean_object* v_toApplicative_306_; lean_object* v_toBind_307_; lean_object* v_toPure_308_; lean_object* v___f_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___f_312_; lean_object* v___x_313_; 
v_toApplicative_306_ = lean_ctor_get(v_inst_300_, 0);
lean_inc_ref(v_toApplicative_306_);
v_toBind_307_ = lean_ctor_get(v_inst_300_, 1);
lean_inc_n(v_toBind_307_, 2);
lean_dec_ref(v_inst_300_);
v_toPure_308_ = lean_ctor_get(v_toApplicative_306_, 1);
lean_inc(v_toPure_308_);
lean_dec_ref(v_toApplicative_306_);
lean_inc(v_inst_301_);
lean_inc_ref(v_r_305_);
lean_inc_ref(v_k_302_);
v___f_309_ = lean_alloc_closure((void*)(l_Lake_BuildStoreRef_fetchOrCreate___redArg___lam__0), 4, 3);
lean_closure_set(v___f_309_, 0, v_k_302_);
lean_closure_set(v___f_309_, 1, v_r_305_);
lean_closure_set(v___f_309_, 2, v_inst_301_);
v___x_310_ = lean_alloc_closure((void*)(l_Lake_BuildStoreRef_fetch_x3f___boxed), 5, 4);
lean_closure_set(v___x_310_, 0, lean_box(0));
lean_closure_set(v___x_310_, 1, v_k_302_);
lean_closure_set(v___x_310_, 2, lean_box(0));
lean_closure_set(v___x_310_, 3, v_r_305_);
v___x_311_ = lean_apply_2(v_inst_301_, lean_box(0), v___x_310_);
v___f_312_ = lean_alloc_closure((void*)(l_Lake_BuildStoreRef_fetchOrCreate___redArg___lam__1), 5, 4);
lean_closure_set(v___f_312_, 0, v_toPure_308_);
lean_closure_set(v___f_312_, 1, v_toBind_307_);
lean_closure_set(v___f_312_, 2, v_create_304_);
lean_closure_set(v___f_312_, 3, v___f_309_);
v___x_313_ = lean_apply_4(v_toBind_307_, lean_box(0), lean_box(0), v___x_311_, v___f_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreT_run___redArg___lam__0(lean_object* v_a_314_, lean_object* v_toPure_315_, lean_object* v_s_316_){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v_a_314_);
lean_ctor_set(v___x_317_, 1, v_s_316_);
v___x_318_ = lean_apply_2(v_toPure_315_, lean_box(0), v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreT_run___redArg___lam__1(lean_object* v_toPure_319_, lean_object* v_ref_320_, lean_object* v_inst_321_, lean_object* v_toBind_322_, lean_object* v_a_323_){
_start:
{
lean_object* v___f_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___f_324_ = lean_alloc_closure((void*)(l_Lake_BuildStoreT_run___redArg___lam__0), 3, 2);
lean_closure_set(v___f_324_, 0, v_a_323_);
lean_closure_set(v___f_324_, 1, v_toPure_319_);
v___x_325_ = lean_alloc_closure((void*)(l_Lake_BuildStoreRef_get___boxed), 2, 1);
lean_closure_set(v___x_325_, 0, v_ref_320_);
v___x_326_ = lean_apply_2(v_inst_321_, lean_box(0), v___x_325_);
v___x_327_ = lean_apply_4(v_toBind_322_, lean_box(0), lean_box(0), v___x_326_, v___f_324_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreT_run___redArg___lam__2(lean_object* v_toPure_328_, lean_object* v_inst_329_, lean_object* v_toBind_330_, lean_object* v_x_331_, lean_object* v_ref_332_){
_start:
{
lean_object* v___f_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
lean_inc(v_toBind_330_);
lean_inc_ref(v_ref_332_);
v___f_333_ = lean_alloc_closure((void*)(l_Lake_BuildStoreT_run___redArg___lam__1), 5, 4);
lean_closure_set(v___f_333_, 0, v_toPure_328_);
lean_closure_set(v___f_333_, 1, v_ref_332_);
lean_closure_set(v___f_333_, 2, v_inst_329_);
lean_closure_set(v___f_333_, 3, v_toBind_330_);
v___x_334_ = lean_apply_1(v_x_331_, v_ref_332_);
v___x_335_ = lean_apply_4(v_toBind_330_, lean_box(0), lean_box(0), v___x_334_, v___f_333_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreT_run___redArg(lean_object* v_inst_336_, lean_object* v_inst_337_, lean_object* v_s_338_, lean_object* v_x_339_){
_start:
{
lean_object* v_toApplicative_340_; lean_object* v_toBind_341_; lean_object* v_toPure_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___f_345_; lean_object* v___x_346_; 
v_toApplicative_340_ = lean_ctor_get(v_inst_336_, 0);
lean_inc_ref(v_toApplicative_340_);
v_toBind_341_ = lean_ctor_get(v_inst_336_, 1);
lean_inc_n(v_toBind_341_, 2);
lean_dec_ref(v_inst_336_);
v_toPure_342_ = lean_ctor_get(v_toApplicative_340_, 1);
lean_inc(v_toPure_342_);
lean_dec_ref(v_toApplicative_340_);
v___x_343_ = lean_alloc_closure((void*)(l_Lake_BuildStoreRef_new___boxed), 2, 1);
lean_closure_set(v___x_343_, 0, v_s_338_);
lean_inc(v_inst_337_);
v___x_344_ = lean_apply_2(v_inst_337_, lean_box(0), v___x_343_);
v___f_345_ = lean_alloc_closure((void*)(l_Lake_BuildStoreT_run___redArg___lam__2), 5, 4);
lean_closure_set(v___f_345_, 0, v_toPure_342_);
lean_closure_set(v___f_345_, 1, v_inst_337_);
lean_closure_set(v___f_345_, 2, v_toBind_341_);
lean_closure_set(v___f_345_, 3, v_x_339_);
v___x_346_ = lean_apply_4(v_toBind_341_, lean_box(0), lean_box(0), v___x_344_, v___f_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStoreT_run(lean_object* v_m_347_, lean_object* v_00_u03b1_348_, lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_s_351_, lean_object* v_x_352_){
_start:
{
lean_object* v_toApplicative_353_; lean_object* v_toBind_354_; lean_object* v_toPure_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___f_358_; lean_object* v___x_359_; 
v_toApplicative_353_ = lean_ctor_get(v_inst_349_, 0);
lean_inc_ref(v_toApplicative_353_);
v_toBind_354_ = lean_ctor_get(v_inst_349_, 1);
lean_inc_n(v_toBind_354_, 2);
lean_dec_ref(v_inst_349_);
v_toPure_355_ = lean_ctor_get(v_toApplicative_353_, 1);
lean_inc(v_toPure_355_);
lean_dec_ref(v_toApplicative_353_);
v___x_356_ = lean_alloc_closure((void*)(l_Lake_BuildStoreRef_new___boxed), 2, 1);
lean_closure_set(v___x_356_, 0, v_s_351_);
lean_inc(v_inst_350_);
v___x_357_ = lean_apply_2(v_inst_350_, lean_box(0), v___x_356_);
v___f_358_ = lean_alloc_closure((void*)(l_Lake_BuildStoreT_run___redArg___lam__2), 5, 4);
lean_closure_set(v___f_358_, 0, v_toPure_355_);
lean_closure_set(v___f_358_, 1, v_inst_350_);
lean_closure_set(v___f_358_, 2, v_toBind_354_);
lean_closure_set(v___f_358_, 3, v_x_352_);
v___x_359_ = lean_apply_4(v_toBind_354_, lean_box(0), lean_box(0), v___x_357_, v___f_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadBuildStoreBuildStoreTOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_360_, lean_object* v_k_361_, lean_object* v_r_362_){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = lean_alloc_closure((void*)(l_Lake_BuildStoreRef_fetch_x3f___boxed), 5, 4);
lean_closure_set(v___x_363_, 0, lean_box(0));
lean_closure_set(v___x_363_, 1, v_k_361_);
lean_closure_set(v___x_363_, 2, lean_box(0));
lean_closure_set(v___x_363_, 3, v_r_362_);
v___x_364_ = lean_apply_2(v_inst_360_, lean_box(0), v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadBuildStoreBuildStoreTOfMonadOfMonadLiftTBaseIO___redArg___lam__1(lean_object* v_inst_365_, lean_object* v_k_366_, lean_object* v_v_367_, lean_object* v_r_368_){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = lean_alloc_closure((void*)(l_Lake_BuildStoreRef_store___boxed), 6, 5);
lean_closure_set(v___x_369_, 0, lean_box(0));
lean_closure_set(v___x_369_, 1, v_k_366_);
lean_closure_set(v___x_369_, 2, lean_box(0));
lean_closure_set(v___x_369_, 3, v_v_367_);
lean_closure_set(v___x_369_, 4, v_r_368_);
v___x_370_ = lean_apply_2(v_inst_365_, lean_box(0), v___x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadBuildStoreBuildStoreTOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_371_){
_start:
{
lean_object* v___f_372_; lean_object* v___f_373_; lean_object* v___x_374_; 
lean_inc(v_inst_371_);
v___f_372_ = lean_alloc_closure((void*)(l_Lake_instMonadBuildStoreBuildStoreTOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 3, 1);
lean_closure_set(v___f_372_, 0, v_inst_371_);
v___f_373_ = lean_alloc_closure((void*)(l_Lake_instMonadBuildStoreBuildStoreTOfMonadOfMonadLiftTBaseIO___redArg___lam__1), 4, 1);
lean_closure_set(v___f_373_, 0, v_inst_371_);
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v___f_372_);
lean_ctor_set(v___x_374_, 1, v___f_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadBuildStoreBuildStoreTOfMonadOfMonadLiftTBaseIO(lean_object* v_m_375_, lean_object* v_inst_376_, lean_object* v_inst_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lake_instMonadBuildStoreBuildStoreTOfMonadOfMonadLiftTBaseIO___redArg(v_inst_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadBuildStoreBuildStoreTOfMonadOfMonadLiftTBaseIO___boxed(lean_object* v_m_379_, lean_object* v_inst_380_, lean_object* v_inst_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lake_instMonadBuildStoreBuildStoreTOfMonadOfMonadLiftTBaseIO(v_m_379_, v_inst_380_, v_inst_381_);
lean_dec_ref(v_inst_380_);
return v_res_382_;
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
