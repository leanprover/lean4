// Lean compiler output
// Module: Std.Sync.RecursiveMutex
// Imports: public import Std.Sync.Basic
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
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_RecursiveMutex_0__Std_RecursiveMutexImpl;
lean_object* lean_io_baserecmutex_new();
LEAN_EXPORT lean_object* l_Std_BaseRecursiveMutex_new___boxed(lean_object*);
lean_object* lean_io_baserecmutex_lock(lean_object*);
LEAN_EXPORT lean_object* l_Std_BaseRecursiveMutex_lock___boxed(lean_object*, lean_object*);
uint8_t lean_io_baserecmutex_try_lock(lean_object*);
LEAN_EXPORT lean_object* l_Std_BaseRecursiveMutex_tryLock___boxed(lean_object*, lean_object*);
lean_object* lean_io_baserecmutex_unlock(lean_object*);
LEAN_EXPORT lean_object* l_Std_BaseRecursiveMutex_unlock___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___closed__0 = (const lean_object*)&l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex(lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_new___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_new___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_new(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_new___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_RecursiveMutex_atomically___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_RecursiveMutex_atomically___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_RecursiveMutex_atomically___redArg___closed__0 = (const lean_object*)&l_Std_RecursiveMutex_atomically___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_RecursiveMutex_tryAtomically___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_RecursiveMutex_tryAtomically___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___closed__0 = (const lean_object*)&l_Std_RecursiveMutex_tryAtomically___redArg___closed__0_value;
static const lean_closure_object l_Std_RecursiveMutex_tryAtomically___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_RecursiveMutex_tryAtomically___redArg___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___closed__1 = (const lean_object*)&l_Std_RecursiveMutex_tryAtomically___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Std_Sync_RecursiveMutex_0__Std_RecursiveMutexImpl(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_Std_BaseRecursiveMutex_new___boxed(lean_object* v_a_00___x40___internal___hyg_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lean_io_baserecmutex_new();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_BaseRecursiveMutex_lock___boxed(lean_object* v_mutex_7_, lean_object* v_a_00___x40___internal___hyg_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lean_io_baserecmutex_lock(v_mutex_7_);
lean_dec(v_mutex_7_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Std_BaseRecursiveMutex_tryLock___boxed(lean_object* v_mutex_12_, lean_object* v_a_00___x40___internal___hyg_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = lean_io_baserecmutex_try_lock(v_mutex_12_);
lean_dec(v_mutex_12_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT lean_object* l_Std_BaseRecursiveMutex_unlock___boxed(lean_object* v_mutex_18_, lean_object* v_a_00___x40___internal___hyg_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lean_io_baserecmutex_unlock(v_mutex_18_);
lean_dec(v_mutex_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___lam__0(lean_object* v_self_21_){
_start:
{
lean_object* v_mutex_22_; 
v_mutex_22_ = lean_ctor_get(v_self_21_, 1);
lean_inc(v_mutex_22_);
return v_mutex_22_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___lam__0___boxed(lean_object* v_self_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___lam__0(v_self_23_);
lean_dec_ref(v_self_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex(lean_object* v_00_u03b1_26_){
_start:
{
lean_object* v___f_27_; 
v___f_27_ = ((lean_object*)(l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___closed__0));
return v___f_27_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_new___redArg(lean_object* v_a_28_){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_30_ = lean_st_mk_ref(v_a_28_);
v___x_31_ = lean_io_baserecmutex_new();
v___x_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_30_);
lean_ctor_set(v___x_32_, 1, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_new___redArg___boxed(lean_object* v_a_33_, lean_object* v_a_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Std_RecursiveMutex_new___redArg(v_a_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_new(lean_object* v_00_u03b1_36_, lean_object* v_a_37_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Std_RecursiveMutex_new___redArg(v_a_37_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_new___boxed(lean_object* v_00_u03b1_40_, lean_object* v_a_41_, lean_object* v_a_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Std_RecursiveMutex_new(v_00_u03b1_40_, v_a_41_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg___lam__0(lean_object* v_k_44_, lean_object* v_ref_45_, lean_object* v_____r_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lean_apply_1(v_k_44_, v_ref_45_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg___lam__1(lean_object* v_x_48_){
_start:
{
lean_object* v_fst_49_; 
v_fst_49_ = lean_ctor_get(v_x_48_, 0);
lean_inc(v_fst_49_);
return v_fst_49_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg___lam__1___boxed(lean_object* v_x_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Std_RecursiveMutex_atomically___redArg___lam__1(v_x_50_);
lean_dec_ref(v_x_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg___lam__2(lean_object* v___x_52_, lean_object* v_x_53_){
_start:
{
lean_inc(v___x_52_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg___lam__2___boxed(lean_object* v___x_54_, lean_object* v_x_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Std_RecursiveMutex_atomically___redArg___lam__2(v___x_54_, v_x_55_);
lean_dec(v_x_55_);
lean_dec(v___x_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg(lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_mutex_61_, lean_object* v_k_62_){
_start:
{
lean_object* v_toApplicative_63_; lean_object* v_toFunctor_64_; lean_object* v_toBind_65_; lean_object* v_ref_66_; lean_object* v_mutex_67_; lean_object* v_map_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___f_71_; lean_object* v___f_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___f_76_; lean_object* v_y_77_; lean_object* v___x_78_; 
v_toApplicative_63_ = lean_ctor_get(v_inst_58_, 0);
v_toFunctor_64_ = lean_ctor_get(v_toApplicative_63_, 0);
lean_inc_ref(v_toFunctor_64_);
v_toBind_65_ = lean_ctor_get(v_inst_58_, 1);
lean_inc(v_toBind_65_);
lean_dec_ref(v_inst_58_);
v_ref_66_ = lean_ctor_get(v_mutex_61_, 0);
lean_inc(v_ref_66_);
v_mutex_67_ = lean_ctor_get(v_mutex_61_, 1);
lean_inc(v_mutex_67_);
lean_dec_ref(v_mutex_61_);
v_map_68_ = lean_ctor_get(v_toFunctor_64_, 0);
lean_inc(v_map_68_);
lean_dec_ref(v_toFunctor_64_);
lean_inc(v_mutex_67_);
v___x_69_ = lean_alloc_closure((void*)(l_Std_BaseRecursiveMutex_lock___boxed), 2, 1);
lean_closure_set(v___x_69_, 0, v_mutex_67_);
lean_inc(v_inst_59_);
v___x_70_ = lean_apply_2(v_inst_59_, lean_box(0), v___x_69_);
v___f_71_ = lean_alloc_closure((void*)(l_Std_RecursiveMutex_atomically___redArg___lam__0), 3, 2);
lean_closure_set(v___f_71_, 0, v_k_62_);
lean_closure_set(v___f_71_, 1, v_ref_66_);
v___f_72_ = ((lean_object*)(l_Std_RecursiveMutex_atomically___redArg___closed__0));
v___x_73_ = lean_apply_4(v_toBind_65_, lean_box(0), lean_box(0), v___x_70_, v___f_71_);
v___x_74_ = lean_alloc_closure((void*)(l_Std_BaseRecursiveMutex_unlock___boxed), 2, 1);
lean_closure_set(v___x_74_, 0, v_mutex_67_);
v___x_75_ = lean_apply_2(v_inst_59_, lean_box(0), v___x_74_);
v___f_76_ = lean_alloc_closure((void*)(l_Std_RecursiveMutex_atomically___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_76_, 0, v___x_75_);
v_y_77_ = lean_apply_4(v_inst_60_, lean_box(0), lean_box(0), v___x_73_, v___f_76_);
v___x_78_ = lean_apply_4(v_map_68_, lean_box(0), lean_box(0), v___f_72_, v_y_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically(lean_object* v_m_79_, lean_object* v_00_u03b1_80_, lean_object* v_00_u03b2_81_, lean_object* v_inst_82_, lean_object* v_inst_83_, lean_object* v_inst_84_, lean_object* v_mutex_85_, lean_object* v_k_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Std_RecursiveMutex_atomically___redArg(v_inst_82_, v_inst_83_, v_inst_84_, v_mutex_85_, v_k_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__0(lean_object* v_x_88_){
_start:
{
lean_object* v_fst_89_; 
v_fst_89_ = lean_ctor_get(v_x_88_, 0);
lean_inc(v_fst_89_);
return v_fst_89_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__0___boxed(lean_object* v_x_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Std_RecursiveMutex_tryAtomically___redArg___lam__0(v_x_90_);
lean_dec_ref(v_x_90_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__1(lean_object* v_val_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_93_, 0, v_val_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__2(lean_object* v___x_94_, lean_object* v_x_95_){
_start:
{
lean_inc(v___x_94_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__2___boxed(lean_object* v___x_96_, lean_object* v_x_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Std_RecursiveMutex_tryAtomically___redArg___lam__2(v___x_96_, v_x_97_);
lean_dec(v_x_97_);
lean_dec(v___x_96_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__3(lean_object* v_toApplicative_99_, lean_object* v_k_100_, lean_object* v_ref_101_, lean_object* v___f_102_, lean_object* v_mutex_103_, lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v___f_106_, uint8_t v_____do__lift_107_){
_start:
{
if (v_____do__lift_107_ == 0)
{
lean_object* v_toPure_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
lean_dec_ref(v___f_106_);
lean_dec(v_inst_105_);
lean_dec(v_inst_104_);
lean_dec(v_mutex_103_);
lean_dec_ref(v___f_102_);
lean_dec(v_ref_101_);
lean_dec(v_k_100_);
v_toPure_108_ = lean_ctor_get(v_toApplicative_99_, 1);
lean_inc(v_toPure_108_);
lean_dec_ref(v_toApplicative_99_);
v___x_109_ = lean_box(0);
v___x_110_ = lean_apply_2(v_toPure_108_, lean_box(0), v___x_109_);
return v___x_110_;
}
else
{
lean_object* v_toFunctor_111_; lean_object* v_map_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___f_117_; lean_object* v_y_118_; lean_object* v___x_119_; 
v_toFunctor_111_ = lean_ctor_get(v_toApplicative_99_, 0);
lean_inc_ref(v_toFunctor_111_);
lean_dec_ref(v_toApplicative_99_);
v_map_112_ = lean_ctor_get(v_toFunctor_111_, 0);
lean_inc(v_map_112_);
lean_dec_ref(v_toFunctor_111_);
v___x_113_ = lean_apply_1(v_k_100_, v_ref_101_);
lean_inc(v_map_112_);
v___x_114_ = lean_apply_4(v_map_112_, lean_box(0), lean_box(0), v___f_102_, v___x_113_);
v___x_115_ = lean_alloc_closure((void*)(l_Std_BaseRecursiveMutex_unlock___boxed), 2, 1);
lean_closure_set(v___x_115_, 0, v_mutex_103_);
v___x_116_ = lean_apply_2(v_inst_104_, lean_box(0), v___x_115_);
v___f_117_ = lean_alloc_closure((void*)(l_Std_RecursiveMutex_tryAtomically___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_117_, 0, v___x_116_);
v_y_118_ = lean_apply_4(v_inst_105_, lean_box(0), lean_box(0), v___x_114_, v___f_117_);
v___x_119_ = lean_apply_4(v_map_112_, lean_box(0), lean_box(0), v___f_106_, v_y_118_);
return v___x_119_;
}
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__3___boxed(lean_object* v_toApplicative_120_, lean_object* v_k_121_, lean_object* v_ref_122_, lean_object* v___f_123_, lean_object* v_mutex_124_, lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v___f_127_, lean_object* v_____do__lift_128_){
_start:
{
uint8_t v_____do__lift_140__boxed_129_; lean_object* v_res_130_; 
v_____do__lift_140__boxed_129_ = lean_unbox(v_____do__lift_128_);
v_res_130_ = l_Std_RecursiveMutex_tryAtomically___redArg___lam__3(v_toApplicative_120_, v_k_121_, v_ref_122_, v___f_123_, v_mutex_124_, v_inst_125_, v_inst_126_, v___f_127_, v_____do__lift_140__boxed_129_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg(lean_object* v_inst_133_, lean_object* v_inst_134_, lean_object* v_inst_135_, lean_object* v_mutex_136_, lean_object* v_k_137_){
_start:
{
lean_object* v_toApplicative_138_; lean_object* v_toBind_139_; lean_object* v_ref_140_; lean_object* v_mutex_141_; lean_object* v___f_142_; lean_object* v___f_143_; lean_object* v___f_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v_toApplicative_138_ = lean_ctor_get(v_inst_133_, 0);
lean_inc_ref(v_toApplicative_138_);
v_toBind_139_ = lean_ctor_get(v_inst_133_, 1);
lean_inc(v_toBind_139_);
lean_dec_ref(v_inst_133_);
v_ref_140_ = lean_ctor_get(v_mutex_136_, 0);
lean_inc(v_ref_140_);
v_mutex_141_ = lean_ctor_get(v_mutex_136_, 1);
lean_inc(v_mutex_141_);
lean_dec_ref(v_mutex_136_);
v___f_142_ = ((lean_object*)(l_Std_RecursiveMutex_tryAtomically___redArg___closed__0));
v___f_143_ = ((lean_object*)(l_Std_RecursiveMutex_tryAtomically___redArg___closed__1));
lean_inc(v_inst_134_);
lean_inc(v_mutex_141_);
v___f_144_ = lean_alloc_closure((void*)(l_Std_RecursiveMutex_tryAtomically___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_144_, 0, v_toApplicative_138_);
lean_closure_set(v___f_144_, 1, v_k_137_);
lean_closure_set(v___f_144_, 2, v_ref_140_);
lean_closure_set(v___f_144_, 3, v___f_143_);
lean_closure_set(v___f_144_, 4, v_mutex_141_);
lean_closure_set(v___f_144_, 5, v_inst_134_);
lean_closure_set(v___f_144_, 6, v_inst_135_);
lean_closure_set(v___f_144_, 7, v___f_142_);
v___x_145_ = lean_alloc_closure((void*)(l_Std_BaseRecursiveMutex_tryLock___boxed), 2, 1);
lean_closure_set(v___x_145_, 0, v_mutex_141_);
v___x_146_ = lean_apply_2(v_inst_134_, lean_box(0), v___x_145_);
v___x_147_ = lean_apply_4(v_toBind_139_, lean_box(0), lean_box(0), v___x_146_, v___f_144_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically(lean_object* v_m_148_, lean_object* v_00_u03b1_149_, lean_object* v_00_u03b2_150_, lean_object* v_inst_151_, lean_object* v_inst_152_, lean_object* v_inst_153_, lean_object* v_mutex_154_, lean_object* v_k_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Std_RecursiveMutex_tryAtomically___redArg(v_inst_151_, v_inst_152_, v_inst_153_, v_mutex_154_, v_k_155_);
return v___x_156_;
}
}
lean_object* runtime_initialize_Std_Sync_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sync_RecursiveMutex(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Sync_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Std_Sync_RecursiveMutex_0__Std_RecursiveMutexImpl = _init_l___private_Std_Sync_RecursiveMutex_0__Std_RecursiveMutexImpl();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sync_RecursiveMutex(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sync_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sync_RecursiveMutex(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sync_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sync_RecursiveMutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sync_RecursiveMutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sync_RecursiveMutex(builtin);
}
#ifdef __cplusplus
}
#endif
