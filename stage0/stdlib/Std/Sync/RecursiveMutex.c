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
LEAN_EXPORT lean_object* l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg___closed__0 = (const lean_object*)&l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg();
LEAN_EXPORT lean_object* l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg___lam__0(lean_object* v_self_21_){
_start:
{
lean_object* v_mutex_22_; 
v_mutex_22_ = lean_ctor_get(v_self_21_, 1);
lean_inc(v_mutex_22_);
return v_mutex_22_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg___lam__0___boxed(lean_object* v_self_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg___lam__0(v_self_23_);
lean_dec_ref(v_self_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg(){
_start:
{
lean_object* v___f_27_; 
v___f_27_ = ((lean_object*)(l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg___closed__0));
return v___f_27_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg___boxed(lean_object* v___dummy_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg();
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex(lean_object* v_00_u03b1_30_){
_start:
{
lean_object* v___f_31_; 
v___f_31_ = ((lean_object*)(l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg___closed__0));
return v___f_31_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_new___redArg(lean_object* v_a_32_){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_34_ = lean_st_mk_ref(v_a_32_);
v___x_35_ = lean_io_baserecmutex_new();
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v___x_34_);
lean_ctor_set(v___x_36_, 1, v___x_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_new___redArg___boxed(lean_object* v_a_37_, lean_object* v_a_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Std_RecursiveMutex_new___redArg(v_a_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_new(lean_object* v_00_u03b1_40_, lean_object* v_a_41_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Std_RecursiveMutex_new___redArg(v_a_41_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_new___boxed(lean_object* v_00_u03b1_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Std_RecursiveMutex_new(v_00_u03b1_44_, v_a_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg___lam__0(lean_object* v_k_48_, lean_object* v_ref_49_, lean_object* v_____r_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lean_apply_1(v_k_48_, v_ref_49_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg___lam__1(lean_object* v_x_52_){
_start:
{
lean_object* v_fst_53_; 
v_fst_53_ = lean_ctor_get(v_x_52_, 0);
lean_inc(v_fst_53_);
return v_fst_53_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg___lam__1___boxed(lean_object* v_x_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Std_RecursiveMutex_atomically___redArg___lam__1(v_x_54_);
lean_dec_ref(v_x_54_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg___lam__2(lean_object* v___x_56_, lean_object* v_x_57_){
_start:
{
lean_inc(v___x_56_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg___lam__2___boxed(lean_object* v___x_58_, lean_object* v_x_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Std_RecursiveMutex_atomically___redArg___lam__2(v___x_58_, v_x_59_);
lean_dec(v_x_59_);
lean_dec(v___x_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg(lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_mutex_65_, lean_object* v_k_66_){
_start:
{
lean_object* v_toApplicative_67_; lean_object* v_toFunctor_68_; lean_object* v_toBind_69_; lean_object* v_ref_70_; lean_object* v_mutex_71_; lean_object* v_map_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___f_75_; lean_object* v___f_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___f_80_; lean_object* v_y_81_; lean_object* v___x_82_; 
v_toApplicative_67_ = lean_ctor_get(v_inst_62_, 0);
v_toFunctor_68_ = lean_ctor_get(v_toApplicative_67_, 0);
lean_inc_ref(v_toFunctor_68_);
v_toBind_69_ = lean_ctor_get(v_inst_62_, 1);
lean_inc(v_toBind_69_);
lean_dec_ref(v_inst_62_);
v_ref_70_ = lean_ctor_get(v_mutex_65_, 0);
lean_inc(v_ref_70_);
v_mutex_71_ = lean_ctor_get(v_mutex_65_, 1);
lean_inc_n(v_mutex_71_, 2);
lean_dec_ref(v_mutex_65_);
v_map_72_ = lean_ctor_get(v_toFunctor_68_, 0);
lean_inc(v_map_72_);
lean_dec_ref(v_toFunctor_68_);
v___x_73_ = lean_alloc_closure((void*)(l_Std_BaseRecursiveMutex_lock___boxed), 2, 1);
lean_closure_set(v___x_73_, 0, v_mutex_71_);
lean_inc(v_inst_63_);
v___x_74_ = lean_apply_2(v_inst_63_, lean_box(0), v___x_73_);
v___f_75_ = lean_alloc_closure((void*)(l_Std_RecursiveMutex_atomically___redArg___lam__0), 3, 2);
lean_closure_set(v___f_75_, 0, v_k_66_);
lean_closure_set(v___f_75_, 1, v_ref_70_);
v___f_76_ = ((lean_object*)(l_Std_RecursiveMutex_atomically___redArg___closed__0));
v___x_77_ = lean_apply_4(v_toBind_69_, lean_box(0), lean_box(0), v___x_74_, v___f_75_);
v___x_78_ = lean_alloc_closure((void*)(l_Std_BaseRecursiveMutex_unlock___boxed), 2, 1);
lean_closure_set(v___x_78_, 0, v_mutex_71_);
v___x_79_ = lean_apply_2(v_inst_63_, lean_box(0), v___x_78_);
v___f_80_ = lean_alloc_closure((void*)(l_Std_RecursiveMutex_atomically___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_80_, 0, v___x_79_);
v_y_81_ = lean_apply_4(v_inst_64_, lean_box(0), lean_box(0), v___x_77_, v___f_80_);
v___x_82_ = lean_apply_4(v_map_72_, lean_box(0), lean_box(0), v___f_76_, v_y_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically(lean_object* v_m_83_, lean_object* v_00_u03b1_84_, lean_object* v_00_u03b2_85_, lean_object* v_inst_86_, lean_object* v_inst_87_, lean_object* v_inst_88_, lean_object* v_mutex_89_, lean_object* v_k_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Std_RecursiveMutex_atomically___redArg(v_inst_86_, v_inst_87_, v_inst_88_, v_mutex_89_, v_k_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__0(lean_object* v_x_92_){
_start:
{
lean_object* v_fst_93_; 
v_fst_93_ = lean_ctor_get(v_x_92_, 0);
lean_inc(v_fst_93_);
return v_fst_93_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__0___boxed(lean_object* v_x_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Std_RecursiveMutex_tryAtomically___redArg___lam__0(v_x_94_);
lean_dec_ref(v_x_94_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__1(lean_object* v_val_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_97_, 0, v_val_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__2(lean_object* v___x_98_, lean_object* v_x_99_){
_start:
{
lean_inc(v___x_98_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__2___boxed(lean_object* v___x_100_, lean_object* v_x_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Std_RecursiveMutex_tryAtomically___redArg___lam__2(v___x_100_, v_x_101_);
lean_dec(v_x_101_);
lean_dec(v___x_100_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__3(lean_object* v_toPure_103_, lean_object* v_toFunctor_104_, lean_object* v_k_105_, lean_object* v_ref_106_, lean_object* v___f_107_, lean_object* v_mutex_108_, lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v___f_111_, uint8_t v_____do__lift_112_){
_start:
{
if (v_____do__lift_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; 
lean_dec_ref(v___f_111_);
lean_dec(v_inst_110_);
lean_dec(v_inst_109_);
lean_dec(v_mutex_108_);
lean_dec_ref(v___f_107_);
lean_dec(v_ref_106_);
lean_dec(v_k_105_);
lean_dec_ref(v_toFunctor_104_);
v___x_113_ = lean_box(0);
v___x_114_ = lean_apply_2(v_toPure_103_, lean_box(0), v___x_113_);
return v___x_114_;
}
else
{
lean_object* v_map_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___f_120_; lean_object* v_y_121_; lean_object* v___x_122_; 
lean_dec(v_toPure_103_);
v_map_115_ = lean_ctor_get(v_toFunctor_104_, 0);
lean_inc_n(v_map_115_, 2);
lean_dec_ref(v_toFunctor_104_);
v___x_116_ = lean_apply_1(v_k_105_, v_ref_106_);
v___x_117_ = lean_apply_4(v_map_115_, lean_box(0), lean_box(0), v___f_107_, v___x_116_);
v___x_118_ = lean_alloc_closure((void*)(l_Std_BaseRecursiveMutex_unlock___boxed), 2, 1);
lean_closure_set(v___x_118_, 0, v_mutex_108_);
v___x_119_ = lean_apply_2(v_inst_109_, lean_box(0), v___x_118_);
v___f_120_ = lean_alloc_closure((void*)(l_Std_RecursiveMutex_tryAtomically___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_120_, 0, v___x_119_);
v_y_121_ = lean_apply_4(v_inst_110_, lean_box(0), lean_box(0), v___x_117_, v___f_120_);
v___x_122_ = lean_apply_4(v_map_115_, lean_box(0), lean_box(0), v___f_111_, v_y_121_);
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__3___boxed(lean_object* v_toPure_123_, lean_object* v_toFunctor_124_, lean_object* v_k_125_, lean_object* v_ref_126_, lean_object* v___f_127_, lean_object* v_mutex_128_, lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v___f_131_, lean_object* v_____do__lift_132_){
_start:
{
uint8_t v_____do__lift_85__boxed_133_; lean_object* v_res_134_; 
v_____do__lift_85__boxed_133_ = lean_unbox(v_____do__lift_132_);
v_res_134_ = l_Std_RecursiveMutex_tryAtomically___redArg___lam__3(v_toPure_123_, v_toFunctor_124_, v_k_125_, v_ref_126_, v___f_127_, v_mutex_128_, v_inst_129_, v_inst_130_, v___f_131_, v_____do__lift_85__boxed_133_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg(lean_object* v_inst_137_, lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_mutex_140_, lean_object* v_k_141_){
_start:
{
lean_object* v_toApplicative_142_; lean_object* v_toBind_143_; lean_object* v_ref_144_; lean_object* v_mutex_145_; lean_object* v_toFunctor_146_; lean_object* v_toPure_147_; lean_object* v___f_148_; lean_object* v___f_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___f_152_; lean_object* v___x_153_; 
v_toApplicative_142_ = lean_ctor_get(v_inst_137_, 0);
lean_inc_ref(v_toApplicative_142_);
v_toBind_143_ = lean_ctor_get(v_inst_137_, 1);
lean_inc(v_toBind_143_);
lean_dec_ref(v_inst_137_);
v_ref_144_ = lean_ctor_get(v_mutex_140_, 0);
lean_inc(v_ref_144_);
v_mutex_145_ = lean_ctor_get(v_mutex_140_, 1);
lean_inc_n(v_mutex_145_, 2);
lean_dec_ref(v_mutex_140_);
v_toFunctor_146_ = lean_ctor_get(v_toApplicative_142_, 0);
lean_inc_ref(v_toFunctor_146_);
v_toPure_147_ = lean_ctor_get(v_toApplicative_142_, 1);
lean_inc(v_toPure_147_);
lean_dec_ref(v_toApplicative_142_);
v___f_148_ = ((lean_object*)(l_Std_RecursiveMutex_tryAtomically___redArg___closed__0));
v___f_149_ = ((lean_object*)(l_Std_RecursiveMutex_tryAtomically___redArg___closed__1));
v___x_150_ = lean_alloc_closure((void*)(l_Std_BaseRecursiveMutex_tryLock___boxed), 2, 1);
lean_closure_set(v___x_150_, 0, v_mutex_145_);
lean_inc(v_inst_138_);
v___x_151_ = lean_apply_2(v_inst_138_, lean_box(0), v___x_150_);
v___f_152_ = lean_alloc_closure((void*)(l_Std_RecursiveMutex_tryAtomically___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_152_, 0, v_toPure_147_);
lean_closure_set(v___f_152_, 1, v_toFunctor_146_);
lean_closure_set(v___f_152_, 2, v_k_141_);
lean_closure_set(v___f_152_, 3, v_ref_144_);
lean_closure_set(v___f_152_, 4, v___f_149_);
lean_closure_set(v___f_152_, 5, v_mutex_145_);
lean_closure_set(v___f_152_, 6, v_inst_138_);
lean_closure_set(v___f_152_, 7, v_inst_139_);
lean_closure_set(v___f_152_, 8, v___f_148_);
v___x_153_ = lean_apply_4(v_toBind_143_, lean_box(0), lean_box(0), v___x_151_, v___f_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically(lean_object* v_m_154_, lean_object* v_00_u03b1_155_, lean_object* v_00_u03b2_156_, lean_object* v_inst_157_, lean_object* v_inst_158_, lean_object* v_inst_159_, lean_object* v_mutex_160_, lean_object* v_k_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Std_RecursiveMutex_tryAtomically___redArg(v_inst_157_, v_inst_158_, v_inst_159_, v_mutex_160_, v_k_161_);
return v___x_162_;
}
}
lean_object* runtime_initialize_Std_Sync_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sync_RecursiveMutex(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
