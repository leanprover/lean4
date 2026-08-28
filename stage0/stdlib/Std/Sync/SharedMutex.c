// Lean compiler output
// Module: Std.Sync.SharedMutex
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
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_SharedMutex_0__Std_SharedMutexImpl;
lean_object* lean_io_basesharedmutex_new();
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_new___boxed(lean_object*);
lean_object* lean_io_basesharedmutex_write(lean_object*);
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_write___boxed(lean_object*, lean_object*);
uint8_t lean_io_basesharedmutex_try_write(lean_object*);
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_tryWrite___boxed(lean_object*, lean_object*);
lean_object* lean_io_basesharedmutex_unlock_write(lean_object*);
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_unlockWrite___boxed(lean_object*, lean_object*);
lean_object* lean_io_basesharedmutex_read(lean_object*);
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_read___boxed(lean_object*, lean_object*);
uint8_t lean_io_basesharedmutex_try_read(lean_object*);
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_tryRead___boxed(lean_object*, lean_object*);
lean_object* lean_io_basesharedmutex_unlock_read(lean_object*);
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_unlockRead___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instCoeOutSharedMutexBaseSharedMutex___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_instCoeOutSharedMutexBaseSharedMutex___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_instCoeOutSharedMutexBaseSharedMutex___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instCoeOutSharedMutexBaseSharedMutex___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instCoeOutSharedMutexBaseSharedMutex___closed__0 = (const lean_object*)&l_Std_instCoeOutSharedMutexBaseSharedMutex___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instCoeOutSharedMutexBaseSharedMutex(lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_new___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_new___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_new(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_new___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_SharedMutex_atomically___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_SharedMutex_atomically___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_SharedMutex_atomically___redArg___closed__0 = (const lean_object*)&l_Std_SharedMutex_atomically___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_SharedMutex_tryAtomically___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_SharedMutex_tryAtomically___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_SharedMutex_tryAtomically___redArg___closed__0 = (const lean_object*)&l_Std_SharedMutex_tryAtomically___redArg___closed__0_value;
static const lean_closure_object l_Std_SharedMutex_tryAtomically___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_SharedMutex_tryAtomically___redArg___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_SharedMutex_tryAtomically___redArg___closed__1 = (const lean_object*)&l_Std_SharedMutex_tryAtomically___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomicallyRead___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomicallyRead___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomicallyRead___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomicallyRead___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomicallyRead___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomicallyRead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomicallyRead___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomicallyRead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Std_Sync_SharedMutex_0__Std_SharedMutexImpl(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_new___boxed(lean_object* v_a_00___x40___internal___hyg_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lean_io_basesharedmutex_new();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_write___boxed(lean_object* v_mutex_7_, lean_object* v_a_00___x40___internal___hyg_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lean_io_basesharedmutex_write(v_mutex_7_);
lean_dec(v_mutex_7_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_tryWrite___boxed(lean_object* v_mutex_12_, lean_object* v_a_00___x40___internal___hyg_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = lean_io_basesharedmutex_try_write(v_mutex_12_);
lean_dec(v_mutex_12_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_unlockWrite___boxed(lean_object* v_mutex_18_, lean_object* v_a_00___x40___internal___hyg_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lean_io_basesharedmutex_unlock_write(v_mutex_18_);
lean_dec(v_mutex_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_read___boxed(lean_object* v_mutex_23_, lean_object* v_a_00___x40___internal___hyg_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lean_io_basesharedmutex_read(v_mutex_23_);
lean_dec(v_mutex_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_tryRead___boxed(lean_object* v_mutex_28_, lean_object* v_a_00___x40___internal___hyg_29_){
_start:
{
uint8_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = lean_io_basesharedmutex_try_read(v_mutex_28_);
lean_dec(v_mutex_28_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_unlockRead___boxed(lean_object* v_mutex_34_, lean_object* v_a_00___x40___internal___hyg_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lean_io_basesharedmutex_unlock_read(v_mutex_34_);
lean_dec(v_mutex_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutSharedMutexBaseSharedMutex___lam__0(lean_object* v_self_37_){
_start:
{
lean_object* v_mutex_38_; 
v_mutex_38_ = lean_ctor_get(v_self_37_, 1);
lean_inc(v_mutex_38_);
return v_mutex_38_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutSharedMutexBaseSharedMutex___lam__0___boxed(lean_object* v_self_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Std_instCoeOutSharedMutexBaseSharedMutex___lam__0(v_self_39_);
lean_dec_ref(v_self_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutSharedMutexBaseSharedMutex(lean_object* v_00_u03b1_42_){
_start:
{
lean_object* v___f_43_; 
v___f_43_ = ((lean_object*)(l_Std_instCoeOutSharedMutexBaseSharedMutex___closed__0));
return v___f_43_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_new___redArg(lean_object* v_a_44_){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_st_mk_ref(v_a_44_);
v___x_47_ = lean_io_basesharedmutex_new();
v___x_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_48_, 0, v___x_46_);
lean_ctor_set(v___x_48_, 1, v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_new___redArg___boxed(lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Std_SharedMutex_new___redArg(v_a_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_new(lean_object* v_00_u03b1_52_, lean_object* v_a_53_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Std_SharedMutex_new___redArg(v_a_53_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_new___boxed(lean_object* v_00_u03b1_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Std_SharedMutex_new(v_00_u03b1_56_, v_a_57_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg___lam__0(lean_object* v_k_60_, lean_object* v_ref_61_, lean_object* v_____r_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lean_apply_1(v_k_60_, v_ref_61_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg___lam__1(lean_object* v_x_64_){
_start:
{
lean_object* v_fst_65_; 
v_fst_65_ = lean_ctor_get(v_x_64_, 0);
lean_inc(v_fst_65_);
return v_fst_65_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg___lam__1___boxed(lean_object* v_x_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Std_SharedMutex_atomically___redArg___lam__1(v_x_66_);
lean_dec_ref(v_x_66_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg___lam__2(lean_object* v___x_68_, lean_object* v_x_69_){
_start:
{
lean_inc(v___x_68_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg___lam__2___boxed(lean_object* v___x_70_, lean_object* v_x_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Std_SharedMutex_atomically___redArg___lam__2(v___x_70_, v_x_71_);
lean_dec(v_x_71_);
lean_dec(v___x_70_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg(lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_mutex_77_, lean_object* v_k_78_){
_start:
{
lean_object* v_toApplicative_79_; lean_object* v_toFunctor_80_; lean_object* v_toBind_81_; lean_object* v_ref_82_; lean_object* v_mutex_83_; lean_object* v_map_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___f_87_; lean_object* v___f_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___f_92_; lean_object* v_y_93_; lean_object* v___x_94_; 
v_toApplicative_79_ = lean_ctor_get(v_inst_74_, 0);
v_toFunctor_80_ = lean_ctor_get(v_toApplicative_79_, 0);
lean_inc_ref(v_toFunctor_80_);
v_toBind_81_ = lean_ctor_get(v_inst_74_, 1);
lean_inc(v_toBind_81_);
lean_dec_ref(v_inst_74_);
v_ref_82_ = lean_ctor_get(v_mutex_77_, 0);
lean_inc(v_ref_82_);
v_mutex_83_ = lean_ctor_get(v_mutex_77_, 1);
lean_inc_n(v_mutex_83_, 2);
lean_dec_ref(v_mutex_77_);
v_map_84_ = lean_ctor_get(v_toFunctor_80_, 0);
lean_inc(v_map_84_);
lean_dec_ref(v_toFunctor_80_);
v___x_85_ = lean_alloc_closure((void*)(l_Std_BaseSharedMutex_write___boxed), 2, 1);
lean_closure_set(v___x_85_, 0, v_mutex_83_);
lean_inc(v_inst_75_);
v___x_86_ = lean_apply_2(v_inst_75_, lean_box(0), v___x_85_);
v___f_87_ = lean_alloc_closure((void*)(l_Std_SharedMutex_atomically___redArg___lam__0), 3, 2);
lean_closure_set(v___f_87_, 0, v_k_78_);
lean_closure_set(v___f_87_, 1, v_ref_82_);
v___f_88_ = ((lean_object*)(l_Std_SharedMutex_atomically___redArg___closed__0));
v___x_89_ = lean_apply_4(v_toBind_81_, lean_box(0), lean_box(0), v___x_86_, v___f_87_);
v___x_90_ = lean_alloc_closure((void*)(l_Std_BaseSharedMutex_unlockWrite___boxed), 2, 1);
lean_closure_set(v___x_90_, 0, v_mutex_83_);
v___x_91_ = lean_apply_2(v_inst_75_, lean_box(0), v___x_90_);
v___f_92_ = lean_alloc_closure((void*)(l_Std_SharedMutex_atomically___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_92_, 0, v___x_91_);
v_y_93_ = lean_apply_4(v_inst_76_, lean_box(0), lean_box(0), v___x_89_, v___f_92_);
v___x_94_ = lean_apply_4(v_map_84_, lean_box(0), lean_box(0), v___f_88_, v_y_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically(lean_object* v_m_95_, lean_object* v_00_u03b1_96_, lean_object* v_00_u03b2_97_, lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_mutex_101_, lean_object* v_k_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Std_SharedMutex_atomically___redArg(v_inst_98_, v_inst_99_, v_inst_100_, v_mutex_101_, v_k_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__0(lean_object* v_x_104_){
_start:
{
lean_object* v_fst_105_; 
v_fst_105_ = lean_ctor_get(v_x_104_, 0);
lean_inc(v_fst_105_);
return v_fst_105_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__0___boxed(lean_object* v_x_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Std_SharedMutex_tryAtomically___redArg___lam__0(v_x_106_);
lean_dec_ref(v_x_106_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__1(lean_object* v_val_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_109_, 0, v_val_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__2(lean_object* v___x_110_, lean_object* v_x_111_){
_start:
{
lean_inc(v___x_110_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__2___boxed(lean_object* v___x_112_, lean_object* v_x_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Std_SharedMutex_tryAtomically___redArg___lam__2(v___x_112_, v_x_113_);
lean_dec(v_x_113_);
lean_dec(v___x_112_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__3(lean_object* v_toPure_115_, lean_object* v_toFunctor_116_, lean_object* v_k_117_, lean_object* v_ref_118_, lean_object* v___f_119_, lean_object* v_mutex_120_, lean_object* v_inst_121_, lean_object* v_inst_122_, lean_object* v___f_123_, uint8_t v_____do__lift_124_){
_start:
{
if (v_____do__lift_124_ == 0)
{
lean_object* v___x_125_; lean_object* v___x_126_; 
lean_dec_ref(v___f_123_);
lean_dec(v_inst_122_);
lean_dec(v_inst_121_);
lean_dec(v_mutex_120_);
lean_dec_ref(v___f_119_);
lean_dec(v_ref_118_);
lean_dec(v_k_117_);
lean_dec_ref(v_toFunctor_116_);
v___x_125_ = lean_box(0);
v___x_126_ = lean_apply_2(v_toPure_115_, lean_box(0), v___x_125_);
return v___x_126_;
}
else
{
lean_object* v_map_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___f_132_; lean_object* v_y_133_; lean_object* v___x_134_; 
lean_dec(v_toPure_115_);
v_map_127_ = lean_ctor_get(v_toFunctor_116_, 0);
lean_inc_n(v_map_127_, 2);
lean_dec_ref(v_toFunctor_116_);
v___x_128_ = lean_apply_1(v_k_117_, v_ref_118_);
v___x_129_ = lean_apply_4(v_map_127_, lean_box(0), lean_box(0), v___f_119_, v___x_128_);
v___x_130_ = lean_alloc_closure((void*)(l_Std_BaseSharedMutex_unlockWrite___boxed), 2, 1);
lean_closure_set(v___x_130_, 0, v_mutex_120_);
v___x_131_ = lean_apply_2(v_inst_121_, lean_box(0), v___x_130_);
v___f_132_ = lean_alloc_closure((void*)(l_Std_SharedMutex_tryAtomically___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_132_, 0, v___x_131_);
v_y_133_ = lean_apply_4(v_inst_122_, lean_box(0), lean_box(0), v___x_129_, v___f_132_);
v___x_134_ = lean_apply_4(v_map_127_, lean_box(0), lean_box(0), v___f_123_, v_y_133_);
return v___x_134_;
}
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__3___boxed(lean_object* v_toPure_135_, lean_object* v_toFunctor_136_, lean_object* v_k_137_, lean_object* v_ref_138_, lean_object* v___f_139_, lean_object* v_mutex_140_, lean_object* v_inst_141_, lean_object* v_inst_142_, lean_object* v___f_143_, lean_object* v_____do__lift_144_){
_start:
{
uint8_t v_____do__lift_85__boxed_145_; lean_object* v_res_146_; 
v_____do__lift_85__boxed_145_ = lean_unbox(v_____do__lift_144_);
v_res_146_ = l_Std_SharedMutex_tryAtomically___redArg___lam__3(v_toPure_135_, v_toFunctor_136_, v_k_137_, v_ref_138_, v___f_139_, v_mutex_140_, v_inst_141_, v_inst_142_, v___f_143_, v_____do__lift_85__boxed_145_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg(lean_object* v_inst_149_, lean_object* v_inst_150_, lean_object* v_inst_151_, lean_object* v_mutex_152_, lean_object* v_k_153_){
_start:
{
lean_object* v_toApplicative_154_; lean_object* v_toBind_155_; lean_object* v_ref_156_; lean_object* v_mutex_157_; lean_object* v_toFunctor_158_; lean_object* v_toPure_159_; lean_object* v___f_160_; lean_object* v___f_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___f_164_; lean_object* v___x_165_; 
v_toApplicative_154_ = lean_ctor_get(v_inst_149_, 0);
lean_inc_ref(v_toApplicative_154_);
v_toBind_155_ = lean_ctor_get(v_inst_149_, 1);
lean_inc(v_toBind_155_);
lean_dec_ref(v_inst_149_);
v_ref_156_ = lean_ctor_get(v_mutex_152_, 0);
lean_inc(v_ref_156_);
v_mutex_157_ = lean_ctor_get(v_mutex_152_, 1);
lean_inc_n(v_mutex_157_, 2);
lean_dec_ref(v_mutex_152_);
v_toFunctor_158_ = lean_ctor_get(v_toApplicative_154_, 0);
lean_inc_ref(v_toFunctor_158_);
v_toPure_159_ = lean_ctor_get(v_toApplicative_154_, 1);
lean_inc(v_toPure_159_);
lean_dec_ref(v_toApplicative_154_);
v___f_160_ = ((lean_object*)(l_Std_SharedMutex_tryAtomically___redArg___closed__0));
v___f_161_ = ((lean_object*)(l_Std_SharedMutex_tryAtomically___redArg___closed__1));
v___x_162_ = lean_alloc_closure((void*)(l_Std_BaseSharedMutex_tryWrite___boxed), 2, 1);
lean_closure_set(v___x_162_, 0, v_mutex_157_);
lean_inc(v_inst_150_);
v___x_163_ = lean_apply_2(v_inst_150_, lean_box(0), v___x_162_);
v___f_164_ = lean_alloc_closure((void*)(l_Std_SharedMutex_tryAtomically___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_164_, 0, v_toPure_159_);
lean_closure_set(v___f_164_, 1, v_toFunctor_158_);
lean_closure_set(v___f_164_, 2, v_k_153_);
lean_closure_set(v___f_164_, 3, v_ref_156_);
lean_closure_set(v___f_164_, 4, v___f_161_);
lean_closure_set(v___f_164_, 5, v_mutex_157_);
lean_closure_set(v___f_164_, 6, v_inst_150_);
lean_closure_set(v___f_164_, 7, v_inst_151_);
lean_closure_set(v___f_164_, 8, v___f_160_);
v___x_165_ = lean_apply_4(v_toBind_155_, lean_box(0), lean_box(0), v___x_163_, v___f_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically(lean_object* v_m_166_, lean_object* v_00_u03b1_167_, lean_object* v_00_u03b2_168_, lean_object* v_inst_169_, lean_object* v_inst_170_, lean_object* v_inst_171_, lean_object* v_mutex_172_, lean_object* v_k_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Std_SharedMutex_tryAtomically___redArg(v_inst_169_, v_inst_170_, v_inst_171_, v_mutex_172_, v_k_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomicallyRead___redArg___lam__0(lean_object* v_k_175_, lean_object* v_state_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = lean_apply_1(v_k_175_, v_state_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomicallyRead___redArg___lam__2(lean_object* v_ref_178_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = lean_st_ref_get(v_ref_178_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomicallyRead___redArg___lam__2___boxed(lean_object* v_ref_181_, lean_object* v___y_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Std_SharedMutex_atomicallyRead___redArg___lam__2(v_ref_181_);
lean_dec(v_ref_181_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomicallyRead___redArg___lam__1(lean_object* v_ref_184_, lean_object* v_inst_185_, lean_object* v_toBind_186_, lean_object* v___f_187_, lean_object* v_____r_188_){
_start:
{
lean_object* v___f_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___f_189_ = lean_alloc_closure((void*)(l_Std_SharedMutex_atomicallyRead___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_189_, 0, v_ref_184_);
v___x_190_ = lean_apply_2(v_inst_185_, lean_box(0), v___f_189_);
v___x_191_ = lean_apply_4(v_toBind_186_, lean_box(0), lean_box(0), v___x_190_, v___f_187_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomicallyRead___redArg(lean_object* v_inst_192_, lean_object* v_inst_193_, lean_object* v_inst_194_, lean_object* v_mutex_195_, lean_object* v_k_196_){
_start:
{
lean_object* v_toApplicative_197_; lean_object* v_toFunctor_198_; lean_object* v_toBind_199_; lean_object* v_ref_200_; lean_object* v_mutex_201_; lean_object* v_map_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___f_205_; lean_object* v___f_206_; lean_object* v___f_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___f_211_; lean_object* v_y_212_; lean_object* v___x_213_; 
v_toApplicative_197_ = lean_ctor_get(v_inst_192_, 0);
v_toFunctor_198_ = lean_ctor_get(v_toApplicative_197_, 0);
lean_inc_ref(v_toFunctor_198_);
v_toBind_199_ = lean_ctor_get(v_inst_192_, 1);
lean_inc_n(v_toBind_199_, 2);
lean_dec_ref(v_inst_192_);
v_ref_200_ = lean_ctor_get(v_mutex_195_, 0);
lean_inc(v_ref_200_);
v_mutex_201_ = lean_ctor_get(v_mutex_195_, 1);
lean_inc_n(v_mutex_201_, 2);
lean_dec_ref(v_mutex_195_);
v_map_202_ = lean_ctor_get(v_toFunctor_198_, 0);
lean_inc(v_map_202_);
lean_dec_ref(v_toFunctor_198_);
v___x_203_ = lean_alloc_closure((void*)(l_Std_BaseSharedMutex_read___boxed), 2, 1);
lean_closure_set(v___x_203_, 0, v_mutex_201_);
lean_inc_n(v_inst_193_, 2);
v___x_204_ = lean_apply_2(v_inst_193_, lean_box(0), v___x_203_);
v___f_205_ = lean_alloc_closure((void*)(l_Std_SharedMutex_atomicallyRead___redArg___lam__0), 2, 1);
lean_closure_set(v___f_205_, 0, v_k_196_);
v___f_206_ = ((lean_object*)(l_Std_SharedMutex_atomically___redArg___closed__0));
v___f_207_ = lean_alloc_closure((void*)(l_Std_SharedMutex_atomicallyRead___redArg___lam__1), 5, 4);
lean_closure_set(v___f_207_, 0, v_ref_200_);
lean_closure_set(v___f_207_, 1, v_inst_193_);
lean_closure_set(v___f_207_, 2, v_toBind_199_);
lean_closure_set(v___f_207_, 3, v___f_205_);
v___x_208_ = lean_apply_4(v_toBind_199_, lean_box(0), lean_box(0), v___x_204_, v___f_207_);
v___x_209_ = lean_alloc_closure((void*)(l_Std_BaseSharedMutex_unlockRead___boxed), 2, 1);
lean_closure_set(v___x_209_, 0, v_mutex_201_);
v___x_210_ = lean_apply_2(v_inst_193_, lean_box(0), v___x_209_);
v___f_211_ = lean_alloc_closure((void*)(l_Std_SharedMutex_atomically___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_211_, 0, v___x_210_);
v_y_212_ = lean_apply_4(v_inst_194_, lean_box(0), lean_box(0), v___x_208_, v___f_211_);
v___x_213_ = lean_apply_4(v_map_202_, lean_box(0), lean_box(0), v___f_206_, v_y_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomicallyRead(lean_object* v_m_214_, lean_object* v_00_u03b1_215_, lean_object* v_00_u03b2_216_, lean_object* v_inst_217_, lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_mutex_220_, lean_object* v_k_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Std_SharedMutex_atomicallyRead___redArg(v_inst_217_, v_inst_218_, v_inst_219_, v_mutex_220_, v_k_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__3(lean_object* v_toFunctor_223_, lean_object* v_k_224_, lean_object* v___f_225_, lean_object* v_state_226_){
_start:
{
lean_object* v_map_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_map_227_ = lean_ctor_get(v_toFunctor_223_, 0);
lean_inc(v_map_227_);
lean_dec_ref(v_toFunctor_223_);
v___x_228_ = lean_apply_1(v_k_224_, v_state_226_);
v___x_229_ = lean_apply_4(v_map_227_, lean_box(0), lean_box(0), v___f_225_, v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__1(lean_object* v_toPure_230_, lean_object* v_toFunctor_231_, lean_object* v_inst_232_, lean_object* v___f_233_, lean_object* v_toBind_234_, lean_object* v___f_235_, lean_object* v_mutex_236_, lean_object* v_inst_237_, lean_object* v___f_238_, uint8_t v_____do__lift_239_){
_start:
{
if (v_____do__lift_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec_ref(v___f_238_);
lean_dec(v_inst_237_);
lean_dec(v_mutex_236_);
lean_dec(v___f_235_);
lean_dec(v_toBind_234_);
lean_dec_ref(v___f_233_);
lean_dec(v_inst_232_);
lean_dec_ref(v_toFunctor_231_);
v___x_240_ = lean_box(0);
v___x_241_ = lean_apply_2(v_toPure_230_, lean_box(0), v___x_240_);
return v___x_241_;
}
else
{
lean_object* v_map_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___f_247_; lean_object* v_y_248_; lean_object* v___x_249_; 
lean_dec(v_toPure_230_);
v_map_242_ = lean_ctor_get(v_toFunctor_231_, 0);
lean_inc(v_map_242_);
lean_dec_ref(v_toFunctor_231_);
lean_inc(v_inst_232_);
v___x_243_ = lean_apply_2(v_inst_232_, lean_box(0), v___f_233_);
v___x_244_ = lean_apply_4(v_toBind_234_, lean_box(0), lean_box(0), v___x_243_, v___f_235_);
v___x_245_ = lean_alloc_closure((void*)(l_Std_BaseSharedMutex_unlockRead___boxed), 2, 1);
lean_closure_set(v___x_245_, 0, v_mutex_236_);
v___x_246_ = lean_apply_2(v_inst_232_, lean_box(0), v___x_245_);
v___f_247_ = lean_alloc_closure((void*)(l_Std_SharedMutex_tryAtomically___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_247_, 0, v___x_246_);
v_y_248_ = lean_apply_4(v_inst_237_, lean_box(0), lean_box(0), v___x_244_, v___f_247_);
v___x_249_ = lean_apply_4(v_map_242_, lean_box(0), lean_box(0), v___f_238_, v_y_248_);
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__1___boxed(lean_object* v_toPure_250_, lean_object* v_toFunctor_251_, lean_object* v_inst_252_, lean_object* v___f_253_, lean_object* v_toBind_254_, lean_object* v___f_255_, lean_object* v_mutex_256_, lean_object* v_inst_257_, lean_object* v___f_258_, lean_object* v_____do__lift_259_){
_start:
{
uint8_t v_____do__lift_120__boxed_260_; lean_object* v_res_261_; 
v_____do__lift_120__boxed_260_ = lean_unbox(v_____do__lift_259_);
v_res_261_ = l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__1(v_toPure_250_, v_toFunctor_251_, v_inst_252_, v___f_253_, v_toBind_254_, v___f_255_, v_mutex_256_, v_inst_257_, v___f_258_, v_____do__lift_120__boxed_260_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomicallyRead___redArg(lean_object* v_inst_262_, lean_object* v_inst_263_, lean_object* v_inst_264_, lean_object* v_mutex_265_, lean_object* v_k_266_){
_start:
{
lean_object* v_toApplicative_267_; lean_object* v_toBind_268_; lean_object* v_ref_269_; lean_object* v_mutex_270_; lean_object* v_toFunctor_271_; lean_object* v_toPure_272_; lean_object* v___f_273_; lean_object* v___f_274_; lean_object* v___f_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___f_278_; lean_object* v___f_279_; lean_object* v___x_280_; 
v_toApplicative_267_ = lean_ctor_get(v_inst_262_, 0);
lean_inc_ref(v_toApplicative_267_);
v_toBind_268_ = lean_ctor_get(v_inst_262_, 1);
lean_inc_n(v_toBind_268_, 2);
lean_dec_ref(v_inst_262_);
v_ref_269_ = lean_ctor_get(v_mutex_265_, 0);
lean_inc(v_ref_269_);
v_mutex_270_ = lean_ctor_get(v_mutex_265_, 1);
lean_inc_n(v_mutex_270_, 2);
lean_dec_ref(v_mutex_265_);
v_toFunctor_271_ = lean_ctor_get(v_toApplicative_267_, 0);
lean_inc_ref_n(v_toFunctor_271_, 2);
v_toPure_272_ = lean_ctor_get(v_toApplicative_267_, 1);
lean_inc(v_toPure_272_);
lean_dec_ref(v_toApplicative_267_);
v___f_273_ = ((lean_object*)(l_Std_SharedMutex_tryAtomically___redArg___closed__0));
v___f_274_ = ((lean_object*)(l_Std_SharedMutex_tryAtomically___redArg___closed__1));
v___f_275_ = lean_alloc_closure((void*)(l_Std_SharedMutex_atomicallyRead___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_275_, 0, v_ref_269_);
v___x_276_ = lean_alloc_closure((void*)(l_Std_BaseSharedMutex_tryRead___boxed), 2, 1);
lean_closure_set(v___x_276_, 0, v_mutex_270_);
lean_inc(v_inst_263_);
v___x_277_ = lean_apply_2(v_inst_263_, lean_box(0), v___x_276_);
v___f_278_ = lean_alloc_closure((void*)(l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__3), 4, 3);
lean_closure_set(v___f_278_, 0, v_toFunctor_271_);
lean_closure_set(v___f_278_, 1, v_k_266_);
lean_closure_set(v___f_278_, 2, v___f_274_);
v___f_279_ = lean_alloc_closure((void*)(l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_279_, 0, v_toPure_272_);
lean_closure_set(v___f_279_, 1, v_toFunctor_271_);
lean_closure_set(v___f_279_, 2, v_inst_263_);
lean_closure_set(v___f_279_, 3, v___f_275_);
lean_closure_set(v___f_279_, 4, v_toBind_268_);
lean_closure_set(v___f_279_, 5, v___f_278_);
lean_closure_set(v___f_279_, 6, v_mutex_270_);
lean_closure_set(v___f_279_, 7, v_inst_264_);
lean_closure_set(v___f_279_, 8, v___f_273_);
v___x_280_ = lean_apply_4(v_toBind_268_, lean_box(0), lean_box(0), v___x_277_, v___f_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomicallyRead(lean_object* v_m_281_, lean_object* v_00_u03b1_282_, lean_object* v_00_u03b2_283_, lean_object* v_inst_284_, lean_object* v_inst_285_, lean_object* v_inst_286_, lean_object* v_mutex_287_, lean_object* v_k_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_Std_SharedMutex_tryAtomicallyRead___redArg(v_inst_284_, v_inst_285_, v_inst_286_, v_mutex_287_, v_k_288_);
return v___x_289_;
}
}
lean_object* runtime_initialize_Std_Sync_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sync_SharedMutex(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Sync_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Std_Sync_SharedMutex_0__Std_SharedMutexImpl = _init_l___private_Std_Sync_SharedMutex_0__Std_SharedMutexImpl();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sync_SharedMutex(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sync_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sync_SharedMutex(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sync_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sync_SharedMutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sync_SharedMutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sync_SharedMutex(builtin);
}
#ifdef __cplusplus
}
#endif
