// Lean compiler output
// Module: Std.Sync.Mutex
// Imports: public import Std.Sync.Basic public import Init.While
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
lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_liftM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Mutex_0__Std_BaseMutexImpl;
lean_object* lean_io_basemutex_new();
LEAN_EXPORT lean_object* l_Std_BaseMutex_new___boxed(lean_object*);
lean_object* lean_io_basemutex_lock(lean_object*);
LEAN_EXPORT lean_object* l_Std_BaseMutex_lock___boxed(lean_object*, lean_object*);
uint8_t lean_io_basemutex_try_lock(lean_object*);
LEAN_EXPORT lean_object* l_Std_BaseMutex_tryLock___boxed(lean_object*, lean_object*);
lean_object* lean_io_basemutex_unlock(lean_object*);
LEAN_EXPORT lean_object* l_Std_BaseMutex_unlock___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Mutex_0__Std_CondvarImpl;
lean_object* lean_io_condvar_new();
LEAN_EXPORT lean_object* l_Std_Condvar_new___boxed(lean_object*);
lean_object* lean_io_condvar_wait(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Condvar_wait___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_condvar_notify_one(lean_object*);
LEAN_EXPORT lean_object* l_Std_Condvar_notifyOne___boxed(lean_object*, lean_object*);
lean_object* lean_io_condvar_notify_all(lean_object*);
LEAN_EXPORT lean_object* l_Std_Condvar_notifyAll___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instCoeOutMutexBaseMutex___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_instCoeOutMutexBaseMutex___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_instCoeOutMutexBaseMutex___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instCoeOutMutexBaseMutex___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instCoeOutMutexBaseMutex___closed__0 = (const lean_object*)&l_Std_instCoeOutMutexBaseMutex___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instCoeOutMutexBaseMutex(lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_new___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_new___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_new(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_new___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Mutex_atomically___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Mutex_atomically___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Mutex_atomically___redArg___closed__0 = (const lean_object*)&l_Std_Mutex_atomically___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Mutex_tryAtomically___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Mutex_tryAtomically___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Mutex_tryAtomically___redArg___closed__0 = (const lean_object*)&l_Std_Mutex_tryAtomically___redArg___closed__0_value;
static const lean_closure_object l_Std_Mutex_tryAtomically___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Mutex_tryAtomically___redArg___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Mutex_tryAtomically___redArg___closed__1 = (const lean_object*)&l_Std_Mutex_tryAtomically___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomicallyOnce___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Mutex_atomicallyOnce___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Mutex_atomicallyOnce___redArg___closed__0 = (const lean_object*)&l_Std_Mutex_atomicallyOnce___redArg___closed__0_value;
static const lean_closure_object l_Std_Mutex_atomicallyOnce___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Mutex_atomicallyOnce___redArg___closed__1 = (const lean_object*)&l_Std_Mutex_atomicallyOnce___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Mutex_atomicallyOnce___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomicallyOnce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Std_Sync_Mutex_0__Std_BaseMutexImpl(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_Std_BaseMutex_new___boxed(lean_object* v_a_00___x40___internal___hyg_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lean_io_basemutex_new();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_BaseMutex_lock___boxed(lean_object* v_mutex_7_, lean_object* v_a_00___x40___internal___hyg_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lean_io_basemutex_lock(v_mutex_7_);
lean_dec(v_mutex_7_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Std_BaseMutex_tryLock___boxed(lean_object* v_mutex_12_, lean_object* v_a_00___x40___internal___hyg_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = lean_io_basemutex_try_lock(v_mutex_12_);
lean_dec(v_mutex_12_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT lean_object* l_Std_BaseMutex_unlock___boxed(lean_object* v_mutex_18_, lean_object* v_a_00___x40___internal___hyg_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lean_io_basemutex_unlock(v_mutex_18_);
lean_dec(v_mutex_18_);
return v_res_20_;
}
}
static lean_object* _init_l___private_Std_Sync_Mutex_0__Std_CondvarImpl(void){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_box(0);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_new___boxed(lean_object* v_a_00___x40___internal___hyg_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lean_io_condvar_new();
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_wait___boxed(lean_object* v_condvar_28_, lean_object* v_mutex_29_, lean_object* v_a_00___x40___internal___hyg_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lean_io_condvar_wait(v_condvar_28_, v_mutex_29_);
lean_dec(v_mutex_29_);
lean_dec(v_condvar_28_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_notifyOne___boxed(lean_object* v_condvar_34_, lean_object* v_a_00___x40___internal___hyg_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lean_io_condvar_notify_one(v_condvar_34_);
lean_dec(v_condvar_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_notifyAll___boxed(lean_object* v_condvar_39_, lean_object* v_a_00___x40___internal___hyg_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = lean_io_condvar_notify_all(v_condvar_39_);
lean_dec(v_condvar_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__0(lean_object* v___x_42_, lean_object* v_toPure_43_, lean_object* v_r_44_){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_45_, 0, v___x_42_);
v___x_46_ = lean_apply_2(v_toPure_43_, lean_box(0), v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__1(lean_object* v_condvar_47_, lean_object* v_mutex_48_, lean_object* v_inst_49_, lean_object* v_toBind_50_, lean_object* v___f_51_, lean_object* v___x_52_, lean_object* v_toPure_53_, uint8_t v_____do__lift_54_){
_start:
{
if (v_____do__lift_54_ == 0)
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
lean_dec(v_toPure_53_);
v___x_55_ = lean_alloc_closure((void*)(l_Std_Condvar_wait___boxed), 3, 2);
lean_closure_set(v___x_55_, 0, v_condvar_47_);
lean_closure_set(v___x_55_, 1, v_mutex_48_);
v___x_56_ = lean_apply_2(v_inst_49_, lean_box(0), v___x_55_);
v___x_57_ = lean_apply_4(v_toBind_50_, lean_box(0), lean_box(0), v___x_56_, v___f_51_);
return v___x_57_;
}
else
{
lean_object* v___x_58_; lean_object* v___x_59_; 
lean_dec(v___f_51_);
lean_dec(v_toBind_50_);
lean_dec(v_inst_49_);
lean_dec(v_mutex_48_);
lean_dec(v_condvar_47_);
v___x_58_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_58_, 0, v___x_52_);
v___x_59_ = lean_apply_2(v_toPure_53_, lean_box(0), v___x_58_);
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__1___boxed(lean_object* v_condvar_60_, lean_object* v_mutex_61_, lean_object* v_inst_62_, lean_object* v_toBind_63_, lean_object* v___f_64_, lean_object* v___x_65_, lean_object* v_toPure_66_, lean_object* v_____do__lift_67_){
_start:
{
uint8_t v_____do__lift_155__boxed_68_; lean_object* v_res_69_; 
v_____do__lift_155__boxed_68_ = lean_unbox(v_____do__lift_67_);
v_res_69_ = l_Std_Condvar_waitUntil___redArg___lam__1(v_condvar_60_, v_mutex_61_, v_inst_62_, v_toBind_63_, v___f_64_, v___x_65_, v_toPure_66_, v_____do__lift_155__boxed_68_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__2(lean_object* v_toBind_70_, lean_object* v_pred_71_, lean_object* v___f_72_, lean_object* v_x_73_, lean_object* v_____s_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_apply_4(v_toBind_70_, lean_box(0), lean_box(0), v_pred_71_, v___f_72_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__3(lean_object* v_toPure_76_, lean_object* v___x_77_, lean_object* v_____s_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_apply_2(v_toPure_76_, lean_box(0), v___x_77_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg(lean_object* v_inst_80_, lean_object* v_inst_81_, lean_object* v_condvar_82_, lean_object* v_mutex_83_, lean_object* v_pred_84_){
_start:
{
lean_object* v_toApplicative_85_; lean_object* v_toBind_86_; lean_object* v_toPure_87_; lean_object* v___x_88_; lean_object* v___f_89_; lean_object* v___f_90_; lean_object* v___f_91_; lean_object* v___f_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v_toApplicative_85_ = lean_ctor_get(v_inst_80_, 0);
v_toBind_86_ = lean_ctor_get(v_inst_80_, 1);
lean_inc(v_toBind_86_);
v_toPure_87_ = lean_ctor_get(v_toApplicative_85_, 1);
v___x_88_ = lean_box(0);
lean_inc(v_toPure_87_);
v___f_89_ = lean_alloc_closure((void*)(l_Std_Condvar_waitUntil___redArg___lam__0), 3, 2);
lean_closure_set(v___f_89_, 0, v___x_88_);
lean_closure_set(v___f_89_, 1, v_toPure_87_);
lean_inc(v_toPure_87_);
lean_inc(v_toBind_86_);
v___f_90_ = lean_alloc_closure((void*)(l_Std_Condvar_waitUntil___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_90_, 0, v_condvar_82_);
lean_closure_set(v___f_90_, 1, v_mutex_83_);
lean_closure_set(v___f_90_, 2, v_inst_81_);
lean_closure_set(v___f_90_, 3, v_toBind_86_);
lean_closure_set(v___f_90_, 4, v___f_89_);
lean_closure_set(v___f_90_, 5, v___x_88_);
lean_closure_set(v___f_90_, 6, v_toPure_87_);
lean_inc(v_toBind_86_);
v___f_91_ = lean_alloc_closure((void*)(l_Std_Condvar_waitUntil___redArg___lam__2), 5, 3);
lean_closure_set(v___f_91_, 0, v_toBind_86_);
lean_closure_set(v___f_91_, 1, v_pred_84_);
lean_closure_set(v___f_91_, 2, v___f_90_);
lean_inc(v_toPure_87_);
v___f_92_ = lean_alloc_closure((void*)(l_Std_Condvar_waitUntil___redArg___lam__3), 3, 2);
lean_closure_set(v___f_92_, 0, v_toPure_87_);
lean_closure_set(v___f_92_, 1, v___x_88_);
v___x_93_ = l___private_Init_While_0__Lean_Loop_forIn_loop(lean_box(0), lean_box(0), v_inst_80_, v___f_91_, v___x_88_);
v___x_94_ = lean_apply_4(v_toBind_86_, lean_box(0), lean_box(0), v___x_93_, v___f_92_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil(lean_object* v_m_95_, lean_object* v_inst_96_, lean_object* v_inst_97_, lean_object* v_condvar_98_, lean_object* v_mutex_99_, lean_object* v_pred_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Std_Condvar_waitUntil___redArg(v_inst_96_, v_inst_97_, v_condvar_98_, v_mutex_99_, v_pred_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutMutexBaseMutex___lam__0(lean_object* v_self_102_){
_start:
{
lean_object* v_mutex_103_; 
v_mutex_103_ = lean_ctor_get(v_self_102_, 1);
lean_inc(v_mutex_103_);
return v_mutex_103_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutMutexBaseMutex___lam__0___boxed(lean_object* v_self_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Std_instCoeOutMutexBaseMutex___lam__0(v_self_104_);
lean_dec_ref(v_self_104_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutMutexBaseMutex(lean_object* v_00_u03b1_107_){
_start:
{
lean_object* v___f_108_; 
v___f_108_ = ((lean_object*)(l_Std_instCoeOutMutexBaseMutex___closed__0));
return v___f_108_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_new___redArg(lean_object* v_a_109_){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_111_ = lean_st_mk_ref(v_a_109_);
v___x_112_ = lean_io_basemutex_new();
v___x_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_111_);
lean_ctor_set(v___x_113_, 1, v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_new___redArg___boxed(lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Std_Mutex_new___redArg(v_a_114_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_new(lean_object* v_00_u03b1_117_, lean_object* v_a_118_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Std_Mutex_new___redArg(v_a_118_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_new___boxed(lean_object* v_00_u03b1_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Std_Mutex_new(v_00_u03b1_121_, v_a_122_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg___lam__0(lean_object* v_k_125_, lean_object* v_ref_126_, lean_object* v_____r_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = lean_apply_1(v_k_125_, v_ref_126_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg___lam__1(lean_object* v_x_129_){
_start:
{
lean_object* v_fst_130_; 
v_fst_130_ = lean_ctor_get(v_x_129_, 0);
lean_inc(v_fst_130_);
return v_fst_130_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg___lam__1___boxed(lean_object* v_x_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Std_Mutex_atomically___redArg___lam__1(v_x_131_);
lean_dec_ref(v_x_131_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg___lam__2(lean_object* v___x_133_, lean_object* v_x_134_){
_start:
{
lean_inc(v___x_133_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg___lam__2___boxed(lean_object* v___x_135_, lean_object* v_x_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Std_Mutex_atomically___redArg___lam__2(v___x_135_, v_x_136_);
lean_dec(v_x_136_);
lean_dec(v___x_135_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg(lean_object* v_inst_139_, lean_object* v_inst_140_, lean_object* v_inst_141_, lean_object* v_mutex_142_, lean_object* v_k_143_){
_start:
{
lean_object* v_toApplicative_144_; lean_object* v_toFunctor_145_; lean_object* v_toBind_146_; lean_object* v_ref_147_; lean_object* v_mutex_148_; lean_object* v_map_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___f_152_; lean_object* v___f_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___f_157_; lean_object* v_y_158_; lean_object* v___x_159_; 
v_toApplicative_144_ = lean_ctor_get(v_inst_139_, 0);
v_toFunctor_145_ = lean_ctor_get(v_toApplicative_144_, 0);
lean_inc_ref(v_toFunctor_145_);
v_toBind_146_ = lean_ctor_get(v_inst_139_, 1);
lean_inc(v_toBind_146_);
lean_dec_ref(v_inst_139_);
v_ref_147_ = lean_ctor_get(v_mutex_142_, 0);
lean_inc(v_ref_147_);
v_mutex_148_ = lean_ctor_get(v_mutex_142_, 1);
lean_inc(v_mutex_148_);
lean_dec_ref(v_mutex_142_);
v_map_149_ = lean_ctor_get(v_toFunctor_145_, 0);
lean_inc(v_map_149_);
lean_dec_ref(v_toFunctor_145_);
lean_inc(v_mutex_148_);
v___x_150_ = lean_alloc_closure((void*)(l_Std_BaseMutex_lock___boxed), 2, 1);
lean_closure_set(v___x_150_, 0, v_mutex_148_);
lean_inc(v_inst_140_);
v___x_151_ = lean_apply_2(v_inst_140_, lean_box(0), v___x_150_);
v___f_152_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___redArg___lam__0), 3, 2);
lean_closure_set(v___f_152_, 0, v_k_143_);
lean_closure_set(v___f_152_, 1, v_ref_147_);
v___f_153_ = ((lean_object*)(l_Std_Mutex_atomically___redArg___closed__0));
v___x_154_ = lean_apply_4(v_toBind_146_, lean_box(0), lean_box(0), v___x_151_, v___f_152_);
v___x_155_ = lean_alloc_closure((void*)(l_Std_BaseMutex_unlock___boxed), 2, 1);
lean_closure_set(v___x_155_, 0, v_mutex_148_);
v___x_156_ = lean_apply_2(v_inst_140_, lean_box(0), v___x_155_);
v___f_157_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_157_, 0, v___x_156_);
v_y_158_ = lean_apply_4(v_inst_141_, lean_box(0), lean_box(0), v___x_154_, v___f_157_);
v___x_159_ = lean_apply_4(v_map_149_, lean_box(0), lean_box(0), v___f_153_, v_y_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically(lean_object* v_m_160_, lean_object* v_00_u03b1_161_, lean_object* v_00_u03b2_162_, lean_object* v_inst_163_, lean_object* v_inst_164_, lean_object* v_inst_165_, lean_object* v_mutex_166_, lean_object* v_k_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Std_Mutex_atomically___redArg(v_inst_163_, v_inst_164_, v_inst_165_, v_mutex_166_, v_k_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__0(lean_object* v_x_169_){
_start:
{
lean_object* v_fst_170_; 
v_fst_170_ = lean_ctor_get(v_x_169_, 0);
lean_inc(v_fst_170_);
return v_fst_170_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__0___boxed(lean_object* v_x_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Std_Mutex_tryAtomically___redArg___lam__0(v_x_171_);
lean_dec_ref(v_x_171_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__1(lean_object* v_val_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_174_, 0, v_val_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__2(lean_object* v___x_175_, lean_object* v_x_176_){
_start:
{
lean_inc(v___x_175_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__2___boxed(lean_object* v___x_177_, lean_object* v_x_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Std_Mutex_tryAtomically___redArg___lam__2(v___x_177_, v_x_178_);
lean_dec(v_x_178_);
lean_dec(v___x_177_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__3(lean_object* v_toApplicative_180_, lean_object* v_k_181_, lean_object* v_ref_182_, lean_object* v___f_183_, lean_object* v_mutex_184_, lean_object* v_inst_185_, lean_object* v_inst_186_, lean_object* v___f_187_, uint8_t v_____do__lift_188_){
_start:
{
if (v_____do__lift_188_ == 0)
{
lean_object* v_toPure_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
lean_dec_ref(v___f_187_);
lean_dec(v_inst_186_);
lean_dec(v_inst_185_);
lean_dec(v_mutex_184_);
lean_dec_ref(v___f_183_);
lean_dec(v_ref_182_);
lean_dec(v_k_181_);
v_toPure_189_ = lean_ctor_get(v_toApplicative_180_, 1);
lean_inc(v_toPure_189_);
lean_dec_ref(v_toApplicative_180_);
v___x_190_ = lean_box(0);
v___x_191_ = lean_apply_2(v_toPure_189_, lean_box(0), v___x_190_);
return v___x_191_;
}
else
{
lean_object* v_toFunctor_192_; lean_object* v_map_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___f_198_; lean_object* v_y_199_; lean_object* v___x_200_; 
v_toFunctor_192_ = lean_ctor_get(v_toApplicative_180_, 0);
lean_inc_ref(v_toFunctor_192_);
lean_dec_ref(v_toApplicative_180_);
v_map_193_ = lean_ctor_get(v_toFunctor_192_, 0);
lean_inc(v_map_193_);
lean_dec_ref(v_toFunctor_192_);
v___x_194_ = lean_apply_1(v_k_181_, v_ref_182_);
lean_inc(v_map_193_);
v___x_195_ = lean_apply_4(v_map_193_, lean_box(0), lean_box(0), v___f_183_, v___x_194_);
v___x_196_ = lean_alloc_closure((void*)(l_Std_BaseMutex_unlock___boxed), 2, 1);
lean_closure_set(v___x_196_, 0, v_mutex_184_);
v___x_197_ = lean_apply_2(v_inst_185_, lean_box(0), v___x_196_);
v___f_198_ = lean_alloc_closure((void*)(l_Std_Mutex_tryAtomically___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_198_, 0, v___x_197_);
v_y_199_ = lean_apply_4(v_inst_186_, lean_box(0), lean_box(0), v___x_195_, v___f_198_);
v___x_200_ = lean_apply_4(v_map_193_, lean_box(0), lean_box(0), v___f_187_, v_y_199_);
return v___x_200_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__3___boxed(lean_object* v_toApplicative_201_, lean_object* v_k_202_, lean_object* v_ref_203_, lean_object* v___f_204_, lean_object* v_mutex_205_, lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v___f_208_, lean_object* v_____do__lift_209_){
_start:
{
uint8_t v_____do__lift_140__boxed_210_; lean_object* v_res_211_; 
v_____do__lift_140__boxed_210_ = lean_unbox(v_____do__lift_209_);
v_res_211_ = l_Std_Mutex_tryAtomically___redArg___lam__3(v_toApplicative_201_, v_k_202_, v_ref_203_, v___f_204_, v_mutex_205_, v_inst_206_, v_inst_207_, v___f_208_, v_____do__lift_140__boxed_210_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg(lean_object* v_inst_214_, lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_mutex_217_, lean_object* v_k_218_){
_start:
{
lean_object* v_toApplicative_219_; lean_object* v_toBind_220_; lean_object* v_ref_221_; lean_object* v_mutex_222_; lean_object* v___f_223_; lean_object* v___f_224_; lean_object* v___f_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v_toApplicative_219_ = lean_ctor_get(v_inst_214_, 0);
lean_inc_ref(v_toApplicative_219_);
v_toBind_220_ = lean_ctor_get(v_inst_214_, 1);
lean_inc(v_toBind_220_);
lean_dec_ref(v_inst_214_);
v_ref_221_ = lean_ctor_get(v_mutex_217_, 0);
lean_inc(v_ref_221_);
v_mutex_222_ = lean_ctor_get(v_mutex_217_, 1);
lean_inc(v_mutex_222_);
lean_dec_ref(v_mutex_217_);
v___f_223_ = ((lean_object*)(l_Std_Mutex_tryAtomically___redArg___closed__0));
v___f_224_ = ((lean_object*)(l_Std_Mutex_tryAtomically___redArg___closed__1));
lean_inc(v_inst_215_);
lean_inc(v_mutex_222_);
v___f_225_ = lean_alloc_closure((void*)(l_Std_Mutex_tryAtomically___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_225_, 0, v_toApplicative_219_);
lean_closure_set(v___f_225_, 1, v_k_218_);
lean_closure_set(v___f_225_, 2, v_ref_221_);
lean_closure_set(v___f_225_, 3, v___f_224_);
lean_closure_set(v___f_225_, 4, v_mutex_222_);
lean_closure_set(v___f_225_, 5, v_inst_215_);
lean_closure_set(v___f_225_, 6, v_inst_216_);
lean_closure_set(v___f_225_, 7, v___f_223_);
v___x_226_ = lean_alloc_closure((void*)(l_Std_BaseMutex_tryLock___boxed), 2, 1);
lean_closure_set(v___x_226_, 0, v_mutex_222_);
v___x_227_ = lean_apply_2(v_inst_215_, lean_box(0), v___x_226_);
v___x_228_ = lean_apply_4(v_toBind_220_, lean_box(0), lean_box(0), v___x_227_, v___f_225_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically(lean_object* v_m_229_, lean_object* v_00_u03b1_230_, lean_object* v_00_u03b2_231_, lean_object* v_inst_232_, lean_object* v_inst_233_, lean_object* v_inst_234_, lean_object* v_mutex_235_, lean_object* v_k_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Std_Mutex_tryAtomically___redArg(v_inst_232_, v_inst_233_, v_inst_234_, v_mutex_235_, v_k_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomicallyOnce___redArg___lam__0(lean_object* v_k_238_, lean_object* v_____r_239_, lean_object* v___y_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = lean_apply_1(v_k_238_, v___y_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomicallyOnce___redArg(lean_object* v_inst_244_, lean_object* v_inst_245_, lean_object* v_inst_246_, lean_object* v_mutex_247_, lean_object* v_condvar_248_, lean_object* v_pred_249_, lean_object* v_k_250_){
_start:
{
lean_object* v___x_251_; lean_object* v_mutex_252_; lean_object* v___f_253_; lean_object* v___f_254_; lean_object* v___x_255_; lean_object* v___f_256_; lean_object* v_x_257_; lean_object* v___f_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
lean_inc_ref(v_inst_244_);
v___x_251_ = l_ReaderT_instMonad___redArg(v_inst_244_);
v_mutex_252_ = lean_ctor_get(v_mutex_247_, 1);
v___f_253_ = lean_alloc_closure((void*)(l_Std_Mutex_atomicallyOnce___redArg___lam__0), 3, 1);
lean_closure_set(v___f_253_, 0, v_k_250_);
v___f_254_ = ((lean_object*)(l_Std_Mutex_atomicallyOnce___redArg___closed__0));
v___x_255_ = ((lean_object*)(l_Std_Mutex_atomicallyOnce___redArg___closed__1));
lean_inc(v_inst_245_);
v___f_256_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_256_, 0, v_inst_245_);
lean_closure_set(v___f_256_, 1, v___x_255_);
v_x_257_ = lean_alloc_closure((void*)(l_liftM), 5, 3);
lean_closure_set(v_x_257_, 0, lean_box(0));
lean_closure_set(v_x_257_, 1, lean_box(0));
lean_closure_set(v_x_257_, 2, v___f_256_);
v___f_258_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_258_, 0, v___f_254_);
lean_closure_set(v___f_258_, 1, v_x_257_);
lean_inc(v_mutex_252_);
v___x_259_ = l_Std_Condvar_waitUntil___redArg(v___x_251_, v___f_258_, v_condvar_248_, v_mutex_252_, v_pred_249_);
lean_inc_ref(v_inst_244_);
v___x_260_ = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(v___x_260_, 0, lean_box(0));
lean_closure_set(v___x_260_, 1, lean_box(0));
lean_closure_set(v___x_260_, 2, v_inst_244_);
lean_closure_set(v___x_260_, 3, lean_box(0));
lean_closure_set(v___x_260_, 4, lean_box(0));
lean_closure_set(v___x_260_, 5, v___x_259_);
lean_closure_set(v___x_260_, 6, v___f_253_);
v___x_261_ = l_Std_Mutex_atomically___redArg(v_inst_244_, v_inst_245_, v_inst_246_, v_mutex_247_, v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomicallyOnce(lean_object* v_m_262_, lean_object* v_00_u03b1_263_, lean_object* v_00_u03b2_264_, lean_object* v_inst_265_, lean_object* v_inst_266_, lean_object* v_inst_267_, lean_object* v_mutex_268_, lean_object* v_condvar_269_, lean_object* v_pred_270_, lean_object* v_k_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Std_Mutex_atomicallyOnce___redArg(v_inst_265_, v_inst_266_, v_inst_267_, v_mutex_268_, v_condvar_269_, v_pred_270_, v_k_271_);
return v___x_272_;
}
}
lean_object* runtime_initialize_Std_Sync_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sync_Mutex(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Sync_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Std_Sync_Mutex_0__Std_BaseMutexImpl = _init_l___private_Std_Sync_Mutex_0__Std_BaseMutexImpl();
l___private_Std_Sync_Mutex_0__Std_CondvarImpl = _init_l___private_Std_Sync_Mutex_0__Std_CondvarImpl();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sync_Mutex(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sync_Basic(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sync_Mutex(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sync_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sync_Mutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sync_Mutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sync_Mutex(builtin);
}
#ifdef __cplusplus
}
#endif
