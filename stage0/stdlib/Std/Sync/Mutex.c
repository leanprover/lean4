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
lean_object* l___private_Init_While_0__repeatM_erased___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_liftM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonad___aux__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__4(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Mutex_atomicallyOnce___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__0(lean_object* v_toPure_42_, lean_object* v_____do__lift_43_){
_start:
{
if (lean_obj_tag(v_____do__lift_43_) == 0)
{
lean_object* v_a_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_52_; 
v_a_44_ = lean_ctor_get(v_____do__lift_43_, 0);
v_isSharedCheck_52_ = !lean_is_exclusive(v_____do__lift_43_);
if (v_isSharedCheck_52_ == 0)
{
v___x_46_ = v_____do__lift_43_;
v_isShared_47_ = v_isSharedCheck_52_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_a_44_);
lean_dec(v_____do__lift_43_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_52_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_49_; 
if (v_isShared_47_ == 0)
{
lean_ctor_set_tag(v___x_46_, 1);
v___x_49_ = v___x_46_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_a_44_);
v___x_49_ = v_reuseFailAlloc_51_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
lean_object* v___x_50_; 
v___x_50_ = lean_apply_2(v_toPure_42_, lean_box(0), v___x_49_);
return v___x_50_;
}
}
}
else
{
lean_object* v_a_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_61_; 
v_a_53_ = lean_ctor_get(v_____do__lift_43_, 0);
v_isSharedCheck_61_ = !lean_is_exclusive(v_____do__lift_43_);
if (v_isSharedCheck_61_ == 0)
{
v___x_55_ = v_____do__lift_43_;
v_isShared_56_ = v_isSharedCheck_61_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_a_53_);
lean_dec(v_____do__lift_43_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_61_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_58_; 
if (v_isShared_56_ == 0)
{
lean_ctor_set_tag(v___x_55_, 0);
v___x_58_ = v___x_55_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_a_53_);
v___x_58_ = v_reuseFailAlloc_60_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
lean_object* v___x_59_; 
v___x_59_ = lean_apply_2(v_toPure_42_, lean_box(0), v___x_58_);
return v___x_59_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__1(lean_object* v___x_62_, lean_object* v_toPure_63_, lean_object* v_r_64_){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_65_, 0, v___x_62_);
v___x_66_ = lean_apply_2(v_toPure_63_, lean_box(0), v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__2(lean_object* v_condvar_67_, lean_object* v_mutex_68_, lean_object* v_inst_69_, lean_object* v_toBind_70_, lean_object* v___f_71_, lean_object* v___x_72_, lean_object* v_toPure_73_, uint8_t v_____do__lift_74_){
_start:
{
if (v_____do__lift_74_ == 0)
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
lean_dec(v_toPure_73_);
v___x_75_ = lean_alloc_closure((void*)(l_Std_Condvar_wait___boxed), 3, 2);
lean_closure_set(v___x_75_, 0, v_condvar_67_);
lean_closure_set(v___x_75_, 1, v_mutex_68_);
v___x_76_ = lean_apply_2(v_inst_69_, lean_box(0), v___x_75_);
v___x_77_ = lean_apply_4(v_toBind_70_, lean_box(0), lean_box(0), v___x_76_, v___f_71_);
return v___x_77_;
}
else
{
lean_object* v___x_78_; lean_object* v___x_79_; 
lean_dec(v___f_71_);
lean_dec(v_toBind_70_);
lean_dec(v_inst_69_);
lean_dec(v_mutex_68_);
lean_dec(v_condvar_67_);
v___x_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_72_);
v___x_79_ = lean_apply_2(v_toPure_73_, lean_box(0), v___x_78_);
return v___x_79_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__2___boxed(lean_object* v_condvar_80_, lean_object* v_mutex_81_, lean_object* v_inst_82_, lean_object* v_toBind_83_, lean_object* v___f_84_, lean_object* v___x_85_, lean_object* v_toPure_86_, lean_object* v_____do__lift_87_){
_start:
{
uint8_t v_____do__lift_261__boxed_88_; lean_object* v_res_89_; 
v_____do__lift_261__boxed_88_ = lean_unbox(v_____do__lift_87_);
v_res_89_ = l_Std_Condvar_waitUntil___redArg___lam__2(v_condvar_80_, v_mutex_81_, v_inst_82_, v_toBind_83_, v___f_84_, v___x_85_, v_toPure_86_, v_____do__lift_261__boxed_88_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__3(lean_object* v_toBind_90_, lean_object* v_pred_91_, lean_object* v___f_92_, lean_object* v___f_93_, lean_object* v_b_94_){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
lean_inc(v_toBind_90_);
v___x_95_ = lean_apply_4(v_toBind_90_, lean_box(0), lean_box(0), v_pred_91_, v___f_92_);
v___x_96_ = lean_apply_4(v_toBind_90_, lean_box(0), lean_box(0), v___x_95_, v___f_93_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__4(lean_object* v_toPure_97_, lean_object* v___x_98_, lean_object* v_____s_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lean_apply_2(v_toPure_97_, lean_box(0), v___x_98_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg(lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_condvar_103_, lean_object* v_mutex_104_, lean_object* v_pred_105_){
_start:
{
lean_object* v_toApplicative_106_; lean_object* v_toBind_107_; lean_object* v_toPure_108_; lean_object* v___x_109_; lean_object* v___f_110_; lean_object* v___f_111_; lean_object* v___f_112_; lean_object* v___f_113_; lean_object* v___f_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v_toApplicative_106_ = lean_ctor_get(v_inst_101_, 0);
v_toBind_107_ = lean_ctor_get(v_inst_101_, 1);
lean_inc_n(v_toBind_107_, 3);
v_toPure_108_ = lean_ctor_get(v_toApplicative_106_, 1);
v___x_109_ = lean_box(0);
lean_inc_n(v_toPure_108_, 4);
v___f_110_ = lean_alloc_closure((void*)(l_Std_Condvar_waitUntil___redArg___lam__0), 2, 1);
lean_closure_set(v___f_110_, 0, v_toPure_108_);
v___f_111_ = lean_alloc_closure((void*)(l_Std_Condvar_waitUntil___redArg___lam__1), 3, 2);
lean_closure_set(v___f_111_, 0, v___x_109_);
lean_closure_set(v___f_111_, 1, v_toPure_108_);
v___f_112_ = lean_alloc_closure((void*)(l_Std_Condvar_waitUntil___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_112_, 0, v_condvar_103_);
lean_closure_set(v___f_112_, 1, v_mutex_104_);
lean_closure_set(v___f_112_, 2, v_inst_102_);
lean_closure_set(v___f_112_, 3, v_toBind_107_);
lean_closure_set(v___f_112_, 4, v___f_111_);
lean_closure_set(v___f_112_, 5, v___x_109_);
lean_closure_set(v___f_112_, 6, v_toPure_108_);
v___f_113_ = lean_alloc_closure((void*)(l_Std_Condvar_waitUntil___redArg___lam__3), 5, 4);
lean_closure_set(v___f_113_, 0, v_toBind_107_);
lean_closure_set(v___f_113_, 1, v_pred_105_);
lean_closure_set(v___f_113_, 2, v___f_112_);
lean_closure_set(v___f_113_, 3, v___f_110_);
v___f_114_ = lean_alloc_closure((void*)(l_Std_Condvar_waitUntil___redArg___lam__4), 3, 2);
lean_closure_set(v___f_114_, 0, v_toPure_108_);
lean_closure_set(v___f_114_, 1, v___x_109_);
v___x_115_ = l___private_Init_While_0__repeatM_erased___redArg(v_inst_101_, v___f_113_, v___x_109_);
v___x_116_ = lean_apply_4(v_toBind_107_, lean_box(0), lean_box(0), v___x_115_, v___f_114_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil(lean_object* v_m_117_, lean_object* v_inst_118_, lean_object* v_inst_119_, lean_object* v_condvar_120_, lean_object* v_mutex_121_, lean_object* v_pred_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Std_Condvar_waitUntil___redArg(v_inst_118_, v_inst_119_, v_condvar_120_, v_mutex_121_, v_pred_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutMutexBaseMutex___lam__0(lean_object* v_self_124_){
_start:
{
lean_object* v_mutex_125_; 
v_mutex_125_ = lean_ctor_get(v_self_124_, 1);
lean_inc(v_mutex_125_);
return v_mutex_125_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutMutexBaseMutex___lam__0___boxed(lean_object* v_self_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Std_instCoeOutMutexBaseMutex___lam__0(v_self_126_);
lean_dec_ref(v_self_126_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutMutexBaseMutex(lean_object* v_00_u03b1_129_){
_start:
{
lean_object* v___f_130_; 
v___f_130_ = ((lean_object*)(l_Std_instCoeOutMutexBaseMutex___closed__0));
return v___f_130_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_new___redArg(lean_object* v_a_131_){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_133_ = lean_st_mk_ref(v_a_131_);
v___x_134_ = lean_io_basemutex_new();
v___x_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_133_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_new___redArg___boxed(lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Std_Mutex_new___redArg(v_a_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_new(lean_object* v_00_u03b1_139_, lean_object* v_a_140_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Std_Mutex_new___redArg(v_a_140_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_new___boxed(lean_object* v_00_u03b1_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Std_Mutex_new(v_00_u03b1_143_, v_a_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg___lam__0(lean_object* v_k_147_, lean_object* v_ref_148_, lean_object* v_____r_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = lean_apply_1(v_k_147_, v_ref_148_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg___lam__1(lean_object* v_x_151_){
_start:
{
lean_object* v_fst_152_; 
v_fst_152_ = lean_ctor_get(v_x_151_, 0);
lean_inc(v_fst_152_);
return v_fst_152_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg___lam__1___boxed(lean_object* v_x_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Std_Mutex_atomically___redArg___lam__1(v_x_153_);
lean_dec_ref(v_x_153_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg___lam__2(lean_object* v___x_155_, lean_object* v_x_156_){
_start:
{
lean_inc(v___x_155_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg___lam__2___boxed(lean_object* v___x_157_, lean_object* v_x_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Std_Mutex_atomically___redArg___lam__2(v___x_157_, v_x_158_);
lean_dec(v_x_158_);
lean_dec(v___x_157_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg(lean_object* v_inst_161_, lean_object* v_inst_162_, lean_object* v_inst_163_, lean_object* v_mutex_164_, lean_object* v_k_165_){
_start:
{
lean_object* v_toApplicative_166_; lean_object* v_toFunctor_167_; lean_object* v_toBind_168_; lean_object* v_ref_169_; lean_object* v_mutex_170_; lean_object* v_map_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___f_174_; lean_object* v___f_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___f_179_; lean_object* v_y_180_; lean_object* v___x_181_; 
v_toApplicative_166_ = lean_ctor_get(v_inst_161_, 0);
v_toFunctor_167_ = lean_ctor_get(v_toApplicative_166_, 0);
lean_inc_ref(v_toFunctor_167_);
v_toBind_168_ = lean_ctor_get(v_inst_161_, 1);
lean_inc(v_toBind_168_);
lean_dec_ref(v_inst_161_);
v_ref_169_ = lean_ctor_get(v_mutex_164_, 0);
lean_inc(v_ref_169_);
v_mutex_170_ = lean_ctor_get(v_mutex_164_, 1);
lean_inc_n(v_mutex_170_, 2);
lean_dec_ref(v_mutex_164_);
v_map_171_ = lean_ctor_get(v_toFunctor_167_, 0);
lean_inc(v_map_171_);
lean_dec_ref(v_toFunctor_167_);
v___x_172_ = lean_alloc_closure((void*)(l_Std_BaseMutex_lock___boxed), 2, 1);
lean_closure_set(v___x_172_, 0, v_mutex_170_);
lean_inc(v_inst_162_);
v___x_173_ = lean_apply_2(v_inst_162_, lean_box(0), v___x_172_);
v___f_174_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___redArg___lam__0), 3, 2);
lean_closure_set(v___f_174_, 0, v_k_165_);
lean_closure_set(v___f_174_, 1, v_ref_169_);
v___f_175_ = ((lean_object*)(l_Std_Mutex_atomically___redArg___closed__0));
v___x_176_ = lean_apply_4(v_toBind_168_, lean_box(0), lean_box(0), v___x_173_, v___f_174_);
v___x_177_ = lean_alloc_closure((void*)(l_Std_BaseMutex_unlock___boxed), 2, 1);
lean_closure_set(v___x_177_, 0, v_mutex_170_);
v___x_178_ = lean_apply_2(v_inst_162_, lean_box(0), v___x_177_);
v___f_179_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_179_, 0, v___x_178_);
v_y_180_ = lean_apply_4(v_inst_163_, lean_box(0), lean_box(0), v___x_176_, v___f_179_);
v___x_181_ = lean_apply_4(v_map_171_, lean_box(0), lean_box(0), v___f_175_, v_y_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically(lean_object* v_m_182_, lean_object* v_00_u03b1_183_, lean_object* v_00_u03b2_184_, lean_object* v_inst_185_, lean_object* v_inst_186_, lean_object* v_inst_187_, lean_object* v_mutex_188_, lean_object* v_k_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Std_Mutex_atomically___redArg(v_inst_185_, v_inst_186_, v_inst_187_, v_mutex_188_, v_k_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__0(lean_object* v_x_191_){
_start:
{
lean_object* v_fst_192_; 
v_fst_192_ = lean_ctor_get(v_x_191_, 0);
lean_inc(v_fst_192_);
return v_fst_192_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__0___boxed(lean_object* v_x_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Std_Mutex_tryAtomically___redArg___lam__0(v_x_193_);
lean_dec_ref(v_x_193_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__1(lean_object* v_val_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_196_, 0, v_val_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__2(lean_object* v___x_197_, lean_object* v_x_198_){
_start:
{
lean_inc(v___x_197_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__2___boxed(lean_object* v___x_199_, lean_object* v_x_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Std_Mutex_tryAtomically___redArg___lam__2(v___x_199_, v_x_200_);
lean_dec(v_x_200_);
lean_dec(v___x_199_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__3(lean_object* v_toApplicative_202_, lean_object* v_k_203_, lean_object* v_ref_204_, lean_object* v___f_205_, lean_object* v_mutex_206_, lean_object* v_inst_207_, lean_object* v_inst_208_, lean_object* v___f_209_, uint8_t v_____do__lift_210_){
_start:
{
if (v_____do__lift_210_ == 0)
{
lean_object* v_toPure_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec_ref(v___f_209_);
lean_dec(v_inst_208_);
lean_dec(v_inst_207_);
lean_dec(v_mutex_206_);
lean_dec_ref(v___f_205_);
lean_dec(v_ref_204_);
lean_dec(v_k_203_);
v_toPure_211_ = lean_ctor_get(v_toApplicative_202_, 1);
lean_inc(v_toPure_211_);
lean_dec_ref(v_toApplicative_202_);
v___x_212_ = lean_box(0);
v___x_213_ = lean_apply_2(v_toPure_211_, lean_box(0), v___x_212_);
return v___x_213_;
}
else
{
lean_object* v_toFunctor_214_; lean_object* v_map_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___f_220_; lean_object* v_y_221_; lean_object* v___x_222_; 
v_toFunctor_214_ = lean_ctor_get(v_toApplicative_202_, 0);
lean_inc_ref(v_toFunctor_214_);
lean_dec_ref(v_toApplicative_202_);
v_map_215_ = lean_ctor_get(v_toFunctor_214_, 0);
lean_inc_n(v_map_215_, 2);
lean_dec_ref(v_toFunctor_214_);
v___x_216_ = lean_apply_1(v_k_203_, v_ref_204_);
v___x_217_ = lean_apply_4(v_map_215_, lean_box(0), lean_box(0), v___f_205_, v___x_216_);
v___x_218_ = lean_alloc_closure((void*)(l_Std_BaseMutex_unlock___boxed), 2, 1);
lean_closure_set(v___x_218_, 0, v_mutex_206_);
v___x_219_ = lean_apply_2(v_inst_207_, lean_box(0), v___x_218_);
v___f_220_ = lean_alloc_closure((void*)(l_Std_Mutex_tryAtomically___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_220_, 0, v___x_219_);
v_y_221_ = lean_apply_4(v_inst_208_, lean_box(0), lean_box(0), v___x_217_, v___f_220_);
v___x_222_ = lean_apply_4(v_map_215_, lean_box(0), lean_box(0), v___f_209_, v_y_221_);
return v___x_222_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__3___boxed(lean_object* v_toApplicative_223_, lean_object* v_k_224_, lean_object* v_ref_225_, lean_object* v___f_226_, lean_object* v_mutex_227_, lean_object* v_inst_228_, lean_object* v_inst_229_, lean_object* v___f_230_, lean_object* v_____do__lift_231_){
_start:
{
uint8_t v_____do__lift_140__boxed_232_; lean_object* v_res_233_; 
v_____do__lift_140__boxed_232_ = lean_unbox(v_____do__lift_231_);
v_res_233_ = l_Std_Mutex_tryAtomically___redArg___lam__3(v_toApplicative_223_, v_k_224_, v_ref_225_, v___f_226_, v_mutex_227_, v_inst_228_, v_inst_229_, v___f_230_, v_____do__lift_140__boxed_232_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg(lean_object* v_inst_236_, lean_object* v_inst_237_, lean_object* v_inst_238_, lean_object* v_mutex_239_, lean_object* v_k_240_){
_start:
{
lean_object* v_toApplicative_241_; lean_object* v_toBind_242_; lean_object* v_ref_243_; lean_object* v_mutex_244_; lean_object* v___f_245_; lean_object* v___f_246_; lean_object* v___f_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v_toApplicative_241_ = lean_ctor_get(v_inst_236_, 0);
lean_inc_ref(v_toApplicative_241_);
v_toBind_242_ = lean_ctor_get(v_inst_236_, 1);
lean_inc(v_toBind_242_);
lean_dec_ref(v_inst_236_);
v_ref_243_ = lean_ctor_get(v_mutex_239_, 0);
lean_inc(v_ref_243_);
v_mutex_244_ = lean_ctor_get(v_mutex_239_, 1);
lean_inc_n(v_mutex_244_, 2);
lean_dec_ref(v_mutex_239_);
v___f_245_ = ((lean_object*)(l_Std_Mutex_tryAtomically___redArg___closed__0));
v___f_246_ = ((lean_object*)(l_Std_Mutex_tryAtomically___redArg___closed__1));
lean_inc(v_inst_237_);
v___f_247_ = lean_alloc_closure((void*)(l_Std_Mutex_tryAtomically___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_247_, 0, v_toApplicative_241_);
lean_closure_set(v___f_247_, 1, v_k_240_);
lean_closure_set(v___f_247_, 2, v_ref_243_);
lean_closure_set(v___f_247_, 3, v___f_246_);
lean_closure_set(v___f_247_, 4, v_mutex_244_);
lean_closure_set(v___f_247_, 5, v_inst_237_);
lean_closure_set(v___f_247_, 6, v_inst_238_);
lean_closure_set(v___f_247_, 7, v___f_245_);
v___x_248_ = lean_alloc_closure((void*)(l_Std_BaseMutex_tryLock___boxed), 2, 1);
lean_closure_set(v___x_248_, 0, v_mutex_244_);
v___x_249_ = lean_apply_2(v_inst_237_, lean_box(0), v___x_248_);
v___x_250_ = lean_apply_4(v_toBind_242_, lean_box(0), lean_box(0), v___x_249_, v___f_247_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically(lean_object* v_m_251_, lean_object* v_00_u03b1_252_, lean_object* v_00_u03b2_253_, lean_object* v_inst_254_, lean_object* v_inst_255_, lean_object* v_inst_256_, lean_object* v_mutex_257_, lean_object* v_k_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Std_Mutex_tryAtomically___redArg(v_inst_254_, v_inst_255_, v_inst_256_, v_mutex_257_, v_k_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomicallyOnce___redArg___lam__0(lean_object* v_k_260_, lean_object* v_____r_261_, lean_object* v___y_262_){
_start:
{
lean_object* v___x_263_; 
lean_inc(v___y_262_);
v___x_263_ = lean_apply_1(v_k_260_, v___y_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomicallyOnce___redArg___lam__0___boxed(lean_object* v_k_264_, lean_object* v_____r_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Std_Mutex_atomicallyOnce___redArg___lam__0(v_k_264_, v_____r_265_, v___y_266_);
lean_dec(v___y_266_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomicallyOnce___redArg(lean_object* v_inst_270_, lean_object* v_inst_271_, lean_object* v_inst_272_, lean_object* v_mutex_273_, lean_object* v_condvar_274_, lean_object* v_pred_275_, lean_object* v_k_276_){
_start:
{
lean_object* v___x_277_; lean_object* v_mutex_278_; lean_object* v___f_279_; lean_object* v___f_280_; lean_object* v___x_281_; lean_object* v___f_282_; lean_object* v_x_283_; lean_object* v___f_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
lean_inc_ref_n(v_inst_270_, 2);
v___x_277_ = l_StateRefT_x27_instMonad___redArg(v_inst_270_);
v_mutex_278_ = lean_ctor_get(v_mutex_273_, 1);
v___f_279_ = lean_alloc_closure((void*)(l_Std_Mutex_atomicallyOnce___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_279_, 0, v_k_276_);
v___f_280_ = ((lean_object*)(l_Std_Mutex_atomicallyOnce___redArg___closed__0));
v___x_281_ = ((lean_object*)(l_Std_Mutex_atomicallyOnce___redArg___closed__1));
lean_inc(v_inst_271_);
v___f_282_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_282_, 0, v_inst_271_);
lean_closure_set(v___f_282_, 1, v___x_281_);
v_x_283_ = lean_alloc_closure((void*)(l_liftM), 5, 3);
lean_closure_set(v_x_283_, 0, lean_box(0));
lean_closure_set(v_x_283_, 1, lean_box(0));
lean_closure_set(v_x_283_, 2, v___f_282_);
v___f_284_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_284_, 0, v___f_280_);
lean_closure_set(v___f_284_, 1, v_x_283_);
lean_inc(v_mutex_278_);
v___x_285_ = l_Std_Condvar_waitUntil___redArg(v___x_277_, v___f_284_, v_condvar_274_, v_mutex_278_, v_pred_275_);
v___x_286_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_286_, 0, lean_box(0));
lean_closure_set(v___x_286_, 1, lean_box(0));
lean_closure_set(v___x_286_, 2, lean_box(0));
lean_closure_set(v___x_286_, 3, v_inst_270_);
lean_closure_set(v___x_286_, 4, lean_box(0));
lean_closure_set(v___x_286_, 5, lean_box(0));
lean_closure_set(v___x_286_, 6, v___x_285_);
lean_closure_set(v___x_286_, 7, v___f_279_);
v___x_287_ = l_Std_Mutex_atomically___redArg(v_inst_270_, v_inst_271_, v_inst_272_, v_mutex_273_, v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomicallyOnce(lean_object* v_m_288_, lean_object* v_00_u03b1_289_, lean_object* v_00_u03b2_290_, lean_object* v_inst_291_, lean_object* v_inst_292_, lean_object* v_inst_293_, lean_object* v_mutex_294_, lean_object* v_condvar_295_, lean_object* v_pred_296_, lean_object* v_k_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Std_Mutex_atomicallyOnce___redArg(v_inst_291_, v_inst_292_, v_inst_293_, v_mutex_294_, v_condvar_295_, v_pred_296_, v_k_297_);
return v___x_298_;
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
