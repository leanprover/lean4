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
uint8_t lean_bool_not(uint8_t);
lean_object* l___private_Init_While_0__repeatM_erased___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_liftM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__2(lean_object* v___x_67_, lean_object* v_toPure_68_, lean_object* v_condvar_69_, lean_object* v_mutex_70_, lean_object* v_inst_71_, lean_object* v_toBind_72_, lean_object* v___f_73_, uint8_t v_____do__lift_74_){
_start:
{
uint8_t v___x_75_; 
v___x_75_ = lean_bool_not(v_____do__lift_74_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; lean_object* v___x_77_; 
lean_dec(v___f_73_);
lean_dec(v_toBind_72_);
lean_dec(v_inst_71_);
lean_dec(v_mutex_70_);
lean_dec(v_condvar_69_);
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_67_);
v___x_77_ = lean_apply_2(v_toPure_68_, lean_box(0), v___x_76_);
return v___x_77_;
}
else
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
lean_dec(v_toPure_68_);
v___x_78_ = lean_alloc_closure((void*)(l_Std_Condvar_wait___boxed), 3, 2);
lean_closure_set(v___x_78_, 0, v_condvar_69_);
lean_closure_set(v___x_78_, 1, v_mutex_70_);
v___x_79_ = lean_apply_2(v_inst_71_, lean_box(0), v___x_78_);
v___x_80_ = lean_apply_4(v_toBind_72_, lean_box(0), lean_box(0), v___x_79_, v___f_73_);
return v___x_80_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__2___boxed(lean_object* v___x_81_, lean_object* v_toPure_82_, lean_object* v_condvar_83_, lean_object* v_mutex_84_, lean_object* v_inst_85_, lean_object* v_toBind_86_, lean_object* v___f_87_, lean_object* v_____do__lift_88_){
_start:
{
uint8_t v_____do__lift_229__boxed_89_; lean_object* v_res_90_; 
v_____do__lift_229__boxed_89_ = lean_unbox(v_____do__lift_88_);
v_res_90_ = l_Std_Condvar_waitUntil___redArg___lam__2(v___x_81_, v_toPure_82_, v_condvar_83_, v_mutex_84_, v_inst_85_, v_toBind_86_, v___f_87_, v_____do__lift_229__boxed_89_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__3(lean_object* v_toBind_91_, lean_object* v_pred_92_, lean_object* v___f_93_, lean_object* v___f_94_, lean_object* v_b_95_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
lean_inc(v_toBind_91_);
v___x_96_ = lean_apply_4(v_toBind_91_, lean_box(0), lean_box(0), v_pred_92_, v___f_93_);
v___x_97_ = lean_apply_4(v_toBind_91_, lean_box(0), lean_box(0), v___x_96_, v___f_94_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__4(lean_object* v_toPure_98_, lean_object* v___x_99_, lean_object* v_____s_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = lean_apply_2(v_toPure_98_, lean_box(0), v___x_99_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg(lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_condvar_104_, lean_object* v_mutex_105_, lean_object* v_pred_106_){
_start:
{
lean_object* v_toApplicative_107_; lean_object* v_toBind_108_; lean_object* v_toPure_109_; lean_object* v___x_110_; lean_object* v___f_111_; lean_object* v___f_112_; lean_object* v___f_113_; lean_object* v___f_114_; lean_object* v___f_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v_toApplicative_107_ = lean_ctor_get(v_inst_102_, 0);
v_toBind_108_ = lean_ctor_get(v_inst_102_, 1);
lean_inc_n(v_toBind_108_, 3);
v_toPure_109_ = lean_ctor_get(v_toApplicative_107_, 1);
v___x_110_ = lean_box(0);
lean_inc_n(v_toPure_109_, 4);
v___f_111_ = lean_alloc_closure((void*)(l_Std_Condvar_waitUntil___redArg___lam__0), 2, 1);
lean_closure_set(v___f_111_, 0, v_toPure_109_);
v___f_112_ = lean_alloc_closure((void*)(l_Std_Condvar_waitUntil___redArg___lam__1), 3, 2);
lean_closure_set(v___f_112_, 0, v___x_110_);
lean_closure_set(v___f_112_, 1, v_toPure_109_);
v___f_113_ = lean_alloc_closure((void*)(l_Std_Condvar_waitUntil___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_113_, 0, v___x_110_);
lean_closure_set(v___f_113_, 1, v_toPure_109_);
lean_closure_set(v___f_113_, 2, v_condvar_104_);
lean_closure_set(v___f_113_, 3, v_mutex_105_);
lean_closure_set(v___f_113_, 4, v_inst_103_);
lean_closure_set(v___f_113_, 5, v_toBind_108_);
lean_closure_set(v___f_113_, 6, v___f_112_);
v___f_114_ = lean_alloc_closure((void*)(l_Std_Condvar_waitUntil___redArg___lam__3), 5, 4);
lean_closure_set(v___f_114_, 0, v_toBind_108_);
lean_closure_set(v___f_114_, 1, v_pred_106_);
lean_closure_set(v___f_114_, 2, v___f_113_);
lean_closure_set(v___f_114_, 3, v___f_111_);
v___f_115_ = lean_alloc_closure((void*)(l_Std_Condvar_waitUntil___redArg___lam__4), 3, 2);
lean_closure_set(v___f_115_, 0, v_toPure_109_);
lean_closure_set(v___f_115_, 1, v___x_110_);
v___x_116_ = l___private_Init_While_0__repeatM_erased___redArg(v_inst_102_, v___f_114_, v___x_110_);
v___x_117_ = lean_apply_4(v_toBind_108_, lean_box(0), lean_box(0), v___x_116_, v___f_115_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil(lean_object* v_m_118_, lean_object* v_inst_119_, lean_object* v_inst_120_, lean_object* v_condvar_121_, lean_object* v_mutex_122_, lean_object* v_pred_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_Std_Condvar_waitUntil___redArg(v_inst_119_, v_inst_120_, v_condvar_121_, v_mutex_122_, v_pred_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutMutexBaseMutex___lam__0(lean_object* v_self_125_){
_start:
{
lean_object* v_mutex_126_; 
v_mutex_126_ = lean_ctor_get(v_self_125_, 1);
lean_inc(v_mutex_126_);
return v_mutex_126_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutMutexBaseMutex___lam__0___boxed(lean_object* v_self_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Std_instCoeOutMutexBaseMutex___lam__0(v_self_127_);
lean_dec_ref(v_self_127_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutMutexBaseMutex(lean_object* v_00_u03b1_130_){
_start:
{
lean_object* v___f_131_; 
v___f_131_ = ((lean_object*)(l_Std_instCoeOutMutexBaseMutex___closed__0));
return v___f_131_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_new___redArg(lean_object* v_a_132_){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_134_ = lean_st_mk_ref(v_a_132_);
v___x_135_ = lean_io_basemutex_new();
v___x_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_134_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_new___redArg___boxed(lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Std_Mutex_new___redArg(v_a_137_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_new(lean_object* v_00_u03b1_140_, lean_object* v_a_141_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Std_Mutex_new___redArg(v_a_141_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_new___boxed(lean_object* v_00_u03b1_144_, lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Std_Mutex_new(v_00_u03b1_144_, v_a_145_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg___lam__0(lean_object* v_k_148_, lean_object* v_ref_149_, lean_object* v_____r_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lean_apply_1(v_k_148_, v_ref_149_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg___lam__1(lean_object* v_x_152_){
_start:
{
lean_object* v_fst_153_; 
v_fst_153_ = lean_ctor_get(v_x_152_, 0);
lean_inc(v_fst_153_);
return v_fst_153_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg___lam__1___boxed(lean_object* v_x_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Std_Mutex_atomically___redArg___lam__1(v_x_154_);
lean_dec_ref(v_x_154_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg___lam__2(lean_object* v___x_156_, lean_object* v_x_157_){
_start:
{
lean_inc(v___x_156_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg___lam__2___boxed(lean_object* v___x_158_, lean_object* v_x_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Std_Mutex_atomically___redArg___lam__2(v___x_158_, v_x_159_);
lean_dec(v_x_159_);
lean_dec(v___x_158_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg(lean_object* v_inst_162_, lean_object* v_inst_163_, lean_object* v_inst_164_, lean_object* v_mutex_165_, lean_object* v_k_166_){
_start:
{
lean_object* v_toApplicative_167_; lean_object* v_toFunctor_168_; lean_object* v_toBind_169_; lean_object* v_ref_170_; lean_object* v_mutex_171_; lean_object* v_map_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___f_175_; lean_object* v___f_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___f_180_; lean_object* v_y_181_; lean_object* v___x_182_; 
v_toApplicative_167_ = lean_ctor_get(v_inst_162_, 0);
v_toFunctor_168_ = lean_ctor_get(v_toApplicative_167_, 0);
lean_inc_ref(v_toFunctor_168_);
v_toBind_169_ = lean_ctor_get(v_inst_162_, 1);
lean_inc(v_toBind_169_);
lean_dec_ref(v_inst_162_);
v_ref_170_ = lean_ctor_get(v_mutex_165_, 0);
lean_inc(v_ref_170_);
v_mutex_171_ = lean_ctor_get(v_mutex_165_, 1);
lean_inc_n(v_mutex_171_, 2);
lean_dec_ref(v_mutex_165_);
v_map_172_ = lean_ctor_get(v_toFunctor_168_, 0);
lean_inc(v_map_172_);
lean_dec_ref(v_toFunctor_168_);
v___x_173_ = lean_alloc_closure((void*)(l_Std_BaseMutex_lock___boxed), 2, 1);
lean_closure_set(v___x_173_, 0, v_mutex_171_);
lean_inc(v_inst_163_);
v___x_174_ = lean_apply_2(v_inst_163_, lean_box(0), v___x_173_);
v___f_175_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___redArg___lam__0), 3, 2);
lean_closure_set(v___f_175_, 0, v_k_166_);
lean_closure_set(v___f_175_, 1, v_ref_170_);
v___f_176_ = ((lean_object*)(l_Std_Mutex_atomically___redArg___closed__0));
v___x_177_ = lean_apply_4(v_toBind_169_, lean_box(0), lean_box(0), v___x_174_, v___f_175_);
v___x_178_ = lean_alloc_closure((void*)(l_Std_BaseMutex_unlock___boxed), 2, 1);
lean_closure_set(v___x_178_, 0, v_mutex_171_);
v___x_179_ = lean_apply_2(v_inst_163_, lean_box(0), v___x_178_);
v___f_180_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_180_, 0, v___x_179_);
v_y_181_ = lean_apply_4(v_inst_164_, lean_box(0), lean_box(0), v___x_177_, v___f_180_);
v___x_182_ = lean_apply_4(v_map_172_, lean_box(0), lean_box(0), v___f_176_, v_y_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically(lean_object* v_m_183_, lean_object* v_00_u03b1_184_, lean_object* v_00_u03b2_185_, lean_object* v_inst_186_, lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_mutex_189_, lean_object* v_k_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Std_Mutex_atomically___redArg(v_inst_186_, v_inst_187_, v_inst_188_, v_mutex_189_, v_k_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__0(lean_object* v_x_192_){
_start:
{
lean_object* v_fst_193_; 
v_fst_193_ = lean_ctor_get(v_x_192_, 0);
lean_inc(v_fst_193_);
return v_fst_193_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__0___boxed(lean_object* v_x_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Std_Mutex_tryAtomically___redArg___lam__0(v_x_194_);
lean_dec_ref(v_x_194_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__1(lean_object* v_val_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_197_, 0, v_val_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__2(lean_object* v___x_198_, lean_object* v_x_199_){
_start:
{
lean_inc(v___x_198_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__2___boxed(lean_object* v___x_200_, lean_object* v_x_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Std_Mutex_tryAtomically___redArg___lam__2(v___x_200_, v_x_201_);
lean_dec(v_x_201_);
lean_dec(v___x_200_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__3(lean_object* v_toApplicative_203_, lean_object* v_k_204_, lean_object* v_ref_205_, lean_object* v___f_206_, lean_object* v_mutex_207_, lean_object* v_inst_208_, lean_object* v_inst_209_, lean_object* v___f_210_, uint8_t v_____do__lift_211_){
_start:
{
if (v_____do__lift_211_ == 0)
{
lean_object* v_toPure_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
lean_dec_ref(v___f_210_);
lean_dec(v_inst_209_);
lean_dec(v_inst_208_);
lean_dec(v_mutex_207_);
lean_dec_ref(v___f_206_);
lean_dec(v_ref_205_);
lean_dec(v_k_204_);
v_toPure_212_ = lean_ctor_get(v_toApplicative_203_, 1);
lean_inc(v_toPure_212_);
lean_dec_ref(v_toApplicative_203_);
v___x_213_ = lean_box(0);
v___x_214_ = lean_apply_2(v_toPure_212_, lean_box(0), v___x_213_);
return v___x_214_;
}
else
{
lean_object* v_toFunctor_215_; lean_object* v_map_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___f_221_; lean_object* v_y_222_; lean_object* v___x_223_; 
v_toFunctor_215_ = lean_ctor_get(v_toApplicative_203_, 0);
lean_inc_ref(v_toFunctor_215_);
lean_dec_ref(v_toApplicative_203_);
v_map_216_ = lean_ctor_get(v_toFunctor_215_, 0);
lean_inc_n(v_map_216_, 2);
lean_dec_ref(v_toFunctor_215_);
v___x_217_ = lean_apply_1(v_k_204_, v_ref_205_);
v___x_218_ = lean_apply_4(v_map_216_, lean_box(0), lean_box(0), v___f_206_, v___x_217_);
v___x_219_ = lean_alloc_closure((void*)(l_Std_BaseMutex_unlock___boxed), 2, 1);
lean_closure_set(v___x_219_, 0, v_mutex_207_);
v___x_220_ = lean_apply_2(v_inst_208_, lean_box(0), v___x_219_);
v___f_221_ = lean_alloc_closure((void*)(l_Std_Mutex_tryAtomically___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_221_, 0, v___x_220_);
v_y_222_ = lean_apply_4(v_inst_209_, lean_box(0), lean_box(0), v___x_218_, v___f_221_);
v___x_223_ = lean_apply_4(v_map_216_, lean_box(0), lean_box(0), v___f_210_, v_y_222_);
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__3___boxed(lean_object* v_toApplicative_224_, lean_object* v_k_225_, lean_object* v_ref_226_, lean_object* v___f_227_, lean_object* v_mutex_228_, lean_object* v_inst_229_, lean_object* v_inst_230_, lean_object* v___f_231_, lean_object* v_____do__lift_232_){
_start:
{
uint8_t v_____do__lift_140__boxed_233_; lean_object* v_res_234_; 
v_____do__lift_140__boxed_233_ = lean_unbox(v_____do__lift_232_);
v_res_234_ = l_Std_Mutex_tryAtomically___redArg___lam__3(v_toApplicative_224_, v_k_225_, v_ref_226_, v___f_227_, v_mutex_228_, v_inst_229_, v_inst_230_, v___f_231_, v_____do__lift_140__boxed_233_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg(lean_object* v_inst_237_, lean_object* v_inst_238_, lean_object* v_inst_239_, lean_object* v_mutex_240_, lean_object* v_k_241_){
_start:
{
lean_object* v_toApplicative_242_; lean_object* v_toBind_243_; lean_object* v_ref_244_; lean_object* v_mutex_245_; lean_object* v___f_246_; lean_object* v___f_247_; lean_object* v___f_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_toApplicative_242_ = lean_ctor_get(v_inst_237_, 0);
lean_inc_ref(v_toApplicative_242_);
v_toBind_243_ = lean_ctor_get(v_inst_237_, 1);
lean_inc(v_toBind_243_);
lean_dec_ref(v_inst_237_);
v_ref_244_ = lean_ctor_get(v_mutex_240_, 0);
lean_inc(v_ref_244_);
v_mutex_245_ = lean_ctor_get(v_mutex_240_, 1);
lean_inc_n(v_mutex_245_, 2);
lean_dec_ref(v_mutex_240_);
v___f_246_ = ((lean_object*)(l_Std_Mutex_tryAtomically___redArg___closed__0));
v___f_247_ = ((lean_object*)(l_Std_Mutex_tryAtomically___redArg___closed__1));
lean_inc(v_inst_238_);
v___f_248_ = lean_alloc_closure((void*)(l_Std_Mutex_tryAtomically___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_248_, 0, v_toApplicative_242_);
lean_closure_set(v___f_248_, 1, v_k_241_);
lean_closure_set(v___f_248_, 2, v_ref_244_);
lean_closure_set(v___f_248_, 3, v___f_247_);
lean_closure_set(v___f_248_, 4, v_mutex_245_);
lean_closure_set(v___f_248_, 5, v_inst_238_);
lean_closure_set(v___f_248_, 6, v_inst_239_);
lean_closure_set(v___f_248_, 7, v___f_246_);
v___x_249_ = lean_alloc_closure((void*)(l_Std_BaseMutex_tryLock___boxed), 2, 1);
lean_closure_set(v___x_249_, 0, v_mutex_245_);
v___x_250_ = lean_apply_2(v_inst_238_, lean_box(0), v___x_249_);
v___x_251_ = lean_apply_4(v_toBind_243_, lean_box(0), lean_box(0), v___x_250_, v___f_248_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically(lean_object* v_m_252_, lean_object* v_00_u03b1_253_, lean_object* v_00_u03b2_254_, lean_object* v_inst_255_, lean_object* v_inst_256_, lean_object* v_inst_257_, lean_object* v_mutex_258_, lean_object* v_k_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Std_Mutex_tryAtomically___redArg(v_inst_255_, v_inst_256_, v_inst_257_, v_mutex_258_, v_k_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomicallyOnce___redArg___lam__0(lean_object* v_k_261_, lean_object* v_____r_262_, lean_object* v___y_263_){
_start:
{
lean_object* v___x_264_; 
lean_inc(v___y_263_);
v___x_264_ = lean_apply_1(v_k_261_, v___y_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomicallyOnce___redArg___lam__0___boxed(lean_object* v_k_265_, lean_object* v_____r_266_, lean_object* v___y_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Std_Mutex_atomicallyOnce___redArg___lam__0(v_k_265_, v_____r_266_, v___y_267_);
lean_dec(v___y_267_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomicallyOnce___redArg(lean_object* v_inst_271_, lean_object* v_inst_272_, lean_object* v_inst_273_, lean_object* v_mutex_274_, lean_object* v_condvar_275_, lean_object* v_pred_276_, lean_object* v_k_277_){
_start:
{
lean_object* v___x_278_; lean_object* v_mutex_279_; lean_object* v___f_280_; lean_object* v___f_281_; lean_object* v___x_282_; lean_object* v___f_283_; lean_object* v_x_284_; lean_object* v___f_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
lean_inc_ref_n(v_inst_271_, 2);
v___x_278_ = l_StateRefT_x27_instMonad___redArg(v_inst_271_);
v_mutex_279_ = lean_ctor_get(v_mutex_274_, 1);
v___f_280_ = lean_alloc_closure((void*)(l_Std_Mutex_atomicallyOnce___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_280_, 0, v_k_277_);
v___f_281_ = ((lean_object*)(l_Std_Mutex_atomicallyOnce___redArg___closed__0));
v___x_282_ = ((lean_object*)(l_Std_Mutex_atomicallyOnce___redArg___closed__1));
lean_inc(v_inst_272_);
v___f_283_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_283_, 0, v_inst_272_);
lean_closure_set(v___f_283_, 1, v___x_282_);
v_x_284_ = lean_alloc_closure((void*)(l_liftM), 5, 3);
lean_closure_set(v_x_284_, 0, lean_box(0));
lean_closure_set(v_x_284_, 1, lean_box(0));
lean_closure_set(v_x_284_, 2, v___f_283_);
v___f_285_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_285_, 0, v___f_281_);
lean_closure_set(v___f_285_, 1, v_x_284_);
lean_inc(v_mutex_279_);
v___x_286_ = l_Std_Condvar_waitUntil___redArg(v___x_278_, v___f_285_, v_condvar_275_, v_mutex_279_, v_pred_276_);
v___x_287_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_287_, 0, lean_box(0));
lean_closure_set(v___x_287_, 1, lean_box(0));
lean_closure_set(v___x_287_, 2, v_inst_271_);
lean_closure_set(v___x_287_, 3, lean_box(0));
lean_closure_set(v___x_287_, 4, lean_box(0));
lean_closure_set(v___x_287_, 5, v___x_286_);
lean_closure_set(v___x_287_, 6, v___f_280_);
v___x_288_ = l_Std_Mutex_atomically___redArg(v_inst_271_, v_inst_272_, v_inst_273_, v_mutex_274_, v___x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomicallyOnce(lean_object* v_m_289_, lean_object* v_00_u03b1_290_, lean_object* v_00_u03b2_291_, lean_object* v_inst_292_, lean_object* v_inst_293_, lean_object* v_inst_294_, lean_object* v_mutex_295_, lean_object* v_condvar_296_, lean_object* v_pred_297_, lean_object* v_k_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Std_Mutex_atomicallyOnce___redArg(v_inst_292_, v_inst_293_, v_inst_294_, v_mutex_295_, v_condvar_296_, v_pred_297_, v_k_298_);
return v___x_299_;
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
