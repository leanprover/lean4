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
lean_object* l_instMonadLiftT___redArg___lam__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_instCoeOutMutexBaseMutex___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_instCoeOutMutexBaseMutex___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_instCoeOutMutexBaseMutex___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instCoeOutMutexBaseMutex___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instCoeOutMutexBaseMutex___redArg___closed__0 = (const lean_object*)&l_Std_instCoeOutMutexBaseMutex___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instCoeOutMutexBaseMutex___redArg();
LEAN_EXPORT lean_object* l_Std_instCoeOutMutexBaseMutex___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Mutex_tryAtomically___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Mutex_tryAtomically___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Mutex_tryAtomically___redArg___closed__0 = (const lean_object*)&l_Std_Mutex_tryAtomically___redArg___closed__0_value;
static const lean_closure_object l_Std_Mutex_tryAtomically___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Mutex_tryAtomically___redArg___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Mutex_tryAtomically___redArg___closed__1 = (const lean_object*)&l_Std_Mutex_tryAtomically___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomicallyOnce___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomicallyOnce___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Mutex_atomicallyOnce___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT void l_Std_BaseMutex_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3_;
v_res_3_ = lean_io_basemutex_new();
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l_Std_BaseMutex_new___boxed(lean_object* v_a_00___x40___internal___hyg_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lean_io_basemutex_new();
return v_res_5_;
}
}
LEAN_EXPORT void l_Std_BaseMutex_lock_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_6_ = stack[0].m_obj;
lean_object* v_res_8_;
v_res_8_ = lean_io_basemutex_lock(v_mutex_6_);
stack->m_obj
 = v_res_8_;
}
LEAN_EXPORT lean_object* l_Std_BaseMutex_lock___boxed(lean_object* v_mutex_9_, lean_object* v_a_00___x40___internal___hyg_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lean_io_basemutex_lock(v_mutex_9_);
lean_dec(v_mutex_9_);
return v_res_11_;
}
}
LEAN_EXPORT void l_Std_BaseMutex_tryLock_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_12_ = stack[0].m_obj;
uint8_t v_res_14_;
v_res_14_ = lean_io_basemutex_try_lock(v_mutex_12_);
stack->m_num = v_res_14_;
}
LEAN_EXPORT lean_object* l_Std_BaseMutex_tryLock___boxed(lean_object* v_mutex_15_, lean_object* v_a_00___x40___internal___hyg_16_){
_start:
{
uint8_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = lean_io_basemutex_try_lock(v_mutex_15_);
lean_dec(v_mutex_15_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT void l_Std_BaseMutex_unlock_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_19_ = stack[0].m_obj;
lean_object* v_res_21_;
v_res_21_ = lean_io_basemutex_unlock(v_mutex_19_);
stack->m_obj
 = v_res_21_;
}
LEAN_EXPORT lean_object* l_Std_BaseMutex_unlock___boxed(lean_object* v_mutex_22_, lean_object* v_a_00___x40___internal___hyg_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lean_io_basemutex_unlock(v_mutex_22_);
lean_dec(v_mutex_22_);
return v_res_24_;
}
}
static lean_object* _init_l___private_Std_Sync_Mutex_0__Std_CondvarImpl(void){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lean_box(0);
return v___x_25_;
}
}
LEAN_EXPORT void l_Std_Condvar_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_27_;
v_res_27_ = lean_io_condvar_new();
stack->m_obj
 = v_res_27_;
}
LEAN_EXPORT lean_object* l_Std_Condvar_new___boxed(lean_object* v_a_00___x40___internal___hyg_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = lean_io_condvar_new();
return v_res_29_;
}
}
LEAN_EXPORT void l_Std_Condvar_wait_0interp(lean_interpreter_value* stack)
{
lean_object* v_condvar_30_ = stack[0].m_obj;
lean_object* v_mutex_31_ = stack[1].m_obj;
lean_object* v_res_33_;
v_res_33_ = lean_io_condvar_wait(v_condvar_30_, v_mutex_31_);
stack->m_obj
 = v_res_33_;
}
LEAN_EXPORT lean_object* l_Std_Condvar_wait___boxed(lean_object* v_condvar_34_, lean_object* v_mutex_35_, lean_object* v_a_00___x40___internal___hyg_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lean_io_condvar_wait(v_condvar_34_, v_mutex_35_);
lean_dec(v_mutex_35_);
lean_dec(v_condvar_34_);
return v_res_37_;
}
}
LEAN_EXPORT void l_Std_Condvar_notifyOne_0interp(lean_interpreter_value* stack)
{
lean_object* v_condvar_38_ = stack[0].m_obj;
lean_object* v_res_40_;
v_res_40_ = lean_io_condvar_notify_one(v_condvar_38_);
stack->m_obj
 = v_res_40_;
}
LEAN_EXPORT lean_object* l_Std_Condvar_notifyOne___boxed(lean_object* v_condvar_41_, lean_object* v_a_00___x40___internal___hyg_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lean_io_condvar_notify_one(v_condvar_41_);
lean_dec(v_condvar_41_);
return v_res_43_;
}
}
LEAN_EXPORT void l_Std_Condvar_notifyAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_condvar_44_ = stack[0].m_obj;
lean_object* v_res_46_;
v_res_46_ = lean_io_condvar_notify_all(v_condvar_44_);
stack->m_obj
 = v_res_46_;
}
LEAN_EXPORT lean_object* l_Std_Condvar_notifyAll___boxed(lean_object* v_condvar_47_, lean_object* v_a_00___x40___internal___hyg_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = lean_io_condvar_notify_all(v_condvar_47_);
lean_dec(v_condvar_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__0(lean_object* v_toPure_50_, lean_object* v_____do__lift_51_){
_start:
{
if (lean_obj_tag(v_____do__lift_51_) == 0)
{
lean_object* v_a_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_60_; 
v_a_52_ = lean_ctor_get(v_____do__lift_51_, 0);
v_isSharedCheck_60_ = !lean_is_exclusive(v_____do__lift_51_);
if (v_isSharedCheck_60_ == 0)
{
v___x_54_ = v_____do__lift_51_;
v_isShared_55_ = v_isSharedCheck_60_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_a_52_);
lean_dec(v_____do__lift_51_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_60_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_57_; 
if (v_isShared_55_ == 0)
{
lean_ctor_set_tag(v___x_54_, 1);
v___x_57_ = v___x_54_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_a_52_);
v___x_57_ = v_reuseFailAlloc_59_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
lean_object* v___x_58_; 
v___x_58_ = lean_apply_2(v_toPure_50_, lean_box(0), v___x_57_);
return v___x_58_;
}
}
}
else
{
lean_object* v_a_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_69_; 
v_a_61_ = lean_ctor_get(v_____do__lift_51_, 0);
v_isSharedCheck_69_ = !lean_is_exclusive(v_____do__lift_51_);
if (v_isSharedCheck_69_ == 0)
{
v___x_63_ = v_____do__lift_51_;
v_isShared_64_ = v_isSharedCheck_69_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_a_61_);
lean_dec(v_____do__lift_51_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_69_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_66_; 
if (v_isShared_64_ == 0)
{
lean_ctor_set_tag(v___x_63_, 0);
v___x_66_ = v___x_63_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_a_61_);
v___x_66_ = v_reuseFailAlloc_68_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
lean_object* v___x_67_; 
v___x_67_ = lean_apply_2(v_toPure_50_, lean_box(0), v___x_66_);
return v___x_67_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__1(lean_object* v___x_70_, lean_object* v_toPure_71_, lean_object* v_r_72_){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_73_, 0, v___x_70_);
v___x_74_ = lean_apply_2(v_toPure_71_, lean_box(0), v___x_73_);
return v___x_74_;
}
}
lean_object* l_Std_Condvar_waitUntil___redArg___lam__2(lean_object* v_condvar_75_, lean_object* v_mutex_76_, lean_object* v_inst_77_, lean_object* v_toBind_78_, lean_object* v___f_79_, lean_object* v___x_80_, lean_object* v_toPure_81_, uint8_t v_____do__lift_82_){
_start:
{
if (v_____do__lift_82_ == 0)
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
lean_dec(v_toPure_81_);
v___x_83_ = lean_alloc_closure((void*)(l_Std_Condvar_wait___boxed), 3, 2);
lean_closure_set(v___x_83_, 0, v_condvar_75_);
lean_closure_set(v___x_83_, 1, v_mutex_76_);
v___x_84_ = lean_apply_2(v_inst_77_, lean_box(0), v___x_83_);
v___x_85_ = lean_apply_4(v_toBind_78_, lean_box(0), lean_box(0), v___x_84_, v___f_79_);
return v___x_85_;
}
else
{
lean_object* v___x_86_; lean_object* v___x_87_; 
lean_dec(v___f_79_);
lean_dec(v_toBind_78_);
lean_dec(v_inst_77_);
lean_dec(v_mutex_76_);
lean_dec(v_condvar_75_);
v___x_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_86_, 0, v___x_80_);
v___x_87_ = lean_apply_2(v_toPure_81_, lean_box(0), v___x_86_);
return v___x_87_;
}
}
}
LEAN_EXPORT void l_Std_Condvar_waitUntil___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_condvar_75_ = stack[0].m_obj;
lean_object* v_mutex_76_ = stack[1].m_obj;
lean_object* v_inst_77_ = stack[2].m_obj;
lean_object* v_toBind_78_ = stack[3].m_obj;
lean_object* v___f_79_ = stack[4].m_obj;
lean_object* v___x_80_ = stack[5].m_obj;
lean_object* v_toPure_81_ = stack[6].m_obj;
uint8_t v_____do__lift_82_ = stack[7].m_num;
lean_object* v_res_88_;
v_res_88_ = l_Std_Condvar_waitUntil___redArg___lam__2(v_condvar_75_, v_mutex_76_, v_inst_77_, v_toBind_78_, v___f_79_, v___x_80_, v_toPure_81_, v_____do__lift_82_);
stack->m_obj
 = v_res_88_;
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__2___boxed(lean_object* v_condvar_89_, lean_object* v_mutex_90_, lean_object* v_inst_91_, lean_object* v_toBind_92_, lean_object* v___f_93_, lean_object* v___x_94_, lean_object* v_toPure_95_, lean_object* v_____do__lift_96_){
_start:
{
uint8_t v_____do__lift_249__boxed_97_; lean_object* v_res_98_; 
v_____do__lift_249__boxed_97_ = lean_unbox(v_____do__lift_96_);
v_res_98_ = l_Std_Condvar_waitUntil___redArg___lam__2(v_condvar_89_, v_mutex_90_, v_inst_91_, v_toBind_92_, v___f_93_, v___x_94_, v_toPure_95_, v_____do__lift_249__boxed_97_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__3(lean_object* v_toBind_99_, lean_object* v_pred_100_, lean_object* v___f_101_, lean_object* v___f_102_, lean_object* v_b_103_){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
lean_inc(v_toBind_99_);
v___x_104_ = lean_apply_4(v_toBind_99_, lean_box(0), lean_box(0), v_pred_100_, v___f_101_);
v___x_105_ = lean_apply_4(v_toBind_99_, lean_box(0), lean_box(0), v___x_104_, v___f_102_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg___lam__4(lean_object* v_toPure_106_, lean_object* v___x_107_, lean_object* v_____s_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lean_apply_2(v_toPure_106_, lean_box(0), v___x_107_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___redArg(lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_condvar_112_, lean_object* v_mutex_113_, lean_object* v_pred_114_){
_start:
{
lean_object* v_toApplicative_115_; lean_object* v_toBind_116_; lean_object* v_toPure_117_; lean_object* v___x_118_; lean_object* v___f_119_; lean_object* v___f_120_; lean_object* v___f_121_; lean_object* v___f_122_; lean_object* v___f_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v_toApplicative_115_ = lean_ctor_get(v_inst_110_, 0);
v_toBind_116_ = lean_ctor_get(v_inst_110_, 1);
lean_inc_n(v_toBind_116_, 3);
v_toPure_117_ = lean_ctor_get(v_toApplicative_115_, 1);
v___x_118_ = lean_box(0);
lean_inc_n(v_toPure_117_, 4);
v___f_119_ = lean_alloc_closure((void*)(l_Std_Condvar_waitUntil___redArg___lam__0), 2, 1);
lean_closure_set(v___f_119_, 0, v_toPure_117_);
v___f_120_ = lean_alloc_closure((void*)(l_Std_Condvar_waitUntil___redArg___lam__1), 3, 2);
lean_closure_set(v___f_120_, 0, v___x_118_);
lean_closure_set(v___f_120_, 1, v_toPure_117_);
v___f_121_ = lean_alloc_closure((void*)(l_Std_Condvar_waitUntil___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_121_, 0, v_condvar_112_);
lean_closure_set(v___f_121_, 1, v_mutex_113_);
lean_closure_set(v___f_121_, 2, v_inst_111_);
lean_closure_set(v___f_121_, 3, v_toBind_116_);
lean_closure_set(v___f_121_, 4, v___f_120_);
lean_closure_set(v___f_121_, 5, v___x_118_);
lean_closure_set(v___f_121_, 6, v_toPure_117_);
v___f_122_ = lean_alloc_closure((void*)(l_Std_Condvar_waitUntil___redArg___lam__3), 5, 4);
lean_closure_set(v___f_122_, 0, v_toBind_116_);
lean_closure_set(v___f_122_, 1, v_pred_114_);
lean_closure_set(v___f_122_, 2, v___f_121_);
lean_closure_set(v___f_122_, 3, v___f_119_);
v___f_123_ = lean_alloc_closure((void*)(l_Std_Condvar_waitUntil___redArg___lam__4), 3, 2);
lean_closure_set(v___f_123_, 0, v_toPure_117_);
lean_closure_set(v___f_123_, 1, v___x_118_);
v___x_124_ = l___private_Init_While_0__repeatM_erased___redArg(v_inst_110_, v___f_122_, v___x_118_);
v___x_125_ = lean_apply_4(v_toBind_116_, lean_box(0), lean_box(0), v___x_124_, v___f_123_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil(lean_object* v_m_126_, lean_object* v_inst_127_, lean_object* v_inst_128_, lean_object* v_condvar_129_, lean_object* v_mutex_130_, lean_object* v_pred_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Std_Condvar_waitUntil___redArg(v_inst_127_, v_inst_128_, v_condvar_129_, v_mutex_130_, v_pred_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutMutexBaseMutex___redArg___lam__0(lean_object* v_self_133_){
_start:
{
lean_object* v_mutex_134_; 
v_mutex_134_ = lean_ctor_get(v_self_133_, 1);
lean_inc(v_mutex_134_);
return v_mutex_134_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutMutexBaseMutex___redArg___lam__0___boxed(lean_object* v_self_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Std_instCoeOutMutexBaseMutex___redArg___lam__0(v_self_135_);
lean_dec_ref(v_self_135_);
return v_res_136_;
}
}
lean_object* l_Std_instCoeOutMutexBaseMutex___redArg(){
_start:
{
lean_object* v___f_139_; 
v___f_139_ = ((lean_object*)(l_Std_instCoeOutMutexBaseMutex___redArg___closed__0));
return v___f_139_;
}
}
LEAN_EXPORT void l_Std_instCoeOutMutexBaseMutex___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_140_;
v_res_140_ = l_Std_instCoeOutMutexBaseMutex___redArg();
stack->m_obj
 = v_res_140_;
}
LEAN_EXPORT lean_object* l_Std_instCoeOutMutexBaseMutex___redArg___boxed(lean_object* v___dummy_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Std_instCoeOutMutexBaseMutex___redArg();
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutMutexBaseMutex(lean_object* v_00_u03b1_143_){
_start:
{
lean_object* v___f_144_; 
v___f_144_ = ((lean_object*)(l_Std_instCoeOutMutexBaseMutex___redArg___closed__0));
return v___f_144_;
}
}
lean_object* l_Std_Mutex_new___redArg(lean_object* v_a_145_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = lean_st_mk_ref(v_a_145_);
v___x_148_ = lean_io_basemutex_new();
v___x_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_147_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
return v___x_149_;
}
}
LEAN_EXPORT void l_Std_Mutex_new___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_145_ = stack[0].m_obj;
lean_object* v_res_150_;
v_res_150_ = l_Std_Mutex_new___redArg(v_a_145_);
stack->m_obj
 = v_res_150_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_new___redArg___boxed(lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Std_Mutex_new___redArg(v_a_151_);
return v_res_153_;
}
}
lean_object* l_Std_Mutex_new(lean_object* v_00_u03b1_154_, lean_object* v_a_155_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Std_Mutex_new___redArg(v_a_155_);
return v___x_157_;
}
}
LEAN_EXPORT void l_Std_Mutex_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_155_ = stack[1].m_obj;
lean_object* v_res_158_;
v_res_158_ = l_Std_Mutex_new(lean_box(0), v_a_155_);
stack->m_obj
 = v_res_158_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_new___boxed(lean_object* v_00_u03b1_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Std_Mutex_new(v_00_u03b1_159_, v_a_160_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg___lam__0(lean_object* v_k_163_, lean_object* v_ref_164_, lean_object* v_____r_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_apply_1(v_k_163_, v_ref_164_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg___lam__1(lean_object* v_x_167_){
_start:
{
lean_object* v_fst_168_; 
v_fst_168_ = lean_ctor_get(v_x_167_, 0);
lean_inc(v_fst_168_);
return v_fst_168_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg___lam__1___boxed(lean_object* v_x_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Std_Mutex_atomically___redArg___lam__1(v_x_169_);
lean_dec_ref(v_x_169_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg___lam__2(lean_object* v___x_171_, lean_object* v_x_172_){
_start:
{
lean_inc(v___x_171_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg___lam__2___boxed(lean_object* v___x_173_, lean_object* v_x_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Std_Mutex_atomically___redArg___lam__2(v___x_173_, v_x_174_);
lean_dec(v_x_174_);
lean_dec(v___x_173_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___redArg(lean_object* v_inst_177_, lean_object* v_inst_178_, lean_object* v_inst_179_, lean_object* v_mutex_180_, lean_object* v_k_181_){
_start:
{
lean_object* v_toApplicative_182_; lean_object* v_toFunctor_183_; lean_object* v_toBind_184_; lean_object* v_ref_185_; lean_object* v_mutex_186_; lean_object* v_map_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___f_190_; lean_object* v___f_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___f_195_; lean_object* v_y_196_; lean_object* v___x_197_; 
v_toApplicative_182_ = lean_ctor_get(v_inst_177_, 0);
v_toFunctor_183_ = lean_ctor_get(v_toApplicative_182_, 0);
lean_inc_ref(v_toFunctor_183_);
v_toBind_184_ = lean_ctor_get(v_inst_177_, 1);
lean_inc(v_toBind_184_);
lean_dec_ref(v_inst_177_);
v_ref_185_ = lean_ctor_get(v_mutex_180_, 0);
lean_inc(v_ref_185_);
v_mutex_186_ = lean_ctor_get(v_mutex_180_, 1);
lean_inc_n(v_mutex_186_, 2);
lean_dec_ref(v_mutex_180_);
v_map_187_ = lean_ctor_get(v_toFunctor_183_, 0);
lean_inc(v_map_187_);
lean_dec_ref(v_toFunctor_183_);
v___x_188_ = lean_alloc_closure((void*)(l_Std_BaseMutex_lock___boxed), 2, 1);
lean_closure_set(v___x_188_, 0, v_mutex_186_);
lean_inc(v_inst_178_);
v___x_189_ = lean_apply_2(v_inst_178_, lean_box(0), v___x_188_);
v___f_190_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___redArg___lam__0), 3, 2);
lean_closure_set(v___f_190_, 0, v_k_181_);
lean_closure_set(v___f_190_, 1, v_ref_185_);
v___f_191_ = ((lean_object*)(l_Std_Mutex_atomically___redArg___closed__0));
v___x_192_ = lean_apply_4(v_toBind_184_, lean_box(0), lean_box(0), v___x_189_, v___f_190_);
v___x_193_ = lean_alloc_closure((void*)(l_Std_BaseMutex_unlock___boxed), 2, 1);
lean_closure_set(v___x_193_, 0, v_mutex_186_);
v___x_194_ = lean_apply_2(v_inst_178_, lean_box(0), v___x_193_);
v___f_195_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_195_, 0, v___x_194_);
v_y_196_ = lean_apply_4(v_inst_179_, lean_box(0), lean_box(0), v___x_192_, v___f_195_);
v___x_197_ = lean_apply_4(v_map_187_, lean_box(0), lean_box(0), v___f_191_, v_y_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically(lean_object* v_m_198_, lean_object* v_00_u03b1_199_, lean_object* v_00_u03b2_200_, lean_object* v_inst_201_, lean_object* v_inst_202_, lean_object* v_inst_203_, lean_object* v_mutex_204_, lean_object* v_k_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Std_Mutex_atomically___redArg(v_inst_201_, v_inst_202_, v_inst_203_, v_mutex_204_, v_k_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__0(lean_object* v_x_207_){
_start:
{
lean_object* v_fst_208_; 
v_fst_208_ = lean_ctor_get(v_x_207_, 0);
lean_inc(v_fst_208_);
return v_fst_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__0___boxed(lean_object* v_x_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Std_Mutex_tryAtomically___redArg___lam__0(v_x_209_);
lean_dec_ref(v_x_209_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__1(lean_object* v_val_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_212_, 0, v_val_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__2(lean_object* v___x_213_, lean_object* v_x_214_){
_start:
{
lean_inc(v___x_213_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__2___boxed(lean_object* v___x_215_, lean_object* v_x_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Std_Mutex_tryAtomically___redArg___lam__2(v___x_215_, v_x_216_);
lean_dec(v_x_216_);
lean_dec(v___x_215_);
return v_res_217_;
}
}
lean_object* l_Std_Mutex_tryAtomically___redArg___lam__3(lean_object* v_toPure_218_, lean_object* v_toFunctor_219_, lean_object* v_k_220_, lean_object* v_ref_221_, lean_object* v___f_222_, lean_object* v_mutex_223_, lean_object* v_inst_224_, lean_object* v_inst_225_, lean_object* v___f_226_, uint8_t v_____do__lift_227_){
_start:
{
if (v_____do__lift_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
lean_dec_ref(v___f_226_);
lean_dec(v_inst_225_);
lean_dec(v_inst_224_);
lean_dec(v_mutex_223_);
lean_dec_ref(v___f_222_);
lean_dec(v_ref_221_);
lean_dec(v_k_220_);
lean_dec_ref(v_toFunctor_219_);
v___x_228_ = lean_box(0);
v___x_229_ = lean_apply_2(v_toPure_218_, lean_box(0), v___x_228_);
return v___x_229_;
}
else
{
lean_object* v_map_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___f_235_; lean_object* v_y_236_; lean_object* v___x_237_; 
lean_dec(v_toPure_218_);
v_map_230_ = lean_ctor_get(v_toFunctor_219_, 0);
lean_inc_n(v_map_230_, 2);
lean_dec_ref(v_toFunctor_219_);
v___x_231_ = lean_apply_1(v_k_220_, v_ref_221_);
v___x_232_ = lean_apply_4(v_map_230_, lean_box(0), lean_box(0), v___f_222_, v___x_231_);
v___x_233_ = lean_alloc_closure((void*)(l_Std_BaseMutex_unlock___boxed), 2, 1);
lean_closure_set(v___x_233_, 0, v_mutex_223_);
v___x_234_ = lean_apply_2(v_inst_224_, lean_box(0), v___x_233_);
v___f_235_ = lean_alloc_closure((void*)(l_Std_Mutex_tryAtomically___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_235_, 0, v___x_234_);
v_y_236_ = lean_apply_4(v_inst_225_, lean_box(0), lean_box(0), v___x_232_, v___f_235_);
v___x_237_ = lean_apply_4(v_map_230_, lean_box(0), lean_box(0), v___f_226_, v_y_236_);
return v___x_237_;
}
}
}
LEAN_EXPORT void l_Std_Mutex_tryAtomically___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_218_ = stack[0].m_obj;
lean_object* v_toFunctor_219_ = stack[1].m_obj;
lean_object* v_k_220_ = stack[2].m_obj;
lean_object* v_ref_221_ = stack[3].m_obj;
lean_object* v___f_222_ = stack[4].m_obj;
lean_object* v_mutex_223_ = stack[5].m_obj;
lean_object* v_inst_224_ = stack[6].m_obj;
lean_object* v_inst_225_ = stack[7].m_obj;
lean_object* v___f_226_ = stack[8].m_obj;
uint8_t v_____do__lift_227_ = stack[9].m_num;
lean_object* v_res_238_;
v_res_238_ = l_Std_Mutex_tryAtomically___redArg___lam__3(v_toPure_218_, v_toFunctor_219_, v_k_220_, v_ref_221_, v___f_222_, v_mutex_223_, v_inst_224_, v_inst_225_, v___f_226_, v_____do__lift_227_);
stack->m_obj
 = v_res_238_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg___lam__3___boxed(lean_object* v_toPure_239_, lean_object* v_toFunctor_240_, lean_object* v_k_241_, lean_object* v_ref_242_, lean_object* v___f_243_, lean_object* v_mutex_244_, lean_object* v_inst_245_, lean_object* v_inst_246_, lean_object* v___f_247_, lean_object* v_____do__lift_248_){
_start:
{
uint8_t v_____do__lift_92__boxed_249_; lean_object* v_res_250_; 
v_____do__lift_92__boxed_249_ = lean_unbox(v_____do__lift_248_);
v_res_250_ = l_Std_Mutex_tryAtomically___redArg___lam__3(v_toPure_239_, v_toFunctor_240_, v_k_241_, v_ref_242_, v___f_243_, v_mutex_244_, v_inst_245_, v_inst_246_, v___f_247_, v_____do__lift_92__boxed_249_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically___redArg(lean_object* v_inst_253_, lean_object* v_inst_254_, lean_object* v_inst_255_, lean_object* v_mutex_256_, lean_object* v_k_257_){
_start:
{
lean_object* v_toApplicative_258_; lean_object* v_toBind_259_; lean_object* v_ref_260_; lean_object* v_mutex_261_; lean_object* v_toFunctor_262_; lean_object* v_toPure_263_; lean_object* v___f_264_; lean_object* v___f_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___f_268_; lean_object* v___x_269_; 
v_toApplicative_258_ = lean_ctor_get(v_inst_253_, 0);
lean_inc_ref(v_toApplicative_258_);
v_toBind_259_ = lean_ctor_get(v_inst_253_, 1);
lean_inc(v_toBind_259_);
lean_dec_ref(v_inst_253_);
v_ref_260_ = lean_ctor_get(v_mutex_256_, 0);
lean_inc(v_ref_260_);
v_mutex_261_ = lean_ctor_get(v_mutex_256_, 1);
lean_inc_n(v_mutex_261_, 2);
lean_dec_ref(v_mutex_256_);
v_toFunctor_262_ = lean_ctor_get(v_toApplicative_258_, 0);
lean_inc_ref(v_toFunctor_262_);
v_toPure_263_ = lean_ctor_get(v_toApplicative_258_, 1);
lean_inc(v_toPure_263_);
lean_dec_ref(v_toApplicative_258_);
v___f_264_ = ((lean_object*)(l_Std_Mutex_tryAtomically___redArg___closed__0));
v___f_265_ = ((lean_object*)(l_Std_Mutex_tryAtomically___redArg___closed__1));
v___x_266_ = lean_alloc_closure((void*)(l_Std_BaseMutex_tryLock___boxed), 2, 1);
lean_closure_set(v___x_266_, 0, v_mutex_261_);
lean_inc(v_inst_254_);
v___x_267_ = lean_apply_2(v_inst_254_, lean_box(0), v___x_266_);
v___f_268_ = lean_alloc_closure((void*)(l_Std_Mutex_tryAtomically___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_268_, 0, v_toPure_263_);
lean_closure_set(v___f_268_, 1, v_toFunctor_262_);
lean_closure_set(v___f_268_, 2, v_k_257_);
lean_closure_set(v___f_268_, 3, v_ref_260_);
lean_closure_set(v___f_268_, 4, v___f_265_);
lean_closure_set(v___f_268_, 5, v_mutex_261_);
lean_closure_set(v___f_268_, 6, v_inst_254_);
lean_closure_set(v___f_268_, 7, v_inst_255_);
lean_closure_set(v___f_268_, 8, v___f_264_);
v___x_269_ = lean_apply_4(v_toBind_259_, lean_box(0), lean_box(0), v___x_267_, v___f_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_tryAtomically(lean_object* v_m_270_, lean_object* v_00_u03b1_271_, lean_object* v_00_u03b2_272_, lean_object* v_inst_273_, lean_object* v_inst_274_, lean_object* v_inst_275_, lean_object* v_mutex_276_, lean_object* v_k_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Std_Mutex_tryAtomically___redArg(v_inst_273_, v_inst_274_, v_inst_275_, v_mutex_276_, v_k_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomicallyOnce___redArg___lam__0(lean_object* v_k_279_, lean_object* v_____r_280_, lean_object* v___y_281_){
_start:
{
lean_object* v___x_282_; 
lean_inc(v___y_281_);
v___x_282_ = lean_apply_1(v_k_279_, v___y_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomicallyOnce___redArg___lam__0___boxed(lean_object* v_k_283_, lean_object* v_____r_284_, lean_object* v___y_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Std_Mutex_atomicallyOnce___redArg___lam__0(v_k_283_, v_____r_284_, v___y_285_);
lean_dec(v___y_285_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomicallyOnce___redArg(lean_object* v_inst_289_, lean_object* v_inst_290_, lean_object* v_inst_291_, lean_object* v_mutex_292_, lean_object* v_condvar_293_, lean_object* v_pred_294_, lean_object* v_k_295_){
_start:
{
lean_object* v___x_296_; lean_object* v_mutex_297_; lean_object* v___f_298_; lean_object* v___f_299_; lean_object* v___x_300_; lean_object* v___f_301_; lean_object* v_x_302_; lean_object* v___f_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
lean_inc_ref_n(v_inst_289_, 2);
v___x_296_ = l_StateRefT_x27_instMonad___redArg(v_inst_289_);
v_mutex_297_ = lean_ctor_get(v_mutex_292_, 1);
v___f_298_ = lean_alloc_closure((void*)(l_Std_Mutex_atomicallyOnce___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_298_, 0, v_k_295_);
v___f_299_ = ((lean_object*)(l_Std_Mutex_atomicallyOnce___redArg___closed__0));
v___x_300_ = ((lean_object*)(l_Std_Mutex_atomicallyOnce___redArg___closed__1));
lean_inc(v_inst_290_);
v___f_301_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_301_, 0, v_inst_290_);
lean_closure_set(v___f_301_, 1, v___x_300_);
v_x_302_ = lean_alloc_closure((void*)(l_liftM), 5, 3);
lean_closure_set(v_x_302_, 0, lean_box(0));
lean_closure_set(v_x_302_, 1, lean_box(0));
lean_closure_set(v_x_302_, 2, v___f_301_);
v___f_303_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_303_, 0, v___f_299_);
lean_closure_set(v___f_303_, 1, v_x_302_);
lean_inc(v_mutex_297_);
v___x_304_ = l_Std_Condvar_waitUntil___redArg(v___x_296_, v___f_303_, v_condvar_293_, v_mutex_297_, v_pred_294_);
v___x_305_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_305_, 0, lean_box(0));
lean_closure_set(v___x_305_, 1, lean_box(0));
lean_closure_set(v___x_305_, 2, v_inst_289_);
lean_closure_set(v___x_305_, 3, lean_box(0));
lean_closure_set(v___x_305_, 4, lean_box(0));
lean_closure_set(v___x_305_, 5, v___x_304_);
lean_closure_set(v___x_305_, 6, v___f_298_);
v___x_306_ = l_Std_Mutex_atomically___redArg(v_inst_289_, v_inst_290_, v_inst_291_, v_mutex_292_, v___x_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomicallyOnce(lean_object* v_m_307_, lean_object* v_00_u03b1_308_, lean_object* v_00_u03b2_309_, lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_inst_312_, lean_object* v_mutex_313_, lean_object* v_condvar_314_, lean_object* v_pred_315_, lean_object* v_k_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Std_Mutex_atomicallyOnce___redArg(v_inst_310_, v_inst_311_, v_inst_312_, v_mutex_313_, v_condvar_314_, v_pred_315_, v_k_316_);
return v___x_317_;
}
}
lean_object* runtime_initialize_Std_Sync_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sync_Mutex(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
