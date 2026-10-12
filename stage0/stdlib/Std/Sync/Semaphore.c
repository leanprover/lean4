// Lean compiler output
// Module: Std.Sync.Semaphore
// Imports: public import Init.Data.Queue public import Init.System.Promise public import Std.Sync.Mutex
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
lean_object* lean_st_ref_get(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_io_promise_new();
lean_object* l_Std_Queue_enqueue___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_io_basemutex_lock(lean_object*);
lean_object* lean_io_basemutex_unlock(lean_object*);
lean_object* l_Std_Queue_dequeue_x3f___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_Queue_empty___redArg();
lean_object* l_Std_Mutex_new___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Semaphore_new___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Semaphore_new___closed__0;
LEAN_EXPORT lean_object* l_Std_Semaphore_new(lean_object*);
LEAN_EXPORT lean_object* l_Std_Semaphore_new___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Semaphore_acquire___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Semaphore_acquire___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Semaphore_acquire___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Semaphore_acquire___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Semaphore_acquire___closed__0 = (const lean_object*)&l_Std_Semaphore_acquire___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Semaphore_acquire(lean_object*);
LEAN_EXPORT lean_object* l_Std_Semaphore_acquire___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Semaphore_tryAcquire___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Semaphore_tryAcquire___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Semaphore_tryAcquire___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Semaphore_tryAcquire___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Semaphore_tryAcquire___closed__0 = (const lean_object*)&l_Std_Semaphore_tryAcquire___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Semaphore_tryAcquire(lean_object*);
LEAN_EXPORT lean_object* l_Std_Semaphore_tryAcquire___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Semaphore_release___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Semaphore_release___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Semaphore_release___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Semaphore_release___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Semaphore_release___closed__0 = (const lean_object*)&l_Std_Semaphore_release___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Semaphore_release(lean_object*);
LEAN_EXPORT lean_object* l_Std_Semaphore_release___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Semaphore_availablePermits___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Semaphore_availablePermits___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Semaphore_availablePermits___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Semaphore_availablePermits___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Semaphore_availablePermits___closed__0 = (const lean_object*)&l_Std_Semaphore_availablePermits___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Semaphore_availablePermits(lean_object*);
LEAN_EXPORT lean_object* l_Std_Semaphore_availablePermits___boxed(lean_object*, lean_object*);
lean_object* l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise___redArg(lean_object* v_a_1_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_io_promise_new();
v___x_4_ = lean_io_promise_resolve(v_a_1_, v___x_3_);
return v___x_3_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
lean_object* v_res_5_;
v_res_5_ = l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise___redArg(v_a_1_);
stack->m_obj
 = v_res_5_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise___redArg___boxed(lean_object* v_a_6_, lean_object* v_a_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise___redArg(v_a_6_);
return v_res_8_;
}
}
lean_object* l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise(lean_object* v_00_u03b1_9_, lean_object* v_inst_10_, lean_object* v_a_11_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise___redArg(v_a_11_);
return v___x_13_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_11_ = stack[2].m_obj;
lean_object* v_res_14_;
v_res_14_ = l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise(lean_box(0), lean_box(0), v_a_11_);
stack->m_obj
 = v_res_14_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise___boxed(lean_object* v_00_u03b1_15_, lean_object* v_inst_16_, lean_object* v_a_17_, lean_object* v_a_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise(v_00_u03b1_15_, v_inst_16_, v_a_17_);
return v_res_19_;
}
}
static lean_object* _init_l_Std_Semaphore_new___closed__0(void){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Std_Queue_empty___redArg();
return v___x_20_;
}
}
lean_object* l_Std_Semaphore_new(lean_object* v_permits_21_){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_23_ = lean_obj_once(&l_Std_Semaphore_new___closed__0, &l_Std_Semaphore_new___closed__0_once, _init_l_Std_Semaphore_new___closed__0);
v___x_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_24_, 0, v_permits_21_);
lean_ctor_set(v___x_24_, 1, v___x_23_);
v___x_25_ = l_Std_Mutex_new___redArg(v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT void l_Std_Semaphore_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_permits_21_ = stack[0].m_obj;
lean_object* v_res_26_;
v_res_26_ = l_Std_Semaphore_new(v_permits_21_);
stack->m_obj
 = v_res_26_;
}
LEAN_EXPORT lean_object* l_Std_Semaphore_new___boxed(lean_object* v_permits_27_, lean_object* v_a_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Std_Semaphore_new(v_permits_27_);
return v_res_29_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___redArg(lean_object* v_mutex_30_, lean_object* v_k_31_){
_start:
{
lean_object* v_ref_33_; lean_object* v_mutex_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v_ref_33_ = lean_ctor_get(v_mutex_30_, 0);
lean_inc(v_ref_33_);
v_mutex_34_ = lean_ctor_get(v_mutex_30_, 1);
lean_inc(v_mutex_34_);
lean_dec_ref(v_mutex_30_);
v___x_35_ = lean_io_basemutex_lock(v_mutex_34_);
v___x_36_ = lean_apply_2(v_k_31_, v_ref_33_, lean_box(0));
v___x_37_ = lean_io_basemutex_unlock(v_mutex_34_);
lean_dec(v_mutex_34_);
return v___x_36_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_30_ = stack[0].m_obj;
lean_object* v_k_31_ = stack[1].m_obj;
lean_object* v_res_38_;
v_res_38_ = l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___redArg(v_mutex_30_, v_k_31_);
stack->m_obj
 = v_res_38_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___redArg___boxed(lean_object* v_mutex_39_, lean_object* v_k_40_, lean_object* v___y_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___redArg(v_mutex_39_, v_k_40_);
return v_res_42_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0(lean_object* v_00_u03b1_43_, lean_object* v_00_u03b2_44_, lean_object* v_mutex_45_, lean_object* v_k_46_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___redArg(v_mutex_45_, v_k_46_);
return v___x_48_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_45_ = stack[2].m_obj;
lean_object* v_k_46_ = stack[3].m_obj;
lean_object* v_res_49_;
v_res_49_ = l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0(lean_box(0), lean_box(0), v_mutex_45_, v_k_46_);
stack->m_obj
 = v_res_49_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___boxed(lean_object* v_00_u03b1_50_, lean_object* v_00_u03b2_51_, lean_object* v_mutex_52_, lean_object* v_k_53_, lean_object* v___y_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0(v_00_u03b1_50_, v_00_u03b2_51_, v_mutex_52_, v_k_53_);
return v_res_55_;
}
}
lean_object* l_Std_Semaphore_acquire___lam__0(lean_object* v___y_56_){
_start:
{
lean_object* v___x_58_; lean_object* v_permits_59_; lean_object* v_waiters_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_80_; 
v___x_58_ = lean_st_ref_get(v___y_56_);
v_permits_59_ = lean_ctor_get(v___x_58_, 0);
v_waiters_60_ = lean_ctor_get(v___x_58_, 1);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_80_ == 0)
{
v___x_62_ = v___x_58_;
v_isShared_63_ = v_isSharedCheck_80_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_waiters_60_);
lean_inc(v_permits_59_);
lean_dec(v___x_58_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_80_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_64_; uint8_t v___x_65_; 
v___x_64_ = lean_unsigned_to_nat(0u);
v___x_65_ = lean_nat_dec_lt(v___x_64_, v_permits_59_);
if (v___x_65_ == 0)
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_69_; 
v___x_66_ = lean_io_promise_new();
lean_inc(v___x_66_);
v___x_67_ = l_Std_Queue_enqueue___redArg(v___x_66_, v_waiters_60_);
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 1, v___x_67_);
v___x_69_ = v___x_62_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_permits_59_);
lean_ctor_set(v_reuseFailAlloc_71_, 1, v___x_67_);
v___x_69_ = v_reuseFailAlloc_71_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
lean_object* v___x_70_; 
v___x_70_ = lean_st_ref_swap(v___y_56_, v___x_69_);
lean_dec(v___x_70_);
return v___x_66_;
}
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_75_; 
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_nat_sub(v_permits_59_, v___x_72_);
lean_dec(v_permits_59_);
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 0, v___x_73_);
v___x_75_ = v___x_62_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_73_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v_waiters_60_);
v___x_75_ = v_reuseFailAlloc_79_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = lean_st_ref_swap(v___y_56_, v___x_75_);
lean_dec(v___x_76_);
v___x_77_ = lean_box(0);
v___x_78_ = l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise___redArg(v___x_77_);
return v___x_78_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Semaphore_acquire___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_56_ = stack[0].m_obj;
lean_object* v_res_81_;
v_res_81_ = l_Std_Semaphore_acquire___lam__0(v___y_56_);
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l_Std_Semaphore_acquire___lam__0___boxed(lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Std_Semaphore_acquire___lam__0(v___y_82_);
lean_dec(v___y_82_);
return v_res_84_;
}
}
lean_object* l_Std_Semaphore_acquire(lean_object* v_sem_86_){
_start:
{
lean_object* v___f_88_; lean_object* v___x_89_; 
v___f_88_ = ((lean_object*)(l_Std_Semaphore_acquire___closed__0));
v___x_89_ = l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___redArg(v_sem_86_, v___f_88_);
return v___x_89_;
}
}
LEAN_EXPORT void l_Std_Semaphore_acquire_0interp(lean_interpreter_value* stack)
{
lean_object* v_sem_86_ = stack[0].m_obj;
lean_object* v_res_90_;
v_res_90_ = l_Std_Semaphore_acquire(v_sem_86_);
stack->m_obj
 = v_res_90_;
}
LEAN_EXPORT lean_object* l_Std_Semaphore_acquire___boxed(lean_object* v_sem_91_, lean_object* v_a_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Std_Semaphore_acquire(v_sem_91_);
return v_res_93_;
}
}
uint8_t l_Std_Semaphore_tryAcquire___lam__0(lean_object* v___y_94_){
_start:
{
lean_object* v___x_96_; lean_object* v_permits_97_; lean_object* v_waiters_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_110_; 
v___x_96_ = lean_st_ref_get(v___y_94_);
v_permits_97_ = lean_ctor_get(v___x_96_, 0);
v_waiters_98_ = lean_ctor_get(v___x_96_, 1);
v_isSharedCheck_110_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_110_ == 0)
{
v___x_100_ = v___x_96_;
v_isShared_101_ = v_isSharedCheck_110_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_waiters_98_);
lean_inc(v_permits_97_);
lean_dec(v___x_96_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_110_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = lean_unsigned_to_nat(0u);
v___x_103_ = lean_nat_dec_lt(v___x_102_, v_permits_97_);
if (v___x_103_ == 0)
{
lean_del_object(v___x_100_);
lean_dec_ref(v_waiters_98_);
lean_dec(v_permits_97_);
return v___x_103_;
}
else
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_107_; 
v___x_104_ = lean_unsigned_to_nat(1u);
v___x_105_ = lean_nat_sub(v_permits_97_, v___x_104_);
lean_dec(v_permits_97_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 0, v___x_105_);
v___x_107_ = v___x_100_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v___x_105_);
lean_ctor_set(v_reuseFailAlloc_109_, 1, v_waiters_98_);
v___x_107_ = v_reuseFailAlloc_109_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
lean_object* v___x_108_; 
v___x_108_ = lean_st_ref_swap(v___y_94_, v___x_107_);
lean_dec(v___x_108_);
return v___x_103_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Semaphore_tryAcquire___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_94_ = stack[0].m_obj;
uint8_t v_res_111_;
v_res_111_ = l_Std_Semaphore_tryAcquire___lam__0(v___y_94_);
stack->m_num = v_res_111_;
}
LEAN_EXPORT lean_object* l_Std_Semaphore_tryAcquire___lam__0___boxed(lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
uint8_t v_res_114_; lean_object* v_r_115_; 
v_res_114_ = l_Std_Semaphore_tryAcquire___lam__0(v___y_112_);
lean_dec(v___y_112_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
uint8_t l_Std_Semaphore_tryAcquire(lean_object* v_sem_117_){
_start:
{
lean_object* v___f_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___f_119_ = ((lean_object*)(l_Std_Semaphore_tryAcquire___closed__0));
v___x_120_ = l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___redArg(v_sem_117_, v___f_119_);
v___x_121_ = lean_unbox(v___x_120_);
lean_dec(v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT void l_Std_Semaphore_tryAcquire_0interp(lean_interpreter_value* stack)
{
lean_object* v_sem_117_ = stack[0].m_obj;
uint8_t v_res_122_;
v_res_122_ = l_Std_Semaphore_tryAcquire(v_sem_117_);
stack->m_num = v_res_122_;
}
LEAN_EXPORT lean_object* l_Std_Semaphore_tryAcquire___boxed(lean_object* v_sem_123_, lean_object* v_a_124_){
_start:
{
uint8_t v_res_125_; lean_object* v_r_126_; 
v_res_125_ = l_Std_Semaphore_tryAcquire(v_sem_123_);
v_r_126_ = lean_box(v_res_125_);
return v_r_126_;
}
}
lean_object* l_Std_Semaphore_release___lam__0(lean_object* v___y_127_){
_start:
{
lean_object* v___x_129_; lean_object* v_permits_130_; lean_object* v_waiters_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_157_; 
v___x_129_ = lean_st_ref_get(v___y_127_);
v_permits_130_ = lean_ctor_get(v___x_129_, 0);
v_waiters_131_ = lean_ctor_get(v___x_129_, 1);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_157_ == 0)
{
v___x_133_ = v___x_129_;
v_isShared_134_ = v_isSharedCheck_157_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_waiters_131_);
lean_inc(v_permits_130_);
lean_dec(v___x_129_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_157_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; 
lean_inc_ref(v_waiters_131_);
v___x_135_ = l_Std_Queue_dequeue_x3f___redArg(v_waiters_131_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_139_; 
v___x_136_ = lean_unsigned_to_nat(1u);
v___x_137_ = lean_nat_add(v_permits_130_, v___x_136_);
lean_dec(v_permits_130_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 0, v___x_137_);
v___x_139_ = v___x_133_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_137_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v_waiters_131_);
v___x_139_ = v_reuseFailAlloc_142_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_st_ref_swap(v___y_127_, v___x_139_);
lean_dec(v___x_140_);
v___x_141_ = lean_box(0);
return v___x_141_;
}
}
else
{
lean_object* v_val_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_156_; 
lean_dec_ref(v_waiters_131_);
v_val_143_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_156_ == 0)
{
v___x_145_ = v___x_135_;
v_isShared_146_ = v_isSharedCheck_156_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_val_143_);
lean_dec(v___x_135_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_156_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v_fst_147_; lean_object* v_snd_148_; lean_object* v___x_150_; 
v_fst_147_ = lean_ctor_get(v_val_143_, 0);
lean_inc(v_fst_147_);
v_snd_148_ = lean_ctor_get(v_val_143_, 1);
lean_inc(v_snd_148_);
lean_dec(v_val_143_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v_snd_148_);
v___x_150_ = v___x_133_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_permits_130_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_snd_148_);
v___x_150_ = v_reuseFailAlloc_155_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_151_ = lean_st_ref_swap(v___y_127_, v___x_150_);
lean_dec(v___x_151_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 0, v_fst_147_);
v___x_153_ = v___x_145_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_fst_147_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Semaphore_release___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_127_ = stack[0].m_obj;
lean_object* v_res_158_;
v_res_158_ = l_Std_Semaphore_release___lam__0(v___y_127_);
stack->m_obj
 = v_res_158_;
}
LEAN_EXPORT lean_object* l_Std_Semaphore_release___lam__0___boxed(lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Std_Semaphore_release___lam__0(v___y_159_);
lean_dec(v___y_159_);
return v_res_161_;
}
}
lean_object* l_Std_Semaphore_release(lean_object* v_sem_163_){
_start:
{
lean_object* v___f_165_; lean_object* v___x_166_; 
v___f_165_ = ((lean_object*)(l_Std_Semaphore_release___closed__0));
v___x_166_ = l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___redArg(v_sem_163_, v___f_165_);
if (lean_obj_tag(v___x_166_) == 1)
{
lean_object* v_val_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v_val_167_ = lean_ctor_get(v___x_166_, 0);
lean_inc(v_val_167_);
lean_dec_ref_known(v___x_166_, 1);
v___x_168_ = lean_box(0);
v___x_169_ = lean_io_promise_resolve(v___x_168_, v_val_167_);
lean_dec(v_val_167_);
return v___x_169_;
}
else
{
lean_object* v___x_170_; 
lean_dec(v___x_166_);
v___x_170_ = lean_box(0);
return v___x_170_;
}
}
}
LEAN_EXPORT void l_Std_Semaphore_release_0interp(lean_interpreter_value* stack)
{
lean_object* v_sem_163_ = stack[0].m_obj;
lean_object* v_res_171_;
v_res_171_ = l_Std_Semaphore_release(v_sem_163_);
stack->m_obj
 = v_res_171_;
}
LEAN_EXPORT lean_object* l_Std_Semaphore_release___boxed(lean_object* v_sem_172_, lean_object* v_a_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Std_Semaphore_release(v_sem_172_);
return v_res_174_;
}
}
lean_object* l_Std_Semaphore_availablePermits___lam__0(lean_object* v___y_175_){
_start:
{
lean_object* v___x_177_; lean_object* v_permits_178_; 
v___x_177_ = lean_st_ref_get(v___y_175_);
v_permits_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_permits_178_);
lean_dec(v___x_177_);
return v_permits_178_;
}
}
LEAN_EXPORT void l_Std_Semaphore_availablePermits___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_175_ = stack[0].m_obj;
lean_object* v_res_179_;
v_res_179_ = l_Std_Semaphore_availablePermits___lam__0(v___y_175_);
stack->m_obj
 = v_res_179_;
}
LEAN_EXPORT lean_object* l_Std_Semaphore_availablePermits___lam__0___boxed(lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Std_Semaphore_availablePermits___lam__0(v___y_180_);
lean_dec(v___y_180_);
return v_res_182_;
}
}
lean_object* l_Std_Semaphore_availablePermits(lean_object* v_sem_184_){
_start:
{
lean_object* v___f_186_; lean_object* v___x_187_; 
v___f_186_ = ((lean_object*)(l_Std_Semaphore_availablePermits___closed__0));
v___x_187_ = l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___redArg(v_sem_184_, v___f_186_);
return v___x_187_;
}
}
LEAN_EXPORT void l_Std_Semaphore_availablePermits_0interp(lean_interpreter_value* stack)
{
lean_object* v_sem_184_ = stack[0].m_obj;
lean_object* v_res_188_;
v_res_188_ = l_Std_Semaphore_availablePermits(v_sem_184_);
stack->m_obj
 = v_res_188_;
}
LEAN_EXPORT lean_object* l_Std_Semaphore_availablePermits___boxed(lean_object* v_sem_189_, lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Std_Semaphore_availablePermits(v_sem_189_);
return v_res_191_;
}
}
lean_object* runtime_initialize_Init_Data_Queue(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Promise(uint8_t builtin);
lean_object* runtime_initialize_Std_Sync_Mutex(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sync_Semaphore(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Queue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Promise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sync_Mutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sync_Semaphore(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Queue(uint8_t builtin);
lean_object* initialize_Init_System_Promise(uint8_t builtin);
lean_object* initialize_Std_Sync_Mutex(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sync_Semaphore(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Queue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Promise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sync_Mutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sync_Semaphore(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sync_Semaphore(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sync_Semaphore(builtin);
}
#ifdef __cplusplus
}
#endif
