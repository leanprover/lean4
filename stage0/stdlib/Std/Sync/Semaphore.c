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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_io_basemutex_lock(lean_object*);
lean_object* lean_io_basemutex_unlock(lean_object*);
lean_object* l_Std_Queue_dequeue_x3f___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_Queue_empty(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise___redArg(lean_object* v_a_1_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_io_promise_new();
v___x_4_ = lean_io_promise_resolve(v_a_1_, v___x_3_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise___redArg___boxed(lean_object* v_a_5_, lean_object* v_a_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise___redArg(v_a_5_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise(lean_object* v_00_u03b1_8_, lean_object* v_inst_9_, lean_object* v_a_10_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise___redArg(v_a_10_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise___boxed(lean_object* v_00_u03b1_13_, lean_object* v_inst_14_, lean_object* v_a_15_, lean_object* v_a_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise(v_00_u03b1_13_, v_inst_14_, v_a_15_);
return v_res_17_;
}
}
static lean_object* _init_l_Std_Semaphore_new___closed__0(void){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Std_Queue_empty(lean_box(0));
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Std_Semaphore_new(lean_object* v_permits_19_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_21_ = lean_obj_once(&l_Std_Semaphore_new___closed__0, &l_Std_Semaphore_new___closed__0_once, _init_l_Std_Semaphore_new___closed__0);
v___x_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_22_, 0, v_permits_19_);
lean_ctor_set(v___x_22_, 1, v___x_21_);
v___x_23_ = l_Std_Mutex_new___redArg(v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Semaphore_new___boxed(lean_object* v_permits_24_, lean_object* v_a_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Std_Semaphore_new(v_permits_24_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___redArg(lean_object* v_mutex_27_, lean_object* v_k_28_){
_start:
{
lean_object* v_ref_30_; lean_object* v_mutex_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v_ref_30_ = lean_ctor_get(v_mutex_27_, 0);
lean_inc(v_ref_30_);
v_mutex_31_ = lean_ctor_get(v_mutex_27_, 1);
lean_inc(v_mutex_31_);
lean_dec_ref(v_mutex_27_);
v___x_32_ = lean_io_basemutex_lock(v_mutex_31_);
v___x_33_ = lean_apply_2(v_k_28_, v_ref_30_, lean_box(0));
v___x_34_ = lean_io_basemutex_unlock(v_mutex_31_);
lean_dec(v_mutex_31_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___redArg___boxed(lean_object* v_mutex_35_, lean_object* v_k_36_, lean_object* v___y_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___redArg(v_mutex_35_, v_k_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0(lean_object* v_00_u03b1_39_, lean_object* v_00_u03b2_40_, lean_object* v_mutex_41_, lean_object* v_k_42_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___redArg(v_mutex_41_, v_k_42_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___boxed(lean_object* v_00_u03b1_45_, lean_object* v_00_u03b2_46_, lean_object* v_mutex_47_, lean_object* v_k_48_, lean_object* v___y_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0(v_00_u03b1_45_, v_00_u03b2_46_, v_mutex_47_, v_k_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Semaphore_acquire___lam__0(lean_object* v___y_51_){
_start:
{
lean_object* v___x_53_; lean_object* v_permits_54_; lean_object* v_waiters_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_75_; 
v___x_53_ = lean_st_ref_get(v___y_51_);
v_permits_54_ = lean_ctor_get(v___x_53_, 0);
v_waiters_55_ = lean_ctor_get(v___x_53_, 1);
v_isSharedCheck_75_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_75_ == 0)
{
v___x_57_ = v___x_53_;
v_isShared_58_ = v_isSharedCheck_75_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_waiters_55_);
lean_inc(v_permits_54_);
lean_dec(v___x_53_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_75_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_59_ = lean_unsigned_to_nat(0u);
v___x_60_ = lean_nat_dec_lt(v___x_59_, v_permits_54_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_64_; 
v___x_61_ = lean_io_promise_new();
lean_inc(v___x_61_);
v___x_62_ = l_Std_Queue_enqueue___redArg(v___x_61_, v_waiters_55_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 1, v___x_62_);
v___x_64_ = v___x_57_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v_permits_54_);
lean_ctor_set(v_reuseFailAlloc_66_, 1, v___x_62_);
v___x_64_ = v_reuseFailAlloc_66_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
lean_object* v___x_65_; 
v___x_65_ = lean_st_ref_set(v___y_51_, v___x_64_);
return v___x_61_;
}
}
else
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_70_; 
v___x_67_ = lean_unsigned_to_nat(1u);
v___x_68_ = lean_nat_sub(v_permits_54_, v___x_67_);
lean_dec(v_permits_54_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_68_);
v___x_70_ = v___x_57_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_68_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v_waiters_55_);
v___x_70_ = v_reuseFailAlloc_74_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_71_ = lean_st_ref_set(v___y_51_, v___x_70_);
v___x_72_ = lean_box(0);
v___x_73_ = l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise___redArg(v___x_72_);
return v___x_73_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Semaphore_acquire___lam__0___boxed(lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Std_Semaphore_acquire___lam__0(v___y_76_);
lean_dec(v___y_76_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Std_Semaphore_acquire(lean_object* v_sem_80_){
_start:
{
lean_object* v___f_82_; lean_object* v___x_83_; 
v___f_82_ = ((lean_object*)(l_Std_Semaphore_acquire___closed__0));
v___x_83_ = l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___redArg(v_sem_80_, v___f_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Std_Semaphore_acquire___boxed(lean_object* v_sem_84_, lean_object* v_a_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Std_Semaphore_acquire(v_sem_84_);
return v_res_86_;
}
}
LEAN_EXPORT uint8_t l_Std_Semaphore_tryAcquire___lam__0(lean_object* v___y_87_){
_start:
{
lean_object* v___x_89_; lean_object* v_permits_90_; lean_object* v_waiters_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_103_; 
v___x_89_ = lean_st_ref_get(v___y_87_);
v_permits_90_ = lean_ctor_get(v___x_89_, 0);
v_waiters_91_ = lean_ctor_get(v___x_89_, 1);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_103_ == 0)
{
v___x_93_ = v___x_89_;
v_isShared_94_ = v_isSharedCheck_103_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_waiters_91_);
lean_inc(v_permits_90_);
lean_dec(v___x_89_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_103_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_95_ = lean_unsigned_to_nat(0u);
v___x_96_ = lean_nat_dec_lt(v___x_95_, v_permits_90_);
if (v___x_96_ == 0)
{
lean_del_object(v___x_93_);
lean_dec_ref(v_waiters_91_);
lean_dec(v_permits_90_);
return v___x_96_;
}
else
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_100_; 
v___x_97_ = lean_unsigned_to_nat(1u);
v___x_98_ = lean_nat_sub(v_permits_90_, v___x_97_);
lean_dec(v_permits_90_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 0, v___x_98_);
v___x_100_ = v___x_93_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___x_98_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v_waiters_91_);
v___x_100_ = v_reuseFailAlloc_102_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v___x_101_; 
v___x_101_ = lean_st_ref_set(v___y_87_, v___x_100_);
return v___x_96_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Semaphore_tryAcquire___lam__0___boxed(lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
uint8_t v_res_106_; lean_object* v_r_107_; 
v_res_106_ = l_Std_Semaphore_tryAcquire___lam__0(v___y_104_);
lean_dec(v___y_104_);
v_r_107_ = lean_box(v_res_106_);
return v_r_107_;
}
}
LEAN_EXPORT uint8_t l_Std_Semaphore_tryAcquire(lean_object* v_sem_109_){
_start:
{
lean_object* v___f_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v___f_111_ = ((lean_object*)(l_Std_Semaphore_tryAcquire___closed__0));
v___x_112_ = l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___redArg(v_sem_109_, v___f_111_);
v___x_113_ = lean_unbox(v___x_112_);
lean_dec(v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Semaphore_tryAcquire___boxed(lean_object* v_sem_114_, lean_object* v_a_115_){
_start:
{
uint8_t v_res_116_; lean_object* v_r_117_; 
v_res_116_ = l_Std_Semaphore_tryAcquire(v_sem_114_);
v_r_117_ = lean_box(v_res_116_);
return v_r_117_;
}
}
LEAN_EXPORT lean_object* l_Std_Semaphore_release___lam__0(lean_object* v___y_118_){
_start:
{
lean_object* v___x_120_; lean_object* v_permits_121_; lean_object* v_waiters_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_148_; 
v___x_120_ = lean_st_ref_get(v___y_118_);
v_permits_121_ = lean_ctor_get(v___x_120_, 0);
v_waiters_122_ = lean_ctor_get(v___x_120_, 1);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_148_ == 0)
{
v___x_124_ = v___x_120_;
v_isShared_125_ = v_isSharedCheck_148_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_waiters_122_);
lean_inc(v_permits_121_);
lean_dec(v___x_120_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_148_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; 
lean_inc_ref(v_waiters_122_);
v___x_126_ = l_Std_Queue_dequeue_x3f___redArg(v_waiters_122_);
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_127_ = lean_unsigned_to_nat(1u);
v___x_128_ = lean_nat_add(v_permits_121_, v___x_127_);
lean_dec(v_permits_121_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v___x_128_);
v___x_130_ = v___x_124_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_128_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v_waiters_122_);
v___x_130_ = v_reuseFailAlloc_133_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_st_ref_set(v___y_118_, v___x_130_);
v___x_132_ = lean_box(0);
return v___x_132_;
}
}
else
{
lean_object* v_val_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_147_; 
lean_dec_ref(v_waiters_122_);
v_val_134_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_147_ == 0)
{
v___x_136_ = v___x_126_;
v_isShared_137_ = v_isSharedCheck_147_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_val_134_);
lean_dec(v___x_126_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_147_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v_fst_138_; lean_object* v_snd_139_; lean_object* v___x_141_; 
v_fst_138_ = lean_ctor_get(v_val_134_, 0);
lean_inc(v_fst_138_);
v_snd_139_ = lean_ctor_get(v_val_134_, 1);
lean_inc(v_snd_139_);
lean_dec(v_val_134_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 1, v_snd_139_);
v___x_141_ = v___x_124_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_permits_121_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_snd_139_);
v___x_141_ = v_reuseFailAlloc_146_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v___x_142_; lean_object* v___x_144_; 
v___x_142_ = lean_st_ref_set(v___y_118_, v___x_141_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 0, v_fst_138_);
v___x_144_ = v___x_136_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_fst_138_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Semaphore_release___lam__0___boxed(lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Std_Semaphore_release___lam__0(v___y_149_);
lean_dec(v___y_149_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Std_Semaphore_release(lean_object* v_sem_153_){
_start:
{
lean_object* v___f_155_; lean_object* v___x_156_; 
v___f_155_ = ((lean_object*)(l_Std_Semaphore_release___closed__0));
v___x_156_ = l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___redArg(v_sem_153_, v___f_155_);
if (lean_obj_tag(v___x_156_) == 1)
{
lean_object* v_val_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v_val_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_val_157_);
lean_dec_ref(v___x_156_);
v___x_158_ = lean_box(0);
v___x_159_ = lean_io_promise_resolve(v___x_158_, v_val_157_);
lean_dec(v_val_157_);
return v___x_159_;
}
else
{
lean_object* v___x_160_; 
lean_dec(v___x_156_);
v___x_160_ = lean_box(0);
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Semaphore_release___boxed(lean_object* v_sem_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Std_Semaphore_release(v_sem_161_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Semaphore_availablePermits___lam__0(lean_object* v___y_164_){
_start:
{
lean_object* v___x_166_; lean_object* v_permits_167_; 
v___x_166_ = lean_st_ref_get(v___y_164_);
v_permits_167_ = lean_ctor_get(v___x_166_, 0);
lean_inc(v_permits_167_);
lean_dec(v___x_166_);
return v_permits_167_;
}
}
LEAN_EXPORT lean_object* l_Std_Semaphore_availablePermits___lam__0___boxed(lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Std_Semaphore_availablePermits___lam__0(v___y_168_);
lean_dec(v___y_168_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Std_Semaphore_availablePermits(lean_object* v_sem_172_){
_start:
{
lean_object* v___f_174_; lean_object* v___x_175_; 
v___f_174_ = ((lean_object*)(l_Std_Semaphore_availablePermits___closed__0));
v___x_175_ = l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___redArg(v_sem_172_, v___f_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Std_Semaphore_availablePermits___boxed(lean_object* v_sem_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Std_Semaphore_availablePermits(v_sem_176_);
return v_res_178_;
}
}
lean_object* runtime_initialize_Init_Data_Queue(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Promise(uint8_t builtin);
lean_object* runtime_initialize_Std_Sync_Mutex(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sync_Semaphore(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
