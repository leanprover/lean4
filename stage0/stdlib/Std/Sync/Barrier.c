// Lean compiler output
// Module: Std.Sync.Barrier
// Imports: public import Std.Sync.Mutex
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_io_condvar_notify_all(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_io_condvar_wait(lean_object*, lean_object*);
lean_object* lean_io_basemutex_lock(lean_object*);
lean_object* lean_io_basemutex_unlock(lean_object*);
lean_object* l_Std_Mutex_new___redArg(lean_object*);
lean_object* lean_io_condvar_new();
static const lean_ctor_object l_Std_Barrier_new___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Barrier_new___closed__0 = (const lean_object*)&l_Std_Barrier_new___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Barrier_new(lean_object*);
LEAN_EXPORT lean_object* l_Std_Barrier_new___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Barrier_wait___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Barrier_wait___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Barrier_wait___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Barrier_wait___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Barrier_wait(lean_object*);
LEAN_EXPORT lean_object* l_Std_Barrier_wait___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Barrier_new(lean_object* v_numThreads_3_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_5_ = ((lean_object*)(l_Std_Barrier_new___closed__0));
v___x_6_ = l_Std_Mutex_new___redArg(v___x_5_);
v___x_7_ = lean_io_condvar_new();
v___x_8_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_8_, 0, v___x_6_);
lean_ctor_set(v___x_8_, 1, v___x_7_);
lean_ctor_set(v___x_8_, 2, v_numThreads_3_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Barrier_new___boxed(lean_object* v_numThreads_9_, lean_object* v_a_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Std_Barrier_new(v_numThreads_9_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___redArg(lean_object* v_mutex_12_, lean_object* v_k_13_){
_start:
{
lean_object* v_ref_15_; lean_object* v_mutex_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v_ref_15_ = lean_ctor_get(v_mutex_12_, 0);
lean_inc(v_ref_15_);
v_mutex_16_ = lean_ctor_get(v_mutex_12_, 1);
lean_inc(v_mutex_16_);
lean_dec_ref(v_mutex_12_);
v___x_17_ = lean_io_basemutex_lock(v_mutex_16_);
v___x_18_ = lean_apply_2(v_k_13_, v_ref_15_, lean_box(0));
v___x_19_ = lean_io_basemutex_unlock(v_mutex_16_);
lean_dec(v_mutex_16_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___redArg___boxed(lean_object* v_mutex_20_, lean_object* v_k_21_, lean_object* v___y_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___redArg(v_mutex_20_, v_k_21_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1(lean_object* v_00_u03b1_24_, lean_object* v_00_u03b2_25_, lean_object* v_mutex_26_, lean_object* v_k_27_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___redArg(v_mutex_26_, v_k_27_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___boxed(lean_object* v_00_u03b1_30_, lean_object* v_00_u03b2_31_, lean_object* v_mutex_32_, lean_object* v_k_33_, lean_object* v___y_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1(v_00_u03b1_30_, v_00_u03b2_31_, v_mutex_32_, v_k_33_);
return v_res_35_;
}
}
LEAN_EXPORT uint8_t l_Std_Barrier_wait___lam__0(lean_object* v_generationId_36_, lean_object* v___y_37_){
_start:
{
lean_object* v___x_39_; lean_object* v_generationId_40_; uint8_t v___x_41_; uint8_t v___x_42_; 
v___x_39_ = lean_st_ref_get(v___y_37_);
v_generationId_40_ = lean_ctor_get(v___x_39_, 1);
lean_inc(v_generationId_40_);
lean_dec(v___x_39_);
v___x_41_ = lean_nat_dec_eq(v_generationId_40_, v_generationId_36_);
lean_dec(v_generationId_40_);
v___x_42_ = lean_bool_not(v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Barrier_wait___lam__0___boxed(lean_object* v_generationId_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
uint8_t v_res_46_; lean_object* v_r_47_; 
v_res_46_ = l_Std_Barrier_wait___lam__0(v_generationId_43_, v___y_44_);
lean_dec(v___y_44_);
lean_dec(v_generationId_43_);
v_r_47_ = lean_box(v_res_46_);
return v_r_47_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg(lean_object* v_pred_48_, lean_object* v_condvar_49_, lean_object* v_mutex_50_, lean_object* v___y_51_){
_start:
{
lean_object* v___x_53_; uint8_t v___x_54_; uint8_t v___x_55_; 
lean_inc_ref(v_pred_48_);
lean_inc(v___y_51_);
v___x_53_ = lean_apply_2(v_pred_48_, v___y_51_, lean_box(0));
v___x_54_ = lean_unbox(v___x_53_);
v___x_55_ = lean_bool_not(v___x_54_);
if (v___x_55_ == 0)
{
lean_object* v___x_56_; 
lean_dec_ref(v_pred_48_);
v___x_56_ = lean_box(0);
return v___x_56_;
}
else
{
lean_object* v___x_57_; 
v___x_57_ = lean_io_condvar_wait(v_condvar_49_, v_mutex_50_);
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg___boxed(lean_object* v_pred_59_, lean_object* v_condvar_60_, lean_object* v_mutex_61_, lean_object* v___y_62_, lean_object* v___y_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l___private_Init_While_0__repeatM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg(v_pred_59_, v_condvar_60_, v_mutex_61_, v___y_62_);
lean_dec(v___y_62_);
lean_dec(v_mutex_61_);
lean_dec(v_condvar_60_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0(lean_object* v_condvar_65_, lean_object* v_mutex_66_, lean_object* v_pred_67_, lean_object* v___y_68_){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = l___private_Init_While_0__repeatM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg(v_pred_67_, v_condvar_65_, v_mutex_66_, v___y_68_);
v___x_71_ = lean_box(0);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0___boxed(lean_object* v_condvar_72_, lean_object* v_mutex_73_, lean_object* v_pred_74_, lean_object* v___y_75_, lean_object* v___y_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0(v_condvar_72_, v_mutex_73_, v_pred_74_, v___y_75_);
lean_dec(v___y_75_);
lean_dec(v_mutex_73_);
lean_dec(v_condvar_72_);
return v_res_77_;
}
}
LEAN_EXPORT uint8_t l_Std_Barrier_wait___lam__1(lean_object* v_numThreads_78_, lean_object* v_cvar_79_, lean_object* v_lock_80_, lean_object* v___y_81_){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v_count_85_; lean_object* v_generationId_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_119_; 
v___x_83_ = lean_st_ref_get(v___y_81_);
v___x_84_ = lean_st_ref_take(v___y_81_);
v_count_85_ = lean_ctor_get(v___x_84_, 0);
v_generationId_86_ = lean_ctor_get(v___x_84_, 1);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_119_ == 0)
{
v___x_88_ = v___x_84_;
v_isShared_89_ = v_isSharedCheck_119_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_generationId_86_);
lean_inc(v_count_85_);
lean_dec(v___x_84_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_119_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_90_ = lean_unsigned_to_nat(1u);
v___x_91_ = lean_nat_add(v_count_85_, v___x_90_);
lean_dec(v_count_85_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 0, v___x_91_);
v___x_93_ = v___x_88_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_91_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v_generationId_86_);
v___x_93_ = v_reuseFailAlloc_118_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v_count_96_; uint8_t v___x_97_; 
v___x_94_ = lean_st_ref_set(v___y_81_, v___x_93_);
v___x_95_ = lean_st_ref_get(v___y_81_);
v_count_96_ = lean_ctor_get(v___x_95_, 0);
lean_inc(v_count_96_);
lean_dec(v___x_95_);
v___x_97_ = lean_nat_dec_lt(v_count_96_, v_numThreads_78_);
lean_dec(v_count_96_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; lean_object* v_generationId_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_111_; 
lean_dec(v___x_83_);
v___x_98_ = lean_st_ref_take(v___y_81_);
v_generationId_99_ = lean_ctor_get(v___x_98_, 1);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_111_ == 0)
{
lean_object* v_unused_112_; 
v_unused_112_ = lean_ctor_get(v___x_98_, 0);
lean_dec(v_unused_112_);
v___x_101_ = v___x_98_;
v_isShared_102_ = v_isSharedCheck_111_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_generationId_99_);
lean_dec(v___x_98_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_111_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_103_ = lean_unsigned_to_nat(0u);
v___x_104_ = lean_nat_add(v_generationId_99_, v___x_90_);
lean_dec(v_generationId_99_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 1, v___x_104_);
lean_ctor_set(v___x_101_, 0, v___x_103_);
v___x_106_ = v___x_101_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_103_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v___x_104_);
v___x_106_ = v_reuseFailAlloc_110_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_107_ = lean_st_ref_set(v___y_81_, v___x_106_);
v___x_108_ = lean_io_condvar_notify_all(v_cvar_79_);
v___x_109_ = 1;
return v___x_109_;
}
}
}
else
{
lean_object* v_generationId_113_; lean_object* v_mutex_114_; lean_object* v___f_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v_generationId_113_ = lean_ctor_get(v___x_83_, 1);
lean_inc(v_generationId_113_);
lean_dec(v___x_83_);
v_mutex_114_ = lean_ctor_get(v_lock_80_, 1);
v___f_115_ = lean_alloc_closure((void*)(l_Std_Barrier_wait___lam__0___boxed), 3, 1);
lean_closure_set(v___f_115_, 0, v_generationId_113_);
v___x_116_ = l_Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0(v_cvar_79_, v_mutex_114_, v___f_115_, v___y_81_);
v___x_117_ = 0;
return v___x_117_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Barrier_wait___lam__1___boxed(lean_object* v_numThreads_120_, lean_object* v_cvar_121_, lean_object* v_lock_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
uint8_t v_res_125_; lean_object* v_r_126_; 
v_res_125_ = l_Std_Barrier_wait___lam__1(v_numThreads_120_, v_cvar_121_, v_lock_122_, v___y_123_);
lean_dec(v___y_123_);
lean_dec_ref(v_lock_122_);
lean_dec(v_cvar_121_);
lean_dec(v_numThreads_120_);
v_r_126_ = lean_box(v_res_125_);
return v_r_126_;
}
}
LEAN_EXPORT uint8_t l_Std_Barrier_wait(lean_object* v_barrier_127_){
_start:
{
lean_object* v_lock_129_; lean_object* v_cvar_130_; lean_object* v_numThreads_131_; lean_object* v___f_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
v_lock_129_ = lean_ctor_get(v_barrier_127_, 0);
lean_inc_ref_n(v_lock_129_, 2);
v_cvar_130_ = lean_ctor_get(v_barrier_127_, 1);
lean_inc(v_cvar_130_);
v_numThreads_131_ = lean_ctor_get(v_barrier_127_, 2);
lean_inc(v_numThreads_131_);
lean_dec_ref(v_barrier_127_);
v___f_132_ = lean_alloc_closure((void*)(l_Std_Barrier_wait___lam__1___boxed), 5, 3);
lean_closure_set(v___f_132_, 0, v_numThreads_131_);
lean_closure_set(v___f_132_, 1, v_cvar_130_);
lean_closure_set(v___f_132_, 2, v_lock_129_);
v___x_133_ = l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___redArg(v_lock_129_, v___f_132_);
v___x_134_ = lean_unbox(v___x_133_);
lean_dec(v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Std_Barrier_wait___boxed(lean_object* v_barrier_135_, lean_object* v_a_136_){
_start:
{
uint8_t v_res_137_; lean_object* v_r_138_; 
v_res_137_ = l_Std_Barrier_wait(v_barrier_135_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0(lean_object* v_pred_139_, lean_object* v_condvar_140_, lean_object* v_mutex_141_, lean_object* v_inst_142_, lean_object* v_a_143_, lean_object* v___y_144_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l___private_Init_While_0__repeatM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg(v_pred_139_, v_condvar_140_, v_mutex_141_, v___y_144_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___boxed(lean_object* v_pred_147_, lean_object* v_condvar_148_, lean_object* v_mutex_149_, lean_object* v_inst_150_, lean_object* v_a_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l___private_Init_While_0__repeatM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0(v_pred_147_, v_condvar_148_, v_mutex_149_, v_inst_150_, v_a_151_, v___y_152_);
lean_dec(v___y_152_);
lean_dec(v_mutex_149_);
lean_dec(v_condvar_148_);
return v_res_154_;
}
}
lean_object* runtime_initialize_Std_Sync_Mutex(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sync_Barrier(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Sync_Mutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sync_Barrier(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sync_Mutex(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sync_Barrier(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sync_Mutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sync_Barrier(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sync_Barrier(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sync_Barrier(builtin);
}
#ifdef __cplusplus
}
#endif
