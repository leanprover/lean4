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
LEAN_EXPORT uint8_t l_Std_Barrier_wait___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Barrier_wait___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Barrier_wait___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Barrier_wait___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Barrier_wait(lean_object*);
LEAN_EXPORT lean_object* l_Std_Barrier_wait___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_Barrier_wait___lam__0(lean_object* v_generationId_36_, uint8_t v___x_37_, lean_object* v___y_38_){
_start:
{
lean_object* v___x_40_; lean_object* v_generationId_41_; uint8_t v___x_42_; 
v___x_40_ = lean_st_ref_get(v___y_38_);
v_generationId_41_ = lean_ctor_get(v___x_40_, 1);
lean_inc(v_generationId_41_);
lean_dec(v___x_40_);
v___x_42_ = lean_nat_dec_eq(v_generationId_41_, v_generationId_36_);
lean_dec(v_generationId_41_);
if (v___x_42_ == 0)
{
return v___x_37_;
}
else
{
uint8_t v___x_43_; 
v___x_43_ = 0;
return v___x_43_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Barrier_wait___lam__0___boxed(lean_object* v_generationId_44_, lean_object* v___x_45_, lean_object* v___y_46_, lean_object* v___y_47_){
_start:
{
uint8_t v___x_2266__boxed_48_; uint8_t v_res_49_; lean_object* v_r_50_; 
v___x_2266__boxed_48_ = lean_unbox(v___x_45_);
v_res_49_ = l_Std_Barrier_wait___lam__0(v_generationId_44_, v___x_2266__boxed_48_, v___y_46_);
lean_dec(v___y_46_);
lean_dec(v_generationId_44_);
v_r_50_ = lean_box(v_res_49_);
return v_r_50_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg(lean_object* v_pred_51_, lean_object* v_condvar_52_, lean_object* v_mutex_53_, lean_object* v___y_54_){
_start:
{
lean_object* v___x_56_; uint8_t v___x_57_; 
lean_inc_ref(v_pred_51_);
lean_inc(v___y_54_);
v___x_56_ = lean_apply_2(v_pred_51_, v___y_54_, lean_box(0));
v___x_57_ = lean_unbox(v___x_56_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; 
v___x_58_ = lean_io_condvar_wait(v_condvar_52_, v_mutex_53_);
goto _start;
}
else
{
lean_object* v___x_60_; 
lean_dec_ref(v_pred_51_);
v___x_60_ = lean_box(0);
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg___boxed(lean_object* v_pred_61_, lean_object* v_condvar_62_, lean_object* v_mutex_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg(v_pred_61_, v_condvar_62_, v_mutex_63_, v___y_64_);
lean_dec(v___y_64_);
lean_dec(v_mutex_63_);
lean_dec(v_condvar_62_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0(lean_object* v_condvar_67_, lean_object* v_mutex_68_, lean_object* v_pred_69_, lean_object* v___y_70_){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg(v_pred_69_, v_condvar_67_, v_mutex_68_, v___y_70_);
v___x_73_ = lean_box(0);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0___boxed(lean_object* v_condvar_74_, lean_object* v_mutex_75_, lean_object* v_pred_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0(v_condvar_74_, v_mutex_75_, v_pred_76_, v___y_77_);
lean_dec(v___y_77_);
lean_dec(v_mutex_75_);
lean_dec(v_condvar_74_);
return v_res_79_;
}
}
LEAN_EXPORT uint8_t l_Std_Barrier_wait___lam__1(lean_object* v_numThreads_80_, lean_object* v_cvar_81_, lean_object* v_lock_82_, lean_object* v___y_83_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v_count_87_; lean_object* v_generationId_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_122_; 
v___x_85_ = lean_st_ref_get(v___y_83_);
v___x_86_ = lean_st_ref_take(v___y_83_);
v_count_87_ = lean_ctor_get(v___x_86_, 0);
v_generationId_88_ = lean_ctor_get(v___x_86_, 1);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_122_ == 0)
{
v___x_90_ = v___x_86_;
v_isShared_91_ = v_isSharedCheck_122_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_generationId_88_);
lean_inc(v_count_87_);
lean_dec(v___x_86_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_122_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_95_; 
v___x_92_ = lean_unsigned_to_nat(1u);
v___x_93_ = lean_nat_add(v_count_87_, v___x_92_);
lean_dec(v_count_87_);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 0, v___x_93_);
v___x_95_ = v___x_90_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_93_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_generationId_88_);
v___x_95_ = v_reuseFailAlloc_121_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v_count_98_; uint8_t v___x_99_; 
v___x_96_ = lean_st_ref_set(v___y_83_, v___x_95_);
v___x_97_ = lean_st_ref_get(v___y_83_);
v_count_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc(v_count_98_);
lean_dec(v___x_97_);
v___x_99_ = lean_nat_dec_lt(v_count_98_, v_numThreads_80_);
lean_dec(v_count_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; lean_object* v_generationId_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_113_; 
lean_dec(v___x_85_);
v___x_100_ = lean_st_ref_take(v___y_83_);
v_generationId_101_ = lean_ctor_get(v___x_100_, 1);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_113_ == 0)
{
lean_object* v_unused_114_; 
v_unused_114_ = lean_ctor_get(v___x_100_, 0);
lean_dec(v_unused_114_);
v___x_103_ = v___x_100_;
v_isShared_104_ = v_isSharedCheck_113_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_generationId_101_);
lean_dec(v___x_100_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_113_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_108_; 
v___x_105_ = lean_unsigned_to_nat(0u);
v___x_106_ = lean_nat_add(v_generationId_101_, v___x_92_);
lean_dec(v_generationId_101_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 1, v___x_106_);
lean_ctor_set(v___x_103_, 0, v___x_105_);
v___x_108_ = v___x_103_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_105_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v___x_106_);
v___x_108_ = v_reuseFailAlloc_112_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_109_ = lean_st_ref_set(v___y_83_, v___x_108_);
v___x_110_ = lean_io_condvar_notify_all(v_cvar_81_);
v___x_111_ = 1;
return v___x_111_;
}
}
}
else
{
lean_object* v_generationId_115_; lean_object* v_mutex_116_; lean_object* v___x_117_; lean_object* v___f_118_; lean_object* v___x_119_; uint8_t v___x_120_; 
v_generationId_115_ = lean_ctor_get(v___x_85_, 1);
lean_inc(v_generationId_115_);
lean_dec(v___x_85_);
v_mutex_116_ = lean_ctor_get(v_lock_82_, 1);
v___x_117_ = lean_box(v___x_99_);
v___f_118_ = lean_alloc_closure((void*)(l_Std_Barrier_wait___lam__0___boxed), 4, 2);
lean_closure_set(v___f_118_, 0, v_generationId_115_);
lean_closure_set(v___f_118_, 1, v___x_117_);
v___x_119_ = l_Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0(v_cvar_81_, v_mutex_116_, v___f_118_, v___y_83_);
v___x_120_ = 0;
return v___x_120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Barrier_wait___lam__1___boxed(lean_object* v_numThreads_123_, lean_object* v_cvar_124_, lean_object* v_lock_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
uint8_t v_res_128_; lean_object* v_r_129_; 
v_res_128_ = l_Std_Barrier_wait___lam__1(v_numThreads_123_, v_cvar_124_, v_lock_125_, v___y_126_);
lean_dec(v___y_126_);
lean_dec_ref(v_lock_125_);
lean_dec(v_cvar_124_);
lean_dec(v_numThreads_123_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT uint8_t l_Std_Barrier_wait(lean_object* v_barrier_130_){
_start:
{
lean_object* v_lock_132_; lean_object* v_cvar_133_; lean_object* v_numThreads_134_; lean_object* v___f_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v_lock_132_ = lean_ctor_get(v_barrier_130_, 0);
lean_inc_ref(v_lock_132_);
v_cvar_133_ = lean_ctor_get(v_barrier_130_, 1);
lean_inc(v_cvar_133_);
v_numThreads_134_ = lean_ctor_get(v_barrier_130_, 2);
lean_inc(v_numThreads_134_);
lean_dec_ref(v_barrier_130_);
lean_inc_ref(v_lock_132_);
v___f_135_ = lean_alloc_closure((void*)(l_Std_Barrier_wait___lam__1___boxed), 5, 3);
lean_closure_set(v___f_135_, 0, v_numThreads_134_);
lean_closure_set(v___f_135_, 1, v_cvar_133_);
lean_closure_set(v___f_135_, 2, v_lock_132_);
v___x_136_ = l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___redArg(v_lock_132_, v___f_135_);
v___x_137_ = lean_unbox(v___x_136_);
lean_dec(v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Std_Barrier_wait___boxed(lean_object* v_barrier_138_, lean_object* v_a_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = l_Std_Barrier_wait(v_barrier_138_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0(lean_object* v_pred_142_, lean_object* v_condvar_143_, lean_object* v_mutex_144_, lean_object* v_b_145_, lean_object* v___y_146_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg(v_pred_142_, v_condvar_143_, v_mutex_144_, v___y_146_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___boxed(lean_object* v_pred_149_, lean_object* v_condvar_150_, lean_object* v_mutex_151_, lean_object* v_b_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0(v_pred_149_, v_condvar_150_, v_mutex_151_, v_b_152_, v___y_153_);
lean_dec(v___y_153_);
lean_dec(v_mutex_151_);
lean_dec(v_condvar_150_);
return v_res_155_;
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
