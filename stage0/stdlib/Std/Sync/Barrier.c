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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Std_Barrier_new(lean_object* v_numThreads_3_){
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
LEAN_EXPORT void l_Std_Barrier_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_numThreads_3_ = stack[0].m_obj;
lean_object* v_res_9_;
v_res_9_ = l_Std_Barrier_new(v_numThreads_3_);
stack->m_obj
 = v_res_9_;
}
LEAN_EXPORT lean_object* l_Std_Barrier_new___boxed(lean_object* v_numThreads_10_, lean_object* v_a_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_Barrier_new(v_numThreads_10_);
return v_res_12_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___redArg(lean_object* v_mutex_13_, lean_object* v_k_14_){
_start:
{
lean_object* v_ref_16_; lean_object* v_mutex_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v_ref_16_ = lean_ctor_get(v_mutex_13_, 0);
lean_inc(v_ref_16_);
v_mutex_17_ = lean_ctor_get(v_mutex_13_, 1);
lean_inc(v_mutex_17_);
lean_dec_ref(v_mutex_13_);
v___x_18_ = lean_io_basemutex_lock(v_mutex_17_);
v___x_19_ = lean_apply_2(v_k_14_, v_ref_16_, lean_box(0));
v___x_20_ = lean_io_basemutex_unlock(v_mutex_17_);
lean_dec(v_mutex_17_);
return v___x_19_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_13_ = stack[0].m_obj;
lean_object* v_k_14_ = stack[1].m_obj;
lean_object* v_res_21_;
v_res_21_ = l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___redArg(v_mutex_13_, v_k_14_);
stack->m_obj
 = v_res_21_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___redArg___boxed(lean_object* v_mutex_22_, lean_object* v_k_23_, lean_object* v___y_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___redArg(v_mutex_22_, v_k_23_);
return v_res_25_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1(lean_object* v_00_u03b1_26_, lean_object* v_00_u03b2_27_, lean_object* v_mutex_28_, lean_object* v_k_29_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___redArg(v_mutex_28_, v_k_29_);
return v___x_31_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_28_ = stack[2].m_obj;
lean_object* v_k_29_ = stack[3].m_obj;
lean_object* v_res_32_;
v_res_32_ = l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1(lean_box(0), lean_box(0), v_mutex_28_, v_k_29_);
stack->m_obj
 = v_res_32_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___boxed(lean_object* v_00_u03b1_33_, lean_object* v_00_u03b2_34_, lean_object* v_mutex_35_, lean_object* v_k_36_, lean_object* v___y_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1(v_00_u03b1_33_, v_00_u03b2_34_, v_mutex_35_, v_k_36_);
return v_res_38_;
}
}
uint8_t l_Std_Barrier_wait___lam__0(lean_object* v_generationId_39_, uint8_t v___x_40_, lean_object* v___y_41_){
_start:
{
lean_object* v___x_43_; lean_object* v_generationId_44_; uint8_t v___x_45_; 
v___x_43_ = lean_st_ref_get(v___y_41_);
v_generationId_44_ = lean_ctor_get(v___x_43_, 1);
lean_inc(v_generationId_44_);
lean_dec(v___x_43_);
v___x_45_ = lean_nat_dec_eq(v_generationId_44_, v_generationId_39_);
lean_dec(v_generationId_44_);
if (v___x_45_ == 0)
{
return v___x_40_;
}
else
{
uint8_t v___x_46_; 
v___x_46_ = 0;
return v___x_46_;
}
}
}
LEAN_EXPORT void l_Std_Barrier_wait___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_generationId_39_ = stack[0].m_obj;
uint8_t v___x_40_ = stack[1].m_num;
lean_object* v___y_41_ = stack[2].m_obj;
uint8_t v_res_47_;
v_res_47_ = l_Std_Barrier_wait___lam__0(v_generationId_39_, v___x_40_, v___y_41_);
stack->m_num = v_res_47_;
}
LEAN_EXPORT lean_object* l_Std_Barrier_wait___lam__0___boxed(lean_object* v_generationId_48_, lean_object* v___x_49_, lean_object* v___y_50_, lean_object* v___y_51_){
_start:
{
uint8_t v___x_2425__boxed_52_; uint8_t v_res_53_; lean_object* v_r_54_; 
v___x_2425__boxed_52_ = lean_unbox(v___x_49_);
v_res_53_ = l_Std_Barrier_wait___lam__0(v_generationId_48_, v___x_2425__boxed_52_, v___y_50_);
lean_dec(v___y_50_);
lean_dec(v_generationId_48_);
v_r_54_ = lean_box(v_res_53_);
return v_r_54_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg(lean_object* v_pred_55_, lean_object* v_condvar_56_, lean_object* v_mutex_57_, lean_object* v___y_58_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v___x_60_ = lean_box(0);
lean_inc_ref(v_pred_55_);
lean_inc(v___y_58_);
v___x_61_ = lean_apply_2(v_pred_55_, v___y_58_, lean_box(0));
v___x_62_ = lean_unbox(v___x_61_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; 
v___x_63_ = lean_io_condvar_wait(v_condvar_56_, v_mutex_57_);
goto _start;
}
else
{
lean_dec_ref(v_pred_55_);
return v___x_60_;
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_pred_55_ = stack[0].m_obj;
lean_object* v_condvar_56_ = stack[1].m_obj;
lean_object* v_mutex_57_ = stack[2].m_obj;
lean_object* v___y_58_ = stack[3].m_obj;
lean_object* v_res_65_;
v_res_65_ = l___private_Init_While_0__repeatM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg(v_pred_55_, v_condvar_56_, v_mutex_57_, v___y_58_);
stack->m_obj
 = v_res_65_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg___boxed(lean_object* v_pred_66_, lean_object* v_condvar_67_, lean_object* v_mutex_68_, lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l___private_Init_While_0__repeatM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg(v_pred_66_, v_condvar_67_, v_mutex_68_, v___y_69_);
lean_dec(v___y_69_);
lean_dec(v_mutex_68_);
lean_dec(v_condvar_67_);
return v_res_71_;
}
}
lean_object* l_Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0(lean_object* v_condvar_72_, lean_object* v_mutex_73_, lean_object* v_pred_74_, lean_object* v___y_75_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_box(0);
v___x_78_ = l___private_Init_While_0__repeatM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg(v_pred_74_, v_condvar_72_, v_mutex_73_, v___y_75_);
return v___x_77_;
}
}
LEAN_EXPORT void l_Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_condvar_72_ = stack[0].m_obj;
lean_object* v_mutex_73_ = stack[1].m_obj;
lean_object* v_pred_74_ = stack[2].m_obj;
lean_object* v___y_75_ = stack[3].m_obj;
lean_object* v_res_79_;
v_res_79_ = l_Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0(v_condvar_72_, v_mutex_73_, v_pred_74_, v___y_75_);
stack->m_obj
 = v_res_79_;
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0___boxed(lean_object* v_condvar_80_, lean_object* v_mutex_81_, lean_object* v_pred_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0(v_condvar_80_, v_mutex_81_, v_pred_82_, v___y_83_);
lean_dec(v___y_83_);
lean_dec(v_mutex_81_);
lean_dec(v_condvar_80_);
return v_res_85_;
}
}
uint8_t l_Std_Barrier_wait___lam__1(lean_object* v_numThreads_86_, lean_object* v_cvar_87_, lean_object* v_lock_88_, lean_object* v___y_89_){
_start:
{
lean_object* v___x_91_; lean_object* v_generationId_92_; lean_object* v___x_93_; lean_object* v_count_94_; lean_object* v_generationId_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_128_; 
v___x_91_ = lean_st_ref_get(v___y_89_);
v_generationId_92_ = lean_ctor_get(v___x_91_, 1);
lean_inc(v_generationId_92_);
lean_dec(v___x_91_);
v___x_93_ = lean_st_ref_take(v___y_89_);
v_count_94_ = lean_ctor_get(v___x_93_, 0);
v_generationId_95_ = lean_ctor_get(v___x_93_, 1);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_128_ == 0)
{
v___x_97_ = v___x_93_;
v_isShared_98_ = v_isSharedCheck_128_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_generationId_95_);
lean_inc(v_count_94_);
lean_dec(v___x_93_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_128_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_102_; 
v___x_99_ = lean_unsigned_to_nat(1u);
v___x_100_ = lean_nat_add(v_count_94_, v___x_99_);
lean_dec(v_count_94_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 0, v___x_100_);
v___x_102_ = v___x_97_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___x_100_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v_generationId_95_);
v___x_102_ = v_reuseFailAlloc_127_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v_count_105_; uint8_t v___x_106_; 
v___x_103_ = lean_st_ref_put(v___y_89_, v___x_102_);
v___x_104_ = lean_st_ref_get(v___y_89_);
v_count_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_count_105_);
lean_dec(v___x_104_);
v___x_106_ = lean_nat_dec_lt(v_count_105_, v_numThreads_86_);
lean_dec(v_count_105_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; lean_object* v_generationId_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_120_; 
lean_dec(v_generationId_92_);
v___x_107_ = lean_st_ref_take(v___y_89_);
v_generationId_108_ = lean_ctor_get(v___x_107_, 1);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_120_ == 0)
{
lean_object* v_unused_121_; 
v_unused_121_ = lean_ctor_get(v___x_107_, 0);
lean_dec(v_unused_121_);
v___x_110_ = v___x_107_;
v_isShared_111_ = v_isSharedCheck_120_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_generationId_108_);
lean_dec(v___x_107_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_120_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_115_; 
v___x_112_ = lean_unsigned_to_nat(0u);
v___x_113_ = lean_nat_add(v_generationId_108_, v___x_99_);
lean_dec(v_generationId_108_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 1, v___x_113_);
lean_ctor_set(v___x_110_, 0, v___x_112_);
v___x_115_ = v___x_110_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_112_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v___x_113_);
v___x_115_ = v_reuseFailAlloc_119_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_116_ = lean_st_ref_put(v___y_89_, v___x_115_);
v___x_117_ = lean_io_condvar_notify_all(v_cvar_87_);
v___x_118_ = 1;
return v___x_118_;
}
}
}
else
{
lean_object* v_mutex_122_; lean_object* v___x_123_; lean_object* v___f_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v_mutex_122_ = lean_ctor_get(v_lock_88_, 1);
v___x_123_ = lean_box(v___x_106_);
v___f_124_ = lean_alloc_closure((void*)(l_Std_Barrier_wait___lam__0___boxed), 4, 2);
lean_closure_set(v___f_124_, 0, v_generationId_92_);
lean_closure_set(v___f_124_, 1, v___x_123_);
v___x_125_ = l_Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0(v_cvar_87_, v_mutex_122_, v___f_124_, v___y_89_);
v___x_126_ = 0;
return v___x_126_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Barrier_wait___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_numThreads_86_ = stack[0].m_obj;
lean_object* v_cvar_87_ = stack[1].m_obj;
lean_object* v_lock_88_ = stack[2].m_obj;
lean_object* v___y_89_ = stack[3].m_obj;
uint8_t v_res_129_;
v_res_129_ = l_Std_Barrier_wait___lam__1(v_numThreads_86_, v_cvar_87_, v_lock_88_, v___y_89_);
stack->m_num = v_res_129_;
}
LEAN_EXPORT lean_object* l_Std_Barrier_wait___lam__1___boxed(lean_object* v_numThreads_130_, lean_object* v_cvar_131_, lean_object* v_lock_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = l_Std_Barrier_wait___lam__1(v_numThreads_130_, v_cvar_131_, v_lock_132_, v___y_133_);
lean_dec(v___y_133_);
lean_dec_ref(v_lock_132_);
lean_dec(v_cvar_131_);
lean_dec(v_numThreads_130_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
uint8_t l_Std_Barrier_wait(lean_object* v_barrier_137_){
_start:
{
lean_object* v_lock_139_; lean_object* v_cvar_140_; lean_object* v_numThreads_141_; lean_object* v___f_142_; lean_object* v___x_143_; uint8_t v___x_144_; 
v_lock_139_ = lean_ctor_get(v_barrier_137_, 0);
lean_inc_ref_n(v_lock_139_, 2);
v_cvar_140_ = lean_ctor_get(v_barrier_137_, 1);
lean_inc(v_cvar_140_);
v_numThreads_141_ = lean_ctor_get(v_barrier_137_, 2);
lean_inc(v_numThreads_141_);
lean_dec_ref(v_barrier_137_);
v___f_142_ = lean_alloc_closure((void*)(l_Std_Barrier_wait___lam__1___boxed), 5, 3);
lean_closure_set(v___f_142_, 0, v_numThreads_141_);
lean_closure_set(v___f_142_, 1, v_cvar_140_);
lean_closure_set(v___f_142_, 2, v_lock_139_);
v___x_143_ = l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___redArg(v_lock_139_, v___f_142_);
v___x_144_ = lean_unbox(v___x_143_);
lean_dec(v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT void l_Std_Barrier_wait_0interp(lean_interpreter_value* stack)
{
lean_object* v_barrier_137_ = stack[0].m_obj;
uint8_t v_res_145_;
v_res_145_ = l_Std_Barrier_wait(v_barrier_137_);
stack->m_num = v_res_145_;
}
LEAN_EXPORT lean_object* l_Std_Barrier_wait___boxed(lean_object* v_barrier_146_, lean_object* v_a_147_){
_start:
{
uint8_t v_res_148_; lean_object* v_r_149_; 
v_res_148_ = l_Std_Barrier_wait(v_barrier_146_);
v_r_149_ = lean_box(v_res_148_);
return v_r_149_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0(lean_object* v_pred_150_, lean_object* v_condvar_151_, lean_object* v_mutex_152_, lean_object* v_inst_153_, lean_object* v_a_154_, lean_object* v___y_155_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l___private_Init_While_0__repeatM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg(v_pred_150_, v_condvar_151_, v_mutex_152_, v___y_155_);
return v___x_157_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pred_150_ = stack[0].m_obj;
lean_object* v_condvar_151_ = stack[1].m_obj;
lean_object* v_mutex_152_ = stack[2].m_obj;
lean_object* v_a_154_ = stack[4].m_obj;
lean_object* v___y_155_ = stack[5].m_obj;
lean_object* v_res_158_;
v_res_158_ = l___private_Init_While_0__repeatM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0(v_pred_150_, v_condvar_151_, v_mutex_152_, lean_box(0), v_a_154_, v___y_155_);
stack->m_obj
 = v_res_158_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___boxed(lean_object* v_pred_159_, lean_object* v_condvar_160_, lean_object* v_mutex_161_, lean_object* v_inst_162_, lean_object* v_a_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l___private_Init_While_0__repeatM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0(v_pred_159_, v_condvar_160_, v_mutex_161_, v_inst_162_, v_a_163_, v___y_164_);
lean_dec(v___y_164_);
lean_dec(v_mutex_161_);
lean_dec(v_condvar_160_);
return v_res_166_;
}
}
lean_object* runtime_initialize_Std_Sync_Mutex(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sync_Barrier(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
