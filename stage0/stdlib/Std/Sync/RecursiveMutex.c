// Lean compiler output
// Module: Std.Sync.RecursiveMutex
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
LEAN_EXPORT lean_object* l___private_Std_Sync_RecursiveMutex_0__Std_RecursiveMutexImpl;
lean_object* lean_io_baserecmutex_new();
LEAN_EXPORT lean_object* l_Std_BaseRecursiveMutex_new___boxed(lean_object*);
lean_object* lean_io_baserecmutex_lock(lean_object*);
LEAN_EXPORT lean_object* l_Std_BaseRecursiveMutex_lock___boxed(lean_object*, lean_object*);
uint8_t lean_io_baserecmutex_try_lock(lean_object*);
LEAN_EXPORT lean_object* l_Std_BaseRecursiveMutex_tryLock___boxed(lean_object*, lean_object*);
lean_object* lean_io_baserecmutex_unlock(lean_object*);
LEAN_EXPORT lean_object* l_Std_BaseRecursiveMutex_unlock___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg___closed__0 = (const lean_object*)&l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg();
LEAN_EXPORT lean_object* l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex(lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_new___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_new___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_new(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_new___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_RecursiveMutex_atomically___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_RecursiveMutex_atomically___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_RecursiveMutex_atomically___redArg___closed__0 = (const lean_object*)&l_Std_RecursiveMutex_atomically___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_RecursiveMutex_tryAtomically___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_RecursiveMutex_tryAtomically___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___closed__0 = (const lean_object*)&l_Std_RecursiveMutex_tryAtomically___redArg___closed__0_value;
static const lean_closure_object l_Std_RecursiveMutex_tryAtomically___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_RecursiveMutex_tryAtomically___redArg___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___closed__1 = (const lean_object*)&l_Std_RecursiveMutex_tryAtomically___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Std_Sync_RecursiveMutex_0__Std_RecursiveMutexImpl(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
LEAN_EXPORT void l_Std_BaseRecursiveMutex_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3_;
v_res_3_ = lean_io_baserecmutex_new();
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l_Std_BaseRecursiveMutex_new___boxed(lean_object* v_a_00___x40___internal___hyg_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lean_io_baserecmutex_new();
return v_res_5_;
}
}
LEAN_EXPORT void l_Std_BaseRecursiveMutex_lock_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_6_ = stack[0].m_obj;
lean_object* v_res_8_;
v_res_8_ = lean_io_baserecmutex_lock(v_mutex_6_);
stack->m_obj
 = v_res_8_;
}
LEAN_EXPORT lean_object* l_Std_BaseRecursiveMutex_lock___boxed(lean_object* v_mutex_9_, lean_object* v_a_00___x40___internal___hyg_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lean_io_baserecmutex_lock(v_mutex_9_);
lean_dec(v_mutex_9_);
return v_res_11_;
}
}
LEAN_EXPORT void l_Std_BaseRecursiveMutex_tryLock_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_12_ = stack[0].m_obj;
uint8_t v_res_14_;
v_res_14_ = lean_io_baserecmutex_try_lock(v_mutex_12_);
stack->m_num = v_res_14_;
}
LEAN_EXPORT lean_object* l_Std_BaseRecursiveMutex_tryLock___boxed(lean_object* v_mutex_15_, lean_object* v_a_00___x40___internal___hyg_16_){
_start:
{
uint8_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = lean_io_baserecmutex_try_lock(v_mutex_15_);
lean_dec(v_mutex_15_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT void l_Std_BaseRecursiveMutex_unlock_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_19_ = stack[0].m_obj;
lean_object* v_res_21_;
v_res_21_ = lean_io_baserecmutex_unlock(v_mutex_19_);
stack->m_obj
 = v_res_21_;
}
LEAN_EXPORT lean_object* l_Std_BaseRecursiveMutex_unlock___boxed(lean_object* v_mutex_22_, lean_object* v_a_00___x40___internal___hyg_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lean_io_baserecmutex_unlock(v_mutex_22_);
lean_dec(v_mutex_22_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg___lam__0(lean_object* v_self_25_){
_start:
{
lean_object* v_mutex_26_; 
v_mutex_26_ = lean_ctor_get(v_self_25_, 1);
lean_inc(v_mutex_26_);
return v_mutex_26_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg___lam__0___boxed(lean_object* v_self_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg___lam__0(v_self_27_);
lean_dec_ref(v_self_27_);
return v_res_28_;
}
}
lean_object* l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg(){
_start:
{
lean_object* v___f_31_; 
v___f_31_ = ((lean_object*)(l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg___closed__0));
return v___f_31_;
}
}
LEAN_EXPORT void l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_32_;
v_res_32_ = l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg();
stack->m_obj
 = v_res_32_;
}
LEAN_EXPORT lean_object* l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg___boxed(lean_object* v___dummy_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg();
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex(lean_object* v_00_u03b1_35_){
_start:
{
lean_object* v___f_36_; 
v___f_36_ = ((lean_object*)(l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___redArg___closed__0));
return v___f_36_;
}
}
lean_object* l_Std_RecursiveMutex_new___redArg(lean_object* v_a_37_){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_39_ = lean_st_mk_ref(v_a_37_);
v___x_40_ = lean_io_baserecmutex_new();
v___x_41_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_41_, 0, v___x_39_);
lean_ctor_set(v___x_41_, 1, v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT void l_Std_RecursiveMutex_new___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_37_ = stack[0].m_obj;
lean_object* v_res_42_;
v_res_42_ = l_Std_RecursiveMutex_new___redArg(v_a_37_);
stack->m_obj
 = v_res_42_;
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_new___redArg___boxed(lean_object* v_a_43_, lean_object* v_a_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Std_RecursiveMutex_new___redArg(v_a_43_);
return v_res_45_;
}
}
lean_object* l_Std_RecursiveMutex_new(lean_object* v_00_u03b1_46_, lean_object* v_a_47_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Std_RecursiveMutex_new___redArg(v_a_47_);
return v___x_49_;
}
}
LEAN_EXPORT void l_Std_RecursiveMutex_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_47_ = stack[1].m_obj;
lean_object* v_res_50_;
v_res_50_ = l_Std_RecursiveMutex_new(lean_box(0), v_a_47_);
stack->m_obj
 = v_res_50_;
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_new___boxed(lean_object* v_00_u03b1_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Std_RecursiveMutex_new(v_00_u03b1_51_, v_a_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg___lam__0(lean_object* v_k_55_, lean_object* v_ref_56_, lean_object* v_____r_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lean_apply_1(v_k_55_, v_ref_56_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg___lam__1(lean_object* v_x_59_){
_start:
{
lean_object* v_fst_60_; 
v_fst_60_ = lean_ctor_get(v_x_59_, 0);
lean_inc(v_fst_60_);
return v_fst_60_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg___lam__1___boxed(lean_object* v_x_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Std_RecursiveMutex_atomically___redArg___lam__1(v_x_61_);
lean_dec_ref(v_x_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg___lam__2(lean_object* v___x_63_, lean_object* v_x_64_){
_start:
{
lean_inc(v___x_63_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg___lam__2___boxed(lean_object* v___x_65_, lean_object* v_x_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Std_RecursiveMutex_atomically___redArg___lam__2(v___x_65_, v_x_66_);
lean_dec(v_x_66_);
lean_dec(v___x_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically___redArg(lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_mutex_72_, lean_object* v_k_73_){
_start:
{
lean_object* v_toApplicative_74_; lean_object* v_toFunctor_75_; lean_object* v_toBind_76_; lean_object* v_ref_77_; lean_object* v_mutex_78_; lean_object* v_map_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___f_82_; lean_object* v___f_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___f_87_; lean_object* v_y_88_; lean_object* v___x_89_; 
v_toApplicative_74_ = lean_ctor_get(v_inst_69_, 0);
v_toFunctor_75_ = lean_ctor_get(v_toApplicative_74_, 0);
lean_inc_ref(v_toFunctor_75_);
v_toBind_76_ = lean_ctor_get(v_inst_69_, 1);
lean_inc(v_toBind_76_);
lean_dec_ref(v_inst_69_);
v_ref_77_ = lean_ctor_get(v_mutex_72_, 0);
lean_inc(v_ref_77_);
v_mutex_78_ = lean_ctor_get(v_mutex_72_, 1);
lean_inc_n(v_mutex_78_, 2);
lean_dec_ref(v_mutex_72_);
v_map_79_ = lean_ctor_get(v_toFunctor_75_, 0);
lean_inc(v_map_79_);
lean_dec_ref(v_toFunctor_75_);
v___x_80_ = lean_alloc_closure((void*)(l_Std_BaseRecursiveMutex_lock___boxed), 2, 1);
lean_closure_set(v___x_80_, 0, v_mutex_78_);
lean_inc(v_inst_70_);
v___x_81_ = lean_apply_2(v_inst_70_, lean_box(0), v___x_80_);
v___f_82_ = lean_alloc_closure((void*)(l_Std_RecursiveMutex_atomically___redArg___lam__0), 3, 2);
lean_closure_set(v___f_82_, 0, v_k_73_);
lean_closure_set(v___f_82_, 1, v_ref_77_);
v___f_83_ = ((lean_object*)(l_Std_RecursiveMutex_atomically___redArg___closed__0));
v___x_84_ = lean_apply_4(v_toBind_76_, lean_box(0), lean_box(0), v___x_81_, v___f_82_);
v___x_85_ = lean_alloc_closure((void*)(l_Std_BaseRecursiveMutex_unlock___boxed), 2, 1);
lean_closure_set(v___x_85_, 0, v_mutex_78_);
v___x_86_ = lean_apply_2(v_inst_70_, lean_box(0), v___x_85_);
v___f_87_ = lean_alloc_closure((void*)(l_Std_RecursiveMutex_atomically___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_87_, 0, v___x_86_);
v_y_88_ = lean_apply_4(v_inst_71_, lean_box(0), lean_box(0), v___x_84_, v___f_87_);
v___x_89_ = lean_apply_4(v_map_79_, lean_box(0), lean_box(0), v___f_83_, v_y_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_atomically(lean_object* v_m_90_, lean_object* v_00_u03b1_91_, lean_object* v_00_u03b2_92_, lean_object* v_inst_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_mutex_96_, lean_object* v_k_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Std_RecursiveMutex_atomically___redArg(v_inst_93_, v_inst_94_, v_inst_95_, v_mutex_96_, v_k_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__0(lean_object* v_x_99_){
_start:
{
lean_object* v_fst_100_; 
v_fst_100_ = lean_ctor_get(v_x_99_, 0);
lean_inc(v_fst_100_);
return v_fst_100_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__0___boxed(lean_object* v_x_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Std_RecursiveMutex_tryAtomically___redArg___lam__0(v_x_101_);
lean_dec_ref(v_x_101_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__1(lean_object* v_val_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_104_, 0, v_val_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__2(lean_object* v___x_105_, lean_object* v_x_106_){
_start:
{
lean_inc(v___x_105_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__2___boxed(lean_object* v___x_107_, lean_object* v_x_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Std_RecursiveMutex_tryAtomically___redArg___lam__2(v___x_107_, v_x_108_);
lean_dec(v_x_108_);
lean_dec(v___x_107_);
return v_res_109_;
}
}
lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__3(lean_object* v_toPure_110_, lean_object* v_toFunctor_111_, lean_object* v_k_112_, lean_object* v_ref_113_, lean_object* v___f_114_, lean_object* v_mutex_115_, lean_object* v_inst_116_, lean_object* v_inst_117_, lean_object* v___f_118_, uint8_t v_____do__lift_119_){
_start:
{
if (v_____do__lift_119_ == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; 
lean_dec_ref(v___f_118_);
lean_dec(v_inst_117_);
lean_dec(v_inst_116_);
lean_dec(v_mutex_115_);
lean_dec_ref(v___f_114_);
lean_dec(v_ref_113_);
lean_dec(v_k_112_);
lean_dec_ref(v_toFunctor_111_);
v___x_120_ = lean_box(0);
v___x_121_ = lean_apply_2(v_toPure_110_, lean_box(0), v___x_120_);
return v___x_121_;
}
else
{
lean_object* v_map_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___f_127_; lean_object* v_y_128_; lean_object* v___x_129_; 
lean_dec(v_toPure_110_);
v_map_122_ = lean_ctor_get(v_toFunctor_111_, 0);
lean_inc_n(v_map_122_, 2);
lean_dec_ref(v_toFunctor_111_);
v___x_123_ = lean_apply_1(v_k_112_, v_ref_113_);
v___x_124_ = lean_apply_4(v_map_122_, lean_box(0), lean_box(0), v___f_114_, v___x_123_);
v___x_125_ = lean_alloc_closure((void*)(l_Std_BaseRecursiveMutex_unlock___boxed), 2, 1);
lean_closure_set(v___x_125_, 0, v_mutex_115_);
v___x_126_ = lean_apply_2(v_inst_116_, lean_box(0), v___x_125_);
v___f_127_ = lean_alloc_closure((void*)(l_Std_RecursiveMutex_tryAtomically___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_127_, 0, v___x_126_);
v_y_128_ = lean_apply_4(v_inst_117_, lean_box(0), lean_box(0), v___x_124_, v___f_127_);
v___x_129_ = lean_apply_4(v_map_122_, lean_box(0), lean_box(0), v___f_118_, v_y_128_);
return v___x_129_;
}
}
}
LEAN_EXPORT void l_Std_RecursiveMutex_tryAtomically___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_110_ = stack[0].m_obj;
lean_object* v_toFunctor_111_ = stack[1].m_obj;
lean_object* v_k_112_ = stack[2].m_obj;
lean_object* v_ref_113_ = stack[3].m_obj;
lean_object* v___f_114_ = stack[4].m_obj;
lean_object* v_mutex_115_ = stack[5].m_obj;
lean_object* v_inst_116_ = stack[6].m_obj;
lean_object* v_inst_117_ = stack[7].m_obj;
lean_object* v___f_118_ = stack[8].m_obj;
uint8_t v_____do__lift_119_ = stack[9].m_num;
lean_object* v_res_130_;
v_res_130_ = l_Std_RecursiveMutex_tryAtomically___redArg___lam__3(v_toPure_110_, v_toFunctor_111_, v_k_112_, v_ref_113_, v___f_114_, v_mutex_115_, v_inst_116_, v_inst_117_, v___f_118_, v_____do__lift_119_);
stack->m_obj
 = v_res_130_;
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg___lam__3___boxed(lean_object* v_toPure_131_, lean_object* v_toFunctor_132_, lean_object* v_k_133_, lean_object* v_ref_134_, lean_object* v___f_135_, lean_object* v_mutex_136_, lean_object* v_inst_137_, lean_object* v_inst_138_, lean_object* v___f_139_, lean_object* v_____do__lift_140_){
_start:
{
uint8_t v_____do__lift_92__boxed_141_; lean_object* v_res_142_; 
v_____do__lift_92__boxed_141_ = lean_unbox(v_____do__lift_140_);
v_res_142_ = l_Std_RecursiveMutex_tryAtomically___redArg___lam__3(v_toPure_131_, v_toFunctor_132_, v_k_133_, v_ref_134_, v___f_135_, v_mutex_136_, v_inst_137_, v_inst_138_, v___f_139_, v_____do__lift_92__boxed_141_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically___redArg(lean_object* v_inst_145_, lean_object* v_inst_146_, lean_object* v_inst_147_, lean_object* v_mutex_148_, lean_object* v_k_149_){
_start:
{
lean_object* v_toApplicative_150_; lean_object* v_toBind_151_; lean_object* v_ref_152_; lean_object* v_mutex_153_; lean_object* v_toFunctor_154_; lean_object* v_toPure_155_; lean_object* v___f_156_; lean_object* v___f_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___f_160_; lean_object* v___x_161_; 
v_toApplicative_150_ = lean_ctor_get(v_inst_145_, 0);
lean_inc_ref(v_toApplicative_150_);
v_toBind_151_ = lean_ctor_get(v_inst_145_, 1);
lean_inc(v_toBind_151_);
lean_dec_ref(v_inst_145_);
v_ref_152_ = lean_ctor_get(v_mutex_148_, 0);
lean_inc(v_ref_152_);
v_mutex_153_ = lean_ctor_get(v_mutex_148_, 1);
lean_inc_n(v_mutex_153_, 2);
lean_dec_ref(v_mutex_148_);
v_toFunctor_154_ = lean_ctor_get(v_toApplicative_150_, 0);
lean_inc_ref(v_toFunctor_154_);
v_toPure_155_ = lean_ctor_get(v_toApplicative_150_, 1);
lean_inc(v_toPure_155_);
lean_dec_ref(v_toApplicative_150_);
v___f_156_ = ((lean_object*)(l_Std_RecursiveMutex_tryAtomically___redArg___closed__0));
v___f_157_ = ((lean_object*)(l_Std_RecursiveMutex_tryAtomically___redArg___closed__1));
v___x_158_ = lean_alloc_closure((void*)(l_Std_BaseRecursiveMutex_tryLock___boxed), 2, 1);
lean_closure_set(v___x_158_, 0, v_mutex_153_);
lean_inc(v_inst_146_);
v___x_159_ = lean_apply_2(v_inst_146_, lean_box(0), v___x_158_);
v___f_160_ = lean_alloc_closure((void*)(l_Std_RecursiveMutex_tryAtomically___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_160_, 0, v_toPure_155_);
lean_closure_set(v___f_160_, 1, v_toFunctor_154_);
lean_closure_set(v___f_160_, 2, v_k_149_);
lean_closure_set(v___f_160_, 3, v_ref_152_);
lean_closure_set(v___f_160_, 4, v___f_157_);
lean_closure_set(v___f_160_, 5, v_mutex_153_);
lean_closure_set(v___f_160_, 6, v_inst_146_);
lean_closure_set(v___f_160_, 7, v_inst_147_);
lean_closure_set(v___f_160_, 8, v___f_156_);
v___x_161_ = lean_apply_4(v_toBind_151_, lean_box(0), lean_box(0), v___x_159_, v___f_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Std_RecursiveMutex_tryAtomically(lean_object* v_m_162_, lean_object* v_00_u03b1_163_, lean_object* v_00_u03b2_164_, lean_object* v_inst_165_, lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_mutex_168_, lean_object* v_k_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Std_RecursiveMutex_tryAtomically___redArg(v_inst_165_, v_inst_166_, v_inst_167_, v_mutex_168_, v_k_169_);
return v___x_170_;
}
}
lean_object* runtime_initialize_Std_Sync_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sync_RecursiveMutex(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Sync_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Std_Sync_RecursiveMutex_0__Std_RecursiveMutexImpl = _init_l___private_Std_Sync_RecursiveMutex_0__Std_RecursiveMutexImpl();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sync_RecursiveMutex(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sync_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sync_RecursiveMutex(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sync_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sync_RecursiveMutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sync_RecursiveMutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sync_RecursiveMutex(builtin);
}
#ifdef __cplusplus
}
#endif
