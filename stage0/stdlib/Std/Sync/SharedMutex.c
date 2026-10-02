// Lean compiler output
// Module: Std.Sync.SharedMutex
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
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_SharedMutex_0__Std_SharedMutexImpl;
lean_object* lean_io_basesharedmutex_new();
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_new___boxed(lean_object*);
lean_object* lean_io_basesharedmutex_write(lean_object*);
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_write___boxed(lean_object*, lean_object*);
uint8_t lean_io_basesharedmutex_try_write(lean_object*);
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_tryWrite___boxed(lean_object*, lean_object*);
lean_object* lean_io_basesharedmutex_unlock_write(lean_object*);
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_unlockWrite___boxed(lean_object*, lean_object*);
lean_object* lean_io_basesharedmutex_read(lean_object*);
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_read___boxed(lean_object*, lean_object*);
uint8_t lean_io_basesharedmutex_try_read(lean_object*);
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_tryRead___boxed(lean_object*, lean_object*);
lean_object* lean_io_basesharedmutex_unlock_read(lean_object*);
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_unlockRead___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instCoeOutSharedMutexBaseSharedMutex___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_instCoeOutSharedMutexBaseSharedMutex___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_instCoeOutSharedMutexBaseSharedMutex___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instCoeOutSharedMutexBaseSharedMutex___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instCoeOutSharedMutexBaseSharedMutex___redArg___closed__0 = (const lean_object*)&l_Std_instCoeOutSharedMutexBaseSharedMutex___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instCoeOutSharedMutexBaseSharedMutex___redArg();
LEAN_EXPORT lean_object* l_Std_instCoeOutSharedMutexBaseSharedMutex___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_instCoeOutSharedMutexBaseSharedMutex(lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_new___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_new___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_new(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_new___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_SharedMutex_atomically___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_SharedMutex_atomically___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_SharedMutex_atomically___redArg___closed__0 = (const lean_object*)&l_Std_SharedMutex_atomically___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_SharedMutex_tryAtomically___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_SharedMutex_tryAtomically___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_SharedMutex_tryAtomically___redArg___closed__0 = (const lean_object*)&l_Std_SharedMutex_tryAtomically___redArg___closed__0_value;
static const lean_closure_object l_Std_SharedMutex_tryAtomically___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_SharedMutex_tryAtomically___redArg___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_SharedMutex_tryAtomically___redArg___closed__1 = (const lean_object*)&l_Std_SharedMutex_tryAtomically___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomicallyRead___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomicallyRead___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomicallyRead___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomicallyRead___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomicallyRead___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomicallyRead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomicallyRead___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomicallyRead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Std_Sync_SharedMutex_0__Std_SharedMutexImpl(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_new___boxed(lean_object* v_a_00___x40___internal___hyg_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lean_io_basesharedmutex_new();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_write___boxed(lean_object* v_mutex_7_, lean_object* v_a_00___x40___internal___hyg_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lean_io_basesharedmutex_write(v_mutex_7_);
lean_dec(v_mutex_7_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_tryWrite___boxed(lean_object* v_mutex_12_, lean_object* v_a_00___x40___internal___hyg_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = lean_io_basesharedmutex_try_write(v_mutex_12_);
lean_dec(v_mutex_12_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_unlockWrite___boxed(lean_object* v_mutex_18_, lean_object* v_a_00___x40___internal___hyg_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lean_io_basesharedmutex_unlock_write(v_mutex_18_);
lean_dec(v_mutex_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_read___boxed(lean_object* v_mutex_23_, lean_object* v_a_00___x40___internal___hyg_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lean_io_basesharedmutex_read(v_mutex_23_);
lean_dec(v_mutex_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_tryRead___boxed(lean_object* v_mutex_28_, lean_object* v_a_00___x40___internal___hyg_29_){
_start:
{
uint8_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = lean_io_basesharedmutex_try_read(v_mutex_28_);
lean_dec(v_mutex_28_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_unlockRead___boxed(lean_object* v_mutex_34_, lean_object* v_a_00___x40___internal___hyg_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lean_io_basesharedmutex_unlock_read(v_mutex_34_);
lean_dec(v_mutex_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutSharedMutexBaseSharedMutex___redArg___lam__0(lean_object* v_self_37_){
_start:
{
lean_object* v_mutex_38_; 
v_mutex_38_ = lean_ctor_get(v_self_37_, 1);
lean_inc(v_mutex_38_);
return v_mutex_38_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutSharedMutexBaseSharedMutex___redArg___lam__0___boxed(lean_object* v_self_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Std_instCoeOutSharedMutexBaseSharedMutex___redArg___lam__0(v_self_39_);
lean_dec_ref(v_self_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutSharedMutexBaseSharedMutex___redArg(){
_start:
{
lean_object* v___f_43_; 
v___f_43_ = ((lean_object*)(l_Std_instCoeOutSharedMutexBaseSharedMutex___redArg___closed__0));
return v___f_43_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutSharedMutexBaseSharedMutex___redArg___boxed(lean_object* v___dummy_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Std_instCoeOutSharedMutexBaseSharedMutex___redArg();
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutSharedMutexBaseSharedMutex(lean_object* v_00_u03b1_46_){
_start:
{
lean_object* v___f_47_; 
v___f_47_ = ((lean_object*)(l_Std_instCoeOutSharedMutexBaseSharedMutex___redArg___closed__0));
return v___f_47_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_new___redArg(lean_object* v_a_48_){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = lean_st_mk_ref(v_a_48_);
v___x_51_ = lean_io_basesharedmutex_new();
v___x_52_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_50_);
lean_ctor_set(v___x_52_, 1, v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_new___redArg___boxed(lean_object* v_a_53_, lean_object* v_a_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Std_SharedMutex_new___redArg(v_a_53_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_new(lean_object* v_00_u03b1_56_, lean_object* v_a_57_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Std_SharedMutex_new___redArg(v_a_57_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_new___boxed(lean_object* v_00_u03b1_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Std_SharedMutex_new(v_00_u03b1_60_, v_a_61_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg___lam__0(lean_object* v_k_64_, lean_object* v_ref_65_, lean_object* v_____r_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lean_apply_1(v_k_64_, v_ref_65_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg___lam__1(lean_object* v_x_68_){
_start:
{
lean_object* v_fst_69_; 
v_fst_69_ = lean_ctor_get(v_x_68_, 0);
lean_inc(v_fst_69_);
return v_fst_69_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg___lam__1___boxed(lean_object* v_x_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Std_SharedMutex_atomically___redArg___lam__1(v_x_70_);
lean_dec_ref(v_x_70_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg___lam__2(lean_object* v___x_72_, lean_object* v_x_73_){
_start:
{
lean_inc(v___x_72_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg___lam__2___boxed(lean_object* v___x_74_, lean_object* v_x_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Std_SharedMutex_atomically___redArg___lam__2(v___x_74_, v_x_75_);
lean_dec(v_x_75_);
lean_dec(v___x_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg(lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_inst_80_, lean_object* v_mutex_81_, lean_object* v_k_82_){
_start:
{
lean_object* v_toApplicative_83_; lean_object* v_toFunctor_84_; lean_object* v_toBind_85_; lean_object* v_ref_86_; lean_object* v_mutex_87_; lean_object* v_map_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___f_91_; lean_object* v___f_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___f_96_; lean_object* v_y_97_; lean_object* v___x_98_; 
v_toApplicative_83_ = lean_ctor_get(v_inst_78_, 0);
v_toFunctor_84_ = lean_ctor_get(v_toApplicative_83_, 0);
lean_inc_ref(v_toFunctor_84_);
v_toBind_85_ = lean_ctor_get(v_inst_78_, 1);
lean_inc(v_toBind_85_);
lean_dec_ref(v_inst_78_);
v_ref_86_ = lean_ctor_get(v_mutex_81_, 0);
lean_inc(v_ref_86_);
v_mutex_87_ = lean_ctor_get(v_mutex_81_, 1);
lean_inc_n(v_mutex_87_, 2);
lean_dec_ref(v_mutex_81_);
v_map_88_ = lean_ctor_get(v_toFunctor_84_, 0);
lean_inc(v_map_88_);
lean_dec_ref(v_toFunctor_84_);
v___x_89_ = lean_alloc_closure((void*)(l_Std_BaseSharedMutex_write___boxed), 2, 1);
lean_closure_set(v___x_89_, 0, v_mutex_87_);
lean_inc(v_inst_79_);
v___x_90_ = lean_apply_2(v_inst_79_, lean_box(0), v___x_89_);
v___f_91_ = lean_alloc_closure((void*)(l_Std_SharedMutex_atomically___redArg___lam__0), 3, 2);
lean_closure_set(v___f_91_, 0, v_k_82_);
lean_closure_set(v___f_91_, 1, v_ref_86_);
v___f_92_ = ((lean_object*)(l_Std_SharedMutex_atomically___redArg___closed__0));
v___x_93_ = lean_apply_4(v_toBind_85_, lean_box(0), lean_box(0), v___x_90_, v___f_91_);
v___x_94_ = lean_alloc_closure((void*)(l_Std_BaseSharedMutex_unlockWrite___boxed), 2, 1);
lean_closure_set(v___x_94_, 0, v_mutex_87_);
v___x_95_ = lean_apply_2(v_inst_79_, lean_box(0), v___x_94_);
v___f_96_ = lean_alloc_closure((void*)(l_Std_SharedMutex_atomically___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_96_, 0, v___x_95_);
v_y_97_ = lean_apply_4(v_inst_80_, lean_box(0), lean_box(0), v___x_93_, v___f_96_);
v___x_98_ = lean_apply_4(v_map_88_, lean_box(0), lean_box(0), v___f_92_, v_y_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically(lean_object* v_m_99_, lean_object* v_00_u03b1_100_, lean_object* v_00_u03b2_101_, lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v_mutex_105_, lean_object* v_k_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Std_SharedMutex_atomically___redArg(v_inst_102_, v_inst_103_, v_inst_104_, v_mutex_105_, v_k_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__0(lean_object* v_x_108_){
_start:
{
lean_object* v_fst_109_; 
v_fst_109_ = lean_ctor_get(v_x_108_, 0);
lean_inc(v_fst_109_);
return v_fst_109_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__0___boxed(lean_object* v_x_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Std_SharedMutex_tryAtomically___redArg___lam__0(v_x_110_);
lean_dec_ref(v_x_110_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__1(lean_object* v_val_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_113_, 0, v_val_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__2(lean_object* v___x_114_, lean_object* v_x_115_){
_start:
{
lean_inc(v___x_114_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__2___boxed(lean_object* v___x_116_, lean_object* v_x_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Std_SharedMutex_tryAtomically___redArg___lam__2(v___x_116_, v_x_117_);
lean_dec(v_x_117_);
lean_dec(v___x_116_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__3(lean_object* v_toPure_119_, lean_object* v_toFunctor_120_, lean_object* v_k_121_, lean_object* v_ref_122_, lean_object* v___f_123_, lean_object* v_mutex_124_, lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v___f_127_, uint8_t v_____do__lift_128_){
_start:
{
if (v_____do__lift_128_ == 0)
{
lean_object* v___x_129_; lean_object* v___x_130_; 
lean_dec_ref(v___f_127_);
lean_dec(v_inst_126_);
lean_dec(v_inst_125_);
lean_dec(v_mutex_124_);
lean_dec_ref(v___f_123_);
lean_dec(v_ref_122_);
lean_dec(v_k_121_);
lean_dec_ref(v_toFunctor_120_);
v___x_129_ = lean_box(0);
v___x_130_ = lean_apply_2(v_toPure_119_, lean_box(0), v___x_129_);
return v___x_130_;
}
else
{
lean_object* v_map_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___f_136_; lean_object* v_y_137_; lean_object* v___x_138_; 
lean_dec(v_toPure_119_);
v_map_131_ = lean_ctor_get(v_toFunctor_120_, 0);
lean_inc_n(v_map_131_, 2);
lean_dec_ref(v_toFunctor_120_);
v___x_132_ = lean_apply_1(v_k_121_, v_ref_122_);
v___x_133_ = lean_apply_4(v_map_131_, lean_box(0), lean_box(0), v___f_123_, v___x_132_);
v___x_134_ = lean_alloc_closure((void*)(l_Std_BaseSharedMutex_unlockWrite___boxed), 2, 1);
lean_closure_set(v___x_134_, 0, v_mutex_124_);
v___x_135_ = lean_apply_2(v_inst_125_, lean_box(0), v___x_134_);
v___f_136_ = lean_alloc_closure((void*)(l_Std_SharedMutex_tryAtomically___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_136_, 0, v___x_135_);
v_y_137_ = lean_apply_4(v_inst_126_, lean_box(0), lean_box(0), v___x_133_, v___f_136_);
v___x_138_ = lean_apply_4(v_map_131_, lean_box(0), lean_box(0), v___f_127_, v_y_137_);
return v___x_138_;
}
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__3___boxed(lean_object* v_toPure_139_, lean_object* v_toFunctor_140_, lean_object* v_k_141_, lean_object* v_ref_142_, lean_object* v___f_143_, lean_object* v_mutex_144_, lean_object* v_inst_145_, lean_object* v_inst_146_, lean_object* v___f_147_, lean_object* v_____do__lift_148_){
_start:
{
uint8_t v_____do__lift_85__boxed_149_; lean_object* v_res_150_; 
v_____do__lift_85__boxed_149_ = lean_unbox(v_____do__lift_148_);
v_res_150_ = l_Std_SharedMutex_tryAtomically___redArg___lam__3(v_toPure_139_, v_toFunctor_140_, v_k_141_, v_ref_142_, v___f_143_, v_mutex_144_, v_inst_145_, v_inst_146_, v___f_147_, v_____do__lift_85__boxed_149_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg(lean_object* v_inst_153_, lean_object* v_inst_154_, lean_object* v_inst_155_, lean_object* v_mutex_156_, lean_object* v_k_157_){
_start:
{
lean_object* v_toApplicative_158_; lean_object* v_toBind_159_; lean_object* v_ref_160_; lean_object* v_mutex_161_; lean_object* v_toFunctor_162_; lean_object* v_toPure_163_; lean_object* v___f_164_; lean_object* v___f_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___f_168_; lean_object* v___x_169_; 
v_toApplicative_158_ = lean_ctor_get(v_inst_153_, 0);
lean_inc_ref(v_toApplicative_158_);
v_toBind_159_ = lean_ctor_get(v_inst_153_, 1);
lean_inc(v_toBind_159_);
lean_dec_ref(v_inst_153_);
v_ref_160_ = lean_ctor_get(v_mutex_156_, 0);
lean_inc(v_ref_160_);
v_mutex_161_ = lean_ctor_get(v_mutex_156_, 1);
lean_inc_n(v_mutex_161_, 2);
lean_dec_ref(v_mutex_156_);
v_toFunctor_162_ = lean_ctor_get(v_toApplicative_158_, 0);
lean_inc_ref(v_toFunctor_162_);
v_toPure_163_ = lean_ctor_get(v_toApplicative_158_, 1);
lean_inc(v_toPure_163_);
lean_dec_ref(v_toApplicative_158_);
v___f_164_ = ((lean_object*)(l_Std_SharedMutex_tryAtomically___redArg___closed__0));
v___f_165_ = ((lean_object*)(l_Std_SharedMutex_tryAtomically___redArg___closed__1));
v___x_166_ = lean_alloc_closure((void*)(l_Std_BaseSharedMutex_tryWrite___boxed), 2, 1);
lean_closure_set(v___x_166_, 0, v_mutex_161_);
lean_inc(v_inst_154_);
v___x_167_ = lean_apply_2(v_inst_154_, lean_box(0), v___x_166_);
v___f_168_ = lean_alloc_closure((void*)(l_Std_SharedMutex_tryAtomically___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_168_, 0, v_toPure_163_);
lean_closure_set(v___f_168_, 1, v_toFunctor_162_);
lean_closure_set(v___f_168_, 2, v_k_157_);
lean_closure_set(v___f_168_, 3, v_ref_160_);
lean_closure_set(v___f_168_, 4, v___f_165_);
lean_closure_set(v___f_168_, 5, v_mutex_161_);
lean_closure_set(v___f_168_, 6, v_inst_154_);
lean_closure_set(v___f_168_, 7, v_inst_155_);
lean_closure_set(v___f_168_, 8, v___f_164_);
v___x_169_ = lean_apply_4(v_toBind_159_, lean_box(0), lean_box(0), v___x_167_, v___f_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically(lean_object* v_m_170_, lean_object* v_00_u03b1_171_, lean_object* v_00_u03b2_172_, lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_inst_175_, lean_object* v_mutex_176_, lean_object* v_k_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Std_SharedMutex_tryAtomically___redArg(v_inst_173_, v_inst_174_, v_inst_175_, v_mutex_176_, v_k_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomicallyRead___redArg___lam__0(lean_object* v_k_179_, lean_object* v_state_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = lean_apply_1(v_k_179_, v_state_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomicallyRead___redArg___lam__2(lean_object* v_ref_182_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = lean_st_ref_get(v_ref_182_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomicallyRead___redArg___lam__2___boxed(lean_object* v_ref_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Std_SharedMutex_atomicallyRead___redArg___lam__2(v_ref_185_);
lean_dec(v_ref_185_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomicallyRead___redArg___lam__1(lean_object* v_ref_188_, lean_object* v_inst_189_, lean_object* v_toBind_190_, lean_object* v___f_191_, lean_object* v_____r_192_){
_start:
{
lean_object* v___f_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___f_193_ = lean_alloc_closure((void*)(l_Std_SharedMutex_atomicallyRead___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_193_, 0, v_ref_188_);
v___x_194_ = lean_apply_2(v_inst_189_, lean_box(0), v___f_193_);
v___x_195_ = lean_apply_4(v_toBind_190_, lean_box(0), lean_box(0), v___x_194_, v___f_191_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomicallyRead___redArg(lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_mutex_199_, lean_object* v_k_200_){
_start:
{
lean_object* v_toApplicative_201_; lean_object* v_toFunctor_202_; lean_object* v_toBind_203_; lean_object* v_ref_204_; lean_object* v_mutex_205_; lean_object* v_map_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___f_209_; lean_object* v___f_210_; lean_object* v___f_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___f_215_; lean_object* v_y_216_; lean_object* v___x_217_; 
v_toApplicative_201_ = lean_ctor_get(v_inst_196_, 0);
v_toFunctor_202_ = lean_ctor_get(v_toApplicative_201_, 0);
lean_inc_ref(v_toFunctor_202_);
v_toBind_203_ = lean_ctor_get(v_inst_196_, 1);
lean_inc_n(v_toBind_203_, 2);
lean_dec_ref(v_inst_196_);
v_ref_204_ = lean_ctor_get(v_mutex_199_, 0);
lean_inc(v_ref_204_);
v_mutex_205_ = lean_ctor_get(v_mutex_199_, 1);
lean_inc_n(v_mutex_205_, 2);
lean_dec_ref(v_mutex_199_);
v_map_206_ = lean_ctor_get(v_toFunctor_202_, 0);
lean_inc(v_map_206_);
lean_dec_ref(v_toFunctor_202_);
v___x_207_ = lean_alloc_closure((void*)(l_Std_BaseSharedMutex_read___boxed), 2, 1);
lean_closure_set(v___x_207_, 0, v_mutex_205_);
lean_inc_n(v_inst_197_, 2);
v___x_208_ = lean_apply_2(v_inst_197_, lean_box(0), v___x_207_);
v___f_209_ = lean_alloc_closure((void*)(l_Std_SharedMutex_atomicallyRead___redArg___lam__0), 2, 1);
lean_closure_set(v___f_209_, 0, v_k_200_);
v___f_210_ = ((lean_object*)(l_Std_SharedMutex_atomically___redArg___closed__0));
v___f_211_ = lean_alloc_closure((void*)(l_Std_SharedMutex_atomicallyRead___redArg___lam__1), 5, 4);
lean_closure_set(v___f_211_, 0, v_ref_204_);
lean_closure_set(v___f_211_, 1, v_inst_197_);
lean_closure_set(v___f_211_, 2, v_toBind_203_);
lean_closure_set(v___f_211_, 3, v___f_209_);
v___x_212_ = lean_apply_4(v_toBind_203_, lean_box(0), lean_box(0), v___x_208_, v___f_211_);
v___x_213_ = lean_alloc_closure((void*)(l_Std_BaseSharedMutex_unlockRead___boxed), 2, 1);
lean_closure_set(v___x_213_, 0, v_mutex_205_);
v___x_214_ = lean_apply_2(v_inst_197_, lean_box(0), v___x_213_);
v___f_215_ = lean_alloc_closure((void*)(l_Std_SharedMutex_atomically___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_215_, 0, v___x_214_);
v_y_216_ = lean_apply_4(v_inst_198_, lean_box(0), lean_box(0), v___x_212_, v___f_215_);
v___x_217_ = lean_apply_4(v_map_206_, lean_box(0), lean_box(0), v___f_210_, v_y_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomicallyRead(lean_object* v_m_218_, lean_object* v_00_u03b1_219_, lean_object* v_00_u03b2_220_, lean_object* v_inst_221_, lean_object* v_inst_222_, lean_object* v_inst_223_, lean_object* v_mutex_224_, lean_object* v_k_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Std_SharedMutex_atomicallyRead___redArg(v_inst_221_, v_inst_222_, v_inst_223_, v_mutex_224_, v_k_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__3(lean_object* v_toFunctor_227_, lean_object* v_k_228_, lean_object* v___f_229_, lean_object* v_state_230_){
_start:
{
lean_object* v_map_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v_map_231_ = lean_ctor_get(v_toFunctor_227_, 0);
lean_inc(v_map_231_);
lean_dec_ref(v_toFunctor_227_);
v___x_232_ = lean_apply_1(v_k_228_, v_state_230_);
v___x_233_ = lean_apply_4(v_map_231_, lean_box(0), lean_box(0), v___f_229_, v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__1(lean_object* v_toPure_234_, lean_object* v_toFunctor_235_, lean_object* v_inst_236_, lean_object* v___f_237_, lean_object* v_toBind_238_, lean_object* v___f_239_, lean_object* v_mutex_240_, lean_object* v_inst_241_, lean_object* v___f_242_, uint8_t v_____do__lift_243_){
_start:
{
if (v_____do__lift_243_ == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec_ref(v___f_242_);
lean_dec(v_inst_241_);
lean_dec(v_mutex_240_);
lean_dec(v___f_239_);
lean_dec(v_toBind_238_);
lean_dec_ref(v___f_237_);
lean_dec(v_inst_236_);
lean_dec_ref(v_toFunctor_235_);
v___x_244_ = lean_box(0);
v___x_245_ = lean_apply_2(v_toPure_234_, lean_box(0), v___x_244_);
return v___x_245_;
}
else
{
lean_object* v_map_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___f_251_; lean_object* v_y_252_; lean_object* v___x_253_; 
lean_dec(v_toPure_234_);
v_map_246_ = lean_ctor_get(v_toFunctor_235_, 0);
lean_inc(v_map_246_);
lean_dec_ref(v_toFunctor_235_);
lean_inc(v_inst_236_);
v___x_247_ = lean_apply_2(v_inst_236_, lean_box(0), v___f_237_);
v___x_248_ = lean_apply_4(v_toBind_238_, lean_box(0), lean_box(0), v___x_247_, v___f_239_);
v___x_249_ = lean_alloc_closure((void*)(l_Std_BaseSharedMutex_unlockRead___boxed), 2, 1);
lean_closure_set(v___x_249_, 0, v_mutex_240_);
v___x_250_ = lean_apply_2(v_inst_236_, lean_box(0), v___x_249_);
v___f_251_ = lean_alloc_closure((void*)(l_Std_SharedMutex_tryAtomically___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_251_, 0, v___x_250_);
v_y_252_ = lean_apply_4(v_inst_241_, lean_box(0), lean_box(0), v___x_248_, v___f_251_);
v___x_253_ = lean_apply_4(v_map_246_, lean_box(0), lean_box(0), v___f_242_, v_y_252_);
return v___x_253_;
}
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__1___boxed(lean_object* v_toPure_254_, lean_object* v_toFunctor_255_, lean_object* v_inst_256_, lean_object* v___f_257_, lean_object* v_toBind_258_, lean_object* v___f_259_, lean_object* v_mutex_260_, lean_object* v_inst_261_, lean_object* v___f_262_, lean_object* v_____do__lift_263_){
_start:
{
uint8_t v_____do__lift_120__boxed_264_; lean_object* v_res_265_; 
v_____do__lift_120__boxed_264_ = lean_unbox(v_____do__lift_263_);
v_res_265_ = l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__1(v_toPure_254_, v_toFunctor_255_, v_inst_256_, v___f_257_, v_toBind_258_, v___f_259_, v_mutex_260_, v_inst_261_, v___f_262_, v_____do__lift_120__boxed_264_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomicallyRead___redArg(lean_object* v_inst_266_, lean_object* v_inst_267_, lean_object* v_inst_268_, lean_object* v_mutex_269_, lean_object* v_k_270_){
_start:
{
lean_object* v_toApplicative_271_; lean_object* v_toBind_272_; lean_object* v_ref_273_; lean_object* v_mutex_274_; lean_object* v_toFunctor_275_; lean_object* v_toPure_276_; lean_object* v___f_277_; lean_object* v___f_278_; lean_object* v___f_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___f_282_; lean_object* v___f_283_; lean_object* v___x_284_; 
v_toApplicative_271_ = lean_ctor_get(v_inst_266_, 0);
lean_inc_ref(v_toApplicative_271_);
v_toBind_272_ = lean_ctor_get(v_inst_266_, 1);
lean_inc_n(v_toBind_272_, 2);
lean_dec_ref(v_inst_266_);
v_ref_273_ = lean_ctor_get(v_mutex_269_, 0);
lean_inc(v_ref_273_);
v_mutex_274_ = lean_ctor_get(v_mutex_269_, 1);
lean_inc_n(v_mutex_274_, 2);
lean_dec_ref(v_mutex_269_);
v_toFunctor_275_ = lean_ctor_get(v_toApplicative_271_, 0);
lean_inc_ref_n(v_toFunctor_275_, 2);
v_toPure_276_ = lean_ctor_get(v_toApplicative_271_, 1);
lean_inc(v_toPure_276_);
lean_dec_ref(v_toApplicative_271_);
v___f_277_ = ((lean_object*)(l_Std_SharedMutex_tryAtomically___redArg___closed__0));
v___f_278_ = ((lean_object*)(l_Std_SharedMutex_tryAtomically___redArg___closed__1));
v___f_279_ = lean_alloc_closure((void*)(l_Std_SharedMutex_atomicallyRead___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_279_, 0, v_ref_273_);
v___x_280_ = lean_alloc_closure((void*)(l_Std_BaseSharedMutex_tryRead___boxed), 2, 1);
lean_closure_set(v___x_280_, 0, v_mutex_274_);
lean_inc(v_inst_267_);
v___x_281_ = lean_apply_2(v_inst_267_, lean_box(0), v___x_280_);
v___f_282_ = lean_alloc_closure((void*)(l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__3), 4, 3);
lean_closure_set(v___f_282_, 0, v_toFunctor_275_);
lean_closure_set(v___f_282_, 1, v_k_270_);
lean_closure_set(v___f_282_, 2, v___f_278_);
v___f_283_ = lean_alloc_closure((void*)(l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_283_, 0, v_toPure_276_);
lean_closure_set(v___f_283_, 1, v_toFunctor_275_);
lean_closure_set(v___f_283_, 2, v_inst_267_);
lean_closure_set(v___f_283_, 3, v___f_279_);
lean_closure_set(v___f_283_, 4, v_toBind_272_);
lean_closure_set(v___f_283_, 5, v___f_282_);
lean_closure_set(v___f_283_, 6, v_mutex_274_);
lean_closure_set(v___f_283_, 7, v_inst_268_);
lean_closure_set(v___f_283_, 8, v___f_277_);
v___x_284_ = lean_apply_4(v_toBind_272_, lean_box(0), lean_box(0), v___x_281_, v___f_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomicallyRead(lean_object* v_m_285_, lean_object* v_00_u03b1_286_, lean_object* v_00_u03b2_287_, lean_object* v_inst_288_, lean_object* v_inst_289_, lean_object* v_inst_290_, lean_object* v_mutex_291_, lean_object* v_k_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Std_SharedMutex_tryAtomicallyRead___redArg(v_inst_288_, v_inst_289_, v_inst_290_, v_mutex_291_, v_k_292_);
return v___x_293_;
}
}
lean_object* runtime_initialize_Std_Sync_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sync_SharedMutex(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Sync_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Std_Sync_SharedMutex_0__Std_SharedMutexImpl = _init_l___private_Std_Sync_SharedMutex_0__Std_SharedMutexImpl();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sync_SharedMutex(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sync_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sync_SharedMutex(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sync_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sync_SharedMutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sync_SharedMutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sync_SharedMutex(builtin);
}
#ifdef __cplusplus
}
#endif
