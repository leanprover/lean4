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
LEAN_EXPORT void l_Std_BaseSharedMutex_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3_;
v_res_3_ = lean_io_basesharedmutex_new();
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_new___boxed(lean_object* v_a_00___x40___internal___hyg_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lean_io_basesharedmutex_new();
return v_res_5_;
}
}
LEAN_EXPORT void l_Std_BaseSharedMutex_write_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_6_ = stack[0].m_obj;
lean_object* v_res_8_;
v_res_8_ = lean_io_basesharedmutex_write(v_mutex_6_);
stack->m_obj
 = v_res_8_;
}
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_write___boxed(lean_object* v_mutex_9_, lean_object* v_a_00___x40___internal___hyg_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lean_io_basesharedmutex_write(v_mutex_9_);
lean_dec(v_mutex_9_);
return v_res_11_;
}
}
LEAN_EXPORT void l_Std_BaseSharedMutex_tryWrite_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_12_ = stack[0].m_obj;
uint8_t v_res_14_;
v_res_14_ = lean_io_basesharedmutex_try_write(v_mutex_12_);
stack->m_num = v_res_14_;
}
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_tryWrite___boxed(lean_object* v_mutex_15_, lean_object* v_a_00___x40___internal___hyg_16_){
_start:
{
uint8_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = lean_io_basesharedmutex_try_write(v_mutex_15_);
lean_dec(v_mutex_15_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT void l_Std_BaseSharedMutex_unlockWrite_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_19_ = stack[0].m_obj;
lean_object* v_res_21_;
v_res_21_ = lean_io_basesharedmutex_unlock_write(v_mutex_19_);
stack->m_obj
 = v_res_21_;
}
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_unlockWrite___boxed(lean_object* v_mutex_22_, lean_object* v_a_00___x40___internal___hyg_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lean_io_basesharedmutex_unlock_write(v_mutex_22_);
lean_dec(v_mutex_22_);
return v_res_24_;
}
}
LEAN_EXPORT void l_Std_BaseSharedMutex_read_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_25_ = stack[0].m_obj;
lean_object* v_res_27_;
v_res_27_ = lean_io_basesharedmutex_read(v_mutex_25_);
stack->m_obj
 = v_res_27_;
}
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_read___boxed(lean_object* v_mutex_28_, lean_object* v_a_00___x40___internal___hyg_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lean_io_basesharedmutex_read(v_mutex_28_);
lean_dec(v_mutex_28_);
return v_res_30_;
}
}
LEAN_EXPORT void l_Std_BaseSharedMutex_tryRead_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_31_ = stack[0].m_obj;
uint8_t v_res_33_;
v_res_33_ = lean_io_basesharedmutex_try_read(v_mutex_31_);
stack->m_num = v_res_33_;
}
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_tryRead___boxed(lean_object* v_mutex_34_, lean_object* v_a_00___x40___internal___hyg_35_){
_start:
{
uint8_t v_res_36_; lean_object* v_r_37_; 
v_res_36_ = lean_io_basesharedmutex_try_read(v_mutex_34_);
lean_dec(v_mutex_34_);
v_r_37_ = lean_box(v_res_36_);
return v_r_37_;
}
}
LEAN_EXPORT void l_Std_BaseSharedMutex_unlockRead_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_38_ = stack[0].m_obj;
lean_object* v_res_40_;
v_res_40_ = lean_io_basesharedmutex_unlock_read(v_mutex_38_);
stack->m_obj
 = v_res_40_;
}
LEAN_EXPORT lean_object* l_Std_BaseSharedMutex_unlockRead___boxed(lean_object* v_mutex_41_, lean_object* v_a_00___x40___internal___hyg_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lean_io_basesharedmutex_unlock_read(v_mutex_41_);
lean_dec(v_mutex_41_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutSharedMutexBaseSharedMutex___redArg___lam__0(lean_object* v_self_44_){
_start:
{
lean_object* v_mutex_45_; 
v_mutex_45_ = lean_ctor_get(v_self_44_, 1);
lean_inc(v_mutex_45_);
return v_mutex_45_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutSharedMutexBaseSharedMutex___redArg___lam__0___boxed(lean_object* v_self_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Std_instCoeOutSharedMutexBaseSharedMutex___redArg___lam__0(v_self_46_);
lean_dec_ref(v_self_46_);
return v_res_47_;
}
}
lean_object* l_Std_instCoeOutSharedMutexBaseSharedMutex___redArg(){
_start:
{
lean_object* v___f_50_; 
v___f_50_ = ((lean_object*)(l_Std_instCoeOutSharedMutexBaseSharedMutex___redArg___closed__0));
return v___f_50_;
}
}
LEAN_EXPORT void l_Std_instCoeOutSharedMutexBaseSharedMutex___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_51_;
v_res_51_ = l_Std_instCoeOutSharedMutexBaseSharedMutex___redArg();
stack->m_obj
 = v_res_51_;
}
LEAN_EXPORT lean_object* l_Std_instCoeOutSharedMutexBaseSharedMutex___redArg___boxed(lean_object* v___dummy_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Std_instCoeOutSharedMutexBaseSharedMutex___redArg();
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutSharedMutexBaseSharedMutex(lean_object* v_00_u03b1_54_){
_start:
{
lean_object* v___f_55_; 
v___f_55_ = ((lean_object*)(l_Std_instCoeOutSharedMutexBaseSharedMutex___redArg___closed__0));
return v___f_55_;
}
}
lean_object* l_Std_SharedMutex_new___redArg(lean_object* v_a_56_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = lean_st_mk_ref(v_a_56_);
v___x_59_ = lean_io_basesharedmutex_new();
v___x_60_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_58_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT void l_Std_SharedMutex_new___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_56_ = stack[0].m_obj;
lean_object* v_res_61_;
v_res_61_ = l_Std_SharedMutex_new___redArg(v_a_56_);
stack->m_obj
 = v_res_61_;
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_new___redArg___boxed(lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Std_SharedMutex_new___redArg(v_a_62_);
return v_res_64_;
}
}
lean_object* l_Std_SharedMutex_new(lean_object* v_00_u03b1_65_, lean_object* v_a_66_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Std_SharedMutex_new___redArg(v_a_66_);
return v___x_68_;
}
}
LEAN_EXPORT void l_Std_SharedMutex_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_66_ = stack[1].m_obj;
lean_object* v_res_69_;
v_res_69_ = l_Std_SharedMutex_new(lean_box(0), v_a_66_);
stack->m_obj
 = v_res_69_;
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_new___boxed(lean_object* v_00_u03b1_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Std_SharedMutex_new(v_00_u03b1_70_, v_a_71_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg___lam__0(lean_object* v_k_74_, lean_object* v_ref_75_, lean_object* v_____r_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_apply_1(v_k_74_, v_ref_75_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg___lam__1(lean_object* v_x_78_){
_start:
{
lean_object* v_fst_79_; 
v_fst_79_ = lean_ctor_get(v_x_78_, 0);
lean_inc(v_fst_79_);
return v_fst_79_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg___lam__1___boxed(lean_object* v_x_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Std_SharedMutex_atomically___redArg___lam__1(v_x_80_);
lean_dec_ref(v_x_80_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg___lam__2(lean_object* v___x_82_, lean_object* v_x_83_){
_start:
{
lean_inc(v___x_82_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg___lam__2___boxed(lean_object* v___x_84_, lean_object* v_x_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Std_SharedMutex_atomically___redArg___lam__2(v___x_84_, v_x_85_);
lean_dec(v_x_85_);
lean_dec(v___x_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically___redArg(lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_mutex_91_, lean_object* v_k_92_){
_start:
{
lean_object* v_toApplicative_93_; lean_object* v_toFunctor_94_; lean_object* v_toBind_95_; lean_object* v_ref_96_; lean_object* v_mutex_97_; lean_object* v_map_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___f_101_; lean_object* v___f_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___f_106_; lean_object* v_y_107_; lean_object* v___x_108_; 
v_toApplicative_93_ = lean_ctor_get(v_inst_88_, 0);
v_toFunctor_94_ = lean_ctor_get(v_toApplicative_93_, 0);
lean_inc_ref(v_toFunctor_94_);
v_toBind_95_ = lean_ctor_get(v_inst_88_, 1);
lean_inc(v_toBind_95_);
lean_dec_ref(v_inst_88_);
v_ref_96_ = lean_ctor_get(v_mutex_91_, 0);
lean_inc(v_ref_96_);
v_mutex_97_ = lean_ctor_get(v_mutex_91_, 1);
lean_inc_n(v_mutex_97_, 2);
lean_dec_ref(v_mutex_91_);
v_map_98_ = lean_ctor_get(v_toFunctor_94_, 0);
lean_inc(v_map_98_);
lean_dec_ref(v_toFunctor_94_);
v___x_99_ = lean_alloc_closure((void*)(l_Std_BaseSharedMutex_write___boxed), 2, 1);
lean_closure_set(v___x_99_, 0, v_mutex_97_);
lean_inc(v_inst_89_);
v___x_100_ = lean_apply_2(v_inst_89_, lean_box(0), v___x_99_);
v___f_101_ = lean_alloc_closure((void*)(l_Std_SharedMutex_atomically___redArg___lam__0), 3, 2);
lean_closure_set(v___f_101_, 0, v_k_92_);
lean_closure_set(v___f_101_, 1, v_ref_96_);
v___f_102_ = ((lean_object*)(l_Std_SharedMutex_atomically___redArg___closed__0));
v___x_103_ = lean_apply_4(v_toBind_95_, lean_box(0), lean_box(0), v___x_100_, v___f_101_);
v___x_104_ = lean_alloc_closure((void*)(l_Std_BaseSharedMutex_unlockWrite___boxed), 2, 1);
lean_closure_set(v___x_104_, 0, v_mutex_97_);
v___x_105_ = lean_apply_2(v_inst_89_, lean_box(0), v___x_104_);
v___f_106_ = lean_alloc_closure((void*)(l_Std_SharedMutex_atomically___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_106_, 0, v___x_105_);
v_y_107_ = lean_apply_4(v_inst_90_, lean_box(0), lean_box(0), v___x_103_, v___f_106_);
v___x_108_ = lean_apply_4(v_map_98_, lean_box(0), lean_box(0), v___f_102_, v_y_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomically(lean_object* v_m_109_, lean_object* v_00_u03b1_110_, lean_object* v_00_u03b2_111_, lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_inst_114_, lean_object* v_mutex_115_, lean_object* v_k_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Std_SharedMutex_atomically___redArg(v_inst_112_, v_inst_113_, v_inst_114_, v_mutex_115_, v_k_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__0(lean_object* v_x_118_){
_start:
{
lean_object* v_fst_119_; 
v_fst_119_ = lean_ctor_get(v_x_118_, 0);
lean_inc(v_fst_119_);
return v_fst_119_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__0___boxed(lean_object* v_x_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Std_SharedMutex_tryAtomically___redArg___lam__0(v_x_120_);
lean_dec_ref(v_x_120_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__1(lean_object* v_val_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_123_, 0, v_val_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__2(lean_object* v___x_124_, lean_object* v_x_125_){
_start:
{
lean_inc(v___x_124_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__2___boxed(lean_object* v___x_126_, lean_object* v_x_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Std_SharedMutex_tryAtomically___redArg___lam__2(v___x_126_, v_x_127_);
lean_dec(v_x_127_);
lean_dec(v___x_126_);
return v_res_128_;
}
}
lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__3(lean_object* v_toPure_129_, lean_object* v_toFunctor_130_, lean_object* v_k_131_, lean_object* v_ref_132_, lean_object* v___f_133_, lean_object* v_mutex_134_, lean_object* v_inst_135_, lean_object* v_inst_136_, lean_object* v___f_137_, uint8_t v_____do__lift_138_){
_start:
{
if (v_____do__lift_138_ == 0)
{
lean_object* v___x_139_; lean_object* v___x_140_; 
lean_dec_ref(v___f_137_);
lean_dec(v_inst_136_);
lean_dec(v_inst_135_);
lean_dec(v_mutex_134_);
lean_dec_ref(v___f_133_);
lean_dec(v_ref_132_);
lean_dec(v_k_131_);
lean_dec_ref(v_toFunctor_130_);
v___x_139_ = lean_box(0);
v___x_140_ = lean_apply_2(v_toPure_129_, lean_box(0), v___x_139_);
return v___x_140_;
}
else
{
lean_object* v_map_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___f_146_; lean_object* v_y_147_; lean_object* v___x_148_; 
lean_dec(v_toPure_129_);
v_map_141_ = lean_ctor_get(v_toFunctor_130_, 0);
lean_inc_n(v_map_141_, 2);
lean_dec_ref(v_toFunctor_130_);
v___x_142_ = lean_apply_1(v_k_131_, v_ref_132_);
v___x_143_ = lean_apply_4(v_map_141_, lean_box(0), lean_box(0), v___f_133_, v___x_142_);
v___x_144_ = lean_alloc_closure((void*)(l_Std_BaseSharedMutex_unlockWrite___boxed), 2, 1);
lean_closure_set(v___x_144_, 0, v_mutex_134_);
v___x_145_ = lean_apply_2(v_inst_135_, lean_box(0), v___x_144_);
v___f_146_ = lean_alloc_closure((void*)(l_Std_SharedMutex_tryAtomically___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_146_, 0, v___x_145_);
v_y_147_ = lean_apply_4(v_inst_136_, lean_box(0), lean_box(0), v___x_143_, v___f_146_);
v___x_148_ = lean_apply_4(v_map_141_, lean_box(0), lean_box(0), v___f_137_, v_y_147_);
return v___x_148_;
}
}
}
LEAN_EXPORT void l_Std_SharedMutex_tryAtomically___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_129_ = stack[0].m_obj;
lean_object* v_toFunctor_130_ = stack[1].m_obj;
lean_object* v_k_131_ = stack[2].m_obj;
lean_object* v_ref_132_ = stack[3].m_obj;
lean_object* v___f_133_ = stack[4].m_obj;
lean_object* v_mutex_134_ = stack[5].m_obj;
lean_object* v_inst_135_ = stack[6].m_obj;
lean_object* v_inst_136_ = stack[7].m_obj;
lean_object* v___f_137_ = stack[8].m_obj;
uint8_t v_____do__lift_138_ = stack[9].m_num;
lean_object* v_res_149_;
v_res_149_ = l_Std_SharedMutex_tryAtomically___redArg___lam__3(v_toPure_129_, v_toFunctor_130_, v_k_131_, v_ref_132_, v___f_133_, v_mutex_134_, v_inst_135_, v_inst_136_, v___f_137_, v_____do__lift_138_);
stack->m_obj
 = v_res_149_;
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg___lam__3___boxed(lean_object* v_toPure_150_, lean_object* v_toFunctor_151_, lean_object* v_k_152_, lean_object* v_ref_153_, lean_object* v___f_154_, lean_object* v_mutex_155_, lean_object* v_inst_156_, lean_object* v_inst_157_, lean_object* v___f_158_, lean_object* v_____do__lift_159_){
_start:
{
uint8_t v_____do__lift_92__boxed_160_; lean_object* v_res_161_; 
v_____do__lift_92__boxed_160_ = lean_unbox(v_____do__lift_159_);
v_res_161_ = l_Std_SharedMutex_tryAtomically___redArg___lam__3(v_toPure_150_, v_toFunctor_151_, v_k_152_, v_ref_153_, v___f_154_, v_mutex_155_, v_inst_156_, v_inst_157_, v___f_158_, v_____do__lift_92__boxed_160_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically___redArg(lean_object* v_inst_164_, lean_object* v_inst_165_, lean_object* v_inst_166_, lean_object* v_mutex_167_, lean_object* v_k_168_){
_start:
{
lean_object* v_toApplicative_169_; lean_object* v_toBind_170_; lean_object* v_ref_171_; lean_object* v_mutex_172_; lean_object* v_toFunctor_173_; lean_object* v_toPure_174_; lean_object* v___f_175_; lean_object* v___f_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___f_179_; lean_object* v___x_180_; 
v_toApplicative_169_ = lean_ctor_get(v_inst_164_, 0);
lean_inc_ref(v_toApplicative_169_);
v_toBind_170_ = lean_ctor_get(v_inst_164_, 1);
lean_inc(v_toBind_170_);
lean_dec_ref(v_inst_164_);
v_ref_171_ = lean_ctor_get(v_mutex_167_, 0);
lean_inc(v_ref_171_);
v_mutex_172_ = lean_ctor_get(v_mutex_167_, 1);
lean_inc_n(v_mutex_172_, 2);
lean_dec_ref(v_mutex_167_);
v_toFunctor_173_ = lean_ctor_get(v_toApplicative_169_, 0);
lean_inc_ref(v_toFunctor_173_);
v_toPure_174_ = lean_ctor_get(v_toApplicative_169_, 1);
lean_inc(v_toPure_174_);
lean_dec_ref(v_toApplicative_169_);
v___f_175_ = ((lean_object*)(l_Std_SharedMutex_tryAtomically___redArg___closed__0));
v___f_176_ = ((lean_object*)(l_Std_SharedMutex_tryAtomically___redArg___closed__1));
v___x_177_ = lean_alloc_closure((void*)(l_Std_BaseSharedMutex_tryWrite___boxed), 2, 1);
lean_closure_set(v___x_177_, 0, v_mutex_172_);
lean_inc(v_inst_165_);
v___x_178_ = lean_apply_2(v_inst_165_, lean_box(0), v___x_177_);
v___f_179_ = lean_alloc_closure((void*)(l_Std_SharedMutex_tryAtomically___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_179_, 0, v_toPure_174_);
lean_closure_set(v___f_179_, 1, v_toFunctor_173_);
lean_closure_set(v___f_179_, 2, v_k_168_);
lean_closure_set(v___f_179_, 3, v_ref_171_);
lean_closure_set(v___f_179_, 4, v___f_176_);
lean_closure_set(v___f_179_, 5, v_mutex_172_);
lean_closure_set(v___f_179_, 6, v_inst_165_);
lean_closure_set(v___f_179_, 7, v_inst_166_);
lean_closure_set(v___f_179_, 8, v___f_175_);
v___x_180_ = lean_apply_4(v_toBind_170_, lean_box(0), lean_box(0), v___x_178_, v___f_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomically(lean_object* v_m_181_, lean_object* v_00_u03b1_182_, lean_object* v_00_u03b2_183_, lean_object* v_inst_184_, lean_object* v_inst_185_, lean_object* v_inst_186_, lean_object* v_mutex_187_, lean_object* v_k_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Std_SharedMutex_tryAtomically___redArg(v_inst_184_, v_inst_185_, v_inst_186_, v_mutex_187_, v_k_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomicallyRead___redArg___lam__0(lean_object* v_k_190_, lean_object* v_state_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_apply_1(v_k_190_, v_state_191_);
return v___x_192_;
}
}
lean_object* l_Std_SharedMutex_atomicallyRead___redArg___lam__2(lean_object* v_ref_193_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = lean_st_ref_get(v_ref_193_);
return v___x_195_;
}
}
LEAN_EXPORT void l_Std_SharedMutex_atomicallyRead___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_193_ = stack[0].m_obj;
lean_object* v_res_196_;
v_res_196_ = l_Std_SharedMutex_atomicallyRead___redArg___lam__2(v_ref_193_);
stack->m_obj
 = v_res_196_;
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomicallyRead___redArg___lam__2___boxed(lean_object* v_ref_197_, lean_object* v___y_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Std_SharedMutex_atomicallyRead___redArg___lam__2(v_ref_197_);
lean_dec(v_ref_197_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomicallyRead___redArg___lam__1(lean_object* v_ref_200_, lean_object* v_inst_201_, lean_object* v_toBind_202_, lean_object* v___f_203_, lean_object* v_____r_204_){
_start:
{
lean_object* v___f_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___f_205_ = lean_alloc_closure((void*)(l_Std_SharedMutex_atomicallyRead___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_205_, 0, v_ref_200_);
v___x_206_ = lean_apply_2(v_inst_201_, lean_box(0), v___f_205_);
v___x_207_ = lean_apply_4(v_toBind_202_, lean_box(0), lean_box(0), v___x_206_, v___f_203_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomicallyRead___redArg(lean_object* v_inst_208_, lean_object* v_inst_209_, lean_object* v_inst_210_, lean_object* v_mutex_211_, lean_object* v_k_212_){
_start:
{
lean_object* v_toApplicative_213_; lean_object* v_toFunctor_214_; lean_object* v_toBind_215_; lean_object* v_ref_216_; lean_object* v_mutex_217_; lean_object* v_map_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___f_221_; lean_object* v___f_222_; lean_object* v___f_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___f_227_; lean_object* v_y_228_; lean_object* v___x_229_; 
v_toApplicative_213_ = lean_ctor_get(v_inst_208_, 0);
v_toFunctor_214_ = lean_ctor_get(v_toApplicative_213_, 0);
lean_inc_ref(v_toFunctor_214_);
v_toBind_215_ = lean_ctor_get(v_inst_208_, 1);
lean_inc_n(v_toBind_215_, 2);
lean_dec_ref(v_inst_208_);
v_ref_216_ = lean_ctor_get(v_mutex_211_, 0);
lean_inc(v_ref_216_);
v_mutex_217_ = lean_ctor_get(v_mutex_211_, 1);
lean_inc_n(v_mutex_217_, 2);
lean_dec_ref(v_mutex_211_);
v_map_218_ = lean_ctor_get(v_toFunctor_214_, 0);
lean_inc(v_map_218_);
lean_dec_ref(v_toFunctor_214_);
v___x_219_ = lean_alloc_closure((void*)(l_Std_BaseSharedMutex_read___boxed), 2, 1);
lean_closure_set(v___x_219_, 0, v_mutex_217_);
lean_inc_n(v_inst_209_, 2);
v___x_220_ = lean_apply_2(v_inst_209_, lean_box(0), v___x_219_);
v___f_221_ = lean_alloc_closure((void*)(l_Std_SharedMutex_atomicallyRead___redArg___lam__0), 2, 1);
lean_closure_set(v___f_221_, 0, v_k_212_);
v___f_222_ = ((lean_object*)(l_Std_SharedMutex_atomically___redArg___closed__0));
v___f_223_ = lean_alloc_closure((void*)(l_Std_SharedMutex_atomicallyRead___redArg___lam__1), 5, 4);
lean_closure_set(v___f_223_, 0, v_ref_216_);
lean_closure_set(v___f_223_, 1, v_inst_209_);
lean_closure_set(v___f_223_, 2, v_toBind_215_);
lean_closure_set(v___f_223_, 3, v___f_221_);
v___x_224_ = lean_apply_4(v_toBind_215_, lean_box(0), lean_box(0), v___x_220_, v___f_223_);
v___x_225_ = lean_alloc_closure((void*)(l_Std_BaseSharedMutex_unlockRead___boxed), 2, 1);
lean_closure_set(v___x_225_, 0, v_mutex_217_);
v___x_226_ = lean_apply_2(v_inst_209_, lean_box(0), v___x_225_);
v___f_227_ = lean_alloc_closure((void*)(l_Std_SharedMutex_atomically___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_227_, 0, v___x_226_);
v_y_228_ = lean_apply_4(v_inst_210_, lean_box(0), lean_box(0), v___x_224_, v___f_227_);
v___x_229_ = lean_apply_4(v_map_218_, lean_box(0), lean_box(0), v___f_222_, v_y_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_atomicallyRead(lean_object* v_m_230_, lean_object* v_00_u03b1_231_, lean_object* v_00_u03b2_232_, lean_object* v_inst_233_, lean_object* v_inst_234_, lean_object* v_inst_235_, lean_object* v_mutex_236_, lean_object* v_k_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Std_SharedMutex_atomicallyRead___redArg(v_inst_233_, v_inst_234_, v_inst_235_, v_mutex_236_, v_k_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__3(lean_object* v_toFunctor_239_, lean_object* v_k_240_, lean_object* v___f_241_, lean_object* v_state_242_){
_start:
{
lean_object* v_map_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_map_243_ = lean_ctor_get(v_toFunctor_239_, 0);
lean_inc(v_map_243_);
lean_dec_ref(v_toFunctor_239_);
v___x_244_ = lean_apply_1(v_k_240_, v_state_242_);
v___x_245_ = lean_apply_4(v_map_243_, lean_box(0), lean_box(0), v___f_241_, v___x_244_);
return v___x_245_;
}
}
lean_object* l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__1(lean_object* v_toPure_246_, lean_object* v_toFunctor_247_, lean_object* v_inst_248_, lean_object* v___f_249_, lean_object* v_toBind_250_, lean_object* v___f_251_, lean_object* v_mutex_252_, lean_object* v_inst_253_, lean_object* v___f_254_, uint8_t v_____do__lift_255_){
_start:
{
if (v_____do__lift_255_ == 0)
{
lean_object* v___x_256_; lean_object* v___x_257_; 
lean_dec_ref(v___f_254_);
lean_dec(v_inst_253_);
lean_dec(v_mutex_252_);
lean_dec(v___f_251_);
lean_dec(v_toBind_250_);
lean_dec_ref(v___f_249_);
lean_dec(v_inst_248_);
lean_dec_ref(v_toFunctor_247_);
v___x_256_ = lean_box(0);
v___x_257_ = lean_apply_2(v_toPure_246_, lean_box(0), v___x_256_);
return v___x_257_;
}
else
{
lean_object* v_map_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___f_263_; lean_object* v_y_264_; lean_object* v___x_265_; 
lean_dec(v_toPure_246_);
v_map_258_ = lean_ctor_get(v_toFunctor_247_, 0);
lean_inc(v_map_258_);
lean_dec_ref(v_toFunctor_247_);
lean_inc(v_inst_248_);
v___x_259_ = lean_apply_2(v_inst_248_, lean_box(0), v___f_249_);
v___x_260_ = lean_apply_4(v_toBind_250_, lean_box(0), lean_box(0), v___x_259_, v___f_251_);
v___x_261_ = lean_alloc_closure((void*)(l_Std_BaseSharedMutex_unlockRead___boxed), 2, 1);
lean_closure_set(v___x_261_, 0, v_mutex_252_);
v___x_262_ = lean_apply_2(v_inst_248_, lean_box(0), v___x_261_);
v___f_263_ = lean_alloc_closure((void*)(l_Std_SharedMutex_tryAtomically___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_263_, 0, v___x_262_);
v_y_264_ = lean_apply_4(v_inst_253_, lean_box(0), lean_box(0), v___x_260_, v___f_263_);
v___x_265_ = lean_apply_4(v_map_258_, lean_box(0), lean_box(0), v___f_254_, v_y_264_);
return v___x_265_;
}
}
}
LEAN_EXPORT void l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_246_ = stack[0].m_obj;
lean_object* v_toFunctor_247_ = stack[1].m_obj;
lean_object* v_inst_248_ = stack[2].m_obj;
lean_object* v___f_249_ = stack[3].m_obj;
lean_object* v_toBind_250_ = stack[4].m_obj;
lean_object* v___f_251_ = stack[5].m_obj;
lean_object* v_mutex_252_ = stack[6].m_obj;
lean_object* v_inst_253_ = stack[7].m_obj;
lean_object* v___f_254_ = stack[8].m_obj;
uint8_t v_____do__lift_255_ = stack[9].m_num;
lean_object* v_res_266_;
v_res_266_ = l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__1(v_toPure_246_, v_toFunctor_247_, v_inst_248_, v___f_249_, v_toBind_250_, v___f_251_, v_mutex_252_, v_inst_253_, v___f_254_, v_____do__lift_255_);
stack->m_obj
 = v_res_266_;
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__1___boxed(lean_object* v_toPure_267_, lean_object* v_toFunctor_268_, lean_object* v_inst_269_, lean_object* v___f_270_, lean_object* v_toBind_271_, lean_object* v___f_272_, lean_object* v_mutex_273_, lean_object* v_inst_274_, lean_object* v___f_275_, lean_object* v_____do__lift_276_){
_start:
{
uint8_t v_____do__lift_123__boxed_277_; lean_object* v_res_278_; 
v_____do__lift_123__boxed_277_ = lean_unbox(v_____do__lift_276_);
v_res_278_ = l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__1(v_toPure_267_, v_toFunctor_268_, v_inst_269_, v___f_270_, v_toBind_271_, v___f_272_, v_mutex_273_, v_inst_274_, v___f_275_, v_____do__lift_123__boxed_277_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomicallyRead___redArg(lean_object* v_inst_279_, lean_object* v_inst_280_, lean_object* v_inst_281_, lean_object* v_mutex_282_, lean_object* v_k_283_){
_start:
{
lean_object* v_toApplicative_284_; lean_object* v_toBind_285_; lean_object* v_ref_286_; lean_object* v_mutex_287_; lean_object* v_toFunctor_288_; lean_object* v_toPure_289_; lean_object* v___f_290_; lean_object* v___f_291_; lean_object* v___f_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___f_295_; lean_object* v___f_296_; lean_object* v___x_297_; 
v_toApplicative_284_ = lean_ctor_get(v_inst_279_, 0);
lean_inc_ref(v_toApplicative_284_);
v_toBind_285_ = lean_ctor_get(v_inst_279_, 1);
lean_inc_n(v_toBind_285_, 2);
lean_dec_ref(v_inst_279_);
v_ref_286_ = lean_ctor_get(v_mutex_282_, 0);
lean_inc(v_ref_286_);
v_mutex_287_ = lean_ctor_get(v_mutex_282_, 1);
lean_inc_n(v_mutex_287_, 2);
lean_dec_ref(v_mutex_282_);
v_toFunctor_288_ = lean_ctor_get(v_toApplicative_284_, 0);
lean_inc_ref_n(v_toFunctor_288_, 2);
v_toPure_289_ = lean_ctor_get(v_toApplicative_284_, 1);
lean_inc(v_toPure_289_);
lean_dec_ref(v_toApplicative_284_);
v___f_290_ = ((lean_object*)(l_Std_SharedMutex_tryAtomically___redArg___closed__0));
v___f_291_ = ((lean_object*)(l_Std_SharedMutex_tryAtomically___redArg___closed__1));
v___f_292_ = lean_alloc_closure((void*)(l_Std_SharedMutex_atomicallyRead___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_292_, 0, v_ref_286_);
v___x_293_ = lean_alloc_closure((void*)(l_Std_BaseSharedMutex_tryRead___boxed), 2, 1);
lean_closure_set(v___x_293_, 0, v_mutex_287_);
lean_inc(v_inst_280_);
v___x_294_ = lean_apply_2(v_inst_280_, lean_box(0), v___x_293_);
v___f_295_ = lean_alloc_closure((void*)(l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__3), 4, 3);
lean_closure_set(v___f_295_, 0, v_toFunctor_288_);
lean_closure_set(v___f_295_, 1, v_k_283_);
lean_closure_set(v___f_295_, 2, v___f_291_);
v___f_296_ = lean_alloc_closure((void*)(l_Std_SharedMutex_tryAtomicallyRead___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_296_, 0, v_toPure_289_);
lean_closure_set(v___f_296_, 1, v_toFunctor_288_);
lean_closure_set(v___f_296_, 2, v_inst_280_);
lean_closure_set(v___f_296_, 3, v___f_292_);
lean_closure_set(v___f_296_, 4, v_toBind_285_);
lean_closure_set(v___f_296_, 5, v___f_295_);
lean_closure_set(v___f_296_, 6, v_mutex_287_);
lean_closure_set(v___f_296_, 7, v_inst_281_);
lean_closure_set(v___f_296_, 8, v___f_290_);
v___x_297_ = lean_apply_4(v_toBind_285_, lean_box(0), lean_box(0), v___x_294_, v___f_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Std_SharedMutex_tryAtomicallyRead(lean_object* v_m_298_, lean_object* v_00_u03b1_299_, lean_object* v_00_u03b2_300_, lean_object* v_inst_301_, lean_object* v_inst_302_, lean_object* v_inst_303_, lean_object* v_mutex_304_, lean_object* v_k_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Std_SharedMutex_tryAtomicallyRead___redArg(v_inst_301_, v_inst_302_, v_inst_303_, v_mutex_304_, v_k_305_);
return v___x_306_;
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
