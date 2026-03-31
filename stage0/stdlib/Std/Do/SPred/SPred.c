// Lean compiler output
// Module: Std.Do.SPred.SPred
// Imports: public import Init.Ext public import Std.Do.SPred.SVal public import Init.NotationExtra
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
LEAN_EXPORT lean_object* l_Std_Do_SPred_pure___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_pure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_pure___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_pure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_and(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_and___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_or(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_or___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_not(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_not___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_imp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_imp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_iff(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_iff___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_exists___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_exists___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_exists___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_exists(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_forall___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_forall___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_forall(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_conjunction(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_conjunction_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_conjunction_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_conjunction_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_pure___redArg___lam__0___boxed(lean_object* v_tail_1_, lean_object* v___y_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l_Std_Do_SPred_pure___redArg___lam__0(v_tail_1_, v___y_2_);
lean_dec(v___y_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_pure___redArg(lean_object* v_00_u03c3s_4_){
_start:
{
if (lean_obj_tag(v_00_u03c3s_4_) == 0)
{
lean_object* v___x_5_; 
v___x_5_ = lean_box(0);
return v___x_5_;
}
else
{
lean_object* v_tail_6_; lean_object* v___f_7_; 
v_tail_6_ = lean_ctor_get(v_00_u03c3s_4_, 1);
lean_inc(v_tail_6_);
lean_dec_ref(v_00_u03c3s_4_);
v___f_7_ = lean_alloc_closure((void*)(l_Std_Do_SPred_pure___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_7_, 0, v_tail_6_);
return v___f_7_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_pure___redArg___lam__0(lean_object* v_tail_8_, lean_object* v___y_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Std_Do_SPred_pure___redArg(v_tail_8_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_pure(lean_object* v_00_u03c3s_11_, lean_object* v_P_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l_Std_Do_SPred_pure___redArg(v_00_u03c3s_11_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_and(lean_object* v_00_u03c3s_14_, lean_object* v_P_15_, lean_object* v_Q_16_){
_start:
{
if (lean_obj_tag(v_00_u03c3s_14_) == 0)
{
lean_object* v___x_17_; 
lean_dec(v_Q_16_);
lean_dec(v_P_15_);
v___x_17_ = lean_box(0);
return v___x_17_;
}
else
{
lean_object* v_tail_18_; lean_object* v___f_19_; 
v_tail_18_ = lean_ctor_get(v_00_u03c3s_14_, 1);
lean_inc(v_tail_18_);
lean_dec_ref(v_00_u03c3s_14_);
v___f_19_ = lean_alloc_closure((void*)(l_Std_Do_SPred_and___lam__0), 4, 3);
lean_closure_set(v___f_19_, 0, v_P_15_);
lean_closure_set(v___f_19_, 1, v_Q_16_);
lean_closure_set(v___f_19_, 2, v_tail_18_);
return v___f_19_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_and___lam__0(lean_object* v_P_20_, lean_object* v_Q_21_, lean_object* v_tail_22_, lean_object* v___y_23_){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
lean_inc(v___y_23_);
v___x_24_ = lean_apply_1(v_P_20_, v___y_23_);
v___x_25_ = lean_apply_1(v_Q_21_, v___y_23_);
v___x_26_ = l_Std_Do_SPred_and(v_tail_22_, v___x_24_, v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_or(lean_object* v_00_u03c3s_27_, lean_object* v_P_28_, lean_object* v_Q_29_){
_start:
{
if (lean_obj_tag(v_00_u03c3s_27_) == 0)
{
lean_object* v___x_30_; 
lean_dec(v_Q_29_);
lean_dec(v_P_28_);
v___x_30_ = lean_box(0);
return v___x_30_;
}
else
{
lean_object* v_tail_31_; lean_object* v___f_32_; 
v_tail_31_ = lean_ctor_get(v_00_u03c3s_27_, 1);
lean_inc(v_tail_31_);
lean_dec_ref(v_00_u03c3s_27_);
v___f_32_ = lean_alloc_closure((void*)(l_Std_Do_SPred_or___lam__0), 4, 3);
lean_closure_set(v___f_32_, 0, v_P_28_);
lean_closure_set(v___f_32_, 1, v_Q_29_);
lean_closure_set(v___f_32_, 2, v_tail_31_);
return v___f_32_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_or___lam__0(lean_object* v_P_33_, lean_object* v_Q_34_, lean_object* v_tail_35_, lean_object* v___y_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
lean_inc(v___y_36_);
v___x_37_ = lean_apply_1(v_P_33_, v___y_36_);
v___x_38_ = lean_apply_1(v_Q_34_, v___y_36_);
v___x_39_ = l_Std_Do_SPred_or(v_tail_35_, v___x_37_, v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_not(lean_object* v_00_u03c3s_40_, lean_object* v_P_41_){
_start:
{
if (lean_obj_tag(v_00_u03c3s_40_) == 0)
{
lean_object* v___x_42_; 
lean_dec(v_P_41_);
v___x_42_ = lean_box(0);
return v___x_42_;
}
else
{
lean_object* v_tail_43_; lean_object* v___f_44_; 
v_tail_43_ = lean_ctor_get(v_00_u03c3s_40_, 1);
lean_inc(v_tail_43_);
lean_dec_ref(v_00_u03c3s_40_);
v___f_44_ = lean_alloc_closure((void*)(l_Std_Do_SPred_not___lam__0), 3, 2);
lean_closure_set(v___f_44_, 0, v_P_41_);
lean_closure_set(v___f_44_, 1, v_tail_43_);
return v___f_44_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_not___lam__0(lean_object* v_P_45_, lean_object* v_tail_46_, lean_object* v___y_47_){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = lean_apply_1(v_P_45_, v___y_47_);
v___x_49_ = l_Std_Do_SPred_not(v_tail_46_, v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_imp(lean_object* v_00_u03c3s_50_, lean_object* v_P_51_, lean_object* v_Q_52_){
_start:
{
if (lean_obj_tag(v_00_u03c3s_50_) == 0)
{
lean_object* v___x_53_; 
lean_dec(v_Q_52_);
lean_dec(v_P_51_);
v___x_53_ = lean_box(0);
return v___x_53_;
}
else
{
lean_object* v_tail_54_; lean_object* v___f_55_; 
v_tail_54_ = lean_ctor_get(v_00_u03c3s_50_, 1);
lean_inc(v_tail_54_);
lean_dec_ref(v_00_u03c3s_50_);
v___f_55_ = lean_alloc_closure((void*)(l_Std_Do_SPred_imp___lam__0), 4, 3);
lean_closure_set(v___f_55_, 0, v_P_51_);
lean_closure_set(v___f_55_, 1, v_Q_52_);
lean_closure_set(v___f_55_, 2, v_tail_54_);
return v___f_55_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_imp___lam__0(lean_object* v_P_56_, lean_object* v_Q_57_, lean_object* v_tail_58_, lean_object* v___y_59_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
lean_inc(v___y_59_);
v___x_60_ = lean_apply_1(v_P_56_, v___y_59_);
v___x_61_ = lean_apply_1(v_Q_57_, v___y_59_);
v___x_62_ = l_Std_Do_SPred_imp(v_tail_58_, v___x_60_, v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_iff(lean_object* v_00_u03c3s_63_, lean_object* v_P_64_, lean_object* v_Q_65_){
_start:
{
if (lean_obj_tag(v_00_u03c3s_63_) == 0)
{
lean_object* v___x_66_; 
lean_dec(v_Q_65_);
lean_dec(v_P_64_);
v___x_66_ = lean_box(0);
return v___x_66_;
}
else
{
lean_object* v_tail_67_; lean_object* v___f_68_; 
v_tail_67_ = lean_ctor_get(v_00_u03c3s_63_, 1);
lean_inc(v_tail_67_);
lean_dec_ref(v_00_u03c3s_63_);
v___f_68_ = lean_alloc_closure((void*)(l_Std_Do_SPred_iff___lam__0), 4, 3);
lean_closure_set(v___f_68_, 0, v_P_64_);
lean_closure_set(v___f_68_, 1, v_Q_65_);
lean_closure_set(v___f_68_, 2, v_tail_67_);
return v___f_68_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_iff___lam__0(lean_object* v_P_69_, lean_object* v_Q_70_, lean_object* v_tail_71_, lean_object* v___y_72_){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
lean_inc(v___y_72_);
v___x_73_ = lean_apply_1(v_P_69_, v___y_72_);
v___x_74_ = lean_apply_1(v_Q_70_, v___y_72_);
v___x_75_ = l_Std_Do_SPred_iff(v_tail_71_, v___x_73_, v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_exists___redArg___lam__0(lean_object* v_P_76_, lean_object* v___y_77_, lean_object* v_a_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_apply_2(v_P_76_, v_a_78_, v___y_77_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_exists___redArg(lean_object* v_00_u03c3s_80_, lean_object* v_P_81_){
_start:
{
if (lean_obj_tag(v_00_u03c3s_80_) == 0)
{
lean_object* v___x_82_; 
lean_dec(v_P_81_);
v___x_82_ = lean_box(0);
return v___x_82_;
}
else
{
lean_object* v_tail_83_; lean_object* v___f_84_; 
v_tail_83_ = lean_ctor_get(v_00_u03c3s_80_, 1);
lean_inc(v_tail_83_);
lean_dec_ref(v_00_u03c3s_80_);
v___f_84_ = lean_alloc_closure((void*)(l_Std_Do_SPred_exists___redArg___lam__1), 3, 2);
lean_closure_set(v___f_84_, 0, v_P_81_);
lean_closure_set(v___f_84_, 1, v_tail_83_);
return v___f_84_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_exists___redArg___lam__1(lean_object* v_P_85_, lean_object* v_tail_86_, lean_object* v___y_87_){
_start:
{
lean_object* v___f_88_; lean_object* v___x_89_; 
v___f_88_ = lean_alloc_closure((void*)(l_Std_Do_SPred_exists___redArg___lam__0), 3, 2);
lean_closure_set(v___f_88_, 0, v_P_85_);
lean_closure_set(v___f_88_, 1, v___y_87_);
v___x_89_ = l_Std_Do_SPred_exists___redArg(v_tail_86_, v___f_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_exists(lean_object* v_00_u03b1_90_, lean_object* v_00_u03c3s_91_, lean_object* v_P_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Std_Do_SPred_exists___redArg(v_00_u03c3s_91_, v_P_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_forall___redArg(lean_object* v_00_u03c3s_94_, lean_object* v_P_95_){
_start:
{
if (lean_obj_tag(v_00_u03c3s_94_) == 0)
{
lean_object* v___x_96_; 
lean_dec(v_P_95_);
v___x_96_ = lean_box(0);
return v___x_96_;
}
else
{
lean_object* v_tail_97_; lean_object* v___f_98_; 
v_tail_97_ = lean_ctor_get(v_00_u03c3s_94_, 1);
lean_inc(v_tail_97_);
lean_dec_ref(v_00_u03c3s_94_);
v___f_98_ = lean_alloc_closure((void*)(l_Std_Do_SPred_forall___redArg___lam__1), 3, 2);
lean_closure_set(v___f_98_, 0, v_P_95_);
lean_closure_set(v___f_98_, 1, v_tail_97_);
return v___f_98_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_forall___redArg___lam__1(lean_object* v_P_99_, lean_object* v_tail_100_, lean_object* v___y_101_){
_start:
{
lean_object* v___f_102_; lean_object* v___x_103_; 
v___f_102_ = lean_alloc_closure((void*)(l_Std_Do_SPred_exists___redArg___lam__0), 3, 2);
lean_closure_set(v___f_102_, 0, v_P_99_);
lean_closure_set(v___f_102_, 1, v___y_101_);
v___x_103_ = l_Std_Do_SPred_forall___redArg(v_tail_100_, v___f_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_forall(lean_object* v_00_u03b1_104_, lean_object* v_00_u03c3s_105_, lean_object* v_P_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Std_Do_SPred_forall___redArg(v_00_u03c3s_105_, v_P_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_conjunction(lean_object* v_00_u03c3s_108_, lean_object* v_env_109_){
_start:
{
if (lean_obj_tag(v_env_109_) == 0)
{
lean_object* v___x_110_; 
v___x_110_ = l_Std_Do_SPred_pure___redArg(v_00_u03c3s_108_);
return v___x_110_;
}
else
{
lean_object* v_head_111_; lean_object* v_tail_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v_head_111_ = lean_ctor_get(v_env_109_, 0);
lean_inc(v_head_111_);
v_tail_112_ = lean_ctor_get(v_env_109_, 1);
lean_inc(v_tail_112_);
lean_dec_ref(v_env_109_);
lean_inc(v_00_u03c3s_108_);
v___x_113_ = l_Std_Do_SPred_conjunction(v_00_u03c3s_108_, v_tail_112_);
v___x_114_ = l_Std_Do_SPred_and(v_00_u03c3s_108_, v_head_111_, v___x_113_);
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_conjunction_match__1_splitter___redArg(lean_object* v_env_115_, lean_object* v_h__1_116_, lean_object* v_h__2_117_){
_start:
{
if (lean_obj_tag(v_env_115_) == 0)
{
lean_object* v___x_118_; lean_object* v___x_119_; 
lean_dec(v_h__2_117_);
v___x_118_ = lean_box(0);
v___x_119_ = lean_apply_1(v_h__1_116_, v___x_118_);
return v___x_119_;
}
else
{
lean_object* v_head_120_; lean_object* v_tail_121_; lean_object* v___x_122_; 
lean_dec(v_h__1_116_);
v_head_120_ = lean_ctor_get(v_env_115_, 0);
lean_inc(v_head_120_);
v_tail_121_ = lean_ctor_get(v_env_115_, 1);
lean_inc(v_tail_121_);
lean_dec_ref(v_env_115_);
v___x_122_ = lean_apply_2(v_h__2_117_, v_head_120_, v_tail_121_);
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_conjunction_match__1_splitter(lean_object* v_00_u03c3s_123_, lean_object* v_motive_124_, lean_object* v_env_125_, lean_object* v_h__1_126_, lean_object* v_h__2_127_){
_start:
{
if (lean_obj_tag(v_env_125_) == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; 
lean_dec(v_h__2_127_);
v___x_128_ = lean_box(0);
v___x_129_ = lean_apply_1(v_h__1_126_, v___x_128_);
return v___x_129_;
}
else
{
lean_object* v_head_130_; lean_object* v_tail_131_; lean_object* v___x_132_; 
lean_dec(v_h__1_126_);
v_head_130_ = lean_ctor_get(v_env_125_, 0);
lean_inc(v_head_130_);
v_tail_131_ = lean_ctor_get(v_env_125_, 1);
lean_inc(v_tail_131_);
lean_dec_ref(v_env_125_);
v___x_132_ = lean_apply_2(v_h__2_127_, v_head_130_, v_tail_131_);
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_conjunction_match__1_splitter___boxed(lean_object* v_00_u03c3s_133_, lean_object* v_motive_134_, lean_object* v_env_135_, lean_object* v_h__1_136_, lean_object* v_h__2_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_conjunction_match__1_splitter(v_00_u03c3s_133_, v_motive_134_, v_env_135_, v_h__1_136_, v_h__2_137_);
lean_dec(v_00_u03c3s_133_);
return v_res_138_;
}
}
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Std_Do_SPred_SVal(uint8_t builtin);
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Do_SPred_SPred(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Do_SPred_SVal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Do_SPred_SPred(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Std_Do_SPred_SVal(uint8_t builtin);
lean_object* initialize_Init_NotationExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Do_SPred_SPred(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Do_SPred_SVal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Do_SPred_SPred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Do_SPred_SPred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Do_SPred_SPred(builtin);
}
#ifdef __cplusplus
}
#endif
