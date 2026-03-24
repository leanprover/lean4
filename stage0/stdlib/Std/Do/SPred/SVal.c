// Lean compiler output
// Module: Std.Do.SPred.SVal
// Imports: public import Init.Data.List.Notation import Init.SimpLemmas public import Init.Core import Init.Grind.Attr
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
LEAN_EXPORT lean_object* l_Std_Do_SVal_instInhabitedStateTupleNil;
LEAN_EXPORT lean_object* l_Std_Do_SVal_instInhabitedStateTupleCons___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SVal_instInhabitedStateTupleCons(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SVal_instInhabitedStateTupleCons___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SVal_curry___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SVal_curry___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SVal_curry___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SVal_curry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SVal_uncurry___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SVal_uncurry___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SVal_uncurry(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SVal_uncurry___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SVal_0__Std_Do_SVal_uncurry_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SVal_0__Std_Do_SVal_uncurry_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SVal_0__Std_Do_SVal_uncurry_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SVal_0__Std_Do_SVal_uncurry_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SVal_0__Std_Do_SVal_uncurry_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SVal_0__Std_Do_SVal_curry_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SVal_0__Std_Do_SVal_curry_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SVal_instInhabited___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SVal_instInhabited___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SVal_instInhabited___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SVal_instInhabited(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SVal_instGetTyCons___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SVal_instGetTyCons___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SVal_instGetTyCons___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SVal_instGetTyCons___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SVal_instGetTyCons(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SVal_instGetTyCons__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SVal_instGetTyCons__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SVal_instGetTyCons__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SVal_getThe___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SVal_getThe___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SVal_getThe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SVal_getThe___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Std_Do_SVal_instInhabitedStateTupleNil(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_instInhabitedStateTupleCons___redArg(lean_object* v_inst_2_, lean_object* v_inst_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4_, 0, v_inst_2_);
lean_ctor_set(v___x_4_, 1, v_inst_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_instInhabitedStateTupleCons(lean_object* v_00_u03c3_5_, lean_object* v_00_u03c3s_6_, lean_object* v_inst_7_, lean_object* v_inst_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_9_, 0, v_inst_7_);
lean_ctor_set(v___x_9_, 1, v_inst_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_instInhabitedStateTupleCons___boxed(lean_object* v_00_u03c3_10_, lean_object* v_00_u03c3s_11_, lean_object* v_inst_12_, lean_object* v_inst_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_Do_SVal_instInhabitedStateTupleCons(v_00_u03c3_10_, v_00_u03c3s_11_, v_inst_12_, v_inst_13_);
lean_dec(v_00_u03c3s_11_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_curry___redArg___lam__0(lean_object* v___y_15_, lean_object* v_f_16_, lean_object* v_s_x27_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_18_, 0, v___y_15_);
lean_ctor_set(v___x_18_, 1, v_s_x27_17_);
v___x_19_ = lean_apply_1(v_f_16_, v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_curry___redArg(lean_object* v_00_u03c3s_20_, lean_object* v_f_21_){
_start:
{
if (lean_obj_tag(v_00_u03c3s_20_) == 0)
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_box(0);
v___x_23_ = lean_apply_1(v_f_21_, v___x_22_);
return v___x_23_;
}
else
{
lean_object* v_tail_24_; lean_object* v___f_25_; 
v_tail_24_ = lean_ctor_get(v_00_u03c3s_20_, 1);
lean_inc(v_tail_24_);
lean_dec_ref(v_00_u03c3s_20_);
v___f_25_ = lean_alloc_closure((void*)(l_Std_Do_SVal_curry___redArg___lam__1), 3, 2);
lean_closure_set(v___f_25_, 0, v_f_21_);
lean_closure_set(v___f_25_, 1, v_tail_24_);
return v___f_25_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_curry___redArg___lam__1(lean_object* v_f_26_, lean_object* v_tail_27_, lean_object* v___y_28_){
_start:
{
lean_object* v___f_29_; lean_object* v___x_30_; 
v___f_29_ = lean_alloc_closure((void*)(l_Std_Do_SVal_curry___redArg___lam__0), 3, 2);
lean_closure_set(v___f_29_, 0, v___y_28_);
lean_closure_set(v___f_29_, 1, v_f_26_);
v___x_30_ = l_Std_Do_SVal_curry___redArg(v_tail_27_, v___f_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_curry(lean_object* v_00_u03b1_31_, lean_object* v_00_u03c3s_32_, lean_object* v_f_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Std_Do_SVal_curry___redArg(v_00_u03c3s_32_, v_f_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_uncurry___redArg(lean_object* v_00_u03c3s_35_, lean_object* v_f_36_, lean_object* v_a_37_){
_start:
{
if (lean_obj_tag(v_00_u03c3s_35_) == 0)
{
lean_dec(v_a_37_);
return v_f_36_;
}
else
{
lean_object* v_tail_38_; lean_object* v_fst_39_; lean_object* v_snd_40_; lean_object* v___x_41_; 
v_tail_38_ = lean_ctor_get(v_00_u03c3s_35_, 1);
v_fst_39_ = lean_ctor_get(v_a_37_, 0);
lean_inc(v_fst_39_);
v_snd_40_ = lean_ctor_get(v_a_37_, 1);
lean_inc(v_snd_40_);
lean_dec(v_a_37_);
v___x_41_ = lean_apply_1(v_f_36_, v_fst_39_);
v_00_u03c3s_35_ = v_tail_38_;
v_f_36_ = v___x_41_;
v_a_37_ = v_snd_40_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_uncurry___redArg___boxed(lean_object* v_00_u03c3s_43_, lean_object* v_f_44_, lean_object* v_a_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Std_Do_SVal_uncurry___redArg(v_00_u03c3s_43_, v_f_44_, v_a_45_);
lean_dec(v_00_u03c3s_43_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_uncurry(lean_object* v_00_u03b1_47_, lean_object* v_00_u03c3s_48_, lean_object* v_f_49_, lean_object* v_a_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Std_Do_SVal_uncurry___redArg(v_00_u03c3s_48_, v_f_49_, v_a_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_uncurry___boxed(lean_object* v_00_u03b1_52_, lean_object* v_00_u03c3s_53_, lean_object* v_f_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Std_Do_SVal_uncurry(v_00_u03b1_52_, v_00_u03c3s_53_, v_f_54_, v_a_55_);
lean_dec(v_00_u03c3s_53_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SVal_0__Std_Do_SVal_uncurry_match__3_splitter___redArg(lean_object* v_00_u03c3s_57_, lean_object* v_f_58_, lean_object* v_h__1_59_, lean_object* v_h__2_60_){
_start:
{
if (lean_obj_tag(v_00_u03c3s_57_) == 0)
{
lean_object* v___x_61_; 
lean_dec(v_h__2_60_);
v___x_61_ = lean_apply_1(v_h__1_59_, v_f_58_);
return v___x_61_;
}
else
{
lean_object* v_tail_62_; lean_object* v___x_63_; 
lean_dec(v_h__1_59_);
v_tail_62_ = lean_ctor_get(v_00_u03c3s_57_, 1);
lean_inc(v_tail_62_);
lean_dec_ref(v_00_u03c3s_57_);
v___x_63_ = lean_apply_3(v_h__2_60_, lean_box(0), v_tail_62_, v_f_58_);
return v___x_63_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SVal_0__Std_Do_SVal_uncurry_match__3_splitter(lean_object* v_00_u03b1_64_, lean_object* v_motive_65_, lean_object* v_00_u03c3s_66_, lean_object* v_f_67_, lean_object* v_h__1_68_, lean_object* v_h__2_69_){
_start:
{
if (lean_obj_tag(v_00_u03c3s_66_) == 0)
{
lean_object* v___x_70_; 
lean_dec(v_h__2_69_);
v___x_70_ = lean_apply_1(v_h__1_68_, v_f_67_);
return v___x_70_;
}
else
{
lean_object* v_tail_71_; lean_object* v___x_72_; 
lean_dec(v_h__1_68_);
v_tail_71_ = lean_ctor_get(v_00_u03c3s_66_, 1);
lean_inc(v_tail_71_);
lean_dec_ref(v_00_u03c3s_66_);
v___x_72_ = lean_apply_3(v_h__2_69_, lean_box(0), v_tail_71_, v_f_67_);
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SVal_0__Std_Do_SVal_uncurry_match__1_splitter___redArg(lean_object* v_x_73_, lean_object* v_h__1_74_){
_start:
{
lean_object* v_fst_75_; lean_object* v_snd_76_; lean_object* v___x_77_; 
v_fst_75_ = lean_ctor_get(v_x_73_, 0);
lean_inc(v_fst_75_);
v_snd_76_ = lean_ctor_get(v_x_73_, 1);
lean_inc(v_snd_76_);
lean_dec_ref(v_x_73_);
v___x_77_ = lean_apply_2(v_h__1_74_, v_fst_75_, v_snd_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SVal_0__Std_Do_SVal_uncurry_match__1_splitter(lean_object* v_head_78_, lean_object* v_tail_79_, lean_object* v_motive_80_, lean_object* v_x_81_, lean_object* v_h__1_82_){
_start:
{
lean_object* v_fst_83_; lean_object* v_snd_84_; lean_object* v___x_85_; 
v_fst_83_ = lean_ctor_get(v_x_81_, 0);
lean_inc(v_fst_83_);
v_snd_84_ = lean_ctor_get(v_x_81_, 1);
lean_inc(v_snd_84_);
lean_dec_ref(v_x_81_);
v___x_85_ = lean_apply_2(v_h__1_82_, v_fst_83_, v_snd_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SVal_0__Std_Do_SVal_uncurry_match__1_splitter___boxed(lean_object* v_head_86_, lean_object* v_tail_87_, lean_object* v_motive_88_, lean_object* v_x_89_, lean_object* v_h__1_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l___private_Std_Do_SPred_SVal_0__Std_Do_SVal_uncurry_match__1_splitter(v_head_86_, v_tail_87_, v_motive_88_, v_x_89_, v_h__1_90_);
lean_dec(v_tail_87_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SVal_0__Std_Do_SVal_curry_match__1_splitter___redArg(lean_object* v_00_u03c3s_92_, lean_object* v_f_93_, lean_object* v_h__1_94_, lean_object* v_h__2_95_){
_start:
{
if (lean_obj_tag(v_00_u03c3s_92_) == 0)
{
lean_object* v___x_96_; 
lean_dec(v_h__2_95_);
v___x_96_ = lean_apply_1(v_h__1_94_, v_f_93_);
return v___x_96_;
}
else
{
lean_object* v_tail_97_; lean_object* v___x_98_; 
lean_dec(v_h__1_94_);
v_tail_97_ = lean_ctor_get(v_00_u03c3s_92_, 1);
lean_inc(v_tail_97_);
lean_dec_ref(v_00_u03c3s_92_);
v___x_98_ = lean_apply_3(v_h__2_95_, lean_box(0), v_tail_97_, v_f_93_);
return v___x_98_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_SPred_SVal_0__Std_Do_SVal_curry_match__1_splitter(lean_object* v_00_u03b1_99_, lean_object* v_motive_100_, lean_object* v_00_u03c3s_101_, lean_object* v_f_102_, lean_object* v_h__1_103_, lean_object* v_h__2_104_){
_start:
{
if (lean_obj_tag(v_00_u03c3s_101_) == 0)
{
lean_object* v___x_105_; 
lean_dec(v_h__2_104_);
v___x_105_ = lean_apply_1(v_h__1_103_, v_f_102_);
return v___x_105_;
}
else
{
lean_object* v_tail_106_; lean_object* v___x_107_; 
lean_dec(v_h__1_103_);
v_tail_106_ = lean_ctor_get(v_00_u03c3s_101_, 1);
lean_inc(v_tail_106_);
lean_dec_ref(v_00_u03c3s_101_);
v___x_107_ = lean_apply_3(v_h__2_104_, lean_box(0), v_tail_106_, v_f_102_);
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_instInhabited___redArg___lam__0(lean_object* v_inst_108_, lean_object* v_x_109_){
_start:
{
lean_inc(v_inst_108_);
return v_inst_108_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_instInhabited___redArg___lam__0___boxed(lean_object* v_inst_110_, lean_object* v_x_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Std_Do_SVal_instInhabited___redArg___lam__0(v_inst_110_, v_x_111_);
lean_dec(v_x_111_);
lean_dec(v_inst_110_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_instInhabited___redArg(lean_object* v_00_u03c3s_113_, lean_object* v_inst_114_){
_start:
{
lean_object* v___f_115_; lean_object* v___x_116_; 
v___f_115_ = lean_alloc_closure((void*)(l_Std_Do_SVal_instInhabited___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_115_, 0, v_inst_114_);
v___x_116_ = l_Std_Do_SVal_curry___redArg(v_00_u03c3s_113_, v___f_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_instInhabited(lean_object* v_00_u03b1_117_, lean_object* v_00_u03c3s_118_, lean_object* v_inst_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Std_Do_SVal_instInhabited___redArg(v_00_u03c3s_118_, v_inst_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_instGetTyCons___redArg___lam__0(lean_object* v_s_121_, lean_object* v_x_122_){
_start:
{
lean_inc(v_s_121_);
return v_s_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_instGetTyCons___redArg___lam__0___boxed(lean_object* v_s_123_, lean_object* v_x_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Std_Do_SVal_instGetTyCons___redArg___lam__0(v_s_123_, v_x_124_);
lean_dec(v_x_124_);
lean_dec(v_s_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_instGetTyCons___redArg___lam__1(lean_object* v_00_u03c3s_126_, lean_object* v_s_127_){
_start:
{
lean_object* v___f_128_; lean_object* v___x_129_; 
v___f_128_ = lean_alloc_closure((void*)(l_Std_Do_SVal_instGetTyCons___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_128_, 0, v_s_127_);
v___x_129_ = l_Std_Do_SVal_curry___redArg(v_00_u03c3s_126_, v___f_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_instGetTyCons___redArg(lean_object* v_00_u03c3s_130_){
_start:
{
lean_object* v___f_131_; 
v___f_131_ = lean_alloc_closure((void*)(l_Std_Do_SVal_instGetTyCons___redArg___lam__1), 2, 1);
lean_closure_set(v___f_131_, 0, v_00_u03c3s_130_);
return v___f_131_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_instGetTyCons(lean_object* v_00_u03c3_132_, lean_object* v_00_u03c3s_133_){
_start:
{
lean_object* v___f_134_; 
v___f_134_ = lean_alloc_closure((void*)(l_Std_Do_SVal_instGetTyCons___redArg___lam__1), 2, 1);
lean_closure_set(v___f_134_, 0, v_00_u03c3s_133_);
return v___f_134_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_instGetTyCons__1___redArg(lean_object* v_inst_135_){
_start:
{
lean_object* v___f_136_; 
v___f_136_ = lean_alloc_closure((void*)(l_Std_Do_SVal_instInhabited___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_136_, 0, v_inst_135_);
return v___f_136_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_instGetTyCons__1(lean_object* v_00_u03c3_u2081_137_, lean_object* v_00_u03c3s_138_, lean_object* v_00_u03c3_u2082_139_, lean_object* v_inst_140_){
_start:
{
lean_object* v___f_141_; 
v___f_141_ = lean_alloc_closure((void*)(l_Std_Do_SVal_instInhabited___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_141_, 0, v_inst_140_);
return v___f_141_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_instGetTyCons__1___boxed(lean_object* v_00_u03c3_u2081_142_, lean_object* v_00_u03c3s_143_, lean_object* v_00_u03c3_u2082_144_, lean_object* v_inst_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Std_Do_SVal_instGetTyCons__1(v_00_u03c3_u2081_142_, v_00_u03c3s_143_, v_00_u03c3_u2082_144_, v_inst_145_);
lean_dec(v_00_u03c3s_143_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_getThe___redArg(lean_object* v_inst_147_){
_start:
{
lean_inc(v_inst_147_);
return v_inst_147_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_getThe___redArg___boxed(lean_object* v_inst_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Std_Do_SVal_getThe___redArg(v_inst_148_);
lean_dec(v_inst_148_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_getThe(lean_object* v_00_u03c3s_150_, lean_object* v_00_u03c3_151_, lean_object* v_inst_152_){
_start:
{
lean_inc(v_inst_152_);
return v_inst_152_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SVal_getThe___boxed(lean_object* v_00_u03c3s_153_, lean_object* v_00_u03c3_154_, lean_object* v_inst_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Std_Do_SVal_getThe(v_00_u03c3s_153_, v_00_u03c3_154_, v_inst_155_);
lean_dec(v_inst_155_);
lean_dec(v_00_u03c3s_153_);
return v_res_156_;
}
}
lean_object* runtime_initialize_Init_Data_List_Notation(uint8_t builtin);
lean_object* runtime_initialize_Init_SimpLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Core(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Attr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Do_SPred_SVal(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_List_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_SimpLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Do_SVal_instInhabitedStateTupleNil = _init_l_Std_Do_SVal_instInhabitedStateTupleNil();
lean_mark_persistent(l_Std_Do_SVal_instInhabitedStateTupleNil);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Do_SPred_SVal(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_Notation(uint8_t builtin);
lean_object* initialize_Init_SimpLemmas(uint8_t builtin);
lean_object* initialize_Init_Core(uint8_t builtin);
lean_object* initialize_Init_Grind_Attr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Do_SPred_SVal(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_SimpLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Do_SPred_SVal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Do_SPred_SVal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Do_SPred_SVal(builtin);
}
#ifdef __cplusplus
}
#endif
