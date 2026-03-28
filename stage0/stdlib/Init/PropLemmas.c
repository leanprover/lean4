// Lean compiler output
// Module: Init.PropLemmas
// Imports: public import Init.NotationExtra
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
LEAN_EXPORT lean_object* l_Or_by__cases___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Or_by__cases___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Or_by__cases(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Or_by__cases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Or_by__cases_x27___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Or_by__cases_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Or_by__cases_x27(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Or_by__cases_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_exists__prop__decidable___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_exists__prop__decidable___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_exists__prop__decidable(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_exists__prop__decidable___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_forall__prop__decidable___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_forall__prop__decidable___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_forall__prop__decidable(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_forall__prop__decidable___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_decidable__of__iff___redArg(uint8_t);
LEAN_EXPORT lean_object* l_decidable__of__iff___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_decidable__of__iff(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_decidable__of__iff___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_decidable__of__iff_x27___redArg(uint8_t);
LEAN_EXPORT lean_object* l_decidable__of__iff_x27___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_decidable__of__iff_x27(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_decidable__of__iff_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Decidable_predToBool___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Decidable_predToBool___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Decidable_predToBool___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Decidable_predToBool(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidablePredComp___aux__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidablePredComp___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidablePredComp___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidablePredComp___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidablePredComp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidablePredComp___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidablePredComp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidablePredComp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_decidable__of__bool___redArg(uint8_t);
LEAN_EXPORT lean_object* l_decidable__of__bool___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_decidable__of__bool(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_decidable__of__bool___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Or_by__cases___redArg(uint8_t v_inst_1_, lean_object* v_h_u2081_2_, lean_object* v_h_u2082_3_){
_start:
{
if (v_inst_1_ == 0)
{
lean_object* v___x_4_; 
lean_dec(v_h_u2081_2_);
v___x_4_ = lean_apply_1(v_h_u2082_3_, lean_box(0));
return v___x_4_;
}
else
{
lean_object* v___x_5_; 
lean_dec(v_h_u2082_3_);
v___x_5_ = lean_apply_1(v_h_u2081_2_, lean_box(0));
return v___x_5_;
}
}
}
LEAN_EXPORT lean_object* l_Or_by__cases___redArg___boxed(lean_object* v_inst_6_, lean_object* v_h_u2081_7_, lean_object* v_h_u2082_8_){
_start:
{
uint8_t v_inst_8__boxed_9_; lean_object* v_res_10_; 
v_inst_8__boxed_9_ = lean_unbox(v_inst_6_);
v_res_10_ = l_Or_by__cases___redArg(v_inst_8__boxed_9_, v_h_u2081_7_, v_h_u2082_8_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Or_by__cases(lean_object* v_p_11_, lean_object* v_q_12_, uint8_t v_inst_13_, lean_object* v_00_u03b1_14_, lean_object* v_h_15_, lean_object* v_h_u2081_16_, lean_object* v_h_u2082_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Or_by__cases___redArg(v_inst_13_, v_h_u2081_16_, v_h_u2082_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Or_by__cases___boxed(lean_object* v_p_19_, lean_object* v_q_20_, lean_object* v_inst_21_, lean_object* v_00_u03b1_22_, lean_object* v_h_23_, lean_object* v_h_u2081_24_, lean_object* v_h_u2082_25_){
_start:
{
uint8_t v_inst_15__boxed_26_; lean_object* v_res_27_; 
v_inst_15__boxed_26_ = lean_unbox(v_inst_21_);
v_res_27_ = l_Or_by__cases(v_p_19_, v_q_20_, v_inst_15__boxed_26_, v_00_u03b1_22_, v_h_23_, v_h_u2081_24_, v_h_u2082_25_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Or_by__cases_x27___redArg(uint8_t v_inst_28_, lean_object* v_h_u2081_29_, lean_object* v_h_u2082_30_){
_start:
{
if (v_inst_28_ == 0)
{
lean_object* v___x_31_; 
lean_dec(v_h_u2082_30_);
v___x_31_ = lean_apply_1(v_h_u2081_29_, lean_box(0));
return v___x_31_;
}
else
{
lean_object* v___x_32_; 
lean_dec(v_h_u2081_29_);
v___x_32_ = lean_apply_1(v_h_u2082_30_, lean_box(0));
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* l_Or_by__cases_x27___redArg___boxed(lean_object* v_inst_33_, lean_object* v_h_u2081_34_, lean_object* v_h_u2082_35_){
_start:
{
uint8_t v_inst_8__boxed_36_; lean_object* v_res_37_; 
v_inst_8__boxed_36_ = lean_unbox(v_inst_33_);
v_res_37_ = l_Or_by__cases_x27___redArg(v_inst_8__boxed_36_, v_h_u2081_34_, v_h_u2082_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Or_by__cases_x27(lean_object* v_q_38_, lean_object* v_p_39_, uint8_t v_inst_40_, lean_object* v_00_u03b1_41_, lean_object* v_h_42_, lean_object* v_h_u2081_43_, lean_object* v_h_u2082_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Or_by__cases_x27___redArg(v_inst_40_, v_h_u2081_43_, v_h_u2082_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Or_by__cases_x27___boxed(lean_object* v_q_46_, lean_object* v_p_47_, lean_object* v_inst_48_, lean_object* v_00_u03b1_49_, lean_object* v_h_50_, lean_object* v_h_u2081_51_, lean_object* v_h_u2082_52_){
_start:
{
uint8_t v_inst_15__boxed_53_; lean_object* v_res_54_; 
v_inst_15__boxed_53_ = lean_unbox(v_inst_48_);
v_res_54_ = l_Or_by__cases_x27(v_q_46_, v_p_47_, v_inst_15__boxed_53_, v_00_u03b1_49_, v_h_50_, v_h_u2081_51_, v_h_u2082_52_);
return v_res_54_;
}
}
LEAN_EXPORT uint8_t l_exists__prop__decidable___redArg(uint8_t v_inst_55_, lean_object* v_inst_56_){
_start:
{
if (v_inst_55_ == 0)
{
lean_dec_ref(v_inst_56_);
return v_inst_55_;
}
else
{
lean_object* v___x_57_; uint8_t v___x_58_; 
v___x_57_ = lean_apply_1(v_inst_56_, lean_box(0));
v___x_58_ = lean_unbox(v___x_57_);
return v___x_58_;
}
}
}
LEAN_EXPORT lean_object* l_exists__prop__decidable___redArg___boxed(lean_object* v_inst_59_, lean_object* v_inst_60_){
_start:
{
uint8_t v_inst_14__boxed_61_; uint8_t v_res_62_; lean_object* v_r_63_; 
v_inst_14__boxed_61_ = lean_unbox(v_inst_59_);
v_res_62_ = l_exists__prop__decidable___redArg(v_inst_14__boxed_61_, v_inst_60_);
v_r_63_ = lean_box(v_res_62_);
return v_r_63_;
}
}
LEAN_EXPORT uint8_t l_exists__prop__decidable(lean_object* v_p_64_, lean_object* v_P_65_, uint8_t v_inst_66_, lean_object* v_inst_67_){
_start:
{
if (v_inst_66_ == 0)
{
lean_dec_ref(v_inst_67_);
return v_inst_66_;
}
else
{
lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_68_ = lean_apply_1(v_inst_67_, lean_box(0));
v___x_69_ = lean_unbox(v___x_68_);
return v___x_69_;
}
}
}
LEAN_EXPORT lean_object* l_exists__prop__decidable___boxed(lean_object* v_p_70_, lean_object* v_P_71_, lean_object* v_inst_72_, lean_object* v_inst_73_){
_start:
{
uint8_t v_inst_24__boxed_74_; uint8_t v_res_75_; lean_object* v_r_76_; 
v_inst_24__boxed_74_ = lean_unbox(v_inst_72_);
v_res_75_ = l_exists__prop__decidable(v_p_70_, v_P_71_, v_inst_24__boxed_74_, v_inst_73_);
v_r_76_ = lean_box(v_res_75_);
return v_r_76_;
}
}
LEAN_EXPORT uint8_t l_forall__prop__decidable___redArg(uint8_t v_inst_77_, lean_object* v_inst_78_){
_start:
{
if (v_inst_77_ == 0)
{
uint8_t v___x_79_; 
lean_dec_ref(v_inst_78_);
v___x_79_ = 1;
return v___x_79_;
}
else
{
lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_80_ = lean_apply_1(v_inst_78_, lean_box(0));
v___x_81_ = lean_unbox(v___x_80_);
return v___x_81_;
}
}
}
LEAN_EXPORT lean_object* l_forall__prop__decidable___redArg___boxed(lean_object* v_inst_82_, lean_object* v_inst_83_){
_start:
{
uint8_t v_inst_15__boxed_84_; uint8_t v_res_85_; lean_object* v_r_86_; 
v_inst_15__boxed_84_ = lean_unbox(v_inst_82_);
v_res_85_ = l_forall__prop__decidable___redArg(v_inst_15__boxed_84_, v_inst_83_);
v_r_86_ = lean_box(v_res_85_);
return v_r_86_;
}
}
LEAN_EXPORT uint8_t l_forall__prop__decidable(lean_object* v_p_87_, lean_object* v_P_88_, uint8_t v_inst_89_, lean_object* v_inst_90_){
_start:
{
if (v_inst_89_ == 0)
{
uint8_t v___x_91_; 
lean_dec_ref(v_inst_90_);
v___x_91_ = 1;
return v___x_91_;
}
else
{
lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_92_ = lean_apply_1(v_inst_90_, lean_box(0));
v___x_93_ = lean_unbox(v___x_92_);
return v___x_93_;
}
}
}
LEAN_EXPORT lean_object* l_forall__prop__decidable___boxed(lean_object* v_p_94_, lean_object* v_P_95_, lean_object* v_inst_96_, lean_object* v_inst_97_){
_start:
{
uint8_t v_inst_27__boxed_98_; uint8_t v_res_99_; lean_object* v_r_100_; 
v_inst_27__boxed_98_ = lean_unbox(v_inst_96_);
v_res_99_ = l_forall__prop__decidable(v_p_94_, v_P_95_, v_inst_27__boxed_98_, v_inst_97_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
LEAN_EXPORT uint8_t l_decidable__of__iff___redArg(uint8_t v_inst_101_){
_start:
{
return v_inst_101_;
}
}
LEAN_EXPORT lean_object* l_decidable__of__iff___redArg___boxed(lean_object* v_inst_102_){
_start:
{
uint8_t v_inst_8__boxed_103_; uint8_t v_res_104_; lean_object* v_r_105_; 
v_inst_8__boxed_103_ = lean_unbox(v_inst_102_);
v_res_104_ = l_decidable__of__iff___redArg(v_inst_8__boxed_103_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
LEAN_EXPORT uint8_t l_decidable__of__iff(lean_object* v_b_106_, lean_object* v_a_107_, lean_object* v_h_108_, uint8_t v_inst_109_){
_start:
{
return v_inst_109_;
}
}
LEAN_EXPORT lean_object* l_decidable__of__iff___boxed(lean_object* v_b_110_, lean_object* v_a_111_, lean_object* v_h_112_, lean_object* v_inst_113_){
_start:
{
uint8_t v_inst_11__boxed_114_; uint8_t v_res_115_; lean_object* v_r_116_; 
v_inst_11__boxed_114_ = lean_unbox(v_inst_113_);
v_res_115_ = l_decidable__of__iff(v_b_110_, v_a_111_, v_h_112_, v_inst_11__boxed_114_);
v_r_116_ = lean_box(v_res_115_);
return v_r_116_;
}
}
LEAN_EXPORT uint8_t l_decidable__of__iff_x27___redArg(uint8_t v_inst_117_){
_start:
{
return v_inst_117_;
}
}
LEAN_EXPORT lean_object* l_decidable__of__iff_x27___redArg___boxed(lean_object* v_inst_118_){
_start:
{
uint8_t v_inst_8__boxed_119_; uint8_t v_res_120_; lean_object* v_r_121_; 
v_inst_8__boxed_119_ = lean_unbox(v_inst_118_);
v_res_120_ = l_decidable__of__iff_x27___redArg(v_inst_8__boxed_119_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
LEAN_EXPORT uint8_t l_decidable__of__iff_x27(lean_object* v_a_122_, lean_object* v_b_123_, lean_object* v_h_124_, uint8_t v_inst_125_){
_start:
{
return v_inst_125_;
}
}
LEAN_EXPORT lean_object* l_decidable__of__iff_x27___boxed(lean_object* v_a_126_, lean_object* v_b_127_, lean_object* v_h_128_, lean_object* v_inst_129_){
_start:
{
uint8_t v_inst_11__boxed_130_; uint8_t v_res_131_; lean_object* v_r_132_; 
v_inst_11__boxed_130_ = lean_unbox(v_inst_129_);
v_res_131_ = l_decidable__of__iff_x27(v_a_126_, v_b_127_, v_h_128_, v_inst_11__boxed_130_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
LEAN_EXPORT uint8_t l_Decidable_predToBool___redArg___lam__0(lean_object* v_inst_133_, lean_object* v_b_134_){
_start:
{
lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_135_ = lean_apply_1(v_inst_133_, v_b_134_);
v___x_136_ = lean_unbox(v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Decidable_predToBool___redArg___lam__0___boxed(lean_object* v_inst_137_, lean_object* v_b_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l_Decidable_predToBool___redArg___lam__0(v_inst_137_, v_b_138_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT lean_object* l_Decidable_predToBool___redArg(lean_object* v_inst_141_){
_start:
{
lean_object* v___f_142_; 
v___f_142_ = lean_alloc_closure((void*)(l_Decidable_predToBool___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_142_, 0, v_inst_141_);
return v___f_142_;
}
}
LEAN_EXPORT lean_object* l_Decidable_predToBool(lean_object* v_00_u03b1_143_, lean_object* v_p_144_, lean_object* v_inst_145_){
_start:
{
lean_object* v___f_146_; 
v___f_146_ = lean_alloc_closure((void*)(l_Decidable_predToBool___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_146_, 0, v_inst_145_);
return v___f_146_;
}
}
LEAN_EXPORT uint8_t l_instDecidablePredComp___aux__1___redArg(lean_object* v_f_147_, lean_object* v_inst_148_, lean_object* v_x_149_){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_150_ = lean_apply_1(v_f_147_, v_x_149_);
v___x_151_ = lean_apply_1(v_inst_148_, v___x_150_);
v___x_152_ = lean_unbox(v___x_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_instDecidablePredComp___aux__1___redArg___boxed(lean_object* v_f_153_, lean_object* v_inst_154_, lean_object* v_x_155_){
_start:
{
uint8_t v_res_156_; lean_object* v_r_157_; 
v_res_156_ = l_instDecidablePredComp___aux__1___redArg(v_f_153_, v_inst_154_, v_x_155_);
v_r_157_ = lean_box(v_res_156_);
return v_r_157_;
}
}
LEAN_EXPORT uint8_t l_instDecidablePredComp___aux__1(lean_object* v_00_u03b1_158_, lean_object* v_p_159_, lean_object* v_00_u03b1_160_, lean_object* v_f_161_, lean_object* v_inst_162_, lean_object* v_x_163_){
_start:
{
uint8_t v___x_164_; 
v___x_164_ = l_instDecidablePredComp___aux__1___redArg(v_f_161_, v_inst_162_, v_x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_instDecidablePredComp___aux__1___boxed(lean_object* v_00_u03b1_165_, lean_object* v_p_166_, lean_object* v_00_u03b1_167_, lean_object* v_f_168_, lean_object* v_inst_169_, lean_object* v_x_170_){
_start:
{
uint8_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l_instDecidablePredComp___aux__1(v_00_u03b1_165_, v_p_166_, v_00_u03b1_167_, v_f_168_, v_inst_169_, v_x_170_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT uint8_t l_instDecidablePredComp___redArg(lean_object* v_f_173_, lean_object* v_inst_174_, lean_object* v_x_175_){
_start:
{
uint8_t v___x_176_; 
v___x_176_ = l_instDecidablePredComp___aux__1___redArg(v_f_173_, v_inst_174_, v_x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_instDecidablePredComp___redArg___boxed(lean_object* v_f_177_, lean_object* v_inst_178_, lean_object* v_x_179_){
_start:
{
uint8_t v_res_180_; lean_object* v_r_181_; 
v_res_180_ = l_instDecidablePredComp___redArg(v_f_177_, v_inst_178_, v_x_179_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
LEAN_EXPORT uint8_t l_instDecidablePredComp(lean_object* v_00_u03b1_182_, lean_object* v_p_183_, lean_object* v_00_u03b1_184_, lean_object* v_f_185_, lean_object* v_inst_186_, lean_object* v_x_187_){
_start:
{
uint8_t v___x_188_; 
v___x_188_ = l_instDecidablePredComp___aux__1___redArg(v_f_185_, v_inst_186_, v_x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_instDecidablePredComp___boxed(lean_object* v_00_u03b1_189_, lean_object* v_p_190_, lean_object* v_00_u03b1_191_, lean_object* v_f_192_, lean_object* v_inst_193_, lean_object* v_x_194_){
_start:
{
uint8_t v_res_195_; lean_object* v_r_196_; 
v_res_195_ = l_instDecidablePredComp(v_00_u03b1_189_, v_p_190_, v_00_u03b1_191_, v_f_192_, v_inst_193_, v_x_194_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT uint8_t l_decidable__of__bool___redArg(uint8_t v_x_197_){
_start:
{
return v_x_197_;
}
}
LEAN_EXPORT lean_object* l_decidable__of__bool___redArg___boxed(lean_object* v_x_198_){
_start:
{
uint8_t v_x_36__boxed_199_; uint8_t v_res_200_; lean_object* v_r_201_; 
v_x_36__boxed_199_ = lean_unbox(v_x_198_);
v_res_200_ = l_decidable__of__bool___redArg(v_x_36__boxed_199_);
v_r_201_ = lean_box(v_res_200_);
return v_r_201_;
}
}
LEAN_EXPORT uint8_t l_decidable__of__bool(lean_object* v_a_202_, uint8_t v_x_203_, lean_object* v_x_204_){
_start:
{
return v_x_203_;
}
}
LEAN_EXPORT lean_object* l_decidable__of__bool___boxed(lean_object* v_a_205_, lean_object* v_x_206_, lean_object* v_x_207_){
_start:
{
uint8_t v_x_39__boxed_208_; uint8_t v_res_209_; lean_object* v_r_210_; 
v_x_39__boxed_208_ = lean_unbox(v_x_206_);
v_res_209_ = l_decidable__of__bool(v_a_205_, v_x_39__boxed_208_, v_x_207_);
v_r_210_ = lean_box(v_res_209_);
return v_r_210_;
}
}
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_PropLemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_NotationExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_PropLemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_PropLemmas(builtin);
}
#ifdef __cplusplus
}
#endif
