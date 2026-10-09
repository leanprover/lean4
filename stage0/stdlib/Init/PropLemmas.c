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
lean_object* l_Or_by__cases___redArg(uint8_t v_inst_1_, lean_object* v_h_u2081_2_, lean_object* v_h_u2082_3_){
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
LEAN_EXPORT void l_Or_by__cases___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_inst_1_ = stack[0].m_num;
lean_object* v_h_u2081_2_ = stack[1].m_obj;
lean_object* v_h_u2082_3_ = stack[2].m_obj;
lean_object* v_res_6_;
v_res_6_ = l_Or_by__cases___redArg(v_inst_1_, v_h_u2081_2_, v_h_u2082_3_);
stack->m_obj
 = v_res_6_;
}
LEAN_EXPORT lean_object* l_Or_by__cases___redArg___boxed(lean_object* v_inst_7_, lean_object* v_h_u2081_8_, lean_object* v_h_u2082_9_){
_start:
{
uint8_t v_inst_9__boxed_10_; lean_object* v_res_11_; 
v_inst_9__boxed_10_ = lean_unbox(v_inst_7_);
v_res_11_ = l_Or_by__cases___redArg(v_inst_9__boxed_10_, v_h_u2081_8_, v_h_u2082_9_);
return v_res_11_;
}
}
lean_object* l_Or_by__cases(lean_object* v_p_12_, lean_object* v_q_13_, uint8_t v_inst_14_, lean_object* v_00_u03b1_15_, lean_object* v_h_16_, lean_object* v_h_u2081_17_, lean_object* v_h_u2082_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Or_by__cases___redArg(v_inst_14_, v_h_u2081_17_, v_h_u2082_18_);
return v___x_19_;
}
}
LEAN_EXPORT void l_Or_by__cases_0interp(lean_interpreter_value* stack)
{
uint8_t v_inst_14_ = stack[2].m_num;
lean_object* v_h_u2081_17_ = stack[5].m_obj;
lean_object* v_h_u2082_18_ = stack[6].m_obj;
lean_object* v_res_20_;
v_res_20_ = l_Or_by__cases(lean_box(0), lean_box(0), v_inst_14_, lean_box(0), lean_box(0), v_h_u2081_17_, v_h_u2082_18_);
stack->m_obj
 = v_res_20_;
}
LEAN_EXPORT lean_object* l_Or_by__cases___boxed(lean_object* v_p_21_, lean_object* v_q_22_, lean_object* v_inst_23_, lean_object* v_00_u03b1_24_, lean_object* v_h_25_, lean_object* v_h_u2081_26_, lean_object* v_h_u2082_27_){
_start:
{
uint8_t v_inst_20__boxed_28_; lean_object* v_res_29_; 
v_inst_20__boxed_28_ = lean_unbox(v_inst_23_);
v_res_29_ = l_Or_by__cases(v_p_21_, v_q_22_, v_inst_20__boxed_28_, v_00_u03b1_24_, v_h_25_, v_h_u2081_26_, v_h_u2082_27_);
return v_res_29_;
}
}
lean_object* l_Or_by__cases_x27___redArg(uint8_t v_inst_30_, lean_object* v_h_u2081_31_, lean_object* v_h_u2082_32_){
_start:
{
if (v_inst_30_ == 0)
{
lean_object* v___x_33_; 
lean_dec(v_h_u2082_32_);
v___x_33_ = lean_apply_1(v_h_u2081_31_, lean_box(0));
return v___x_33_;
}
else
{
lean_object* v___x_34_; 
lean_dec(v_h_u2081_31_);
v___x_34_ = lean_apply_1(v_h_u2082_32_, lean_box(0));
return v___x_34_;
}
}
}
LEAN_EXPORT void l_Or_by__cases_x27___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_inst_30_ = stack[0].m_num;
lean_object* v_h_u2081_31_ = stack[1].m_obj;
lean_object* v_h_u2082_32_ = stack[2].m_obj;
lean_object* v_res_35_;
v_res_35_ = l_Or_by__cases_x27___redArg(v_inst_30_, v_h_u2081_31_, v_h_u2082_32_);
stack->m_obj
 = v_res_35_;
}
LEAN_EXPORT lean_object* l_Or_by__cases_x27___redArg___boxed(lean_object* v_inst_36_, lean_object* v_h_u2081_37_, lean_object* v_h_u2082_38_){
_start:
{
uint8_t v_inst_9__boxed_39_; lean_object* v_res_40_; 
v_inst_9__boxed_39_ = lean_unbox(v_inst_36_);
v_res_40_ = l_Or_by__cases_x27___redArg(v_inst_9__boxed_39_, v_h_u2081_37_, v_h_u2082_38_);
return v_res_40_;
}
}
lean_object* l_Or_by__cases_x27(lean_object* v_q_41_, lean_object* v_p_42_, uint8_t v_inst_43_, lean_object* v_00_u03b1_44_, lean_object* v_h_45_, lean_object* v_h_u2081_46_, lean_object* v_h_u2082_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Or_by__cases_x27___redArg(v_inst_43_, v_h_u2081_46_, v_h_u2082_47_);
return v___x_48_;
}
}
LEAN_EXPORT void l_Or_by__cases_x27_0interp(lean_interpreter_value* stack)
{
uint8_t v_inst_43_ = stack[2].m_num;
lean_object* v_h_u2081_46_ = stack[5].m_obj;
lean_object* v_h_u2082_47_ = stack[6].m_obj;
lean_object* v_res_49_;
v_res_49_ = l_Or_by__cases_x27(lean_box(0), lean_box(0), v_inst_43_, lean_box(0), lean_box(0), v_h_u2081_46_, v_h_u2082_47_);
stack->m_obj
 = v_res_49_;
}
LEAN_EXPORT lean_object* l_Or_by__cases_x27___boxed(lean_object* v_q_50_, lean_object* v_p_51_, lean_object* v_inst_52_, lean_object* v_00_u03b1_53_, lean_object* v_h_54_, lean_object* v_h_u2081_55_, lean_object* v_h_u2082_56_){
_start:
{
uint8_t v_inst_20__boxed_57_; lean_object* v_res_58_; 
v_inst_20__boxed_57_ = lean_unbox(v_inst_52_);
v_res_58_ = l_Or_by__cases_x27(v_q_50_, v_p_51_, v_inst_20__boxed_57_, v_00_u03b1_53_, v_h_54_, v_h_u2081_55_, v_h_u2082_56_);
return v_res_58_;
}
}
uint8_t l_exists__prop__decidable___redArg(uint8_t v_hp_59_, lean_object* v_hP_60_){
_start:
{
if (v_hp_59_ == 0)
{
lean_dec_ref(v_hP_60_);
return v_hp_59_;
}
else
{
lean_object* v___x_61_; uint8_t v___x_62_; 
v___x_61_ = lean_apply_1(v_hP_60_, lean_box(0));
v___x_62_ = lean_unbox(v___x_61_);
return v___x_62_;
}
}
}
LEAN_EXPORT void l_exists__prop__decidable___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_hp_59_ = stack[0].m_num;
lean_object* v_hP_60_ = stack[1].m_obj;
uint8_t v_res_63_;
v_res_63_ = l_exists__prop__decidable___redArg(v_hp_59_, v_hP_60_);
stack->m_num = v_res_63_;
}
LEAN_EXPORT lean_object* l_exists__prop__decidable___redArg___boxed(lean_object* v_hp_64_, lean_object* v_hP_65_){
_start:
{
uint8_t v_hp_boxed_66_; uint8_t v_res_67_; lean_object* v_r_68_; 
v_hp_boxed_66_ = lean_unbox(v_hp_64_);
v_res_67_ = l_exists__prop__decidable___redArg(v_hp_boxed_66_, v_hP_65_);
v_r_68_ = lean_box(v_res_67_);
return v_r_68_;
}
}
uint8_t l_exists__prop__decidable(lean_object* v_p_69_, lean_object* v_P_70_, uint8_t v_hp_71_, lean_object* v_hP_72_){
_start:
{
if (v_hp_71_ == 0)
{
lean_dec_ref(v_hP_72_);
return v_hp_71_;
}
else
{
lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_73_ = lean_apply_1(v_hP_72_, lean_box(0));
v___x_74_ = lean_unbox(v___x_73_);
return v___x_74_;
}
}
}
LEAN_EXPORT void l_exists__prop__decidable_0interp(lean_interpreter_value* stack)
{
uint8_t v_hp_71_ = stack[2].m_num;
lean_object* v_hP_72_ = stack[3].m_obj;
uint8_t v_res_75_;
v_res_75_ = l_exists__prop__decidable(lean_box(0), lean_box(0), v_hp_71_, v_hP_72_);
stack->m_num = v_res_75_;
}
LEAN_EXPORT lean_object* l_exists__prop__decidable___boxed(lean_object* v_p_76_, lean_object* v_P_77_, lean_object* v_hp_78_, lean_object* v_hP_79_){
_start:
{
uint8_t v_hp_boxed_80_; uint8_t v_res_81_; lean_object* v_r_82_; 
v_hp_boxed_80_ = lean_unbox(v_hp_78_);
v_res_81_ = l_exists__prop__decidable(v_p_76_, v_P_77_, v_hp_boxed_80_, v_hP_79_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
uint8_t l_forall__prop__decidable___redArg(uint8_t v_hp_83_, lean_object* v_hP_84_){
_start:
{
if (v_hp_83_ == 0)
{
uint8_t v___x_85_; 
lean_dec_ref(v_hP_84_);
v___x_85_ = 1;
return v___x_85_;
}
else
{
lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_86_ = lean_apply_1(v_hP_84_, lean_box(0));
v___x_87_ = lean_unbox(v___x_86_);
return v___x_87_;
}
}
}
LEAN_EXPORT void l_forall__prop__decidable___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_hp_83_ = stack[0].m_num;
lean_object* v_hP_84_ = stack[1].m_obj;
uint8_t v_res_88_;
v_res_88_ = l_forall__prop__decidable___redArg(v_hp_83_, v_hP_84_);
stack->m_num = v_res_88_;
}
LEAN_EXPORT lean_object* l_forall__prop__decidable___redArg___boxed(lean_object* v_hp_89_, lean_object* v_hP_90_){
_start:
{
uint8_t v_hp_boxed_91_; uint8_t v_res_92_; lean_object* v_r_93_; 
v_hp_boxed_91_ = lean_unbox(v_hp_89_);
v_res_92_ = l_forall__prop__decidable___redArg(v_hp_boxed_91_, v_hP_90_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
uint8_t l_forall__prop__decidable(lean_object* v_p_94_, lean_object* v_P_95_, uint8_t v_hp_96_, lean_object* v_hP_97_){
_start:
{
if (v_hp_96_ == 0)
{
uint8_t v___x_98_; 
lean_dec_ref(v_hP_97_);
v___x_98_ = 1;
return v___x_98_;
}
else
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = lean_apply_1(v_hP_97_, lean_box(0));
v___x_100_ = lean_unbox(v___x_99_);
return v___x_100_;
}
}
}
LEAN_EXPORT void l_forall__prop__decidable_0interp(lean_interpreter_value* stack)
{
uint8_t v_hp_96_ = stack[2].m_num;
lean_object* v_hP_97_ = stack[3].m_obj;
uint8_t v_res_101_;
v_res_101_ = l_forall__prop__decidable(lean_box(0), lean_box(0), v_hp_96_, v_hP_97_);
stack->m_num = v_res_101_;
}
LEAN_EXPORT lean_object* l_forall__prop__decidable___boxed(lean_object* v_p_102_, lean_object* v_P_103_, lean_object* v_hp_104_, lean_object* v_hP_105_){
_start:
{
uint8_t v_hp_boxed_106_; uint8_t v_res_107_; lean_object* v_r_108_; 
v_hp_boxed_106_ = lean_unbox(v_hp_104_);
v_res_107_ = l_forall__prop__decidable(v_p_102_, v_P_103_, v_hp_boxed_106_, v_hP_105_);
v_r_108_ = lean_box(v_res_107_);
return v_r_108_;
}
}
uint8_t l_decidable__of__iff___redArg(uint8_t v_inst_109_){
_start:
{
return v_inst_109_;
}
}
LEAN_EXPORT void l_decidable__of__iff___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_inst_109_ = stack[0].m_num;
uint8_t v_res_110_;
v_res_110_ = l_decidable__of__iff___redArg(v_inst_109_);
stack->m_num = v_res_110_;
}
LEAN_EXPORT lean_object* l_decidable__of__iff___redArg___boxed(lean_object* v_inst_111_){
_start:
{
uint8_t v_inst_8__boxed_112_; uint8_t v_res_113_; lean_object* v_r_114_; 
v_inst_8__boxed_112_ = lean_unbox(v_inst_111_);
v_res_113_ = l_decidable__of__iff___redArg(v_inst_8__boxed_112_);
v_r_114_ = lean_box(v_res_113_);
return v_r_114_;
}
}
uint8_t l_decidable__of__iff(lean_object* v_b_115_, lean_object* v_a_116_, lean_object* v_h_117_, uint8_t v_inst_118_){
_start:
{
return v_inst_118_;
}
}
LEAN_EXPORT void l_decidable__of__iff_0interp(lean_interpreter_value* stack)
{
uint8_t v_inst_118_ = stack[3].m_num;
uint8_t v_res_119_;
v_res_119_ = l_decidable__of__iff(lean_box(0), lean_box(0), lean_box(0), v_inst_118_);
stack->m_num = v_res_119_;
}
LEAN_EXPORT lean_object* l_decidable__of__iff___boxed(lean_object* v_b_120_, lean_object* v_a_121_, lean_object* v_h_122_, lean_object* v_inst_123_){
_start:
{
uint8_t v_inst_13__boxed_124_; uint8_t v_res_125_; lean_object* v_r_126_; 
v_inst_13__boxed_124_ = lean_unbox(v_inst_123_);
v_res_125_ = l_decidable__of__iff(v_b_120_, v_a_121_, v_h_122_, v_inst_13__boxed_124_);
v_r_126_ = lean_box(v_res_125_);
return v_r_126_;
}
}
uint8_t l_decidable__of__iff_x27___redArg(uint8_t v_inst_127_){
_start:
{
return v_inst_127_;
}
}
LEAN_EXPORT void l_decidable__of__iff_x27___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_inst_127_ = stack[0].m_num;
uint8_t v_res_128_;
v_res_128_ = l_decidable__of__iff_x27___redArg(v_inst_127_);
stack->m_num = v_res_128_;
}
LEAN_EXPORT lean_object* l_decidable__of__iff_x27___redArg___boxed(lean_object* v_inst_129_){
_start:
{
uint8_t v_inst_8__boxed_130_; uint8_t v_res_131_; lean_object* v_r_132_; 
v_inst_8__boxed_130_ = lean_unbox(v_inst_129_);
v_res_131_ = l_decidable__of__iff_x27___redArg(v_inst_8__boxed_130_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
uint8_t l_decidable__of__iff_x27(lean_object* v_a_133_, lean_object* v_b_134_, lean_object* v_h_135_, uint8_t v_inst_136_){
_start:
{
return v_inst_136_;
}
}
LEAN_EXPORT void l_decidable__of__iff_x27_0interp(lean_interpreter_value* stack)
{
uint8_t v_inst_136_ = stack[3].m_num;
uint8_t v_res_137_;
v_res_137_ = l_decidable__of__iff_x27(lean_box(0), lean_box(0), lean_box(0), v_inst_136_);
stack->m_num = v_res_137_;
}
LEAN_EXPORT lean_object* l_decidable__of__iff_x27___boxed(lean_object* v_a_138_, lean_object* v_b_139_, lean_object* v_h_140_, lean_object* v_inst_141_){
_start:
{
uint8_t v_inst_13__boxed_142_; uint8_t v_res_143_; lean_object* v_r_144_; 
v_inst_13__boxed_142_ = lean_unbox(v_inst_141_);
v_res_143_ = l_decidable__of__iff_x27(v_a_138_, v_b_139_, v_h_140_, v_inst_13__boxed_142_);
v_r_144_ = lean_box(v_res_143_);
return v_r_144_;
}
}
uint8_t l_Decidable_predToBool___redArg___lam__0(lean_object* v_inst_145_, lean_object* v_b_146_){
_start:
{
lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_147_ = lean_apply_1(v_inst_145_, v_b_146_);
v___x_148_ = lean_unbox(v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT void l_Decidable_predToBool___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_145_ = stack[0].m_obj;
lean_object* v_b_146_ = stack[1].m_obj;
uint8_t v_res_149_;
v_res_149_ = l_Decidable_predToBool___redArg___lam__0(v_inst_145_, v_b_146_);
stack->m_num = v_res_149_;
}
LEAN_EXPORT lean_object* l_Decidable_predToBool___redArg___lam__0___boxed(lean_object* v_inst_150_, lean_object* v_b_151_){
_start:
{
uint8_t v_res_152_; lean_object* v_r_153_; 
v_res_152_ = l_Decidable_predToBool___redArg___lam__0(v_inst_150_, v_b_151_);
v_r_153_ = lean_box(v_res_152_);
return v_r_153_;
}
}
LEAN_EXPORT lean_object* l_Decidable_predToBool___redArg(lean_object* v_inst_154_){
_start:
{
lean_object* v___f_155_; 
v___f_155_ = lean_alloc_closure((void*)(l_Decidable_predToBool___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_155_, 0, v_inst_154_);
return v___f_155_;
}
}
LEAN_EXPORT lean_object* l_Decidable_predToBool(lean_object* v_00_u03b1_156_, lean_object* v_p_157_, lean_object* v_inst_158_){
_start:
{
lean_object* v___f_159_; 
v___f_159_ = lean_alloc_closure((void*)(l_Decidable_predToBool___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_159_, 0, v_inst_158_);
return v___f_159_;
}
}
uint8_t l_instDecidablePredComp___aux__1___redArg(lean_object* v_f_160_, lean_object* v_inst_161_, lean_object* v_x_162_){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_163_ = lean_apply_1(v_f_160_, v_x_162_);
v___x_164_ = lean_apply_1(v_inst_161_, v___x_163_);
v___x_165_ = lean_unbox(v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT void l_instDecidablePredComp___aux__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_160_ = stack[0].m_obj;
lean_object* v_inst_161_ = stack[1].m_obj;
lean_object* v_x_162_ = stack[2].m_obj;
uint8_t v_res_166_;
v_res_166_ = l_instDecidablePredComp___aux__1___redArg(v_f_160_, v_inst_161_, v_x_162_);
stack->m_num = v_res_166_;
}
LEAN_EXPORT lean_object* l_instDecidablePredComp___aux__1___redArg___boxed(lean_object* v_f_167_, lean_object* v_inst_168_, lean_object* v_x_169_){
_start:
{
uint8_t v_res_170_; lean_object* v_r_171_; 
v_res_170_ = l_instDecidablePredComp___aux__1___redArg(v_f_167_, v_inst_168_, v_x_169_);
v_r_171_ = lean_box(v_res_170_);
return v_r_171_;
}
}
uint8_t l_instDecidablePredComp___aux__1(lean_object* v_00_u03b1_172_, lean_object* v_p_173_, lean_object* v_00_u03b1_174_, lean_object* v_f_175_, lean_object* v_inst_176_, lean_object* v_x_177_){
_start:
{
uint8_t v___x_178_; 
v___x_178_ = l_instDecidablePredComp___aux__1___redArg(v_f_175_, v_inst_176_, v_x_177_);
return v___x_178_;
}
}
LEAN_EXPORT void l_instDecidablePredComp___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_175_ = stack[3].m_obj;
lean_object* v_inst_176_ = stack[4].m_obj;
lean_object* v_x_177_ = stack[5].m_obj;
uint8_t v_res_179_;
v_res_179_ = l_instDecidablePredComp___aux__1(lean_box(0), lean_box(0), lean_box(0), v_f_175_, v_inst_176_, v_x_177_);
stack->m_num = v_res_179_;
}
LEAN_EXPORT lean_object* l_instDecidablePredComp___aux__1___boxed(lean_object* v_00_u03b1_180_, lean_object* v_p_181_, lean_object* v_00_u03b1_182_, lean_object* v_f_183_, lean_object* v_inst_184_, lean_object* v_x_185_){
_start:
{
uint8_t v_res_186_; lean_object* v_r_187_; 
v_res_186_ = l_instDecidablePredComp___aux__1(v_00_u03b1_180_, v_p_181_, v_00_u03b1_182_, v_f_183_, v_inst_184_, v_x_185_);
v_r_187_ = lean_box(v_res_186_);
return v_r_187_;
}
}
uint8_t l_instDecidablePredComp___redArg(lean_object* v_f_188_, lean_object* v_inst_189_, lean_object* v_x_190_){
_start:
{
uint8_t v___x_191_; 
v___x_191_ = l_instDecidablePredComp___aux__1___redArg(v_f_188_, v_inst_189_, v_x_190_);
return v___x_191_;
}
}
LEAN_EXPORT void l_instDecidablePredComp___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_188_ = stack[0].m_obj;
lean_object* v_inst_189_ = stack[1].m_obj;
lean_object* v_x_190_ = stack[2].m_obj;
uint8_t v_res_192_;
v_res_192_ = l_instDecidablePredComp___redArg(v_f_188_, v_inst_189_, v_x_190_);
stack->m_num = v_res_192_;
}
LEAN_EXPORT lean_object* l_instDecidablePredComp___redArg___boxed(lean_object* v_f_193_, lean_object* v_inst_194_, lean_object* v_x_195_){
_start:
{
uint8_t v_res_196_; lean_object* v_r_197_; 
v_res_196_ = l_instDecidablePredComp___redArg(v_f_193_, v_inst_194_, v_x_195_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
uint8_t l_instDecidablePredComp(lean_object* v_00_u03b1_198_, lean_object* v_p_199_, lean_object* v_00_u03b1_200_, lean_object* v_f_201_, lean_object* v_inst_202_, lean_object* v_x_203_){
_start:
{
uint8_t v___x_204_; 
v___x_204_ = l_instDecidablePredComp___aux__1___redArg(v_f_201_, v_inst_202_, v_x_203_);
return v___x_204_;
}
}
LEAN_EXPORT void l_instDecidablePredComp_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_201_ = stack[3].m_obj;
lean_object* v_inst_202_ = stack[4].m_obj;
lean_object* v_x_203_ = stack[5].m_obj;
uint8_t v_res_205_;
v_res_205_ = l_instDecidablePredComp(lean_box(0), lean_box(0), lean_box(0), v_f_201_, v_inst_202_, v_x_203_);
stack->m_num = v_res_205_;
}
LEAN_EXPORT lean_object* l_instDecidablePredComp___boxed(lean_object* v_00_u03b1_206_, lean_object* v_p_207_, lean_object* v_00_u03b1_208_, lean_object* v_f_209_, lean_object* v_inst_210_, lean_object* v_x_211_){
_start:
{
uint8_t v_res_212_; lean_object* v_r_213_; 
v_res_212_ = l_instDecidablePredComp(v_00_u03b1_206_, v_p_207_, v_00_u03b1_208_, v_f_209_, v_inst_210_, v_x_211_);
v_r_213_ = lean_box(v_res_212_);
return v_r_213_;
}
}
uint8_t l_decidable__of__bool___redArg(uint8_t v_b_214_){
_start:
{
return v_b_214_;
}
}
LEAN_EXPORT void l_decidable__of__bool___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_214_ = stack[0].m_num;
uint8_t v_res_215_;
v_res_215_ = l_decidable__of__bool___redArg(v_b_214_);
stack->m_num = v_res_215_;
}
LEAN_EXPORT lean_object* l_decidable__of__bool___redArg___boxed(lean_object* v_b_216_){
_start:
{
uint8_t v_b_boxed_217_; uint8_t v_res_218_; lean_object* v_r_219_; 
v_b_boxed_217_ = lean_unbox(v_b_216_);
v_res_218_ = l_decidable__of__bool___redArg(v_b_boxed_217_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
uint8_t l_decidable__of__bool(lean_object* v_a_220_, uint8_t v_b_221_, lean_object* v_h_222_){
_start:
{
return v_b_221_;
}
}
LEAN_EXPORT void l_decidable__of__bool_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_221_ = stack[1].m_num;
uint8_t v_res_223_;
v_res_223_ = l_decidable__of__bool(lean_box(0), v_b_221_, lean_box(0));
stack->m_num = v_res_223_;
}
LEAN_EXPORT lean_object* l_decidable__of__bool___boxed(lean_object* v_a_224_, lean_object* v_b_225_, lean_object* v_h_226_){
_start:
{
uint8_t v_b_boxed_227_; uint8_t v_res_228_; lean_object* v_r_229_; 
v_b_boxed_227_ = lean_unbox(v_b_225_);
v_res_228_ = l_decidable__of__bool(v_a_224_, v_b_boxed_227_, v_h_226_);
v_r_229_ = lean_box(v_res_228_);
return v_r_229_;
}
}
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
