// Lean compiler output
// Module: Init.Data.Option.Instances
// Imports: public import Init.Data.Option.Basic
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
uint8_t l_Option_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instMembership(lean_object*);
LEAN_EXPORT uint8_t l_Option_instDecidableMemOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instDecidableMemOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instDecidableMemOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instDecidableMemOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_decidableForallMem___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_decidableForallMem___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_decidableForallMem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_decidableForallMem___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_decidableExistsMem___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_decidableExistsMem___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_decidableExistsMem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_decidableExistsMem___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_pbind___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_pbind(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_pmap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_pmap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_pelim___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_pelim___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_pelim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_pelim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_pfilter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_pfilter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instForMOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Option_instForMOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instForIn_x27InferInstanceMembershipOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Option_instForIn_x27InferInstanceMembershipOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instMembership(lean_object* v_00_u03b1_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT uint8_t l_Option_instDecidableMemOfDecidableEq___redArg(lean_object* v_inst_3_, lean_object* v_j_4_, lean_object* v_o_5_){
_start:
{
lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v_j_4_);
v___x_7_ = l_Option_instDecidableEq___redArg(v_inst_3_, v_o_5_, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Option_instDecidableMemOfDecidableEq___redArg___boxed(lean_object* v_inst_8_, lean_object* v_j_9_, lean_object* v_o_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Option_instDecidableMemOfDecidableEq___redArg(v_inst_8_, v_j_9_, v_o_10_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT uint8_t l_Option_instDecidableMemOfDecidableEq(lean_object* v_00_u03b1_13_, lean_object* v_inst_14_, lean_object* v_j_15_, lean_object* v_o_16_){
_start:
{
uint8_t v___x_17_; 
v___x_17_ = l_Option_instDecidableMemOfDecidableEq___redArg(v_inst_14_, v_j_15_, v_o_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Option_instDecidableMemOfDecidableEq___boxed(lean_object* v_00_u03b1_18_, lean_object* v_inst_19_, lean_object* v_j_20_, lean_object* v_o_21_){
_start:
{
uint8_t v_res_22_; lean_object* v_r_23_; 
v_res_22_ = l_Option_instDecidableMemOfDecidableEq(v_00_u03b1_18_, v_inst_19_, v_j_20_, v_o_21_);
v_r_23_ = lean_box(v_res_22_);
return v_r_23_;
}
}
LEAN_EXPORT uint8_t l_Option_decidableForallMem___redArg(lean_object* v_inst_24_, lean_object* v_x_25_){
_start:
{
if (lean_obj_tag(v_x_25_) == 0)
{
uint8_t v___x_26_; 
lean_dec_ref(v_inst_24_);
v___x_26_ = 1;
return v___x_26_;
}
else
{
lean_object* v_val_27_; lean_object* v___x_28_; uint8_t v___x_29_; 
v_val_27_ = lean_ctor_get(v_x_25_, 0);
lean_inc(v_val_27_);
lean_dec_ref(v_x_25_);
v___x_28_ = lean_apply_1(v_inst_24_, v_val_27_);
v___x_29_ = lean_unbox(v___x_28_);
return v___x_29_;
}
}
}
LEAN_EXPORT lean_object* l_Option_decidableForallMem___redArg___boxed(lean_object* v_inst_30_, lean_object* v_x_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = l_Option_decidableForallMem___redArg(v_inst_30_, v_x_31_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
LEAN_EXPORT uint8_t l_Option_decidableForallMem(lean_object* v_00_u03b1_34_, lean_object* v_p_35_, lean_object* v_inst_36_, lean_object* v_x_37_){
_start:
{
uint8_t v___x_38_; 
v___x_38_ = l_Option_decidableForallMem___redArg(v_inst_36_, v_x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Option_decidableForallMem___boxed(lean_object* v_00_u03b1_39_, lean_object* v_p_40_, lean_object* v_inst_41_, lean_object* v_x_42_){
_start:
{
uint8_t v_res_43_; lean_object* v_r_44_; 
v_res_43_ = l_Option_decidableForallMem(v_00_u03b1_39_, v_p_40_, v_inst_41_, v_x_42_);
v_r_44_ = lean_box(v_res_43_);
return v_r_44_;
}
}
LEAN_EXPORT uint8_t l_Option_decidableExistsMem___redArg(lean_object* v_inst_45_, lean_object* v_x_46_){
_start:
{
if (lean_obj_tag(v_x_46_) == 0)
{
uint8_t v___x_47_; 
lean_dec_ref(v_inst_45_);
v___x_47_ = 0;
return v___x_47_;
}
else
{
lean_object* v_val_48_; lean_object* v___x_49_; uint8_t v___x_50_; 
v_val_48_ = lean_ctor_get(v_x_46_, 0);
lean_inc(v_val_48_);
lean_dec_ref(v_x_46_);
v___x_49_ = lean_apply_1(v_inst_45_, v_val_48_);
v___x_50_ = lean_unbox(v___x_49_);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l_Option_decidableExistsMem___redArg___boxed(lean_object* v_inst_51_, lean_object* v_x_52_){
_start:
{
uint8_t v_res_53_; lean_object* v_r_54_; 
v_res_53_ = l_Option_decidableExistsMem___redArg(v_inst_51_, v_x_52_);
v_r_54_ = lean_box(v_res_53_);
return v_r_54_;
}
}
LEAN_EXPORT uint8_t l_Option_decidableExistsMem(lean_object* v_00_u03b1_55_, lean_object* v_p_56_, lean_object* v_inst_57_, lean_object* v_x_58_){
_start:
{
uint8_t v___x_59_; 
v___x_59_ = l_Option_decidableExistsMem___redArg(v_inst_57_, v_x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Option_decidableExistsMem___boxed(lean_object* v_00_u03b1_60_, lean_object* v_p_61_, lean_object* v_inst_62_, lean_object* v_x_63_){
_start:
{
uint8_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = l_Option_decidableExistsMem(v_00_u03b1_60_, v_p_61_, v_inst_62_, v_x_63_);
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
LEAN_EXPORT lean_object* l_Option_pbind___redArg(lean_object* v_x_66_, lean_object* v_x_67_){
_start:
{
if (lean_obj_tag(v_x_66_) == 0)
{
lean_object* v___x_68_; 
lean_dec_ref(v_x_67_);
v___x_68_ = lean_box(0);
return v___x_68_;
}
else
{
lean_object* v_val_69_; lean_object* v___x_70_; 
v_val_69_ = lean_ctor_get(v_x_66_, 0);
lean_inc(v_val_69_);
lean_dec_ref(v_x_66_);
v___x_70_ = lean_apply_2(v_x_67_, v_val_69_, lean_box(0));
return v___x_70_;
}
}
}
LEAN_EXPORT lean_object* l_Option_pbind(lean_object* v_00_u03b1_71_, lean_object* v_00_u03b2_72_, lean_object* v_x_73_, lean_object* v_x_74_){
_start:
{
if (lean_obj_tag(v_x_73_) == 0)
{
lean_object* v___x_75_; 
lean_dec_ref(v_x_74_);
v___x_75_ = lean_box(0);
return v___x_75_;
}
else
{
lean_object* v_val_76_; lean_object* v___x_77_; 
v_val_76_ = lean_ctor_get(v_x_73_, 0);
lean_inc(v_val_76_);
lean_dec_ref(v_x_73_);
v___x_77_ = lean_apply_2(v_x_74_, v_val_76_, lean_box(0));
return v___x_77_;
}
}
}
LEAN_EXPORT lean_object* l_Option_pmap___redArg(lean_object* v_f_78_, lean_object* v_x_79_){
_start:
{
if (lean_obj_tag(v_x_79_) == 0)
{
lean_object* v___x_80_; 
lean_dec(v_f_78_);
v___x_80_ = lean_box(0);
return v___x_80_;
}
else
{
lean_object* v_val_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_89_; 
v_val_81_ = lean_ctor_get(v_x_79_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v_x_79_);
if (v_isSharedCheck_89_ == 0)
{
v___x_83_ = v_x_79_;
v_isShared_84_ = v_isSharedCheck_89_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_val_81_);
lean_dec(v_x_79_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_89_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_85_; lean_object* v___x_87_; 
v___x_85_ = lean_apply_2(v_f_78_, v_val_81_, lean_box(0));
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 0, v___x_85_);
v___x_87_ = v___x_83_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_85_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_pmap(lean_object* v_00_u03b1_90_, lean_object* v_00_u03b2_91_, lean_object* v_p_92_, lean_object* v_f_93_, lean_object* v_x_94_, lean_object* v_x_95_){
_start:
{
if (lean_obj_tag(v_x_94_) == 0)
{
lean_object* v___x_96_; 
lean_dec(v_f_93_);
v___x_96_ = lean_box(0);
return v___x_96_;
}
else
{
lean_object* v_val_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_105_; 
v_val_97_ = lean_ctor_get(v_x_94_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v_x_94_);
if (v_isSharedCheck_105_ == 0)
{
v___x_99_ = v_x_94_;
v_isShared_100_ = v_isSharedCheck_105_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_val_97_);
lean_dec(v_x_94_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_105_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_101_; lean_object* v___x_103_; 
v___x_101_ = lean_apply_2(v_f_93_, v_val_97_, lean_box(0));
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 0, v___x_101_);
v___x_103_ = v___x_99_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_101_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_pelim___redArg(lean_object* v_o_106_, lean_object* v_b_107_, lean_object* v_f_108_){
_start:
{
if (lean_obj_tag(v_o_106_) == 0)
{
lean_dec(v_f_108_);
lean_inc(v_b_107_);
return v_b_107_;
}
else
{
lean_object* v_val_109_; lean_object* v___x_110_; 
v_val_109_ = lean_ctor_get(v_o_106_, 0);
lean_inc(v_val_109_);
lean_dec_ref(v_o_106_);
v___x_110_ = lean_apply_2(v_f_108_, v_val_109_, lean_box(0));
return v___x_110_;
}
}
}
LEAN_EXPORT lean_object* l_Option_pelim___redArg___boxed(lean_object* v_o_111_, lean_object* v_b_112_, lean_object* v_f_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Option_pelim___redArg(v_o_111_, v_b_112_, v_f_113_);
lean_dec(v_b_112_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Option_pelim(lean_object* v_00_u03b1_115_, lean_object* v_00_u03b2_116_, lean_object* v_o_117_, lean_object* v_b_118_, lean_object* v_f_119_){
_start:
{
if (lean_obj_tag(v_o_117_) == 0)
{
lean_dec(v_f_119_);
lean_inc(v_b_118_);
return v_b_118_;
}
else
{
lean_object* v_val_120_; lean_object* v___x_121_; 
v_val_120_ = lean_ctor_get(v_o_117_, 0);
lean_inc(v_val_120_);
lean_dec_ref(v_o_117_);
v___x_121_ = lean_apply_2(v_f_119_, v_val_120_, lean_box(0));
return v___x_121_;
}
}
}
LEAN_EXPORT lean_object* l_Option_pelim___boxed(lean_object* v_00_u03b1_122_, lean_object* v_00_u03b2_123_, lean_object* v_o_124_, lean_object* v_b_125_, lean_object* v_f_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Option_pelim(v_00_u03b1_122_, v_00_u03b2_123_, v_o_124_, v_b_125_, v_f_126_);
lean_dec(v_b_125_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Option_pfilter___redArg(lean_object* v_o_128_, lean_object* v_p_129_){
_start:
{
if (lean_obj_tag(v_o_128_) == 0)
{
lean_dec_ref(v_p_129_);
return v_o_128_;
}
else
{
lean_object* v_val_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v_val_130_ = lean_ctor_get(v_o_128_, 0);
lean_inc(v_val_130_);
v___x_131_ = lean_apply_2(v_p_129_, v_val_130_, lean_box(0));
v___x_132_ = lean_unbox(v___x_131_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; 
lean_dec_ref(v_o_128_);
v___x_133_ = lean_box(0);
return v___x_133_;
}
else
{
return v_o_128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_pfilter(lean_object* v_00_u03b1_134_, lean_object* v_o_135_, lean_object* v_p_136_){
_start:
{
if (lean_obj_tag(v_o_135_) == 0)
{
lean_dec_ref(v_p_136_);
return v_o_135_;
}
else
{
lean_object* v_val_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v_val_137_ = lean_ctor_get(v_o_135_, 0);
lean_inc(v_val_137_);
v___x_138_ = lean_apply_2(v_p_136_, v_val_137_, lean_box(0));
v___x_139_ = lean_unbox(v___x_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; 
lean_dec_ref(v_o_135_);
v___x_140_ = lean_box(0);
return v___x_140_;
}
else
{
return v_o_135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_forM___redArg(lean_object* v_inst_141_, lean_object* v_x_142_, lean_object* v_x_143_){
_start:
{
if (lean_obj_tag(v_x_142_) == 0)
{
lean_object* v___x_144_; lean_object* v___x_145_; 
lean_dec(v_x_143_);
v___x_144_ = lean_box(0);
v___x_145_ = lean_apply_2(v_inst_141_, lean_box(0), v___x_144_);
return v___x_145_;
}
else
{
lean_object* v_val_146_; lean_object* v___x_147_; 
lean_dec(v_inst_141_);
v_val_146_ = lean_ctor_get(v_x_142_, 0);
lean_inc(v_val_146_);
lean_dec_ref(v_x_142_);
v___x_147_ = lean_apply_1(v_x_143_, v_val_146_);
return v___x_147_;
}
}
}
LEAN_EXPORT lean_object* l_Option_forM(lean_object* v_m_148_, lean_object* v_00_u03b1_149_, lean_object* v_inst_150_, lean_object* v_x_151_, lean_object* v_x_152_){
_start:
{
if (lean_obj_tag(v_x_151_) == 0)
{
lean_object* v___x_153_; lean_object* v___x_154_; 
lean_dec(v_x_152_);
v___x_153_ = lean_box(0);
v___x_154_ = lean_apply_2(v_inst_150_, lean_box(0), v___x_153_);
return v___x_154_;
}
else
{
lean_object* v_val_155_; lean_object* v___x_156_; 
lean_dec(v_inst_150_);
v_val_155_ = lean_ctor_get(v_x_151_, 0);
lean_inc(v_val_155_);
lean_dec_ref(v_x_151_);
v___x_156_ = lean_apply_1(v_x_152_, v_val_155_);
return v___x_156_;
}
}
}
LEAN_EXPORT lean_object* l_Option_instForMOfMonad___redArg(lean_object* v_inst_157_){
_start:
{
lean_object* v_toApplicative_158_; lean_object* v_toPure_159_; lean_object* v___x_160_; 
v_toApplicative_158_ = lean_ctor_get(v_inst_157_, 0);
lean_inc_ref(v_toApplicative_158_);
lean_dec_ref(v_inst_157_);
v_toPure_159_ = lean_ctor_get(v_toApplicative_158_, 1);
lean_inc(v_toPure_159_);
lean_dec_ref(v_toApplicative_158_);
v___x_160_ = lean_alloc_closure((void*)(l_Option_forM), 5, 3);
lean_closure_set(v___x_160_, 0, lean_box(0));
lean_closure_set(v___x_160_, 1, lean_box(0));
lean_closure_set(v___x_160_, 2, v_toPure_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Option_instForMOfMonad(lean_object* v_m_161_, lean_object* v_00_u03b1_162_, lean_object* v_inst_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Option_instForMOfMonad___redArg(v_inst_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Option_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object* v_toPure_165_, lean_object* v_____do__lift_166_){
_start:
{
lean_object* v_a_167_; lean_object* v___x_168_; 
v_a_167_ = lean_ctor_get(v_____do__lift_166_, 0);
lean_inc(v_a_167_);
lean_dec_ref(v_____do__lift_166_);
v___x_168_ = lean_apply_2(v_toPure_165_, lean_box(0), v_a_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Option_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1(lean_object* v_toPure_169_, lean_object* v_toBind_170_, lean_object* v___f_171_, lean_object* v_00_u03b2_172_, lean_object* v_x_173_, lean_object* v_init_174_, lean_object* v_f_175_){
_start:
{
if (lean_obj_tag(v_x_173_) == 0)
{
lean_object* v___x_176_; 
lean_dec(v_f_175_);
lean_dec(v___f_171_);
lean_dec(v_toBind_170_);
v___x_176_ = lean_apply_2(v_toPure_169_, lean_box(0), v_init_174_);
return v___x_176_;
}
else
{
lean_object* v_val_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
lean_dec(v_toPure_169_);
v_val_177_ = lean_ctor_get(v_x_173_, 0);
lean_inc(v_val_177_);
lean_dec_ref(v_x_173_);
v___x_178_ = lean_apply_3(v_f_175_, v_val_177_, lean_box(0), v_init_174_);
v___x_179_ = lean_apply_4(v_toBind_170_, lean_box(0), lean_box(0), v___x_178_, v___f_171_);
return v___x_179_;
}
}
}
LEAN_EXPORT lean_object* l_Option_instForIn_x27InferInstanceMembershipOfMonad___redArg(lean_object* v_inst_180_){
_start:
{
lean_object* v_toApplicative_181_; lean_object* v_toBind_182_; lean_object* v_toPure_183_; lean_object* v___f_184_; lean_object* v___f_185_; 
v_toApplicative_181_ = lean_ctor_get(v_inst_180_, 0);
lean_inc_ref(v_toApplicative_181_);
v_toBind_182_ = lean_ctor_get(v_inst_180_, 1);
lean_inc(v_toBind_182_);
lean_dec_ref(v_inst_180_);
v_toPure_183_ = lean_ctor_get(v_toApplicative_181_, 1);
lean_inc_n(v_toPure_183_, 2);
lean_dec_ref(v_toApplicative_181_);
v___f_184_ = lean_alloc_closure((void*)(l_Option_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_184_, 0, v_toPure_183_);
v___f_185_ = lean_alloc_closure((void*)(l_Option_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1), 7, 3);
lean_closure_set(v___f_185_, 0, v_toPure_183_);
lean_closure_set(v___f_185_, 1, v_toBind_182_);
lean_closure_set(v___f_185_, 2, v___f_184_);
return v___f_185_;
}
}
LEAN_EXPORT lean_object* l_Option_instForIn_x27InferInstanceMembershipOfMonad(lean_object* v_m_186_, lean_object* v_00_u03b1_187_, lean_object* v_inst_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Option_instForIn_x27InferInstanceMembershipOfMonad___redArg(v_inst_188_);
return v___x_189_;
}
}
lean_object* runtime_initialize_Init_Data_Option_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Option_Instances(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Option_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Option_Instances(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Option_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Option_Instances(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Option_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Option_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Option_Instances(builtin);
}
#ifdef __cplusplus
}
#endif
