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
if (lean_obj_tag(v_o_5_) == 0)
{
uint8_t v___x_6_; 
lean_dec(v_j_4_);
lean_dec_ref(v_inst_3_);
v___x_6_ = 0;
return v___x_6_;
}
else
{
lean_object* v_val_7_; lean_object* v___x_8_; uint8_t v___x_9_; 
v_val_7_ = lean_ctor_get(v_o_5_, 0);
lean_inc(v_val_7_);
lean_dec_ref(v_o_5_);
v___x_8_ = lean_apply_2(v_inst_3_, v_val_7_, v_j_4_);
v___x_9_ = lean_unbox(v___x_8_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l_Option_instDecidableMemOfDecidableEq___redArg___boxed(lean_object* v_inst_10_, lean_object* v_j_11_, lean_object* v_o_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Option_instDecidableMemOfDecidableEq___redArg(v_inst_10_, v_j_11_, v_o_12_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT uint8_t l_Option_instDecidableMemOfDecidableEq(lean_object* v_00_u03b1_15_, lean_object* v_inst_16_, lean_object* v_j_17_, lean_object* v_o_18_){
_start:
{
uint8_t v___x_19_; 
v___x_19_ = l_Option_instDecidableMemOfDecidableEq___redArg(v_inst_16_, v_j_17_, v_o_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Option_instDecidableMemOfDecidableEq___boxed(lean_object* v_00_u03b1_20_, lean_object* v_inst_21_, lean_object* v_j_22_, lean_object* v_o_23_){
_start:
{
uint8_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = l_Option_instDecidableMemOfDecidableEq(v_00_u03b1_20_, v_inst_21_, v_j_22_, v_o_23_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
LEAN_EXPORT uint8_t l_Option_decidableForallMem___redArg(lean_object* v_inst_26_, lean_object* v_x_27_){
_start:
{
if (lean_obj_tag(v_x_27_) == 0)
{
uint8_t v___x_28_; 
lean_dec_ref(v_inst_26_);
v___x_28_ = 1;
return v___x_28_;
}
else
{
lean_object* v_val_29_; lean_object* v___x_30_; uint8_t v___x_31_; 
v_val_29_ = lean_ctor_get(v_x_27_, 0);
lean_inc(v_val_29_);
lean_dec_ref(v_x_27_);
v___x_30_ = lean_apply_1(v_inst_26_, v_val_29_);
v___x_31_ = lean_unbox(v___x_30_);
return v___x_31_;
}
}
}
LEAN_EXPORT lean_object* l_Option_decidableForallMem___redArg___boxed(lean_object* v_inst_32_, lean_object* v_x_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l_Option_decidableForallMem___redArg(v_inst_32_, v_x_33_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
LEAN_EXPORT uint8_t l_Option_decidableForallMem(lean_object* v_00_u03b1_36_, lean_object* v_p_37_, lean_object* v_inst_38_, lean_object* v_x_39_){
_start:
{
uint8_t v___x_40_; 
v___x_40_ = l_Option_decidableForallMem___redArg(v_inst_38_, v_x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Option_decidableForallMem___boxed(lean_object* v_00_u03b1_41_, lean_object* v_p_42_, lean_object* v_inst_43_, lean_object* v_x_44_){
_start:
{
uint8_t v_res_45_; lean_object* v_r_46_; 
v_res_45_ = l_Option_decidableForallMem(v_00_u03b1_41_, v_p_42_, v_inst_43_, v_x_44_);
v_r_46_ = lean_box(v_res_45_);
return v_r_46_;
}
}
LEAN_EXPORT uint8_t l_Option_decidableExistsMem___redArg(lean_object* v_inst_47_, lean_object* v_x_48_){
_start:
{
if (lean_obj_tag(v_x_48_) == 0)
{
uint8_t v___x_49_; 
lean_dec_ref(v_inst_47_);
v___x_49_ = 0;
return v___x_49_;
}
else
{
lean_object* v_val_50_; lean_object* v___x_51_; uint8_t v___x_52_; 
v_val_50_ = lean_ctor_get(v_x_48_, 0);
lean_inc(v_val_50_);
lean_dec_ref(v_x_48_);
v___x_51_ = lean_apply_1(v_inst_47_, v_val_50_);
v___x_52_ = lean_unbox(v___x_51_);
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l_Option_decidableExistsMem___redArg___boxed(lean_object* v_inst_53_, lean_object* v_x_54_){
_start:
{
uint8_t v_res_55_; lean_object* v_r_56_; 
v_res_55_ = l_Option_decidableExistsMem___redArg(v_inst_53_, v_x_54_);
v_r_56_ = lean_box(v_res_55_);
return v_r_56_;
}
}
LEAN_EXPORT uint8_t l_Option_decidableExistsMem(lean_object* v_00_u03b1_57_, lean_object* v_p_58_, lean_object* v_inst_59_, lean_object* v_x_60_){
_start:
{
uint8_t v___x_61_; 
v___x_61_ = l_Option_decidableExistsMem___redArg(v_inst_59_, v_x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Option_decidableExistsMem___boxed(lean_object* v_00_u03b1_62_, lean_object* v_p_63_, lean_object* v_inst_64_, lean_object* v_x_65_){
_start:
{
uint8_t v_res_66_; lean_object* v_r_67_; 
v_res_66_ = l_Option_decidableExistsMem(v_00_u03b1_62_, v_p_63_, v_inst_64_, v_x_65_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
LEAN_EXPORT lean_object* l_Option_pbind___redArg(lean_object* v_x_68_, lean_object* v_x_69_){
_start:
{
if (lean_obj_tag(v_x_68_) == 0)
{
lean_object* v___x_70_; 
lean_dec_ref(v_x_69_);
v___x_70_ = lean_box(0);
return v___x_70_;
}
else
{
lean_object* v_val_71_; lean_object* v___x_72_; 
v_val_71_ = lean_ctor_get(v_x_68_, 0);
lean_inc(v_val_71_);
lean_dec_ref(v_x_68_);
v___x_72_ = lean_apply_2(v_x_69_, v_val_71_, lean_box(0));
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l_Option_pbind(lean_object* v_00_u03b1_73_, lean_object* v_00_u03b2_74_, lean_object* v_x_75_, lean_object* v_x_76_){
_start:
{
if (lean_obj_tag(v_x_75_) == 0)
{
lean_object* v___x_77_; 
lean_dec_ref(v_x_76_);
v___x_77_ = lean_box(0);
return v___x_77_;
}
else
{
lean_object* v_val_78_; lean_object* v___x_79_; 
v_val_78_ = lean_ctor_get(v_x_75_, 0);
lean_inc(v_val_78_);
lean_dec_ref(v_x_75_);
v___x_79_ = lean_apply_2(v_x_76_, v_val_78_, lean_box(0));
return v___x_79_;
}
}
}
LEAN_EXPORT lean_object* l_Option_pmap___redArg(lean_object* v_f_80_, lean_object* v_x_81_){
_start:
{
if (lean_obj_tag(v_x_81_) == 0)
{
lean_object* v___x_82_; 
lean_dec(v_f_80_);
v___x_82_ = lean_box(0);
return v___x_82_;
}
else
{
lean_object* v_val_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_91_; 
v_val_83_ = lean_ctor_get(v_x_81_, 0);
v_isSharedCheck_91_ = !lean_is_exclusive(v_x_81_);
if (v_isSharedCheck_91_ == 0)
{
v___x_85_ = v_x_81_;
v_isShared_86_ = v_isSharedCheck_91_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_val_83_);
lean_dec(v_x_81_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_91_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_87_; lean_object* v___x_89_; 
v___x_87_ = lean_apply_2(v_f_80_, v_val_83_, lean_box(0));
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_87_);
v___x_89_ = v___x_85_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_87_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_pmap(lean_object* v_00_u03b1_92_, lean_object* v_00_u03b2_93_, lean_object* v_p_94_, lean_object* v_f_95_, lean_object* v_x_96_, lean_object* v_x_97_){
_start:
{
if (lean_obj_tag(v_x_96_) == 0)
{
lean_object* v___x_98_; 
lean_dec(v_f_95_);
v___x_98_ = lean_box(0);
return v___x_98_;
}
else
{
lean_object* v_val_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_107_; 
v_val_99_ = lean_ctor_get(v_x_96_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v_x_96_);
if (v_isSharedCheck_107_ == 0)
{
v___x_101_ = v_x_96_;
v_isShared_102_ = v_isSharedCheck_107_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_val_99_);
lean_dec(v_x_96_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_107_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; lean_object* v___x_105_; 
v___x_103_ = lean_apply_2(v_f_95_, v_val_99_, lean_box(0));
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 0, v___x_103_);
v___x_105_ = v___x_101_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_103_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_pelim___redArg(lean_object* v_o_108_, lean_object* v_b_109_, lean_object* v_f_110_){
_start:
{
if (lean_obj_tag(v_o_108_) == 0)
{
lean_dec(v_f_110_);
lean_inc(v_b_109_);
return v_b_109_;
}
else
{
lean_object* v_val_111_; lean_object* v___x_112_; 
v_val_111_ = lean_ctor_get(v_o_108_, 0);
lean_inc(v_val_111_);
lean_dec_ref(v_o_108_);
v___x_112_ = lean_apply_2(v_f_110_, v_val_111_, lean_box(0));
return v___x_112_;
}
}
}
LEAN_EXPORT lean_object* l_Option_pelim___redArg___boxed(lean_object* v_o_113_, lean_object* v_b_114_, lean_object* v_f_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Option_pelim___redArg(v_o_113_, v_b_114_, v_f_115_);
lean_dec(v_b_114_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Option_pelim(lean_object* v_00_u03b1_117_, lean_object* v_00_u03b2_118_, lean_object* v_o_119_, lean_object* v_b_120_, lean_object* v_f_121_){
_start:
{
if (lean_obj_tag(v_o_119_) == 0)
{
lean_dec(v_f_121_);
lean_inc(v_b_120_);
return v_b_120_;
}
else
{
lean_object* v_val_122_; lean_object* v___x_123_; 
v_val_122_ = lean_ctor_get(v_o_119_, 0);
lean_inc(v_val_122_);
lean_dec_ref(v_o_119_);
v___x_123_ = lean_apply_2(v_f_121_, v_val_122_, lean_box(0));
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l_Option_pelim___boxed(lean_object* v_00_u03b1_124_, lean_object* v_00_u03b2_125_, lean_object* v_o_126_, lean_object* v_b_127_, lean_object* v_f_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Option_pelim(v_00_u03b1_124_, v_00_u03b2_125_, v_o_126_, v_b_127_, v_f_128_);
lean_dec(v_b_127_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Option_pfilter___redArg(lean_object* v_o_130_, lean_object* v_p_131_){
_start:
{
if (lean_obj_tag(v_o_130_) == 0)
{
lean_dec_ref(v_p_131_);
return v_o_130_;
}
else
{
lean_object* v_val_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
v_val_132_ = lean_ctor_get(v_o_130_, 0);
lean_inc(v_val_132_);
v___x_133_ = lean_apply_2(v_p_131_, v_val_132_, lean_box(0));
v___x_134_ = lean_unbox(v___x_133_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; 
lean_dec_ref(v_o_130_);
v___x_135_ = lean_box(0);
return v___x_135_;
}
else
{
return v_o_130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_pfilter(lean_object* v_00_u03b1_136_, lean_object* v_o_137_, lean_object* v_p_138_){
_start:
{
if (lean_obj_tag(v_o_137_) == 0)
{
lean_dec_ref(v_p_138_);
return v_o_137_;
}
else
{
lean_object* v_val_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v_val_139_ = lean_ctor_get(v_o_137_, 0);
lean_inc(v_val_139_);
v___x_140_ = lean_apply_2(v_p_138_, v_val_139_, lean_box(0));
v___x_141_ = lean_unbox(v___x_140_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; 
lean_dec_ref(v_o_137_);
v___x_142_ = lean_box(0);
return v___x_142_;
}
else
{
return v_o_137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_forM___redArg(lean_object* v_inst_143_, lean_object* v_x_144_, lean_object* v_x_145_){
_start:
{
if (lean_obj_tag(v_x_144_) == 0)
{
lean_object* v___x_146_; lean_object* v___x_147_; 
lean_dec(v_x_145_);
v___x_146_ = lean_box(0);
v___x_147_ = lean_apply_2(v_inst_143_, lean_box(0), v___x_146_);
return v___x_147_;
}
else
{
lean_object* v_val_148_; lean_object* v___x_149_; 
lean_dec(v_inst_143_);
v_val_148_ = lean_ctor_get(v_x_144_, 0);
lean_inc(v_val_148_);
lean_dec_ref(v_x_144_);
v___x_149_ = lean_apply_1(v_x_145_, v_val_148_);
return v___x_149_;
}
}
}
LEAN_EXPORT lean_object* l_Option_forM(lean_object* v_m_150_, lean_object* v_00_u03b1_151_, lean_object* v_inst_152_, lean_object* v_x_153_, lean_object* v_x_154_){
_start:
{
if (lean_obj_tag(v_x_153_) == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; 
lean_dec(v_x_154_);
v___x_155_ = lean_box(0);
v___x_156_ = lean_apply_2(v_inst_152_, lean_box(0), v___x_155_);
return v___x_156_;
}
else
{
lean_object* v_val_157_; lean_object* v___x_158_; 
lean_dec(v_inst_152_);
v_val_157_ = lean_ctor_get(v_x_153_, 0);
lean_inc(v_val_157_);
lean_dec_ref(v_x_153_);
v___x_158_ = lean_apply_1(v_x_154_, v_val_157_);
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l_Option_instForMOfMonad___redArg(lean_object* v_inst_159_){
_start:
{
lean_object* v_toApplicative_160_; lean_object* v_toPure_161_; lean_object* v___x_162_; 
v_toApplicative_160_ = lean_ctor_get(v_inst_159_, 0);
lean_inc_ref(v_toApplicative_160_);
lean_dec_ref(v_inst_159_);
v_toPure_161_ = lean_ctor_get(v_toApplicative_160_, 1);
lean_inc(v_toPure_161_);
lean_dec_ref(v_toApplicative_160_);
v___x_162_ = lean_alloc_closure((void*)(l_Option_forM), 5, 3);
lean_closure_set(v___x_162_, 0, lean_box(0));
lean_closure_set(v___x_162_, 1, lean_box(0));
lean_closure_set(v___x_162_, 2, v_toPure_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Option_instForMOfMonad(lean_object* v_m_163_, lean_object* v_00_u03b1_164_, lean_object* v_inst_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_Option_instForMOfMonad___redArg(v_inst_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Option_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object* v_toPure_167_, lean_object* v_____do__lift_168_){
_start:
{
lean_object* v_a_169_; lean_object* v___x_170_; 
v_a_169_ = lean_ctor_get(v_____do__lift_168_, 0);
lean_inc(v_a_169_);
lean_dec_ref(v_____do__lift_168_);
v___x_170_ = lean_apply_2(v_toPure_167_, lean_box(0), v_a_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Option_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1(lean_object* v_toPure_171_, lean_object* v_toBind_172_, lean_object* v___f_173_, lean_object* v_00_u03b2_174_, lean_object* v_x_175_, lean_object* v_init_176_, lean_object* v_f_177_){
_start:
{
if (lean_obj_tag(v_x_175_) == 0)
{
lean_object* v___x_178_; 
lean_dec(v_f_177_);
lean_dec(v___f_173_);
lean_dec(v_toBind_172_);
v___x_178_ = lean_apply_2(v_toPure_171_, lean_box(0), v_init_176_);
return v___x_178_;
}
else
{
lean_object* v_val_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
lean_dec(v_toPure_171_);
v_val_179_ = lean_ctor_get(v_x_175_, 0);
lean_inc(v_val_179_);
lean_dec_ref(v_x_175_);
v___x_180_ = lean_apply_3(v_f_177_, v_val_179_, lean_box(0), v_init_176_);
v___x_181_ = lean_apply_4(v_toBind_172_, lean_box(0), lean_box(0), v___x_180_, v___f_173_);
return v___x_181_;
}
}
}
LEAN_EXPORT lean_object* l_Option_instForIn_x27InferInstanceMembershipOfMonad___redArg(lean_object* v_inst_182_){
_start:
{
lean_object* v_toApplicative_183_; lean_object* v_toBind_184_; lean_object* v_toPure_185_; lean_object* v___f_186_; lean_object* v___f_187_; 
v_toApplicative_183_ = lean_ctor_get(v_inst_182_, 0);
lean_inc_ref(v_toApplicative_183_);
v_toBind_184_ = lean_ctor_get(v_inst_182_, 1);
lean_inc(v_toBind_184_);
lean_dec_ref(v_inst_182_);
v_toPure_185_ = lean_ctor_get(v_toApplicative_183_, 1);
lean_inc(v_toPure_185_);
lean_dec_ref(v_toApplicative_183_);
lean_inc(v_toPure_185_);
v___f_186_ = lean_alloc_closure((void*)(l_Option_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_186_, 0, v_toPure_185_);
v___f_187_ = lean_alloc_closure((void*)(l_Option_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1), 7, 3);
lean_closure_set(v___f_187_, 0, v_toPure_185_);
lean_closure_set(v___f_187_, 1, v_toBind_184_);
lean_closure_set(v___f_187_, 2, v___f_186_);
return v___f_187_;
}
}
LEAN_EXPORT lean_object* l_Option_instForIn_x27InferInstanceMembershipOfMonad(lean_object* v_m_188_, lean_object* v_00_u03b1_189_, lean_object* v_inst_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Option_instForIn_x27InferInstanceMembershipOfMonad___redArg(v_inst_190_);
return v___x_191_;
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
