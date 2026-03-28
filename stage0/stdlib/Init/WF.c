// Lean compiler output
// Module: Init.WF
// Imports: public import Init.BinderNameHint public import Init.Grind.Tactics import Init.Data.Nat.Basic
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Nat_recCompiled___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_wrap___redArg(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_wrap___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_wrap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_wrap___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_emptyWf(lean_object*);
LEAN_EXPORT lean_object* l_invImage(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_invImage___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_lt__wfRel;
LEAN_EXPORT lean_object* l_measure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_measure___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_sizeOfWFRel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_sizeOfWFRel___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Prod_Lex_instDecidableRelOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_Lex_instDecidableRelOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Prod_Lex_instDecidableRelOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_Lex_instDecidableRelOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_lex(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_instWellFoundedRelation(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_rprod(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PSigma_lex(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PSigma_lex___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PSigma_instWellFoundedRelation(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PSigma_instWellFoundedRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PSigma_skipLeft(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_Nat_eager(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_Nat_eager___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_WellFounded_Nat_fix_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_Nat_fix_go___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_Nat_fix_go___redArg___closed__0 = (const lean_object*)&l_WellFounded_Nat_fix_go___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_wfParam___redArg(lean_object*);
LEAN_EXPORT lean_object* l_wfParam___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_wfParam(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_wfParam___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_wrap___redArg(lean_object* v_x_1_){
_start:
{
lean_inc(v_x_1_);
return v_x_1_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_wrap___redArg___boxed(lean_object* v_x_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l_WellFounded_wrap___redArg(v_x_2_);
lean_dec(v_x_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_wrap(lean_object* v_00_u03b1_4_, lean_object* v_r_5_, lean_object* v_h_6_, lean_object* v_x_7_){
_start:
{
lean_inc(v_x_7_);
return v_x_7_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_wrap___boxed(lean_object* v_00_u03b1_8_, lean_object* v_r_9_, lean_object* v_h_10_, lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_WellFounded_wrap(v_00_u03b1_8_, v_r_9_, v_h_10_, v_x_11_);
lean_dec(v_x_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_emptyWf(lean_object* v_00_u03b1_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_box(0);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_invImage(lean_object* v_00_u03b1_15_, lean_object* v_00_u03b2_16_, lean_object* v_f_17_, lean_object* v_h_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lean_box(0);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_invImage___boxed(lean_object* v_00_u03b1_20_, lean_object* v_00_u03b2_21_, lean_object* v_f_22_, lean_object* v_h_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_invImage(v_00_u03b1_20_, v_00_u03b2_21_, v_f_22_, v_h_23_);
lean_dec(v_f_22_);
return v_res_24_;
}
}
static lean_object* _init_l_Nat_lt__wfRel(void){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lean_box(0);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_measure(lean_object* v_00_u03b1_26_, lean_object* v_f_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_box(0);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_measure___boxed(lean_object* v_00_u03b1_29_, lean_object* v_f_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_measure(v_00_u03b1_29_, v_f_30_);
lean_dec_ref(v_f_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_sizeOfWFRel(lean_object* v_00_u03b1_32_, lean_object* v_inst_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lean_box(0);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_sizeOfWFRel___boxed(lean_object* v_00_u03b1_35_, lean_object* v_inst_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_sizeOfWFRel(v_00_u03b1_35_, v_inst_36_);
lean_dec_ref(v_inst_36_);
return v_res_37_;
}
}
LEAN_EXPORT uint8_t l_Prod_Lex_instDecidableRelOfDecidableEq___redArg(lean_object* v_00_u03b1eqDec_38_, lean_object* v_rDec_39_, lean_object* v_sDec_40_, lean_object* v_x_41_, lean_object* v_x_42_){
_start:
{
lean_object* v_fst_43_; lean_object* v_snd_44_; lean_object* v_fst_45_; lean_object* v_snd_46_; lean_object* v___x_47_; lean_object* v___x_48_; uint8_t v___x_49_; 
v_fst_43_ = lean_ctor_get(v_x_41_, 0);
lean_inc_n(v_fst_43_, 2);
v_snd_44_ = lean_ctor_get(v_x_41_, 1);
lean_inc(v_snd_44_);
lean_dec_ref(v_x_41_);
v_fst_45_ = lean_ctor_get(v_x_42_, 0);
lean_inc_n(v_fst_45_, 2);
v_snd_46_ = lean_ctor_get(v_x_42_, 1);
lean_inc(v_snd_46_);
lean_dec_ref(v_x_42_);
v___x_47_ = lean_apply_2(v_00_u03b1eqDec_38_, v_fst_43_, v_fst_45_);
v___x_48_ = lean_apply_2(v_rDec_39_, v_fst_43_, v_fst_45_);
v___x_49_ = lean_unbox(v___x_48_);
if (v___x_49_ == 0)
{
uint8_t v___x_50_; 
v___x_50_ = lean_unbox(v___x_47_);
if (v___x_50_ == 0)
{
uint8_t v___x_51_; 
lean_dec(v_snd_46_);
lean_dec(v_snd_44_);
lean_dec_ref(v_sDec_40_);
v___x_51_ = lean_unbox(v___x_47_);
return v___x_51_;
}
else
{
lean_object* v___x_52_; uint8_t v___x_53_; 
v___x_52_ = lean_apply_2(v_sDec_40_, v_snd_44_, v_snd_46_);
v___x_53_ = lean_unbox(v___x_52_);
return v___x_53_;
}
}
else
{
uint8_t v___x_54_; 
lean_dec(v_snd_46_);
lean_dec(v_snd_44_);
lean_dec_ref(v_sDec_40_);
v___x_54_ = lean_unbox(v___x_48_);
return v___x_54_;
}
}
}
LEAN_EXPORT lean_object* l_Prod_Lex_instDecidableRelOfDecidableEq___redArg___boxed(lean_object* v_00_u03b1eqDec_55_, lean_object* v_rDec_56_, lean_object* v_sDec_57_, lean_object* v_x_58_, lean_object* v_x_59_){
_start:
{
uint8_t v_res_60_; lean_object* v_r_61_; 
v_res_60_ = l_Prod_Lex_instDecidableRelOfDecidableEq___redArg(v_00_u03b1eqDec_55_, v_rDec_56_, v_sDec_57_, v_x_58_, v_x_59_);
v_r_61_ = lean_box(v_res_60_);
return v_r_61_;
}
}
LEAN_EXPORT uint8_t l_Prod_Lex_instDecidableRelOfDecidableEq(lean_object* v_00_u03b1_62_, lean_object* v_00_u03b2_63_, lean_object* v_00_u03b1eqDec_64_, lean_object* v_r_65_, lean_object* v_rDec_66_, lean_object* v_s_67_, lean_object* v_sDec_68_, lean_object* v_x_69_, lean_object* v_x_70_){
_start:
{
uint8_t v___x_71_; 
v___x_71_ = l_Prod_Lex_instDecidableRelOfDecidableEq___redArg(v_00_u03b1eqDec_64_, v_rDec_66_, v_sDec_68_, v_x_69_, v_x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Prod_Lex_instDecidableRelOfDecidableEq___boxed(lean_object* v_00_u03b1_72_, lean_object* v_00_u03b2_73_, lean_object* v_00_u03b1eqDec_74_, lean_object* v_r_75_, lean_object* v_rDec_76_, lean_object* v_s_77_, lean_object* v_sDec_78_, lean_object* v_x_79_, lean_object* v_x_80_){
_start:
{
uint8_t v_res_81_; lean_object* v_r_82_; 
v_res_81_ = l_Prod_Lex_instDecidableRelOfDecidableEq(v_00_u03b1_72_, v_00_u03b2_73_, v_00_u03b1eqDec_74_, v_r_75_, v_rDec_76_, v_s_77_, v_sDec_78_, v_x_79_, v_x_80_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT lean_object* l_Prod_lex(lean_object* v_00_u03b1_83_, lean_object* v_00_u03b2_84_, lean_object* v_ha_85_, lean_object* v_hb_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lean_box(0);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Prod_instWellFoundedRelation(lean_object* v_00_u03b1_88_, lean_object* v_00_u03b2_89_, lean_object* v_ha_90_, lean_object* v_hb_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lean_box(0);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Prod_rprod(lean_object* v_00_u03b1_93_, lean_object* v_00_u03b2_94_, lean_object* v_ha_95_, lean_object* v_hb_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lean_box(0);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_PSigma_lex(lean_object* v_00_u03b1_98_, lean_object* v_00_u03b2_99_, lean_object* v_ha_100_, lean_object* v_hb_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lean_box(0);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_PSigma_lex___boxed(lean_object* v_00_u03b1_103_, lean_object* v_00_u03b2_104_, lean_object* v_ha_105_, lean_object* v_hb_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_PSigma_lex(v_00_u03b1_103_, v_00_u03b2_104_, v_ha_105_, v_hb_106_);
lean_dec_ref(v_hb_106_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_PSigma_instWellFoundedRelation(lean_object* v_00_u03b1_108_, lean_object* v_00_u03b2_109_, lean_object* v_ha_110_, lean_object* v_hb_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lean_box(0);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_PSigma_instWellFoundedRelation___boxed(lean_object* v_00_u03b1_113_, lean_object* v_00_u03b2_114_, lean_object* v_ha_115_, lean_object* v_hb_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_PSigma_instWellFoundedRelation(v_00_u03b1_113_, v_00_u03b2_114_, v_ha_115_, v_hb_116_);
lean_dec_ref(v_hb_116_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_PSigma_skipLeft(lean_object* v_00_u03b1_118_, lean_object* v_00_u03b2_119_, lean_object* v_hb_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = lean_box(0);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_eager(lean_object* v_n_122_){
_start:
{
lean_inc(v_n_122_);
return v_n_122_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_eager___boxed(lean_object* v_n_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_WellFounded_Nat_eager(v_n_123_);
lean_dec(v_n_123_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___redArg___lam__0(lean_object* v_x_125_, lean_object* v_hfuel_126_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___redArg___lam__0___boxed(lean_object* v_x_127_, lean_object* v_hfuel_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_WellFounded_Nat_fix_go___redArg___lam__0(v_x_127_, v_hfuel_128_);
lean_dec(v_x_127_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___redArg___lam__1(lean_object* v_ih_130_, lean_object* v_y_131_, lean_object* v_hy_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = lean_apply_2(v_ih_130_, v_y_131_, lean_box(0));
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___redArg___lam__2(lean_object* v_F_134_, lean_object* v_x_135_, lean_object* v_ih_136_, lean_object* v_x_137_, lean_object* v_hfuel_138_){
_start:
{
lean_object* v___f_139_; lean_object* v___x_140_; 
v___f_139_ = lean_alloc_closure((void*)(l_WellFounded_Nat_fix_go___redArg___lam__1), 3, 1);
lean_closure_set(v___f_139_, 0, v_ih_136_);
v___x_140_ = lean_apply_2(v_F_134_, v_x_137_, v___f_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___redArg___lam__2___boxed(lean_object* v_F_141_, lean_object* v_x_142_, lean_object* v_ih_143_, lean_object* v_x_144_, lean_object* v_hfuel_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_WellFounded_Nat_fix_go___redArg___lam__2(v_F_141_, v_x_142_, v_ih_143_, v_x_144_, v_hfuel_145_);
lean_dec(v_x_142_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___redArg(lean_object* v_F_148_, lean_object* v_fuel_149_, lean_object* v_x_150_){
_start:
{
lean_object* v___f_151_; lean_object* v___f_152_; lean_object* v___x_10__overap_153_; lean_object* v___x_154_; 
v___f_151_ = ((lean_object*)(l_WellFounded_Nat_fix_go___redArg___closed__0));
v___f_152_ = lean_alloc_closure((void*)(l_WellFounded_Nat_fix_go___redArg___lam__2___boxed), 5, 1);
lean_closure_set(v___f_152_, 0, v_F_148_);
v___x_10__overap_153_ = l_Nat_recCompiled___redArg(v___f_151_, v___f_152_, v_fuel_149_);
v___x_154_ = lean_apply_2(v___x_10__overap_153_, v_x_150_, lean_box(0));
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___redArg___boxed(lean_object* v_F_155_, lean_object* v_fuel_156_, lean_object* v_x_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_WellFounded_Nat_fix_go___redArg(v_F_155_, v_fuel_156_, v_x_157_);
lean_dec(v_fuel_156_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go(lean_object* v_00_u03b1_159_, lean_object* v_motive_160_, lean_object* v_h_161_, lean_object* v_F_162_, lean_object* v_fuel_163_, lean_object* v_x_164_, lean_object* v_a_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_WellFounded_Nat_fix_go___redArg(v_F_162_, v_fuel_163_, v_x_164_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___boxed(lean_object* v_00_u03b1_167_, lean_object* v_motive_168_, lean_object* v_h_169_, lean_object* v_F_170_, lean_object* v_fuel_171_, lean_object* v_x_172_, lean_object* v_a_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_WellFounded_Nat_fix_go(v_00_u03b1_167_, v_motive_168_, v_h_169_, v_F_170_, v_fuel_171_, v_x_172_, v_a_173_);
lean_dec(v_fuel_171_);
lean_dec_ref(v_h_169_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix___redArg(lean_object* v_h_175_, lean_object* v_F_176_, lean_object* v_x_177_){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
lean_inc(v_x_177_);
v___x_178_ = lean_apply_1(v_h_175_, v_x_177_);
v___x_179_ = lean_unsigned_to_nat(1u);
v___x_180_ = lean_nat_add(v___x_178_, v___x_179_);
lean_dec(v___x_178_);
v___x_181_ = l_WellFounded_Nat_fix_go___redArg(v_F_176_, v___x_180_, v_x_177_);
lean_dec(v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix(lean_object* v_00_u03b1_182_, lean_object* v_motive_183_, lean_object* v_h_184_, lean_object* v_F_185_, lean_object* v_x_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_WellFounded_Nat_fix___redArg(v_h_184_, v_F_185_, v_x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_wfParam___redArg(lean_object* v_a_188_){
_start:
{
lean_inc(v_a_188_);
return v_a_188_;
}
}
LEAN_EXPORT lean_object* l_wfParam___redArg___boxed(lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_wfParam___redArg(v_a_189_);
lean_dec(v_a_189_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_wfParam(lean_object* v_00_u03b1_191_, lean_object* v_a_192_){
_start:
{
lean_inc(v_a_192_);
return v_a_192_;
}
}
LEAN_EXPORT lean_object* l_wfParam___boxed(lean_object* v_00_u03b1_193_, lean_object* v_a_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_wfParam(v_00_u03b1_193_, v_a_194_);
lean_dec(v_a_194_);
return v_res_195_;
}
}
lean_object* runtime_initialize_Init_BinderNameHint(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_WF(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_BinderNameHint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Nat_lt__wfRel = _init_l_Nat_lt__wfRel();
lean_mark_persistent(l_Nat_lt__wfRel);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_WF(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_BinderNameHint(uint8_t builtin);
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_WF(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_BinderNameHint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_WF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_WF(builtin);
}
#ifdef __cplusplus
}
#endif
