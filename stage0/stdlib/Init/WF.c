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
LEAN_EXPORT lean_object* l_emptyWf___redArg();
LEAN_EXPORT lean_object* l_emptyWf___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_emptyWf(lean_object*);
LEAN_EXPORT lean_object* l_invImage___redArg();
LEAN_EXPORT lean_object* l_invImage___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_invImage(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_invImage___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_lt__wfRel;
LEAN_EXPORT lean_object* l_measure___redArg();
LEAN_EXPORT lean_object* l_measure___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_measure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_measure___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_sizeOfWFRel___redArg();
LEAN_EXPORT lean_object* l_sizeOfWFRel___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_sizeOfWFRel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_sizeOfWFRel___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Prod_Lex_instDecidableRelOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_Lex_instDecidableRelOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Prod_Lex_instDecidableRelOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_Lex_instDecidableRelOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_lex___redArg();
LEAN_EXPORT lean_object* l_Prod_lex___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Prod_lex(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_instWellFoundedRelation___redArg();
LEAN_EXPORT lean_object* l_Prod_instWellFoundedRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Prod_instWellFoundedRelation(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_rprod___redArg();
LEAN_EXPORT lean_object* l_Prod_rprod___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Prod_rprod(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PSigma_lex___redArg();
LEAN_EXPORT lean_object* l_PSigma_lex___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_PSigma_lex(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PSigma_lex___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PSigma_instWellFoundedRelation___redArg();
LEAN_EXPORT lean_object* l_PSigma_instWellFoundedRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_PSigma_instWellFoundedRelation(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PSigma_instWellFoundedRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PSigma_skipLeft___redArg();
LEAN_EXPORT lean_object* l_PSigma_skipLeft___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_emptyWf___redArg(){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_box(0);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_emptyWf___redArg___boxed(lean_object* v___dummy_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_emptyWf___redArg();
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_emptyWf(lean_object* v_00_u03b1_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_box(0);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_invImage___redArg(){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lean_box(0);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_invImage___redArg___boxed(lean_object* v___dummy_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_invImage___redArg();
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_invImage(lean_object* v_00_u03b1_23_, lean_object* v_00_u03b2_24_, lean_object* v_f_25_, lean_object* v_h_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_box(0);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_invImage___boxed(lean_object* v_00_u03b1_28_, lean_object* v_00_u03b2_29_, lean_object* v_f_30_, lean_object* v_h_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_invImage(v_00_u03b1_28_, v_00_u03b2_29_, v_f_30_, v_h_31_);
lean_dec(v_f_30_);
return v_res_32_;
}
}
static lean_object* _init_l_Nat_lt__wfRel(void){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_box(0);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_measure___redArg(){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lean_box(0);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_measure___redArg___boxed(lean_object* v___dummy_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_measure___redArg();
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_measure(lean_object* v_00_u03b1_38_, lean_object* v_f_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_box(0);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_measure___boxed(lean_object* v_00_u03b1_41_, lean_object* v_f_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_measure(v_00_u03b1_41_, v_f_42_);
lean_dec_ref(v_f_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_sizeOfWFRel___redArg(){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_box(0);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_sizeOfWFRel___redArg___boxed(lean_object* v___dummy_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_sizeOfWFRel___redArg();
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_sizeOfWFRel(lean_object* v_00_u03b1_48_, lean_object* v_inst_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lean_box(0);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_sizeOfWFRel___boxed(lean_object* v_00_u03b1_51_, lean_object* v_inst_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_sizeOfWFRel(v_00_u03b1_51_, v_inst_52_);
lean_dec_ref(v_inst_52_);
return v_res_53_;
}
}
LEAN_EXPORT uint8_t l_Prod_Lex_instDecidableRelOfDecidableEq___redArg(lean_object* v_00_u03b1eqDec_54_, lean_object* v_rDec_55_, lean_object* v_sDec_56_, lean_object* v_x_57_, lean_object* v_x_58_){
_start:
{
lean_object* v_fst_59_; lean_object* v_snd_60_; lean_object* v_fst_61_; lean_object* v_snd_62_; lean_object* v_decide_63_; lean_object* v_decide_64_; uint8_t v___x_65_; 
v_fst_59_ = lean_ctor_get(v_x_57_, 0);
lean_inc_n(v_fst_59_, 2);
v_snd_60_ = lean_ctor_get(v_x_57_, 1);
lean_inc(v_snd_60_);
lean_dec_ref(v_x_57_);
v_fst_61_ = lean_ctor_get(v_x_58_, 0);
lean_inc_n(v_fst_61_, 2);
v_snd_62_ = lean_ctor_get(v_x_58_, 1);
lean_inc(v_snd_62_);
lean_dec_ref(v_x_58_);
v_decide_63_ = lean_apply_2(v_00_u03b1eqDec_54_, v_fst_59_, v_fst_61_);
v_decide_64_ = lean_apply_2(v_rDec_55_, v_fst_59_, v_fst_61_);
v___x_65_ = lean_unbox(v_decide_64_);
if (v___x_65_ == 0)
{
uint8_t v___x_66_; 
v___x_66_ = lean_unbox(v_decide_63_);
if (v___x_66_ == 0)
{
uint8_t v___x_67_; 
lean_dec(v_snd_62_);
lean_dec(v_snd_60_);
lean_dec_ref(v_sDec_56_);
v___x_67_ = lean_unbox(v_decide_63_);
return v___x_67_;
}
else
{
lean_object* v_x_68_; uint8_t v___x_69_; 
v_x_68_ = lean_apply_2(v_sDec_56_, v_snd_60_, v_snd_62_);
v___x_69_ = lean_unbox(v_x_68_);
return v___x_69_;
}
}
else
{
uint8_t v___x_70_; 
lean_dec(v_snd_62_);
lean_dec(v_snd_60_);
lean_dec_ref(v_sDec_56_);
v___x_70_ = lean_unbox(v_decide_64_);
return v___x_70_;
}
}
}
LEAN_EXPORT lean_object* l_Prod_Lex_instDecidableRelOfDecidableEq___redArg___boxed(lean_object* v_00_u03b1eqDec_71_, lean_object* v_rDec_72_, lean_object* v_sDec_73_, lean_object* v_x_74_, lean_object* v_x_75_){
_start:
{
uint8_t v_res_76_; lean_object* v_r_77_; 
v_res_76_ = l_Prod_Lex_instDecidableRelOfDecidableEq___redArg(v_00_u03b1eqDec_71_, v_rDec_72_, v_sDec_73_, v_x_74_, v_x_75_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
LEAN_EXPORT uint8_t l_Prod_Lex_instDecidableRelOfDecidableEq(lean_object* v_00_u03b1_78_, lean_object* v_00_u03b2_79_, lean_object* v_00_u03b1eqDec_80_, lean_object* v_r_81_, lean_object* v_rDec_82_, lean_object* v_s_83_, lean_object* v_sDec_84_, lean_object* v_x_85_, lean_object* v_x_86_){
_start:
{
uint8_t v___x_87_; 
v___x_87_ = l_Prod_Lex_instDecidableRelOfDecidableEq___redArg(v_00_u03b1eqDec_80_, v_rDec_82_, v_sDec_84_, v_x_85_, v_x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Prod_Lex_instDecidableRelOfDecidableEq___boxed(lean_object* v_00_u03b1_88_, lean_object* v_00_u03b2_89_, lean_object* v_00_u03b1eqDec_90_, lean_object* v_r_91_, lean_object* v_rDec_92_, lean_object* v_s_93_, lean_object* v_sDec_94_, lean_object* v_x_95_, lean_object* v_x_96_){
_start:
{
uint8_t v_res_97_; lean_object* v_r_98_; 
v_res_97_ = l_Prod_Lex_instDecidableRelOfDecidableEq(v_00_u03b1_88_, v_00_u03b2_89_, v_00_u03b1eqDec_90_, v_r_91_, v_rDec_92_, v_s_93_, v_sDec_94_, v_x_95_, v_x_96_);
v_r_98_ = lean_box(v_res_97_);
return v_r_98_;
}
}
LEAN_EXPORT lean_object* l_Prod_lex___redArg(){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lean_box(0);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Prod_lex___redArg___boxed(lean_object* v___dummy_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Prod_lex___redArg();
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Prod_lex(lean_object* v_00_u03b1_103_, lean_object* v_00_u03b2_104_, lean_object* v_ha_105_, lean_object* v_hb_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = lean_box(0);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Prod_instWellFoundedRelation___redArg(){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lean_box(0);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Prod_instWellFoundedRelation___redArg___boxed(lean_object* v___dummy_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Prod_instWellFoundedRelation___redArg();
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Prod_instWellFoundedRelation(lean_object* v_00_u03b1_112_, lean_object* v_00_u03b2_113_, lean_object* v_ha_114_, lean_object* v_hb_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_box(0);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Prod_rprod___redArg(){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_box(0);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Prod_rprod___redArg___boxed(lean_object* v___dummy_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Prod_rprod___redArg();
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Prod_rprod(lean_object* v_00_u03b1_121_, lean_object* v_00_u03b2_122_, lean_object* v_ha_123_, lean_object* v_hb_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = lean_box(0);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_PSigma_lex___redArg(){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = lean_box(0);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_PSigma_lex___redArg___boxed(lean_object* v___dummy_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_PSigma_lex___redArg();
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_PSigma_lex(lean_object* v_00_u03b1_130_, lean_object* v_00_u03b2_131_, lean_object* v_ha_132_, lean_object* v_hb_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = lean_box(0);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_PSigma_lex___boxed(lean_object* v_00_u03b1_135_, lean_object* v_00_u03b2_136_, lean_object* v_ha_137_, lean_object* v_hb_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_PSigma_lex(v_00_u03b1_135_, v_00_u03b2_136_, v_ha_137_, v_hb_138_);
lean_dec_ref(v_hb_138_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_PSigma_instWellFoundedRelation___redArg(){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = lean_box(0);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_PSigma_instWellFoundedRelation___redArg___boxed(lean_object* v___dummy_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_PSigma_instWellFoundedRelation___redArg();
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_PSigma_instWellFoundedRelation(lean_object* v_00_u03b1_144_, lean_object* v_00_u03b2_145_, lean_object* v_ha_146_, lean_object* v_hb_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = lean_box(0);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_PSigma_instWellFoundedRelation___boxed(lean_object* v_00_u03b1_149_, lean_object* v_00_u03b2_150_, lean_object* v_ha_151_, lean_object* v_hb_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_PSigma_instWellFoundedRelation(v_00_u03b1_149_, v_00_u03b2_150_, v_ha_151_, v_hb_152_);
lean_dec_ref(v_hb_152_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_PSigma_skipLeft___redArg(){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = lean_box(0);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_PSigma_skipLeft___redArg___boxed(lean_object* v___dummy_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_PSigma_skipLeft___redArg();
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_PSigma_skipLeft(lean_object* v_00_u03b1_158_, lean_object* v_00_u03b2_159_, lean_object* v_hb_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = lean_box(0);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_eager(lean_object* v_n_162_){
_start:
{
lean_inc(v_n_162_);
return v_n_162_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_eager___boxed(lean_object* v_n_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_WellFounded_Nat_eager(v_n_163_);
lean_dec(v_n_163_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___redArg___lam__0(lean_object* v_x_165_, lean_object* v_hfuel_166_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___redArg___lam__0___boxed(lean_object* v_x_167_, lean_object* v_hfuel_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_WellFounded_Nat_fix_go___redArg___lam__0(v_x_167_, v_hfuel_168_);
lean_dec(v_x_167_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___redArg___lam__1(lean_object* v_ih_170_, lean_object* v_y_171_, lean_object* v_hy_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = lean_apply_2(v_ih_170_, v_y_171_, lean_box(0));
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___redArg___lam__2(lean_object* v_F_174_, lean_object* v_x_175_, lean_object* v_ih_176_, lean_object* v_x_177_, lean_object* v_hfuel_178_){
_start:
{
lean_object* v___f_179_; lean_object* v___x_180_; 
v___f_179_ = lean_alloc_closure((void*)(l_WellFounded_Nat_fix_go___redArg___lam__1), 3, 1);
lean_closure_set(v___f_179_, 0, v_ih_176_);
v___x_180_ = lean_apply_2(v_F_174_, v_x_177_, v___f_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___redArg___lam__2___boxed(lean_object* v_F_181_, lean_object* v_x_182_, lean_object* v_ih_183_, lean_object* v_x_184_, lean_object* v_hfuel_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_WellFounded_Nat_fix_go___redArg___lam__2(v_F_181_, v_x_182_, v_ih_183_, v_x_184_, v_hfuel_185_);
lean_dec(v_x_182_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___redArg(lean_object* v_F_188_, lean_object* v_fuel_189_, lean_object* v_x_190_){
_start:
{
lean_object* v___f_191_; lean_object* v___f_192_; lean_object* v___x_13__overap_193_; lean_object* v___x_194_; 
v___f_191_ = ((lean_object*)(l_WellFounded_Nat_fix_go___redArg___closed__0));
v___f_192_ = lean_alloc_closure((void*)(l_WellFounded_Nat_fix_go___redArg___lam__2___boxed), 5, 1);
lean_closure_set(v___f_192_, 0, v_F_188_);
v___x_13__overap_193_ = l_Nat_recCompiled___redArg(v___f_191_, v___f_192_, v_fuel_189_);
v___x_194_ = lean_apply_2(v___x_13__overap_193_, v_x_190_, lean_box(0));
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___redArg___boxed(lean_object* v_F_195_, lean_object* v_fuel_196_, lean_object* v_x_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_WellFounded_Nat_fix_go___redArg(v_F_195_, v_fuel_196_, v_x_197_);
lean_dec(v_fuel_196_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go(lean_object* v_00_u03b1_199_, lean_object* v_motive_200_, lean_object* v_h_201_, lean_object* v_F_202_, lean_object* v_fuel_203_, lean_object* v_x_204_, lean_object* v_a_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_WellFounded_Nat_fix_go___redArg(v_F_202_, v_fuel_203_, v_x_204_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___boxed(lean_object* v_00_u03b1_207_, lean_object* v_motive_208_, lean_object* v_h_209_, lean_object* v_F_210_, lean_object* v_fuel_211_, lean_object* v_x_212_, lean_object* v_a_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_WellFounded_Nat_fix_go(v_00_u03b1_207_, v_motive_208_, v_h_209_, v_F_210_, v_fuel_211_, v_x_212_, v_a_213_);
lean_dec(v_fuel_211_);
lean_dec_ref(v_h_209_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix___redArg(lean_object* v_h_215_, lean_object* v_F_216_, lean_object* v_x_217_){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
lean_inc(v_x_217_);
v___x_218_ = lean_apply_1(v_h_215_, v_x_217_);
v___x_219_ = lean_unsigned_to_nat(1u);
v___x_220_ = lean_nat_add(v___x_218_, v___x_219_);
lean_dec(v___x_218_);
v___x_221_ = l_WellFounded_Nat_fix_go___redArg(v_F_216_, v___x_220_, v_x_217_);
lean_dec(v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix(lean_object* v_00_u03b1_222_, lean_object* v_motive_223_, lean_object* v_h_224_, lean_object* v_F_225_, lean_object* v_x_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_WellFounded_Nat_fix___redArg(v_h_224_, v_F_225_, v_x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_wfParam___redArg(lean_object* v_a_228_){
_start:
{
lean_inc(v_a_228_);
return v_a_228_;
}
}
LEAN_EXPORT lean_object* l_wfParam___redArg___boxed(lean_object* v_a_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_wfParam___redArg(v_a_229_);
lean_dec(v_a_229_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_wfParam(lean_object* v_00_u03b1_231_, lean_object* v_a_232_){
_start:
{
lean_inc(v_a_232_);
return v_a_232_;
}
}
LEAN_EXPORT lean_object* l_wfParam___boxed(lean_object* v_00_u03b1_233_, lean_object* v_a_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_wfParam(v_00_u03b1_233_, v_a_234_);
lean_dec(v_a_234_);
return v_res_235_;
}
}
lean_object* runtime_initialize_Init_BinderNameHint(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_WF(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
