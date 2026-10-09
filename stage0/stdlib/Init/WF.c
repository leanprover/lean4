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
lean_object* l_emptyWf___redArg(){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_box(0);
return v___x_14_;
}
}
LEAN_EXPORT void l_emptyWf___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_15_;
v_res_15_ = l_emptyWf___redArg();
stack->m_obj
 = v_res_15_;
}
LEAN_EXPORT lean_object* l_emptyWf___redArg___boxed(lean_object* v___dummy_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_emptyWf___redArg();
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_emptyWf(lean_object* v_00_u03b1_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lean_box(0);
return v___x_19_;
}
}
lean_object* l_invImage___redArg(){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_box(0);
return v___x_21_;
}
}
LEAN_EXPORT void l_invImage___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_22_;
v_res_22_ = l_invImage___redArg();
stack->m_obj
 = v_res_22_;
}
LEAN_EXPORT lean_object* l_invImage___redArg___boxed(lean_object* v___dummy_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_invImage___redArg();
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_invImage(lean_object* v_00_u03b1_25_, lean_object* v_00_u03b2_26_, lean_object* v_f_27_, lean_object* v_h_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lean_box(0);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_invImage___boxed(lean_object* v_00_u03b1_30_, lean_object* v_00_u03b2_31_, lean_object* v_f_32_, lean_object* v_h_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_invImage(v_00_u03b1_30_, v_00_u03b2_31_, v_f_32_, v_h_33_);
lean_dec(v_f_32_);
return v_res_34_;
}
}
static lean_object* _init_l_Nat_lt__wfRel(void){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lean_box(0);
return v___x_35_;
}
}
lean_object* l_measure___redArg(){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_box(0);
return v___x_37_;
}
}
LEAN_EXPORT void l_measure___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_38_;
v_res_38_ = l_measure___redArg();
stack->m_obj
 = v_res_38_;
}
LEAN_EXPORT lean_object* l_measure___redArg___boxed(lean_object* v___dummy_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_measure___redArg();
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_measure(lean_object* v_00_u03b1_41_, lean_object* v_f_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_box(0);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_measure___boxed(lean_object* v_00_u03b1_44_, lean_object* v_f_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_measure(v_00_u03b1_44_, v_f_45_);
lean_dec_ref(v_f_45_);
return v_res_46_;
}
}
lean_object* l_sizeOfWFRel___redArg(){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lean_box(0);
return v___x_48_;
}
}
LEAN_EXPORT void l_sizeOfWFRel___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_49_;
v_res_49_ = l_sizeOfWFRel___redArg();
stack->m_obj
 = v_res_49_;
}
LEAN_EXPORT lean_object* l_sizeOfWFRel___redArg___boxed(lean_object* v___dummy_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_sizeOfWFRel___redArg();
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_sizeOfWFRel(lean_object* v_00_u03b1_52_, lean_object* v_inst_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = lean_box(0);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_sizeOfWFRel___boxed(lean_object* v_00_u03b1_55_, lean_object* v_inst_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_sizeOfWFRel(v_00_u03b1_55_, v_inst_56_);
lean_dec_ref(v_inst_56_);
return v_res_57_;
}
}
uint8_t l_Prod_Lex_instDecidableRelOfDecidableEq___redArg(lean_object* v_00_u03b1eqDec_58_, lean_object* v_rDec_59_, lean_object* v_sDec_60_, lean_object* v_x_61_, lean_object* v_x_62_){
_start:
{
lean_object* v_fst_63_; lean_object* v_snd_64_; lean_object* v_fst_65_; lean_object* v_snd_66_; lean_object* v_decide_67_; uint8_t v___x_68_; 
v_fst_63_ = lean_ctor_get(v_x_61_, 0);
lean_inc_n(v_fst_63_, 2);
v_snd_64_ = lean_ctor_get(v_x_61_, 1);
lean_inc(v_snd_64_);
lean_dec_ref(v_x_61_);
v_fst_65_ = lean_ctor_get(v_x_62_, 0);
lean_inc_n(v_fst_65_, 2);
v_snd_66_ = lean_ctor_get(v_x_62_, 1);
lean_inc(v_snd_66_);
lean_dec_ref(v_x_62_);
v_decide_67_ = lean_apply_2(v_rDec_59_, v_fst_63_, v_fst_65_);
v___x_68_ = lean_unbox(v_decide_67_);
if (v___x_68_ == 0)
{
lean_object* v_decide_69_; uint8_t v___x_70_; 
v_decide_69_ = lean_apply_2(v_00_u03b1eqDec_58_, v_fst_63_, v_fst_65_);
v___x_70_ = lean_unbox(v_decide_69_);
if (v___x_70_ == 0)
{
uint8_t v___x_71_; 
lean_dec(v_snd_66_);
lean_dec(v_snd_64_);
lean_dec_ref(v_sDec_60_);
v___x_71_ = lean_unbox(v_decide_69_);
return v___x_71_;
}
else
{
lean_object* v_x_72_; uint8_t v___x_73_; 
v_x_72_ = lean_apply_2(v_sDec_60_, v_snd_64_, v_snd_66_);
v___x_73_ = lean_unbox(v_x_72_);
return v___x_73_;
}
}
else
{
uint8_t v___x_74_; 
lean_dec(v_snd_66_);
lean_dec(v_fst_65_);
lean_dec(v_snd_64_);
lean_dec(v_fst_63_);
lean_dec_ref(v_sDec_60_);
lean_dec_ref(v_00_u03b1eqDec_58_);
v___x_74_ = lean_unbox(v_decide_67_);
return v___x_74_;
}
}
}
LEAN_EXPORT void l_Prod_Lex_instDecidableRelOfDecidableEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_00_u03b1eqDec_58_ = stack[0].m_obj;
lean_object* v_rDec_59_ = stack[1].m_obj;
lean_object* v_sDec_60_ = stack[2].m_obj;
lean_object* v_x_61_ = stack[3].m_obj;
lean_object* v_x_62_ = stack[4].m_obj;
uint8_t v_res_75_;
v_res_75_ = l_Prod_Lex_instDecidableRelOfDecidableEq___redArg(v_00_u03b1eqDec_58_, v_rDec_59_, v_sDec_60_, v_x_61_, v_x_62_);
stack->m_num = v_res_75_;
}
LEAN_EXPORT lean_object* l_Prod_Lex_instDecidableRelOfDecidableEq___redArg___boxed(lean_object* v_00_u03b1eqDec_76_, lean_object* v_rDec_77_, lean_object* v_sDec_78_, lean_object* v_x_79_, lean_object* v_x_80_){
_start:
{
uint8_t v_res_81_; lean_object* v_r_82_; 
v_res_81_ = l_Prod_Lex_instDecidableRelOfDecidableEq___redArg(v_00_u03b1eqDec_76_, v_rDec_77_, v_sDec_78_, v_x_79_, v_x_80_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
uint8_t l_Prod_Lex_instDecidableRelOfDecidableEq(lean_object* v_00_u03b1_83_, lean_object* v_00_u03b2_84_, lean_object* v_00_u03b1eqDec_85_, lean_object* v_r_86_, lean_object* v_rDec_87_, lean_object* v_s_88_, lean_object* v_sDec_89_, lean_object* v_x_90_, lean_object* v_x_91_){
_start:
{
uint8_t v___x_92_; 
v___x_92_ = l_Prod_Lex_instDecidableRelOfDecidableEq___redArg(v_00_u03b1eqDec_85_, v_rDec_87_, v_sDec_89_, v_x_90_, v_x_91_);
return v___x_92_;
}
}
LEAN_EXPORT void l_Prod_Lex_instDecidableRelOfDecidableEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_00_u03b1eqDec_85_ = stack[2].m_obj;
lean_object* v_rDec_87_ = stack[4].m_obj;
lean_object* v_sDec_89_ = stack[6].m_obj;
lean_object* v_x_90_ = stack[7].m_obj;
lean_object* v_x_91_ = stack[8].m_obj;
uint8_t v_res_93_;
v_res_93_ = l_Prod_Lex_instDecidableRelOfDecidableEq(lean_box(0), lean_box(0), v_00_u03b1eqDec_85_, lean_box(0), v_rDec_87_, lean_box(0), v_sDec_89_, v_x_90_, v_x_91_);
stack->m_num = v_res_93_;
}
LEAN_EXPORT lean_object* l_Prod_Lex_instDecidableRelOfDecidableEq___boxed(lean_object* v_00_u03b1_94_, lean_object* v_00_u03b2_95_, lean_object* v_00_u03b1eqDec_96_, lean_object* v_r_97_, lean_object* v_rDec_98_, lean_object* v_s_99_, lean_object* v_sDec_100_, lean_object* v_x_101_, lean_object* v_x_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = l_Prod_Lex_instDecidableRelOfDecidableEq(v_00_u03b1_94_, v_00_u03b2_95_, v_00_u03b1eqDec_96_, v_r_97_, v_rDec_98_, v_s_99_, v_sDec_100_, v_x_101_, v_x_102_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
lean_object* l_Prod_lex___redArg(){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = lean_box(0);
return v___x_106_;
}
}
LEAN_EXPORT void l_Prod_lex___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_107_;
v_res_107_ = l_Prod_lex___redArg();
stack->m_obj
 = v_res_107_;
}
LEAN_EXPORT lean_object* l_Prod_lex___redArg___boxed(lean_object* v___dummy_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Prod_lex___redArg();
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Prod_lex(lean_object* v_00_u03b1_110_, lean_object* v_00_u03b2_111_, lean_object* v_ha_112_, lean_object* v_hb_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = lean_box(0);
return v___x_114_;
}
}
lean_object* l_Prod_instWellFoundedRelation___redArg(){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_box(0);
return v___x_116_;
}
}
LEAN_EXPORT void l_Prod_instWellFoundedRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_117_;
v_res_117_ = l_Prod_instWellFoundedRelation___redArg();
stack->m_obj
 = v_res_117_;
}
LEAN_EXPORT lean_object* l_Prod_instWellFoundedRelation___redArg___boxed(lean_object* v___dummy_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Prod_instWellFoundedRelation___redArg();
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Prod_instWellFoundedRelation(lean_object* v_00_u03b1_120_, lean_object* v_00_u03b2_121_, lean_object* v_ha_122_, lean_object* v_hb_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = lean_box(0);
return v___x_124_;
}
}
lean_object* l_Prod_rprod___redArg(){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lean_box(0);
return v___x_126_;
}
}
LEAN_EXPORT void l_Prod_rprod___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_127_;
v_res_127_ = l_Prod_rprod___redArg();
stack->m_obj
 = v_res_127_;
}
LEAN_EXPORT lean_object* l_Prod_rprod___redArg___boxed(lean_object* v___dummy_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Prod_rprod___redArg();
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Prod_rprod(lean_object* v_00_u03b1_130_, lean_object* v_00_u03b2_131_, lean_object* v_ha_132_, lean_object* v_hb_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = lean_box(0);
return v___x_134_;
}
}
lean_object* l_PSigma_lex___redArg(){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = lean_box(0);
return v___x_136_;
}
}
LEAN_EXPORT void l_PSigma_lex___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_137_;
v_res_137_ = l_PSigma_lex___redArg();
stack->m_obj
 = v_res_137_;
}
LEAN_EXPORT lean_object* l_PSigma_lex___redArg___boxed(lean_object* v___dummy_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_PSigma_lex___redArg();
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_PSigma_lex(lean_object* v_00_u03b1_140_, lean_object* v_00_u03b2_141_, lean_object* v_ha_142_, lean_object* v_hb_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = lean_box(0);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_PSigma_lex___boxed(lean_object* v_00_u03b1_145_, lean_object* v_00_u03b2_146_, lean_object* v_ha_147_, lean_object* v_hb_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_PSigma_lex(v_00_u03b1_145_, v_00_u03b2_146_, v_ha_147_, v_hb_148_);
lean_dec_ref(v_hb_148_);
return v_res_149_;
}
}
lean_object* l_PSigma_instWellFoundedRelation___redArg(){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lean_box(0);
return v___x_151_;
}
}
LEAN_EXPORT void l_PSigma_instWellFoundedRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_152_;
v_res_152_ = l_PSigma_instWellFoundedRelation___redArg();
stack->m_obj
 = v_res_152_;
}
LEAN_EXPORT lean_object* l_PSigma_instWellFoundedRelation___redArg___boxed(lean_object* v___dummy_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_PSigma_instWellFoundedRelation___redArg();
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_PSigma_instWellFoundedRelation(lean_object* v_00_u03b1_155_, lean_object* v_00_u03b2_156_, lean_object* v_ha_157_, lean_object* v_hb_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = lean_box(0);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_PSigma_instWellFoundedRelation___boxed(lean_object* v_00_u03b1_160_, lean_object* v_00_u03b2_161_, lean_object* v_ha_162_, lean_object* v_hb_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_PSigma_instWellFoundedRelation(v_00_u03b1_160_, v_00_u03b2_161_, v_ha_162_, v_hb_163_);
lean_dec_ref(v_hb_163_);
return v_res_164_;
}
}
lean_object* l_PSigma_skipLeft___redArg(){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_box(0);
return v___x_166_;
}
}
LEAN_EXPORT void l_PSigma_skipLeft___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_167_;
v_res_167_ = l_PSigma_skipLeft___redArg();
stack->m_obj
 = v_res_167_;
}
LEAN_EXPORT lean_object* l_PSigma_skipLeft___redArg___boxed(lean_object* v___dummy_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_PSigma_skipLeft___redArg();
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_PSigma_skipLeft(lean_object* v_00_u03b1_170_, lean_object* v_00_u03b2_171_, lean_object* v_hb_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = lean_box(0);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_eager(lean_object* v_n_174_){
_start:
{
lean_inc(v_n_174_);
return v_n_174_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_eager___boxed(lean_object* v_n_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_WellFounded_Nat_eager(v_n_175_);
lean_dec(v_n_175_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___redArg___lam__0(lean_object* v_x_177_, lean_object* v_hfuel_178_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___redArg___lam__0___boxed(lean_object* v_x_179_, lean_object* v_hfuel_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_WellFounded_Nat_fix_go___redArg___lam__0(v_x_179_, v_hfuel_180_);
lean_dec(v_x_179_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___redArg___lam__1(lean_object* v_ih_182_, lean_object* v_y_183_, lean_object* v_hy_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = lean_apply_2(v_ih_182_, v_y_183_, lean_box(0));
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___redArg___lam__2(lean_object* v_F_186_, lean_object* v_x_187_, lean_object* v_ih_188_, lean_object* v_x_189_, lean_object* v_hfuel_190_){
_start:
{
lean_object* v___f_191_; lean_object* v___x_192_; 
v___f_191_ = lean_alloc_closure((void*)(l_WellFounded_Nat_fix_go___redArg___lam__1), 3, 1);
lean_closure_set(v___f_191_, 0, v_ih_188_);
v___x_192_ = lean_apply_2(v_F_186_, v_x_189_, v___f_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___redArg___lam__2___boxed(lean_object* v_F_193_, lean_object* v_x_194_, lean_object* v_ih_195_, lean_object* v_x_196_, lean_object* v_hfuel_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_WellFounded_Nat_fix_go___redArg___lam__2(v_F_193_, v_x_194_, v_ih_195_, v_x_196_, v_hfuel_197_);
lean_dec(v_x_194_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___redArg(lean_object* v_F_200_, lean_object* v_fuel_201_, lean_object* v_x_202_){
_start:
{
lean_object* v___f_203_; lean_object* v___f_204_; lean_object* v___x_13__overap_205_; lean_object* v___x_206_; 
v___f_203_ = ((lean_object*)(l_WellFounded_Nat_fix_go___redArg___closed__0));
v___f_204_ = lean_alloc_closure((void*)(l_WellFounded_Nat_fix_go___redArg___lam__2___boxed), 5, 1);
lean_closure_set(v___f_204_, 0, v_F_200_);
v___x_13__overap_205_ = l_Nat_recCompiled___redArg(v___f_203_, v___f_204_, v_fuel_201_);
v___x_206_ = lean_apply_2(v___x_13__overap_205_, v_x_202_, lean_box(0));
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___redArg___boxed(lean_object* v_F_207_, lean_object* v_fuel_208_, lean_object* v_x_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_WellFounded_Nat_fix_go___redArg(v_F_207_, v_fuel_208_, v_x_209_);
lean_dec(v_fuel_208_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go(lean_object* v_00_u03b1_211_, lean_object* v_motive_212_, lean_object* v_h_213_, lean_object* v_F_214_, lean_object* v_fuel_215_, lean_object* v_x_216_, lean_object* v_a_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_WellFounded_Nat_fix_go___redArg(v_F_214_, v_fuel_215_, v_x_216_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix_go___boxed(lean_object* v_00_u03b1_219_, lean_object* v_motive_220_, lean_object* v_h_221_, lean_object* v_F_222_, lean_object* v_fuel_223_, lean_object* v_x_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_WellFounded_Nat_fix_go(v_00_u03b1_219_, v_motive_220_, v_h_221_, v_F_222_, v_fuel_223_, v_x_224_, v_a_225_);
lean_dec(v_fuel_223_);
lean_dec_ref(v_h_221_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix___redArg(lean_object* v_h_227_, lean_object* v_F_228_, lean_object* v_x_229_){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
lean_inc(v_x_229_);
v___x_230_ = lean_apply_1(v_h_227_, v_x_229_);
v___x_231_ = lean_unsigned_to_nat(1u);
v___x_232_ = lean_nat_add(v___x_230_, v___x_231_);
lean_dec(v___x_230_);
v___x_233_ = l_WellFounded_Nat_fix_go___redArg(v_F_228_, v___x_232_, v_x_229_);
lean_dec(v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_Nat_fix(lean_object* v_00_u03b1_234_, lean_object* v_motive_235_, lean_object* v_h_236_, lean_object* v_F_237_, lean_object* v_x_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_WellFounded_Nat_fix___redArg(v_h_236_, v_F_237_, v_x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_wfParam___redArg(lean_object* v_a_240_){
_start:
{
lean_inc(v_a_240_);
return v_a_240_;
}
}
LEAN_EXPORT lean_object* l_wfParam___redArg___boxed(lean_object* v_a_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_wfParam___redArg(v_a_241_);
lean_dec(v_a_241_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_wfParam(lean_object* v_00_u03b1_243_, lean_object* v_a_244_){
_start:
{
lean_inc(v_a_244_);
return v_a_244_;
}
}
LEAN_EXPORT lean_object* l_wfParam___boxed(lean_object* v_00_u03b1_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_wfParam(v_00_u03b1_245_, v_a_246_);
lean_dec(v_a_246_);
return v_res_247_;
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
