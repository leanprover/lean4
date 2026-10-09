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
LEAN_EXPORT lean_object* l_Option_instMembership___redArg();
LEAN_EXPORT lean_object* l_Option_instMembership___redArg___boxed(lean_object*);
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
lean_object* l_Option_instMembership___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT void l_Option_instMembership___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3_;
v_res_3_ = l_Option_instMembership___redArg();
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l_Option_instMembership___redArg___boxed(lean_object* v___dummy_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Option_instMembership___redArg();
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Option_instMembership(lean_object* v_00_u03b1_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_box(0);
return v___x_7_;
}
}
uint8_t l_Option_instDecidableMemOfDecidableEq___redArg(lean_object* v_inst_8_, lean_object* v_j_9_, lean_object* v_o_10_){
_start:
{
lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_11_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_11_, 0, v_j_9_);
v___x_12_ = l_Option_instDecidableEq___redArg(v_inst_8_, v_o_10_, v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT void l_Option_instDecidableMemOfDecidableEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_8_ = stack[0].m_obj;
lean_object* v_j_9_ = stack[1].m_obj;
lean_object* v_o_10_ = stack[2].m_obj;
uint8_t v_res_13_;
v_res_13_ = l_Option_instDecidableMemOfDecidableEq___redArg(v_inst_8_, v_j_9_, v_o_10_);
stack->m_num = v_res_13_;
}
LEAN_EXPORT lean_object* l_Option_instDecidableMemOfDecidableEq___redArg___boxed(lean_object* v_inst_14_, lean_object* v_j_15_, lean_object* v_o_16_){
_start:
{
uint8_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = l_Option_instDecidableMemOfDecidableEq___redArg(v_inst_14_, v_j_15_, v_o_16_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
uint8_t l_Option_instDecidableMemOfDecidableEq(lean_object* v_00_u03b1_19_, lean_object* v_inst_20_, lean_object* v_j_21_, lean_object* v_o_22_){
_start:
{
uint8_t v___x_23_; 
v___x_23_ = l_Option_instDecidableMemOfDecidableEq___redArg(v_inst_20_, v_j_21_, v_o_22_);
return v___x_23_;
}
}
LEAN_EXPORT void l_Option_instDecidableMemOfDecidableEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_20_ = stack[1].m_obj;
lean_object* v_j_21_ = stack[2].m_obj;
lean_object* v_o_22_ = stack[3].m_obj;
uint8_t v_res_24_;
v_res_24_ = l_Option_instDecidableMemOfDecidableEq(lean_box(0), v_inst_20_, v_j_21_, v_o_22_);
stack->m_num = v_res_24_;
}
LEAN_EXPORT lean_object* l_Option_instDecidableMemOfDecidableEq___boxed(lean_object* v_00_u03b1_25_, lean_object* v_inst_26_, lean_object* v_j_27_, lean_object* v_o_28_){
_start:
{
uint8_t v_res_29_; lean_object* v_r_30_; 
v_res_29_ = l_Option_instDecidableMemOfDecidableEq(v_00_u03b1_25_, v_inst_26_, v_j_27_, v_o_28_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
uint8_t l_Option_decidableForallMem___redArg(lean_object* v_inst_31_, lean_object* v_x_32_){
_start:
{
if (lean_obj_tag(v_x_32_) == 0)
{
uint8_t v___x_33_; 
lean_dec_ref(v_inst_31_);
v___x_33_ = 1;
return v___x_33_;
}
else
{
lean_object* v_val_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
v_val_34_ = lean_ctor_get(v_x_32_, 0);
lean_inc(v_val_34_);
lean_dec_ref_known(v_x_32_, 1);
v___x_35_ = lean_apply_1(v_inst_31_, v_val_34_);
v___x_36_ = lean_unbox(v___x_35_);
return v___x_36_;
}
}
}
LEAN_EXPORT void l_Option_decidableForallMem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_31_ = stack[0].m_obj;
lean_object* v_x_32_ = stack[1].m_obj;
uint8_t v_res_37_;
v_res_37_ = l_Option_decidableForallMem___redArg(v_inst_31_, v_x_32_);
stack->m_num = v_res_37_;
}
LEAN_EXPORT lean_object* l_Option_decidableForallMem___redArg___boxed(lean_object* v_inst_38_, lean_object* v_x_39_){
_start:
{
uint8_t v_res_40_; lean_object* v_r_41_; 
v_res_40_ = l_Option_decidableForallMem___redArg(v_inst_38_, v_x_39_);
v_r_41_ = lean_box(v_res_40_);
return v_r_41_;
}
}
uint8_t l_Option_decidableForallMem(lean_object* v_00_u03b1_42_, lean_object* v_p_43_, lean_object* v_inst_44_, lean_object* v_x_45_){
_start:
{
uint8_t v___x_46_; 
v___x_46_ = l_Option_decidableForallMem___redArg(v_inst_44_, v_x_45_);
return v___x_46_;
}
}
LEAN_EXPORT void l_Option_decidableForallMem_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_44_ = stack[2].m_obj;
lean_object* v_x_45_ = stack[3].m_obj;
uint8_t v_res_47_;
v_res_47_ = l_Option_decidableForallMem(lean_box(0), lean_box(0), v_inst_44_, v_x_45_);
stack->m_num = v_res_47_;
}
LEAN_EXPORT lean_object* l_Option_decidableForallMem___boxed(lean_object* v_00_u03b1_48_, lean_object* v_p_49_, lean_object* v_inst_50_, lean_object* v_x_51_){
_start:
{
uint8_t v_res_52_; lean_object* v_r_53_; 
v_res_52_ = l_Option_decidableForallMem(v_00_u03b1_48_, v_p_49_, v_inst_50_, v_x_51_);
v_r_53_ = lean_box(v_res_52_);
return v_r_53_;
}
}
uint8_t l_Option_decidableExistsMem___redArg(lean_object* v_inst_54_, lean_object* v_x_55_){
_start:
{
if (lean_obj_tag(v_x_55_) == 0)
{
uint8_t v___x_56_; 
lean_dec_ref(v_inst_54_);
v___x_56_ = 0;
return v___x_56_;
}
else
{
lean_object* v_val_57_; lean_object* v___x_58_; uint8_t v___x_59_; 
v_val_57_ = lean_ctor_get(v_x_55_, 0);
lean_inc(v_val_57_);
lean_dec_ref_known(v_x_55_, 1);
v___x_58_ = lean_apply_1(v_inst_54_, v_val_57_);
v___x_59_ = lean_unbox(v___x_58_);
return v___x_59_;
}
}
}
LEAN_EXPORT void l_Option_decidableExistsMem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_54_ = stack[0].m_obj;
lean_object* v_x_55_ = stack[1].m_obj;
uint8_t v_res_60_;
v_res_60_ = l_Option_decidableExistsMem___redArg(v_inst_54_, v_x_55_);
stack->m_num = v_res_60_;
}
LEAN_EXPORT lean_object* l_Option_decidableExistsMem___redArg___boxed(lean_object* v_inst_61_, lean_object* v_x_62_){
_start:
{
uint8_t v_res_63_; lean_object* v_r_64_; 
v_res_63_ = l_Option_decidableExistsMem___redArg(v_inst_61_, v_x_62_);
v_r_64_ = lean_box(v_res_63_);
return v_r_64_;
}
}
uint8_t l_Option_decidableExistsMem(lean_object* v_00_u03b1_65_, lean_object* v_p_66_, lean_object* v_inst_67_, lean_object* v_x_68_){
_start:
{
uint8_t v___x_69_; 
v___x_69_ = l_Option_decidableExistsMem___redArg(v_inst_67_, v_x_68_);
return v___x_69_;
}
}
LEAN_EXPORT void l_Option_decidableExistsMem_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_67_ = stack[2].m_obj;
lean_object* v_x_68_ = stack[3].m_obj;
uint8_t v_res_70_;
v_res_70_ = l_Option_decidableExistsMem(lean_box(0), lean_box(0), v_inst_67_, v_x_68_);
stack->m_num = v_res_70_;
}
LEAN_EXPORT lean_object* l_Option_decidableExistsMem___boxed(lean_object* v_00_u03b1_71_, lean_object* v_p_72_, lean_object* v_inst_73_, lean_object* v_x_74_){
_start:
{
uint8_t v_res_75_; lean_object* v_r_76_; 
v_res_75_ = l_Option_decidableExistsMem(v_00_u03b1_71_, v_p_72_, v_inst_73_, v_x_74_);
v_r_76_ = lean_box(v_res_75_);
return v_r_76_;
}
}
LEAN_EXPORT lean_object* l_Option_pbind___redArg(lean_object* v_x_77_, lean_object* v_x_78_){
_start:
{
if (lean_obj_tag(v_x_77_) == 0)
{
lean_object* v___x_79_; 
lean_dec_ref(v_x_78_);
v___x_79_ = lean_box(0);
return v___x_79_;
}
else
{
lean_object* v_val_80_; lean_object* v___x_81_; 
v_val_80_ = lean_ctor_get(v_x_77_, 0);
lean_inc(v_val_80_);
lean_dec_ref_known(v_x_77_, 1);
v___x_81_ = lean_apply_2(v_x_78_, v_val_80_, lean_box(0));
return v___x_81_;
}
}
}
LEAN_EXPORT lean_object* l_Option_pbind(lean_object* v_00_u03b1_82_, lean_object* v_00_u03b2_83_, lean_object* v_x_84_, lean_object* v_x_85_){
_start:
{
if (lean_obj_tag(v_x_84_) == 0)
{
lean_object* v___x_86_; 
lean_dec_ref(v_x_85_);
v___x_86_ = lean_box(0);
return v___x_86_;
}
else
{
lean_object* v_val_87_; lean_object* v___x_88_; 
v_val_87_ = lean_ctor_get(v_x_84_, 0);
lean_inc(v_val_87_);
lean_dec_ref_known(v_x_84_, 1);
v___x_88_ = lean_apply_2(v_x_85_, v_val_87_, lean_box(0));
return v___x_88_;
}
}
}
LEAN_EXPORT lean_object* l_Option_pmap___redArg(lean_object* v_f_89_, lean_object* v_x_90_){
_start:
{
if (lean_obj_tag(v_x_90_) == 0)
{
lean_object* v___x_91_; 
lean_dec(v_f_89_);
v___x_91_ = lean_box(0);
return v___x_91_;
}
else
{
lean_object* v_val_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_100_; 
v_val_92_ = lean_ctor_get(v_x_90_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v_x_90_);
if (v_isSharedCheck_100_ == 0)
{
v___x_94_ = v_x_90_;
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_val_92_);
lean_dec(v_x_90_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_96_; lean_object* v___x_98_; 
v___x_96_ = lean_apply_2(v_f_89_, v_val_92_, lean_box(0));
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v___x_96_);
v___x_98_ = v___x_94_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_pmap(lean_object* v_00_u03b1_101_, lean_object* v_00_u03b2_102_, lean_object* v_p_103_, lean_object* v_f_104_, lean_object* v_x_105_, lean_object* v_x_106_){
_start:
{
if (lean_obj_tag(v_x_105_) == 0)
{
lean_object* v___x_107_; 
lean_dec(v_f_104_);
v___x_107_ = lean_box(0);
return v___x_107_;
}
else
{
lean_object* v_val_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_116_; 
v_val_108_ = lean_ctor_get(v_x_105_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v_x_105_);
if (v_isSharedCheck_116_ == 0)
{
v___x_110_ = v_x_105_;
v_isShared_111_ = v_isSharedCheck_116_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_val_108_);
lean_dec(v_x_105_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_116_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; lean_object* v___x_114_; 
v___x_112_ = lean_apply_2(v_f_104_, v_val_108_, lean_box(0));
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v___x_112_);
v___x_114_ = v___x_110_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v___x_112_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_pelim___redArg(lean_object* v_o_117_, lean_object* v_b_118_, lean_object* v_f_119_){
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
lean_dec_ref_known(v_o_117_, 1);
v___x_121_ = lean_apply_2(v_f_119_, v_val_120_, lean_box(0));
return v___x_121_;
}
}
}
LEAN_EXPORT lean_object* l_Option_pelim___redArg___boxed(lean_object* v_o_122_, lean_object* v_b_123_, lean_object* v_f_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Option_pelim___redArg(v_o_122_, v_b_123_, v_f_124_);
lean_dec(v_b_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Option_pelim(lean_object* v_00_u03b1_126_, lean_object* v_00_u03b2_127_, lean_object* v_o_128_, lean_object* v_b_129_, lean_object* v_f_130_){
_start:
{
if (lean_obj_tag(v_o_128_) == 0)
{
lean_dec(v_f_130_);
lean_inc(v_b_129_);
return v_b_129_;
}
else
{
lean_object* v_val_131_; lean_object* v___x_132_; 
v_val_131_ = lean_ctor_get(v_o_128_, 0);
lean_inc(v_val_131_);
lean_dec_ref_known(v_o_128_, 1);
v___x_132_ = lean_apply_2(v_f_130_, v_val_131_, lean_box(0));
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l_Option_pelim___boxed(lean_object* v_00_u03b1_133_, lean_object* v_00_u03b2_134_, lean_object* v_o_135_, lean_object* v_b_136_, lean_object* v_f_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Option_pelim(v_00_u03b1_133_, v_00_u03b2_134_, v_o_135_, v_b_136_, v_f_137_);
lean_dec(v_b_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Option_pfilter___redArg(lean_object* v_o_139_, lean_object* v_p_140_){
_start:
{
if (lean_obj_tag(v_o_139_) == 0)
{
lean_dec_ref(v_p_140_);
return v_o_139_;
}
else
{
lean_object* v_val_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v_val_141_ = lean_ctor_get(v_o_139_, 0);
lean_inc(v_val_141_);
v___x_142_ = lean_apply_2(v_p_140_, v_val_141_, lean_box(0));
v___x_143_ = lean_unbox(v___x_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; 
lean_dec_ref_known(v_o_139_, 1);
v___x_144_ = lean_box(0);
return v___x_144_;
}
else
{
return v_o_139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_pfilter(lean_object* v_00_u03b1_145_, lean_object* v_o_146_, lean_object* v_p_147_){
_start:
{
if (lean_obj_tag(v_o_146_) == 0)
{
lean_dec_ref(v_p_147_);
return v_o_146_;
}
else
{
lean_object* v_val_148_; lean_object* v___x_149_; uint8_t v___x_150_; 
v_val_148_ = lean_ctor_get(v_o_146_, 0);
lean_inc(v_val_148_);
v___x_149_ = lean_apply_2(v_p_147_, v_val_148_, lean_box(0));
v___x_150_ = lean_unbox(v___x_149_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; 
lean_dec_ref_known(v_o_146_, 1);
v___x_151_ = lean_box(0);
return v___x_151_;
}
else
{
return v_o_146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_forM___redArg(lean_object* v_inst_152_, lean_object* v_x_153_, lean_object* v_x_154_){
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
lean_dec_ref_known(v_x_153_, 1);
v___x_158_ = lean_apply_1(v_x_154_, v_val_157_);
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l_Option_forM(lean_object* v_m_159_, lean_object* v_00_u03b1_160_, lean_object* v_inst_161_, lean_object* v_x_162_, lean_object* v_x_163_){
_start:
{
if (lean_obj_tag(v_x_162_) == 0)
{
lean_object* v___x_164_; lean_object* v___x_165_; 
lean_dec(v_x_163_);
v___x_164_ = lean_box(0);
v___x_165_ = lean_apply_2(v_inst_161_, lean_box(0), v___x_164_);
return v___x_165_;
}
else
{
lean_object* v_val_166_; lean_object* v___x_167_; 
lean_dec(v_inst_161_);
v_val_166_ = lean_ctor_get(v_x_162_, 0);
lean_inc(v_val_166_);
lean_dec_ref_known(v_x_162_, 1);
v___x_167_ = lean_apply_1(v_x_163_, v_val_166_);
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l_Option_instForMOfMonad___redArg(lean_object* v_inst_168_){
_start:
{
lean_object* v_toApplicative_169_; lean_object* v_toPure_170_; lean_object* v___x_171_; 
v_toApplicative_169_ = lean_ctor_get(v_inst_168_, 0);
lean_inc_ref(v_toApplicative_169_);
lean_dec_ref(v_inst_168_);
v_toPure_170_ = lean_ctor_get(v_toApplicative_169_, 1);
lean_inc(v_toPure_170_);
lean_dec_ref(v_toApplicative_169_);
v___x_171_ = lean_alloc_closure((void*)(l_Option_forM), 5, 3);
lean_closure_set(v___x_171_, 0, lean_box(0));
lean_closure_set(v___x_171_, 1, lean_box(0));
lean_closure_set(v___x_171_, 2, v_toPure_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Option_instForMOfMonad(lean_object* v_m_172_, lean_object* v_00_u03b1_173_, lean_object* v_inst_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Option_instForMOfMonad___redArg(v_inst_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Option_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object* v_toPure_176_, lean_object* v_____do__lift_177_){
_start:
{
lean_object* v_a_178_; lean_object* v___x_179_; 
v_a_178_ = lean_ctor_get(v_____do__lift_177_, 0);
lean_inc(v_a_178_);
lean_dec_ref(v_____do__lift_177_);
v___x_179_ = lean_apply_2(v_toPure_176_, lean_box(0), v_a_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Option_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1(lean_object* v_toPure_180_, lean_object* v_toBind_181_, lean_object* v___f_182_, lean_object* v_00_u03b2_183_, lean_object* v_x_184_, lean_object* v_init_185_, lean_object* v_f_186_){
_start:
{
if (lean_obj_tag(v_x_184_) == 0)
{
lean_object* v___x_187_; 
lean_dec(v_f_186_);
lean_dec(v___f_182_);
lean_dec(v_toBind_181_);
v___x_187_ = lean_apply_2(v_toPure_180_, lean_box(0), v_init_185_);
return v___x_187_;
}
else
{
lean_object* v_val_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
lean_dec(v_toPure_180_);
v_val_188_ = lean_ctor_get(v_x_184_, 0);
lean_inc(v_val_188_);
lean_dec_ref_known(v_x_184_, 1);
v___x_189_ = lean_apply_3(v_f_186_, v_val_188_, lean_box(0), v_init_185_);
v___x_190_ = lean_apply_4(v_toBind_181_, lean_box(0), lean_box(0), v___x_189_, v___f_182_);
return v___x_190_;
}
}
}
LEAN_EXPORT lean_object* l_Option_instForIn_x27InferInstanceMembershipOfMonad___redArg(lean_object* v_inst_191_){
_start:
{
lean_object* v_toApplicative_192_; lean_object* v_toBind_193_; lean_object* v_toPure_194_; lean_object* v___f_195_; lean_object* v___f_196_; 
v_toApplicative_192_ = lean_ctor_get(v_inst_191_, 0);
lean_inc_ref(v_toApplicative_192_);
v_toBind_193_ = lean_ctor_get(v_inst_191_, 1);
lean_inc(v_toBind_193_);
lean_dec_ref(v_inst_191_);
v_toPure_194_ = lean_ctor_get(v_toApplicative_192_, 1);
lean_inc_n(v_toPure_194_, 2);
lean_dec_ref(v_toApplicative_192_);
v___f_195_ = lean_alloc_closure((void*)(l_Option_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_195_, 0, v_toPure_194_);
v___f_196_ = lean_alloc_closure((void*)(l_Option_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1), 7, 3);
lean_closure_set(v___f_196_, 0, v_toPure_194_);
lean_closure_set(v___f_196_, 1, v_toBind_193_);
lean_closure_set(v___f_196_, 2, v___f_195_);
return v___f_196_;
}
}
LEAN_EXPORT lean_object* l_Option_instForIn_x27InferInstanceMembershipOfMonad(lean_object* v_m_197_, lean_object* v_00_u03b1_198_, lean_object* v_inst_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Option_instForIn_x27InferInstanceMembershipOfMonad___redArg(v_inst_199_);
return v___x_200_;
}
}
lean_object* runtime_initialize_Init_Data_Option_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Option_Instances(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
