// Lean compiler output
// Module: Init.Grind.Config
// Imports: public import Init.Core
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Grind_instInhabitedConfig_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*12 + 32, .m_other = 12, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1048576) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 1, 0, 1, 1)}};
static const lean_object* l_Lean_Grind_instInhabitedConfig_default___closed__0 = (const lean_object*)&l_Lean_Grind_instInhabitedConfig_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instInhabitedConfig_default = (const lean_object*)&l_Lean_Grind_instInhabitedConfig_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instInhabitedConfig = (const lean_object*)&l_Lean_Grind_instInhabitedConfig_default___closed__0_value;
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_instBEqConfig_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instBEqConfig_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instBEqConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instBEqConfig_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instBEqConfig___closed__0 = (const lean_object*)&l_Lean_Grind_instBEqConfig___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instBEqConfig = (const lean_object*)&l_Lean_Grind_instBEqConfig___closed__0_value;
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(lean_object* v_x_16_, lean_object* v_x_17_){
_start:
{
if (lean_obj_tag(v_x_16_) == 0)
{
if (lean_obj_tag(v_x_17_) == 0)
{
uint8_t v___x_18_; 
v___x_18_ = 1;
return v___x_18_;
}
else
{
uint8_t v___x_19_; 
v___x_19_ = 0;
return v___x_19_;
}
}
else
{
if (lean_obj_tag(v_x_17_) == 0)
{
uint8_t v___x_20_; 
v___x_20_ = 0;
return v___x_20_;
}
else
{
lean_object* v_val_21_; lean_object* v_val_22_; uint8_t v___x_23_; 
v_val_21_ = lean_ctor_get(v_x_16_, 0);
v_val_22_ = lean_ctor_get(v_x_17_, 0);
v___x_23_ = lean_nat_dec_eq(v_val_21_, v_val_22_);
return v___x_23_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0___boxed(lean_object* v_x_24_, lean_object* v_x_25_){
_start:
{
uint8_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_x_24_, v_x_25_);
lean_dec(v_x_25_);
lean_dec(v_x_24_);
v_r_27_ = lean_box(v_res_26_);
return v_r_27_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_instBEqConfig_beq(lean_object* v_x_28_, lean_object* v_x_29_){
_start:
{
uint8_t v_trace_30_; uint8_t v_markInstances_31_; uint8_t v_lax_32_; uint8_t v_suggestions_33_; uint8_t v_locals_34_; lean_object* v_splits_35_; lean_object* v_ematch_36_; lean_object* v_gen_37_; lean_object* v_instances_38_; uint8_t v_matchEqs_39_; uint8_t v_splitMatch_40_; uint8_t v_splitIte_41_; uint8_t v_splitIndPred_42_; uint8_t v_splitImp_43_; lean_object* v_canonHeartbeats_44_; uint8_t v_ext_45_; uint8_t v_extAll_46_; uint8_t v_etaStruct_47_; uint8_t v_funext_48_; uint8_t v_lookahead_49_; uint8_t v_verbose_50_; uint8_t v_clean_51_; uint8_t v_qlia_52_; uint8_t v_mbtc_53_; uint8_t v_zetaDelta_54_; uint8_t v_zeta_55_; uint8_t v_ring_56_; lean_object* v_ringSteps_57_; lean_object* v_ringMaxDegree_58_; uint8_t v_linarith_59_; uint8_t v_lia_60_; uint8_t v_ac_61_; lean_object* v_acSteps_62_; lean_object* v_exp_63_; uint8_t v_abstractProof_64_; uint8_t v_inj_65_; uint8_t v_order_66_; lean_object* v_min_67_; lean_object* v_detailed_68_; uint8_t v_useSorry_69_; uint8_t v_revert_70_; uint8_t v_funCC_71_; uint8_t v_reducible_72_; lean_object* v_maxSuggestions_73_; uint8_t v_trace_74_; uint8_t v_markInstances_75_; uint8_t v_lax_76_; uint8_t v_suggestions_77_; uint8_t v_locals_78_; lean_object* v_splits_79_; lean_object* v_ematch_80_; lean_object* v_gen_81_; lean_object* v_instances_82_; uint8_t v_matchEqs_83_; uint8_t v_splitMatch_84_; uint8_t v_splitIte_85_; uint8_t v_splitIndPred_86_; uint8_t v_splitImp_87_; lean_object* v_canonHeartbeats_88_; uint8_t v_ext_89_; uint8_t v_extAll_90_; uint8_t v_etaStruct_91_; uint8_t v_funext_92_; uint8_t v_lookahead_93_; uint8_t v_verbose_94_; uint8_t v_clean_95_; uint8_t v_qlia_96_; uint8_t v_mbtc_97_; uint8_t v_zetaDelta_98_; uint8_t v_zeta_99_; uint8_t v_ring_100_; lean_object* v_ringSteps_101_; lean_object* v_ringMaxDegree_102_; uint8_t v_linarith_103_; uint8_t v_lia_104_; uint8_t v_ac_105_; lean_object* v_acSteps_106_; lean_object* v_exp_107_; uint8_t v_abstractProof_108_; uint8_t v_inj_109_; uint8_t v_order_110_; lean_object* v_min_111_; lean_object* v_detailed_112_; uint8_t v_useSorry_113_; uint8_t v_revert_114_; uint8_t v_funCC_115_; uint8_t v_reducible_116_; lean_object* v_maxSuggestions_117_; uint8_t v___y_123_; uint8_t v___y_129_; uint8_t v___y_135_; uint8_t v___y_150_; uint8_t v___y_157_; 
v_trace_30_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12);
v_markInstances_31_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 1);
v_lax_32_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 2);
v_suggestions_33_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 3);
v_locals_34_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 4);
v_splits_35_ = lean_ctor_get(v_x_28_, 0);
v_ematch_36_ = lean_ctor_get(v_x_28_, 1);
v_gen_37_ = lean_ctor_get(v_x_28_, 2);
v_instances_38_ = lean_ctor_get(v_x_28_, 3);
v_matchEqs_39_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 5);
v_splitMatch_40_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 6);
v_splitIte_41_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 7);
v_splitIndPred_42_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 8);
v_splitImp_43_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 9);
v_canonHeartbeats_44_ = lean_ctor_get(v_x_28_, 4);
v_ext_45_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 10);
v_extAll_46_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 11);
v_etaStruct_47_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 12);
v_funext_48_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 13);
v_lookahead_49_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 14);
v_verbose_50_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 15);
v_clean_51_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 16);
v_qlia_52_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 17);
v_mbtc_53_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 18);
v_zetaDelta_54_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 19);
v_zeta_55_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 20);
v_ring_56_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 21);
v_ringSteps_57_ = lean_ctor_get(v_x_28_, 5);
v_ringMaxDegree_58_ = lean_ctor_get(v_x_28_, 6);
v_linarith_59_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 22);
v_lia_60_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 23);
v_ac_61_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 24);
v_acSteps_62_ = lean_ctor_get(v_x_28_, 7);
v_exp_63_ = lean_ctor_get(v_x_28_, 8);
v_abstractProof_64_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 25);
v_inj_65_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 26);
v_order_66_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 27);
v_min_67_ = lean_ctor_get(v_x_28_, 9);
v_detailed_68_ = lean_ctor_get(v_x_28_, 10);
v_useSorry_69_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 28);
v_revert_70_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 29);
v_funCC_71_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 30);
v_reducible_72_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*12 + 31);
v_maxSuggestions_73_ = lean_ctor_get(v_x_28_, 11);
v_trace_74_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12);
v_markInstances_75_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 1);
v_lax_76_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 2);
v_suggestions_77_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 3);
v_locals_78_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 4);
v_splits_79_ = lean_ctor_get(v_x_29_, 0);
v_ematch_80_ = lean_ctor_get(v_x_29_, 1);
v_gen_81_ = lean_ctor_get(v_x_29_, 2);
v_instances_82_ = lean_ctor_get(v_x_29_, 3);
v_matchEqs_83_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 5);
v_splitMatch_84_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 6);
v_splitIte_85_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 7);
v_splitIndPred_86_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 8);
v_splitImp_87_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 9);
v_canonHeartbeats_88_ = lean_ctor_get(v_x_29_, 4);
v_ext_89_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 10);
v_extAll_90_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 11);
v_etaStruct_91_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 12);
v_funext_92_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 13);
v_lookahead_93_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 14);
v_verbose_94_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 15);
v_clean_95_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 16);
v_qlia_96_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 17);
v_mbtc_97_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 18);
v_zetaDelta_98_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 19);
v_zeta_99_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 20);
v_ring_100_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 21);
v_ringSteps_101_ = lean_ctor_get(v_x_29_, 5);
v_ringMaxDegree_102_ = lean_ctor_get(v_x_29_, 6);
v_linarith_103_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 22);
v_lia_104_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 23);
v_ac_105_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 24);
v_acSteps_106_ = lean_ctor_get(v_x_29_, 7);
v_exp_107_ = lean_ctor_get(v_x_29_, 8);
v_abstractProof_108_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 25);
v_inj_109_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 26);
v_order_110_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 27);
v_min_111_ = lean_ctor_get(v_x_29_, 9);
v_detailed_112_ = lean_ctor_get(v_x_29_, 10);
v_useSorry_113_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 28);
v_revert_114_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 29);
v_funCC_115_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 30);
v_reducible_116_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*12 + 31);
v_maxSuggestions_117_ = lean_ctor_get(v_x_29_, 11);
if (v_trace_30_ == 0)
{
if (v_trace_74_ == 0)
{
goto v___jp_166_;
}
else
{
return v_trace_30_;
}
}
else
{
if (v_trace_74_ == 0)
{
return v_trace_74_;
}
else
{
goto v___jp_166_;
}
}
v___jp_118_:
{
if (v_reducible_72_ == 0)
{
if (v_reducible_116_ == 0)
{
uint8_t v___x_119_; 
v___x_119_ = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_maxSuggestions_73_, v_maxSuggestions_117_);
return v___x_119_;
}
else
{
return v_reducible_72_;
}
}
else
{
if (v_reducible_116_ == 0)
{
return v_reducible_116_;
}
else
{
uint8_t v___x_120_; 
v___x_120_ = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_maxSuggestions_73_, v_maxSuggestions_117_);
return v___x_120_;
}
}
}
v___jp_121_:
{
if (v_funCC_71_ == 0)
{
if (v_funCC_115_ == 0)
{
goto v___jp_118_;
}
else
{
return v_funCC_71_;
}
}
else
{
if (v_funCC_115_ == 0)
{
return v_funCC_115_;
}
else
{
goto v___jp_118_;
}
}
}
v___jp_122_:
{
if (v___y_123_ == 0)
{
return v___y_123_;
}
else
{
if (v_revert_70_ == 0)
{
if (v_revert_114_ == 0)
{
goto v___jp_121_;
}
else
{
return v_revert_70_;
}
}
else
{
if (v_revert_114_ == 0)
{
return v_revert_114_;
}
else
{
goto v___jp_121_;
}
}
}
}
v___jp_124_:
{
uint8_t v___x_125_; 
v___x_125_ = lean_nat_dec_eq(v_min_67_, v_min_111_);
if (v___x_125_ == 0)
{
return v___x_125_;
}
else
{
uint8_t v___x_126_; 
v___x_126_ = lean_nat_dec_eq(v_detailed_68_, v_detailed_112_);
if (v___x_126_ == 0)
{
return v___x_126_;
}
else
{
if (v_useSorry_69_ == 0)
{
if (v_useSorry_113_ == 0)
{
v___y_123_ = v___x_126_;
goto v___jp_122_;
}
else
{
return v_useSorry_69_;
}
}
else
{
v___y_123_ = v_useSorry_113_;
goto v___jp_122_;
}
}
}
}
v___jp_127_:
{
if (v_order_66_ == 0)
{
if (v_order_110_ == 0)
{
goto v___jp_124_;
}
else
{
return v_order_66_;
}
}
else
{
if (v_order_110_ == 0)
{
return v_order_110_;
}
else
{
goto v___jp_124_;
}
}
}
v___jp_128_:
{
if (v___y_129_ == 0)
{
return v___y_129_;
}
else
{
if (v_inj_65_ == 0)
{
if (v_inj_109_ == 0)
{
goto v___jp_127_;
}
else
{
return v_inj_65_;
}
}
else
{
if (v_inj_109_ == 0)
{
return v_inj_109_;
}
else
{
goto v___jp_127_;
}
}
}
}
v___jp_130_:
{
uint8_t v___x_131_; 
v___x_131_ = lean_nat_dec_eq(v_acSteps_62_, v_acSteps_106_);
if (v___x_131_ == 0)
{
return v___x_131_;
}
else
{
uint8_t v___x_132_; 
v___x_132_ = lean_nat_dec_eq(v_exp_63_, v_exp_107_);
if (v___x_132_ == 0)
{
return v___x_132_;
}
else
{
if (v_abstractProof_64_ == 0)
{
if (v_abstractProof_108_ == 0)
{
v___y_129_ = v___x_132_;
goto v___jp_128_;
}
else
{
return v_abstractProof_64_;
}
}
else
{
v___y_129_ = v_abstractProof_108_;
goto v___jp_128_;
}
}
}
}
v___jp_133_:
{
if (v_ac_61_ == 0)
{
if (v_ac_105_ == 0)
{
goto v___jp_130_;
}
else
{
return v_ac_61_;
}
}
else
{
if (v_ac_105_ == 0)
{
return v_ac_105_;
}
else
{
goto v___jp_130_;
}
}
}
v___jp_134_:
{
if (v___y_135_ == 0)
{
return v___y_135_;
}
else
{
if (v_lia_60_ == 0)
{
if (v_lia_104_ == 0)
{
goto v___jp_133_;
}
else
{
return v_lia_60_;
}
}
else
{
if (v_lia_104_ == 0)
{
return v_lia_104_;
}
else
{
goto v___jp_133_;
}
}
}
}
v___jp_136_:
{
uint8_t v___x_137_; 
v___x_137_ = lean_nat_dec_eq(v_ringSteps_57_, v_ringSteps_101_);
if (v___x_137_ == 0)
{
return v___x_137_;
}
else
{
uint8_t v___x_138_; 
v___x_138_ = lean_nat_dec_eq(v_ringMaxDegree_58_, v_ringMaxDegree_102_);
if (v___x_138_ == 0)
{
return v___x_138_;
}
else
{
if (v_linarith_59_ == 0)
{
if (v_linarith_103_ == 0)
{
v___y_135_ = v___x_138_;
goto v___jp_134_;
}
else
{
return v_linarith_59_;
}
}
else
{
v___y_135_ = v_linarith_103_;
goto v___jp_134_;
}
}
}
}
v___jp_139_:
{
if (v_ring_56_ == 0)
{
if (v_ring_100_ == 0)
{
goto v___jp_136_;
}
else
{
return v_ring_56_;
}
}
else
{
if (v_ring_100_ == 0)
{
return v_ring_100_;
}
else
{
goto v___jp_136_;
}
}
}
v___jp_140_:
{
if (v_zeta_55_ == 0)
{
if (v_zeta_99_ == 0)
{
goto v___jp_139_;
}
else
{
return v_zeta_55_;
}
}
else
{
if (v_zeta_99_ == 0)
{
return v_zeta_99_;
}
else
{
goto v___jp_139_;
}
}
}
v___jp_141_:
{
if (v_zetaDelta_54_ == 0)
{
if (v_zetaDelta_98_ == 0)
{
goto v___jp_140_;
}
else
{
return v_zetaDelta_54_;
}
}
else
{
if (v_zetaDelta_98_ == 0)
{
return v_zetaDelta_98_;
}
else
{
goto v___jp_140_;
}
}
}
v___jp_142_:
{
if (v_mbtc_53_ == 0)
{
if (v_mbtc_97_ == 0)
{
goto v___jp_141_;
}
else
{
return v_mbtc_53_;
}
}
else
{
if (v_mbtc_97_ == 0)
{
return v_mbtc_97_;
}
else
{
goto v___jp_141_;
}
}
}
v___jp_143_:
{
if (v_qlia_52_ == 0)
{
if (v_qlia_96_ == 0)
{
goto v___jp_142_;
}
else
{
return v_qlia_52_;
}
}
else
{
if (v_qlia_96_ == 0)
{
return v_qlia_96_;
}
else
{
goto v___jp_142_;
}
}
}
v___jp_144_:
{
if (v_clean_51_ == 0)
{
if (v_clean_95_ == 0)
{
goto v___jp_143_;
}
else
{
return v_clean_51_;
}
}
else
{
if (v_clean_95_ == 0)
{
return v_clean_95_;
}
else
{
goto v___jp_143_;
}
}
}
v___jp_145_:
{
if (v_verbose_50_ == 0)
{
if (v_verbose_94_ == 0)
{
goto v___jp_144_;
}
else
{
return v_verbose_50_;
}
}
else
{
if (v_verbose_94_ == 0)
{
return v_verbose_94_;
}
else
{
goto v___jp_144_;
}
}
}
v___jp_146_:
{
if (v_lookahead_49_ == 0)
{
if (v_lookahead_93_ == 0)
{
goto v___jp_145_;
}
else
{
return v_lookahead_49_;
}
}
else
{
if (v_lookahead_93_ == 0)
{
return v_lookahead_93_;
}
else
{
goto v___jp_145_;
}
}
}
v___jp_147_:
{
if (v_funext_48_ == 0)
{
if (v_funext_92_ == 0)
{
goto v___jp_146_;
}
else
{
return v_funext_48_;
}
}
else
{
if (v_funext_92_ == 0)
{
return v_funext_92_;
}
else
{
goto v___jp_146_;
}
}
}
v___jp_148_:
{
if (v_etaStruct_47_ == 0)
{
if (v_etaStruct_91_ == 0)
{
goto v___jp_147_;
}
else
{
return v_etaStruct_47_;
}
}
else
{
if (v_etaStruct_91_ == 0)
{
return v_etaStruct_91_;
}
else
{
goto v___jp_147_;
}
}
}
v___jp_149_:
{
if (v___y_150_ == 0)
{
return v___y_150_;
}
else
{
if (v_extAll_46_ == 0)
{
if (v_extAll_90_ == 0)
{
goto v___jp_148_;
}
else
{
return v_extAll_46_;
}
}
else
{
if (v_extAll_90_ == 0)
{
return v_extAll_90_;
}
else
{
goto v___jp_148_;
}
}
}
}
v___jp_151_:
{
uint8_t v___x_152_; 
v___x_152_ = lean_nat_dec_eq(v_canonHeartbeats_44_, v_canonHeartbeats_88_);
if (v___x_152_ == 0)
{
return v___x_152_;
}
else
{
if (v_ext_45_ == 0)
{
if (v_ext_89_ == 0)
{
v___y_150_ = v___x_152_;
goto v___jp_149_;
}
else
{
return v_ext_45_;
}
}
else
{
v___y_150_ = v_ext_89_;
goto v___jp_149_;
}
}
}
v___jp_153_:
{
if (v_splitImp_43_ == 0)
{
if (v_splitImp_87_ == 0)
{
goto v___jp_151_;
}
else
{
return v_splitImp_43_;
}
}
else
{
if (v_splitImp_87_ == 0)
{
return v_splitImp_87_;
}
else
{
goto v___jp_151_;
}
}
}
v___jp_154_:
{
if (v_splitIndPred_42_ == 0)
{
if (v_splitIndPred_86_ == 0)
{
goto v___jp_153_;
}
else
{
return v_splitIndPred_42_;
}
}
else
{
if (v_splitIndPred_86_ == 0)
{
return v_splitIndPred_86_;
}
else
{
goto v___jp_153_;
}
}
}
v___jp_155_:
{
if (v_splitIte_41_ == 0)
{
if (v_splitIte_85_ == 0)
{
goto v___jp_154_;
}
else
{
return v_splitIte_41_;
}
}
else
{
if (v_splitIte_85_ == 0)
{
return v_splitIte_85_;
}
else
{
goto v___jp_154_;
}
}
}
v___jp_156_:
{
if (v___y_157_ == 0)
{
return v___y_157_;
}
else
{
if (v_splitMatch_40_ == 0)
{
if (v_splitMatch_84_ == 0)
{
goto v___jp_155_;
}
else
{
return v_splitMatch_40_;
}
}
else
{
if (v_splitMatch_84_ == 0)
{
return v_splitMatch_84_;
}
else
{
goto v___jp_155_;
}
}
}
}
v___jp_158_:
{
uint8_t v___x_159_; 
v___x_159_ = lean_nat_dec_eq(v_splits_35_, v_splits_79_);
if (v___x_159_ == 0)
{
return v___x_159_;
}
else
{
uint8_t v___x_160_; 
v___x_160_ = lean_nat_dec_eq(v_ematch_36_, v_ematch_80_);
if (v___x_160_ == 0)
{
return v___x_160_;
}
else
{
uint8_t v___x_161_; 
v___x_161_ = lean_nat_dec_eq(v_gen_37_, v_gen_81_);
if (v___x_161_ == 0)
{
return v___x_161_;
}
else
{
uint8_t v___x_162_; 
v___x_162_ = lean_nat_dec_eq(v_instances_38_, v_instances_82_);
if (v___x_162_ == 0)
{
return v___x_162_;
}
else
{
if (v_matchEqs_39_ == 0)
{
if (v_matchEqs_83_ == 0)
{
v___y_157_ = v___x_162_;
goto v___jp_156_;
}
else
{
return v_matchEqs_39_;
}
}
else
{
v___y_157_ = v_matchEqs_83_;
goto v___jp_156_;
}
}
}
}
}
}
v___jp_163_:
{
if (v_locals_34_ == 0)
{
if (v_locals_78_ == 0)
{
goto v___jp_158_;
}
else
{
return v_locals_34_;
}
}
else
{
if (v_locals_78_ == 0)
{
return v_locals_78_;
}
else
{
goto v___jp_158_;
}
}
}
v___jp_164_:
{
if (v_suggestions_33_ == 0)
{
if (v_suggestions_77_ == 0)
{
goto v___jp_163_;
}
else
{
return v_suggestions_33_;
}
}
else
{
if (v_suggestions_77_ == 0)
{
return v_suggestions_77_;
}
else
{
goto v___jp_163_;
}
}
}
v___jp_165_:
{
if (v_lax_32_ == 0)
{
if (v_lax_76_ == 0)
{
goto v___jp_164_;
}
else
{
return v_lax_32_;
}
}
else
{
if (v_lax_76_ == 0)
{
return v_lax_76_;
}
else
{
goto v___jp_164_;
}
}
}
v___jp_166_:
{
if (v_markInstances_31_ == 0)
{
if (v_markInstances_75_ == 0)
{
goto v___jp_165_;
}
else
{
return v_markInstances_31_;
}
}
else
{
if (v_markInstances_75_ == 0)
{
return v_markInstances_75_;
}
else
{
goto v___jp_165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instBEqConfig_beq___boxed(lean_object* v_x_167_, lean_object* v_x_168_){
_start:
{
uint8_t v_res_169_; lean_object* v_r_170_; 
v_res_169_ = l_Lean_Grind_instBEqConfig_beq(v_x_167_, v_x_168_);
lean_dec_ref(v_x_168_);
lean_dec_ref(v_x_167_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
lean_object* runtime_initialize_Init_Core(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_Config(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Grind_Config(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Core(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Config(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Grind_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Grind_Config(builtin);
}
#ifdef __cplusplus
}
#endif
