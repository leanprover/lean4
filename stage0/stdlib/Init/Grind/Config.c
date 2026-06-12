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
static const lean_ctor_object l_Lean_Grind_instInhabitedConfig_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*13 + 32, .m_other = 13, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1048576) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 1, 0, 1, 1)}};
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
uint8_t v_trace_30_; uint8_t v_markInstances_31_; uint8_t v_lax_32_; uint8_t v_suggestions_33_; uint8_t v_locals_34_; lean_object* v_splits_35_; lean_object* v_ematch_36_; lean_object* v_gen_37_; lean_object* v_genLocal_38_; lean_object* v_instances_39_; uint8_t v_matchEqs_40_; uint8_t v_splitMatch_41_; uint8_t v_splitIte_42_; uint8_t v_splitIndPred_43_; uint8_t v_splitImp_44_; lean_object* v_canonHeartbeats_45_; uint8_t v_ext_46_; uint8_t v_extAll_47_; uint8_t v_etaStruct_48_; uint8_t v_funext_49_; uint8_t v_lookahead_50_; uint8_t v_verbose_51_; uint8_t v_clean_52_; uint8_t v_qlia_53_; uint8_t v_mbtc_54_; uint8_t v_zetaDelta_55_; uint8_t v_zeta_56_; uint8_t v_ring_57_; lean_object* v_ringSteps_58_; lean_object* v_ringMaxDegree_59_; uint8_t v_linarith_60_; uint8_t v_lia_61_; uint8_t v_ac_62_; lean_object* v_acSteps_63_; lean_object* v_exp_64_; uint8_t v_abstractProof_65_; uint8_t v_inj_66_; uint8_t v_order_67_; lean_object* v_min_68_; lean_object* v_detailed_69_; uint8_t v_useSorry_70_; uint8_t v_revert_71_; uint8_t v_funCC_72_; uint8_t v_reducible_73_; lean_object* v_maxSuggestions_74_; uint8_t v_trace_75_; uint8_t v_markInstances_76_; uint8_t v_lax_77_; uint8_t v_suggestions_78_; uint8_t v_locals_79_; lean_object* v_splits_80_; lean_object* v_ematch_81_; lean_object* v_gen_82_; lean_object* v_genLocal_83_; lean_object* v_instances_84_; uint8_t v_matchEqs_85_; uint8_t v_splitMatch_86_; uint8_t v_splitIte_87_; uint8_t v_splitIndPred_88_; uint8_t v_splitImp_89_; lean_object* v_canonHeartbeats_90_; uint8_t v_ext_91_; uint8_t v_extAll_92_; uint8_t v_etaStruct_93_; uint8_t v_funext_94_; uint8_t v_lookahead_95_; uint8_t v_verbose_96_; uint8_t v_clean_97_; uint8_t v_qlia_98_; uint8_t v_mbtc_99_; uint8_t v_zetaDelta_100_; uint8_t v_zeta_101_; uint8_t v_ring_102_; lean_object* v_ringSteps_103_; lean_object* v_ringMaxDegree_104_; uint8_t v_linarith_105_; uint8_t v_lia_106_; uint8_t v_ac_107_; lean_object* v_acSteps_108_; lean_object* v_exp_109_; uint8_t v_abstractProof_110_; uint8_t v_inj_111_; uint8_t v_order_112_; lean_object* v_min_113_; lean_object* v_detailed_114_; uint8_t v_useSorry_115_; uint8_t v_revert_116_; uint8_t v_funCC_117_; uint8_t v_reducible_118_; lean_object* v_maxSuggestions_119_; uint8_t v___y_125_; uint8_t v___y_131_; uint8_t v___y_137_; uint8_t v___y_152_; uint8_t v___y_159_; 
v_trace_30_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13);
v_markInstances_31_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 1);
v_lax_32_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 2);
v_suggestions_33_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 3);
v_locals_34_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 4);
v_splits_35_ = lean_ctor_get(v_x_28_, 0);
v_ematch_36_ = lean_ctor_get(v_x_28_, 1);
v_gen_37_ = lean_ctor_get(v_x_28_, 2);
v_genLocal_38_ = lean_ctor_get(v_x_28_, 3);
v_instances_39_ = lean_ctor_get(v_x_28_, 4);
v_matchEqs_40_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 5);
v_splitMatch_41_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 6);
v_splitIte_42_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 7);
v_splitIndPred_43_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 8);
v_splitImp_44_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 9);
v_canonHeartbeats_45_ = lean_ctor_get(v_x_28_, 5);
v_ext_46_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 10);
v_extAll_47_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 11);
v_etaStruct_48_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 12);
v_funext_49_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 13);
v_lookahead_50_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 14);
v_verbose_51_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 15);
v_clean_52_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 16);
v_qlia_53_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 17);
v_mbtc_54_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 18);
v_zetaDelta_55_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 19);
v_zeta_56_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 20);
v_ring_57_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 21);
v_ringSteps_58_ = lean_ctor_get(v_x_28_, 6);
v_ringMaxDegree_59_ = lean_ctor_get(v_x_28_, 7);
v_linarith_60_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 22);
v_lia_61_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 23);
v_ac_62_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 24);
v_acSteps_63_ = lean_ctor_get(v_x_28_, 8);
v_exp_64_ = lean_ctor_get(v_x_28_, 9);
v_abstractProof_65_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 25);
v_inj_66_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 26);
v_order_67_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 27);
v_min_68_ = lean_ctor_get(v_x_28_, 10);
v_detailed_69_ = lean_ctor_get(v_x_28_, 11);
v_useSorry_70_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 28);
v_revert_71_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 29);
v_funCC_72_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 30);
v_reducible_73_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*13 + 31);
v_maxSuggestions_74_ = lean_ctor_get(v_x_28_, 12);
v_trace_75_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13);
v_markInstances_76_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 1);
v_lax_77_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 2);
v_suggestions_78_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 3);
v_locals_79_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 4);
v_splits_80_ = lean_ctor_get(v_x_29_, 0);
v_ematch_81_ = lean_ctor_get(v_x_29_, 1);
v_gen_82_ = lean_ctor_get(v_x_29_, 2);
v_genLocal_83_ = lean_ctor_get(v_x_29_, 3);
v_instances_84_ = lean_ctor_get(v_x_29_, 4);
v_matchEqs_85_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 5);
v_splitMatch_86_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 6);
v_splitIte_87_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 7);
v_splitIndPred_88_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 8);
v_splitImp_89_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 9);
v_canonHeartbeats_90_ = lean_ctor_get(v_x_29_, 5);
v_ext_91_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 10);
v_extAll_92_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 11);
v_etaStruct_93_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 12);
v_funext_94_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 13);
v_lookahead_95_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 14);
v_verbose_96_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 15);
v_clean_97_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 16);
v_qlia_98_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 17);
v_mbtc_99_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 18);
v_zetaDelta_100_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 19);
v_zeta_101_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 20);
v_ring_102_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 21);
v_ringSteps_103_ = lean_ctor_get(v_x_29_, 6);
v_ringMaxDegree_104_ = lean_ctor_get(v_x_29_, 7);
v_linarith_105_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 22);
v_lia_106_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 23);
v_ac_107_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 24);
v_acSteps_108_ = lean_ctor_get(v_x_29_, 8);
v_exp_109_ = lean_ctor_get(v_x_29_, 9);
v_abstractProof_110_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 25);
v_inj_111_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 26);
v_order_112_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 27);
v_min_113_ = lean_ctor_get(v_x_29_, 10);
v_detailed_114_ = lean_ctor_get(v_x_29_, 11);
v_useSorry_115_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 28);
v_revert_116_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 29);
v_funCC_117_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 30);
v_reducible_118_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*13 + 31);
v_maxSuggestions_119_ = lean_ctor_get(v_x_29_, 12);
if (v_trace_30_ == 0)
{
if (v_trace_75_ == 0)
{
goto v___jp_169_;
}
else
{
return v_trace_30_;
}
}
else
{
if (v_trace_75_ == 0)
{
return v_trace_75_;
}
else
{
goto v___jp_169_;
}
}
v___jp_120_:
{
if (v_reducible_73_ == 0)
{
if (v_reducible_118_ == 0)
{
uint8_t v___x_121_; 
v___x_121_ = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_maxSuggestions_74_, v_maxSuggestions_119_);
return v___x_121_;
}
else
{
return v_reducible_73_;
}
}
else
{
if (v_reducible_118_ == 0)
{
return v_reducible_118_;
}
else
{
uint8_t v___x_122_; 
v___x_122_ = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_maxSuggestions_74_, v_maxSuggestions_119_);
return v___x_122_;
}
}
}
v___jp_123_:
{
if (v_funCC_72_ == 0)
{
if (v_funCC_117_ == 0)
{
goto v___jp_120_;
}
else
{
return v_funCC_72_;
}
}
else
{
if (v_funCC_117_ == 0)
{
return v_funCC_117_;
}
else
{
goto v___jp_120_;
}
}
}
v___jp_124_:
{
if (v___y_125_ == 0)
{
return v___y_125_;
}
else
{
if (v_revert_71_ == 0)
{
if (v_revert_116_ == 0)
{
goto v___jp_123_;
}
else
{
return v_revert_71_;
}
}
else
{
if (v_revert_116_ == 0)
{
return v_revert_116_;
}
else
{
goto v___jp_123_;
}
}
}
}
v___jp_126_:
{
uint8_t v___x_127_; 
v___x_127_ = lean_nat_dec_eq(v_min_68_, v_min_113_);
if (v___x_127_ == 0)
{
return v___x_127_;
}
else
{
uint8_t v___x_128_; 
v___x_128_ = lean_nat_dec_eq(v_detailed_69_, v_detailed_114_);
if (v___x_128_ == 0)
{
return v___x_128_;
}
else
{
if (v_useSorry_70_ == 0)
{
if (v_useSorry_115_ == 0)
{
v___y_125_ = v___x_128_;
goto v___jp_124_;
}
else
{
return v_useSorry_70_;
}
}
else
{
v___y_125_ = v_useSorry_115_;
goto v___jp_124_;
}
}
}
}
v___jp_129_:
{
if (v_order_67_ == 0)
{
if (v_order_112_ == 0)
{
goto v___jp_126_;
}
else
{
return v_order_67_;
}
}
else
{
if (v_order_112_ == 0)
{
return v_order_112_;
}
else
{
goto v___jp_126_;
}
}
}
v___jp_130_:
{
if (v___y_131_ == 0)
{
return v___y_131_;
}
else
{
if (v_inj_66_ == 0)
{
if (v_inj_111_ == 0)
{
goto v___jp_129_;
}
else
{
return v_inj_66_;
}
}
else
{
if (v_inj_111_ == 0)
{
return v_inj_111_;
}
else
{
goto v___jp_129_;
}
}
}
}
v___jp_132_:
{
uint8_t v___x_133_; 
v___x_133_ = lean_nat_dec_eq(v_acSteps_63_, v_acSteps_108_);
if (v___x_133_ == 0)
{
return v___x_133_;
}
else
{
uint8_t v___x_134_; 
v___x_134_ = lean_nat_dec_eq(v_exp_64_, v_exp_109_);
if (v___x_134_ == 0)
{
return v___x_134_;
}
else
{
if (v_abstractProof_65_ == 0)
{
if (v_abstractProof_110_ == 0)
{
v___y_131_ = v___x_134_;
goto v___jp_130_;
}
else
{
return v_abstractProof_65_;
}
}
else
{
v___y_131_ = v_abstractProof_110_;
goto v___jp_130_;
}
}
}
}
v___jp_135_:
{
if (v_ac_62_ == 0)
{
if (v_ac_107_ == 0)
{
goto v___jp_132_;
}
else
{
return v_ac_62_;
}
}
else
{
if (v_ac_107_ == 0)
{
return v_ac_107_;
}
else
{
goto v___jp_132_;
}
}
}
v___jp_136_:
{
if (v___y_137_ == 0)
{
return v___y_137_;
}
else
{
if (v_lia_61_ == 0)
{
if (v_lia_106_ == 0)
{
goto v___jp_135_;
}
else
{
return v_lia_61_;
}
}
else
{
if (v_lia_106_ == 0)
{
return v_lia_106_;
}
else
{
goto v___jp_135_;
}
}
}
}
v___jp_138_:
{
uint8_t v___x_139_; 
v___x_139_ = lean_nat_dec_eq(v_ringSteps_58_, v_ringSteps_103_);
if (v___x_139_ == 0)
{
return v___x_139_;
}
else
{
uint8_t v___x_140_; 
v___x_140_ = lean_nat_dec_eq(v_ringMaxDegree_59_, v_ringMaxDegree_104_);
if (v___x_140_ == 0)
{
return v___x_140_;
}
else
{
if (v_linarith_60_ == 0)
{
if (v_linarith_105_ == 0)
{
v___y_137_ = v___x_140_;
goto v___jp_136_;
}
else
{
return v_linarith_60_;
}
}
else
{
v___y_137_ = v_linarith_105_;
goto v___jp_136_;
}
}
}
}
v___jp_141_:
{
if (v_ring_57_ == 0)
{
if (v_ring_102_ == 0)
{
goto v___jp_138_;
}
else
{
return v_ring_57_;
}
}
else
{
if (v_ring_102_ == 0)
{
return v_ring_102_;
}
else
{
goto v___jp_138_;
}
}
}
v___jp_142_:
{
if (v_zeta_56_ == 0)
{
if (v_zeta_101_ == 0)
{
goto v___jp_141_;
}
else
{
return v_zeta_56_;
}
}
else
{
if (v_zeta_101_ == 0)
{
return v_zeta_101_;
}
else
{
goto v___jp_141_;
}
}
}
v___jp_143_:
{
if (v_zetaDelta_55_ == 0)
{
if (v_zetaDelta_100_ == 0)
{
goto v___jp_142_;
}
else
{
return v_zetaDelta_55_;
}
}
else
{
if (v_zetaDelta_100_ == 0)
{
return v_zetaDelta_100_;
}
else
{
goto v___jp_142_;
}
}
}
v___jp_144_:
{
if (v_mbtc_54_ == 0)
{
if (v_mbtc_99_ == 0)
{
goto v___jp_143_;
}
else
{
return v_mbtc_54_;
}
}
else
{
if (v_mbtc_99_ == 0)
{
return v_mbtc_99_;
}
else
{
goto v___jp_143_;
}
}
}
v___jp_145_:
{
if (v_qlia_53_ == 0)
{
if (v_qlia_98_ == 0)
{
goto v___jp_144_;
}
else
{
return v_qlia_53_;
}
}
else
{
if (v_qlia_98_ == 0)
{
return v_qlia_98_;
}
else
{
goto v___jp_144_;
}
}
}
v___jp_146_:
{
if (v_clean_52_ == 0)
{
if (v_clean_97_ == 0)
{
goto v___jp_145_;
}
else
{
return v_clean_52_;
}
}
else
{
if (v_clean_97_ == 0)
{
return v_clean_97_;
}
else
{
goto v___jp_145_;
}
}
}
v___jp_147_:
{
if (v_verbose_51_ == 0)
{
if (v_verbose_96_ == 0)
{
goto v___jp_146_;
}
else
{
return v_verbose_51_;
}
}
else
{
if (v_verbose_96_ == 0)
{
return v_verbose_96_;
}
else
{
goto v___jp_146_;
}
}
}
v___jp_148_:
{
if (v_lookahead_50_ == 0)
{
if (v_lookahead_95_ == 0)
{
goto v___jp_147_;
}
else
{
return v_lookahead_50_;
}
}
else
{
if (v_lookahead_95_ == 0)
{
return v_lookahead_95_;
}
else
{
goto v___jp_147_;
}
}
}
v___jp_149_:
{
if (v_funext_49_ == 0)
{
if (v_funext_94_ == 0)
{
goto v___jp_148_;
}
else
{
return v_funext_49_;
}
}
else
{
if (v_funext_94_ == 0)
{
return v_funext_94_;
}
else
{
goto v___jp_148_;
}
}
}
v___jp_150_:
{
if (v_etaStruct_48_ == 0)
{
if (v_etaStruct_93_ == 0)
{
goto v___jp_149_;
}
else
{
return v_etaStruct_48_;
}
}
else
{
if (v_etaStruct_93_ == 0)
{
return v_etaStruct_93_;
}
else
{
goto v___jp_149_;
}
}
}
v___jp_151_:
{
if (v___y_152_ == 0)
{
return v___y_152_;
}
else
{
if (v_extAll_47_ == 0)
{
if (v_extAll_92_ == 0)
{
goto v___jp_150_;
}
else
{
return v_extAll_47_;
}
}
else
{
if (v_extAll_92_ == 0)
{
return v_extAll_92_;
}
else
{
goto v___jp_150_;
}
}
}
}
v___jp_153_:
{
uint8_t v___x_154_; 
v___x_154_ = lean_nat_dec_eq(v_canonHeartbeats_45_, v_canonHeartbeats_90_);
if (v___x_154_ == 0)
{
return v___x_154_;
}
else
{
if (v_ext_46_ == 0)
{
if (v_ext_91_ == 0)
{
v___y_152_ = v___x_154_;
goto v___jp_151_;
}
else
{
return v_ext_46_;
}
}
else
{
v___y_152_ = v_ext_91_;
goto v___jp_151_;
}
}
}
v___jp_155_:
{
if (v_splitImp_44_ == 0)
{
if (v_splitImp_89_ == 0)
{
goto v___jp_153_;
}
else
{
return v_splitImp_44_;
}
}
else
{
if (v_splitImp_89_ == 0)
{
return v_splitImp_89_;
}
else
{
goto v___jp_153_;
}
}
}
v___jp_156_:
{
if (v_splitIndPred_43_ == 0)
{
if (v_splitIndPred_88_ == 0)
{
goto v___jp_155_;
}
else
{
return v_splitIndPred_43_;
}
}
else
{
if (v_splitIndPred_88_ == 0)
{
return v_splitIndPred_88_;
}
else
{
goto v___jp_155_;
}
}
}
v___jp_157_:
{
if (v_splitIte_42_ == 0)
{
if (v_splitIte_87_ == 0)
{
goto v___jp_156_;
}
else
{
return v_splitIte_42_;
}
}
else
{
if (v_splitIte_87_ == 0)
{
return v_splitIte_87_;
}
else
{
goto v___jp_156_;
}
}
}
v___jp_158_:
{
if (v___y_159_ == 0)
{
return v___y_159_;
}
else
{
if (v_splitMatch_41_ == 0)
{
if (v_splitMatch_86_ == 0)
{
goto v___jp_157_;
}
else
{
return v_splitMatch_41_;
}
}
else
{
if (v_splitMatch_86_ == 0)
{
return v_splitMatch_86_;
}
else
{
goto v___jp_157_;
}
}
}
}
v___jp_160_:
{
uint8_t v___x_161_; 
v___x_161_ = lean_nat_dec_eq(v_splits_35_, v_splits_80_);
if (v___x_161_ == 0)
{
return v___x_161_;
}
else
{
uint8_t v___x_162_; 
v___x_162_ = lean_nat_dec_eq(v_ematch_36_, v_ematch_81_);
if (v___x_162_ == 0)
{
return v___x_162_;
}
else
{
uint8_t v___x_163_; 
v___x_163_ = lean_nat_dec_eq(v_gen_37_, v_gen_82_);
if (v___x_163_ == 0)
{
return v___x_163_;
}
else
{
uint8_t v___x_164_; 
v___x_164_ = lean_nat_dec_eq(v_genLocal_38_, v_genLocal_83_);
if (v___x_164_ == 0)
{
return v___x_164_;
}
else
{
uint8_t v___x_165_; 
v___x_165_ = lean_nat_dec_eq(v_instances_39_, v_instances_84_);
if (v___x_165_ == 0)
{
return v___x_165_;
}
else
{
if (v_matchEqs_40_ == 0)
{
if (v_matchEqs_85_ == 0)
{
v___y_159_ = v___x_165_;
goto v___jp_158_;
}
else
{
return v_matchEqs_40_;
}
}
else
{
v___y_159_ = v_matchEqs_85_;
goto v___jp_158_;
}
}
}
}
}
}
}
v___jp_166_:
{
if (v_locals_34_ == 0)
{
if (v_locals_79_ == 0)
{
goto v___jp_160_;
}
else
{
return v_locals_34_;
}
}
else
{
if (v_locals_79_ == 0)
{
return v_locals_79_;
}
else
{
goto v___jp_160_;
}
}
}
v___jp_167_:
{
if (v_suggestions_33_ == 0)
{
if (v_suggestions_78_ == 0)
{
goto v___jp_166_;
}
else
{
return v_suggestions_33_;
}
}
else
{
if (v_suggestions_78_ == 0)
{
return v_suggestions_78_;
}
else
{
goto v___jp_166_;
}
}
}
v___jp_168_:
{
if (v_lax_32_ == 0)
{
if (v_lax_77_ == 0)
{
goto v___jp_167_;
}
else
{
return v_lax_32_;
}
}
else
{
if (v_lax_77_ == 0)
{
return v_lax_77_;
}
else
{
goto v___jp_167_;
}
}
}
v___jp_169_:
{
if (v_markInstances_31_ == 0)
{
if (v_markInstances_76_ == 0)
{
goto v___jp_168_;
}
else
{
return v_markInstances_31_;
}
}
else
{
if (v_markInstances_76_ == 0)
{
return v_markInstances_76_;
}
else
{
goto v___jp_168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instBEqConfig_beq___boxed(lean_object* v_x_170_, lean_object* v_x_171_){
_start:
{
uint8_t v_res_172_; lean_object* v_r_173_; 
v_res_172_ = l_Lean_Grind_instBEqConfig_beq(v_x_170_, v_x_171_);
lean_dec_ref(v_x_171_);
lean_dec_ref(v_x_170_);
v_r_173_ = lean_box(v_res_172_);
return v_r_173_;
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
