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
static const lean_ctor_object l_Lean_Grind_instInhabitedConfig_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*11 + 32, .m_other = 11, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1048576) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 1, 0, 1, 1)}};
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(lean_object* v_x_15_, lean_object* v_x_16_){
_start:
{
if (lean_obj_tag(v_x_15_) == 0)
{
if (lean_obj_tag(v_x_16_) == 0)
{
uint8_t v___x_17_; 
v___x_17_ = 1;
return v___x_17_;
}
else
{
uint8_t v___x_18_; 
v___x_18_ = 0;
return v___x_18_;
}
}
else
{
if (lean_obj_tag(v_x_16_) == 0)
{
uint8_t v___x_19_; 
v___x_19_ = 0;
return v___x_19_;
}
else
{
lean_object* v_val_20_; lean_object* v_val_21_; uint8_t v___x_22_; 
v_val_20_ = lean_ctor_get(v_x_15_, 0);
v_val_21_ = lean_ctor_get(v_x_16_, 0);
v___x_22_ = lean_nat_dec_eq(v_val_20_, v_val_21_);
return v___x_22_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0___boxed(lean_object* v_x_23_, lean_object* v_x_24_){
_start:
{
uint8_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_x_23_, v_x_24_);
lean_dec(v_x_24_);
lean_dec(v_x_23_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_instBEqConfig_beq(lean_object* v_x_27_, lean_object* v_x_28_){
_start:
{
uint8_t v_trace_29_; uint8_t v_markInstances_30_; uint8_t v_lax_31_; uint8_t v_suggestions_32_; uint8_t v_locals_33_; lean_object* v_splits_34_; lean_object* v_ematch_35_; lean_object* v_gen_36_; lean_object* v_instances_37_; uint8_t v_matchEqs_38_; uint8_t v_splitMatch_39_; uint8_t v_splitIte_40_; uint8_t v_splitIndPred_41_; uint8_t v_splitImp_42_; lean_object* v_canonHeartbeats_43_; uint8_t v_ext_44_; uint8_t v_extAll_45_; uint8_t v_etaStruct_46_; uint8_t v_funext_47_; uint8_t v_lookahead_48_; uint8_t v_verbose_49_; uint8_t v_clean_50_; uint8_t v_qlia_51_; uint8_t v_mbtc_52_; uint8_t v_zetaDelta_53_; uint8_t v_zeta_54_; uint8_t v_ring_55_; lean_object* v_ringSteps_56_; uint8_t v_linarith_57_; uint8_t v_lia_58_; uint8_t v_ac_59_; lean_object* v_acSteps_60_; lean_object* v_exp_61_; uint8_t v_abstractProof_62_; uint8_t v_inj_63_; uint8_t v_order_64_; lean_object* v_min_65_; lean_object* v_detailed_66_; uint8_t v_useSorry_67_; uint8_t v_revert_68_; uint8_t v_funCC_69_; uint8_t v_reducible_70_; lean_object* v_maxSuggestions_71_; uint8_t v_trace_72_; uint8_t v_markInstances_73_; uint8_t v_lax_74_; uint8_t v_suggestions_75_; uint8_t v_locals_76_; lean_object* v_splits_77_; lean_object* v_ematch_78_; lean_object* v_gen_79_; lean_object* v_instances_80_; uint8_t v_matchEqs_81_; uint8_t v_splitMatch_82_; uint8_t v_splitIte_83_; uint8_t v_splitIndPred_84_; uint8_t v_splitImp_85_; lean_object* v_canonHeartbeats_86_; uint8_t v_ext_87_; uint8_t v_extAll_88_; uint8_t v_etaStruct_89_; uint8_t v_funext_90_; uint8_t v_lookahead_91_; uint8_t v_verbose_92_; uint8_t v_clean_93_; uint8_t v_qlia_94_; uint8_t v_mbtc_95_; uint8_t v_zetaDelta_96_; uint8_t v_zeta_97_; uint8_t v_ring_98_; lean_object* v_ringSteps_99_; uint8_t v_linarith_100_; uint8_t v_lia_101_; uint8_t v_ac_102_; lean_object* v_acSteps_103_; lean_object* v_exp_104_; uint8_t v_abstractProof_105_; uint8_t v_inj_106_; uint8_t v_order_107_; lean_object* v_min_108_; lean_object* v_detailed_109_; uint8_t v_useSorry_110_; uint8_t v_revert_111_; uint8_t v_funCC_112_; uint8_t v_reducible_113_; lean_object* v_maxSuggestions_114_; uint8_t v___y_120_; uint8_t v___y_126_; uint8_t v___y_132_; uint8_t v___y_146_; uint8_t v___y_153_; 
v_trace_29_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11);
v_markInstances_30_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 1);
v_lax_31_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 2);
v_suggestions_32_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 3);
v_locals_33_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 4);
v_splits_34_ = lean_ctor_get(v_x_27_, 0);
v_ematch_35_ = lean_ctor_get(v_x_27_, 1);
v_gen_36_ = lean_ctor_get(v_x_27_, 2);
v_instances_37_ = lean_ctor_get(v_x_27_, 3);
v_matchEqs_38_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 5);
v_splitMatch_39_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 6);
v_splitIte_40_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 7);
v_splitIndPred_41_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 8);
v_splitImp_42_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 9);
v_canonHeartbeats_43_ = lean_ctor_get(v_x_27_, 4);
v_ext_44_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 10);
v_extAll_45_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 11);
v_etaStruct_46_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 12);
v_funext_47_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 13);
v_lookahead_48_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 14);
v_verbose_49_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 15);
v_clean_50_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 16);
v_qlia_51_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 17);
v_mbtc_52_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 18);
v_zetaDelta_53_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 19);
v_zeta_54_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 20);
v_ring_55_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 21);
v_ringSteps_56_ = lean_ctor_get(v_x_27_, 5);
v_linarith_57_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 22);
v_lia_58_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 23);
v_ac_59_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 24);
v_acSteps_60_ = lean_ctor_get(v_x_27_, 6);
v_exp_61_ = lean_ctor_get(v_x_27_, 7);
v_abstractProof_62_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 25);
v_inj_63_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 26);
v_order_64_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 27);
v_min_65_ = lean_ctor_get(v_x_27_, 8);
v_detailed_66_ = lean_ctor_get(v_x_27_, 9);
v_useSorry_67_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 28);
v_revert_68_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 29);
v_funCC_69_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 30);
v_reducible_70_ = lean_ctor_get_uint8(v_x_27_, sizeof(void*)*11 + 31);
v_maxSuggestions_71_ = lean_ctor_get(v_x_27_, 10);
v_trace_72_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11);
v_markInstances_73_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 1);
v_lax_74_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 2);
v_suggestions_75_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 3);
v_locals_76_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 4);
v_splits_77_ = lean_ctor_get(v_x_28_, 0);
v_ematch_78_ = lean_ctor_get(v_x_28_, 1);
v_gen_79_ = lean_ctor_get(v_x_28_, 2);
v_instances_80_ = lean_ctor_get(v_x_28_, 3);
v_matchEqs_81_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 5);
v_splitMatch_82_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 6);
v_splitIte_83_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 7);
v_splitIndPred_84_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 8);
v_splitImp_85_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 9);
v_canonHeartbeats_86_ = lean_ctor_get(v_x_28_, 4);
v_ext_87_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 10);
v_extAll_88_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 11);
v_etaStruct_89_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 12);
v_funext_90_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 13);
v_lookahead_91_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 14);
v_verbose_92_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 15);
v_clean_93_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 16);
v_qlia_94_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 17);
v_mbtc_95_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 18);
v_zetaDelta_96_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 19);
v_zeta_97_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 20);
v_ring_98_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 21);
v_ringSteps_99_ = lean_ctor_get(v_x_28_, 5);
v_linarith_100_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 22);
v_lia_101_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 23);
v_ac_102_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 24);
v_acSteps_103_ = lean_ctor_get(v_x_28_, 6);
v_exp_104_ = lean_ctor_get(v_x_28_, 7);
v_abstractProof_105_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 25);
v_inj_106_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 26);
v_order_107_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 27);
v_min_108_ = lean_ctor_get(v_x_28_, 8);
v_detailed_109_ = lean_ctor_get(v_x_28_, 9);
v_useSorry_110_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 28);
v_revert_111_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 29);
v_funCC_112_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 30);
v_reducible_113_ = lean_ctor_get_uint8(v_x_28_, sizeof(void*)*11 + 31);
v_maxSuggestions_114_ = lean_ctor_get(v_x_28_, 10);
if (v_trace_29_ == 0)
{
if (v_trace_72_ == 0)
{
goto v___jp_162_;
}
else
{
return v_trace_29_;
}
}
else
{
if (v_trace_72_ == 0)
{
return v_trace_72_;
}
else
{
goto v___jp_162_;
}
}
v___jp_115_:
{
if (v_reducible_70_ == 0)
{
if (v_reducible_113_ == 0)
{
uint8_t v___x_116_; 
v___x_116_ = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_maxSuggestions_71_, v_maxSuggestions_114_);
return v___x_116_;
}
else
{
return v_reducible_70_;
}
}
else
{
if (v_reducible_113_ == 0)
{
return v_reducible_113_;
}
else
{
uint8_t v___x_117_; 
v___x_117_ = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_maxSuggestions_71_, v_maxSuggestions_114_);
return v___x_117_;
}
}
}
v___jp_118_:
{
if (v_funCC_69_ == 0)
{
if (v_funCC_112_ == 0)
{
goto v___jp_115_;
}
else
{
return v_funCC_69_;
}
}
else
{
if (v_funCC_112_ == 0)
{
return v_funCC_112_;
}
else
{
goto v___jp_115_;
}
}
}
v___jp_119_:
{
if (v___y_120_ == 0)
{
return v___y_120_;
}
else
{
if (v_revert_68_ == 0)
{
if (v_revert_111_ == 0)
{
goto v___jp_118_;
}
else
{
return v_revert_68_;
}
}
else
{
if (v_revert_111_ == 0)
{
return v_revert_111_;
}
else
{
goto v___jp_118_;
}
}
}
}
v___jp_121_:
{
uint8_t v___x_122_; 
v___x_122_ = lean_nat_dec_eq(v_min_65_, v_min_108_);
if (v___x_122_ == 0)
{
return v___x_122_;
}
else
{
uint8_t v___x_123_; 
v___x_123_ = lean_nat_dec_eq(v_detailed_66_, v_detailed_109_);
if (v___x_123_ == 0)
{
return v___x_123_;
}
else
{
if (v_useSorry_67_ == 0)
{
if (v_useSorry_110_ == 0)
{
v___y_120_ = v___x_123_;
goto v___jp_119_;
}
else
{
return v_useSorry_67_;
}
}
else
{
v___y_120_ = v_useSorry_110_;
goto v___jp_119_;
}
}
}
}
v___jp_124_:
{
if (v_order_64_ == 0)
{
if (v_order_107_ == 0)
{
goto v___jp_121_;
}
else
{
return v_order_64_;
}
}
else
{
if (v_order_107_ == 0)
{
return v_order_107_;
}
else
{
goto v___jp_121_;
}
}
}
v___jp_125_:
{
if (v___y_126_ == 0)
{
return v___y_126_;
}
else
{
if (v_inj_63_ == 0)
{
if (v_inj_106_ == 0)
{
goto v___jp_124_;
}
else
{
return v_inj_63_;
}
}
else
{
if (v_inj_106_ == 0)
{
return v_inj_106_;
}
else
{
goto v___jp_124_;
}
}
}
}
v___jp_127_:
{
uint8_t v___x_128_; 
v___x_128_ = lean_nat_dec_eq(v_acSteps_60_, v_acSteps_103_);
if (v___x_128_ == 0)
{
return v___x_128_;
}
else
{
uint8_t v___x_129_; 
v___x_129_ = lean_nat_dec_eq(v_exp_61_, v_exp_104_);
if (v___x_129_ == 0)
{
return v___x_129_;
}
else
{
if (v_abstractProof_62_ == 0)
{
if (v_abstractProof_105_ == 0)
{
v___y_126_ = v___x_129_;
goto v___jp_125_;
}
else
{
return v_abstractProof_62_;
}
}
else
{
v___y_126_ = v_abstractProof_105_;
goto v___jp_125_;
}
}
}
}
v___jp_130_:
{
if (v_ac_59_ == 0)
{
if (v_ac_102_ == 0)
{
goto v___jp_127_;
}
else
{
return v_ac_59_;
}
}
else
{
if (v_ac_102_ == 0)
{
return v_ac_102_;
}
else
{
goto v___jp_127_;
}
}
}
v___jp_131_:
{
if (v___y_132_ == 0)
{
return v___y_132_;
}
else
{
if (v_lia_58_ == 0)
{
if (v_lia_101_ == 0)
{
goto v___jp_130_;
}
else
{
return v_lia_58_;
}
}
else
{
if (v_lia_101_ == 0)
{
return v_lia_101_;
}
else
{
goto v___jp_130_;
}
}
}
}
v___jp_133_:
{
uint8_t v___x_134_; 
v___x_134_ = lean_nat_dec_eq(v_ringSteps_56_, v_ringSteps_99_);
if (v___x_134_ == 0)
{
return v___x_134_;
}
else
{
if (v_linarith_57_ == 0)
{
if (v_linarith_100_ == 0)
{
v___y_132_ = v___x_134_;
goto v___jp_131_;
}
else
{
return v_linarith_57_;
}
}
else
{
v___y_132_ = v_linarith_100_;
goto v___jp_131_;
}
}
}
v___jp_135_:
{
if (v_ring_55_ == 0)
{
if (v_ring_98_ == 0)
{
goto v___jp_133_;
}
else
{
return v_ring_55_;
}
}
else
{
if (v_ring_98_ == 0)
{
return v_ring_98_;
}
else
{
goto v___jp_133_;
}
}
}
v___jp_136_:
{
if (v_zeta_54_ == 0)
{
if (v_zeta_97_ == 0)
{
goto v___jp_135_;
}
else
{
return v_zeta_54_;
}
}
else
{
if (v_zeta_97_ == 0)
{
return v_zeta_97_;
}
else
{
goto v___jp_135_;
}
}
}
v___jp_137_:
{
if (v_zetaDelta_53_ == 0)
{
if (v_zetaDelta_96_ == 0)
{
goto v___jp_136_;
}
else
{
return v_zetaDelta_53_;
}
}
else
{
if (v_zetaDelta_96_ == 0)
{
return v_zetaDelta_96_;
}
else
{
goto v___jp_136_;
}
}
}
v___jp_138_:
{
if (v_mbtc_52_ == 0)
{
if (v_mbtc_95_ == 0)
{
goto v___jp_137_;
}
else
{
return v_mbtc_52_;
}
}
else
{
if (v_mbtc_95_ == 0)
{
return v_mbtc_95_;
}
else
{
goto v___jp_137_;
}
}
}
v___jp_139_:
{
if (v_qlia_51_ == 0)
{
if (v_qlia_94_ == 0)
{
goto v___jp_138_;
}
else
{
return v_qlia_51_;
}
}
else
{
if (v_qlia_94_ == 0)
{
return v_qlia_94_;
}
else
{
goto v___jp_138_;
}
}
}
v___jp_140_:
{
if (v_clean_50_ == 0)
{
if (v_clean_93_ == 0)
{
goto v___jp_139_;
}
else
{
return v_clean_50_;
}
}
else
{
if (v_clean_93_ == 0)
{
return v_clean_93_;
}
else
{
goto v___jp_139_;
}
}
}
v___jp_141_:
{
if (v_verbose_49_ == 0)
{
if (v_verbose_92_ == 0)
{
goto v___jp_140_;
}
else
{
return v_verbose_49_;
}
}
else
{
if (v_verbose_92_ == 0)
{
return v_verbose_92_;
}
else
{
goto v___jp_140_;
}
}
}
v___jp_142_:
{
if (v_lookahead_48_ == 0)
{
if (v_lookahead_91_ == 0)
{
goto v___jp_141_;
}
else
{
return v_lookahead_48_;
}
}
else
{
if (v_lookahead_91_ == 0)
{
return v_lookahead_91_;
}
else
{
goto v___jp_141_;
}
}
}
v___jp_143_:
{
if (v_funext_47_ == 0)
{
if (v_funext_90_ == 0)
{
goto v___jp_142_;
}
else
{
return v_funext_47_;
}
}
else
{
if (v_funext_90_ == 0)
{
return v_funext_90_;
}
else
{
goto v___jp_142_;
}
}
}
v___jp_144_:
{
if (v_etaStruct_46_ == 0)
{
if (v_etaStruct_89_ == 0)
{
goto v___jp_143_;
}
else
{
return v_etaStruct_46_;
}
}
else
{
if (v_etaStruct_89_ == 0)
{
return v_etaStruct_89_;
}
else
{
goto v___jp_143_;
}
}
}
v___jp_145_:
{
if (v___y_146_ == 0)
{
return v___y_146_;
}
else
{
if (v_extAll_45_ == 0)
{
if (v_extAll_88_ == 0)
{
goto v___jp_144_;
}
else
{
return v_extAll_45_;
}
}
else
{
if (v_extAll_88_ == 0)
{
return v_extAll_88_;
}
else
{
goto v___jp_144_;
}
}
}
}
v___jp_147_:
{
uint8_t v___x_148_; 
v___x_148_ = lean_nat_dec_eq(v_canonHeartbeats_43_, v_canonHeartbeats_86_);
if (v___x_148_ == 0)
{
return v___x_148_;
}
else
{
if (v_ext_44_ == 0)
{
if (v_ext_87_ == 0)
{
v___y_146_ = v___x_148_;
goto v___jp_145_;
}
else
{
return v_ext_44_;
}
}
else
{
v___y_146_ = v_ext_87_;
goto v___jp_145_;
}
}
}
v___jp_149_:
{
if (v_splitImp_42_ == 0)
{
if (v_splitImp_85_ == 0)
{
goto v___jp_147_;
}
else
{
return v_splitImp_42_;
}
}
else
{
if (v_splitImp_85_ == 0)
{
return v_splitImp_85_;
}
else
{
goto v___jp_147_;
}
}
}
v___jp_150_:
{
if (v_splitIndPred_41_ == 0)
{
if (v_splitIndPred_84_ == 0)
{
goto v___jp_149_;
}
else
{
return v_splitIndPred_41_;
}
}
else
{
if (v_splitIndPred_84_ == 0)
{
return v_splitIndPred_84_;
}
else
{
goto v___jp_149_;
}
}
}
v___jp_151_:
{
if (v_splitIte_40_ == 0)
{
if (v_splitIte_83_ == 0)
{
goto v___jp_150_;
}
else
{
return v_splitIte_40_;
}
}
else
{
if (v_splitIte_83_ == 0)
{
return v_splitIte_83_;
}
else
{
goto v___jp_150_;
}
}
}
v___jp_152_:
{
if (v___y_153_ == 0)
{
return v___y_153_;
}
else
{
if (v_splitMatch_39_ == 0)
{
if (v_splitMatch_82_ == 0)
{
goto v___jp_151_;
}
else
{
return v_splitMatch_39_;
}
}
else
{
if (v_splitMatch_82_ == 0)
{
return v_splitMatch_82_;
}
else
{
goto v___jp_151_;
}
}
}
}
v___jp_154_:
{
uint8_t v___x_155_; 
v___x_155_ = lean_nat_dec_eq(v_splits_34_, v_splits_77_);
if (v___x_155_ == 0)
{
return v___x_155_;
}
else
{
uint8_t v___x_156_; 
v___x_156_ = lean_nat_dec_eq(v_ematch_35_, v_ematch_78_);
if (v___x_156_ == 0)
{
return v___x_156_;
}
else
{
uint8_t v___x_157_; 
v___x_157_ = lean_nat_dec_eq(v_gen_36_, v_gen_79_);
if (v___x_157_ == 0)
{
return v___x_157_;
}
else
{
uint8_t v___x_158_; 
v___x_158_ = lean_nat_dec_eq(v_instances_37_, v_instances_80_);
if (v___x_158_ == 0)
{
return v___x_158_;
}
else
{
if (v_matchEqs_38_ == 0)
{
if (v_matchEqs_81_ == 0)
{
v___y_153_ = v___x_158_;
goto v___jp_152_;
}
else
{
return v_matchEqs_38_;
}
}
else
{
v___y_153_ = v_matchEqs_81_;
goto v___jp_152_;
}
}
}
}
}
}
v___jp_159_:
{
if (v_locals_33_ == 0)
{
if (v_locals_76_ == 0)
{
goto v___jp_154_;
}
else
{
return v_locals_33_;
}
}
else
{
if (v_locals_76_ == 0)
{
return v_locals_76_;
}
else
{
goto v___jp_154_;
}
}
}
v___jp_160_:
{
if (v_suggestions_32_ == 0)
{
if (v_suggestions_75_ == 0)
{
goto v___jp_159_;
}
else
{
return v_suggestions_32_;
}
}
else
{
if (v_suggestions_75_ == 0)
{
return v_suggestions_75_;
}
else
{
goto v___jp_159_;
}
}
}
v___jp_161_:
{
if (v_lax_31_ == 0)
{
if (v_lax_74_ == 0)
{
goto v___jp_160_;
}
else
{
return v_lax_31_;
}
}
else
{
if (v_lax_74_ == 0)
{
return v_lax_74_;
}
else
{
goto v___jp_160_;
}
}
}
v___jp_162_:
{
if (v_markInstances_30_ == 0)
{
if (v_markInstances_73_ == 0)
{
goto v___jp_161_;
}
else
{
return v_markInstances_30_;
}
}
else
{
if (v_markInstances_73_ == 0)
{
return v_markInstances_73_;
}
else
{
goto v___jp_161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instBEqConfig_beq___boxed(lean_object* v_x_163_, lean_object* v_x_164_){
_start:
{
uint8_t v_res_165_; lean_object* v_r_166_; 
v_res_165_ = l_Lean_Grind_instBEqConfig_beq(v_x_163_, v_x_164_);
lean_dec_ref(v_x_164_);
lean_dec_ref(v_x_163_);
v_r_166_ = lean_box(v_res_165_);
return v_r_166_;
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
