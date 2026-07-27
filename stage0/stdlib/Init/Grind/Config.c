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
static const lean_ctor_object l_Lean_Grind_instInhabitedConfig_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*14 + 32, .m_other = 14, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(10000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1048576) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 1, 0, 1, 1)}};
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(lean_object* v_x_17_, lean_object* v_x_18_){
_start:
{
if (lean_obj_tag(v_x_17_) == 0)
{
if (lean_obj_tag(v_x_18_) == 0)
{
uint8_t v___x_19_; 
v___x_19_ = 1;
return v___x_19_;
}
else
{
uint8_t v___x_20_; 
v___x_20_ = 0;
return v___x_20_;
}
}
else
{
if (lean_obj_tag(v_x_18_) == 0)
{
uint8_t v___x_21_; 
v___x_21_ = 0;
return v___x_21_;
}
else
{
lean_object* v_val_22_; lean_object* v_val_23_; uint8_t v___x_24_; 
v_val_22_ = lean_ctor_get(v_x_17_, 0);
v_val_23_ = lean_ctor_get(v_x_18_, 0);
v___x_24_ = lean_nat_dec_eq(v_val_22_, v_val_23_);
return v___x_24_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0___boxed(lean_object* v_x_25_, lean_object* v_x_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_x_25_, v_x_26_);
lean_dec(v_x_26_);
lean_dec(v_x_25_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_instBEqConfig_beq(lean_object* v_x_29_, lean_object* v_x_30_){
_start:
{
uint8_t v_trace_31_; uint8_t v_markInstances_32_; uint8_t v_lax_33_; uint8_t v_suggestions_34_; uint8_t v_locals_35_; lean_object* v_splits_36_; lean_object* v_ematch_37_; lean_object* v_gen_38_; lean_object* v_genLocal_39_; lean_object* v_instances_40_; uint8_t v_matchEqs_41_; uint8_t v_splitMatch_42_; uint8_t v_splitIte_43_; uint8_t v_splitIndPred_44_; uint8_t v_splitImp_45_; lean_object* v_canonHeartbeats_46_; uint8_t v_ext_47_; uint8_t v_extAll_48_; uint8_t v_etaStruct_49_; uint8_t v_funext_50_; uint8_t v_lookahead_51_; uint8_t v_verbose_52_; uint8_t v_clean_53_; uint8_t v_qlia_54_; uint8_t v_mbtc_55_; uint8_t v_zetaDelta_56_; uint8_t v_zeta_57_; uint8_t v_ring_58_; lean_object* v_ringSteps_59_; lean_object* v_ringMaxDegree_60_; uint8_t v_linarith_61_; uint8_t v_lia_62_; lean_object* v_liaSteps_63_; uint8_t v_ac_64_; lean_object* v_acSteps_65_; lean_object* v_exp_66_; uint8_t v_abstractProof_67_; uint8_t v_inj_68_; uint8_t v_order_69_; lean_object* v_min_70_; lean_object* v_detailed_71_; uint8_t v_useSorry_72_; uint8_t v_revert_73_; uint8_t v_funCC_74_; uint8_t v_reducible_75_; lean_object* v_maxSuggestions_76_; uint8_t v_trace_77_; uint8_t v_markInstances_78_; uint8_t v_lax_79_; uint8_t v_suggestions_80_; uint8_t v_locals_81_; lean_object* v_splits_82_; lean_object* v_ematch_83_; lean_object* v_gen_84_; lean_object* v_genLocal_85_; lean_object* v_instances_86_; uint8_t v_matchEqs_87_; uint8_t v_splitMatch_88_; uint8_t v_splitIte_89_; uint8_t v_splitIndPred_90_; uint8_t v_splitImp_91_; lean_object* v_canonHeartbeats_92_; uint8_t v_ext_93_; uint8_t v_extAll_94_; uint8_t v_etaStruct_95_; uint8_t v_funext_96_; uint8_t v_lookahead_97_; uint8_t v_verbose_98_; uint8_t v_clean_99_; uint8_t v_qlia_100_; uint8_t v_mbtc_101_; uint8_t v_zetaDelta_102_; uint8_t v_zeta_103_; uint8_t v_ring_104_; lean_object* v_ringSteps_105_; lean_object* v_ringMaxDegree_106_; uint8_t v_linarith_107_; uint8_t v_lia_108_; lean_object* v_liaSteps_109_; uint8_t v_ac_110_; lean_object* v_acSteps_111_; lean_object* v_exp_112_; uint8_t v_abstractProof_113_; uint8_t v_inj_114_; uint8_t v_order_115_; lean_object* v_min_116_; lean_object* v_detailed_117_; uint8_t v_useSorry_118_; uint8_t v_revert_119_; uint8_t v_funCC_120_; uint8_t v_reducible_121_; lean_object* v_maxSuggestions_122_; uint8_t v___y_128_; uint8_t v___y_134_; uint8_t v___y_136_; uint8_t v___y_142_; uint8_t v___y_157_; uint8_t v___y_164_; 
v_trace_31_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14);
v_markInstances_32_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 1);
v_lax_33_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 2);
v_suggestions_34_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 3);
v_locals_35_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 4);
v_splits_36_ = lean_ctor_get(v_x_29_, 0);
v_ematch_37_ = lean_ctor_get(v_x_29_, 1);
v_gen_38_ = lean_ctor_get(v_x_29_, 2);
v_genLocal_39_ = lean_ctor_get(v_x_29_, 3);
v_instances_40_ = lean_ctor_get(v_x_29_, 4);
v_matchEqs_41_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 5);
v_splitMatch_42_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 6);
v_splitIte_43_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 7);
v_splitIndPred_44_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 8);
v_splitImp_45_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 9);
v_canonHeartbeats_46_ = lean_ctor_get(v_x_29_, 5);
v_ext_47_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 10);
v_extAll_48_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 11);
v_etaStruct_49_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 12);
v_funext_50_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 13);
v_lookahead_51_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 14);
v_verbose_52_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 15);
v_clean_53_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 16);
v_qlia_54_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 17);
v_mbtc_55_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 18);
v_zetaDelta_56_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 19);
v_zeta_57_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 20);
v_ring_58_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 21);
v_ringSteps_59_ = lean_ctor_get(v_x_29_, 6);
v_ringMaxDegree_60_ = lean_ctor_get(v_x_29_, 7);
v_linarith_61_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 22);
v_lia_62_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 23);
v_liaSteps_63_ = lean_ctor_get(v_x_29_, 8);
v_ac_64_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 24);
v_acSteps_65_ = lean_ctor_get(v_x_29_, 9);
v_exp_66_ = lean_ctor_get(v_x_29_, 10);
v_abstractProof_67_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 25);
v_inj_68_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 26);
v_order_69_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 27);
v_min_70_ = lean_ctor_get(v_x_29_, 11);
v_detailed_71_ = lean_ctor_get(v_x_29_, 12);
v_useSorry_72_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 28);
v_revert_73_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 29);
v_funCC_74_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 30);
v_reducible_75_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 31);
v_maxSuggestions_76_ = lean_ctor_get(v_x_29_, 13);
v_trace_77_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14);
v_markInstances_78_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 1);
v_lax_79_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 2);
v_suggestions_80_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 3);
v_locals_81_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 4);
v_splits_82_ = lean_ctor_get(v_x_30_, 0);
v_ematch_83_ = lean_ctor_get(v_x_30_, 1);
v_gen_84_ = lean_ctor_get(v_x_30_, 2);
v_genLocal_85_ = lean_ctor_get(v_x_30_, 3);
v_instances_86_ = lean_ctor_get(v_x_30_, 4);
v_matchEqs_87_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 5);
v_splitMatch_88_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 6);
v_splitIte_89_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 7);
v_splitIndPred_90_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 8);
v_splitImp_91_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 9);
v_canonHeartbeats_92_ = lean_ctor_get(v_x_30_, 5);
v_ext_93_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 10);
v_extAll_94_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 11);
v_etaStruct_95_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 12);
v_funext_96_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 13);
v_lookahead_97_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 14);
v_verbose_98_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 15);
v_clean_99_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 16);
v_qlia_100_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 17);
v_mbtc_101_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 18);
v_zetaDelta_102_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 19);
v_zeta_103_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 20);
v_ring_104_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 21);
v_ringSteps_105_ = lean_ctor_get(v_x_30_, 6);
v_ringMaxDegree_106_ = lean_ctor_get(v_x_30_, 7);
v_linarith_107_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 22);
v_lia_108_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 23);
v_liaSteps_109_ = lean_ctor_get(v_x_30_, 8);
v_ac_110_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 24);
v_acSteps_111_ = lean_ctor_get(v_x_30_, 9);
v_exp_112_ = lean_ctor_get(v_x_30_, 10);
v_abstractProof_113_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 25);
v_inj_114_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 26);
v_order_115_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 27);
v_min_116_ = lean_ctor_get(v_x_30_, 11);
v_detailed_117_ = lean_ctor_get(v_x_30_, 12);
v_useSorry_118_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 28);
v_revert_119_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 29);
v_funCC_120_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 30);
v_reducible_121_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 31);
v_maxSuggestions_122_ = lean_ctor_get(v_x_30_, 13);
if (v_trace_31_ == 0)
{
if (v_trace_77_ == 0)
{
goto v___jp_174_;
}
else
{
return v_trace_31_;
}
}
else
{
if (v_trace_77_ == 0)
{
return v_trace_77_;
}
else
{
goto v___jp_174_;
}
}
v___jp_123_:
{
if (v_reducible_75_ == 0)
{
if (v_reducible_121_ == 0)
{
uint8_t v___x_124_; 
v___x_124_ = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_maxSuggestions_76_, v_maxSuggestions_122_);
return v___x_124_;
}
else
{
return v_reducible_75_;
}
}
else
{
if (v_reducible_121_ == 0)
{
return v_reducible_121_;
}
else
{
uint8_t v___x_125_; 
v___x_125_ = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_maxSuggestions_76_, v_maxSuggestions_122_);
return v___x_125_;
}
}
}
v___jp_126_:
{
if (v_funCC_74_ == 0)
{
if (v_funCC_120_ == 0)
{
goto v___jp_123_;
}
else
{
return v_funCC_74_;
}
}
else
{
if (v_funCC_120_ == 0)
{
return v_funCC_120_;
}
else
{
goto v___jp_123_;
}
}
}
v___jp_127_:
{
if (v___y_128_ == 0)
{
return v___y_128_;
}
else
{
if (v_revert_73_ == 0)
{
if (v_revert_119_ == 0)
{
goto v___jp_126_;
}
else
{
return v_revert_73_;
}
}
else
{
if (v_revert_119_ == 0)
{
return v_revert_119_;
}
else
{
goto v___jp_126_;
}
}
}
}
v___jp_129_:
{
uint8_t v___x_130_; 
v___x_130_ = lean_nat_dec_eq(v_min_70_, v_min_116_);
if (v___x_130_ == 0)
{
return v___x_130_;
}
else
{
uint8_t v___x_131_; 
v___x_131_ = lean_nat_dec_eq(v_detailed_71_, v_detailed_117_);
if (v___x_131_ == 0)
{
return v___x_131_;
}
else
{
if (v_useSorry_72_ == 0)
{
if (v_useSorry_118_ == 0)
{
v___y_128_ = v___x_131_;
goto v___jp_127_;
}
else
{
return v_useSorry_72_;
}
}
else
{
v___y_128_ = v_useSorry_118_;
goto v___jp_127_;
}
}
}
}
v___jp_132_:
{
if (v_order_69_ == 0)
{
if (v_order_115_ == 0)
{
goto v___jp_129_;
}
else
{
return v_order_69_;
}
}
else
{
if (v_order_115_ == 0)
{
return v_order_115_;
}
else
{
goto v___jp_129_;
}
}
}
v___jp_133_:
{
if (v___y_134_ == 0)
{
return v___y_134_;
}
else
{
if (v_inj_68_ == 0)
{
if (v_inj_114_ == 0)
{
goto v___jp_132_;
}
else
{
return v_inj_68_;
}
}
else
{
if (v_inj_114_ == 0)
{
return v_inj_114_;
}
else
{
goto v___jp_132_;
}
}
}
}
v___jp_135_:
{
if (v___y_136_ == 0)
{
return v___y_136_;
}
else
{
uint8_t v___x_137_; 
v___x_137_ = lean_nat_dec_eq(v_acSteps_65_, v_acSteps_111_);
if (v___x_137_ == 0)
{
return v___x_137_;
}
else
{
uint8_t v___x_138_; 
v___x_138_ = lean_nat_dec_eq(v_exp_66_, v_exp_112_);
if (v___x_138_ == 0)
{
return v___x_138_;
}
else
{
if (v_abstractProof_67_ == 0)
{
if (v_abstractProof_113_ == 0)
{
v___y_134_ = v___x_138_;
goto v___jp_133_;
}
else
{
return v_abstractProof_67_;
}
}
else
{
v___y_134_ = v_abstractProof_113_;
goto v___jp_133_;
}
}
}
}
}
v___jp_139_:
{
uint8_t v___x_140_; 
v___x_140_ = lean_nat_dec_eq(v_liaSteps_63_, v_liaSteps_109_);
if (v___x_140_ == 0)
{
return v___x_140_;
}
else
{
if (v_ac_64_ == 0)
{
if (v_ac_110_ == 0)
{
v___y_136_ = v___x_140_;
goto v___jp_135_;
}
else
{
return v_ac_64_;
}
}
else
{
v___y_136_ = v_ac_110_;
goto v___jp_135_;
}
}
}
v___jp_141_:
{
if (v___y_142_ == 0)
{
return v___y_142_;
}
else
{
if (v_lia_62_ == 0)
{
if (v_lia_108_ == 0)
{
goto v___jp_139_;
}
else
{
return v_lia_62_;
}
}
else
{
if (v_lia_108_ == 0)
{
return v_lia_108_;
}
else
{
goto v___jp_139_;
}
}
}
}
v___jp_143_:
{
uint8_t v___x_144_; 
v___x_144_ = lean_nat_dec_eq(v_ringSteps_59_, v_ringSteps_105_);
if (v___x_144_ == 0)
{
return v___x_144_;
}
else
{
uint8_t v___x_145_; 
v___x_145_ = lean_nat_dec_eq(v_ringMaxDegree_60_, v_ringMaxDegree_106_);
if (v___x_145_ == 0)
{
return v___x_145_;
}
else
{
if (v_linarith_61_ == 0)
{
if (v_linarith_107_ == 0)
{
v___y_142_ = v___x_145_;
goto v___jp_141_;
}
else
{
return v_linarith_61_;
}
}
else
{
v___y_142_ = v_linarith_107_;
goto v___jp_141_;
}
}
}
}
v___jp_146_:
{
if (v_ring_58_ == 0)
{
if (v_ring_104_ == 0)
{
goto v___jp_143_;
}
else
{
return v_ring_58_;
}
}
else
{
if (v_ring_104_ == 0)
{
return v_ring_104_;
}
else
{
goto v___jp_143_;
}
}
}
v___jp_147_:
{
if (v_zeta_57_ == 0)
{
if (v_zeta_103_ == 0)
{
goto v___jp_146_;
}
else
{
return v_zeta_57_;
}
}
else
{
if (v_zeta_103_ == 0)
{
return v_zeta_103_;
}
else
{
goto v___jp_146_;
}
}
}
v___jp_148_:
{
if (v_zetaDelta_56_ == 0)
{
if (v_zetaDelta_102_ == 0)
{
goto v___jp_147_;
}
else
{
return v_zetaDelta_56_;
}
}
else
{
if (v_zetaDelta_102_ == 0)
{
return v_zetaDelta_102_;
}
else
{
goto v___jp_147_;
}
}
}
v___jp_149_:
{
if (v_mbtc_55_ == 0)
{
if (v_mbtc_101_ == 0)
{
goto v___jp_148_;
}
else
{
return v_mbtc_55_;
}
}
else
{
if (v_mbtc_101_ == 0)
{
return v_mbtc_101_;
}
else
{
goto v___jp_148_;
}
}
}
v___jp_150_:
{
if (v_qlia_54_ == 0)
{
if (v_qlia_100_ == 0)
{
goto v___jp_149_;
}
else
{
return v_qlia_54_;
}
}
else
{
if (v_qlia_100_ == 0)
{
return v_qlia_100_;
}
else
{
goto v___jp_149_;
}
}
}
v___jp_151_:
{
if (v_clean_53_ == 0)
{
if (v_clean_99_ == 0)
{
goto v___jp_150_;
}
else
{
return v_clean_53_;
}
}
else
{
if (v_clean_99_ == 0)
{
return v_clean_99_;
}
else
{
goto v___jp_150_;
}
}
}
v___jp_152_:
{
if (v_verbose_52_ == 0)
{
if (v_verbose_98_ == 0)
{
goto v___jp_151_;
}
else
{
return v_verbose_52_;
}
}
else
{
if (v_verbose_98_ == 0)
{
return v_verbose_98_;
}
else
{
goto v___jp_151_;
}
}
}
v___jp_153_:
{
if (v_lookahead_51_ == 0)
{
if (v_lookahead_97_ == 0)
{
goto v___jp_152_;
}
else
{
return v_lookahead_51_;
}
}
else
{
if (v_lookahead_97_ == 0)
{
return v_lookahead_97_;
}
else
{
goto v___jp_152_;
}
}
}
v___jp_154_:
{
if (v_funext_50_ == 0)
{
if (v_funext_96_ == 0)
{
goto v___jp_153_;
}
else
{
return v_funext_50_;
}
}
else
{
if (v_funext_96_ == 0)
{
return v_funext_96_;
}
else
{
goto v___jp_153_;
}
}
}
v___jp_155_:
{
if (v_etaStruct_49_ == 0)
{
if (v_etaStruct_95_ == 0)
{
goto v___jp_154_;
}
else
{
return v_etaStruct_49_;
}
}
else
{
if (v_etaStruct_95_ == 0)
{
return v_etaStruct_95_;
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
if (v_extAll_48_ == 0)
{
if (v_extAll_94_ == 0)
{
goto v___jp_155_;
}
else
{
return v_extAll_48_;
}
}
else
{
if (v_extAll_94_ == 0)
{
return v_extAll_94_;
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
v___x_159_ = lean_nat_dec_eq(v_canonHeartbeats_46_, v_canonHeartbeats_92_);
if (v___x_159_ == 0)
{
return v___x_159_;
}
else
{
if (v_ext_47_ == 0)
{
if (v_ext_93_ == 0)
{
v___y_157_ = v___x_159_;
goto v___jp_156_;
}
else
{
return v_ext_47_;
}
}
else
{
v___y_157_ = v_ext_93_;
goto v___jp_156_;
}
}
}
v___jp_160_:
{
if (v_splitImp_45_ == 0)
{
if (v_splitImp_91_ == 0)
{
goto v___jp_158_;
}
else
{
return v_splitImp_45_;
}
}
else
{
if (v_splitImp_91_ == 0)
{
return v_splitImp_91_;
}
else
{
goto v___jp_158_;
}
}
}
v___jp_161_:
{
if (v_splitIndPred_44_ == 0)
{
if (v_splitIndPred_90_ == 0)
{
goto v___jp_160_;
}
else
{
return v_splitIndPred_44_;
}
}
else
{
if (v_splitIndPred_90_ == 0)
{
return v_splitIndPred_90_;
}
else
{
goto v___jp_160_;
}
}
}
v___jp_162_:
{
if (v_splitIte_43_ == 0)
{
if (v_splitIte_89_ == 0)
{
goto v___jp_161_;
}
else
{
return v_splitIte_43_;
}
}
else
{
if (v_splitIte_89_ == 0)
{
return v_splitIte_89_;
}
else
{
goto v___jp_161_;
}
}
}
v___jp_163_:
{
if (v___y_164_ == 0)
{
return v___y_164_;
}
else
{
if (v_splitMatch_42_ == 0)
{
if (v_splitMatch_88_ == 0)
{
goto v___jp_162_;
}
else
{
return v_splitMatch_42_;
}
}
else
{
if (v_splitMatch_88_ == 0)
{
return v_splitMatch_88_;
}
else
{
goto v___jp_162_;
}
}
}
}
v___jp_165_:
{
uint8_t v___x_166_; 
v___x_166_ = lean_nat_dec_eq(v_splits_36_, v_splits_82_);
if (v___x_166_ == 0)
{
return v___x_166_;
}
else
{
uint8_t v___x_167_; 
v___x_167_ = lean_nat_dec_eq(v_ematch_37_, v_ematch_83_);
if (v___x_167_ == 0)
{
return v___x_167_;
}
else
{
uint8_t v___x_168_; 
v___x_168_ = lean_nat_dec_eq(v_gen_38_, v_gen_84_);
if (v___x_168_ == 0)
{
return v___x_168_;
}
else
{
uint8_t v___x_169_; 
v___x_169_ = lean_nat_dec_eq(v_genLocal_39_, v_genLocal_85_);
if (v___x_169_ == 0)
{
return v___x_169_;
}
else
{
uint8_t v___x_170_; 
v___x_170_ = lean_nat_dec_eq(v_instances_40_, v_instances_86_);
if (v___x_170_ == 0)
{
return v___x_170_;
}
else
{
if (v_matchEqs_41_ == 0)
{
if (v_matchEqs_87_ == 0)
{
v___y_164_ = v___x_170_;
goto v___jp_163_;
}
else
{
return v_matchEqs_41_;
}
}
else
{
v___y_164_ = v_matchEqs_87_;
goto v___jp_163_;
}
}
}
}
}
}
}
v___jp_171_:
{
if (v_locals_35_ == 0)
{
if (v_locals_81_ == 0)
{
goto v___jp_165_;
}
else
{
return v_locals_35_;
}
}
else
{
if (v_locals_81_ == 0)
{
return v_locals_81_;
}
else
{
goto v___jp_165_;
}
}
}
v___jp_172_:
{
if (v_suggestions_34_ == 0)
{
if (v_suggestions_80_ == 0)
{
goto v___jp_171_;
}
else
{
return v_suggestions_34_;
}
}
else
{
if (v_suggestions_80_ == 0)
{
return v_suggestions_80_;
}
else
{
goto v___jp_171_;
}
}
}
v___jp_173_:
{
if (v_lax_33_ == 0)
{
if (v_lax_79_ == 0)
{
goto v___jp_172_;
}
else
{
return v_lax_33_;
}
}
else
{
if (v_lax_79_ == 0)
{
return v_lax_79_;
}
else
{
goto v___jp_172_;
}
}
}
v___jp_174_:
{
if (v_markInstances_32_ == 0)
{
if (v_markInstances_78_ == 0)
{
goto v___jp_173_;
}
else
{
return v_markInstances_32_;
}
}
else
{
if (v_markInstances_78_ == 0)
{
return v_markInstances_78_;
}
else
{
goto v___jp_173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instBEqConfig_beq___boxed(lean_object* v_x_175_, lean_object* v_x_176_){
_start:
{
uint8_t v_res_177_; lean_object* v_r_178_; 
v_res_177_ = l_Lean_Grind_instBEqConfig_beq(v_x_175_, v_x_176_);
lean_dec_ref(v_x_176_);
lean_dec_ref(v_x_175_);
v_r_178_ = lean_box(v_res_177_);
return v_r_178_;
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
