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
static const lean_ctor_object l_Lean_Grind_instInhabitedConfig_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*11 + 32, .m_other = 11, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(lean_object* v_x_7_, lean_object* v_x_8_){
_start:
{
if (lean_obj_tag(v_x_7_) == 0)
{
if (lean_obj_tag(v_x_8_) == 0)
{
uint8_t v___x_9_; 
v___x_9_ = 1;
return v___x_9_;
}
else
{
uint8_t v___x_10_; 
v___x_10_ = 0;
return v___x_10_;
}
}
else
{
if (lean_obj_tag(v_x_8_) == 0)
{
uint8_t v___x_11_; 
v___x_11_ = 0;
return v___x_11_;
}
else
{
lean_object* v_val_12_; lean_object* v_val_13_; uint8_t v___x_14_; 
v_val_12_ = lean_ctor_get(v_x_7_, 0);
v_val_13_ = lean_ctor_get(v_x_8_, 0);
v___x_14_ = lean_nat_dec_eq(v_val_12_, v_val_13_);
return v___x_14_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0___boxed(lean_object* v_x_15_, lean_object* v_x_16_){
_start:
{
uint8_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_x_15_, v_x_16_);
lean_dec(v_x_16_);
lean_dec(v_x_15_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_instBEqConfig_beq(lean_object* v_x_19_, lean_object* v_x_20_){
_start:
{
uint8_t v_trace_21_; uint8_t v_markInstances_22_; uint8_t v_lax_23_; uint8_t v_suggestions_24_; uint8_t v_locals_25_; lean_object* v_splits_26_; lean_object* v_ematch_27_; lean_object* v_gen_28_; lean_object* v_instances_29_; uint8_t v_matchEqs_30_; uint8_t v_splitMatch_31_; uint8_t v_splitIte_32_; uint8_t v_splitIndPred_33_; uint8_t v_splitImp_34_; lean_object* v_canonHeartbeats_35_; uint8_t v_ext_36_; uint8_t v_extAll_37_; uint8_t v_etaStruct_38_; uint8_t v_funext_39_; uint8_t v_lookahead_40_; uint8_t v_verbose_41_; uint8_t v_clean_42_; uint8_t v_qlia_43_; uint8_t v_mbtc_44_; uint8_t v_zetaDelta_45_; uint8_t v_zeta_46_; uint8_t v_ring_47_; lean_object* v_ringSteps_48_; uint8_t v_linarith_49_; uint8_t v_lia_50_; uint8_t v_ac_51_; lean_object* v_acSteps_52_; lean_object* v_exp_53_; uint8_t v_abstractProof_54_; uint8_t v_inj_55_; uint8_t v_order_56_; lean_object* v_min_57_; lean_object* v_detailed_58_; uint8_t v_useSorry_59_; uint8_t v_revert_60_; uint8_t v_funCC_61_; uint8_t v_reducible_62_; lean_object* v_maxSuggestions_63_; uint8_t v_trace_64_; uint8_t v_markInstances_65_; uint8_t v_lax_66_; uint8_t v_suggestions_67_; uint8_t v_locals_68_; lean_object* v_splits_69_; lean_object* v_ematch_70_; lean_object* v_gen_71_; lean_object* v_instances_72_; uint8_t v_matchEqs_73_; uint8_t v_splitMatch_74_; uint8_t v_splitIte_75_; uint8_t v_splitIndPred_76_; uint8_t v_splitImp_77_; lean_object* v_canonHeartbeats_78_; uint8_t v_ext_79_; uint8_t v_extAll_80_; uint8_t v_etaStruct_81_; uint8_t v_funext_82_; uint8_t v_lookahead_83_; uint8_t v_verbose_84_; uint8_t v_clean_85_; uint8_t v_qlia_86_; uint8_t v_mbtc_87_; uint8_t v_zetaDelta_88_; uint8_t v_zeta_89_; uint8_t v_ring_90_; lean_object* v_ringSteps_91_; uint8_t v_linarith_92_; uint8_t v_lia_93_; uint8_t v_ac_94_; lean_object* v_acSteps_95_; lean_object* v_exp_96_; uint8_t v_abstractProof_97_; uint8_t v_inj_98_; uint8_t v_order_99_; lean_object* v_min_100_; lean_object* v_detailed_101_; uint8_t v_useSorry_102_; uint8_t v_revert_103_; uint8_t v_funCC_104_; uint8_t v_reducible_105_; lean_object* v_maxSuggestions_106_; uint8_t v___y_112_; uint8_t v___y_118_; uint8_t v___y_124_; uint8_t v___y_138_; uint8_t v___y_145_; 
v_trace_21_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11);
v_markInstances_22_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 1);
v_lax_23_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 2);
v_suggestions_24_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 3);
v_locals_25_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 4);
v_splits_26_ = lean_ctor_get(v_x_19_, 0);
v_ematch_27_ = lean_ctor_get(v_x_19_, 1);
v_gen_28_ = lean_ctor_get(v_x_19_, 2);
v_instances_29_ = lean_ctor_get(v_x_19_, 3);
v_matchEqs_30_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 5);
v_splitMatch_31_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 6);
v_splitIte_32_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 7);
v_splitIndPred_33_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 8);
v_splitImp_34_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 9);
v_canonHeartbeats_35_ = lean_ctor_get(v_x_19_, 4);
v_ext_36_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 10);
v_extAll_37_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 11);
v_etaStruct_38_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 12);
v_funext_39_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 13);
v_lookahead_40_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 14);
v_verbose_41_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 15);
v_clean_42_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 16);
v_qlia_43_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 17);
v_mbtc_44_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 18);
v_zetaDelta_45_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 19);
v_zeta_46_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 20);
v_ring_47_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 21);
v_ringSteps_48_ = lean_ctor_get(v_x_19_, 5);
v_linarith_49_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 22);
v_lia_50_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 23);
v_ac_51_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 24);
v_acSteps_52_ = lean_ctor_get(v_x_19_, 6);
v_exp_53_ = lean_ctor_get(v_x_19_, 7);
v_abstractProof_54_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 25);
v_inj_55_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 26);
v_order_56_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 27);
v_min_57_ = lean_ctor_get(v_x_19_, 8);
v_detailed_58_ = lean_ctor_get(v_x_19_, 9);
v_useSorry_59_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 28);
v_revert_60_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 29);
v_funCC_61_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 30);
v_reducible_62_ = lean_ctor_get_uint8(v_x_19_, sizeof(void*)*11 + 31);
v_maxSuggestions_63_ = lean_ctor_get(v_x_19_, 10);
v_trace_64_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11);
v_markInstances_65_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 1);
v_lax_66_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 2);
v_suggestions_67_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 3);
v_locals_68_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 4);
v_splits_69_ = lean_ctor_get(v_x_20_, 0);
v_ematch_70_ = lean_ctor_get(v_x_20_, 1);
v_gen_71_ = lean_ctor_get(v_x_20_, 2);
v_instances_72_ = lean_ctor_get(v_x_20_, 3);
v_matchEqs_73_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 5);
v_splitMatch_74_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 6);
v_splitIte_75_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 7);
v_splitIndPred_76_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 8);
v_splitImp_77_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 9);
v_canonHeartbeats_78_ = lean_ctor_get(v_x_20_, 4);
v_ext_79_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 10);
v_extAll_80_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 11);
v_etaStruct_81_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 12);
v_funext_82_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 13);
v_lookahead_83_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 14);
v_verbose_84_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 15);
v_clean_85_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 16);
v_qlia_86_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 17);
v_mbtc_87_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 18);
v_zetaDelta_88_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 19);
v_zeta_89_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 20);
v_ring_90_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 21);
v_ringSteps_91_ = lean_ctor_get(v_x_20_, 5);
v_linarith_92_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 22);
v_lia_93_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 23);
v_ac_94_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 24);
v_acSteps_95_ = lean_ctor_get(v_x_20_, 6);
v_exp_96_ = lean_ctor_get(v_x_20_, 7);
v_abstractProof_97_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 25);
v_inj_98_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 26);
v_order_99_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 27);
v_min_100_ = lean_ctor_get(v_x_20_, 8);
v_detailed_101_ = lean_ctor_get(v_x_20_, 9);
v_useSorry_102_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 28);
v_revert_103_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 29);
v_funCC_104_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 30);
v_reducible_105_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*11 + 31);
v_maxSuggestions_106_ = lean_ctor_get(v_x_20_, 10);
if (v_trace_21_ == 0)
{
if (v_trace_64_ == 0)
{
goto v___jp_154_;
}
else
{
return v_trace_21_;
}
}
else
{
if (v_trace_64_ == 0)
{
return v_trace_64_;
}
else
{
goto v___jp_154_;
}
}
v___jp_107_:
{
if (v_reducible_62_ == 0)
{
if (v_reducible_105_ == 0)
{
uint8_t v___x_108_; 
v___x_108_ = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_maxSuggestions_63_, v_maxSuggestions_106_);
return v___x_108_;
}
else
{
return v_reducible_62_;
}
}
else
{
if (v_reducible_105_ == 0)
{
return v_reducible_105_;
}
else
{
uint8_t v___x_109_; 
v___x_109_ = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_maxSuggestions_63_, v_maxSuggestions_106_);
return v___x_109_;
}
}
}
v___jp_110_:
{
if (v_funCC_61_ == 0)
{
if (v_funCC_104_ == 0)
{
goto v___jp_107_;
}
else
{
return v_funCC_61_;
}
}
else
{
if (v_funCC_104_ == 0)
{
return v_funCC_104_;
}
else
{
goto v___jp_107_;
}
}
}
v___jp_111_:
{
if (v___y_112_ == 0)
{
return v___y_112_;
}
else
{
if (v_revert_60_ == 0)
{
if (v_revert_103_ == 0)
{
goto v___jp_110_;
}
else
{
return v_revert_60_;
}
}
else
{
if (v_revert_103_ == 0)
{
return v_revert_103_;
}
else
{
goto v___jp_110_;
}
}
}
}
v___jp_113_:
{
uint8_t v___x_114_; 
v___x_114_ = lean_nat_dec_eq(v_min_57_, v_min_100_);
if (v___x_114_ == 0)
{
return v___x_114_;
}
else
{
uint8_t v___x_115_; 
v___x_115_ = lean_nat_dec_eq(v_detailed_58_, v_detailed_101_);
if (v___x_115_ == 0)
{
return v___x_115_;
}
else
{
if (v_useSorry_59_ == 0)
{
if (v_useSorry_102_ == 0)
{
v___y_112_ = v___x_115_;
goto v___jp_111_;
}
else
{
return v_useSorry_59_;
}
}
else
{
v___y_112_ = v_useSorry_102_;
goto v___jp_111_;
}
}
}
}
v___jp_116_:
{
if (v_order_56_ == 0)
{
if (v_order_99_ == 0)
{
goto v___jp_113_;
}
else
{
return v_order_56_;
}
}
else
{
if (v_order_99_ == 0)
{
return v_order_99_;
}
else
{
goto v___jp_113_;
}
}
}
v___jp_117_:
{
if (v___y_118_ == 0)
{
return v___y_118_;
}
else
{
if (v_inj_55_ == 0)
{
if (v_inj_98_ == 0)
{
goto v___jp_116_;
}
else
{
return v_inj_55_;
}
}
else
{
if (v_inj_98_ == 0)
{
return v_inj_98_;
}
else
{
goto v___jp_116_;
}
}
}
}
v___jp_119_:
{
uint8_t v___x_120_; 
v___x_120_ = lean_nat_dec_eq(v_acSteps_52_, v_acSteps_95_);
if (v___x_120_ == 0)
{
return v___x_120_;
}
else
{
uint8_t v___x_121_; 
v___x_121_ = lean_nat_dec_eq(v_exp_53_, v_exp_96_);
if (v___x_121_ == 0)
{
return v___x_121_;
}
else
{
if (v_abstractProof_54_ == 0)
{
if (v_abstractProof_97_ == 0)
{
v___y_118_ = v___x_121_;
goto v___jp_117_;
}
else
{
return v_abstractProof_54_;
}
}
else
{
v___y_118_ = v_abstractProof_97_;
goto v___jp_117_;
}
}
}
}
v___jp_122_:
{
if (v_ac_51_ == 0)
{
if (v_ac_94_ == 0)
{
goto v___jp_119_;
}
else
{
return v_ac_51_;
}
}
else
{
if (v_ac_94_ == 0)
{
return v_ac_94_;
}
else
{
goto v___jp_119_;
}
}
}
v___jp_123_:
{
if (v___y_124_ == 0)
{
return v___y_124_;
}
else
{
if (v_lia_50_ == 0)
{
if (v_lia_93_ == 0)
{
goto v___jp_122_;
}
else
{
return v_lia_50_;
}
}
else
{
if (v_lia_93_ == 0)
{
return v_lia_93_;
}
else
{
goto v___jp_122_;
}
}
}
}
v___jp_125_:
{
uint8_t v___x_126_; 
v___x_126_ = lean_nat_dec_eq(v_ringSteps_48_, v_ringSteps_91_);
if (v___x_126_ == 0)
{
return v___x_126_;
}
else
{
if (v_linarith_49_ == 0)
{
if (v_linarith_92_ == 0)
{
v___y_124_ = v___x_126_;
goto v___jp_123_;
}
else
{
return v_linarith_49_;
}
}
else
{
v___y_124_ = v_linarith_92_;
goto v___jp_123_;
}
}
}
v___jp_127_:
{
if (v_ring_47_ == 0)
{
if (v_ring_90_ == 0)
{
goto v___jp_125_;
}
else
{
return v_ring_47_;
}
}
else
{
if (v_ring_90_ == 0)
{
return v_ring_90_;
}
else
{
goto v___jp_125_;
}
}
}
v___jp_128_:
{
if (v_zeta_46_ == 0)
{
if (v_zeta_89_ == 0)
{
goto v___jp_127_;
}
else
{
return v_zeta_46_;
}
}
else
{
if (v_zeta_89_ == 0)
{
return v_zeta_89_;
}
else
{
goto v___jp_127_;
}
}
}
v___jp_129_:
{
if (v_zetaDelta_45_ == 0)
{
if (v_zetaDelta_88_ == 0)
{
goto v___jp_128_;
}
else
{
return v_zetaDelta_45_;
}
}
else
{
if (v_zetaDelta_88_ == 0)
{
return v_zetaDelta_88_;
}
else
{
goto v___jp_128_;
}
}
}
v___jp_130_:
{
if (v_mbtc_44_ == 0)
{
if (v_mbtc_87_ == 0)
{
goto v___jp_129_;
}
else
{
return v_mbtc_44_;
}
}
else
{
if (v_mbtc_87_ == 0)
{
return v_mbtc_87_;
}
else
{
goto v___jp_129_;
}
}
}
v___jp_131_:
{
if (v_qlia_43_ == 0)
{
if (v_qlia_86_ == 0)
{
goto v___jp_130_;
}
else
{
return v_qlia_43_;
}
}
else
{
if (v_qlia_86_ == 0)
{
return v_qlia_86_;
}
else
{
goto v___jp_130_;
}
}
}
v___jp_132_:
{
if (v_clean_42_ == 0)
{
if (v_clean_85_ == 0)
{
goto v___jp_131_;
}
else
{
return v_clean_42_;
}
}
else
{
if (v_clean_85_ == 0)
{
return v_clean_85_;
}
else
{
goto v___jp_131_;
}
}
}
v___jp_133_:
{
if (v_verbose_41_ == 0)
{
if (v_verbose_84_ == 0)
{
goto v___jp_132_;
}
else
{
return v_verbose_41_;
}
}
else
{
if (v_verbose_84_ == 0)
{
return v_verbose_84_;
}
else
{
goto v___jp_132_;
}
}
}
v___jp_134_:
{
if (v_lookahead_40_ == 0)
{
if (v_lookahead_83_ == 0)
{
goto v___jp_133_;
}
else
{
return v_lookahead_40_;
}
}
else
{
if (v_lookahead_83_ == 0)
{
return v_lookahead_83_;
}
else
{
goto v___jp_133_;
}
}
}
v___jp_135_:
{
if (v_funext_39_ == 0)
{
if (v_funext_82_ == 0)
{
goto v___jp_134_;
}
else
{
return v_funext_39_;
}
}
else
{
if (v_funext_82_ == 0)
{
return v_funext_82_;
}
else
{
goto v___jp_134_;
}
}
}
v___jp_136_:
{
if (v_etaStruct_38_ == 0)
{
if (v_etaStruct_81_ == 0)
{
goto v___jp_135_;
}
else
{
return v_etaStruct_38_;
}
}
else
{
if (v_etaStruct_81_ == 0)
{
return v_etaStruct_81_;
}
else
{
goto v___jp_135_;
}
}
}
v___jp_137_:
{
if (v___y_138_ == 0)
{
return v___y_138_;
}
else
{
if (v_extAll_37_ == 0)
{
if (v_extAll_80_ == 0)
{
goto v___jp_136_;
}
else
{
return v_extAll_37_;
}
}
else
{
if (v_extAll_80_ == 0)
{
return v_extAll_80_;
}
else
{
goto v___jp_136_;
}
}
}
}
v___jp_139_:
{
uint8_t v___x_140_; 
v___x_140_ = lean_nat_dec_eq(v_canonHeartbeats_35_, v_canonHeartbeats_78_);
if (v___x_140_ == 0)
{
return v___x_140_;
}
else
{
if (v_ext_36_ == 0)
{
if (v_ext_79_ == 0)
{
v___y_138_ = v___x_140_;
goto v___jp_137_;
}
else
{
return v_ext_36_;
}
}
else
{
v___y_138_ = v_ext_79_;
goto v___jp_137_;
}
}
}
v___jp_141_:
{
if (v_splitImp_34_ == 0)
{
if (v_splitImp_77_ == 0)
{
goto v___jp_139_;
}
else
{
return v_splitImp_34_;
}
}
else
{
if (v_splitImp_77_ == 0)
{
return v_splitImp_77_;
}
else
{
goto v___jp_139_;
}
}
}
v___jp_142_:
{
if (v_splitIndPred_33_ == 0)
{
if (v_splitIndPred_76_ == 0)
{
goto v___jp_141_;
}
else
{
return v_splitIndPred_33_;
}
}
else
{
if (v_splitIndPred_76_ == 0)
{
return v_splitIndPred_76_;
}
else
{
goto v___jp_141_;
}
}
}
v___jp_143_:
{
if (v_splitIte_32_ == 0)
{
if (v_splitIte_75_ == 0)
{
goto v___jp_142_;
}
else
{
return v_splitIte_32_;
}
}
else
{
if (v_splitIte_75_ == 0)
{
return v_splitIte_75_;
}
else
{
goto v___jp_142_;
}
}
}
v___jp_144_:
{
if (v___y_145_ == 0)
{
return v___y_145_;
}
else
{
if (v_splitMatch_31_ == 0)
{
if (v_splitMatch_74_ == 0)
{
goto v___jp_143_;
}
else
{
return v_splitMatch_31_;
}
}
else
{
if (v_splitMatch_74_ == 0)
{
return v_splitMatch_74_;
}
else
{
goto v___jp_143_;
}
}
}
}
v___jp_146_:
{
uint8_t v___x_147_; 
v___x_147_ = lean_nat_dec_eq(v_splits_26_, v_splits_69_);
if (v___x_147_ == 0)
{
return v___x_147_;
}
else
{
uint8_t v___x_148_; 
v___x_148_ = lean_nat_dec_eq(v_ematch_27_, v_ematch_70_);
if (v___x_148_ == 0)
{
return v___x_148_;
}
else
{
uint8_t v___x_149_; 
v___x_149_ = lean_nat_dec_eq(v_gen_28_, v_gen_71_);
if (v___x_149_ == 0)
{
return v___x_149_;
}
else
{
uint8_t v___x_150_; 
v___x_150_ = lean_nat_dec_eq(v_instances_29_, v_instances_72_);
if (v___x_150_ == 0)
{
return v___x_150_;
}
else
{
if (v_matchEqs_30_ == 0)
{
if (v_matchEqs_73_ == 0)
{
v___y_145_ = v___x_150_;
goto v___jp_144_;
}
else
{
return v_matchEqs_30_;
}
}
else
{
v___y_145_ = v_matchEqs_73_;
goto v___jp_144_;
}
}
}
}
}
}
v___jp_151_:
{
if (v_locals_25_ == 0)
{
if (v_locals_68_ == 0)
{
goto v___jp_146_;
}
else
{
return v_locals_25_;
}
}
else
{
if (v_locals_68_ == 0)
{
return v_locals_68_;
}
else
{
goto v___jp_146_;
}
}
}
v___jp_152_:
{
if (v_suggestions_24_ == 0)
{
if (v_suggestions_67_ == 0)
{
goto v___jp_151_;
}
else
{
return v_suggestions_24_;
}
}
else
{
if (v_suggestions_67_ == 0)
{
return v_suggestions_67_;
}
else
{
goto v___jp_151_;
}
}
}
v___jp_153_:
{
if (v_lax_23_ == 0)
{
if (v_lax_66_ == 0)
{
goto v___jp_152_;
}
else
{
return v_lax_23_;
}
}
else
{
if (v_lax_66_ == 0)
{
return v_lax_66_;
}
else
{
goto v___jp_152_;
}
}
}
v___jp_154_:
{
if (v_markInstances_22_ == 0)
{
if (v_markInstances_65_ == 0)
{
goto v___jp_153_;
}
else
{
return v_markInstances_22_;
}
}
else
{
if (v_markInstances_65_ == 0)
{
return v_markInstances_65_;
}
else
{
goto v___jp_153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instBEqConfig_beq___boxed(lean_object* v_x_155_, lean_object* v_x_156_){
_start:
{
uint8_t v_res_157_; lean_object* v_r_158_; 
v_res_157_ = l_Lean_Grind_instBEqConfig_beq(v_x_155_, v_x_156_);
lean_dec_ref(v_x_156_);
lean_dec_ref(v_x_155_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
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
