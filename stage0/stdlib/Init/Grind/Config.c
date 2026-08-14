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
static const lean_ctor_object l_Lean_Grind_instInhabitedConfig_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*14 + 40, .m_other = 14, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(10000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1048576) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 1, 1, 0, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
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
uint8_t v_trace_31_; uint8_t v_markInstances_32_; uint8_t v_lax_33_; uint8_t v_suggestions_34_; uint8_t v_locals_35_; lean_object* v_splits_36_; lean_object* v_ematch_37_; lean_object* v_gen_38_; lean_object* v_genLocal_39_; lean_object* v_instances_40_; uint8_t v_matchEqs_41_; uint8_t v_splitMatch_42_; uint8_t v_splitIte_43_; uint8_t v_splitIndPred_44_; uint8_t v_splitImp_45_; lean_object* v_canonHeartbeats_46_; uint8_t v_ext_47_; uint8_t v_extAll_48_; uint8_t v_etaStruct_49_; uint8_t v_funext_50_; uint8_t v_lookahead_51_; uint8_t v_verbose_52_; uint8_t v_clean_53_; uint8_t v_qlia_54_; uint8_t v_mbtc_55_; uint8_t v_zetaDelta_56_; uint8_t v_zeta_57_; uint8_t v_ring_58_; lean_object* v_ringSteps_59_; lean_object* v_ringMaxDegree_60_; uint8_t v_linarith_61_; uint8_t v_lia_62_; lean_object* v_liaSteps_63_; uint8_t v_hom_64_; uint8_t v_ac_65_; lean_object* v_acSteps_66_; lean_object* v_exp_67_; uint8_t v_abstractProof_68_; uint8_t v_inj_69_; uint8_t v_order_70_; lean_object* v_min_71_; lean_object* v_detailed_72_; uint8_t v_useSorry_73_; uint8_t v_revert_74_; uint8_t v_funCC_75_; uint8_t v_reducible_76_; lean_object* v_maxSuggestions_77_; uint8_t v_trace_78_; uint8_t v_markInstances_79_; uint8_t v_lax_80_; uint8_t v_suggestions_81_; uint8_t v_locals_82_; lean_object* v_splits_83_; lean_object* v_ematch_84_; lean_object* v_gen_85_; lean_object* v_genLocal_86_; lean_object* v_instances_87_; uint8_t v_matchEqs_88_; uint8_t v_splitMatch_89_; uint8_t v_splitIte_90_; uint8_t v_splitIndPred_91_; uint8_t v_splitImp_92_; lean_object* v_canonHeartbeats_93_; uint8_t v_ext_94_; uint8_t v_extAll_95_; uint8_t v_etaStruct_96_; uint8_t v_funext_97_; uint8_t v_lookahead_98_; uint8_t v_verbose_99_; uint8_t v_clean_100_; uint8_t v_qlia_101_; uint8_t v_mbtc_102_; uint8_t v_zetaDelta_103_; uint8_t v_zeta_104_; uint8_t v_ring_105_; lean_object* v_ringSteps_106_; lean_object* v_ringMaxDegree_107_; uint8_t v_linarith_108_; uint8_t v_lia_109_; lean_object* v_liaSteps_110_; uint8_t v_hom_111_; uint8_t v_ac_112_; lean_object* v_acSteps_113_; lean_object* v_exp_114_; uint8_t v_abstractProof_115_; uint8_t v_inj_116_; uint8_t v_order_117_; lean_object* v_min_118_; lean_object* v_detailed_119_; uint8_t v_useSorry_120_; uint8_t v_revert_121_; uint8_t v_funCC_122_; uint8_t v_reducible_123_; lean_object* v_maxSuggestions_124_; uint8_t v___y_130_; uint8_t v___y_136_; uint8_t v___y_141_; uint8_t v___y_145_; uint8_t v___y_160_; uint8_t v___y_167_; 
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
v_hom_64_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 24);
v_ac_65_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 25);
v_acSteps_66_ = lean_ctor_get(v_x_29_, 9);
v_exp_67_ = lean_ctor_get(v_x_29_, 10);
v_abstractProof_68_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 26);
v_inj_69_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 27);
v_order_70_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 28);
v_min_71_ = lean_ctor_get(v_x_29_, 11);
v_detailed_72_ = lean_ctor_get(v_x_29_, 12);
v_useSorry_73_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 29);
v_revert_74_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 30);
v_funCC_75_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 31);
v_reducible_76_ = lean_ctor_get_uint8(v_x_29_, sizeof(void*)*14 + 32);
v_maxSuggestions_77_ = lean_ctor_get(v_x_29_, 13);
v_trace_78_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14);
v_markInstances_79_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 1);
v_lax_80_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 2);
v_suggestions_81_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 3);
v_locals_82_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 4);
v_splits_83_ = lean_ctor_get(v_x_30_, 0);
v_ematch_84_ = lean_ctor_get(v_x_30_, 1);
v_gen_85_ = lean_ctor_get(v_x_30_, 2);
v_genLocal_86_ = lean_ctor_get(v_x_30_, 3);
v_instances_87_ = lean_ctor_get(v_x_30_, 4);
v_matchEqs_88_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 5);
v_splitMatch_89_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 6);
v_splitIte_90_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 7);
v_splitIndPred_91_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 8);
v_splitImp_92_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 9);
v_canonHeartbeats_93_ = lean_ctor_get(v_x_30_, 5);
v_ext_94_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 10);
v_extAll_95_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 11);
v_etaStruct_96_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 12);
v_funext_97_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 13);
v_lookahead_98_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 14);
v_verbose_99_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 15);
v_clean_100_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 16);
v_qlia_101_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 17);
v_mbtc_102_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 18);
v_zetaDelta_103_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 19);
v_zeta_104_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 20);
v_ring_105_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 21);
v_ringSteps_106_ = lean_ctor_get(v_x_30_, 6);
v_ringMaxDegree_107_ = lean_ctor_get(v_x_30_, 7);
v_linarith_108_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 22);
v_lia_109_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 23);
v_liaSteps_110_ = lean_ctor_get(v_x_30_, 8);
v_hom_111_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 24);
v_ac_112_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 25);
v_acSteps_113_ = lean_ctor_get(v_x_30_, 9);
v_exp_114_ = lean_ctor_get(v_x_30_, 10);
v_abstractProof_115_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 26);
v_inj_116_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 27);
v_order_117_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 28);
v_min_118_ = lean_ctor_get(v_x_30_, 11);
v_detailed_119_ = lean_ctor_get(v_x_30_, 12);
v_useSorry_120_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 29);
v_revert_121_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 30);
v_funCC_122_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 31);
v_reducible_123_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 32);
v_maxSuggestions_124_ = lean_ctor_get(v_x_30_, 13);
if (v_trace_31_ == 0)
{
if (v_trace_78_ == 0)
{
goto v___jp_177_;
}
else
{
return v_trace_31_;
}
}
else
{
if (v_trace_78_ == 0)
{
return v_trace_78_;
}
else
{
goto v___jp_177_;
}
}
v___jp_125_:
{
if (v_reducible_76_ == 0)
{
if (v_reducible_123_ == 0)
{
uint8_t v___x_126_; 
v___x_126_ = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_maxSuggestions_77_, v_maxSuggestions_124_);
return v___x_126_;
}
else
{
return v_reducible_76_;
}
}
else
{
if (v_reducible_123_ == 0)
{
return v_reducible_123_;
}
else
{
uint8_t v___x_127_; 
v___x_127_ = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_maxSuggestions_77_, v_maxSuggestions_124_);
return v___x_127_;
}
}
}
v___jp_128_:
{
if (v_funCC_75_ == 0)
{
if (v_funCC_122_ == 0)
{
goto v___jp_125_;
}
else
{
return v_funCC_75_;
}
}
else
{
if (v_funCC_122_ == 0)
{
return v_funCC_122_;
}
else
{
goto v___jp_125_;
}
}
}
v___jp_129_:
{
if (v___y_130_ == 0)
{
return v___y_130_;
}
else
{
if (v_revert_74_ == 0)
{
if (v_revert_121_ == 0)
{
goto v___jp_128_;
}
else
{
return v_revert_74_;
}
}
else
{
if (v_revert_121_ == 0)
{
return v_revert_121_;
}
else
{
goto v___jp_128_;
}
}
}
}
v___jp_131_:
{
uint8_t v___x_132_; 
v___x_132_ = lean_nat_dec_eq(v_min_71_, v_min_118_);
if (v___x_132_ == 0)
{
return v___x_132_;
}
else
{
uint8_t v___x_133_; 
v___x_133_ = lean_nat_dec_eq(v_detailed_72_, v_detailed_119_);
if (v___x_133_ == 0)
{
return v___x_133_;
}
else
{
if (v_useSorry_73_ == 0)
{
if (v_useSorry_120_ == 0)
{
v___y_130_ = v___x_133_;
goto v___jp_129_;
}
else
{
return v_useSorry_73_;
}
}
else
{
v___y_130_ = v_useSorry_120_;
goto v___jp_129_;
}
}
}
}
v___jp_134_:
{
if (v_order_70_ == 0)
{
if (v_order_117_ == 0)
{
goto v___jp_131_;
}
else
{
return v_order_70_;
}
}
else
{
if (v_order_117_ == 0)
{
return v_order_117_;
}
else
{
goto v___jp_131_;
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
if (v_inj_69_ == 0)
{
if (v_inj_116_ == 0)
{
goto v___jp_134_;
}
else
{
return v_inj_69_;
}
}
else
{
if (v_inj_116_ == 0)
{
return v_inj_116_;
}
else
{
goto v___jp_134_;
}
}
}
}
v___jp_137_:
{
uint8_t v___x_138_; 
v___x_138_ = lean_nat_dec_eq(v_acSteps_66_, v_acSteps_113_);
if (v___x_138_ == 0)
{
return v___x_138_;
}
else
{
uint8_t v___x_139_; 
v___x_139_ = lean_nat_dec_eq(v_exp_67_, v_exp_114_);
if (v___x_139_ == 0)
{
return v___x_139_;
}
else
{
if (v_abstractProof_68_ == 0)
{
if (v_abstractProof_115_ == 0)
{
v___y_136_ = v___x_139_;
goto v___jp_135_;
}
else
{
return v_abstractProof_68_;
}
}
else
{
v___y_136_ = v_abstractProof_115_;
goto v___jp_135_;
}
}
}
}
v___jp_140_:
{
if (v___y_141_ == 0)
{
return v___y_141_;
}
else
{
if (v_ac_65_ == 0)
{
if (v_ac_112_ == 0)
{
goto v___jp_137_;
}
else
{
return v_ac_65_;
}
}
else
{
if (v_ac_112_ == 0)
{
return v_ac_112_;
}
else
{
goto v___jp_137_;
}
}
}
}
v___jp_142_:
{
uint8_t v___x_143_; 
v___x_143_ = lean_nat_dec_eq(v_liaSteps_63_, v_liaSteps_110_);
if (v___x_143_ == 0)
{
return v___x_143_;
}
else
{
if (v_hom_64_ == 0)
{
if (v_hom_111_ == 0)
{
v___y_141_ = v___x_143_;
goto v___jp_140_;
}
else
{
return v_hom_64_;
}
}
else
{
v___y_141_ = v_hom_111_;
goto v___jp_140_;
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
if (v_lia_62_ == 0)
{
if (v_lia_109_ == 0)
{
goto v___jp_142_;
}
else
{
return v_lia_62_;
}
}
else
{
if (v_lia_109_ == 0)
{
return v_lia_109_;
}
else
{
goto v___jp_142_;
}
}
}
}
v___jp_146_:
{
uint8_t v___x_147_; 
v___x_147_ = lean_nat_dec_eq(v_ringSteps_59_, v_ringSteps_106_);
if (v___x_147_ == 0)
{
return v___x_147_;
}
else
{
uint8_t v___x_148_; 
v___x_148_ = lean_nat_dec_eq(v_ringMaxDegree_60_, v_ringMaxDegree_107_);
if (v___x_148_ == 0)
{
return v___x_148_;
}
else
{
if (v_linarith_61_ == 0)
{
if (v_linarith_108_ == 0)
{
v___y_145_ = v___x_148_;
goto v___jp_144_;
}
else
{
return v_linarith_61_;
}
}
else
{
v___y_145_ = v_linarith_108_;
goto v___jp_144_;
}
}
}
}
v___jp_149_:
{
if (v_ring_58_ == 0)
{
if (v_ring_105_ == 0)
{
goto v___jp_146_;
}
else
{
return v_ring_58_;
}
}
else
{
if (v_ring_105_ == 0)
{
return v_ring_105_;
}
else
{
goto v___jp_146_;
}
}
}
v___jp_150_:
{
if (v_zeta_57_ == 0)
{
if (v_zeta_104_ == 0)
{
goto v___jp_149_;
}
else
{
return v_zeta_57_;
}
}
else
{
if (v_zeta_104_ == 0)
{
return v_zeta_104_;
}
else
{
goto v___jp_149_;
}
}
}
v___jp_151_:
{
if (v_zetaDelta_56_ == 0)
{
if (v_zetaDelta_103_ == 0)
{
goto v___jp_150_;
}
else
{
return v_zetaDelta_56_;
}
}
else
{
if (v_zetaDelta_103_ == 0)
{
return v_zetaDelta_103_;
}
else
{
goto v___jp_150_;
}
}
}
v___jp_152_:
{
if (v_mbtc_55_ == 0)
{
if (v_mbtc_102_ == 0)
{
goto v___jp_151_;
}
else
{
return v_mbtc_55_;
}
}
else
{
if (v_mbtc_102_ == 0)
{
return v_mbtc_102_;
}
else
{
goto v___jp_151_;
}
}
}
v___jp_153_:
{
if (v_qlia_54_ == 0)
{
if (v_qlia_101_ == 0)
{
goto v___jp_152_;
}
else
{
return v_qlia_54_;
}
}
else
{
if (v_qlia_101_ == 0)
{
return v_qlia_101_;
}
else
{
goto v___jp_152_;
}
}
}
v___jp_154_:
{
if (v_clean_53_ == 0)
{
if (v_clean_100_ == 0)
{
goto v___jp_153_;
}
else
{
return v_clean_53_;
}
}
else
{
if (v_clean_100_ == 0)
{
return v_clean_100_;
}
else
{
goto v___jp_153_;
}
}
}
v___jp_155_:
{
if (v_verbose_52_ == 0)
{
if (v_verbose_99_ == 0)
{
goto v___jp_154_;
}
else
{
return v_verbose_52_;
}
}
else
{
if (v_verbose_99_ == 0)
{
return v_verbose_99_;
}
else
{
goto v___jp_154_;
}
}
}
v___jp_156_:
{
if (v_lookahead_51_ == 0)
{
if (v_lookahead_98_ == 0)
{
goto v___jp_155_;
}
else
{
return v_lookahead_51_;
}
}
else
{
if (v_lookahead_98_ == 0)
{
return v_lookahead_98_;
}
else
{
goto v___jp_155_;
}
}
}
v___jp_157_:
{
if (v_funext_50_ == 0)
{
if (v_funext_97_ == 0)
{
goto v___jp_156_;
}
else
{
return v_funext_50_;
}
}
else
{
if (v_funext_97_ == 0)
{
return v_funext_97_;
}
else
{
goto v___jp_156_;
}
}
}
v___jp_158_:
{
if (v_etaStruct_49_ == 0)
{
if (v_etaStruct_96_ == 0)
{
goto v___jp_157_;
}
else
{
return v_etaStruct_49_;
}
}
else
{
if (v_etaStruct_96_ == 0)
{
return v_etaStruct_96_;
}
else
{
goto v___jp_157_;
}
}
}
v___jp_159_:
{
if (v___y_160_ == 0)
{
return v___y_160_;
}
else
{
if (v_extAll_48_ == 0)
{
if (v_extAll_95_ == 0)
{
goto v___jp_158_;
}
else
{
return v_extAll_48_;
}
}
else
{
if (v_extAll_95_ == 0)
{
return v_extAll_95_;
}
else
{
goto v___jp_158_;
}
}
}
}
v___jp_161_:
{
uint8_t v___x_162_; 
v___x_162_ = lean_nat_dec_eq(v_canonHeartbeats_46_, v_canonHeartbeats_93_);
if (v___x_162_ == 0)
{
return v___x_162_;
}
else
{
if (v_ext_47_ == 0)
{
if (v_ext_94_ == 0)
{
v___y_160_ = v___x_162_;
goto v___jp_159_;
}
else
{
return v_ext_47_;
}
}
else
{
v___y_160_ = v_ext_94_;
goto v___jp_159_;
}
}
}
v___jp_163_:
{
if (v_splitImp_45_ == 0)
{
if (v_splitImp_92_ == 0)
{
goto v___jp_161_;
}
else
{
return v_splitImp_45_;
}
}
else
{
if (v_splitImp_92_ == 0)
{
return v_splitImp_92_;
}
else
{
goto v___jp_161_;
}
}
}
v___jp_164_:
{
if (v_splitIndPred_44_ == 0)
{
if (v_splitIndPred_91_ == 0)
{
goto v___jp_163_;
}
else
{
return v_splitIndPred_44_;
}
}
else
{
if (v_splitIndPred_91_ == 0)
{
return v_splitIndPred_91_;
}
else
{
goto v___jp_163_;
}
}
}
v___jp_165_:
{
if (v_splitIte_43_ == 0)
{
if (v_splitIte_90_ == 0)
{
goto v___jp_164_;
}
else
{
return v_splitIte_43_;
}
}
else
{
if (v_splitIte_90_ == 0)
{
return v_splitIte_90_;
}
else
{
goto v___jp_164_;
}
}
}
v___jp_166_:
{
if (v___y_167_ == 0)
{
return v___y_167_;
}
else
{
if (v_splitMatch_42_ == 0)
{
if (v_splitMatch_89_ == 0)
{
goto v___jp_165_;
}
else
{
return v_splitMatch_42_;
}
}
else
{
if (v_splitMatch_89_ == 0)
{
return v_splitMatch_89_;
}
else
{
goto v___jp_165_;
}
}
}
}
v___jp_168_:
{
uint8_t v___x_169_; 
v___x_169_ = lean_nat_dec_eq(v_splits_36_, v_splits_83_);
if (v___x_169_ == 0)
{
return v___x_169_;
}
else
{
uint8_t v___x_170_; 
v___x_170_ = lean_nat_dec_eq(v_ematch_37_, v_ematch_84_);
if (v___x_170_ == 0)
{
return v___x_170_;
}
else
{
uint8_t v___x_171_; 
v___x_171_ = lean_nat_dec_eq(v_gen_38_, v_gen_85_);
if (v___x_171_ == 0)
{
return v___x_171_;
}
else
{
uint8_t v___x_172_; 
v___x_172_ = lean_nat_dec_eq(v_genLocal_39_, v_genLocal_86_);
if (v___x_172_ == 0)
{
return v___x_172_;
}
else
{
uint8_t v___x_173_; 
v___x_173_ = lean_nat_dec_eq(v_instances_40_, v_instances_87_);
if (v___x_173_ == 0)
{
return v___x_173_;
}
else
{
if (v_matchEqs_41_ == 0)
{
if (v_matchEqs_88_ == 0)
{
v___y_167_ = v___x_173_;
goto v___jp_166_;
}
else
{
return v_matchEqs_41_;
}
}
else
{
v___y_167_ = v_matchEqs_88_;
goto v___jp_166_;
}
}
}
}
}
}
}
v___jp_174_:
{
if (v_locals_35_ == 0)
{
if (v_locals_82_ == 0)
{
goto v___jp_168_;
}
else
{
return v_locals_35_;
}
}
else
{
if (v_locals_82_ == 0)
{
return v_locals_82_;
}
else
{
goto v___jp_168_;
}
}
}
v___jp_175_:
{
if (v_suggestions_34_ == 0)
{
if (v_suggestions_81_ == 0)
{
goto v___jp_174_;
}
else
{
return v_suggestions_34_;
}
}
else
{
if (v_suggestions_81_ == 0)
{
return v_suggestions_81_;
}
else
{
goto v___jp_174_;
}
}
}
v___jp_176_:
{
if (v_lax_33_ == 0)
{
if (v_lax_80_ == 0)
{
goto v___jp_175_;
}
else
{
return v_lax_33_;
}
}
else
{
if (v_lax_80_ == 0)
{
return v_lax_80_;
}
else
{
goto v___jp_175_;
}
}
}
v___jp_177_:
{
if (v_markInstances_32_ == 0)
{
if (v_markInstances_79_ == 0)
{
goto v___jp_176_;
}
else
{
return v_markInstances_32_;
}
}
else
{
if (v_markInstances_79_ == 0)
{
return v_markInstances_79_;
}
else
{
goto v___jp_176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instBEqConfig_beq___boxed(lean_object* v_x_178_, lean_object* v_x_179_){
_start:
{
uint8_t v_res_180_; lean_object* v_r_181_; 
v_res_180_ = l_Lean_Grind_instBEqConfig_beq(v_x_178_, v_x_179_);
lean_dec_ref(v_x_179_);
lean_dec_ref(v_x_178_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
lean_object* runtime_initialize_Init_Core(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_Config(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
