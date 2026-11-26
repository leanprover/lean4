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
static const lean_ctor_object l_Lean_Grind_instInhabitedConfig_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*18 + 40, .m_other = 18, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(9) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(10000) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(16) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1048576) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 1, 0, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 1, 1, 0, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 1, 1, 0, 0, 0, 0, 0)}};
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(lean_object* v_x_19_, lean_object* v_x_20_){
_start:
{
if (lean_obj_tag(v_x_19_) == 0)
{
if (lean_obj_tag(v_x_20_) == 0)
{
uint8_t v___x_21_; 
v___x_21_ = 1;
return v___x_21_;
}
else
{
uint8_t v___x_22_; 
v___x_22_ = 0;
return v___x_22_;
}
}
else
{
if (lean_obj_tag(v_x_20_) == 0)
{
uint8_t v___x_23_; 
v___x_23_ = 0;
return v___x_23_;
}
else
{
lean_object* v_val_24_; lean_object* v_val_25_; uint8_t v___x_26_; 
v_val_24_ = lean_ctor_get(v_x_19_, 0);
v_val_25_ = lean_ctor_get(v_x_20_, 0);
v___x_26_ = lean_nat_dec_eq(v_val_24_, v_val_25_);
return v___x_26_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0___boxed(lean_object* v_x_27_, lean_object* v_x_28_){
_start:
{
uint8_t v_res_29_; lean_object* v_r_30_; 
v_res_29_ = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_x_27_, v_x_28_);
lean_dec(v_x_28_);
lean_dec(v_x_27_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_instBEqConfig_beq(lean_object* v_x_31_, lean_object* v_x_32_){
_start:
{
uint8_t v_trace_33_; uint8_t v_markInstances_34_; uint8_t v_lax_35_; uint8_t v_suggestions_36_; uint8_t v_locals_37_; lean_object* v_branches_38_; lean_object* v_splits_39_; lean_object* v_ematch_40_; lean_object* v_gen_41_; lean_object* v_genLocal_42_; lean_object* v_instances_43_; uint8_t v_matchEqs_44_; uint8_t v_splitMatch_45_; uint8_t v_splitIte_46_; uint8_t v_splitIndPred_47_; uint8_t v_splitImp_48_; uint8_t v_filterFacts_49_; lean_object* v_canonHeartbeats_50_; uint8_t v_ext_51_; uint8_t v_extAll_52_; uint8_t v_etaStruct_53_; uint8_t v_funext_54_; uint8_t v_lookahead_55_; uint8_t v_verbose_56_; uint8_t v_clean_57_; uint8_t v_qlia_58_; uint8_t v_mbtc_59_; uint8_t v_zetaDelta_60_; uint8_t v_zeta_61_; uint8_t v_distrib_62_; lean_object* v_maxChar_63_; uint8_t v_ring_64_; lean_object* v_ringSteps_65_; lean_object* v_ringMaxDegree_66_; uint8_t v_linarith_67_; uint8_t v_lia_68_; lean_object* v_liaSteps_69_; lean_object* v_liaReorders_70_; lean_object* v_liaReorderCases_71_; uint8_t v_hom_72_; uint8_t v_ac_73_; lean_object* v_acSteps_74_; lean_object* v_exp_75_; uint8_t v_abstractProof_76_; uint8_t v_inj_77_; uint8_t v_order_78_; lean_object* v_min_79_; lean_object* v_detailed_80_; uint8_t v_useSorry_81_; uint8_t v_revert_82_; uint8_t v_funCC_83_; uint8_t v_reducible_84_; lean_object* v_maxSuggestions_85_; uint8_t v_trace_86_; uint8_t v_markInstances_87_; uint8_t v_lax_88_; uint8_t v_suggestions_89_; uint8_t v_locals_90_; lean_object* v_branches_91_; lean_object* v_splits_92_; lean_object* v_ematch_93_; lean_object* v_gen_94_; lean_object* v_genLocal_95_; lean_object* v_instances_96_; uint8_t v_matchEqs_97_; uint8_t v_splitMatch_98_; uint8_t v_splitIte_99_; uint8_t v_splitIndPred_100_; uint8_t v_splitImp_101_; uint8_t v_filterFacts_102_; lean_object* v_canonHeartbeats_103_; uint8_t v_ext_104_; uint8_t v_extAll_105_; uint8_t v_etaStruct_106_; uint8_t v_funext_107_; uint8_t v_lookahead_108_; uint8_t v_verbose_109_; uint8_t v_clean_110_; uint8_t v_qlia_111_; uint8_t v_mbtc_112_; uint8_t v_zetaDelta_113_; uint8_t v_zeta_114_; uint8_t v_distrib_115_; lean_object* v_maxChar_116_; uint8_t v_ring_117_; lean_object* v_ringSteps_118_; lean_object* v_ringMaxDegree_119_; uint8_t v_linarith_120_; uint8_t v_lia_121_; lean_object* v_liaSteps_122_; lean_object* v_liaReorders_123_; lean_object* v_liaReorderCases_124_; uint8_t v_hom_125_; uint8_t v_ac_126_; lean_object* v_acSteps_127_; lean_object* v_exp_128_; uint8_t v_abstractProof_129_; uint8_t v_inj_130_; uint8_t v_order_131_; lean_object* v_min_132_; lean_object* v_detailed_133_; uint8_t v_useSorry_134_; uint8_t v_revert_135_; uint8_t v_funCC_136_; uint8_t v_reducible_137_; lean_object* v_maxSuggestions_138_; 
v_trace_33_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18);
v_markInstances_34_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 1);
v_lax_35_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 2);
v_suggestions_36_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 3);
v_locals_37_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 4);
v_branches_38_ = lean_ctor_get(v_x_31_, 0);
v_splits_39_ = lean_ctor_get(v_x_31_, 1);
v_ematch_40_ = lean_ctor_get(v_x_31_, 2);
v_gen_41_ = lean_ctor_get(v_x_31_, 3);
v_genLocal_42_ = lean_ctor_get(v_x_31_, 4);
v_instances_43_ = lean_ctor_get(v_x_31_, 5);
v_matchEqs_44_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 5);
v_splitMatch_45_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 6);
v_splitIte_46_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 7);
v_splitIndPred_47_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 8);
v_splitImp_48_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 9);
v_filterFacts_49_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 10);
v_canonHeartbeats_50_ = lean_ctor_get(v_x_31_, 6);
v_ext_51_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 11);
v_extAll_52_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 12);
v_etaStruct_53_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 13);
v_funext_54_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 14);
v_lookahead_55_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 15);
v_verbose_56_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 16);
v_clean_57_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 17);
v_qlia_58_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 18);
v_mbtc_59_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 19);
v_zetaDelta_60_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 20);
v_zeta_61_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 21);
v_distrib_62_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 22);
v_maxChar_63_ = lean_ctor_get(v_x_31_, 7);
v_ring_64_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 23);
v_ringSteps_65_ = lean_ctor_get(v_x_31_, 8);
v_ringMaxDegree_66_ = lean_ctor_get(v_x_31_, 9);
v_linarith_67_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 24);
v_lia_68_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 25);
v_liaSteps_69_ = lean_ctor_get(v_x_31_, 10);
v_liaReorders_70_ = lean_ctor_get(v_x_31_, 11);
v_liaReorderCases_71_ = lean_ctor_get(v_x_31_, 12);
v_hom_72_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 26);
v_ac_73_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 27);
v_acSteps_74_ = lean_ctor_get(v_x_31_, 13);
v_exp_75_ = lean_ctor_get(v_x_31_, 14);
v_abstractProof_76_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 28);
v_inj_77_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 29);
v_order_78_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 30);
v_min_79_ = lean_ctor_get(v_x_31_, 15);
v_detailed_80_ = lean_ctor_get(v_x_31_, 16);
v_useSorry_81_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 31);
v_revert_82_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 32);
v_funCC_83_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 33);
v_reducible_84_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 34);
v_maxSuggestions_85_ = lean_ctor_get(v_x_31_, 17);
v_trace_86_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18);
v_markInstances_87_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 1);
v_lax_88_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 2);
v_suggestions_89_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 3);
v_locals_90_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 4);
v_branches_91_ = lean_ctor_get(v_x_32_, 0);
v_splits_92_ = lean_ctor_get(v_x_32_, 1);
v_ematch_93_ = lean_ctor_get(v_x_32_, 2);
v_gen_94_ = lean_ctor_get(v_x_32_, 3);
v_genLocal_95_ = lean_ctor_get(v_x_32_, 4);
v_instances_96_ = lean_ctor_get(v_x_32_, 5);
v_matchEqs_97_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 5);
v_splitMatch_98_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 6);
v_splitIte_99_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 7);
v_splitIndPred_100_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 8);
v_splitImp_101_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 9);
v_filterFacts_102_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 10);
v_canonHeartbeats_103_ = lean_ctor_get(v_x_32_, 6);
v_ext_104_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 11);
v_extAll_105_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 12);
v_etaStruct_106_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 13);
v_funext_107_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 14);
v_lookahead_108_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 15);
v_verbose_109_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 16);
v_clean_110_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 17);
v_qlia_111_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 18);
v_mbtc_112_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 19);
v_zetaDelta_113_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 20);
v_zeta_114_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 21);
v_distrib_115_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 22);
v_maxChar_116_ = lean_ctor_get(v_x_32_, 7);
v_ring_117_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 23);
v_ringSteps_118_ = lean_ctor_get(v_x_32_, 8);
v_ringMaxDegree_119_ = lean_ctor_get(v_x_32_, 9);
v_linarith_120_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 24);
v_lia_121_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 25);
v_liaSteps_122_ = lean_ctor_get(v_x_32_, 10);
v_liaReorders_123_ = lean_ctor_get(v_x_32_, 11);
v_liaReorderCases_124_ = lean_ctor_get(v_x_32_, 12);
v_hom_125_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 26);
v_ac_126_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 27);
v_acSteps_127_ = lean_ctor_get(v_x_32_, 13);
v_exp_128_ = lean_ctor_get(v_x_32_, 14);
v_abstractProof_129_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 28);
v_inj_130_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 29);
v_order_131_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 30);
v_min_132_ = lean_ctor_get(v_x_32_, 15);
v_detailed_133_ = lean_ctor_get(v_x_32_, 16);
v_useSorry_134_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 31);
v_revert_135_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 32);
v_funCC_136_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 33);
v_reducible_137_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 34);
v_maxSuggestions_138_ = lean_ctor_get(v_x_32_, 17);
if (v_trace_86_ == 0)
{
if (v_trace_33_ == 0)
{
goto v___jp_191_;
}
else
{
return v_trace_86_;
}
}
else
{
if (v_trace_33_ == 0)
{
return v_trace_33_;
}
else
{
goto v___jp_191_;
}
}
v___jp_139_:
{
if (v_reducible_137_ == 0)
{
if (v_reducible_84_ == 0)
{
uint8_t v___x_140_; 
v___x_140_ = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_maxSuggestions_85_, v_maxSuggestions_138_);
return v___x_140_;
}
else
{
return v_reducible_137_;
}
}
else
{
if (v_reducible_84_ == 0)
{
return v_reducible_84_;
}
else
{
uint8_t v___x_141_; 
v___x_141_ = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_maxSuggestions_85_, v_maxSuggestions_138_);
return v___x_141_;
}
}
}
v___jp_142_:
{
if (v_funCC_136_ == 0)
{
if (v_funCC_83_ == 0)
{
goto v___jp_139_;
}
else
{
return v_funCC_136_;
}
}
else
{
if (v_funCC_83_ == 0)
{
return v_funCC_83_;
}
else
{
goto v___jp_139_;
}
}
}
v___jp_143_:
{
if (v_revert_135_ == 0)
{
if (v_revert_82_ == 0)
{
goto v___jp_142_;
}
else
{
return v_revert_135_;
}
}
else
{
if (v_revert_82_ == 0)
{
return v_revert_82_;
}
else
{
goto v___jp_142_;
}
}
}
v___jp_144_:
{
uint8_t v___x_145_; 
v___x_145_ = lean_nat_dec_eq(v_min_79_, v_min_132_);
if (v___x_145_ == 0)
{
return v___x_145_;
}
else
{
uint8_t v___x_146_; 
v___x_146_ = lean_nat_dec_eq(v_detailed_80_, v_detailed_133_);
if (v___x_146_ == 0)
{
return v___x_146_;
}
else
{
if (v_useSorry_134_ == 0)
{
if (v_useSorry_81_ == 0)
{
goto v___jp_143_;
}
else
{
return v_useSorry_134_;
}
}
else
{
if (v_useSorry_81_ == 0)
{
return v_useSorry_81_;
}
else
{
goto v___jp_143_;
}
}
}
}
}
v___jp_147_:
{
if (v_order_131_ == 0)
{
if (v_order_78_ == 0)
{
goto v___jp_144_;
}
else
{
return v_order_131_;
}
}
else
{
if (v_order_78_ == 0)
{
return v_order_78_;
}
else
{
goto v___jp_144_;
}
}
}
v___jp_148_:
{
if (v_inj_130_ == 0)
{
if (v_inj_77_ == 0)
{
goto v___jp_147_;
}
else
{
return v_inj_130_;
}
}
else
{
if (v_inj_77_ == 0)
{
return v_inj_77_;
}
else
{
goto v___jp_147_;
}
}
}
v___jp_149_:
{
uint8_t v___x_150_; 
v___x_150_ = lean_nat_dec_eq(v_acSteps_74_, v_acSteps_127_);
if (v___x_150_ == 0)
{
return v___x_150_;
}
else
{
uint8_t v___x_151_; 
v___x_151_ = lean_nat_dec_eq(v_exp_75_, v_exp_128_);
if (v___x_151_ == 0)
{
return v___x_151_;
}
else
{
if (v_abstractProof_129_ == 0)
{
if (v_abstractProof_76_ == 0)
{
goto v___jp_148_;
}
else
{
return v_abstractProof_129_;
}
}
else
{
if (v_abstractProof_76_ == 0)
{
return v_abstractProof_76_;
}
else
{
goto v___jp_148_;
}
}
}
}
}
v___jp_152_:
{
if (v_ac_126_ == 0)
{
if (v_ac_73_ == 0)
{
goto v___jp_149_;
}
else
{
return v_ac_126_;
}
}
else
{
if (v_ac_73_ == 0)
{
return v_ac_73_;
}
else
{
goto v___jp_149_;
}
}
}
v___jp_153_:
{
uint8_t v___x_154_; 
v___x_154_ = lean_nat_dec_eq(v_liaSteps_69_, v_liaSteps_122_);
if (v___x_154_ == 0)
{
return v___x_154_;
}
else
{
uint8_t v___x_155_; 
v___x_155_ = lean_nat_dec_eq(v_liaReorders_70_, v_liaReorders_123_);
if (v___x_155_ == 0)
{
return v___x_155_;
}
else
{
uint8_t v___x_156_; 
v___x_156_ = lean_nat_dec_eq(v_liaReorderCases_71_, v_liaReorderCases_124_);
if (v___x_156_ == 0)
{
return v___x_156_;
}
else
{
if (v_hom_125_ == 0)
{
if (v_hom_72_ == 0)
{
goto v___jp_152_;
}
else
{
return v_hom_125_;
}
}
else
{
if (v_hom_72_ == 0)
{
return v_hom_72_;
}
else
{
goto v___jp_152_;
}
}
}
}
}
}
v___jp_157_:
{
if (v_lia_121_ == 0)
{
if (v_lia_68_ == 0)
{
goto v___jp_153_;
}
else
{
return v_lia_121_;
}
}
else
{
if (v_lia_68_ == 0)
{
return v_lia_68_;
}
else
{
goto v___jp_153_;
}
}
}
v___jp_158_:
{
uint8_t v___x_159_; 
v___x_159_ = lean_nat_dec_eq(v_ringSteps_65_, v_ringSteps_118_);
if (v___x_159_ == 0)
{
return v___x_159_;
}
else
{
uint8_t v___x_160_; 
v___x_160_ = lean_nat_dec_eq(v_ringMaxDegree_66_, v_ringMaxDegree_119_);
if (v___x_160_ == 0)
{
return v___x_160_;
}
else
{
if (v_linarith_120_ == 0)
{
if (v_linarith_67_ == 0)
{
goto v___jp_157_;
}
else
{
return v_linarith_120_;
}
}
else
{
if (v_linarith_67_ == 0)
{
return v_linarith_67_;
}
else
{
goto v___jp_157_;
}
}
}
}
}
v___jp_161_:
{
uint8_t v___x_162_; 
v___x_162_ = lean_nat_dec_eq(v_maxChar_63_, v_maxChar_116_);
if (v___x_162_ == 0)
{
return v___x_162_;
}
else
{
if (v_ring_117_ == 0)
{
if (v_ring_64_ == 0)
{
goto v___jp_158_;
}
else
{
return v_ring_117_;
}
}
else
{
if (v_ring_64_ == 0)
{
return v_ring_64_;
}
else
{
goto v___jp_158_;
}
}
}
}
v___jp_163_:
{
if (v_distrib_115_ == 0)
{
if (v_distrib_62_ == 0)
{
goto v___jp_161_;
}
else
{
return v_distrib_115_;
}
}
else
{
if (v_distrib_62_ == 0)
{
return v_distrib_62_;
}
else
{
goto v___jp_161_;
}
}
}
v___jp_164_:
{
if (v_zeta_114_ == 0)
{
if (v_zeta_61_ == 0)
{
goto v___jp_163_;
}
else
{
return v_zeta_114_;
}
}
else
{
if (v_zeta_61_ == 0)
{
return v_zeta_61_;
}
else
{
goto v___jp_163_;
}
}
}
v___jp_165_:
{
if (v_zetaDelta_113_ == 0)
{
if (v_zetaDelta_60_ == 0)
{
goto v___jp_164_;
}
else
{
return v_zetaDelta_113_;
}
}
else
{
if (v_zetaDelta_60_ == 0)
{
return v_zetaDelta_60_;
}
else
{
goto v___jp_164_;
}
}
}
v___jp_166_:
{
if (v_mbtc_112_ == 0)
{
if (v_mbtc_59_ == 0)
{
goto v___jp_165_;
}
else
{
return v_mbtc_112_;
}
}
else
{
if (v_mbtc_59_ == 0)
{
return v_mbtc_59_;
}
else
{
goto v___jp_165_;
}
}
}
v___jp_167_:
{
if (v_qlia_111_ == 0)
{
if (v_qlia_58_ == 0)
{
goto v___jp_166_;
}
else
{
return v_qlia_111_;
}
}
else
{
if (v_qlia_58_ == 0)
{
return v_qlia_58_;
}
else
{
goto v___jp_166_;
}
}
}
v___jp_168_:
{
if (v_clean_110_ == 0)
{
if (v_clean_57_ == 0)
{
goto v___jp_167_;
}
else
{
return v_clean_110_;
}
}
else
{
if (v_clean_57_ == 0)
{
return v_clean_57_;
}
else
{
goto v___jp_167_;
}
}
}
v___jp_169_:
{
if (v_verbose_109_ == 0)
{
if (v_verbose_56_ == 0)
{
goto v___jp_168_;
}
else
{
return v_verbose_109_;
}
}
else
{
if (v_verbose_56_ == 0)
{
return v_verbose_56_;
}
else
{
goto v___jp_168_;
}
}
}
v___jp_170_:
{
if (v_lookahead_108_ == 0)
{
if (v_lookahead_55_ == 0)
{
goto v___jp_169_;
}
else
{
return v_lookahead_108_;
}
}
else
{
if (v_lookahead_55_ == 0)
{
return v_lookahead_55_;
}
else
{
goto v___jp_169_;
}
}
}
v___jp_171_:
{
if (v_funext_107_ == 0)
{
if (v_funext_54_ == 0)
{
goto v___jp_170_;
}
else
{
return v_funext_107_;
}
}
else
{
if (v_funext_54_ == 0)
{
return v_funext_54_;
}
else
{
goto v___jp_170_;
}
}
}
v___jp_172_:
{
if (v_etaStruct_106_ == 0)
{
if (v_etaStruct_53_ == 0)
{
goto v___jp_171_;
}
else
{
return v_etaStruct_106_;
}
}
else
{
if (v_etaStruct_53_ == 0)
{
return v_etaStruct_53_;
}
else
{
goto v___jp_171_;
}
}
}
v___jp_173_:
{
if (v_extAll_105_ == 0)
{
if (v_extAll_52_ == 0)
{
goto v___jp_172_;
}
else
{
return v_extAll_105_;
}
}
else
{
if (v_extAll_52_ == 0)
{
return v_extAll_52_;
}
else
{
goto v___jp_172_;
}
}
}
v___jp_174_:
{
uint8_t v___x_175_; 
v___x_175_ = lean_nat_dec_eq(v_canonHeartbeats_50_, v_canonHeartbeats_103_);
if (v___x_175_ == 0)
{
return v___x_175_;
}
else
{
if (v_ext_104_ == 0)
{
if (v_ext_51_ == 0)
{
goto v___jp_173_;
}
else
{
return v_ext_104_;
}
}
else
{
if (v_ext_51_ == 0)
{
return v_ext_51_;
}
else
{
goto v___jp_173_;
}
}
}
}
v___jp_176_:
{
if (v_filterFacts_102_ == 0)
{
if (v_filterFacts_49_ == 0)
{
goto v___jp_174_;
}
else
{
return v_filterFacts_102_;
}
}
else
{
if (v_filterFacts_49_ == 0)
{
return v_filterFacts_49_;
}
else
{
goto v___jp_174_;
}
}
}
v___jp_177_:
{
if (v_splitImp_101_ == 0)
{
if (v_splitImp_48_ == 0)
{
goto v___jp_176_;
}
else
{
return v_splitImp_101_;
}
}
else
{
if (v_splitImp_48_ == 0)
{
return v_splitImp_48_;
}
else
{
goto v___jp_176_;
}
}
}
v___jp_178_:
{
if (v_splitIndPred_100_ == 0)
{
if (v_splitIndPred_47_ == 0)
{
goto v___jp_177_;
}
else
{
return v_splitIndPred_100_;
}
}
else
{
if (v_splitIndPred_47_ == 0)
{
return v_splitIndPred_47_;
}
else
{
goto v___jp_177_;
}
}
}
v___jp_179_:
{
if (v_splitIte_99_ == 0)
{
if (v_splitIte_46_ == 0)
{
goto v___jp_178_;
}
else
{
return v_splitIte_99_;
}
}
else
{
if (v_splitIte_46_ == 0)
{
return v_splitIte_46_;
}
else
{
goto v___jp_178_;
}
}
}
v___jp_180_:
{
if (v_splitMatch_98_ == 0)
{
if (v_splitMatch_45_ == 0)
{
goto v___jp_179_;
}
else
{
return v_splitMatch_98_;
}
}
else
{
if (v_splitMatch_45_ == 0)
{
return v_splitMatch_45_;
}
else
{
goto v___jp_179_;
}
}
}
v___jp_181_:
{
uint8_t v___x_182_; 
v___x_182_ = lean_nat_dec_eq(v_branches_38_, v_branches_91_);
if (v___x_182_ == 0)
{
return v___x_182_;
}
else
{
uint8_t v___x_183_; 
v___x_183_ = lean_nat_dec_eq(v_splits_39_, v_splits_92_);
if (v___x_183_ == 0)
{
return v___x_183_;
}
else
{
uint8_t v___x_184_; 
v___x_184_ = lean_nat_dec_eq(v_ematch_40_, v_ematch_93_);
if (v___x_184_ == 0)
{
return v___x_184_;
}
else
{
uint8_t v___x_185_; 
v___x_185_ = lean_nat_dec_eq(v_gen_41_, v_gen_94_);
if (v___x_185_ == 0)
{
return v___x_185_;
}
else
{
uint8_t v___x_186_; 
v___x_186_ = lean_nat_dec_eq(v_genLocal_42_, v_genLocal_95_);
if (v___x_186_ == 0)
{
return v___x_186_;
}
else
{
uint8_t v___x_187_; 
v___x_187_ = lean_nat_dec_eq(v_instances_43_, v_instances_96_);
if (v___x_187_ == 0)
{
return v___x_187_;
}
else
{
if (v_matchEqs_97_ == 0)
{
if (v_matchEqs_44_ == 0)
{
goto v___jp_180_;
}
else
{
return v_matchEqs_97_;
}
}
else
{
if (v_matchEqs_44_ == 0)
{
return v_matchEqs_44_;
}
else
{
goto v___jp_180_;
}
}
}
}
}
}
}
}
}
v___jp_188_:
{
if (v_locals_90_ == 0)
{
if (v_locals_37_ == 0)
{
goto v___jp_181_;
}
else
{
return v_locals_90_;
}
}
else
{
if (v_locals_37_ == 0)
{
return v_locals_37_;
}
else
{
goto v___jp_181_;
}
}
}
v___jp_189_:
{
if (v_suggestions_89_ == 0)
{
if (v_suggestions_36_ == 0)
{
goto v___jp_188_;
}
else
{
return v_suggestions_89_;
}
}
else
{
if (v_suggestions_36_ == 0)
{
return v_suggestions_36_;
}
else
{
goto v___jp_188_;
}
}
}
v___jp_190_:
{
if (v_lax_88_ == 0)
{
if (v_lax_35_ == 0)
{
goto v___jp_189_;
}
else
{
return v_lax_88_;
}
}
else
{
if (v_lax_35_ == 0)
{
return v_lax_35_;
}
else
{
goto v___jp_189_;
}
}
}
v___jp_191_:
{
if (v_markInstances_87_ == 0)
{
if (v_markInstances_34_ == 0)
{
goto v___jp_190_;
}
else
{
return v_markInstances_87_;
}
}
else
{
if (v_markInstances_34_ == 0)
{
return v_markInstances_34_;
}
else
{
goto v___jp_190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instBEqConfig_beq___boxed(lean_object* v_x_192_, lean_object* v_x_193_){
_start:
{
uint8_t v_res_194_; lean_object* v_r_195_; 
v_res_194_ = l_Lean_Grind_instBEqConfig_beq(v_x_192_, v_x_193_);
lean_dec_ref(v_x_193_);
lean_dec_ref(v_x_192_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
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
