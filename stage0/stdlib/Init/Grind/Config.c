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
static const lean_ctor_object l_Lean_Grind_instInhabitedConfig_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*18 + 40, .m_other = 18, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(9) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(10000) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(16) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1048576) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 1, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 1, 1, 0, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 1, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
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
uint8_t v_trace_33_; uint8_t v_markInstances_34_; uint8_t v_lax_35_; uint8_t v_suggestions_36_; uint8_t v_locals_37_; lean_object* v_branches_38_; lean_object* v_splits_39_; lean_object* v_ematch_40_; lean_object* v_gen_41_; lean_object* v_genLocal_42_; lean_object* v_instances_43_; uint8_t v_matchEqs_44_; uint8_t v_splitMatch_45_; uint8_t v_splitIte_46_; uint8_t v_splitIndPred_47_; uint8_t v_splitImp_48_; lean_object* v_canonHeartbeats_49_; uint8_t v_ext_50_; uint8_t v_extAll_51_; uint8_t v_etaStruct_52_; uint8_t v_funext_53_; uint8_t v_lookahead_54_; uint8_t v_verbose_55_; uint8_t v_clean_56_; uint8_t v_qlia_57_; uint8_t v_mbtc_58_; uint8_t v_zetaDelta_59_; uint8_t v_zeta_60_; uint8_t v_distrib_61_; lean_object* v_maxChar_62_; uint8_t v_ring_63_; lean_object* v_ringSteps_64_; lean_object* v_ringMaxDegree_65_; uint8_t v_linarith_66_; uint8_t v_lia_67_; lean_object* v_liaSteps_68_; lean_object* v_liaReorders_69_; lean_object* v_liaReorderCases_70_; uint8_t v_hom_71_; uint8_t v_ac_72_; lean_object* v_acSteps_73_; lean_object* v_exp_74_; uint8_t v_abstractProof_75_; uint8_t v_inj_76_; uint8_t v_order_77_; lean_object* v_min_78_; lean_object* v_detailed_79_; uint8_t v_useSorry_80_; uint8_t v_revert_81_; uint8_t v_funCC_82_; uint8_t v_reducible_83_; lean_object* v_maxSuggestions_84_; uint8_t v_trace_85_; uint8_t v_markInstances_86_; uint8_t v_lax_87_; uint8_t v_suggestions_88_; uint8_t v_locals_89_; lean_object* v_branches_90_; lean_object* v_splits_91_; lean_object* v_ematch_92_; lean_object* v_gen_93_; lean_object* v_genLocal_94_; lean_object* v_instances_95_; uint8_t v_matchEqs_96_; uint8_t v_splitMatch_97_; uint8_t v_splitIte_98_; uint8_t v_splitIndPred_99_; uint8_t v_splitImp_100_; lean_object* v_canonHeartbeats_101_; uint8_t v_ext_102_; uint8_t v_extAll_103_; uint8_t v_etaStruct_104_; uint8_t v_funext_105_; uint8_t v_lookahead_106_; uint8_t v_verbose_107_; uint8_t v_clean_108_; uint8_t v_qlia_109_; uint8_t v_mbtc_110_; uint8_t v_zetaDelta_111_; uint8_t v_zeta_112_; uint8_t v_distrib_113_; lean_object* v_maxChar_114_; uint8_t v_ring_115_; lean_object* v_ringSteps_116_; lean_object* v_ringMaxDegree_117_; uint8_t v_linarith_118_; uint8_t v_lia_119_; lean_object* v_liaSteps_120_; lean_object* v_liaReorders_121_; lean_object* v_liaReorderCases_122_; uint8_t v_hom_123_; uint8_t v_ac_124_; lean_object* v_acSteps_125_; lean_object* v_exp_126_; uint8_t v_abstractProof_127_; uint8_t v_inj_128_; uint8_t v_order_129_; lean_object* v_min_130_; lean_object* v_detailed_131_; uint8_t v_useSorry_132_; uint8_t v_revert_133_; uint8_t v_funCC_134_; uint8_t v_reducible_135_; lean_object* v_maxSuggestions_136_; 
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
v_canonHeartbeats_49_ = lean_ctor_get(v_x_31_, 6);
v_ext_50_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 10);
v_extAll_51_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 11);
v_etaStruct_52_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 12);
v_funext_53_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 13);
v_lookahead_54_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 14);
v_verbose_55_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 15);
v_clean_56_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 16);
v_qlia_57_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 17);
v_mbtc_58_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 18);
v_zetaDelta_59_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 19);
v_zeta_60_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 20);
v_distrib_61_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 21);
v_maxChar_62_ = lean_ctor_get(v_x_31_, 7);
v_ring_63_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 22);
v_ringSteps_64_ = lean_ctor_get(v_x_31_, 8);
v_ringMaxDegree_65_ = lean_ctor_get(v_x_31_, 9);
v_linarith_66_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 23);
v_lia_67_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 24);
v_liaSteps_68_ = lean_ctor_get(v_x_31_, 10);
v_liaReorders_69_ = lean_ctor_get(v_x_31_, 11);
v_liaReorderCases_70_ = lean_ctor_get(v_x_31_, 12);
v_hom_71_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 25);
v_ac_72_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 26);
v_acSteps_73_ = lean_ctor_get(v_x_31_, 13);
v_exp_74_ = lean_ctor_get(v_x_31_, 14);
v_abstractProof_75_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 27);
v_inj_76_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 28);
v_order_77_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 29);
v_min_78_ = lean_ctor_get(v_x_31_, 15);
v_detailed_79_ = lean_ctor_get(v_x_31_, 16);
v_useSorry_80_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 30);
v_revert_81_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 31);
v_funCC_82_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 32);
v_reducible_83_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*18 + 33);
v_maxSuggestions_84_ = lean_ctor_get(v_x_31_, 17);
v_trace_85_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18);
v_markInstances_86_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 1);
v_lax_87_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 2);
v_suggestions_88_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 3);
v_locals_89_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 4);
v_branches_90_ = lean_ctor_get(v_x_32_, 0);
v_splits_91_ = lean_ctor_get(v_x_32_, 1);
v_ematch_92_ = lean_ctor_get(v_x_32_, 2);
v_gen_93_ = lean_ctor_get(v_x_32_, 3);
v_genLocal_94_ = lean_ctor_get(v_x_32_, 4);
v_instances_95_ = lean_ctor_get(v_x_32_, 5);
v_matchEqs_96_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 5);
v_splitMatch_97_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 6);
v_splitIte_98_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 7);
v_splitIndPred_99_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 8);
v_splitImp_100_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 9);
v_canonHeartbeats_101_ = lean_ctor_get(v_x_32_, 6);
v_ext_102_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 10);
v_extAll_103_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 11);
v_etaStruct_104_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 12);
v_funext_105_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 13);
v_lookahead_106_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 14);
v_verbose_107_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 15);
v_clean_108_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 16);
v_qlia_109_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 17);
v_mbtc_110_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 18);
v_zetaDelta_111_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 19);
v_zeta_112_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 20);
v_distrib_113_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 21);
v_maxChar_114_ = lean_ctor_get(v_x_32_, 7);
v_ring_115_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 22);
v_ringSteps_116_ = lean_ctor_get(v_x_32_, 8);
v_ringMaxDegree_117_ = lean_ctor_get(v_x_32_, 9);
v_linarith_118_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 23);
v_lia_119_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 24);
v_liaSteps_120_ = lean_ctor_get(v_x_32_, 10);
v_liaReorders_121_ = lean_ctor_get(v_x_32_, 11);
v_liaReorderCases_122_ = lean_ctor_get(v_x_32_, 12);
v_hom_123_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 25);
v_ac_124_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 26);
v_acSteps_125_ = lean_ctor_get(v_x_32_, 13);
v_exp_126_ = lean_ctor_get(v_x_32_, 14);
v_abstractProof_127_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 27);
v_inj_128_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 28);
v_order_129_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 29);
v_min_130_ = lean_ctor_get(v_x_32_, 15);
v_detailed_131_ = lean_ctor_get(v_x_32_, 16);
v_useSorry_132_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 30);
v_revert_133_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 31);
v_funCC_134_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 32);
v_reducible_135_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*18 + 33);
v_maxSuggestions_136_ = lean_ctor_get(v_x_32_, 17);
if (v_trace_85_ == 0)
{
if (v_trace_33_ == 0)
{
goto v___jp_188_;
}
else
{
return v_trace_85_;
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
goto v___jp_188_;
}
}
v___jp_137_:
{
if (v_reducible_135_ == 0)
{
if (v_reducible_83_ == 0)
{
uint8_t v___x_138_; 
v___x_138_ = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_maxSuggestions_84_, v_maxSuggestions_136_);
return v___x_138_;
}
else
{
return v_reducible_135_;
}
}
else
{
if (v_reducible_83_ == 0)
{
return v_reducible_83_;
}
else
{
uint8_t v___x_139_; 
v___x_139_ = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_maxSuggestions_84_, v_maxSuggestions_136_);
return v___x_139_;
}
}
}
v___jp_140_:
{
if (v_funCC_134_ == 0)
{
if (v_funCC_82_ == 0)
{
goto v___jp_137_;
}
else
{
return v_funCC_134_;
}
}
else
{
if (v_funCC_82_ == 0)
{
return v_funCC_82_;
}
else
{
goto v___jp_137_;
}
}
}
v___jp_141_:
{
if (v_revert_133_ == 0)
{
if (v_revert_81_ == 0)
{
goto v___jp_140_;
}
else
{
return v_revert_133_;
}
}
else
{
if (v_revert_81_ == 0)
{
return v_revert_81_;
}
else
{
goto v___jp_140_;
}
}
}
v___jp_142_:
{
uint8_t v___x_143_; 
v___x_143_ = lean_nat_dec_eq(v_min_78_, v_min_130_);
if (v___x_143_ == 0)
{
return v___x_143_;
}
else
{
uint8_t v___x_144_; 
v___x_144_ = lean_nat_dec_eq(v_detailed_79_, v_detailed_131_);
if (v___x_144_ == 0)
{
return v___x_144_;
}
else
{
if (v_useSorry_132_ == 0)
{
if (v_useSorry_80_ == 0)
{
goto v___jp_141_;
}
else
{
return v_useSorry_132_;
}
}
else
{
if (v_useSorry_80_ == 0)
{
return v_useSorry_80_;
}
else
{
goto v___jp_141_;
}
}
}
}
}
v___jp_145_:
{
if (v_order_129_ == 0)
{
if (v_order_77_ == 0)
{
goto v___jp_142_;
}
else
{
return v_order_129_;
}
}
else
{
if (v_order_77_ == 0)
{
return v_order_77_;
}
else
{
goto v___jp_142_;
}
}
}
v___jp_146_:
{
if (v_inj_128_ == 0)
{
if (v_inj_76_ == 0)
{
goto v___jp_145_;
}
else
{
return v_inj_128_;
}
}
else
{
if (v_inj_76_ == 0)
{
return v_inj_76_;
}
else
{
goto v___jp_145_;
}
}
}
v___jp_147_:
{
uint8_t v___x_148_; 
v___x_148_ = lean_nat_dec_eq(v_acSteps_73_, v_acSteps_125_);
if (v___x_148_ == 0)
{
return v___x_148_;
}
else
{
uint8_t v___x_149_; 
v___x_149_ = lean_nat_dec_eq(v_exp_74_, v_exp_126_);
if (v___x_149_ == 0)
{
return v___x_149_;
}
else
{
if (v_abstractProof_127_ == 0)
{
if (v_abstractProof_75_ == 0)
{
goto v___jp_146_;
}
else
{
return v_abstractProof_127_;
}
}
else
{
if (v_abstractProof_75_ == 0)
{
return v_abstractProof_75_;
}
else
{
goto v___jp_146_;
}
}
}
}
}
v___jp_150_:
{
if (v_ac_124_ == 0)
{
if (v_ac_72_ == 0)
{
goto v___jp_147_;
}
else
{
return v_ac_124_;
}
}
else
{
if (v_ac_72_ == 0)
{
return v_ac_72_;
}
else
{
goto v___jp_147_;
}
}
}
v___jp_151_:
{
uint8_t v___x_152_; 
v___x_152_ = lean_nat_dec_eq(v_liaSteps_68_, v_liaSteps_120_);
if (v___x_152_ == 0)
{
return v___x_152_;
}
else
{
uint8_t v___x_153_; 
v___x_153_ = lean_nat_dec_eq(v_liaReorders_69_, v_liaReorders_121_);
if (v___x_153_ == 0)
{
return v___x_153_;
}
else
{
uint8_t v___x_154_; 
v___x_154_ = lean_nat_dec_eq(v_liaReorderCases_70_, v_liaReorderCases_122_);
if (v___x_154_ == 0)
{
return v___x_154_;
}
else
{
if (v_hom_123_ == 0)
{
if (v_hom_71_ == 0)
{
goto v___jp_150_;
}
else
{
return v_hom_123_;
}
}
else
{
if (v_hom_71_ == 0)
{
return v_hom_71_;
}
else
{
goto v___jp_150_;
}
}
}
}
}
}
v___jp_155_:
{
if (v_lia_119_ == 0)
{
if (v_lia_67_ == 0)
{
goto v___jp_151_;
}
else
{
return v_lia_119_;
}
}
else
{
if (v_lia_67_ == 0)
{
return v_lia_67_;
}
else
{
goto v___jp_151_;
}
}
}
v___jp_156_:
{
uint8_t v___x_157_; 
v___x_157_ = lean_nat_dec_eq(v_ringSteps_64_, v_ringSteps_116_);
if (v___x_157_ == 0)
{
return v___x_157_;
}
else
{
uint8_t v___x_158_; 
v___x_158_ = lean_nat_dec_eq(v_ringMaxDegree_65_, v_ringMaxDegree_117_);
if (v___x_158_ == 0)
{
return v___x_158_;
}
else
{
if (v_linarith_118_ == 0)
{
if (v_linarith_66_ == 0)
{
goto v___jp_155_;
}
else
{
return v_linarith_118_;
}
}
else
{
if (v_linarith_66_ == 0)
{
return v_linarith_66_;
}
else
{
goto v___jp_155_;
}
}
}
}
}
v___jp_159_:
{
uint8_t v___x_160_; 
v___x_160_ = lean_nat_dec_eq(v_maxChar_62_, v_maxChar_114_);
if (v___x_160_ == 0)
{
return v___x_160_;
}
else
{
if (v_ring_115_ == 0)
{
if (v_ring_63_ == 0)
{
goto v___jp_156_;
}
else
{
return v_ring_115_;
}
}
else
{
if (v_ring_63_ == 0)
{
return v_ring_63_;
}
else
{
goto v___jp_156_;
}
}
}
}
v___jp_161_:
{
if (v_distrib_113_ == 0)
{
if (v_distrib_61_ == 0)
{
goto v___jp_159_;
}
else
{
return v_distrib_113_;
}
}
else
{
if (v_distrib_61_ == 0)
{
return v_distrib_61_;
}
else
{
goto v___jp_159_;
}
}
}
v___jp_162_:
{
if (v_zeta_112_ == 0)
{
if (v_zeta_60_ == 0)
{
goto v___jp_161_;
}
else
{
return v_zeta_112_;
}
}
else
{
if (v_zeta_60_ == 0)
{
return v_zeta_60_;
}
else
{
goto v___jp_161_;
}
}
}
v___jp_163_:
{
if (v_zetaDelta_111_ == 0)
{
if (v_zetaDelta_59_ == 0)
{
goto v___jp_162_;
}
else
{
return v_zetaDelta_111_;
}
}
else
{
if (v_zetaDelta_59_ == 0)
{
return v_zetaDelta_59_;
}
else
{
goto v___jp_162_;
}
}
}
v___jp_164_:
{
if (v_mbtc_110_ == 0)
{
if (v_mbtc_58_ == 0)
{
goto v___jp_163_;
}
else
{
return v_mbtc_110_;
}
}
else
{
if (v_mbtc_58_ == 0)
{
return v_mbtc_58_;
}
else
{
goto v___jp_163_;
}
}
}
v___jp_165_:
{
if (v_qlia_109_ == 0)
{
if (v_qlia_57_ == 0)
{
goto v___jp_164_;
}
else
{
return v_qlia_109_;
}
}
else
{
if (v_qlia_57_ == 0)
{
return v_qlia_57_;
}
else
{
goto v___jp_164_;
}
}
}
v___jp_166_:
{
if (v_clean_108_ == 0)
{
if (v_clean_56_ == 0)
{
goto v___jp_165_;
}
else
{
return v_clean_108_;
}
}
else
{
if (v_clean_56_ == 0)
{
return v_clean_56_;
}
else
{
goto v___jp_165_;
}
}
}
v___jp_167_:
{
if (v_verbose_107_ == 0)
{
if (v_verbose_55_ == 0)
{
goto v___jp_166_;
}
else
{
return v_verbose_107_;
}
}
else
{
if (v_verbose_55_ == 0)
{
return v_verbose_55_;
}
else
{
goto v___jp_166_;
}
}
}
v___jp_168_:
{
if (v_lookahead_106_ == 0)
{
if (v_lookahead_54_ == 0)
{
goto v___jp_167_;
}
else
{
return v_lookahead_106_;
}
}
else
{
if (v_lookahead_54_ == 0)
{
return v_lookahead_54_;
}
else
{
goto v___jp_167_;
}
}
}
v___jp_169_:
{
if (v_funext_105_ == 0)
{
if (v_funext_53_ == 0)
{
goto v___jp_168_;
}
else
{
return v_funext_105_;
}
}
else
{
if (v_funext_53_ == 0)
{
return v_funext_53_;
}
else
{
goto v___jp_168_;
}
}
}
v___jp_170_:
{
if (v_etaStruct_104_ == 0)
{
if (v_etaStruct_52_ == 0)
{
goto v___jp_169_;
}
else
{
return v_etaStruct_104_;
}
}
else
{
if (v_etaStruct_52_ == 0)
{
return v_etaStruct_52_;
}
else
{
goto v___jp_169_;
}
}
}
v___jp_171_:
{
if (v_extAll_103_ == 0)
{
if (v_extAll_51_ == 0)
{
goto v___jp_170_;
}
else
{
return v_extAll_103_;
}
}
else
{
if (v_extAll_51_ == 0)
{
return v_extAll_51_;
}
else
{
goto v___jp_170_;
}
}
}
v___jp_172_:
{
uint8_t v___x_173_; 
v___x_173_ = lean_nat_dec_eq(v_canonHeartbeats_49_, v_canonHeartbeats_101_);
if (v___x_173_ == 0)
{
return v___x_173_;
}
else
{
if (v_ext_102_ == 0)
{
if (v_ext_50_ == 0)
{
goto v___jp_171_;
}
else
{
return v_ext_102_;
}
}
else
{
if (v_ext_50_ == 0)
{
return v_ext_50_;
}
else
{
goto v___jp_171_;
}
}
}
}
v___jp_174_:
{
if (v_splitImp_100_ == 0)
{
if (v_splitImp_48_ == 0)
{
goto v___jp_172_;
}
else
{
return v_splitImp_100_;
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
goto v___jp_172_;
}
}
}
v___jp_175_:
{
if (v_splitIndPred_99_ == 0)
{
if (v_splitIndPred_47_ == 0)
{
goto v___jp_174_;
}
else
{
return v_splitIndPred_99_;
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
goto v___jp_174_;
}
}
}
v___jp_176_:
{
if (v_splitIte_98_ == 0)
{
if (v_splitIte_46_ == 0)
{
goto v___jp_175_;
}
else
{
return v_splitIte_98_;
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
goto v___jp_175_;
}
}
}
v___jp_177_:
{
if (v_splitMatch_97_ == 0)
{
if (v_splitMatch_45_ == 0)
{
goto v___jp_176_;
}
else
{
return v_splitMatch_97_;
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
goto v___jp_176_;
}
}
}
v___jp_178_:
{
uint8_t v___x_179_; 
v___x_179_ = lean_nat_dec_eq(v_branches_38_, v_branches_90_);
if (v___x_179_ == 0)
{
return v___x_179_;
}
else
{
uint8_t v___x_180_; 
v___x_180_ = lean_nat_dec_eq(v_splits_39_, v_splits_91_);
if (v___x_180_ == 0)
{
return v___x_180_;
}
else
{
uint8_t v___x_181_; 
v___x_181_ = lean_nat_dec_eq(v_ematch_40_, v_ematch_92_);
if (v___x_181_ == 0)
{
return v___x_181_;
}
else
{
uint8_t v___x_182_; 
v___x_182_ = lean_nat_dec_eq(v_gen_41_, v_gen_93_);
if (v___x_182_ == 0)
{
return v___x_182_;
}
else
{
uint8_t v___x_183_; 
v___x_183_ = lean_nat_dec_eq(v_genLocal_42_, v_genLocal_94_);
if (v___x_183_ == 0)
{
return v___x_183_;
}
else
{
uint8_t v___x_184_; 
v___x_184_ = lean_nat_dec_eq(v_instances_43_, v_instances_95_);
if (v___x_184_ == 0)
{
return v___x_184_;
}
else
{
if (v_matchEqs_96_ == 0)
{
if (v_matchEqs_44_ == 0)
{
goto v___jp_177_;
}
else
{
return v_matchEqs_96_;
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
goto v___jp_177_;
}
}
}
}
}
}
}
}
}
v___jp_185_:
{
if (v_locals_89_ == 0)
{
if (v_locals_37_ == 0)
{
goto v___jp_178_;
}
else
{
return v_locals_89_;
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
goto v___jp_178_;
}
}
}
v___jp_186_:
{
if (v_suggestions_88_ == 0)
{
if (v_suggestions_36_ == 0)
{
goto v___jp_185_;
}
else
{
return v_suggestions_88_;
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
goto v___jp_185_;
}
}
}
v___jp_187_:
{
if (v_lax_87_ == 0)
{
if (v_lax_35_ == 0)
{
goto v___jp_186_;
}
else
{
return v_lax_87_;
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
goto v___jp_186_;
}
}
}
v___jp_188_:
{
if (v_markInstances_86_ == 0)
{
if (v_markInstances_34_ == 0)
{
goto v___jp_187_;
}
else
{
return v_markInstances_86_;
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
goto v___jp_187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instBEqConfig_beq___boxed(lean_object* v_x_189_, lean_object* v_x_190_){
_start:
{
uint8_t v_res_191_; lean_object* v_r_192_; 
v_res_191_ = l_Lean_Grind_instBEqConfig_beq(v_x_189_, v_x_190_);
lean_dec_ref(v_x_190_);
lean_dec_ref(v_x_189_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
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
