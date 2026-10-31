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
static const lean_ctor_object l_Lean_Grind_instInhabitedConfig_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*17 + 40, .m_other = 17, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(10000) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(16) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1048576) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 1, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 1, 1, 0, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 1, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
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
uint8_t v_trace_33_; uint8_t v_markInstances_34_; uint8_t v_lax_35_; uint8_t v_suggestions_36_; uint8_t v_locals_37_; lean_object* v_splits_38_; lean_object* v_ematch_39_; lean_object* v_gen_40_; lean_object* v_genLocal_41_; lean_object* v_instances_42_; uint8_t v_matchEqs_43_; uint8_t v_splitMatch_44_; uint8_t v_splitIte_45_; uint8_t v_splitIndPred_46_; uint8_t v_splitImp_47_; lean_object* v_canonHeartbeats_48_; uint8_t v_ext_49_; uint8_t v_extAll_50_; uint8_t v_etaStruct_51_; uint8_t v_funext_52_; uint8_t v_lookahead_53_; uint8_t v_verbose_54_; uint8_t v_clean_55_; uint8_t v_qlia_56_; uint8_t v_mbtc_57_; uint8_t v_zetaDelta_58_; uint8_t v_zeta_59_; uint8_t v_distrib_60_; lean_object* v_maxChar_61_; uint8_t v_ring_62_; lean_object* v_ringSteps_63_; lean_object* v_ringMaxDegree_64_; uint8_t v_linarith_65_; uint8_t v_lia_66_; lean_object* v_liaSteps_67_; lean_object* v_liaReorders_68_; lean_object* v_liaReorderCases_69_; uint8_t v_hom_70_; uint8_t v_ac_71_; lean_object* v_acSteps_72_; lean_object* v_exp_73_; uint8_t v_abstractProof_74_; uint8_t v_inj_75_; uint8_t v_order_76_; lean_object* v_min_77_; lean_object* v_detailed_78_; uint8_t v_useSorry_79_; uint8_t v_revert_80_; uint8_t v_funCC_81_; uint8_t v_reducible_82_; lean_object* v_maxSuggestions_83_; uint8_t v_trace_84_; uint8_t v_markInstances_85_; uint8_t v_lax_86_; uint8_t v_suggestions_87_; uint8_t v_locals_88_; lean_object* v_splits_89_; lean_object* v_ematch_90_; lean_object* v_gen_91_; lean_object* v_genLocal_92_; lean_object* v_instances_93_; uint8_t v_matchEqs_94_; uint8_t v_splitMatch_95_; uint8_t v_splitIte_96_; uint8_t v_splitIndPred_97_; uint8_t v_splitImp_98_; lean_object* v_canonHeartbeats_99_; uint8_t v_ext_100_; uint8_t v_extAll_101_; uint8_t v_etaStruct_102_; uint8_t v_funext_103_; uint8_t v_lookahead_104_; uint8_t v_verbose_105_; uint8_t v_clean_106_; uint8_t v_qlia_107_; uint8_t v_mbtc_108_; uint8_t v_zetaDelta_109_; uint8_t v_zeta_110_; uint8_t v_distrib_111_; lean_object* v_maxChar_112_; uint8_t v_ring_113_; lean_object* v_ringSteps_114_; lean_object* v_ringMaxDegree_115_; uint8_t v_linarith_116_; uint8_t v_lia_117_; lean_object* v_liaSteps_118_; lean_object* v_liaReorders_119_; lean_object* v_liaReorderCases_120_; uint8_t v_hom_121_; uint8_t v_ac_122_; lean_object* v_acSteps_123_; lean_object* v_exp_124_; uint8_t v_abstractProof_125_; uint8_t v_inj_126_; uint8_t v_order_127_; lean_object* v_min_128_; lean_object* v_detailed_129_; uint8_t v_useSorry_130_; uint8_t v_revert_131_; uint8_t v_funCC_132_; uint8_t v_reducible_133_; lean_object* v_maxSuggestions_134_; 
v_trace_33_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17);
v_markInstances_34_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 1);
v_lax_35_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 2);
v_suggestions_36_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 3);
v_locals_37_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 4);
v_splits_38_ = lean_ctor_get(v_x_31_, 0);
v_ematch_39_ = lean_ctor_get(v_x_31_, 1);
v_gen_40_ = lean_ctor_get(v_x_31_, 2);
v_genLocal_41_ = lean_ctor_get(v_x_31_, 3);
v_instances_42_ = lean_ctor_get(v_x_31_, 4);
v_matchEqs_43_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 5);
v_splitMatch_44_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 6);
v_splitIte_45_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 7);
v_splitIndPred_46_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 8);
v_splitImp_47_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 9);
v_canonHeartbeats_48_ = lean_ctor_get(v_x_31_, 5);
v_ext_49_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 10);
v_extAll_50_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 11);
v_etaStruct_51_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 12);
v_funext_52_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 13);
v_lookahead_53_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 14);
v_verbose_54_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 15);
v_clean_55_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 16);
v_qlia_56_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 17);
v_mbtc_57_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 18);
v_zetaDelta_58_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 19);
v_zeta_59_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 20);
v_distrib_60_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 21);
v_maxChar_61_ = lean_ctor_get(v_x_31_, 6);
v_ring_62_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 22);
v_ringSteps_63_ = lean_ctor_get(v_x_31_, 7);
v_ringMaxDegree_64_ = lean_ctor_get(v_x_31_, 8);
v_linarith_65_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 23);
v_lia_66_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 24);
v_liaSteps_67_ = lean_ctor_get(v_x_31_, 9);
v_liaReorders_68_ = lean_ctor_get(v_x_31_, 10);
v_liaReorderCases_69_ = lean_ctor_get(v_x_31_, 11);
v_hom_70_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 25);
v_ac_71_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 26);
v_acSteps_72_ = lean_ctor_get(v_x_31_, 12);
v_exp_73_ = lean_ctor_get(v_x_31_, 13);
v_abstractProof_74_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 27);
v_inj_75_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 28);
v_order_76_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 29);
v_min_77_ = lean_ctor_get(v_x_31_, 14);
v_detailed_78_ = lean_ctor_get(v_x_31_, 15);
v_useSorry_79_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 30);
v_revert_80_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 31);
v_funCC_81_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 32);
v_reducible_82_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*17 + 33);
v_maxSuggestions_83_ = lean_ctor_get(v_x_31_, 16);
v_trace_84_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17);
v_markInstances_85_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 1);
v_lax_86_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 2);
v_suggestions_87_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 3);
v_locals_88_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 4);
v_splits_89_ = lean_ctor_get(v_x_32_, 0);
v_ematch_90_ = lean_ctor_get(v_x_32_, 1);
v_gen_91_ = lean_ctor_get(v_x_32_, 2);
v_genLocal_92_ = lean_ctor_get(v_x_32_, 3);
v_instances_93_ = lean_ctor_get(v_x_32_, 4);
v_matchEqs_94_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 5);
v_splitMatch_95_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 6);
v_splitIte_96_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 7);
v_splitIndPred_97_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 8);
v_splitImp_98_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 9);
v_canonHeartbeats_99_ = lean_ctor_get(v_x_32_, 5);
v_ext_100_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 10);
v_extAll_101_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 11);
v_etaStruct_102_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 12);
v_funext_103_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 13);
v_lookahead_104_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 14);
v_verbose_105_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 15);
v_clean_106_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 16);
v_qlia_107_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 17);
v_mbtc_108_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 18);
v_zetaDelta_109_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 19);
v_zeta_110_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 20);
v_distrib_111_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 21);
v_maxChar_112_ = lean_ctor_get(v_x_32_, 6);
v_ring_113_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 22);
v_ringSteps_114_ = lean_ctor_get(v_x_32_, 7);
v_ringMaxDegree_115_ = lean_ctor_get(v_x_32_, 8);
v_linarith_116_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 23);
v_lia_117_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 24);
v_liaSteps_118_ = lean_ctor_get(v_x_32_, 9);
v_liaReorders_119_ = lean_ctor_get(v_x_32_, 10);
v_liaReorderCases_120_ = lean_ctor_get(v_x_32_, 11);
v_hom_121_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 25);
v_ac_122_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 26);
v_acSteps_123_ = lean_ctor_get(v_x_32_, 12);
v_exp_124_ = lean_ctor_get(v_x_32_, 13);
v_abstractProof_125_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 27);
v_inj_126_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 28);
v_order_127_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 29);
v_min_128_ = lean_ctor_get(v_x_32_, 14);
v_detailed_129_ = lean_ctor_get(v_x_32_, 15);
v_useSorry_130_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 30);
v_revert_131_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 31);
v_funCC_132_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 32);
v_reducible_133_ = lean_ctor_get_uint8(v_x_32_, sizeof(void*)*17 + 33);
v_maxSuggestions_134_ = lean_ctor_get(v_x_32_, 16);
if (v_trace_84_ == 0)
{
if (v_trace_33_ == 0)
{
goto v___jp_185_;
}
else
{
return v_trace_84_;
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
goto v___jp_185_;
}
}
v___jp_135_:
{
if (v_reducible_133_ == 0)
{
if (v_reducible_82_ == 0)
{
uint8_t v___x_136_; 
v___x_136_ = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_maxSuggestions_83_, v_maxSuggestions_134_);
return v___x_136_;
}
else
{
return v_reducible_133_;
}
}
else
{
if (v_reducible_82_ == 0)
{
return v_reducible_82_;
}
else
{
uint8_t v___x_137_; 
v___x_137_ = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_maxSuggestions_83_, v_maxSuggestions_134_);
return v___x_137_;
}
}
}
v___jp_138_:
{
if (v_funCC_132_ == 0)
{
if (v_funCC_81_ == 0)
{
goto v___jp_135_;
}
else
{
return v_funCC_132_;
}
}
else
{
if (v_funCC_81_ == 0)
{
return v_funCC_81_;
}
else
{
goto v___jp_135_;
}
}
}
v___jp_139_:
{
if (v_revert_131_ == 0)
{
if (v_revert_80_ == 0)
{
goto v___jp_138_;
}
else
{
return v_revert_131_;
}
}
else
{
if (v_revert_80_ == 0)
{
return v_revert_80_;
}
else
{
goto v___jp_138_;
}
}
}
v___jp_140_:
{
uint8_t v___x_141_; 
v___x_141_ = lean_nat_dec_eq(v_min_77_, v_min_128_);
if (v___x_141_ == 0)
{
return v___x_141_;
}
else
{
uint8_t v___x_142_; 
v___x_142_ = lean_nat_dec_eq(v_detailed_78_, v_detailed_129_);
if (v___x_142_ == 0)
{
return v___x_142_;
}
else
{
if (v_useSorry_130_ == 0)
{
if (v_useSorry_79_ == 0)
{
goto v___jp_139_;
}
else
{
return v_useSorry_130_;
}
}
else
{
if (v_useSorry_79_ == 0)
{
return v_useSorry_79_;
}
else
{
goto v___jp_139_;
}
}
}
}
}
v___jp_143_:
{
if (v_order_127_ == 0)
{
if (v_order_76_ == 0)
{
goto v___jp_140_;
}
else
{
return v_order_127_;
}
}
else
{
if (v_order_76_ == 0)
{
return v_order_76_;
}
else
{
goto v___jp_140_;
}
}
}
v___jp_144_:
{
if (v_inj_126_ == 0)
{
if (v_inj_75_ == 0)
{
goto v___jp_143_;
}
else
{
return v_inj_126_;
}
}
else
{
if (v_inj_75_ == 0)
{
return v_inj_75_;
}
else
{
goto v___jp_143_;
}
}
}
v___jp_145_:
{
uint8_t v___x_146_; 
v___x_146_ = lean_nat_dec_eq(v_acSteps_72_, v_acSteps_123_);
if (v___x_146_ == 0)
{
return v___x_146_;
}
else
{
uint8_t v___x_147_; 
v___x_147_ = lean_nat_dec_eq(v_exp_73_, v_exp_124_);
if (v___x_147_ == 0)
{
return v___x_147_;
}
else
{
if (v_abstractProof_125_ == 0)
{
if (v_abstractProof_74_ == 0)
{
goto v___jp_144_;
}
else
{
return v_abstractProof_125_;
}
}
else
{
if (v_abstractProof_74_ == 0)
{
return v_abstractProof_74_;
}
else
{
goto v___jp_144_;
}
}
}
}
}
v___jp_148_:
{
if (v_ac_122_ == 0)
{
if (v_ac_71_ == 0)
{
goto v___jp_145_;
}
else
{
return v_ac_122_;
}
}
else
{
if (v_ac_71_ == 0)
{
return v_ac_71_;
}
else
{
goto v___jp_145_;
}
}
}
v___jp_149_:
{
uint8_t v___x_150_; 
v___x_150_ = lean_nat_dec_eq(v_liaSteps_67_, v_liaSteps_118_);
if (v___x_150_ == 0)
{
return v___x_150_;
}
else
{
uint8_t v___x_151_; 
v___x_151_ = lean_nat_dec_eq(v_liaReorders_68_, v_liaReorders_119_);
if (v___x_151_ == 0)
{
return v___x_151_;
}
else
{
uint8_t v___x_152_; 
v___x_152_ = lean_nat_dec_eq(v_liaReorderCases_69_, v_liaReorderCases_120_);
if (v___x_152_ == 0)
{
return v___x_152_;
}
else
{
if (v_hom_121_ == 0)
{
if (v_hom_70_ == 0)
{
goto v___jp_148_;
}
else
{
return v_hom_121_;
}
}
else
{
if (v_hom_70_ == 0)
{
return v_hom_70_;
}
else
{
goto v___jp_148_;
}
}
}
}
}
}
v___jp_153_:
{
if (v_lia_117_ == 0)
{
if (v_lia_66_ == 0)
{
goto v___jp_149_;
}
else
{
return v_lia_117_;
}
}
else
{
if (v_lia_66_ == 0)
{
return v_lia_66_;
}
else
{
goto v___jp_149_;
}
}
}
v___jp_154_:
{
uint8_t v___x_155_; 
v___x_155_ = lean_nat_dec_eq(v_ringSteps_63_, v_ringSteps_114_);
if (v___x_155_ == 0)
{
return v___x_155_;
}
else
{
uint8_t v___x_156_; 
v___x_156_ = lean_nat_dec_eq(v_ringMaxDegree_64_, v_ringMaxDegree_115_);
if (v___x_156_ == 0)
{
return v___x_156_;
}
else
{
if (v_linarith_116_ == 0)
{
if (v_linarith_65_ == 0)
{
goto v___jp_153_;
}
else
{
return v_linarith_116_;
}
}
else
{
if (v_linarith_65_ == 0)
{
return v_linarith_65_;
}
else
{
goto v___jp_153_;
}
}
}
}
}
v___jp_157_:
{
uint8_t v___x_158_; 
v___x_158_ = lean_nat_dec_eq(v_maxChar_61_, v_maxChar_112_);
if (v___x_158_ == 0)
{
return v___x_158_;
}
else
{
if (v_ring_113_ == 0)
{
if (v_ring_62_ == 0)
{
goto v___jp_154_;
}
else
{
return v_ring_113_;
}
}
else
{
if (v_ring_62_ == 0)
{
return v_ring_62_;
}
else
{
goto v___jp_154_;
}
}
}
}
v___jp_159_:
{
if (v_distrib_111_ == 0)
{
if (v_distrib_60_ == 0)
{
goto v___jp_157_;
}
else
{
return v_distrib_111_;
}
}
else
{
if (v_distrib_60_ == 0)
{
return v_distrib_60_;
}
else
{
goto v___jp_157_;
}
}
}
v___jp_160_:
{
if (v_zeta_110_ == 0)
{
if (v_zeta_59_ == 0)
{
goto v___jp_159_;
}
else
{
return v_zeta_110_;
}
}
else
{
if (v_zeta_59_ == 0)
{
return v_zeta_59_;
}
else
{
goto v___jp_159_;
}
}
}
v___jp_161_:
{
if (v_zetaDelta_109_ == 0)
{
if (v_zetaDelta_58_ == 0)
{
goto v___jp_160_;
}
else
{
return v_zetaDelta_109_;
}
}
else
{
if (v_zetaDelta_58_ == 0)
{
return v_zetaDelta_58_;
}
else
{
goto v___jp_160_;
}
}
}
v___jp_162_:
{
if (v_mbtc_108_ == 0)
{
if (v_mbtc_57_ == 0)
{
goto v___jp_161_;
}
else
{
return v_mbtc_108_;
}
}
else
{
if (v_mbtc_57_ == 0)
{
return v_mbtc_57_;
}
else
{
goto v___jp_161_;
}
}
}
v___jp_163_:
{
if (v_qlia_107_ == 0)
{
if (v_qlia_56_ == 0)
{
goto v___jp_162_;
}
else
{
return v_qlia_107_;
}
}
else
{
if (v_qlia_56_ == 0)
{
return v_qlia_56_;
}
else
{
goto v___jp_162_;
}
}
}
v___jp_164_:
{
if (v_clean_106_ == 0)
{
if (v_clean_55_ == 0)
{
goto v___jp_163_;
}
else
{
return v_clean_106_;
}
}
else
{
if (v_clean_55_ == 0)
{
return v_clean_55_;
}
else
{
goto v___jp_163_;
}
}
}
v___jp_165_:
{
if (v_verbose_105_ == 0)
{
if (v_verbose_54_ == 0)
{
goto v___jp_164_;
}
else
{
return v_verbose_105_;
}
}
else
{
if (v_verbose_54_ == 0)
{
return v_verbose_54_;
}
else
{
goto v___jp_164_;
}
}
}
v___jp_166_:
{
if (v_lookahead_104_ == 0)
{
if (v_lookahead_53_ == 0)
{
goto v___jp_165_;
}
else
{
return v_lookahead_104_;
}
}
else
{
if (v_lookahead_53_ == 0)
{
return v_lookahead_53_;
}
else
{
goto v___jp_165_;
}
}
}
v___jp_167_:
{
if (v_funext_103_ == 0)
{
if (v_funext_52_ == 0)
{
goto v___jp_166_;
}
else
{
return v_funext_103_;
}
}
else
{
if (v_funext_52_ == 0)
{
return v_funext_52_;
}
else
{
goto v___jp_166_;
}
}
}
v___jp_168_:
{
if (v_etaStruct_102_ == 0)
{
if (v_etaStruct_51_ == 0)
{
goto v___jp_167_;
}
else
{
return v_etaStruct_102_;
}
}
else
{
if (v_etaStruct_51_ == 0)
{
return v_etaStruct_51_;
}
else
{
goto v___jp_167_;
}
}
}
v___jp_169_:
{
if (v_extAll_101_ == 0)
{
if (v_extAll_50_ == 0)
{
goto v___jp_168_;
}
else
{
return v_extAll_101_;
}
}
else
{
if (v_extAll_50_ == 0)
{
return v_extAll_50_;
}
else
{
goto v___jp_168_;
}
}
}
v___jp_170_:
{
uint8_t v___x_171_; 
v___x_171_ = lean_nat_dec_eq(v_canonHeartbeats_48_, v_canonHeartbeats_99_);
if (v___x_171_ == 0)
{
return v___x_171_;
}
else
{
if (v_ext_100_ == 0)
{
if (v_ext_49_ == 0)
{
goto v___jp_169_;
}
else
{
return v_ext_100_;
}
}
else
{
if (v_ext_49_ == 0)
{
return v_ext_49_;
}
else
{
goto v___jp_169_;
}
}
}
}
v___jp_172_:
{
if (v_splitImp_98_ == 0)
{
if (v_splitImp_47_ == 0)
{
goto v___jp_170_;
}
else
{
return v_splitImp_98_;
}
}
else
{
if (v_splitImp_47_ == 0)
{
return v_splitImp_47_;
}
else
{
goto v___jp_170_;
}
}
}
v___jp_173_:
{
if (v_splitIndPred_97_ == 0)
{
if (v_splitIndPred_46_ == 0)
{
goto v___jp_172_;
}
else
{
return v_splitIndPred_97_;
}
}
else
{
if (v_splitIndPred_46_ == 0)
{
return v_splitIndPred_46_;
}
else
{
goto v___jp_172_;
}
}
}
v___jp_174_:
{
if (v_splitIte_96_ == 0)
{
if (v_splitIte_45_ == 0)
{
goto v___jp_173_;
}
else
{
return v_splitIte_96_;
}
}
else
{
if (v_splitIte_45_ == 0)
{
return v_splitIte_45_;
}
else
{
goto v___jp_173_;
}
}
}
v___jp_175_:
{
if (v_splitMatch_95_ == 0)
{
if (v_splitMatch_44_ == 0)
{
goto v___jp_174_;
}
else
{
return v_splitMatch_95_;
}
}
else
{
if (v_splitMatch_44_ == 0)
{
return v_splitMatch_44_;
}
else
{
goto v___jp_174_;
}
}
}
v___jp_176_:
{
uint8_t v___x_177_; 
v___x_177_ = lean_nat_dec_eq(v_splits_38_, v_splits_89_);
if (v___x_177_ == 0)
{
return v___x_177_;
}
else
{
uint8_t v___x_178_; 
v___x_178_ = lean_nat_dec_eq(v_ematch_39_, v_ematch_90_);
if (v___x_178_ == 0)
{
return v___x_178_;
}
else
{
uint8_t v___x_179_; 
v___x_179_ = lean_nat_dec_eq(v_gen_40_, v_gen_91_);
if (v___x_179_ == 0)
{
return v___x_179_;
}
else
{
uint8_t v___x_180_; 
v___x_180_ = lean_nat_dec_eq(v_genLocal_41_, v_genLocal_92_);
if (v___x_180_ == 0)
{
return v___x_180_;
}
else
{
uint8_t v___x_181_; 
v___x_181_ = lean_nat_dec_eq(v_instances_42_, v_instances_93_);
if (v___x_181_ == 0)
{
return v___x_181_;
}
else
{
if (v_matchEqs_94_ == 0)
{
if (v_matchEqs_43_ == 0)
{
goto v___jp_175_;
}
else
{
return v_matchEqs_94_;
}
}
else
{
if (v_matchEqs_43_ == 0)
{
return v_matchEqs_43_;
}
else
{
goto v___jp_175_;
}
}
}
}
}
}
}
}
v___jp_182_:
{
if (v_locals_88_ == 0)
{
if (v_locals_37_ == 0)
{
goto v___jp_176_;
}
else
{
return v_locals_88_;
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
goto v___jp_176_;
}
}
}
v___jp_183_:
{
if (v_suggestions_87_ == 0)
{
if (v_suggestions_36_ == 0)
{
goto v___jp_182_;
}
else
{
return v_suggestions_87_;
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
goto v___jp_182_;
}
}
}
v___jp_184_:
{
if (v_lax_86_ == 0)
{
if (v_lax_35_ == 0)
{
goto v___jp_183_;
}
else
{
return v_lax_86_;
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
goto v___jp_183_;
}
}
}
v___jp_185_:
{
if (v_markInstances_85_ == 0)
{
if (v_markInstances_34_ == 0)
{
goto v___jp_184_;
}
else
{
return v_markInstances_85_;
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
goto v___jp_184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instBEqConfig_beq___boxed(lean_object* v_x_186_, lean_object* v_x_187_){
_start:
{
uint8_t v_res_188_; lean_object* v_r_189_; 
v_res_188_ = l_Lean_Grind_instBEqConfig_beq(v_x_186_, v_x_187_);
lean_dec_ref(v_x_187_);
lean_dec_ref(v_x_186_);
v_r_189_ = lean_box(v_res_188_);
return v_r_189_;
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
