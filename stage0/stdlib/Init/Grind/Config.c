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
static const lean_ctor_object l_Lean_Grind_instInhabitedConfig_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*15 + 40, .m_other = 15, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(10000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1048576) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 1, 1, 0, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 1, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(lean_object* v_x_18_, lean_object* v_x_19_){
_start:
{
if (lean_obj_tag(v_x_18_) == 0)
{
if (lean_obj_tag(v_x_19_) == 0)
{
uint8_t v___x_20_; 
v___x_20_ = 1;
return v___x_20_;
}
else
{
uint8_t v___x_21_; 
v___x_21_ = 0;
return v___x_21_;
}
}
else
{
if (lean_obj_tag(v_x_19_) == 0)
{
uint8_t v___x_22_; 
v___x_22_ = 0;
return v___x_22_;
}
else
{
lean_object* v_val_23_; lean_object* v_val_24_; uint8_t v___x_25_; 
v_val_23_ = lean_ctor_get(v_x_18_, 0);
v_val_24_ = lean_ctor_get(v_x_19_, 0);
v___x_25_ = lean_nat_dec_eq(v_val_23_, v_val_24_);
return v___x_25_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0___boxed(lean_object* v_x_26_, lean_object* v_x_27_){
_start:
{
uint8_t v_res_28_; lean_object* v_r_29_; 
v_res_28_ = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_x_26_, v_x_27_);
lean_dec(v_x_27_);
lean_dec(v_x_26_);
v_r_29_ = lean_box(v_res_28_);
return v_r_29_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_instBEqConfig_beq(lean_object* v_x_30_, lean_object* v_x_31_){
_start:
{
uint8_t v_trace_32_; uint8_t v_markInstances_33_; uint8_t v_lax_34_; uint8_t v_suggestions_35_; uint8_t v_locals_36_; lean_object* v_splits_37_; lean_object* v_ematch_38_; lean_object* v_gen_39_; lean_object* v_genLocal_40_; lean_object* v_instances_41_; uint8_t v_matchEqs_42_; uint8_t v_splitMatch_43_; uint8_t v_splitIte_44_; uint8_t v_splitIndPred_45_; uint8_t v_splitImp_46_; lean_object* v_canonHeartbeats_47_; uint8_t v_ext_48_; uint8_t v_extAll_49_; uint8_t v_etaStruct_50_; uint8_t v_funext_51_; uint8_t v_lookahead_52_; uint8_t v_verbose_53_; uint8_t v_clean_54_; uint8_t v_qlia_55_; uint8_t v_mbtc_56_; uint8_t v_zetaDelta_57_; uint8_t v_zeta_58_; uint8_t v_distrib_59_; lean_object* v_maxChar_60_; uint8_t v_ring_61_; lean_object* v_ringSteps_62_; lean_object* v_ringMaxDegree_63_; uint8_t v_linarith_64_; uint8_t v_lia_65_; lean_object* v_liaSteps_66_; uint8_t v_hom_67_; uint8_t v_ac_68_; lean_object* v_acSteps_69_; lean_object* v_exp_70_; uint8_t v_abstractProof_71_; uint8_t v_inj_72_; uint8_t v_order_73_; lean_object* v_min_74_; lean_object* v_detailed_75_; uint8_t v_useSorry_76_; uint8_t v_revert_77_; uint8_t v_funCC_78_; uint8_t v_reducible_79_; lean_object* v_maxSuggestions_80_; uint8_t v_trace_81_; uint8_t v_markInstances_82_; uint8_t v_lax_83_; uint8_t v_suggestions_84_; uint8_t v_locals_85_; lean_object* v_splits_86_; lean_object* v_ematch_87_; lean_object* v_gen_88_; lean_object* v_genLocal_89_; lean_object* v_instances_90_; uint8_t v_matchEqs_91_; uint8_t v_splitMatch_92_; uint8_t v_splitIte_93_; uint8_t v_splitIndPred_94_; uint8_t v_splitImp_95_; lean_object* v_canonHeartbeats_96_; uint8_t v_ext_97_; uint8_t v_extAll_98_; uint8_t v_etaStruct_99_; uint8_t v_funext_100_; uint8_t v_lookahead_101_; uint8_t v_verbose_102_; uint8_t v_clean_103_; uint8_t v_qlia_104_; uint8_t v_mbtc_105_; uint8_t v_zetaDelta_106_; uint8_t v_zeta_107_; uint8_t v_distrib_108_; lean_object* v_maxChar_109_; uint8_t v_ring_110_; lean_object* v_ringSteps_111_; lean_object* v_ringMaxDegree_112_; uint8_t v_linarith_113_; uint8_t v_lia_114_; lean_object* v_liaSteps_115_; uint8_t v_hom_116_; uint8_t v_ac_117_; lean_object* v_acSteps_118_; lean_object* v_exp_119_; uint8_t v_abstractProof_120_; uint8_t v_inj_121_; uint8_t v_order_122_; lean_object* v_min_123_; lean_object* v_detailed_124_; uint8_t v_useSorry_125_; uint8_t v_revert_126_; uint8_t v_funCC_127_; uint8_t v_reducible_128_; lean_object* v_maxSuggestions_129_; 
v_trace_32_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15);
v_markInstances_33_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 1);
v_lax_34_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 2);
v_suggestions_35_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 3);
v_locals_36_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 4);
v_splits_37_ = lean_ctor_get(v_x_30_, 0);
v_ematch_38_ = lean_ctor_get(v_x_30_, 1);
v_gen_39_ = lean_ctor_get(v_x_30_, 2);
v_genLocal_40_ = lean_ctor_get(v_x_30_, 3);
v_instances_41_ = lean_ctor_get(v_x_30_, 4);
v_matchEqs_42_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 5);
v_splitMatch_43_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 6);
v_splitIte_44_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 7);
v_splitIndPred_45_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 8);
v_splitImp_46_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 9);
v_canonHeartbeats_47_ = lean_ctor_get(v_x_30_, 5);
v_ext_48_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 10);
v_extAll_49_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 11);
v_etaStruct_50_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 12);
v_funext_51_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 13);
v_lookahead_52_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 14);
v_verbose_53_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 15);
v_clean_54_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 16);
v_qlia_55_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 17);
v_mbtc_56_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 18);
v_zetaDelta_57_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 19);
v_zeta_58_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 20);
v_distrib_59_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 21);
v_maxChar_60_ = lean_ctor_get(v_x_30_, 6);
v_ring_61_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 22);
v_ringSteps_62_ = lean_ctor_get(v_x_30_, 7);
v_ringMaxDegree_63_ = lean_ctor_get(v_x_30_, 8);
v_linarith_64_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 23);
v_lia_65_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 24);
v_liaSteps_66_ = lean_ctor_get(v_x_30_, 9);
v_hom_67_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 25);
v_ac_68_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 26);
v_acSteps_69_ = lean_ctor_get(v_x_30_, 10);
v_exp_70_ = lean_ctor_get(v_x_30_, 11);
v_abstractProof_71_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 27);
v_inj_72_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 28);
v_order_73_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 29);
v_min_74_ = lean_ctor_get(v_x_30_, 12);
v_detailed_75_ = lean_ctor_get(v_x_30_, 13);
v_useSorry_76_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 30);
v_revert_77_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 31);
v_funCC_78_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 32);
v_reducible_79_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*15 + 33);
v_maxSuggestions_80_ = lean_ctor_get(v_x_30_, 14);
v_trace_81_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15);
v_markInstances_82_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 1);
v_lax_83_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 2);
v_suggestions_84_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 3);
v_locals_85_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 4);
v_splits_86_ = lean_ctor_get(v_x_31_, 0);
v_ematch_87_ = lean_ctor_get(v_x_31_, 1);
v_gen_88_ = lean_ctor_get(v_x_31_, 2);
v_genLocal_89_ = lean_ctor_get(v_x_31_, 3);
v_instances_90_ = lean_ctor_get(v_x_31_, 4);
v_matchEqs_91_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 5);
v_splitMatch_92_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 6);
v_splitIte_93_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 7);
v_splitIndPred_94_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 8);
v_splitImp_95_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 9);
v_canonHeartbeats_96_ = lean_ctor_get(v_x_31_, 5);
v_ext_97_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 10);
v_extAll_98_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 11);
v_etaStruct_99_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 12);
v_funext_100_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 13);
v_lookahead_101_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 14);
v_verbose_102_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 15);
v_clean_103_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 16);
v_qlia_104_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 17);
v_mbtc_105_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 18);
v_zetaDelta_106_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 19);
v_zeta_107_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 20);
v_distrib_108_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 21);
v_maxChar_109_ = lean_ctor_get(v_x_31_, 6);
v_ring_110_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 22);
v_ringSteps_111_ = lean_ctor_get(v_x_31_, 7);
v_ringMaxDegree_112_ = lean_ctor_get(v_x_31_, 8);
v_linarith_113_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 23);
v_lia_114_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 24);
v_liaSteps_115_ = lean_ctor_get(v_x_31_, 9);
v_hom_116_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 25);
v_ac_117_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 26);
v_acSteps_118_ = lean_ctor_get(v_x_31_, 10);
v_exp_119_ = lean_ctor_get(v_x_31_, 11);
v_abstractProof_120_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 27);
v_inj_121_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 28);
v_order_122_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 29);
v_min_123_ = lean_ctor_get(v_x_31_, 12);
v_detailed_124_ = lean_ctor_get(v_x_31_, 13);
v_useSorry_125_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 30);
v_revert_126_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 31);
v_funCC_127_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 32);
v_reducible_128_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*15 + 33);
v_maxSuggestions_129_ = lean_ctor_get(v_x_31_, 14);
if (v_trace_81_ == 0)
{
if (v_trace_32_ == 0)
{
goto v___jp_178_;
}
else
{
return v_trace_81_;
}
}
else
{
if (v_trace_32_ == 0)
{
return v_trace_32_;
}
else
{
goto v___jp_178_;
}
}
v___jp_130_:
{
if (v_reducible_128_ == 0)
{
if (v_reducible_79_ == 0)
{
uint8_t v___x_131_; 
v___x_131_ = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_maxSuggestions_80_, v_maxSuggestions_129_);
return v___x_131_;
}
else
{
return v_reducible_128_;
}
}
else
{
if (v_reducible_79_ == 0)
{
return v_reducible_79_;
}
else
{
uint8_t v___x_132_; 
v___x_132_ = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_maxSuggestions_80_, v_maxSuggestions_129_);
return v___x_132_;
}
}
}
v___jp_133_:
{
if (v_funCC_127_ == 0)
{
if (v_funCC_78_ == 0)
{
goto v___jp_130_;
}
else
{
return v_funCC_127_;
}
}
else
{
if (v_funCC_78_ == 0)
{
return v_funCC_78_;
}
else
{
goto v___jp_130_;
}
}
}
v___jp_134_:
{
if (v_revert_126_ == 0)
{
if (v_revert_77_ == 0)
{
goto v___jp_133_;
}
else
{
return v_revert_126_;
}
}
else
{
if (v_revert_77_ == 0)
{
return v_revert_77_;
}
else
{
goto v___jp_133_;
}
}
}
v___jp_135_:
{
uint8_t v___x_136_; 
v___x_136_ = lean_nat_dec_eq(v_min_74_, v_min_123_);
if (v___x_136_ == 0)
{
return v___x_136_;
}
else
{
uint8_t v___x_137_; 
v___x_137_ = lean_nat_dec_eq(v_detailed_75_, v_detailed_124_);
if (v___x_137_ == 0)
{
return v___x_137_;
}
else
{
if (v_useSorry_125_ == 0)
{
if (v_useSorry_76_ == 0)
{
goto v___jp_134_;
}
else
{
return v_useSorry_125_;
}
}
else
{
if (v_useSorry_76_ == 0)
{
return v_useSorry_76_;
}
else
{
goto v___jp_134_;
}
}
}
}
}
v___jp_138_:
{
if (v_order_122_ == 0)
{
if (v_order_73_ == 0)
{
goto v___jp_135_;
}
else
{
return v_order_122_;
}
}
else
{
if (v_order_73_ == 0)
{
return v_order_73_;
}
else
{
goto v___jp_135_;
}
}
}
v___jp_139_:
{
if (v_inj_121_ == 0)
{
if (v_inj_72_ == 0)
{
goto v___jp_138_;
}
else
{
return v_inj_121_;
}
}
else
{
if (v_inj_72_ == 0)
{
return v_inj_72_;
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
v___x_141_ = lean_nat_dec_eq(v_acSteps_69_, v_acSteps_118_);
if (v___x_141_ == 0)
{
return v___x_141_;
}
else
{
uint8_t v___x_142_; 
v___x_142_ = lean_nat_dec_eq(v_exp_70_, v_exp_119_);
if (v___x_142_ == 0)
{
return v___x_142_;
}
else
{
if (v_abstractProof_120_ == 0)
{
if (v_abstractProof_71_ == 0)
{
goto v___jp_139_;
}
else
{
return v_abstractProof_120_;
}
}
else
{
if (v_abstractProof_71_ == 0)
{
return v_abstractProof_71_;
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
if (v_ac_117_ == 0)
{
if (v_ac_68_ == 0)
{
goto v___jp_140_;
}
else
{
return v_ac_117_;
}
}
else
{
if (v_ac_68_ == 0)
{
return v_ac_68_;
}
else
{
goto v___jp_140_;
}
}
}
v___jp_144_:
{
uint8_t v___x_145_; 
v___x_145_ = lean_nat_dec_eq(v_liaSteps_66_, v_liaSteps_115_);
if (v___x_145_ == 0)
{
return v___x_145_;
}
else
{
if (v_hom_116_ == 0)
{
if (v_hom_67_ == 0)
{
goto v___jp_143_;
}
else
{
return v_hom_116_;
}
}
else
{
if (v_hom_67_ == 0)
{
return v_hom_67_;
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
if (v_lia_114_ == 0)
{
if (v_lia_65_ == 0)
{
goto v___jp_144_;
}
else
{
return v_lia_114_;
}
}
else
{
if (v_lia_65_ == 0)
{
return v_lia_65_;
}
else
{
goto v___jp_144_;
}
}
}
v___jp_147_:
{
uint8_t v___x_148_; 
v___x_148_ = lean_nat_dec_eq(v_ringSteps_62_, v_ringSteps_111_);
if (v___x_148_ == 0)
{
return v___x_148_;
}
else
{
uint8_t v___x_149_; 
v___x_149_ = lean_nat_dec_eq(v_ringMaxDegree_63_, v_ringMaxDegree_112_);
if (v___x_149_ == 0)
{
return v___x_149_;
}
else
{
if (v_linarith_113_ == 0)
{
if (v_linarith_64_ == 0)
{
goto v___jp_146_;
}
else
{
return v_linarith_113_;
}
}
else
{
if (v_linarith_64_ == 0)
{
return v_linarith_64_;
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
uint8_t v___x_151_; 
v___x_151_ = lean_nat_dec_eq(v_maxChar_60_, v_maxChar_109_);
if (v___x_151_ == 0)
{
return v___x_151_;
}
else
{
if (v_ring_110_ == 0)
{
if (v_ring_61_ == 0)
{
goto v___jp_147_;
}
else
{
return v_ring_110_;
}
}
else
{
if (v_ring_61_ == 0)
{
return v_ring_61_;
}
else
{
goto v___jp_147_;
}
}
}
}
v___jp_152_:
{
if (v_distrib_108_ == 0)
{
if (v_distrib_59_ == 0)
{
goto v___jp_150_;
}
else
{
return v_distrib_108_;
}
}
else
{
if (v_distrib_59_ == 0)
{
return v_distrib_59_;
}
else
{
goto v___jp_150_;
}
}
}
v___jp_153_:
{
if (v_zeta_107_ == 0)
{
if (v_zeta_58_ == 0)
{
goto v___jp_152_;
}
else
{
return v_zeta_107_;
}
}
else
{
if (v_zeta_58_ == 0)
{
return v_zeta_58_;
}
else
{
goto v___jp_152_;
}
}
}
v___jp_154_:
{
if (v_zetaDelta_106_ == 0)
{
if (v_zetaDelta_57_ == 0)
{
goto v___jp_153_;
}
else
{
return v_zetaDelta_106_;
}
}
else
{
if (v_zetaDelta_57_ == 0)
{
return v_zetaDelta_57_;
}
else
{
goto v___jp_153_;
}
}
}
v___jp_155_:
{
if (v_mbtc_105_ == 0)
{
if (v_mbtc_56_ == 0)
{
goto v___jp_154_;
}
else
{
return v_mbtc_105_;
}
}
else
{
if (v_mbtc_56_ == 0)
{
return v_mbtc_56_;
}
else
{
goto v___jp_154_;
}
}
}
v___jp_156_:
{
if (v_qlia_104_ == 0)
{
if (v_qlia_55_ == 0)
{
goto v___jp_155_;
}
else
{
return v_qlia_104_;
}
}
else
{
if (v_qlia_55_ == 0)
{
return v_qlia_55_;
}
else
{
goto v___jp_155_;
}
}
}
v___jp_157_:
{
if (v_clean_103_ == 0)
{
if (v_clean_54_ == 0)
{
goto v___jp_156_;
}
else
{
return v_clean_103_;
}
}
else
{
if (v_clean_54_ == 0)
{
return v_clean_54_;
}
else
{
goto v___jp_156_;
}
}
}
v___jp_158_:
{
if (v_verbose_102_ == 0)
{
if (v_verbose_53_ == 0)
{
goto v___jp_157_;
}
else
{
return v_verbose_102_;
}
}
else
{
if (v_verbose_53_ == 0)
{
return v_verbose_53_;
}
else
{
goto v___jp_157_;
}
}
}
v___jp_159_:
{
if (v_lookahead_101_ == 0)
{
if (v_lookahead_52_ == 0)
{
goto v___jp_158_;
}
else
{
return v_lookahead_101_;
}
}
else
{
if (v_lookahead_52_ == 0)
{
return v_lookahead_52_;
}
else
{
goto v___jp_158_;
}
}
}
v___jp_160_:
{
if (v_funext_100_ == 0)
{
if (v_funext_51_ == 0)
{
goto v___jp_159_;
}
else
{
return v_funext_100_;
}
}
else
{
if (v_funext_51_ == 0)
{
return v_funext_51_;
}
else
{
goto v___jp_159_;
}
}
}
v___jp_161_:
{
if (v_etaStruct_99_ == 0)
{
if (v_etaStruct_50_ == 0)
{
goto v___jp_160_;
}
else
{
return v_etaStruct_99_;
}
}
else
{
if (v_etaStruct_50_ == 0)
{
return v_etaStruct_50_;
}
else
{
goto v___jp_160_;
}
}
}
v___jp_162_:
{
if (v_extAll_98_ == 0)
{
if (v_extAll_49_ == 0)
{
goto v___jp_161_;
}
else
{
return v_extAll_98_;
}
}
else
{
if (v_extAll_49_ == 0)
{
return v_extAll_49_;
}
else
{
goto v___jp_161_;
}
}
}
v___jp_163_:
{
uint8_t v___x_164_; 
v___x_164_ = lean_nat_dec_eq(v_canonHeartbeats_47_, v_canonHeartbeats_96_);
if (v___x_164_ == 0)
{
return v___x_164_;
}
else
{
if (v_ext_97_ == 0)
{
if (v_ext_48_ == 0)
{
goto v___jp_162_;
}
else
{
return v_ext_97_;
}
}
else
{
if (v_ext_48_ == 0)
{
return v_ext_48_;
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
if (v_splitImp_95_ == 0)
{
if (v_splitImp_46_ == 0)
{
goto v___jp_163_;
}
else
{
return v_splitImp_95_;
}
}
else
{
if (v_splitImp_46_ == 0)
{
return v_splitImp_46_;
}
else
{
goto v___jp_163_;
}
}
}
v___jp_166_:
{
if (v_splitIndPred_94_ == 0)
{
if (v_splitIndPred_45_ == 0)
{
goto v___jp_165_;
}
else
{
return v_splitIndPred_94_;
}
}
else
{
if (v_splitIndPred_45_ == 0)
{
return v_splitIndPred_45_;
}
else
{
goto v___jp_165_;
}
}
}
v___jp_167_:
{
if (v_splitIte_93_ == 0)
{
if (v_splitIte_44_ == 0)
{
goto v___jp_166_;
}
else
{
return v_splitIte_93_;
}
}
else
{
if (v_splitIte_44_ == 0)
{
return v_splitIte_44_;
}
else
{
goto v___jp_166_;
}
}
}
v___jp_168_:
{
if (v_splitMatch_92_ == 0)
{
if (v_splitMatch_43_ == 0)
{
goto v___jp_167_;
}
else
{
return v_splitMatch_92_;
}
}
else
{
if (v_splitMatch_43_ == 0)
{
return v_splitMatch_43_;
}
else
{
goto v___jp_167_;
}
}
}
v___jp_169_:
{
uint8_t v___x_170_; 
v___x_170_ = lean_nat_dec_eq(v_splits_37_, v_splits_86_);
if (v___x_170_ == 0)
{
return v___x_170_;
}
else
{
uint8_t v___x_171_; 
v___x_171_ = lean_nat_dec_eq(v_ematch_38_, v_ematch_87_);
if (v___x_171_ == 0)
{
return v___x_171_;
}
else
{
uint8_t v___x_172_; 
v___x_172_ = lean_nat_dec_eq(v_gen_39_, v_gen_88_);
if (v___x_172_ == 0)
{
return v___x_172_;
}
else
{
uint8_t v___x_173_; 
v___x_173_ = lean_nat_dec_eq(v_genLocal_40_, v_genLocal_89_);
if (v___x_173_ == 0)
{
return v___x_173_;
}
else
{
uint8_t v___x_174_; 
v___x_174_ = lean_nat_dec_eq(v_instances_41_, v_instances_90_);
if (v___x_174_ == 0)
{
return v___x_174_;
}
else
{
if (v_matchEqs_91_ == 0)
{
if (v_matchEqs_42_ == 0)
{
goto v___jp_168_;
}
else
{
return v_matchEqs_91_;
}
}
else
{
if (v_matchEqs_42_ == 0)
{
return v_matchEqs_42_;
}
else
{
goto v___jp_168_;
}
}
}
}
}
}
}
}
v___jp_175_:
{
if (v_locals_85_ == 0)
{
if (v_locals_36_ == 0)
{
goto v___jp_169_;
}
else
{
return v_locals_85_;
}
}
else
{
if (v_locals_36_ == 0)
{
return v_locals_36_;
}
else
{
goto v___jp_169_;
}
}
}
v___jp_176_:
{
if (v_suggestions_84_ == 0)
{
if (v_suggestions_35_ == 0)
{
goto v___jp_175_;
}
else
{
return v_suggestions_84_;
}
}
else
{
if (v_suggestions_35_ == 0)
{
return v_suggestions_35_;
}
else
{
goto v___jp_175_;
}
}
}
v___jp_177_:
{
if (v_lax_83_ == 0)
{
if (v_lax_34_ == 0)
{
goto v___jp_176_;
}
else
{
return v_lax_83_;
}
}
else
{
if (v_lax_34_ == 0)
{
return v_lax_34_;
}
else
{
goto v___jp_176_;
}
}
}
v___jp_178_:
{
if (v_markInstances_82_ == 0)
{
if (v_markInstances_33_ == 0)
{
goto v___jp_177_;
}
else
{
return v_markInstances_82_;
}
}
else
{
if (v_markInstances_33_ == 0)
{
return v_markInstances_33_;
}
else
{
goto v___jp_177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instBEqConfig_beq___boxed(lean_object* v_x_179_, lean_object* v_x_180_){
_start:
{
uint8_t v_res_181_; lean_object* v_r_182_; 
v_res_181_ = l_Lean_Grind_instBEqConfig_beq(v_x_179_, v_x_180_);
lean_dec_ref(v_x_180_);
lean_dec_ref(v_x_179_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
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
