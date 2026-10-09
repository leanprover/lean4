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
uint8_t l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(lean_object* v_x_17_, lean_object* v_x_18_){
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
LEAN_EXPORT void l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_17_ = stack[0].m_obj;
lean_object* v_x_18_ = stack[1].m_obj;
uint8_t v_res_25_;
v_res_25_ = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_x_17_, v_x_18_);
stack->m_num = v_res_25_;
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
uint8_t l_Lean_Grind_instBEqConfig_beq(lean_object* v_x_30_, lean_object* v_x_31_){
_start:
{
uint8_t v_trace_32_; uint8_t v_markInstances_33_; uint8_t v_lax_34_; uint8_t v_suggestions_35_; uint8_t v_locals_36_; lean_object* v_splits_37_; lean_object* v_ematch_38_; lean_object* v_gen_39_; lean_object* v_genLocal_40_; lean_object* v_instances_41_; uint8_t v_matchEqs_42_; uint8_t v_splitMatch_43_; uint8_t v_splitIte_44_; uint8_t v_splitIndPred_45_; uint8_t v_splitImp_46_; lean_object* v_canonHeartbeats_47_; uint8_t v_ext_48_; uint8_t v_extAll_49_; uint8_t v_etaStruct_50_; uint8_t v_funext_51_; uint8_t v_lookahead_52_; uint8_t v_verbose_53_; uint8_t v_clean_54_; uint8_t v_qlia_55_; uint8_t v_mbtc_56_; uint8_t v_zetaDelta_57_; uint8_t v_zeta_58_; uint8_t v_ring_59_; lean_object* v_ringSteps_60_; lean_object* v_ringMaxDegree_61_; uint8_t v_linarith_62_; uint8_t v_lia_63_; lean_object* v_liaSteps_64_; uint8_t v_hom_65_; uint8_t v_ac_66_; lean_object* v_acSteps_67_; lean_object* v_exp_68_; uint8_t v_abstractProof_69_; uint8_t v_inj_70_; uint8_t v_order_71_; lean_object* v_min_72_; lean_object* v_detailed_73_; uint8_t v_useSorry_74_; uint8_t v_revert_75_; uint8_t v_funCC_76_; uint8_t v_reducible_77_; lean_object* v_maxSuggestions_78_; uint8_t v_trace_79_; uint8_t v_markInstances_80_; uint8_t v_lax_81_; uint8_t v_suggestions_82_; uint8_t v_locals_83_; lean_object* v_splits_84_; lean_object* v_ematch_85_; lean_object* v_gen_86_; lean_object* v_genLocal_87_; lean_object* v_instances_88_; uint8_t v_matchEqs_89_; uint8_t v_splitMatch_90_; uint8_t v_splitIte_91_; uint8_t v_splitIndPred_92_; uint8_t v_splitImp_93_; lean_object* v_canonHeartbeats_94_; uint8_t v_ext_95_; uint8_t v_extAll_96_; uint8_t v_etaStruct_97_; uint8_t v_funext_98_; uint8_t v_lookahead_99_; uint8_t v_verbose_100_; uint8_t v_clean_101_; uint8_t v_qlia_102_; uint8_t v_mbtc_103_; uint8_t v_zetaDelta_104_; uint8_t v_zeta_105_; uint8_t v_ring_106_; lean_object* v_ringSteps_107_; lean_object* v_ringMaxDegree_108_; uint8_t v_linarith_109_; uint8_t v_lia_110_; lean_object* v_liaSteps_111_; uint8_t v_hom_112_; uint8_t v_ac_113_; lean_object* v_acSteps_114_; lean_object* v_exp_115_; uint8_t v_abstractProof_116_; uint8_t v_inj_117_; uint8_t v_order_118_; lean_object* v_min_119_; lean_object* v_detailed_120_; uint8_t v_useSorry_121_; uint8_t v_revert_122_; uint8_t v_funCC_123_; uint8_t v_reducible_124_; lean_object* v_maxSuggestions_125_; uint8_t v___y_131_; uint8_t v___y_137_; uint8_t v___y_142_; uint8_t v___y_146_; uint8_t v___y_161_; uint8_t v___y_168_; 
v_trace_32_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14);
v_markInstances_33_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 1);
v_lax_34_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 2);
v_suggestions_35_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 3);
v_locals_36_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 4);
v_splits_37_ = lean_ctor_get(v_x_30_, 0);
v_ematch_38_ = lean_ctor_get(v_x_30_, 1);
v_gen_39_ = lean_ctor_get(v_x_30_, 2);
v_genLocal_40_ = lean_ctor_get(v_x_30_, 3);
v_instances_41_ = lean_ctor_get(v_x_30_, 4);
v_matchEqs_42_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 5);
v_splitMatch_43_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 6);
v_splitIte_44_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 7);
v_splitIndPred_45_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 8);
v_splitImp_46_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 9);
v_canonHeartbeats_47_ = lean_ctor_get(v_x_30_, 5);
v_ext_48_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 10);
v_extAll_49_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 11);
v_etaStruct_50_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 12);
v_funext_51_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 13);
v_lookahead_52_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 14);
v_verbose_53_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 15);
v_clean_54_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 16);
v_qlia_55_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 17);
v_mbtc_56_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 18);
v_zetaDelta_57_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 19);
v_zeta_58_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 20);
v_ring_59_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 21);
v_ringSteps_60_ = lean_ctor_get(v_x_30_, 6);
v_ringMaxDegree_61_ = lean_ctor_get(v_x_30_, 7);
v_linarith_62_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 22);
v_lia_63_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 23);
v_liaSteps_64_ = lean_ctor_get(v_x_30_, 8);
v_hom_65_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 24);
v_ac_66_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 25);
v_acSteps_67_ = lean_ctor_get(v_x_30_, 9);
v_exp_68_ = lean_ctor_get(v_x_30_, 10);
v_abstractProof_69_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 26);
v_inj_70_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 27);
v_order_71_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 28);
v_min_72_ = lean_ctor_get(v_x_30_, 11);
v_detailed_73_ = lean_ctor_get(v_x_30_, 12);
v_useSorry_74_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 29);
v_revert_75_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 30);
v_funCC_76_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 31);
v_reducible_77_ = lean_ctor_get_uint8(v_x_30_, sizeof(void*)*14 + 32);
v_maxSuggestions_78_ = lean_ctor_get(v_x_30_, 13);
v_trace_79_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14);
v_markInstances_80_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 1);
v_lax_81_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 2);
v_suggestions_82_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 3);
v_locals_83_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 4);
v_splits_84_ = lean_ctor_get(v_x_31_, 0);
v_ematch_85_ = lean_ctor_get(v_x_31_, 1);
v_gen_86_ = lean_ctor_get(v_x_31_, 2);
v_genLocal_87_ = lean_ctor_get(v_x_31_, 3);
v_instances_88_ = lean_ctor_get(v_x_31_, 4);
v_matchEqs_89_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 5);
v_splitMatch_90_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 6);
v_splitIte_91_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 7);
v_splitIndPred_92_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 8);
v_splitImp_93_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 9);
v_canonHeartbeats_94_ = lean_ctor_get(v_x_31_, 5);
v_ext_95_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 10);
v_extAll_96_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 11);
v_etaStruct_97_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 12);
v_funext_98_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 13);
v_lookahead_99_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 14);
v_verbose_100_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 15);
v_clean_101_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 16);
v_qlia_102_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 17);
v_mbtc_103_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 18);
v_zetaDelta_104_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 19);
v_zeta_105_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 20);
v_ring_106_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 21);
v_ringSteps_107_ = lean_ctor_get(v_x_31_, 6);
v_ringMaxDegree_108_ = lean_ctor_get(v_x_31_, 7);
v_linarith_109_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 22);
v_lia_110_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 23);
v_liaSteps_111_ = lean_ctor_get(v_x_31_, 8);
v_hom_112_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 24);
v_ac_113_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 25);
v_acSteps_114_ = lean_ctor_get(v_x_31_, 9);
v_exp_115_ = lean_ctor_get(v_x_31_, 10);
v_abstractProof_116_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 26);
v_inj_117_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 27);
v_order_118_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 28);
v_min_119_ = lean_ctor_get(v_x_31_, 11);
v_detailed_120_ = lean_ctor_get(v_x_31_, 12);
v_useSorry_121_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 29);
v_revert_122_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 30);
v_funCC_123_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 31);
v_reducible_124_ = lean_ctor_get_uint8(v_x_31_, sizeof(void*)*14 + 32);
v_maxSuggestions_125_ = lean_ctor_get(v_x_31_, 13);
if (v_trace_79_ == 0)
{
if (v_trace_32_ == 0)
{
goto v___jp_178_;
}
else
{
return v_trace_79_;
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
v___jp_126_:
{
if (v_reducible_124_ == 0)
{
if (v_reducible_77_ == 0)
{
uint8_t v___x_127_; 
v___x_127_ = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_maxSuggestions_78_, v_maxSuggestions_125_);
return v___x_127_;
}
else
{
return v_reducible_124_;
}
}
else
{
if (v_reducible_77_ == 0)
{
return v_reducible_77_;
}
else
{
uint8_t v___x_128_; 
v___x_128_ = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(v_maxSuggestions_78_, v_maxSuggestions_125_);
return v___x_128_;
}
}
}
v___jp_129_:
{
if (v_funCC_123_ == 0)
{
if (v_funCC_76_ == 0)
{
goto v___jp_126_;
}
else
{
return v_funCC_123_;
}
}
else
{
if (v_funCC_76_ == 0)
{
return v_funCC_76_;
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
if (v_revert_122_ == 0)
{
if (v_revert_75_ == 0)
{
goto v___jp_129_;
}
else
{
return v_revert_122_;
}
}
else
{
if (v_revert_75_ == 0)
{
return v_revert_75_;
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
v___x_133_ = lean_nat_dec_eq(v_min_72_, v_min_119_);
if (v___x_133_ == 0)
{
return v___x_133_;
}
else
{
uint8_t v___x_134_; 
v___x_134_ = lean_nat_dec_eq(v_detailed_73_, v_detailed_120_);
if (v___x_134_ == 0)
{
return v___x_134_;
}
else
{
if (v_useSorry_121_ == 0)
{
if (v_useSorry_74_ == 0)
{
v___y_131_ = v___x_134_;
goto v___jp_130_;
}
else
{
return v_useSorry_121_;
}
}
else
{
v___y_131_ = v_useSorry_74_;
goto v___jp_130_;
}
}
}
}
v___jp_135_:
{
if (v_order_118_ == 0)
{
if (v_order_71_ == 0)
{
goto v___jp_132_;
}
else
{
return v_order_118_;
}
}
else
{
if (v_order_71_ == 0)
{
return v_order_71_;
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
if (v_inj_117_ == 0)
{
if (v_inj_70_ == 0)
{
goto v___jp_135_;
}
else
{
return v_inj_117_;
}
}
else
{
if (v_inj_70_ == 0)
{
return v_inj_70_;
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
v___x_139_ = lean_nat_dec_eq(v_acSteps_67_, v_acSteps_114_);
if (v___x_139_ == 0)
{
return v___x_139_;
}
else
{
uint8_t v___x_140_; 
v___x_140_ = lean_nat_dec_eq(v_exp_68_, v_exp_115_);
if (v___x_140_ == 0)
{
return v___x_140_;
}
else
{
if (v_abstractProof_116_ == 0)
{
if (v_abstractProof_69_ == 0)
{
v___y_137_ = v___x_140_;
goto v___jp_136_;
}
else
{
return v_abstractProof_116_;
}
}
else
{
v___y_137_ = v_abstractProof_69_;
goto v___jp_136_;
}
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
if (v_ac_113_ == 0)
{
if (v_ac_66_ == 0)
{
goto v___jp_138_;
}
else
{
return v_ac_113_;
}
}
else
{
if (v_ac_66_ == 0)
{
return v_ac_66_;
}
else
{
goto v___jp_138_;
}
}
}
}
v___jp_143_:
{
uint8_t v___x_144_; 
v___x_144_ = lean_nat_dec_eq(v_liaSteps_64_, v_liaSteps_111_);
if (v___x_144_ == 0)
{
return v___x_144_;
}
else
{
if (v_hom_112_ == 0)
{
if (v_hom_65_ == 0)
{
v___y_142_ = v___x_144_;
goto v___jp_141_;
}
else
{
return v_hom_112_;
}
}
else
{
v___y_142_ = v_hom_65_;
goto v___jp_141_;
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
if (v_lia_110_ == 0)
{
if (v_lia_63_ == 0)
{
goto v___jp_143_;
}
else
{
return v_lia_110_;
}
}
else
{
if (v_lia_63_ == 0)
{
return v_lia_63_;
}
else
{
goto v___jp_143_;
}
}
}
}
v___jp_147_:
{
uint8_t v___x_148_; 
v___x_148_ = lean_nat_dec_eq(v_ringSteps_60_, v_ringSteps_107_);
if (v___x_148_ == 0)
{
return v___x_148_;
}
else
{
uint8_t v___x_149_; 
v___x_149_ = lean_nat_dec_eq(v_ringMaxDegree_61_, v_ringMaxDegree_108_);
if (v___x_149_ == 0)
{
return v___x_149_;
}
else
{
if (v_linarith_109_ == 0)
{
if (v_linarith_62_ == 0)
{
v___y_146_ = v___x_149_;
goto v___jp_145_;
}
else
{
return v_linarith_109_;
}
}
else
{
v___y_146_ = v_linarith_62_;
goto v___jp_145_;
}
}
}
}
v___jp_150_:
{
if (v_ring_106_ == 0)
{
if (v_ring_59_ == 0)
{
goto v___jp_147_;
}
else
{
return v_ring_106_;
}
}
else
{
if (v_ring_59_ == 0)
{
return v_ring_59_;
}
else
{
goto v___jp_147_;
}
}
}
v___jp_151_:
{
if (v_zeta_105_ == 0)
{
if (v_zeta_58_ == 0)
{
goto v___jp_150_;
}
else
{
return v_zeta_105_;
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
goto v___jp_150_;
}
}
}
v___jp_152_:
{
if (v_zetaDelta_104_ == 0)
{
if (v_zetaDelta_57_ == 0)
{
goto v___jp_151_;
}
else
{
return v_zetaDelta_104_;
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
goto v___jp_151_;
}
}
}
v___jp_153_:
{
if (v_mbtc_103_ == 0)
{
if (v_mbtc_56_ == 0)
{
goto v___jp_152_;
}
else
{
return v_mbtc_103_;
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
goto v___jp_152_;
}
}
}
v___jp_154_:
{
if (v_qlia_102_ == 0)
{
if (v_qlia_55_ == 0)
{
goto v___jp_153_;
}
else
{
return v_qlia_102_;
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
goto v___jp_153_;
}
}
}
v___jp_155_:
{
if (v_clean_101_ == 0)
{
if (v_clean_54_ == 0)
{
goto v___jp_154_;
}
else
{
return v_clean_101_;
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
goto v___jp_154_;
}
}
}
v___jp_156_:
{
if (v_verbose_100_ == 0)
{
if (v_verbose_53_ == 0)
{
goto v___jp_155_;
}
else
{
return v_verbose_100_;
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
goto v___jp_155_;
}
}
}
v___jp_157_:
{
if (v_lookahead_99_ == 0)
{
if (v_lookahead_52_ == 0)
{
goto v___jp_156_;
}
else
{
return v_lookahead_99_;
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
goto v___jp_156_;
}
}
}
v___jp_158_:
{
if (v_funext_98_ == 0)
{
if (v_funext_51_ == 0)
{
goto v___jp_157_;
}
else
{
return v_funext_98_;
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
goto v___jp_157_;
}
}
}
v___jp_159_:
{
if (v_etaStruct_97_ == 0)
{
if (v_etaStruct_50_ == 0)
{
goto v___jp_158_;
}
else
{
return v_etaStruct_97_;
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
goto v___jp_158_;
}
}
}
v___jp_160_:
{
if (v___y_161_ == 0)
{
return v___y_161_;
}
else
{
if (v_extAll_96_ == 0)
{
if (v_extAll_49_ == 0)
{
goto v___jp_159_;
}
else
{
return v_extAll_96_;
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
goto v___jp_159_;
}
}
}
}
v___jp_162_:
{
uint8_t v___x_163_; 
v___x_163_ = lean_nat_dec_eq(v_canonHeartbeats_47_, v_canonHeartbeats_94_);
if (v___x_163_ == 0)
{
return v___x_163_;
}
else
{
if (v_ext_95_ == 0)
{
if (v_ext_48_ == 0)
{
v___y_161_ = v___x_163_;
goto v___jp_160_;
}
else
{
return v_ext_95_;
}
}
else
{
v___y_161_ = v_ext_48_;
goto v___jp_160_;
}
}
}
v___jp_164_:
{
if (v_splitImp_93_ == 0)
{
if (v_splitImp_46_ == 0)
{
goto v___jp_162_;
}
else
{
return v_splitImp_93_;
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
goto v___jp_162_;
}
}
}
v___jp_165_:
{
if (v_splitIndPred_92_ == 0)
{
if (v_splitIndPred_45_ == 0)
{
goto v___jp_164_;
}
else
{
return v_splitIndPred_92_;
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
goto v___jp_164_;
}
}
}
v___jp_166_:
{
if (v_splitIte_91_ == 0)
{
if (v_splitIte_44_ == 0)
{
goto v___jp_165_;
}
else
{
return v_splitIte_91_;
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
goto v___jp_165_;
}
}
}
v___jp_167_:
{
if (v___y_168_ == 0)
{
return v___y_168_;
}
else
{
if (v_splitMatch_90_ == 0)
{
if (v_splitMatch_43_ == 0)
{
goto v___jp_166_;
}
else
{
return v_splitMatch_90_;
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
goto v___jp_166_;
}
}
}
}
v___jp_169_:
{
uint8_t v___x_170_; 
v___x_170_ = lean_nat_dec_eq(v_splits_37_, v_splits_84_);
if (v___x_170_ == 0)
{
return v___x_170_;
}
else
{
uint8_t v___x_171_; 
v___x_171_ = lean_nat_dec_eq(v_ematch_38_, v_ematch_85_);
if (v___x_171_ == 0)
{
return v___x_171_;
}
else
{
uint8_t v___x_172_; 
v___x_172_ = lean_nat_dec_eq(v_gen_39_, v_gen_86_);
if (v___x_172_ == 0)
{
return v___x_172_;
}
else
{
uint8_t v___x_173_; 
v___x_173_ = lean_nat_dec_eq(v_genLocal_40_, v_genLocal_87_);
if (v___x_173_ == 0)
{
return v___x_173_;
}
else
{
uint8_t v___x_174_; 
v___x_174_ = lean_nat_dec_eq(v_instances_41_, v_instances_88_);
if (v___x_174_ == 0)
{
return v___x_174_;
}
else
{
if (v_matchEqs_89_ == 0)
{
if (v_matchEqs_42_ == 0)
{
v___y_168_ = v___x_174_;
goto v___jp_167_;
}
else
{
return v_matchEqs_89_;
}
}
else
{
v___y_168_ = v_matchEqs_42_;
goto v___jp_167_;
}
}
}
}
}
}
}
v___jp_175_:
{
if (v_locals_83_ == 0)
{
if (v_locals_36_ == 0)
{
goto v___jp_169_;
}
else
{
return v_locals_83_;
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
if (v_suggestions_82_ == 0)
{
if (v_suggestions_35_ == 0)
{
goto v___jp_175_;
}
else
{
return v_suggestions_82_;
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
if (v_lax_81_ == 0)
{
if (v_lax_34_ == 0)
{
goto v___jp_176_;
}
else
{
return v_lax_81_;
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
if (v_markInstances_80_ == 0)
{
if (v_markInstances_33_ == 0)
{
goto v___jp_177_;
}
else
{
return v_markInstances_80_;
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
LEAN_EXPORT void l_Lean_Grind_instBEqConfig_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_30_ = stack[0].m_obj;
lean_object* v_x_31_ = stack[1].m_obj;
uint8_t v_res_179_;
v_res_179_ = l_Lean_Grind_instBEqConfig_beq(v_x_30_, v_x_31_);
stack->m_num = v_res_179_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_instBEqConfig_beq___boxed(lean_object* v_x_180_, lean_object* v_x_181_){
_start:
{
uint8_t v_res_182_; lean_object* v_r_183_; 
v_res_182_ = l_Lean_Grind_instBEqConfig_beq(v_x_180_, v_x_181_);
lean_dec_ref(v_x_181_);
lean_dec_ref(v_x_180_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
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
