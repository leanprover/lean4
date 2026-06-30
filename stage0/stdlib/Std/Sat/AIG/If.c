// Lean compiler output
// Module: Std.Sat.AIG.If
// Imports: public import Std.Sat.AIG.LawfulVecOperator import Init.Omega
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
lean_object* l_Std_Sat_AIG_mkGateCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkOrCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_aig_3_, lean_object* v_input_4_){
_start:
{
lean_object* v_discr_5_; lean_object* v_lhs_6_; lean_object* v_rhs_7_; lean_object* v___x_8_; lean_object* v_res_9_; lean_object* v_aig_10_; lean_object* v_ref_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_64_; 
v_discr_5_ = lean_ctor_get(v_input_4_, 0);
lean_inc_ref_n(v_discr_5_, 2);
v_lhs_6_ = lean_ctor_get(v_input_4_, 1);
lean_inc_ref(v_lhs_6_);
v_rhs_7_ = lean_ctor_get(v_input_4_, 2);
lean_inc_ref(v_rhs_7_);
lean_dec_ref(v_input_4_);
v___x_8_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8_, 0, v_discr_5_);
lean_ctor_set(v___x_8_, 1, v_lhs_6_);
lean_inc_ref(v_inst_2_);
lean_inc_ref(v_inst_1_);
v_res_9_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_1_, v_inst_2_, v_aig_3_, v___x_8_);
v_aig_10_ = lean_ctor_get(v_res_9_, 0);
v_ref_11_ = lean_ctor_get(v_res_9_, 1);
v_isSharedCheck_64_ = !lean_is_exclusive(v_res_9_);
if (v_isSharedCheck_64_ == 0)
{
v___x_13_ = v_res_9_;
v_isShared_14_ = v_isSharedCheck_64_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_ref_11_);
lean_inc(v_aig_10_);
lean_dec(v_res_9_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_64_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v_gate_15_; uint8_t v_invert_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_63_; 
v_gate_15_ = lean_ctor_get(v_discr_5_, 0);
v_invert_16_ = lean_ctor_get_uint8(v_discr_5_, sizeof(void*)*1);
v_isSharedCheck_63_ = !lean_is_exclusive(v_discr_5_);
if (v_isSharedCheck_63_ == 0)
{
v___x_18_ = v_discr_5_;
v_isShared_19_ = v_isSharedCheck_63_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_gate_15_);
lean_dec(v_discr_5_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_63_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
lean_object* v_gate_20_; uint8_t v_invert_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_62_; 
v_gate_20_ = lean_ctor_get(v_rhs_7_, 0);
v_invert_21_ = lean_ctor_get_uint8(v_rhs_7_, sizeof(void*)*1);
v_isSharedCheck_62_ = !lean_is_exclusive(v_rhs_7_);
if (v_isSharedCheck_62_ == 0)
{
v___x_23_ = v_rhs_7_;
v_isShared_24_ = v_isSharedCheck_62_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_gate_20_);
lean_dec(v_rhs_7_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_62_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v_aig_26_; lean_object* v_ref_27_; 
if (v_invert_16_ == 0)
{
uint8_t v___x_54_; lean_object* v___x_56_; 
v___x_54_ = 1;
if (v_isShared_19_ == 0)
{
v___x_56_ = v___x_18_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v_gate_15_);
v___x_56_ = v_reuseFailAlloc_57_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
lean_ctor_set_uint8(v___x_56_, sizeof(void*)*1, v___x_54_);
v_aig_26_ = v_aig_10_;
v_ref_27_ = v___x_56_;
goto v___jp_25_;
}
}
else
{
uint8_t v___x_58_; lean_object* v___x_60_; 
v___x_58_ = 0;
if (v_isShared_19_ == 0)
{
v___x_60_ = v___x_18_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v_gate_15_);
v___x_60_ = v_reuseFailAlloc_61_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
lean_ctor_set_uint8(v___x_60_, sizeof(void*)*1, v___x_58_);
v_aig_26_ = v_aig_10_;
v_ref_27_ = v___x_60_;
goto v___jp_25_;
}
}
v___jp_25_:
{
lean_object* v___x_29_; 
if (v_isShared_24_ == 0)
{
v___x_29_ = v___x_23_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v_gate_20_);
lean_ctor_set_uint8(v_reuseFailAlloc_53_, sizeof(void*)*1, v_invert_21_);
v___x_29_ = v_reuseFailAlloc_53_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
lean_object* v___x_31_; 
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 1, v___x_29_);
lean_ctor_set(v___x_13_, 0, v_ref_27_);
v___x_31_ = v___x_13_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v_ref_27_);
lean_ctor_set(v_reuseFailAlloc_52_, 1, v___x_29_);
v___x_31_ = v_reuseFailAlloc_52_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
lean_object* v_res_32_; lean_object* v_aig_33_; lean_object* v_ref_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_51_; 
lean_inc_ref(v_inst_2_);
lean_inc_ref(v_inst_1_);
v_res_32_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_1_, v_inst_2_, v_aig_26_, v___x_31_);
v_aig_33_ = lean_ctor_get(v_res_32_, 0);
v_ref_34_ = lean_ctor_get(v_res_32_, 1);
v_isSharedCheck_51_ = !lean_is_exclusive(v_res_32_);
if (v_isSharedCheck_51_ == 0)
{
v___x_36_ = v_res_32_;
v_isShared_37_ = v_isSharedCheck_51_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_ref_34_);
lean_inc(v_aig_33_);
lean_dec(v_res_32_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_51_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v_gate_38_; uint8_t v_invert_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_50_; 
v_gate_38_ = lean_ctor_get(v_ref_11_, 0);
v_invert_39_ = lean_ctor_get_uint8(v_ref_11_, sizeof(void*)*1);
v_isSharedCheck_50_ = !lean_is_exclusive(v_ref_11_);
if (v_isSharedCheck_50_ == 0)
{
v___x_41_ = v_ref_11_;
v_isShared_42_ = v_isSharedCheck_50_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_gate_38_);
lean_dec(v_ref_11_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_50_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v_lhsRef_44_; 
if (v_isShared_42_ == 0)
{
v_lhsRef_44_ = v___x_41_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_gate_38_);
lean_ctor_set_uint8(v_reuseFailAlloc_49_, sizeof(void*)*1, v_invert_39_);
v_lhsRef_44_ = v_reuseFailAlloc_49_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
lean_object* v___x_46_; 
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 0, v_lhsRef_44_);
v___x_46_ = v___x_36_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_lhsRef_44_);
lean_ctor_set(v_reuseFailAlloc_48_, 1, v_ref_34_);
v___x_46_ = v_reuseFailAlloc_48_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
lean_object* v___x_47_; 
v___x_47_ = l_Std_Sat_AIG_mkOrCached___redArg(v_inst_1_, v_inst_2_, v_aig_33_, v___x_46_);
return v___x_47_;
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached(lean_object* v_00_u03b1_65_, lean_object* v_inst_66_, lean_object* v_inst_67_, lean_object* v_aig_68_, lean_object* v_input_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Std_Sat_AIG_mkIfCached___redArg(v_inst_66_, v_inst_67_, v_aig_68_, v_input_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___redArg(lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_w_73_, lean_object* v_aig_74_, lean_object* v_curr_75_, lean_object* v_discr_76_, lean_object* v_lhs_77_, lean_object* v_rhs_78_, lean_object* v_s_79_){
_start:
{
lean_object* v___y_81_; lean_object* v___y_82_; uint8_t v___x_106_; lean_object* v___y_108_; 
v___x_106_ = lean_nat_dec_lt(v_curr_75_, v_w_73_);
if (v___x_106_ == 0)
{
lean_object* v___x_118_; 
lean_dec_ref(v_discr_76_);
lean_dec(v_curr_75_);
lean_dec_ref(v_inst_72_);
lean_dec_ref(v_inst_71_);
v___x_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_118_, 0, v_aig_74_);
lean_ctor_set(v___x_118_, 1, v_s_79_);
return v___x_118_;
}
else
{
lean_object* v_ref_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v_ref_119_ = lean_array_fget_borrowed(v_lhs_77_, v_curr_75_);
v___x_120_ = lean_unsigned_to_nat(1u);
v___x_121_ = lean_nat_shiftr(v_ref_119_, v___x_120_);
v___x_122_ = lean_nat_land(v___x_120_, v_ref_119_);
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = lean_nat_dec_eq(v___x_122_, v___x_123_);
lean_dec(v___x_122_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; 
v___x_125_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_125_, 0, v___x_121_);
lean_ctor_set_uint8(v___x_125_, sizeof(void*)*1, v___x_106_);
v___y_108_ = v___x_125_;
goto v___jp_107_;
}
else
{
uint8_t v___x_126_; lean_object* v___x_127_; 
v___x_126_ = 0;
v___x_127_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_127_, 0, v___x_121_);
lean_ctor_set_uint8(v___x_127_, sizeof(void*)*1, v___x_126_);
v___y_108_ = v___x_127_;
goto v___jp_107_;
}
}
v___jp_80_:
{
lean_object* v_input_83_; lean_object* v_res_84_; lean_object* v_ref_85_; lean_object* v_aig_86_; lean_object* v_gate_87_; uint8_t v_invert_88_; lean_object* v_gate_89_; uint8_t v_invert_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_105_; 
lean_inc_ref(v_discr_76_);
v_input_83_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_input_83_, 0, v_discr_76_);
lean_ctor_set(v_input_83_, 1, v___y_81_);
lean_ctor_set(v_input_83_, 2, v___y_82_);
lean_inc_ref(v_inst_72_);
lean_inc_ref(v_inst_71_);
v_res_84_ = l_Std_Sat_AIG_mkIfCached___redArg(v_inst_71_, v_inst_72_, v_aig_74_, v_input_83_);
v_ref_85_ = lean_ctor_get(v_res_84_, 1);
lean_inc_ref(v_ref_85_);
v_aig_86_ = lean_ctor_get(v_res_84_, 0);
lean_inc_ref(v_aig_86_);
lean_dec_ref(v_res_84_);
v_gate_87_ = lean_ctor_get(v_discr_76_, 0);
lean_inc(v_gate_87_);
v_invert_88_ = lean_ctor_get_uint8(v_discr_76_, sizeof(void*)*1);
lean_dec_ref(v_discr_76_);
v_gate_89_ = lean_ctor_get(v_ref_85_, 0);
v_invert_90_ = lean_ctor_get_uint8(v_ref_85_, sizeof(void*)*1);
v_isSharedCheck_105_ = !lean_is_exclusive(v_ref_85_);
if (v_isSharedCheck_105_ == 0)
{
v___x_92_ = v_ref_85_;
v_isShared_93_ = v_isSharedCheck_105_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_gate_89_);
lean_dec(v_ref_85_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_105_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v_discr_95_; 
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 0, v_gate_87_);
v_discr_95_ = v___x_92_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_gate_87_);
v_discr_95_ = v_reuseFailAlloc_104_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v_s_102_; 
lean_ctor_set_uint8(v_discr_95_, sizeof(void*)*1, v_invert_88_);
v___x_96_ = lean_unsigned_to_nat(1u);
v___x_97_ = lean_nat_add(v_curr_75_, v___x_96_);
lean_dec(v_curr_75_);
v___x_98_ = lean_unsigned_to_nat(2u);
v___x_99_ = lean_nat_mul(v_gate_89_, v___x_98_);
lean_dec(v_gate_89_);
v___x_100_ = l_Bool_toNat(v_invert_90_);
v___x_101_ = lean_nat_lor(v___x_99_, v___x_100_);
lean_dec(v___x_100_);
lean_dec(v___x_99_);
v_s_102_ = lean_array_push(v_s_79_, v___x_101_);
v_aig_74_ = v_aig_86_;
v_curr_75_ = v___x_97_;
v_discr_76_ = v_discr_95_;
v_s_79_ = v_s_102_;
goto _start;
}
}
}
v___jp_107_:
{
lean_object* v_ref_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v_ref_109_ = lean_array_fget_borrowed(v_rhs_78_, v_curr_75_);
v___x_110_ = lean_unsigned_to_nat(1u);
v___x_111_ = lean_nat_shiftr(v_ref_109_, v___x_110_);
v___x_112_ = lean_nat_land(v___x_110_, v_ref_109_);
v___x_113_ = lean_unsigned_to_nat(0u);
v___x_114_ = lean_nat_dec_eq(v___x_112_, v___x_113_);
lean_dec(v___x_112_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; 
v___x_115_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_115_, 0, v___x_111_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*1, v___x_106_);
v___y_81_ = v___y_108_;
v___y_82_ = v___x_115_;
goto v___jp_80_;
}
else
{
uint8_t v___x_116_; lean_object* v___x_117_; 
v___x_116_ = 0;
v___x_117_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_117_, 0, v___x_111_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*1, v___x_116_);
v___y_81_ = v___y_108_;
v___y_82_ = v___x_117_;
goto v___jp_80_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___redArg___boxed(lean_object* v_inst_128_, lean_object* v_inst_129_, lean_object* v_w_130_, lean_object* v_aig_131_, lean_object* v_curr_132_, lean_object* v_discr_133_, lean_object* v_lhs_134_, lean_object* v_rhs_135_, lean_object* v_s_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Std_Sat_AIG_RefVec_ite_go___redArg(v_inst_128_, v_inst_129_, v_w_130_, v_aig_131_, v_curr_132_, v_discr_133_, v_lhs_134_, v_rhs_135_, v_s_136_);
lean_dec_ref(v_rhs_135_);
lean_dec_ref(v_lhs_134_);
lean_dec(v_w_130_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go(lean_object* v_00_u03b1_138_, lean_object* v_inst_139_, lean_object* v_inst_140_, lean_object* v_w_141_, lean_object* v_aig_142_, lean_object* v_curr_143_, lean_object* v_hcurr_144_, lean_object* v_discr_145_, lean_object* v_lhs_146_, lean_object* v_rhs_147_, lean_object* v_s_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Std_Sat_AIG_RefVec_ite_go___redArg(v_inst_139_, v_inst_140_, v_w_141_, v_aig_142_, v_curr_143_, v_discr_145_, v_lhs_146_, v_rhs_147_, v_s_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___boxed(lean_object* v_00_u03b1_150_, lean_object* v_inst_151_, lean_object* v_inst_152_, lean_object* v_w_153_, lean_object* v_aig_154_, lean_object* v_curr_155_, lean_object* v_hcurr_156_, lean_object* v_discr_157_, lean_object* v_lhs_158_, lean_object* v_rhs_159_, lean_object* v_s_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Std_Sat_AIG_RefVec_ite_go(v_00_u03b1_150_, v_inst_151_, v_inst_152_, v_w_153_, v_aig_154_, v_curr_155_, v_hcurr_156_, v_discr_157_, v_lhs_158_, v_rhs_159_, v_s_160_);
lean_dec_ref(v_rhs_159_);
lean_dec_ref(v_lhs_158_);
lean_dec(v_w_153_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___redArg(lean_object* v_inst_162_, lean_object* v_inst_163_, lean_object* v_w_164_, lean_object* v_aig_165_, lean_object* v_input_166_){
_start:
{
lean_object* v_discr_167_; lean_object* v_lhs_168_; lean_object* v_rhs_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_discr_167_ = lean_ctor_get(v_input_166_, 0);
lean_inc_ref(v_discr_167_);
v_lhs_168_ = lean_ctor_get(v_input_166_, 1);
lean_inc_ref(v_lhs_168_);
v_rhs_169_ = lean_ctor_get(v_input_166_, 2);
lean_inc_ref(v_rhs_169_);
lean_dec_ref(v_input_166_);
v___x_170_ = lean_unsigned_to_nat(0u);
v___x_171_ = lean_mk_empty_array_with_capacity(v_w_164_);
v___x_172_ = l_Std_Sat_AIG_RefVec_ite_go___redArg(v_inst_162_, v_inst_163_, v_w_164_, v_aig_165_, v___x_170_, v_discr_167_, v_lhs_168_, v_rhs_169_, v___x_171_);
lean_dec_ref(v_rhs_169_);
lean_dec_ref(v_lhs_168_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___redArg___boxed(lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_w_175_, lean_object* v_aig_176_, lean_object* v_input_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_173_, v_inst_174_, v_w_175_, v_aig_176_, v_input_177_);
lean_dec(v_w_175_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite(lean_object* v_00_u03b1_179_, lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_w_182_, lean_object* v_aig_183_, lean_object* v_input_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_180_, v_inst_181_, v_w_182_, v_aig_183_, v_input_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___boxed(lean_object* v_00_u03b1_186_, lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_w_189_, lean_object* v_aig_190_, lean_object* v_input_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Std_Sat_AIG_RefVec_ite(v_00_u03b1_186_, v_inst_187_, v_inst_188_, v_w_189_, v_aig_190_, v_input_191_);
lean_dec(v_w_189_);
return v_res_192_;
}
}
lean_object* runtime_initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_AIG_If(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sat_AIG_If(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_If(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_AIG_If(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sat_AIG_If(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sat_AIG_If(builtin);
}
#ifdef __cplusplus
}
#endif
