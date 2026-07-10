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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Std_Sat_AIG_mkGateCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_bool_xor(uint8_t, uint8_t);
lean_object* l_Std_Sat_AIG_mkOrCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_bool_to_nat(uint8_t);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_If_0__Std_Sat_AIG_RefVec_ite_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_If_0__Std_Sat_AIG_RefVec_ite_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_If_0__Std_Sat_AIG_RefVec_ite_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_aig_3_, lean_object* v_input_4_){
_start:
{
lean_object* v_discr_5_; lean_object* v_lhs_6_; lean_object* v_rhs_7_; lean_object* v___x_8_; lean_object* v_res_9_; lean_object* v_aig_10_; lean_object* v_ref_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_58_; 
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
v_isSharedCheck_58_ = !lean_is_exclusive(v_res_9_);
if (v_isSharedCheck_58_ == 0)
{
v___x_13_ = v_res_9_;
v_isShared_14_ = v_isSharedCheck_58_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_ref_11_);
lean_inc(v_aig_10_);
lean_dec(v_res_9_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_58_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v_gate_15_; uint8_t v_invert_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_57_; 
v_gate_15_ = lean_ctor_get(v_discr_5_, 0);
v_invert_16_ = lean_ctor_get_uint8(v_discr_5_, sizeof(void*)*1);
v_isSharedCheck_57_ = !lean_is_exclusive(v_discr_5_);
if (v_isSharedCheck_57_ == 0)
{
v___x_18_ = v_discr_5_;
v_isShared_19_ = v_isSharedCheck_57_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_gate_15_);
lean_dec(v_discr_5_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_57_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
lean_object* v_gate_20_; uint8_t v_invert_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_56_; 
v_gate_20_ = lean_ctor_get(v_rhs_7_, 0);
v_invert_21_ = lean_ctor_get_uint8(v_rhs_7_, sizeof(void*)*1);
v_isSharedCheck_56_ = !lean_is_exclusive(v_rhs_7_);
if (v_isSharedCheck_56_ == 0)
{
v___x_23_ = v_rhs_7_;
v_isShared_24_ = v_isSharedCheck_56_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_gate_20_);
lean_dec(v_rhs_7_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_56_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
uint8_t v___x_25_; uint8_t v___x_26_; lean_object* v_notDiscr_28_; 
v___x_25_ = 1;
v___x_26_ = lean_bool_xor(v___x_25_, v_invert_16_);
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 0, v_gate_15_);
v_notDiscr_28_ = v___x_23_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v_gate_15_);
v_notDiscr_28_ = v_reuseFailAlloc_55_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
lean_object* v___x_30_; 
lean_ctor_set_uint8(v_notDiscr_28_, sizeof(void*)*1, v___x_26_);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 0, v_gate_20_);
v___x_30_ = v___x_18_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v_gate_20_);
v___x_30_ = v_reuseFailAlloc_54_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
lean_object* v___x_32_; 
lean_ctor_set_uint8(v___x_30_, sizeof(void*)*1, v_invert_21_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 1, v___x_30_);
lean_ctor_set(v___x_13_, 0, v_notDiscr_28_);
v___x_32_ = v___x_13_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v_notDiscr_28_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v___x_30_);
v___x_32_ = v_reuseFailAlloc_53_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
lean_object* v_res_33_; lean_object* v_aig_34_; lean_object* v_ref_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_52_; 
lean_inc_ref(v_inst_2_);
lean_inc_ref(v_inst_1_);
v_res_33_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_1_, v_inst_2_, v_aig_10_, v___x_32_);
v_aig_34_ = lean_ctor_get(v_res_33_, 0);
v_ref_35_ = lean_ctor_get(v_res_33_, 1);
v_isSharedCheck_52_ = !lean_is_exclusive(v_res_33_);
if (v_isSharedCheck_52_ == 0)
{
v___x_37_ = v_res_33_;
v_isShared_38_ = v_isSharedCheck_52_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_ref_35_);
lean_inc(v_aig_34_);
lean_dec(v_res_33_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_52_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v_gate_39_; uint8_t v_invert_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_51_; 
v_gate_39_ = lean_ctor_get(v_ref_11_, 0);
v_invert_40_ = lean_ctor_get_uint8(v_ref_11_, sizeof(void*)*1);
v_isSharedCheck_51_ = !lean_is_exclusive(v_ref_11_);
if (v_isSharedCheck_51_ == 0)
{
v___x_42_ = v_ref_11_;
v_isShared_43_ = v_isSharedCheck_51_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_gate_39_);
lean_dec(v_ref_11_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_51_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v_lhsRef_45_; 
if (v_isShared_43_ == 0)
{
v_lhsRef_45_ = v___x_42_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v_gate_39_);
lean_ctor_set_uint8(v_reuseFailAlloc_50_, sizeof(void*)*1, v_invert_40_);
v_lhsRef_45_ = v_reuseFailAlloc_50_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
lean_object* v___x_47_; 
if (v_isShared_38_ == 0)
{
lean_ctor_set(v___x_37_, 0, v_lhsRef_45_);
v___x_47_ = v___x_37_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_lhsRef_45_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v_ref_35_);
v___x_47_ = v_reuseFailAlloc_49_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
lean_object* v___x_48_; 
v___x_48_ = l_Std_Sat_AIG_mkOrCached___redArg(v_inst_1_, v_inst_2_, v_aig_34_, v___x_47_);
return v___x_48_;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached(lean_object* v_00_u03b1_59_, lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_aig_62_, lean_object* v_input_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Std_Sat_AIG_mkIfCached___redArg(v_inst_60_, v_inst_61_, v_aig_62_, v_input_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___redArg(lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_w_67_, lean_object* v_aig_68_, lean_object* v_curr_69_, lean_object* v_discr_70_, lean_object* v_lhs_71_, lean_object* v_rhs_72_, lean_object* v_s_73_){
_start:
{
uint8_t v___x_74_; 
v___x_74_ = lean_nat_dec_lt(v_curr_69_, v_w_67_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; 
lean_dec_ref(v_discr_70_);
lean_dec(v_curr_69_);
lean_dec_ref(v_inst_66_);
lean_dec_ref(v_inst_65_);
v___x_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_75_, 0, v_aig_68_);
lean_ctor_set(v___x_75_, 1, v_s_73_);
return v___x_75_;
}
else
{
lean_object* v_ref_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; lean_object* v___x_83_; lean_object* v_ref_84_; lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v_input_90_; lean_object* v_res_91_; lean_object* v_ref_92_; lean_object* v_aig_93_; lean_object* v_gate_94_; uint8_t v_invert_95_; lean_object* v_gate_96_; uint8_t v_invert_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_111_; 
v_ref_76_ = lean_array_fget_borrowed(v_lhs_71_, v_curr_69_);
v___x_77_ = lean_unsigned_to_nat(1u);
v___x_78_ = lean_nat_land(v___x_77_, v_ref_76_);
v___x_79_ = lean_unsigned_to_nat(0u);
v___x_80_ = lean_nat_dec_eq(v___x_78_, v___x_79_);
lean_dec(v___x_78_);
v___x_81_ = lean_nat_shiftr(v_ref_76_, v___x_77_);
v___x_82_ = lean_bool_not(v___x_80_);
v___x_83_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_83_, 0, v___x_81_);
lean_ctor_set_uint8(v___x_83_, sizeof(void*)*1, v___x_82_);
v_ref_84_ = lean_array_fget_borrowed(v_rhs_72_, v_curr_69_);
v___x_85_ = lean_nat_shiftr(v_ref_84_, v___x_77_);
v___x_86_ = lean_nat_land(v___x_77_, v_ref_84_);
v___x_87_ = lean_nat_dec_eq(v___x_86_, v___x_79_);
lean_dec(v___x_86_);
v___x_88_ = lean_bool_not(v___x_87_);
v___x_89_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_89_, 0, v___x_85_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*1, v___x_88_);
lean_inc_ref(v_discr_70_);
v_input_90_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_input_90_, 0, v_discr_70_);
lean_ctor_set(v_input_90_, 1, v___x_83_);
lean_ctor_set(v_input_90_, 2, v___x_89_);
lean_inc_ref(v_inst_66_);
lean_inc_ref(v_inst_65_);
v_res_91_ = l_Std_Sat_AIG_mkIfCached___redArg(v_inst_65_, v_inst_66_, v_aig_68_, v_input_90_);
v_ref_92_ = lean_ctor_get(v_res_91_, 1);
lean_inc_ref(v_ref_92_);
v_aig_93_ = lean_ctor_get(v_res_91_, 0);
lean_inc_ref(v_aig_93_);
lean_dec_ref(v_res_91_);
v_gate_94_ = lean_ctor_get(v_discr_70_, 0);
lean_inc(v_gate_94_);
v_invert_95_ = lean_ctor_get_uint8(v_discr_70_, sizeof(void*)*1);
lean_dec_ref(v_discr_70_);
v_gate_96_ = lean_ctor_get(v_ref_92_, 0);
v_invert_97_ = lean_ctor_get_uint8(v_ref_92_, sizeof(void*)*1);
v_isSharedCheck_111_ = !lean_is_exclusive(v_ref_92_);
if (v_isSharedCheck_111_ == 0)
{
v___x_99_ = v_ref_92_;
v_isShared_100_ = v_isSharedCheck_111_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_gate_96_);
lean_dec(v_ref_92_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_111_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v_discr_102_; 
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 0, v_gate_94_);
v_discr_102_ = v___x_99_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_gate_94_);
v_discr_102_ = v_reuseFailAlloc_110_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v_s_108_; 
lean_ctor_set_uint8(v_discr_102_, sizeof(void*)*1, v_invert_95_);
v___x_103_ = lean_nat_add(v_curr_69_, v___x_77_);
lean_dec(v_curr_69_);
v___x_104_ = lean_unsigned_to_nat(2u);
v___x_105_ = lean_nat_mul(v_gate_96_, v___x_104_);
lean_dec(v_gate_96_);
v___x_106_ = lean_bool_to_nat(v_invert_97_);
v___x_107_ = lean_nat_lor(v___x_105_, v___x_106_);
lean_dec(v___x_105_);
v_s_108_ = lean_array_push(v_s_73_, v___x_107_);
v_aig_68_ = v_aig_93_;
v_curr_69_ = v___x_103_;
v_discr_70_ = v_discr_102_;
v_s_73_ = v_s_108_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___redArg___boxed(lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_w_114_, lean_object* v_aig_115_, lean_object* v_curr_116_, lean_object* v_discr_117_, lean_object* v_lhs_118_, lean_object* v_rhs_119_, lean_object* v_s_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Std_Sat_AIG_RefVec_ite_go___redArg(v_inst_112_, v_inst_113_, v_w_114_, v_aig_115_, v_curr_116_, v_discr_117_, v_lhs_118_, v_rhs_119_, v_s_120_);
lean_dec_ref(v_rhs_119_);
lean_dec_ref(v_lhs_118_);
lean_dec(v_w_114_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go(lean_object* v_00_u03b1_122_, lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_w_125_, lean_object* v_aig_126_, lean_object* v_curr_127_, lean_object* v_hcurr_128_, lean_object* v_discr_129_, lean_object* v_lhs_130_, lean_object* v_rhs_131_, lean_object* v_s_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Std_Sat_AIG_RefVec_ite_go___redArg(v_inst_123_, v_inst_124_, v_w_125_, v_aig_126_, v_curr_127_, v_discr_129_, v_lhs_130_, v_rhs_131_, v_s_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___boxed(lean_object* v_00_u03b1_134_, lean_object* v_inst_135_, lean_object* v_inst_136_, lean_object* v_w_137_, lean_object* v_aig_138_, lean_object* v_curr_139_, lean_object* v_hcurr_140_, lean_object* v_discr_141_, lean_object* v_lhs_142_, lean_object* v_rhs_143_, lean_object* v_s_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Std_Sat_AIG_RefVec_ite_go(v_00_u03b1_134_, v_inst_135_, v_inst_136_, v_w_137_, v_aig_138_, v_curr_139_, v_hcurr_140_, v_discr_141_, v_lhs_142_, v_rhs_143_, v_s_144_);
lean_dec_ref(v_rhs_143_);
lean_dec_ref(v_lhs_142_);
lean_dec(v_w_137_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___redArg(lean_object* v_inst_146_, lean_object* v_inst_147_, lean_object* v_w_148_, lean_object* v_aig_149_, lean_object* v_input_150_){
_start:
{
lean_object* v_discr_151_; lean_object* v_lhs_152_; lean_object* v_rhs_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v_discr_151_ = lean_ctor_get(v_input_150_, 0);
lean_inc_ref(v_discr_151_);
v_lhs_152_ = lean_ctor_get(v_input_150_, 1);
lean_inc_ref(v_lhs_152_);
v_rhs_153_ = lean_ctor_get(v_input_150_, 2);
lean_inc_ref(v_rhs_153_);
lean_dec_ref(v_input_150_);
v___x_154_ = lean_unsigned_to_nat(0u);
v___x_155_ = lean_mk_empty_array_with_capacity(v_w_148_);
v___x_156_ = l_Std_Sat_AIG_RefVec_ite_go___redArg(v_inst_146_, v_inst_147_, v_w_148_, v_aig_149_, v___x_154_, v_discr_151_, v_lhs_152_, v_rhs_153_, v___x_155_);
lean_dec_ref(v_rhs_153_);
lean_dec_ref(v_lhs_152_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___redArg___boxed(lean_object* v_inst_157_, lean_object* v_inst_158_, lean_object* v_w_159_, lean_object* v_aig_160_, lean_object* v_input_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_157_, v_inst_158_, v_w_159_, v_aig_160_, v_input_161_);
lean_dec(v_w_159_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite(lean_object* v_00_u03b1_163_, lean_object* v_inst_164_, lean_object* v_inst_165_, lean_object* v_w_166_, lean_object* v_aig_167_, lean_object* v_input_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Std_Sat_AIG_RefVec_ite___redArg(v_inst_164_, v_inst_165_, v_w_166_, v_aig_167_, v_input_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___boxed(lean_object* v_00_u03b1_170_, lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_w_173_, lean_object* v_aig_174_, lean_object* v_input_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Std_Sat_AIG_RefVec_ite(v_00_u03b1_170_, v_inst_171_, v_inst_172_, v_w_173_, v_aig_174_, v_input_175_);
lean_dec(v_w_173_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_If_0__Std_Sat_AIG_RefVec_ite_match__1_splitter___redArg(lean_object* v_input_177_, lean_object* v_h__1_178_){
_start:
{
lean_object* v_discr_179_; lean_object* v_lhs_180_; lean_object* v_rhs_181_; lean_object* v___x_182_; 
v_discr_179_ = lean_ctor_get(v_input_177_, 0);
lean_inc_ref(v_discr_179_);
v_lhs_180_ = lean_ctor_get(v_input_177_, 1);
lean_inc_ref(v_lhs_180_);
v_rhs_181_ = lean_ctor_get(v_input_177_, 2);
lean_inc_ref(v_rhs_181_);
lean_dec_ref(v_input_177_);
v___x_182_ = lean_apply_3(v_h__1_178_, v_discr_179_, v_lhs_180_, v_rhs_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_If_0__Std_Sat_AIG_RefVec_ite_match__1_splitter(lean_object* v_00_u03b1_183_, lean_object* v_inst_184_, lean_object* v_inst_185_, lean_object* v_w_186_, lean_object* v_aig_187_, lean_object* v_motive_188_, lean_object* v_input_189_, lean_object* v_h__1_190_){
_start:
{
lean_object* v_discr_191_; lean_object* v_lhs_192_; lean_object* v_rhs_193_; lean_object* v___x_194_; 
v_discr_191_ = lean_ctor_get(v_input_189_, 0);
lean_inc_ref(v_discr_191_);
v_lhs_192_ = lean_ctor_get(v_input_189_, 1);
lean_inc_ref(v_lhs_192_);
v_rhs_193_ = lean_ctor_get(v_input_189_, 2);
lean_inc_ref(v_rhs_193_);
lean_dec_ref(v_input_189_);
v___x_194_ = lean_apply_3(v_h__1_190_, v_discr_191_, v_lhs_192_, v_rhs_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_If_0__Std_Sat_AIG_RefVec_ite_match__1_splitter___boxed(lean_object* v_00_u03b1_195_, lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_w_198_, lean_object* v_aig_199_, lean_object* v_motive_200_, lean_object* v_input_201_, lean_object* v_h__1_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l___private_Std_Sat_AIG_If_0__Std_Sat_AIG_RefVec_ite_match__1_splitter(v_00_u03b1_195_, v_inst_196_, v_inst_197_, v_w_198_, v_aig_199_, v_motive_200_, v_input_201_, v_h__1_202_);
lean_dec_ref(v_aig_199_);
lean_dec(v_w_198_);
lean_dec_ref(v_inst_197_);
lean_dec_ref(v_inst_196_);
return v_res_203_;
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
