// Lean compiler output
// Module: Std.Sat.AIG.RefVec
// Imports: public import Std.Sat.AIG.CachedGatesLemmas public import Init.Data.Vector.Lemmas import Init.ByCases import Init.Omega
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_bool_to_nat(uint8_t);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Std_Sat_AIG_RefVec_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Sat_AIG_RefVec_empty___closed__0 = (const lean_object*)&l_Std_Sat_AIG_RefVec_empty___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_empty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_empty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast_x27___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_get___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_get___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_push___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_push(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_push___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_get_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_get_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_get_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_append___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_append(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_append___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_countKnown_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_countKnown_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryRefVec_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryRefVec_cast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryRefVec_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_BinaryRefVec_cast_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_BinaryRefVec_cast_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_BinaryRefVec_cast_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_empty(lean_object* v_00_u03b1_3_, lean_object* v_inst_4_, lean_object* v_inst_5_, lean_object* v_aig_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = ((lean_object*)(l_Std_Sat_AIG_RefVec_empty___closed__0));
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_empty___boxed(lean_object* v_00_u03b1_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_aig_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_Sat_AIG_RefVec_empty(v_00_u03b1_8_, v_inst_9_, v_inst_10_, v_aig_11_);
lean_dec_ref(v_aig_11_);
lean_dec_ref(v_inst_10_);
lean_dec_ref(v_inst_9_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___redArg(lean_object* v_c_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_mk_empty_array_with_capacity(v_c_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___redArg___boxed(lean_object* v_c_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Std_Sat_AIG_RefVec_emptyWithCapacity___redArg(v_c_15_);
lean_dec(v_c_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity(lean_object* v_00_u03b1_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_aig_20_, lean_object* v_c_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lean_mk_empty_array_with_capacity(v_c_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___boxed(lean_object* v_00_u03b1_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_aig_26_, lean_object* v_c_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Std_Sat_AIG_RefVec_emptyWithCapacity(v_00_u03b1_23_, v_inst_24_, v_inst_25_, v_aig_26_, v_c_27_);
lean_dec(v_c_27_);
lean_dec_ref(v_aig_26_);
lean_dec_ref(v_inst_25_);
lean_dec_ref(v_inst_24_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast_x27___redArg(lean_object* v_s_29_){
_start:
{
lean_inc_ref(v_s_29_);
return v_s_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast_x27___redArg___boxed(lean_object* v_s_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Std_Sat_AIG_RefVec_cast_x27___redArg(v_s_30_);
lean_dec_ref(v_s_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast_x27(lean_object* v_00_u03b1_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_len_35_, lean_object* v_aig1_36_, lean_object* v_aig2_37_, lean_object* v_s_38_, lean_object* v_h_39_){
_start:
{
lean_inc_ref(v_s_38_);
return v_s_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast_x27___boxed(lean_object* v_00_u03b1_40_, lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_len_43_, lean_object* v_aig1_44_, lean_object* v_aig2_45_, lean_object* v_s_46_, lean_object* v_h_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Std_Sat_AIG_RefVec_cast_x27(v_00_u03b1_40_, v_inst_41_, v_inst_42_, v_len_43_, v_aig1_44_, v_aig2_45_, v_s_46_, v_h_47_);
lean_dec_ref(v_s_46_);
lean_dec_ref(v_aig2_45_);
lean_dec_ref(v_aig1_44_);
lean_dec(v_len_43_);
lean_dec_ref(v_inst_42_);
lean_dec_ref(v_inst_41_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast___redArg(lean_object* v_s_49_){
_start:
{
lean_inc_ref(v_s_49_);
return v_s_49_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast___redArg___boxed(lean_object* v_s_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Std_Sat_AIG_RefVec_cast___redArg(v_s_50_);
lean_dec_ref(v_s_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast(lean_object* v_00_u03b1_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_len_55_, lean_object* v_aig1_56_, lean_object* v_aig2_57_, lean_object* v_s_58_, lean_object* v_h_59_){
_start:
{
lean_inc_ref(v_s_58_);
return v_s_58_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast___boxed(lean_object* v_00_u03b1_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_len_63_, lean_object* v_aig1_64_, lean_object* v_aig2_65_, lean_object* v_s_66_, lean_object* v_h_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Std_Sat_AIG_RefVec_cast(v_00_u03b1_60_, v_inst_61_, v_inst_62_, v_len_63_, v_aig1_64_, v_aig2_65_, v_s_66_, v_h_67_);
lean_dec_ref(v_s_66_);
lean_dec_ref(v_aig2_65_);
lean_dec_ref(v_aig1_64_);
lean_dec(v_len_63_);
lean_dec_ref(v_inst_62_);
lean_dec_ref(v_inst_61_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_get___redArg(lean_object* v_s_69_, lean_object* v_idx_70_){
_start:
{
lean_object* v_ref_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; uint8_t v___x_77_; lean_object* v___x_78_; 
v_ref_71_ = lean_array_fget_borrowed(v_s_69_, v_idx_70_);
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_nat_shiftr(v_ref_71_, v___x_72_);
v___x_74_ = lean_nat_land(v___x_72_, v_ref_71_);
v___x_75_ = lean_unsigned_to_nat(0u);
v___x_76_ = lean_nat_dec_eq(v___x_74_, v___x_75_);
lean_dec(v___x_74_);
v___x_77_ = lean_bool_not(v___x_76_);
v___x_78_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_78_, 0, v___x_73_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*1, v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_get___redArg___boxed(lean_object* v_s_79_, lean_object* v_idx_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Std_Sat_AIG_RefVec_get___redArg(v_s_79_, v_idx_80_);
lean_dec(v_idx_80_);
lean_dec_ref(v_s_79_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_get(lean_object* v_00_u03b1_82_, lean_object* v_inst_83_, lean_object* v_inst_84_, lean_object* v_aig_85_, lean_object* v_len_86_, lean_object* v_s_87_, lean_object* v_idx_88_, lean_object* v_hidx_89_){
_start:
{
lean_object* v_ref_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; uint8_t v___x_96_; lean_object* v___x_97_; 
v_ref_90_ = lean_array_fget_borrowed(v_s_87_, v_idx_88_);
v___x_91_ = lean_unsigned_to_nat(1u);
v___x_92_ = lean_nat_shiftr(v_ref_90_, v___x_91_);
v___x_93_ = lean_nat_land(v___x_91_, v_ref_90_);
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = lean_nat_dec_eq(v___x_93_, v___x_94_);
lean_dec(v___x_93_);
v___x_96_ = lean_bool_not(v___x_95_);
v___x_97_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_97_, 0, v___x_92_);
lean_ctor_set_uint8(v___x_97_, sizeof(void*)*1, v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_get___boxed(lean_object* v_00_u03b1_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_aig_101_, lean_object* v_len_102_, lean_object* v_s_103_, lean_object* v_idx_104_, lean_object* v_hidx_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Std_Sat_AIG_RefVec_get(v_00_u03b1_98_, v_inst_99_, v_inst_100_, v_aig_101_, v_len_102_, v_s_103_, v_idx_104_, v_hidx_105_);
lean_dec(v_idx_104_);
lean_dec_ref(v_s_103_);
lean_dec(v_len_102_);
lean_dec_ref(v_aig_101_);
lean_dec_ref(v_inst_100_);
lean_dec_ref(v_inst_99_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_push___redArg(lean_object* v_s_107_, lean_object* v_ref_108_){
_start:
{
lean_object* v_gate_109_; uint8_t v_invert_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v_gate_109_ = lean_ctor_get(v_ref_108_, 0);
v_invert_110_ = lean_ctor_get_uint8(v_ref_108_, sizeof(void*)*1);
v___x_111_ = lean_unsigned_to_nat(2u);
v___x_112_ = lean_nat_mul(v_gate_109_, v___x_111_);
v___x_113_ = lean_bool_to_nat(v_invert_110_);
v___x_114_ = lean_nat_lor(v___x_112_, v___x_113_);
lean_dec(v___x_112_);
v___x_115_ = lean_array_push(v_s_107_, v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_push___redArg___boxed(lean_object* v_s_116_, lean_object* v_ref_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Std_Sat_AIG_RefVec_push___redArg(v_s_116_, v_ref_117_);
lean_dec_ref(v_ref_117_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_push(lean_object* v_00_u03b1_119_, lean_object* v_inst_120_, lean_object* v_inst_121_, lean_object* v_aig_122_, lean_object* v_len_123_, lean_object* v_s_124_, lean_object* v_ref_125_){
_start:
{
lean_object* v_gate_126_; uint8_t v_invert_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v_gate_126_ = lean_ctor_get(v_ref_125_, 0);
v_invert_127_ = lean_ctor_get_uint8(v_ref_125_, sizeof(void*)*1);
v___x_128_ = lean_unsigned_to_nat(2u);
v___x_129_ = lean_nat_mul(v_gate_126_, v___x_128_);
v___x_130_ = lean_bool_to_nat(v_invert_127_);
v___x_131_ = lean_nat_lor(v___x_129_, v___x_130_);
lean_dec(v___x_129_);
v___x_132_ = lean_array_push(v_s_124_, v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_push___boxed(lean_object* v_00_u03b1_133_, lean_object* v_inst_134_, lean_object* v_inst_135_, lean_object* v_aig_136_, lean_object* v_len_137_, lean_object* v_s_138_, lean_object* v_ref_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Std_Sat_AIG_RefVec_push(v_00_u03b1_133_, v_inst_134_, v_inst_135_, v_aig_136_, v_len_137_, v_s_138_, v_ref_139_);
lean_dec_ref(v_ref_139_);
lean_dec(v_len_137_);
lean_dec_ref(v_aig_136_);
lean_dec_ref(v_inst_135_);
lean_dec_ref(v_inst_134_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_get_match__1_splitter___redArg(lean_object* v_s_141_, lean_object* v_h__1_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = lean_apply_2(v_h__1_142_, v_s_141_, lean_box(0));
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_get_match__1_splitter(lean_object* v_00_u03b1_144_, lean_object* v_inst_145_, lean_object* v_inst_146_, lean_object* v_aig_147_, lean_object* v_len_148_, lean_object* v_motive_149_, lean_object* v_s_150_, lean_object* v_h__1_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = lean_apply_2(v_h__1_151_, v_s_150_, lean_box(0));
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_get_match__1_splitter___boxed(lean_object* v_00_u03b1_153_, lean_object* v_inst_154_, lean_object* v_inst_155_, lean_object* v_aig_156_, lean_object* v_len_157_, lean_object* v_motive_158_, lean_object* v_s_159_, lean_object* v_h__1_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_get_match__1_splitter(v_00_u03b1_153_, v_inst_154_, v_inst_155_, v_aig_156_, v_len_157_, v_motive_158_, v_s_159_, v_h__1_160_);
lean_dec(v_len_157_);
lean_dec_ref(v_aig_156_);
lean_dec_ref(v_inst_155_);
lean_dec_ref(v_inst_154_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_append___redArg(lean_object* v_lhs_162_, lean_object* v_rhs_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Array_append___redArg(v_lhs_162_, v_rhs_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_append___redArg___boxed(lean_object* v_lhs_165_, lean_object* v_rhs_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Std_Sat_AIG_RefVec_append___redArg(v_lhs_165_, v_rhs_166_);
lean_dec_ref(v_rhs_166_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_append(lean_object* v_00_u03b1_168_, lean_object* v_inst_169_, lean_object* v_inst_170_, lean_object* v_aig_171_, lean_object* v_lw_172_, lean_object* v_rw_173_, lean_object* v_lhs_174_, lean_object* v_rhs_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Array_append___redArg(v_lhs_174_, v_rhs_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_append___boxed(lean_object* v_00_u03b1_177_, lean_object* v_inst_178_, lean_object* v_inst_179_, lean_object* v_aig_180_, lean_object* v_lw_181_, lean_object* v_rw_182_, lean_object* v_lhs_183_, lean_object* v_rhs_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Std_Sat_AIG_RefVec_append(v_00_u03b1_177_, v_inst_178_, v_inst_179_, v_aig_180_, v_lw_181_, v_rw_182_, v_lhs_183_, v_rhs_184_);
lean_dec_ref(v_rhs_184_);
lean_dec(v_rw_182_);
lean_dec(v_lw_181_);
lean_dec_ref(v_aig_180_);
lean_dec_ref(v_inst_179_);
lean_dec_ref(v_inst_178_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_getD___redArg(lean_object* v_len_186_, lean_object* v_s_187_, lean_object* v_idx_188_, lean_object* v_alt_189_){
_start:
{
uint8_t v___x_190_; 
v___x_190_ = lean_nat_dec_lt(v_idx_188_, v_len_186_);
if (v___x_190_ == 0)
{
lean_inc_ref(v_alt_189_);
return v_alt_189_;
}
else
{
lean_object* v_ref_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; uint8_t v___x_197_; lean_object* v___x_198_; 
v_ref_191_ = lean_array_fget_borrowed(v_s_187_, v_idx_188_);
v___x_192_ = lean_unsigned_to_nat(1u);
v___x_193_ = lean_nat_shiftr(v_ref_191_, v___x_192_);
v___x_194_ = lean_nat_land(v___x_192_, v_ref_191_);
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = lean_nat_dec_eq(v___x_194_, v___x_195_);
lean_dec(v___x_194_);
v___x_197_ = lean_bool_not(v___x_196_);
v___x_198_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_198_, 0, v___x_193_);
lean_ctor_set_uint8(v___x_198_, sizeof(void*)*1, v___x_197_);
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_getD___redArg___boxed(lean_object* v_len_199_, lean_object* v_s_200_, lean_object* v_idx_201_, lean_object* v_alt_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Std_Sat_AIG_RefVec_getD___redArg(v_len_199_, v_s_200_, v_idx_201_, v_alt_202_);
lean_dec_ref(v_alt_202_);
lean_dec(v_idx_201_);
lean_dec_ref(v_s_200_);
lean_dec(v_len_199_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_getD(lean_object* v_00_u03b1_204_, lean_object* v_inst_205_, lean_object* v_inst_206_, lean_object* v_aig_207_, lean_object* v_len_208_, lean_object* v_s_209_, lean_object* v_idx_210_, lean_object* v_alt_211_){
_start:
{
uint8_t v___x_212_; 
v___x_212_ = lean_nat_dec_lt(v_idx_210_, v_len_208_);
if (v___x_212_ == 0)
{
lean_inc_ref(v_alt_211_);
return v_alt_211_;
}
else
{
lean_object* v_ref_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v___x_218_; uint8_t v___x_219_; lean_object* v___x_220_; 
v_ref_213_ = lean_array_fget_borrowed(v_s_209_, v_idx_210_);
v___x_214_ = lean_unsigned_to_nat(1u);
v___x_215_ = lean_nat_shiftr(v_ref_213_, v___x_214_);
v___x_216_ = lean_nat_land(v___x_214_, v_ref_213_);
v___x_217_ = lean_unsigned_to_nat(0u);
v___x_218_ = lean_nat_dec_eq(v___x_216_, v___x_217_);
lean_dec(v___x_216_);
v___x_219_ = lean_bool_not(v___x_218_);
v___x_220_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_220_, 0, v___x_215_);
lean_ctor_set_uint8(v___x_220_, sizeof(void*)*1, v___x_219_);
return v___x_220_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_getD___boxed(lean_object* v_00_u03b1_221_, lean_object* v_inst_222_, lean_object* v_inst_223_, lean_object* v_aig_224_, lean_object* v_len_225_, lean_object* v_s_226_, lean_object* v_idx_227_, lean_object* v_alt_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Std_Sat_AIG_RefVec_getD(v_00_u03b1_221_, v_inst_222_, v_inst_223_, v_aig_224_, v_len_225_, v_s_226_, v_idx_227_, v_alt_228_);
lean_dec_ref(v_alt_228_);
lean_dec(v_idx_227_);
lean_dec_ref(v_s_226_);
lean_dec(v_len_225_);
lean_dec_ref(v_aig_224_);
lean_dec_ref(v_inst_223_);
lean_dec_ref(v_inst_222_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown_go___redArg(lean_object* v_len_230_, lean_object* v_aig_231_, lean_object* v_s_232_, lean_object* v_idx_233_, lean_object* v_acc_234_){
_start:
{
uint8_t v___x_235_; 
v___x_235_ = lean_nat_dec_lt(v_idx_233_, v_len_230_);
if (v___x_235_ == 0)
{
lean_dec(v_idx_233_);
return v_acc_234_;
}
else
{
lean_object* v_decls_236_; lean_object* v_ref_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v_decl_240_; 
v_decls_236_ = lean_ctor_get(v_aig_231_, 0);
v_ref_237_ = lean_array_fget_borrowed(v_s_232_, v_idx_233_);
v___x_238_ = lean_unsigned_to_nat(1u);
v___x_239_ = lean_nat_shiftr(v_ref_237_, v___x_238_);
v_decl_240_ = lean_array_fget_borrowed(v_decls_236_, v___x_239_);
lean_dec(v___x_239_);
if (lean_obj_tag(v_decl_240_) == 0)
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = lean_nat_add(v_idx_233_, v___x_238_);
lean_dec(v_idx_233_);
v___x_242_ = lean_nat_add(v_acc_234_, v___x_238_);
lean_dec(v_acc_234_);
v_idx_233_ = v___x_241_;
v_acc_234_ = v___x_242_;
goto _start;
}
else
{
lean_object* v___x_244_; 
v___x_244_ = lean_nat_add(v_idx_233_, v___x_238_);
lean_dec(v_idx_233_);
v_idx_233_ = v___x_244_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown_go___redArg___boxed(lean_object* v_len_246_, lean_object* v_aig_247_, lean_object* v_s_248_, lean_object* v_idx_249_, lean_object* v_acc_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Std_Sat_AIG_RefVec_countKnown_go___redArg(v_len_246_, v_aig_247_, v_s_248_, v_idx_249_, v_acc_250_);
lean_dec_ref(v_s_248_);
lean_dec_ref(v_aig_247_);
lean_dec(v_len_246_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown_go(lean_object* v_00_u03b1_252_, lean_object* v_inst_253_, lean_object* v_inst_254_, lean_object* v_len_255_, lean_object* v_aig_256_, lean_object* v_s_257_, lean_object* v_idx_258_, lean_object* v_acc_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Std_Sat_AIG_RefVec_countKnown_go___redArg(v_len_255_, v_aig_256_, v_s_257_, v_idx_258_, v_acc_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown_go___boxed(lean_object* v_00_u03b1_261_, lean_object* v_inst_262_, lean_object* v_inst_263_, lean_object* v_len_264_, lean_object* v_aig_265_, lean_object* v_s_266_, lean_object* v_idx_267_, lean_object* v_acc_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Std_Sat_AIG_RefVec_countKnown_go(v_00_u03b1_261_, v_inst_262_, v_inst_263_, v_len_264_, v_aig_265_, v_s_266_, v_idx_267_, v_acc_268_);
lean_dec_ref(v_s_266_);
lean_dec_ref(v_aig_265_);
lean_dec(v_len_264_);
lean_dec_ref(v_inst_263_);
lean_dec_ref(v_inst_262_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_countKnown_go_match__1_splitter___redArg(lean_object* v_decl_270_, lean_object* v_h__1_271_, lean_object* v_h__2_272_){
_start:
{
if (lean_obj_tag(v_decl_270_) == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; 
lean_dec(v_h__2_272_);
v___x_273_ = lean_box(0);
v___x_274_ = lean_apply_1(v_h__1_271_, v___x_273_);
return v___x_274_;
}
else
{
lean_object* v___x_275_; 
lean_dec(v_h__1_271_);
v___x_275_ = lean_apply_2(v_h__2_272_, v_decl_270_, lean_box(0));
return v___x_275_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_countKnown_go_match__1_splitter(lean_object* v_00_u03b1_276_, lean_object* v_motive_277_, lean_object* v_decl_278_, lean_object* v_h__1_279_, lean_object* v_h__2_280_){
_start:
{
if (lean_obj_tag(v_decl_278_) == 0)
{
lean_object* v___x_281_; lean_object* v___x_282_; 
lean_dec(v_h__2_280_);
v___x_281_ = lean_box(0);
v___x_282_ = lean_apply_1(v_h__1_279_, v___x_281_);
return v___x_282_;
}
else
{
lean_object* v___x_283_; 
lean_dec(v_h__1_279_);
v___x_283_ = lean_apply_2(v_h__2_280_, v_decl_278_, lean_box(0));
return v___x_283_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___redArg(lean_object* v_len_284_, lean_object* v_aig_285_, lean_object* v_s_286_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = l_Std_Sat_AIG_RefVec_countKnown_go___redArg(v_len_284_, v_aig_285_, v_s_286_, v___x_287_, v___x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___redArg___boxed(lean_object* v_len_289_, lean_object* v_aig_290_, lean_object* v_s_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Std_Sat_AIG_RefVec_countKnown___redArg(v_len_289_, v_aig_290_, v_s_291_);
lean_dec_ref(v_s_291_);
lean_dec_ref(v_aig_290_);
lean_dec(v_len_289_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown(lean_object* v_00_u03b1_293_, lean_object* v_inst_294_, lean_object* v_inst_295_, lean_object* v_len_296_, lean_object* v_aig_297_, lean_object* v_s_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Std_Sat_AIG_RefVec_countKnown___redArg(v_len_296_, v_aig_297_, v_s_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___boxed(lean_object* v_00_u03b1_300_, lean_object* v_inst_301_, lean_object* v_inst_302_, lean_object* v_len_303_, lean_object* v_aig_304_, lean_object* v_s_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Std_Sat_AIG_RefVec_countKnown(v_00_u03b1_300_, v_inst_301_, v_inst_302_, v_len_303_, v_aig_304_, v_s_305_);
lean_dec_ref(v_s_305_);
lean_dec_ref(v_aig_304_);
lean_dec(v_len_303_);
lean_dec_ref(v_inst_302_);
lean_dec_ref(v_inst_301_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryRefVec_cast___redArg(lean_object* v_s_307_){
_start:
{
lean_object* v_lhs_308_; lean_object* v_rhs_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
v_lhs_308_ = lean_ctor_get(v_s_307_, 0);
v_rhs_309_ = lean_ctor_get(v_s_307_, 1);
v_isSharedCheck_316_ = !lean_is_exclusive(v_s_307_);
if (v_isSharedCheck_316_ == 0)
{
v___x_311_ = v_s_307_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_rhs_309_);
lean_inc(v_lhs_308_);
lean_dec(v_s_307_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_lhs_308_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_rhs_309_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryRefVec_cast(lean_object* v_00_u03b1_317_, lean_object* v_inst_318_, lean_object* v_inst_319_, lean_object* v_len_320_, lean_object* v_aig1_321_, lean_object* v_aig2_322_, lean_object* v_s_323_, lean_object* v_h_324_){
_start:
{
lean_object* v_lhs_325_; lean_object* v_rhs_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
v_lhs_325_ = lean_ctor_get(v_s_323_, 0);
v_rhs_326_ = lean_ctor_get(v_s_323_, 1);
v_isSharedCheck_333_ = !lean_is_exclusive(v_s_323_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v_s_323_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_rhs_326_);
lean_inc(v_lhs_325_);
lean_dec(v_s_323_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_lhs_325_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_rhs_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryRefVec_cast___boxed(lean_object* v_00_u03b1_334_, lean_object* v_inst_335_, lean_object* v_inst_336_, lean_object* v_len_337_, lean_object* v_aig1_338_, lean_object* v_aig2_339_, lean_object* v_s_340_, lean_object* v_h_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Std_Sat_AIG_BinaryRefVec_cast(v_00_u03b1_334_, v_inst_335_, v_inst_336_, v_len_337_, v_aig1_338_, v_aig2_339_, v_s_340_, v_h_341_);
lean_dec_ref(v_aig2_339_);
lean_dec_ref(v_aig1_338_);
lean_dec(v_len_337_);
lean_dec_ref(v_inst_336_);
lean_dec_ref(v_inst_335_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_BinaryRefVec_cast_match__1_splitter___redArg(lean_object* v_s_343_, lean_object* v_h__1_344_){
_start:
{
lean_object* v_lhs_345_; lean_object* v_rhs_346_; lean_object* v___x_347_; 
v_lhs_345_ = lean_ctor_get(v_s_343_, 0);
lean_inc_ref(v_lhs_345_);
v_rhs_346_ = lean_ctor_get(v_s_343_, 1);
lean_inc_ref(v_rhs_346_);
lean_dec_ref(v_s_343_);
v___x_347_ = lean_apply_2(v_h__1_344_, v_lhs_345_, v_rhs_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_BinaryRefVec_cast_match__1_splitter(lean_object* v_00_u03b1_348_, lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_len_351_, lean_object* v_aig1_352_, lean_object* v_motive_353_, lean_object* v_s_354_, lean_object* v_h__1_355_){
_start:
{
lean_object* v_lhs_356_; lean_object* v_rhs_357_; lean_object* v___x_358_; 
v_lhs_356_ = lean_ctor_get(v_s_354_, 0);
lean_inc_ref(v_lhs_356_);
v_rhs_357_ = lean_ctor_get(v_s_354_, 1);
lean_inc_ref(v_rhs_357_);
lean_dec_ref(v_s_354_);
v___x_358_ = lean_apply_2(v_h__1_355_, v_lhs_356_, v_rhs_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_BinaryRefVec_cast_match__1_splitter___boxed(lean_object* v_00_u03b1_359_, lean_object* v_inst_360_, lean_object* v_inst_361_, lean_object* v_len_362_, lean_object* v_aig1_363_, lean_object* v_motive_364_, lean_object* v_s_365_, lean_object* v_h__1_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_BinaryRefVec_cast_match__1_splitter(v_00_u03b1_359_, v_inst_360_, v_inst_361_, v_len_362_, v_aig1_363_, v_motive_364_, v_s_365_, v_h__1_366_);
lean_dec_ref(v_aig1_363_);
lean_dec(v_len_362_);
lean_dec_ref(v_inst_361_);
lean_dec_ref(v_inst_360_);
return v_res_367_;
}
}
lean_object* runtime_initialize_Std_Sat_AIG_CachedGatesLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_AIG_RefVec(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Sat_AIG_CachedGatesLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sat_AIG_RefVec(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_AIG_CachedGatesLemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Lemmas(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_RefVec(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_CachedGatesLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_AIG_RefVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sat_AIG_RefVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sat_AIG_RefVec(builtin);
}
#ifdef __cplusplus
}
#endif
