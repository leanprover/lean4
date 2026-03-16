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
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
lean_object* v_ref_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v_ref_71_ = lean_array_fget_borrowed(v_s_69_, v_idx_70_);
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_nat_shiftr(v_ref_71_, v___x_72_);
v___x_74_ = lean_nat_land(v___x_72_, v_ref_71_);
v___x_75_ = lean_unsigned_to_nat(0u);
v___x_76_ = lean_nat_dec_eq(v___x_74_, v___x_75_);
lean_dec(v___x_74_);
if (v___x_76_ == 0)
{
uint8_t v___x_77_; lean_object* v___x_78_; 
v___x_77_ = 1;
v___x_78_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_78_, 0, v___x_73_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*1, v___x_77_);
return v___x_78_;
}
else
{
uint8_t v___x_79_; lean_object* v___x_80_; 
v___x_79_ = 0;
v___x_80_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_80_, 0, v___x_73_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*1, v___x_79_);
return v___x_80_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_get___redArg___boxed(lean_object* v_s_81_, lean_object* v_idx_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Std_Sat_AIG_RefVec_get___redArg(v_s_81_, v_idx_82_);
lean_dec(v_idx_82_);
lean_dec_ref(v_s_81_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_get(lean_object* v_00_u03b1_84_, lean_object* v_inst_85_, lean_object* v_inst_86_, lean_object* v_aig_87_, lean_object* v_len_88_, lean_object* v_s_89_, lean_object* v_idx_90_, lean_object* v_hidx_91_){
_start:
{
lean_object* v_ref_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v_ref_92_ = lean_array_fget_borrowed(v_s_89_, v_idx_90_);
v___x_93_ = lean_unsigned_to_nat(1u);
v___x_94_ = lean_nat_shiftr(v_ref_92_, v___x_93_);
v___x_95_ = lean_nat_land(v___x_93_, v_ref_92_);
v___x_96_ = lean_unsigned_to_nat(0u);
v___x_97_ = lean_nat_dec_eq(v___x_95_, v___x_96_);
lean_dec(v___x_95_);
if (v___x_97_ == 0)
{
uint8_t v___x_98_; lean_object* v___x_99_; 
v___x_98_ = 1;
v___x_99_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_99_, 0, v___x_94_);
lean_ctor_set_uint8(v___x_99_, sizeof(void*)*1, v___x_98_);
return v___x_99_;
}
else
{
uint8_t v___x_100_; lean_object* v___x_101_; 
v___x_100_ = 0;
v___x_101_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_101_, 0, v___x_94_);
lean_ctor_set_uint8(v___x_101_, sizeof(void*)*1, v___x_100_);
return v___x_101_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_get___boxed(lean_object* v_00_u03b1_102_, lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v_aig_105_, lean_object* v_len_106_, lean_object* v_s_107_, lean_object* v_idx_108_, lean_object* v_hidx_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Std_Sat_AIG_RefVec_get(v_00_u03b1_102_, v_inst_103_, v_inst_104_, v_aig_105_, v_len_106_, v_s_107_, v_idx_108_, v_hidx_109_);
lean_dec(v_idx_108_);
lean_dec_ref(v_s_107_);
lean_dec(v_len_106_);
lean_dec_ref(v_aig_105_);
lean_dec_ref(v_inst_104_);
lean_dec_ref(v_inst_103_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_push___redArg(lean_object* v_s_111_, lean_object* v_ref_112_){
_start:
{
lean_object* v_gate_113_; uint8_t v_invert_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v_gate_113_ = lean_ctor_get(v_ref_112_, 0);
v_invert_114_ = lean_ctor_get_uint8(v_ref_112_, sizeof(void*)*1);
v___x_115_ = lean_unsigned_to_nat(2u);
v___x_116_ = lean_nat_mul(v_gate_113_, v___x_115_);
v___x_117_ = l_Bool_toNat(v_invert_114_);
v___x_118_ = lean_nat_lor(v___x_116_, v___x_117_);
lean_dec(v___x_117_);
lean_dec(v___x_116_);
v___x_119_ = lean_array_push(v_s_111_, v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_push___redArg___boxed(lean_object* v_s_120_, lean_object* v_ref_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Std_Sat_AIG_RefVec_push___redArg(v_s_120_, v_ref_121_);
lean_dec_ref(v_ref_121_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_push(lean_object* v_00_u03b1_123_, lean_object* v_inst_124_, lean_object* v_inst_125_, lean_object* v_aig_126_, lean_object* v_len_127_, lean_object* v_s_128_, lean_object* v_ref_129_){
_start:
{
lean_object* v_gate_130_; uint8_t v_invert_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v_gate_130_ = lean_ctor_get(v_ref_129_, 0);
v_invert_131_ = lean_ctor_get_uint8(v_ref_129_, sizeof(void*)*1);
v___x_132_ = lean_unsigned_to_nat(2u);
v___x_133_ = lean_nat_mul(v_gate_130_, v___x_132_);
v___x_134_ = l_Bool_toNat(v_invert_131_);
v___x_135_ = lean_nat_lor(v___x_133_, v___x_134_);
lean_dec(v___x_134_);
lean_dec(v___x_133_);
v___x_136_ = lean_array_push(v_s_128_, v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_push___boxed(lean_object* v_00_u03b1_137_, lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_aig_140_, lean_object* v_len_141_, lean_object* v_s_142_, lean_object* v_ref_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Std_Sat_AIG_RefVec_push(v_00_u03b1_137_, v_inst_138_, v_inst_139_, v_aig_140_, v_len_141_, v_s_142_, v_ref_143_);
lean_dec_ref(v_ref_143_);
lean_dec(v_len_141_);
lean_dec_ref(v_aig_140_);
lean_dec_ref(v_inst_139_);
lean_dec_ref(v_inst_138_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_get_match__1_splitter___redArg(lean_object* v_s_145_, lean_object* v_h__1_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = lean_apply_2(v_h__1_146_, v_s_145_, lean_box(0));
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_get_match__1_splitter(lean_object* v_00_u03b1_148_, lean_object* v_inst_149_, lean_object* v_inst_150_, lean_object* v_aig_151_, lean_object* v_len_152_, lean_object* v_motive_153_, lean_object* v_s_154_, lean_object* v_h__1_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = lean_apply_2(v_h__1_155_, v_s_154_, lean_box(0));
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_get_match__1_splitter___boxed(lean_object* v_00_u03b1_157_, lean_object* v_inst_158_, lean_object* v_inst_159_, lean_object* v_aig_160_, lean_object* v_len_161_, lean_object* v_motive_162_, lean_object* v_s_163_, lean_object* v_h__1_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_get_match__1_splitter(v_00_u03b1_157_, v_inst_158_, v_inst_159_, v_aig_160_, v_len_161_, v_motive_162_, v_s_163_, v_h__1_164_);
lean_dec(v_len_161_);
lean_dec_ref(v_aig_160_);
lean_dec_ref(v_inst_159_);
lean_dec_ref(v_inst_158_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_append___redArg(lean_object* v_lhs_166_, lean_object* v_rhs_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Array_append___redArg(v_lhs_166_, v_rhs_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_append___redArg___boxed(lean_object* v_lhs_169_, lean_object* v_rhs_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Std_Sat_AIG_RefVec_append___redArg(v_lhs_169_, v_rhs_170_);
lean_dec_ref(v_rhs_170_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_append(lean_object* v_00_u03b1_172_, lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_aig_175_, lean_object* v_lw_176_, lean_object* v_rw_177_, lean_object* v_lhs_178_, lean_object* v_rhs_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Array_append___redArg(v_lhs_178_, v_rhs_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_append___boxed(lean_object* v_00_u03b1_181_, lean_object* v_inst_182_, lean_object* v_inst_183_, lean_object* v_aig_184_, lean_object* v_lw_185_, lean_object* v_rw_186_, lean_object* v_lhs_187_, lean_object* v_rhs_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Std_Sat_AIG_RefVec_append(v_00_u03b1_181_, v_inst_182_, v_inst_183_, v_aig_184_, v_lw_185_, v_rw_186_, v_lhs_187_, v_rhs_188_);
lean_dec_ref(v_rhs_188_);
lean_dec(v_rw_186_);
lean_dec(v_lw_185_);
lean_dec_ref(v_aig_184_);
lean_dec_ref(v_inst_183_);
lean_dec_ref(v_inst_182_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_getD___redArg(lean_object* v_len_190_, lean_object* v_s_191_, lean_object* v_idx_192_, lean_object* v_alt_193_){
_start:
{
uint8_t v___x_194_; 
v___x_194_ = lean_nat_dec_lt(v_idx_192_, v_len_190_);
if (v___x_194_ == 0)
{
lean_inc_ref(v_alt_193_);
return v_alt_193_;
}
else
{
lean_object* v_ref_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v_ref_195_ = lean_array_fget_borrowed(v_s_191_, v_idx_192_);
v___x_196_ = lean_unsigned_to_nat(1u);
v___x_197_ = lean_nat_shiftr(v_ref_195_, v___x_196_);
v___x_198_ = lean_nat_land(v___x_196_, v_ref_195_);
v___x_199_ = lean_unsigned_to_nat(0u);
v___x_200_ = lean_nat_dec_eq(v___x_198_, v___x_199_);
lean_dec(v___x_198_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; 
v___x_201_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_201_, 0, v___x_197_);
lean_ctor_set_uint8(v___x_201_, sizeof(void*)*1, v___x_194_);
return v___x_201_;
}
else
{
uint8_t v___x_202_; lean_object* v___x_203_; 
v___x_202_ = 0;
v___x_203_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_203_, 0, v___x_197_);
lean_ctor_set_uint8(v___x_203_, sizeof(void*)*1, v___x_202_);
return v___x_203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_getD___redArg___boxed(lean_object* v_len_204_, lean_object* v_s_205_, lean_object* v_idx_206_, lean_object* v_alt_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Std_Sat_AIG_RefVec_getD___redArg(v_len_204_, v_s_205_, v_idx_206_, v_alt_207_);
lean_dec_ref(v_alt_207_);
lean_dec(v_idx_206_);
lean_dec_ref(v_s_205_);
lean_dec(v_len_204_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_getD(lean_object* v_00_u03b1_209_, lean_object* v_inst_210_, lean_object* v_inst_211_, lean_object* v_aig_212_, lean_object* v_len_213_, lean_object* v_s_214_, lean_object* v_idx_215_, lean_object* v_alt_216_){
_start:
{
uint8_t v___x_217_; 
v___x_217_ = lean_nat_dec_lt(v_idx_215_, v_len_213_);
if (v___x_217_ == 0)
{
lean_inc_ref(v_alt_216_);
return v_alt_216_;
}
else
{
lean_object* v_ref_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v_ref_218_ = lean_array_fget_borrowed(v_s_214_, v_idx_215_);
v___x_219_ = lean_unsigned_to_nat(1u);
v___x_220_ = lean_nat_shiftr(v_ref_218_, v___x_219_);
v___x_221_ = lean_nat_land(v___x_219_, v_ref_218_);
v___x_222_ = lean_unsigned_to_nat(0u);
v___x_223_ = lean_nat_dec_eq(v___x_221_, v___x_222_);
lean_dec(v___x_221_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; 
v___x_224_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_224_, 0, v___x_220_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*1, v___x_217_);
return v___x_224_;
}
else
{
uint8_t v___x_225_; lean_object* v___x_226_; 
v___x_225_ = 0;
v___x_226_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_226_, 0, v___x_220_);
lean_ctor_set_uint8(v___x_226_, sizeof(void*)*1, v___x_225_);
return v___x_226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_getD___boxed(lean_object* v_00_u03b1_227_, lean_object* v_inst_228_, lean_object* v_inst_229_, lean_object* v_aig_230_, lean_object* v_len_231_, lean_object* v_s_232_, lean_object* v_idx_233_, lean_object* v_alt_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Std_Sat_AIG_RefVec_getD(v_00_u03b1_227_, v_inst_228_, v_inst_229_, v_aig_230_, v_len_231_, v_s_232_, v_idx_233_, v_alt_234_);
lean_dec_ref(v_alt_234_);
lean_dec(v_idx_233_);
lean_dec_ref(v_s_232_);
lean_dec(v_len_231_);
lean_dec_ref(v_aig_230_);
lean_dec_ref(v_inst_229_);
lean_dec_ref(v_inst_228_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown_go___redArg(lean_object* v_len_236_, lean_object* v_aig_237_, lean_object* v_s_238_, lean_object* v_idx_239_, lean_object* v_acc_240_){
_start:
{
uint8_t v___x_241_; 
v___x_241_ = lean_nat_dec_lt(v_idx_239_, v_len_236_);
if (v___x_241_ == 0)
{
lean_dec(v_idx_239_);
return v_acc_240_;
}
else
{
lean_object* v_decls_242_; lean_object* v_ref_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v_decl_246_; 
v_decls_242_ = lean_ctor_get(v_aig_237_, 0);
v_ref_243_ = lean_array_fget_borrowed(v_s_238_, v_idx_239_);
v___x_244_ = lean_unsigned_to_nat(1u);
v___x_245_ = lean_nat_shiftr(v_ref_243_, v___x_244_);
v_decl_246_ = lean_array_fget_borrowed(v_decls_242_, v___x_245_);
lean_dec(v___x_245_);
if (lean_obj_tag(v_decl_246_) == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_nat_add(v_idx_239_, v___x_244_);
lean_dec(v_idx_239_);
v___x_248_ = lean_nat_add(v_acc_240_, v___x_244_);
lean_dec(v_acc_240_);
v_idx_239_ = v___x_247_;
v_acc_240_ = v___x_248_;
goto _start;
}
else
{
lean_object* v___x_250_; 
v___x_250_ = lean_nat_add(v_idx_239_, v___x_244_);
lean_dec(v_idx_239_);
v_idx_239_ = v___x_250_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown_go___redArg___boxed(lean_object* v_len_252_, lean_object* v_aig_253_, lean_object* v_s_254_, lean_object* v_idx_255_, lean_object* v_acc_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Std_Sat_AIG_RefVec_countKnown_go___redArg(v_len_252_, v_aig_253_, v_s_254_, v_idx_255_, v_acc_256_);
lean_dec_ref(v_s_254_);
lean_dec_ref(v_aig_253_);
lean_dec(v_len_252_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown_go(lean_object* v_00_u03b1_258_, lean_object* v_inst_259_, lean_object* v_inst_260_, lean_object* v_len_261_, lean_object* v_aig_262_, lean_object* v_s_263_, lean_object* v_idx_264_, lean_object* v_acc_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Std_Sat_AIG_RefVec_countKnown_go___redArg(v_len_261_, v_aig_262_, v_s_263_, v_idx_264_, v_acc_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown_go___boxed(lean_object* v_00_u03b1_267_, lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_len_270_, lean_object* v_aig_271_, lean_object* v_s_272_, lean_object* v_idx_273_, lean_object* v_acc_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Std_Sat_AIG_RefVec_countKnown_go(v_00_u03b1_267_, v_inst_268_, v_inst_269_, v_len_270_, v_aig_271_, v_s_272_, v_idx_273_, v_acc_274_);
lean_dec_ref(v_s_272_);
lean_dec_ref(v_aig_271_);
lean_dec(v_len_270_);
lean_dec_ref(v_inst_269_);
lean_dec_ref(v_inst_268_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_countKnown_go_match__1_splitter___redArg(lean_object* v_decl_276_, lean_object* v_h__1_277_, lean_object* v_h__2_278_){
_start:
{
if (lean_obj_tag(v_decl_276_) == 0)
{
lean_object* v___x_279_; lean_object* v___x_280_; 
lean_dec(v_h__2_278_);
v___x_279_ = lean_box(0);
v___x_280_ = lean_apply_1(v_h__1_277_, v___x_279_);
return v___x_280_;
}
else
{
lean_object* v___x_281_; 
lean_dec(v_h__1_277_);
v___x_281_ = lean_apply_2(v_h__2_278_, v_decl_276_, lean_box(0));
return v___x_281_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_countKnown_go_match__1_splitter(lean_object* v_00_u03b1_282_, lean_object* v_motive_283_, lean_object* v_decl_284_, lean_object* v_h__1_285_, lean_object* v_h__2_286_){
_start:
{
if (lean_obj_tag(v_decl_284_) == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; 
lean_dec(v_h__2_286_);
v___x_287_ = lean_box(0);
v___x_288_ = lean_apply_1(v_h__1_285_, v___x_287_);
return v___x_288_;
}
else
{
lean_object* v___x_289_; 
lean_dec(v_h__1_285_);
v___x_289_ = lean_apply_2(v_h__2_286_, v_decl_284_, lean_box(0));
return v___x_289_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___redArg(lean_object* v_len_290_, lean_object* v_aig_291_, lean_object* v_s_292_){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = lean_unsigned_to_nat(0u);
v___x_294_ = l_Std_Sat_AIG_RefVec_countKnown_go___redArg(v_len_290_, v_aig_291_, v_s_292_, v___x_293_, v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___redArg___boxed(lean_object* v_len_295_, lean_object* v_aig_296_, lean_object* v_s_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Std_Sat_AIG_RefVec_countKnown___redArg(v_len_295_, v_aig_296_, v_s_297_);
lean_dec_ref(v_s_297_);
lean_dec_ref(v_aig_296_);
lean_dec(v_len_295_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown(lean_object* v_00_u03b1_299_, lean_object* v_inst_300_, lean_object* v_inst_301_, lean_object* v_len_302_, lean_object* v_aig_303_, lean_object* v_s_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Std_Sat_AIG_RefVec_countKnown___redArg(v_len_302_, v_aig_303_, v_s_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___boxed(lean_object* v_00_u03b1_306_, lean_object* v_inst_307_, lean_object* v_inst_308_, lean_object* v_len_309_, lean_object* v_aig_310_, lean_object* v_s_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Std_Sat_AIG_RefVec_countKnown(v_00_u03b1_306_, v_inst_307_, v_inst_308_, v_len_309_, v_aig_310_, v_s_311_);
lean_dec_ref(v_s_311_);
lean_dec_ref(v_aig_310_);
lean_dec(v_len_309_);
lean_dec_ref(v_inst_308_);
lean_dec_ref(v_inst_307_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryRefVec_cast___redArg(lean_object* v_s_313_){
_start:
{
lean_object* v_lhs_314_; lean_object* v_rhs_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_322_; 
v_lhs_314_ = lean_ctor_get(v_s_313_, 0);
v_rhs_315_ = lean_ctor_get(v_s_313_, 1);
v_isSharedCheck_322_ = !lean_is_exclusive(v_s_313_);
if (v_isSharedCheck_322_ == 0)
{
v___x_317_ = v_s_313_;
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_rhs_315_);
lean_inc(v_lhs_314_);
lean_dec(v_s_313_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_320_; 
if (v_isShared_318_ == 0)
{
v___x_320_ = v___x_317_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_lhs_314_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_rhs_315_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryRefVec_cast(lean_object* v_00_u03b1_323_, lean_object* v_inst_324_, lean_object* v_inst_325_, lean_object* v_len_326_, lean_object* v_aig1_327_, lean_object* v_aig2_328_, lean_object* v_s_329_, lean_object* v_h_330_){
_start:
{
lean_object* v_lhs_331_; lean_object* v_rhs_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
v_lhs_331_ = lean_ctor_get(v_s_329_, 0);
v_rhs_332_ = lean_ctor_get(v_s_329_, 1);
v_isSharedCheck_339_ = !lean_is_exclusive(v_s_329_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v_s_329_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_rhs_332_);
lean_inc(v_lhs_331_);
lean_dec(v_s_329_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_lhs_331_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_rhs_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryRefVec_cast___boxed(lean_object* v_00_u03b1_340_, lean_object* v_inst_341_, lean_object* v_inst_342_, lean_object* v_len_343_, lean_object* v_aig1_344_, lean_object* v_aig2_345_, lean_object* v_s_346_, lean_object* v_h_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Std_Sat_AIG_BinaryRefVec_cast(v_00_u03b1_340_, v_inst_341_, v_inst_342_, v_len_343_, v_aig1_344_, v_aig2_345_, v_s_346_, v_h_347_);
lean_dec_ref(v_aig2_345_);
lean_dec_ref(v_aig1_344_);
lean_dec(v_len_343_);
lean_dec_ref(v_inst_342_);
lean_dec_ref(v_inst_341_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_BinaryRefVec_cast_match__1_splitter___redArg(lean_object* v_s_349_, lean_object* v_h__1_350_){
_start:
{
lean_object* v_lhs_351_; lean_object* v_rhs_352_; lean_object* v___x_353_; 
v_lhs_351_ = lean_ctor_get(v_s_349_, 0);
lean_inc_ref(v_lhs_351_);
v_rhs_352_ = lean_ctor_get(v_s_349_, 1);
lean_inc_ref(v_rhs_352_);
lean_dec_ref(v_s_349_);
v___x_353_ = lean_apply_2(v_h__1_350_, v_lhs_351_, v_rhs_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_BinaryRefVec_cast_match__1_splitter(lean_object* v_00_u03b1_354_, lean_object* v_inst_355_, lean_object* v_inst_356_, lean_object* v_len_357_, lean_object* v_aig1_358_, lean_object* v_motive_359_, lean_object* v_s_360_, lean_object* v_h__1_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_BinaryRefVec_cast_match__1_splitter___redArg(v_s_360_, v_h__1_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_BinaryRefVec_cast_match__1_splitter___boxed(lean_object* v_00_u03b1_363_, lean_object* v_inst_364_, lean_object* v_inst_365_, lean_object* v_len_366_, lean_object* v_aig1_367_, lean_object* v_motive_368_, lean_object* v_s_369_, lean_object* v_h__1_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_BinaryRefVec_cast_match__1_splitter(v_00_u03b1_363_, v_inst_364_, v_inst_365_, v_len_366_, v_aig1_367_, v_motive_368_, v_s_369_, v_h__1_370_);
lean_dec_ref(v_aig1_367_);
lean_dec(v_len_366_);
lean_dec_ref(v_inst_365_);
lean_dec_ref(v_inst_364_);
return v_res_371_;
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
