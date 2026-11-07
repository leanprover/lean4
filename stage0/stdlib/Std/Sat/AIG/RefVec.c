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
static const lean_array_object l_Std_Sat_AIG_RefVec_empty___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Sat_AIG_RefVec_empty___redArg___closed__0 = (const lean_object*)&l_Std_Sat_AIG_RefVec_empty___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_empty___redArg();
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_empty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Sat_AIG_RefVec_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_RefVec_empty___closed__0;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_empty___redArg(){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = ((lean_object*)(l_Std_Sat_AIG_RefVec_empty___redArg___closed__0));
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_empty___redArg___boxed(lean_object* v___dummy_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Std_Sat_AIG_RefVec_empty___redArg();
return v_res_6_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RefVec_empty___closed__0(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_Std_Sat_AIG_RefVec_empty___redArg();
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_empty(lean_object* v_00_u03b1_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_aig_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&l_Std_Sat_AIG_RefVec_empty___closed__0, &l_Std_Sat_AIG_RefVec_empty___closed__0_once, _init_l_Std_Sat_AIG_RefVec_empty___closed__0);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_empty___boxed(lean_object* v_00_u03b1_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_aig_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Std_Sat_AIG_RefVec_empty(v_00_u03b1_13_, v_inst_14_, v_inst_15_, v_aig_16_);
lean_dec_ref(v_aig_16_);
lean_dec_ref(v_inst_15_);
lean_dec_ref(v_inst_14_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___redArg(lean_object* v_c_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lean_mk_empty_array_with_capacity(v_c_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___redArg___boxed(lean_object* v_c_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Std_Sat_AIG_RefVec_emptyWithCapacity___redArg(v_c_20_);
lean_dec(v_c_20_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity(lean_object* v_00_u03b1_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_aig_25_, lean_object* v_c_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_mk_empty_array_with_capacity(v_c_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___boxed(lean_object* v_00_u03b1_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_aig_31_, lean_object* v_c_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Std_Sat_AIG_RefVec_emptyWithCapacity(v_00_u03b1_28_, v_inst_29_, v_inst_30_, v_aig_31_, v_c_32_);
lean_dec(v_c_32_);
lean_dec_ref(v_aig_31_);
lean_dec_ref(v_inst_30_);
lean_dec_ref(v_inst_29_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast_x27___redArg(lean_object* v_s_34_){
_start:
{
lean_inc_ref(v_s_34_);
return v_s_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast_x27___redArg___boxed(lean_object* v_s_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Std_Sat_AIG_RefVec_cast_x27___redArg(v_s_35_);
lean_dec_ref(v_s_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast_x27(lean_object* v_00_u03b1_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_len_40_, lean_object* v_aig1_41_, lean_object* v_aig2_42_, lean_object* v_s_43_, lean_object* v_h_44_){
_start:
{
lean_inc_ref(v_s_43_);
return v_s_43_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast_x27___boxed(lean_object* v_00_u03b1_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_len_48_, lean_object* v_aig1_49_, lean_object* v_aig2_50_, lean_object* v_s_51_, lean_object* v_h_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Std_Sat_AIG_RefVec_cast_x27(v_00_u03b1_45_, v_inst_46_, v_inst_47_, v_len_48_, v_aig1_49_, v_aig2_50_, v_s_51_, v_h_52_);
lean_dec_ref(v_s_51_);
lean_dec_ref(v_aig2_50_);
lean_dec_ref(v_aig1_49_);
lean_dec(v_len_48_);
lean_dec_ref(v_inst_47_);
lean_dec_ref(v_inst_46_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast___redArg(lean_object* v_s_54_){
_start:
{
lean_inc_ref(v_s_54_);
return v_s_54_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast___redArg___boxed(lean_object* v_s_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Std_Sat_AIG_RefVec_cast___redArg(v_s_55_);
lean_dec_ref(v_s_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast(lean_object* v_00_u03b1_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_len_60_, lean_object* v_aig1_61_, lean_object* v_aig2_62_, lean_object* v_s_63_, lean_object* v_h_64_){
_start:
{
lean_inc_ref(v_s_63_);
return v_s_63_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast___boxed(lean_object* v_00_u03b1_65_, lean_object* v_inst_66_, lean_object* v_inst_67_, lean_object* v_len_68_, lean_object* v_aig1_69_, lean_object* v_aig2_70_, lean_object* v_s_71_, lean_object* v_h_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Std_Sat_AIG_RefVec_cast(v_00_u03b1_65_, v_inst_66_, v_inst_67_, v_len_68_, v_aig1_69_, v_aig2_70_, v_s_71_, v_h_72_);
lean_dec_ref(v_s_71_);
lean_dec_ref(v_aig2_70_);
lean_dec_ref(v_aig1_69_);
lean_dec(v_len_68_);
lean_dec_ref(v_inst_67_);
lean_dec_ref(v_inst_66_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_get___redArg(lean_object* v_s_74_, lean_object* v_idx_75_){
_start:
{
lean_object* v_ref_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; 
v_ref_76_ = lean_array_fget_borrowed(v_s_74_, v_idx_75_);
v___x_77_ = lean_unsigned_to_nat(1u);
v___x_78_ = lean_nat_shiftr(v_ref_76_, v___x_77_);
v___x_79_ = lean_nat_land(v___x_77_, v_ref_76_);
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = lean_nat_dec_eq(v___x_79_, v___x_80_);
lean_dec(v___x_79_);
if (v___x_81_ == 0)
{
uint8_t v___x_82_; lean_object* v___x_83_; 
v___x_82_ = 1;
v___x_83_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_83_, 0, v___x_78_);
lean_ctor_set_uint8(v___x_83_, sizeof(void*)*1, v___x_82_);
return v___x_83_;
}
else
{
uint8_t v___x_84_; lean_object* v___x_85_; 
v___x_84_ = 0;
v___x_85_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_85_, 0, v___x_78_);
lean_ctor_set_uint8(v___x_85_, sizeof(void*)*1, v___x_84_);
return v___x_85_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_get___redArg___boxed(lean_object* v_s_86_, lean_object* v_idx_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Std_Sat_AIG_RefVec_get___redArg(v_s_86_, v_idx_87_);
lean_dec(v_idx_87_);
lean_dec_ref(v_s_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_get(lean_object* v_00_u03b1_89_, lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_aig_92_, lean_object* v_len_93_, lean_object* v_s_94_, lean_object* v_idx_95_, lean_object* v_hidx_96_){
_start:
{
lean_object* v_ref_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v_ref_97_ = lean_array_fget_borrowed(v_s_94_, v_idx_95_);
v___x_98_ = lean_unsigned_to_nat(1u);
v___x_99_ = lean_nat_shiftr(v_ref_97_, v___x_98_);
v___x_100_ = lean_nat_land(v___x_98_, v_ref_97_);
v___x_101_ = lean_unsigned_to_nat(0u);
v___x_102_ = lean_nat_dec_eq(v___x_100_, v___x_101_);
lean_dec(v___x_100_);
if (v___x_102_ == 0)
{
uint8_t v___x_103_; lean_object* v___x_104_; 
v___x_103_ = 1;
v___x_104_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_104_, 0, v___x_99_);
lean_ctor_set_uint8(v___x_104_, sizeof(void*)*1, v___x_103_);
return v___x_104_;
}
else
{
uint8_t v___x_105_; lean_object* v___x_106_; 
v___x_105_ = 0;
v___x_106_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_106_, 0, v___x_99_);
lean_ctor_set_uint8(v___x_106_, sizeof(void*)*1, v___x_105_);
return v___x_106_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_get___boxed(lean_object* v_00_u03b1_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_aig_110_, lean_object* v_len_111_, lean_object* v_s_112_, lean_object* v_idx_113_, lean_object* v_hidx_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Std_Sat_AIG_RefVec_get(v_00_u03b1_107_, v_inst_108_, v_inst_109_, v_aig_110_, v_len_111_, v_s_112_, v_idx_113_, v_hidx_114_);
lean_dec(v_idx_113_);
lean_dec_ref(v_s_112_);
lean_dec(v_len_111_);
lean_dec_ref(v_aig_110_);
lean_dec_ref(v_inst_109_);
lean_dec_ref(v_inst_108_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_push___redArg(lean_object* v_s_116_, lean_object* v_ref_117_){
_start:
{
lean_object* v_gate_118_; uint8_t v_invert_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v_gate_118_ = lean_ctor_get(v_ref_117_, 0);
v_invert_119_ = lean_ctor_get_uint8(v_ref_117_, sizeof(void*)*1);
v___x_120_ = lean_unsigned_to_nat(2u);
v___x_121_ = lean_nat_mul(v_gate_118_, v___x_120_);
v___x_122_ = l_Bool_toNat(v_invert_119_);
v___x_123_ = lean_nat_lor(v___x_121_, v___x_122_);
lean_dec(v___x_122_);
lean_dec(v___x_121_);
v___x_124_ = lean_array_push(v_s_116_, v___x_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_push___redArg___boxed(lean_object* v_s_125_, lean_object* v_ref_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Std_Sat_AIG_RefVec_push___redArg(v_s_125_, v_ref_126_);
lean_dec_ref(v_ref_126_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_push(lean_object* v_00_u03b1_128_, lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v_aig_131_, lean_object* v_len_132_, lean_object* v_s_133_, lean_object* v_ref_134_){
_start:
{
lean_object* v_gate_135_; uint8_t v_invert_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v_gate_135_ = lean_ctor_get(v_ref_134_, 0);
v_invert_136_ = lean_ctor_get_uint8(v_ref_134_, sizeof(void*)*1);
v___x_137_ = lean_unsigned_to_nat(2u);
v___x_138_ = lean_nat_mul(v_gate_135_, v___x_137_);
v___x_139_ = l_Bool_toNat(v_invert_136_);
v___x_140_ = lean_nat_lor(v___x_138_, v___x_139_);
lean_dec(v___x_139_);
lean_dec(v___x_138_);
v___x_141_ = lean_array_push(v_s_133_, v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_push___boxed(lean_object* v_00_u03b1_142_, lean_object* v_inst_143_, lean_object* v_inst_144_, lean_object* v_aig_145_, lean_object* v_len_146_, lean_object* v_s_147_, lean_object* v_ref_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Std_Sat_AIG_RefVec_push(v_00_u03b1_142_, v_inst_143_, v_inst_144_, v_aig_145_, v_len_146_, v_s_147_, v_ref_148_);
lean_dec_ref(v_ref_148_);
lean_dec(v_len_146_);
lean_dec_ref(v_aig_145_);
lean_dec_ref(v_inst_144_);
lean_dec_ref(v_inst_143_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_append___redArg(lean_object* v_lhs_150_, lean_object* v_rhs_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Array_append___redArg(v_lhs_150_, v_rhs_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_append___redArg___boxed(lean_object* v_lhs_153_, lean_object* v_rhs_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Std_Sat_AIG_RefVec_append___redArg(v_lhs_153_, v_rhs_154_);
lean_dec_ref(v_rhs_154_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_append(lean_object* v_00_u03b1_156_, lean_object* v_inst_157_, lean_object* v_inst_158_, lean_object* v_aig_159_, lean_object* v_lw_160_, lean_object* v_rw_161_, lean_object* v_lhs_162_, lean_object* v_rhs_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Array_append___redArg(v_lhs_162_, v_rhs_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_append___boxed(lean_object* v_00_u03b1_165_, lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_aig_168_, lean_object* v_lw_169_, lean_object* v_rw_170_, lean_object* v_lhs_171_, lean_object* v_rhs_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Std_Sat_AIG_RefVec_append(v_00_u03b1_165_, v_inst_166_, v_inst_167_, v_aig_168_, v_lw_169_, v_rw_170_, v_lhs_171_, v_rhs_172_);
lean_dec_ref(v_rhs_172_);
lean_dec(v_rw_170_);
lean_dec(v_lw_169_);
lean_dec_ref(v_aig_168_);
lean_dec_ref(v_inst_167_);
lean_dec_ref(v_inst_166_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_getD___redArg(lean_object* v_len_174_, lean_object* v_s_175_, lean_object* v_idx_176_, lean_object* v_alt_177_){
_start:
{
uint8_t v___x_178_; 
v___x_178_ = lean_nat_dec_lt(v_idx_176_, v_len_174_);
if (v___x_178_ == 0)
{
lean_inc_ref(v_alt_177_);
return v_alt_177_;
}
else
{
lean_object* v_ref_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v_ref_179_ = lean_array_fget_borrowed(v_s_175_, v_idx_176_);
v___x_180_ = lean_unsigned_to_nat(1u);
v___x_181_ = lean_nat_shiftr(v_ref_179_, v___x_180_);
v___x_182_ = lean_nat_land(v___x_180_, v_ref_179_);
v___x_183_ = lean_unsigned_to_nat(0u);
v___x_184_ = lean_nat_dec_eq(v___x_182_, v___x_183_);
lean_dec(v___x_182_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; 
v___x_185_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_185_, 0, v___x_181_);
lean_ctor_set_uint8(v___x_185_, sizeof(void*)*1, v___x_178_);
return v___x_185_;
}
else
{
uint8_t v___x_186_; lean_object* v___x_187_; 
v___x_186_ = 0;
v___x_187_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_187_, 0, v___x_181_);
lean_ctor_set_uint8(v___x_187_, sizeof(void*)*1, v___x_186_);
return v___x_187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_getD___redArg___boxed(lean_object* v_len_188_, lean_object* v_s_189_, lean_object* v_idx_190_, lean_object* v_alt_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Std_Sat_AIG_RefVec_getD___redArg(v_len_188_, v_s_189_, v_idx_190_, v_alt_191_);
lean_dec_ref(v_alt_191_);
lean_dec(v_idx_190_);
lean_dec_ref(v_s_189_);
lean_dec(v_len_188_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_getD(lean_object* v_00_u03b1_193_, lean_object* v_inst_194_, lean_object* v_inst_195_, lean_object* v_aig_196_, lean_object* v_len_197_, lean_object* v_s_198_, lean_object* v_idx_199_, lean_object* v_alt_200_){
_start:
{
uint8_t v___x_201_; 
v___x_201_ = lean_nat_dec_lt(v_idx_199_, v_len_197_);
if (v___x_201_ == 0)
{
lean_inc_ref(v_alt_200_);
return v_alt_200_;
}
else
{
lean_object* v_ref_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v_ref_202_ = lean_array_fget_borrowed(v_s_198_, v_idx_199_);
v___x_203_ = lean_unsigned_to_nat(1u);
v___x_204_ = lean_nat_shiftr(v_ref_202_, v___x_203_);
v___x_205_ = lean_nat_land(v___x_203_, v_ref_202_);
v___x_206_ = lean_unsigned_to_nat(0u);
v___x_207_ = lean_nat_dec_eq(v___x_205_, v___x_206_);
lean_dec(v___x_205_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; 
v___x_208_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_208_, 0, v___x_204_);
lean_ctor_set_uint8(v___x_208_, sizeof(void*)*1, v___x_201_);
return v___x_208_;
}
else
{
uint8_t v___x_209_; lean_object* v___x_210_; 
v___x_209_ = 0;
v___x_210_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_210_, 0, v___x_204_);
lean_ctor_set_uint8(v___x_210_, sizeof(void*)*1, v___x_209_);
return v___x_210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_getD___boxed(lean_object* v_00_u03b1_211_, lean_object* v_inst_212_, lean_object* v_inst_213_, lean_object* v_aig_214_, lean_object* v_len_215_, lean_object* v_s_216_, lean_object* v_idx_217_, lean_object* v_alt_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Std_Sat_AIG_RefVec_getD(v_00_u03b1_211_, v_inst_212_, v_inst_213_, v_aig_214_, v_len_215_, v_s_216_, v_idx_217_, v_alt_218_);
lean_dec_ref(v_alt_218_);
lean_dec(v_idx_217_);
lean_dec_ref(v_s_216_);
lean_dec(v_len_215_);
lean_dec_ref(v_aig_214_);
lean_dec_ref(v_inst_213_);
lean_dec_ref(v_inst_212_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown_go___redArg(lean_object* v_len_220_, lean_object* v_aig_221_, lean_object* v_s_222_, lean_object* v_idx_223_, lean_object* v_acc_224_){
_start:
{
uint8_t v___x_225_; 
v___x_225_ = lean_nat_dec_lt(v_idx_223_, v_len_220_);
if (v___x_225_ == 0)
{
lean_dec(v_idx_223_);
return v_acc_224_;
}
else
{
lean_object* v_decls_226_; lean_object* v_ref_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v_decl_230_; 
v_decls_226_ = lean_ctor_get(v_aig_221_, 0);
v_ref_227_ = lean_array_fget_borrowed(v_s_222_, v_idx_223_);
v___x_228_ = lean_unsigned_to_nat(1u);
v___x_229_ = lean_nat_shiftr(v_ref_227_, v___x_228_);
v_decl_230_ = lean_array_fget_borrowed(v_decls_226_, v___x_229_);
lean_dec(v___x_229_);
if (lean_obj_tag(v_decl_230_) == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = lean_nat_add(v_idx_223_, v___x_228_);
lean_dec(v_idx_223_);
v___x_232_ = lean_nat_add(v_acc_224_, v___x_228_);
lean_dec(v_acc_224_);
v_idx_223_ = v___x_231_;
v_acc_224_ = v___x_232_;
goto _start;
}
else
{
lean_object* v___x_234_; 
v___x_234_ = lean_nat_add(v_idx_223_, v___x_228_);
lean_dec(v_idx_223_);
v_idx_223_ = v___x_234_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown_go___redArg___boxed(lean_object* v_len_236_, lean_object* v_aig_237_, lean_object* v_s_238_, lean_object* v_idx_239_, lean_object* v_acc_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Std_Sat_AIG_RefVec_countKnown_go___redArg(v_len_236_, v_aig_237_, v_s_238_, v_idx_239_, v_acc_240_);
lean_dec_ref(v_s_238_);
lean_dec_ref(v_aig_237_);
lean_dec(v_len_236_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown_go(lean_object* v_00_u03b1_242_, lean_object* v_inst_243_, lean_object* v_inst_244_, lean_object* v_len_245_, lean_object* v_aig_246_, lean_object* v_s_247_, lean_object* v_idx_248_, lean_object* v_acc_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Std_Sat_AIG_RefVec_countKnown_go___redArg(v_len_245_, v_aig_246_, v_s_247_, v_idx_248_, v_acc_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown_go___boxed(lean_object* v_00_u03b1_251_, lean_object* v_inst_252_, lean_object* v_inst_253_, lean_object* v_len_254_, lean_object* v_aig_255_, lean_object* v_s_256_, lean_object* v_idx_257_, lean_object* v_acc_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Std_Sat_AIG_RefVec_countKnown_go(v_00_u03b1_251_, v_inst_252_, v_inst_253_, v_len_254_, v_aig_255_, v_s_256_, v_idx_257_, v_acc_258_);
lean_dec_ref(v_s_256_);
lean_dec_ref(v_aig_255_);
lean_dec(v_len_254_);
lean_dec_ref(v_inst_253_);
lean_dec_ref(v_inst_252_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_countKnown_go_match__1_splitter___redArg(lean_object* v_decl_260_, lean_object* v_h__1_261_, lean_object* v_h__2_262_){
_start:
{
if (lean_obj_tag(v_decl_260_) == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; 
lean_dec(v_h__2_262_);
v___x_263_ = lean_box(0);
v___x_264_ = lean_apply_1(v_h__1_261_, v___x_263_);
return v___x_264_;
}
else
{
lean_object* v___x_265_; 
lean_dec(v_h__1_261_);
v___x_265_ = lean_apply_2(v_h__2_262_, v_decl_260_, lean_box(0));
return v___x_265_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_countKnown_go_match__1_splitter(lean_object* v_00_u03b1_266_, lean_object* v_motive_267_, lean_object* v_decl_268_, lean_object* v_h__1_269_, lean_object* v_h__2_270_){
_start:
{
if (lean_obj_tag(v_decl_268_) == 0)
{
lean_object* v___x_271_; lean_object* v___x_272_; 
lean_dec(v_h__2_270_);
v___x_271_ = lean_box(0);
v___x_272_ = lean_apply_1(v_h__1_269_, v___x_271_);
return v___x_272_;
}
else
{
lean_object* v___x_273_; 
lean_dec(v_h__1_269_);
v___x_273_ = lean_apply_2(v_h__2_270_, v_decl_268_, lean_box(0));
return v___x_273_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___redArg(lean_object* v_len_274_, lean_object* v_aig_275_, lean_object* v_s_276_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = l_Std_Sat_AIG_RefVec_countKnown_go___redArg(v_len_274_, v_aig_275_, v_s_276_, v___x_277_, v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___redArg___boxed(lean_object* v_len_279_, lean_object* v_aig_280_, lean_object* v_s_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Std_Sat_AIG_RefVec_countKnown___redArg(v_len_279_, v_aig_280_, v_s_281_);
lean_dec_ref(v_s_281_);
lean_dec_ref(v_aig_280_);
lean_dec(v_len_279_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown(lean_object* v_00_u03b1_283_, lean_object* v_inst_284_, lean_object* v_inst_285_, lean_object* v_len_286_, lean_object* v_aig_287_, lean_object* v_s_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_Std_Sat_AIG_RefVec_countKnown___redArg(v_len_286_, v_aig_287_, v_s_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___boxed(lean_object* v_00_u03b1_290_, lean_object* v_inst_291_, lean_object* v_inst_292_, lean_object* v_len_293_, lean_object* v_aig_294_, lean_object* v_s_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Std_Sat_AIG_RefVec_countKnown(v_00_u03b1_290_, v_inst_291_, v_inst_292_, v_len_293_, v_aig_294_, v_s_295_);
lean_dec_ref(v_s_295_);
lean_dec_ref(v_aig_294_);
lean_dec(v_len_293_);
lean_dec_ref(v_inst_292_);
lean_dec_ref(v_inst_291_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryRefVec_cast___redArg(lean_object* v_s_297_){
_start:
{
lean_object* v_lhs_298_; lean_object* v_rhs_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
v_lhs_298_ = lean_ctor_get(v_s_297_, 0);
v_rhs_299_ = lean_ctor_get(v_s_297_, 1);
v_isSharedCheck_306_ = !lean_is_exclusive(v_s_297_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v_s_297_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_rhs_299_);
lean_inc(v_lhs_298_);
lean_dec(v_s_297_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_lhs_298_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v_rhs_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryRefVec_cast(lean_object* v_00_u03b1_307_, lean_object* v_inst_308_, lean_object* v_inst_309_, lean_object* v_len_310_, lean_object* v_aig1_311_, lean_object* v_aig2_312_, lean_object* v_s_313_, lean_object* v_h_314_){
_start:
{
lean_object* v_lhs_315_; lean_object* v_rhs_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
v_lhs_315_ = lean_ctor_get(v_s_313_, 0);
v_rhs_316_ = lean_ctor_get(v_s_313_, 1);
v_isSharedCheck_323_ = !lean_is_exclusive(v_s_313_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v_s_313_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_rhs_316_);
lean_inc(v_lhs_315_);
lean_dec(v_s_313_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_lhs_315_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_rhs_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryRefVec_cast___boxed(lean_object* v_00_u03b1_324_, lean_object* v_inst_325_, lean_object* v_inst_326_, lean_object* v_len_327_, lean_object* v_aig1_328_, lean_object* v_aig2_329_, lean_object* v_s_330_, lean_object* v_h_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Std_Sat_AIG_BinaryRefVec_cast(v_00_u03b1_324_, v_inst_325_, v_inst_326_, v_len_327_, v_aig1_328_, v_aig2_329_, v_s_330_, v_h_331_);
lean_dec_ref(v_aig2_329_);
lean_dec_ref(v_aig1_328_);
lean_dec(v_len_327_);
lean_dec_ref(v_inst_326_);
lean_dec_ref(v_inst_325_);
return v_res_332_;
}
}
lean_object* runtime_initialize_Std_Sat_AIG_CachedGatesLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_AIG_RefVec(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
