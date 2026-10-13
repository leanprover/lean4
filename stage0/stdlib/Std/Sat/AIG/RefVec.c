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
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_get_match__1_splitter___redArg(lean_object* v_s_150_, lean_object* v_h__1_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = lean_apply_2(v_h__1_151_, v_s_150_, lean_box(0));
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_get_match__1_splitter(lean_object* v_00_u03b1_153_, lean_object* v_inst_154_, lean_object* v_inst_155_, lean_object* v_aig_156_, lean_object* v_len_157_, lean_object* v_motive_158_, lean_object* v_s_159_, lean_object* v_h__1_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = lean_apply_2(v_h__1_160_, v_s_159_, lean_box(0));
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_get_match__1_splitter___boxed(lean_object* v_00_u03b1_162_, lean_object* v_inst_163_, lean_object* v_inst_164_, lean_object* v_aig_165_, lean_object* v_len_166_, lean_object* v_motive_167_, lean_object* v_s_168_, lean_object* v_h__1_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_get_match__1_splitter(v_00_u03b1_162_, v_inst_163_, v_inst_164_, v_aig_165_, v_len_166_, v_motive_167_, v_s_168_, v_h__1_169_);
lean_dec(v_len_166_);
lean_dec_ref(v_aig_165_);
lean_dec_ref(v_inst_164_);
lean_dec_ref(v_inst_163_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_append___redArg(lean_object* v_lhs_171_, lean_object* v_rhs_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Array_append___redArg(v_lhs_171_, v_rhs_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_append___redArg___boxed(lean_object* v_lhs_174_, lean_object* v_rhs_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Std_Sat_AIG_RefVec_append___redArg(v_lhs_174_, v_rhs_175_);
lean_dec_ref(v_rhs_175_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_append(lean_object* v_00_u03b1_177_, lean_object* v_inst_178_, lean_object* v_inst_179_, lean_object* v_aig_180_, lean_object* v_lw_181_, lean_object* v_rw_182_, lean_object* v_lhs_183_, lean_object* v_rhs_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Array_append___redArg(v_lhs_183_, v_rhs_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_append___boxed(lean_object* v_00_u03b1_186_, lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_aig_189_, lean_object* v_lw_190_, lean_object* v_rw_191_, lean_object* v_lhs_192_, lean_object* v_rhs_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Std_Sat_AIG_RefVec_append(v_00_u03b1_186_, v_inst_187_, v_inst_188_, v_aig_189_, v_lw_190_, v_rw_191_, v_lhs_192_, v_rhs_193_);
lean_dec_ref(v_rhs_193_);
lean_dec(v_rw_191_);
lean_dec(v_lw_190_);
lean_dec_ref(v_aig_189_);
lean_dec_ref(v_inst_188_);
lean_dec_ref(v_inst_187_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_getD___redArg(lean_object* v_len_195_, lean_object* v_s_196_, lean_object* v_idx_197_, lean_object* v_alt_198_){
_start:
{
uint8_t v___x_199_; 
v___x_199_ = lean_nat_dec_lt(v_idx_197_, v_len_195_);
if (v___x_199_ == 0)
{
lean_inc_ref(v_alt_198_);
return v_alt_198_;
}
else
{
lean_object* v_ref_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v_ref_200_ = lean_array_fget_borrowed(v_s_196_, v_idx_197_);
v___x_201_ = lean_unsigned_to_nat(1u);
v___x_202_ = lean_nat_shiftr(v_ref_200_, v___x_201_);
v___x_203_ = lean_nat_land(v___x_201_, v_ref_200_);
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = lean_nat_dec_eq(v___x_203_, v___x_204_);
lean_dec(v___x_203_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; 
v___x_206_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_206_, 0, v___x_202_);
lean_ctor_set_uint8(v___x_206_, sizeof(void*)*1, v___x_199_);
return v___x_206_;
}
else
{
uint8_t v___x_207_; lean_object* v___x_208_; 
v___x_207_ = 0;
v___x_208_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_208_, 0, v___x_202_);
lean_ctor_set_uint8(v___x_208_, sizeof(void*)*1, v___x_207_);
return v___x_208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_getD___redArg___boxed(lean_object* v_len_209_, lean_object* v_s_210_, lean_object* v_idx_211_, lean_object* v_alt_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Std_Sat_AIG_RefVec_getD___redArg(v_len_209_, v_s_210_, v_idx_211_, v_alt_212_);
lean_dec_ref(v_alt_212_);
lean_dec(v_idx_211_);
lean_dec_ref(v_s_210_);
lean_dec(v_len_209_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_getD(lean_object* v_00_u03b1_214_, lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_aig_217_, lean_object* v_len_218_, lean_object* v_s_219_, lean_object* v_idx_220_, lean_object* v_alt_221_){
_start:
{
uint8_t v___x_222_; 
v___x_222_ = lean_nat_dec_lt(v_idx_220_, v_len_218_);
if (v___x_222_ == 0)
{
lean_inc_ref(v_alt_221_);
return v_alt_221_;
}
else
{
lean_object* v_ref_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v_ref_223_ = lean_array_fget_borrowed(v_s_219_, v_idx_220_);
v___x_224_ = lean_unsigned_to_nat(1u);
v___x_225_ = lean_nat_shiftr(v_ref_223_, v___x_224_);
v___x_226_ = lean_nat_land(v___x_224_, v_ref_223_);
v___x_227_ = lean_unsigned_to_nat(0u);
v___x_228_ = lean_nat_dec_eq(v___x_226_, v___x_227_);
lean_dec(v___x_226_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; 
v___x_229_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_229_, 0, v___x_225_);
lean_ctor_set_uint8(v___x_229_, sizeof(void*)*1, v___x_222_);
return v___x_229_;
}
else
{
uint8_t v___x_230_; lean_object* v___x_231_; 
v___x_230_ = 0;
v___x_231_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_231_, 0, v___x_225_);
lean_ctor_set_uint8(v___x_231_, sizeof(void*)*1, v___x_230_);
return v___x_231_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_getD___boxed(lean_object* v_00_u03b1_232_, lean_object* v_inst_233_, lean_object* v_inst_234_, lean_object* v_aig_235_, lean_object* v_len_236_, lean_object* v_s_237_, lean_object* v_idx_238_, lean_object* v_alt_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Std_Sat_AIG_RefVec_getD(v_00_u03b1_232_, v_inst_233_, v_inst_234_, v_aig_235_, v_len_236_, v_s_237_, v_idx_238_, v_alt_239_);
lean_dec_ref(v_alt_239_);
lean_dec(v_idx_238_);
lean_dec_ref(v_s_237_);
lean_dec(v_len_236_);
lean_dec_ref(v_aig_235_);
lean_dec_ref(v_inst_234_);
lean_dec_ref(v_inst_233_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown_go___redArg(lean_object* v_len_241_, lean_object* v_aig_242_, lean_object* v_s_243_, lean_object* v_idx_244_, lean_object* v_acc_245_){
_start:
{
uint8_t v___x_246_; 
v___x_246_ = lean_nat_dec_lt(v_idx_244_, v_len_241_);
if (v___x_246_ == 0)
{
lean_dec(v_idx_244_);
return v_acc_245_;
}
else
{
lean_object* v_decls_247_; lean_object* v_ref_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v_decl_251_; 
v_decls_247_ = lean_ctor_get(v_aig_242_, 0);
v_ref_248_ = lean_array_fget_borrowed(v_s_243_, v_idx_244_);
v___x_249_ = lean_unsigned_to_nat(1u);
v___x_250_ = lean_nat_shiftr(v_ref_248_, v___x_249_);
v_decl_251_ = lean_array_fget_borrowed(v_decls_247_, v___x_250_);
lean_dec(v___x_250_);
if (lean_obj_tag(v_decl_251_) == 0)
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = lean_nat_add(v_idx_244_, v___x_249_);
lean_dec(v_idx_244_);
v___x_253_ = lean_nat_add(v_acc_245_, v___x_249_);
lean_dec(v_acc_245_);
v_idx_244_ = v___x_252_;
v_acc_245_ = v___x_253_;
goto _start;
}
else
{
lean_object* v___x_255_; 
v___x_255_ = lean_nat_add(v_idx_244_, v___x_249_);
lean_dec(v_idx_244_);
v_idx_244_ = v___x_255_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown_go___redArg___boxed(lean_object* v_len_257_, lean_object* v_aig_258_, lean_object* v_s_259_, lean_object* v_idx_260_, lean_object* v_acc_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Std_Sat_AIG_RefVec_countKnown_go___redArg(v_len_257_, v_aig_258_, v_s_259_, v_idx_260_, v_acc_261_);
lean_dec_ref(v_s_259_);
lean_dec_ref(v_aig_258_);
lean_dec(v_len_257_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown_go(lean_object* v_00_u03b1_263_, lean_object* v_inst_264_, lean_object* v_inst_265_, lean_object* v_len_266_, lean_object* v_aig_267_, lean_object* v_s_268_, lean_object* v_idx_269_, lean_object* v_acc_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Std_Sat_AIG_RefVec_countKnown_go___redArg(v_len_266_, v_aig_267_, v_s_268_, v_idx_269_, v_acc_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown_go___boxed(lean_object* v_00_u03b1_272_, lean_object* v_inst_273_, lean_object* v_inst_274_, lean_object* v_len_275_, lean_object* v_aig_276_, lean_object* v_s_277_, lean_object* v_idx_278_, lean_object* v_acc_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Std_Sat_AIG_RefVec_countKnown_go(v_00_u03b1_272_, v_inst_273_, v_inst_274_, v_len_275_, v_aig_276_, v_s_277_, v_idx_278_, v_acc_279_);
lean_dec_ref(v_s_277_);
lean_dec_ref(v_aig_276_);
lean_dec(v_len_275_);
lean_dec_ref(v_inst_274_);
lean_dec_ref(v_inst_273_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_countKnown_go_match__1_splitter___redArg(lean_object* v_decl_281_, lean_object* v_h__1_282_, lean_object* v_h__2_283_){
_start:
{
if (lean_obj_tag(v_decl_281_) == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; 
lean_dec(v_h__2_283_);
v___x_284_ = lean_box(0);
v___x_285_ = lean_apply_1(v_h__1_282_, v___x_284_);
return v___x_285_;
}
else
{
lean_object* v___x_286_; 
lean_dec(v_h__1_282_);
v___x_286_ = lean_apply_2(v_h__2_283_, v_decl_281_, lean_box(0));
return v___x_286_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_countKnown_go_match__1_splitter(lean_object* v_00_u03b1_287_, lean_object* v_motive_288_, lean_object* v_decl_289_, lean_object* v_h__1_290_, lean_object* v_h__2_291_){
_start:
{
if (lean_obj_tag(v_decl_289_) == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; 
lean_dec(v_h__2_291_);
v___x_292_ = lean_box(0);
v___x_293_ = lean_apply_1(v_h__1_290_, v___x_292_);
return v___x_293_;
}
else
{
lean_object* v___x_294_; 
lean_dec(v_h__1_290_);
v___x_294_ = lean_apply_2(v_h__2_291_, v_decl_289_, lean_box(0));
return v___x_294_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___redArg(lean_object* v_len_295_, lean_object* v_aig_296_, lean_object* v_s_297_){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = l_Std_Sat_AIG_RefVec_countKnown_go___redArg(v_len_295_, v_aig_296_, v_s_297_, v___x_298_, v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___redArg___boxed(lean_object* v_len_300_, lean_object* v_aig_301_, lean_object* v_s_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Std_Sat_AIG_RefVec_countKnown___redArg(v_len_300_, v_aig_301_, v_s_302_);
lean_dec_ref(v_s_302_);
lean_dec_ref(v_aig_301_);
lean_dec(v_len_300_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown(lean_object* v_00_u03b1_304_, lean_object* v_inst_305_, lean_object* v_inst_306_, lean_object* v_len_307_, lean_object* v_aig_308_, lean_object* v_s_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l_Std_Sat_AIG_RefVec_countKnown___redArg(v_len_307_, v_aig_308_, v_s_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___boxed(lean_object* v_00_u03b1_311_, lean_object* v_inst_312_, lean_object* v_inst_313_, lean_object* v_len_314_, lean_object* v_aig_315_, lean_object* v_s_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Std_Sat_AIG_RefVec_countKnown(v_00_u03b1_311_, v_inst_312_, v_inst_313_, v_len_314_, v_aig_315_, v_s_316_);
lean_dec_ref(v_s_316_);
lean_dec_ref(v_aig_315_);
lean_dec(v_len_314_);
lean_dec_ref(v_inst_313_);
lean_dec_ref(v_inst_312_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryRefVec_cast___redArg(lean_object* v_s_318_){
_start:
{
lean_object* v_lhs_319_; lean_object* v_rhs_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
v_lhs_319_ = lean_ctor_get(v_s_318_, 0);
v_rhs_320_ = lean_ctor_get(v_s_318_, 1);
v_isSharedCheck_327_ = !lean_is_exclusive(v_s_318_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v_s_318_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_rhs_320_);
lean_inc(v_lhs_319_);
lean_dec(v_s_318_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_lhs_319_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_rhs_320_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryRefVec_cast(lean_object* v_00_u03b1_328_, lean_object* v_inst_329_, lean_object* v_inst_330_, lean_object* v_len_331_, lean_object* v_aig1_332_, lean_object* v_aig2_333_, lean_object* v_s_334_, lean_object* v_h_335_){
_start:
{
lean_object* v_lhs_336_; lean_object* v_rhs_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
v_lhs_336_ = lean_ctor_get(v_s_334_, 0);
v_rhs_337_ = lean_ctor_get(v_s_334_, 1);
v_isSharedCheck_344_ = !lean_is_exclusive(v_s_334_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v_s_334_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_rhs_337_);
lean_inc(v_lhs_336_);
lean_dec(v_s_334_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_lhs_336_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_rhs_337_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryRefVec_cast___boxed(lean_object* v_00_u03b1_345_, lean_object* v_inst_346_, lean_object* v_inst_347_, lean_object* v_len_348_, lean_object* v_aig1_349_, lean_object* v_aig2_350_, lean_object* v_s_351_, lean_object* v_h_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Std_Sat_AIG_BinaryRefVec_cast(v_00_u03b1_345_, v_inst_346_, v_inst_347_, v_len_348_, v_aig1_349_, v_aig2_350_, v_s_351_, v_h_352_);
lean_dec_ref(v_aig2_350_);
lean_dec_ref(v_aig1_349_);
lean_dec(v_len_348_);
lean_dec_ref(v_inst_347_);
lean_dec_ref(v_inst_346_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_BinaryRefVec_cast_match__1_splitter___redArg(lean_object* v_s_354_, lean_object* v_h__1_355_){
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
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_BinaryRefVec_cast_match__1_splitter(lean_object* v_00_u03b1_359_, lean_object* v_inst_360_, lean_object* v_inst_361_, lean_object* v_len_362_, lean_object* v_aig1_363_, lean_object* v_motive_364_, lean_object* v_s_365_, lean_object* v_h__1_366_){
_start:
{
lean_object* v_lhs_367_; lean_object* v_rhs_368_; lean_object* v___x_369_; 
v_lhs_367_ = lean_ctor_get(v_s_365_, 0);
lean_inc_ref(v_lhs_367_);
v_rhs_368_ = lean_ctor_get(v_s_365_, 1);
lean_inc_ref(v_rhs_368_);
lean_dec_ref(v_s_365_);
v___x_369_ = lean_apply_2(v_h__1_366_, v_lhs_367_, v_rhs_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_BinaryRefVec_cast_match__1_splitter___boxed(lean_object* v_00_u03b1_370_, lean_object* v_inst_371_, lean_object* v_inst_372_, lean_object* v_len_373_, lean_object* v_aig1_374_, lean_object* v_motive_375_, lean_object* v_s_376_, lean_object* v_h__1_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_BinaryRefVec_cast_match__1_splitter(v_00_u03b1_370_, v_inst_371_, v_inst_372_, v_len_373_, v_aig1_374_, v_motive_375_, v_s_376_, v_h__1_377_);
lean_dec_ref(v_aig1_374_);
lean_dec(v_len_373_);
lean_dec_ref(v_inst_372_);
lean_dec_ref(v_inst_371_);
return v_res_378_;
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
