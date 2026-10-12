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
lean_object* l_Std_Sat_AIG_RefVec_empty___redArg(){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = ((lean_object*)(l_Std_Sat_AIG_RefVec_empty___redArg___closed__0));
return v___x_4_;
}
}
LEAN_EXPORT void l_Std_Sat_AIG_RefVec_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5_;
v_res_5_ = l_Std_Sat_AIG_RefVec_empty___redArg();
stack->m_obj
 = v_res_5_;
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_empty___redArg___boxed(lean_object* v___dummy_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Std_Sat_AIG_RefVec_empty___redArg();
return v_res_7_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RefVec_empty___closed__0(void){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Std_Sat_AIG_RefVec_empty___redArg();
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_empty(lean_object* v_00_u03b1_9_, lean_object* v_inst_10_, lean_object* v_inst_11_, lean_object* v_aig_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_obj_once(&l_Std_Sat_AIG_RefVec_empty___closed__0, &l_Std_Sat_AIG_RefVec_empty___closed__0_once, _init_l_Std_Sat_AIG_RefVec_empty___closed__0);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_empty___boxed(lean_object* v_00_u03b1_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_aig_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Std_Sat_AIG_RefVec_empty(v_00_u03b1_14_, v_inst_15_, v_inst_16_, v_aig_17_);
lean_dec_ref(v_aig_17_);
lean_dec_ref(v_inst_16_);
lean_dec_ref(v_inst_15_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___redArg(lean_object* v_c_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lean_mk_empty_array_with_capacity(v_c_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___redArg___boxed(lean_object* v_c_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Std_Sat_AIG_RefVec_emptyWithCapacity___redArg(v_c_21_);
lean_dec(v_c_21_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity(lean_object* v_00_u03b1_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_aig_26_, lean_object* v_c_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_mk_empty_array_with_capacity(v_c_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_emptyWithCapacity___boxed(lean_object* v_00_u03b1_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_aig_32_, lean_object* v_c_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Std_Sat_AIG_RefVec_emptyWithCapacity(v_00_u03b1_29_, v_inst_30_, v_inst_31_, v_aig_32_, v_c_33_);
lean_dec(v_c_33_);
lean_dec_ref(v_aig_32_);
lean_dec_ref(v_inst_31_);
lean_dec_ref(v_inst_30_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast_x27___redArg(lean_object* v_s_35_){
_start:
{
lean_inc_ref(v_s_35_);
return v_s_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast_x27___redArg___boxed(lean_object* v_s_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Std_Sat_AIG_RefVec_cast_x27___redArg(v_s_36_);
lean_dec_ref(v_s_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast_x27(lean_object* v_00_u03b1_38_, lean_object* v_inst_39_, lean_object* v_inst_40_, lean_object* v_len_41_, lean_object* v_aig1_42_, lean_object* v_aig2_43_, lean_object* v_s_44_, lean_object* v_h_45_){
_start:
{
lean_inc_ref(v_s_44_);
return v_s_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast_x27___boxed(lean_object* v_00_u03b1_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_len_49_, lean_object* v_aig1_50_, lean_object* v_aig2_51_, lean_object* v_s_52_, lean_object* v_h_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Std_Sat_AIG_RefVec_cast_x27(v_00_u03b1_46_, v_inst_47_, v_inst_48_, v_len_49_, v_aig1_50_, v_aig2_51_, v_s_52_, v_h_53_);
lean_dec_ref(v_s_52_);
lean_dec_ref(v_aig2_51_);
lean_dec_ref(v_aig1_50_);
lean_dec(v_len_49_);
lean_dec_ref(v_inst_48_);
lean_dec_ref(v_inst_47_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast___redArg(lean_object* v_s_55_){
_start:
{
lean_inc_ref(v_s_55_);
return v_s_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast___redArg___boxed(lean_object* v_s_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Std_Sat_AIG_RefVec_cast___redArg(v_s_56_);
lean_dec_ref(v_s_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast(lean_object* v_00_u03b1_58_, lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_len_61_, lean_object* v_aig1_62_, lean_object* v_aig2_63_, lean_object* v_s_64_, lean_object* v_h_65_){
_start:
{
lean_inc_ref(v_s_64_);
return v_s_64_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_cast___boxed(lean_object* v_00_u03b1_66_, lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_len_69_, lean_object* v_aig1_70_, lean_object* v_aig2_71_, lean_object* v_s_72_, lean_object* v_h_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Std_Sat_AIG_RefVec_cast(v_00_u03b1_66_, v_inst_67_, v_inst_68_, v_len_69_, v_aig1_70_, v_aig2_71_, v_s_72_, v_h_73_);
lean_dec_ref(v_s_72_);
lean_dec_ref(v_aig2_71_);
lean_dec_ref(v_aig1_70_);
lean_dec(v_len_69_);
lean_dec_ref(v_inst_68_);
lean_dec_ref(v_inst_67_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_get___redArg(lean_object* v_s_75_, lean_object* v_idx_76_){
_start:
{
lean_object* v_ref_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v_ref_77_ = lean_array_fget_borrowed(v_s_75_, v_idx_76_);
v___x_78_ = lean_unsigned_to_nat(1u);
v___x_79_ = lean_nat_shiftr(v_ref_77_, v___x_78_);
v___x_80_ = lean_nat_land(v___x_78_, v_ref_77_);
v___x_81_ = lean_unsigned_to_nat(0u);
v___x_82_ = lean_nat_dec_eq(v___x_80_, v___x_81_);
lean_dec(v___x_80_);
if (v___x_82_ == 0)
{
uint8_t v___x_83_; lean_object* v___x_84_; 
v___x_83_ = 1;
v___x_84_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_84_, 0, v___x_79_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1, v___x_83_);
return v___x_84_;
}
else
{
uint8_t v___x_85_; lean_object* v___x_86_; 
v___x_85_ = 0;
v___x_86_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_86_, 0, v___x_79_);
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*1, v___x_85_);
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_get___redArg___boxed(lean_object* v_s_87_, lean_object* v_idx_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Std_Sat_AIG_RefVec_get___redArg(v_s_87_, v_idx_88_);
lean_dec(v_idx_88_);
lean_dec_ref(v_s_87_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_get(lean_object* v_00_u03b1_90_, lean_object* v_inst_91_, lean_object* v_inst_92_, lean_object* v_aig_93_, lean_object* v_len_94_, lean_object* v_s_95_, lean_object* v_idx_96_, lean_object* v_hidx_97_){
_start:
{
lean_object* v_ref_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v_ref_98_ = lean_array_fget_borrowed(v_s_95_, v_idx_96_);
v___x_99_ = lean_unsigned_to_nat(1u);
v___x_100_ = lean_nat_shiftr(v_ref_98_, v___x_99_);
v___x_101_ = lean_nat_land(v___x_99_, v_ref_98_);
v___x_102_ = lean_unsigned_to_nat(0u);
v___x_103_ = lean_nat_dec_eq(v___x_101_, v___x_102_);
lean_dec(v___x_101_);
if (v___x_103_ == 0)
{
uint8_t v___x_104_; lean_object* v___x_105_; 
v___x_104_ = 1;
v___x_105_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_105_, 0, v___x_100_);
lean_ctor_set_uint8(v___x_105_, sizeof(void*)*1, v___x_104_);
return v___x_105_;
}
else
{
uint8_t v___x_106_; lean_object* v___x_107_; 
v___x_106_ = 0;
v___x_107_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_107_, 0, v___x_100_);
lean_ctor_set_uint8(v___x_107_, sizeof(void*)*1, v___x_106_);
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_get___boxed(lean_object* v_00_u03b1_108_, lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_aig_111_, lean_object* v_len_112_, lean_object* v_s_113_, lean_object* v_idx_114_, lean_object* v_hidx_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Std_Sat_AIG_RefVec_get(v_00_u03b1_108_, v_inst_109_, v_inst_110_, v_aig_111_, v_len_112_, v_s_113_, v_idx_114_, v_hidx_115_);
lean_dec(v_idx_114_);
lean_dec_ref(v_s_113_);
lean_dec(v_len_112_);
lean_dec_ref(v_aig_111_);
lean_dec_ref(v_inst_110_);
lean_dec_ref(v_inst_109_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_push___redArg(lean_object* v_s_117_, lean_object* v_ref_118_){
_start:
{
lean_object* v_gate_119_; uint8_t v_invert_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v_gate_119_ = lean_ctor_get(v_ref_118_, 0);
v_invert_120_ = lean_ctor_get_uint8(v_ref_118_, sizeof(void*)*1);
v___x_121_ = lean_unsigned_to_nat(2u);
v___x_122_ = lean_nat_mul(v_gate_119_, v___x_121_);
v___x_123_ = l_Bool_toNat(v_invert_120_);
v___x_124_ = lean_nat_lor(v___x_122_, v___x_123_);
lean_dec(v___x_123_);
lean_dec(v___x_122_);
v___x_125_ = lean_array_push(v_s_117_, v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_push___redArg___boxed(lean_object* v_s_126_, lean_object* v_ref_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Std_Sat_AIG_RefVec_push___redArg(v_s_126_, v_ref_127_);
lean_dec_ref(v_ref_127_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_push(lean_object* v_00_u03b1_129_, lean_object* v_inst_130_, lean_object* v_inst_131_, lean_object* v_aig_132_, lean_object* v_len_133_, lean_object* v_s_134_, lean_object* v_ref_135_){
_start:
{
lean_object* v_gate_136_; uint8_t v_invert_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v_gate_136_ = lean_ctor_get(v_ref_135_, 0);
v_invert_137_ = lean_ctor_get_uint8(v_ref_135_, sizeof(void*)*1);
v___x_138_ = lean_unsigned_to_nat(2u);
v___x_139_ = lean_nat_mul(v_gate_136_, v___x_138_);
v___x_140_ = l_Bool_toNat(v_invert_137_);
v___x_141_ = lean_nat_lor(v___x_139_, v___x_140_);
lean_dec(v___x_140_);
lean_dec(v___x_139_);
v___x_142_ = lean_array_push(v_s_134_, v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_push___boxed(lean_object* v_00_u03b1_143_, lean_object* v_inst_144_, lean_object* v_inst_145_, lean_object* v_aig_146_, lean_object* v_len_147_, lean_object* v_s_148_, lean_object* v_ref_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Std_Sat_AIG_RefVec_push(v_00_u03b1_143_, v_inst_144_, v_inst_145_, v_aig_146_, v_len_147_, v_s_148_, v_ref_149_);
lean_dec_ref(v_ref_149_);
lean_dec(v_len_147_);
lean_dec_ref(v_aig_146_);
lean_dec_ref(v_inst_145_);
lean_dec_ref(v_inst_144_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_append___redArg(lean_object* v_lhs_151_, lean_object* v_rhs_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Array_append___redArg(v_lhs_151_, v_rhs_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_append___redArg___boxed(lean_object* v_lhs_154_, lean_object* v_rhs_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Std_Sat_AIG_RefVec_append___redArg(v_lhs_154_, v_rhs_155_);
lean_dec_ref(v_rhs_155_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_append(lean_object* v_00_u03b1_157_, lean_object* v_inst_158_, lean_object* v_inst_159_, lean_object* v_aig_160_, lean_object* v_lw_161_, lean_object* v_rw_162_, lean_object* v_lhs_163_, lean_object* v_rhs_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l_Array_append___redArg(v_lhs_163_, v_rhs_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_append___boxed(lean_object* v_00_u03b1_166_, lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_aig_169_, lean_object* v_lw_170_, lean_object* v_rw_171_, lean_object* v_lhs_172_, lean_object* v_rhs_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Std_Sat_AIG_RefVec_append(v_00_u03b1_166_, v_inst_167_, v_inst_168_, v_aig_169_, v_lw_170_, v_rw_171_, v_lhs_172_, v_rhs_173_);
lean_dec_ref(v_rhs_173_);
lean_dec(v_rw_171_);
lean_dec(v_lw_170_);
lean_dec_ref(v_aig_169_);
lean_dec_ref(v_inst_168_);
lean_dec_ref(v_inst_167_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_getD___redArg(lean_object* v_len_175_, lean_object* v_s_176_, lean_object* v_idx_177_, lean_object* v_alt_178_){
_start:
{
uint8_t v___x_179_; 
v___x_179_ = lean_nat_dec_lt(v_idx_177_, v_len_175_);
if (v___x_179_ == 0)
{
lean_inc_ref(v_alt_178_);
return v_alt_178_;
}
else
{
lean_object* v_ref_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v_ref_180_ = lean_array_fget_borrowed(v_s_176_, v_idx_177_);
v___x_181_ = lean_unsigned_to_nat(1u);
v___x_182_ = lean_nat_shiftr(v_ref_180_, v___x_181_);
v___x_183_ = lean_nat_land(v___x_181_, v_ref_180_);
v___x_184_ = lean_unsigned_to_nat(0u);
v___x_185_ = lean_nat_dec_eq(v___x_183_, v___x_184_);
lean_dec(v___x_183_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; 
v___x_186_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_186_, 0, v___x_182_);
lean_ctor_set_uint8(v___x_186_, sizeof(void*)*1, v___x_179_);
return v___x_186_;
}
else
{
uint8_t v___x_187_; lean_object* v___x_188_; 
v___x_187_ = 0;
v___x_188_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_188_, 0, v___x_182_);
lean_ctor_set_uint8(v___x_188_, sizeof(void*)*1, v___x_187_);
return v___x_188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_getD___redArg___boxed(lean_object* v_len_189_, lean_object* v_s_190_, lean_object* v_idx_191_, lean_object* v_alt_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Std_Sat_AIG_RefVec_getD___redArg(v_len_189_, v_s_190_, v_idx_191_, v_alt_192_);
lean_dec_ref(v_alt_192_);
lean_dec(v_idx_191_);
lean_dec_ref(v_s_190_);
lean_dec(v_len_189_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_getD(lean_object* v_00_u03b1_194_, lean_object* v_inst_195_, lean_object* v_inst_196_, lean_object* v_aig_197_, lean_object* v_len_198_, lean_object* v_s_199_, lean_object* v_idx_200_, lean_object* v_alt_201_){
_start:
{
uint8_t v___x_202_; 
v___x_202_ = lean_nat_dec_lt(v_idx_200_, v_len_198_);
if (v___x_202_ == 0)
{
lean_inc_ref(v_alt_201_);
return v_alt_201_;
}
else
{
lean_object* v_ref_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v_ref_203_ = lean_array_fget_borrowed(v_s_199_, v_idx_200_);
v___x_204_ = lean_unsigned_to_nat(1u);
v___x_205_ = lean_nat_shiftr(v_ref_203_, v___x_204_);
v___x_206_ = lean_nat_land(v___x_204_, v_ref_203_);
v___x_207_ = lean_unsigned_to_nat(0u);
v___x_208_ = lean_nat_dec_eq(v___x_206_, v___x_207_);
lean_dec(v___x_206_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; 
v___x_209_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_209_, 0, v___x_205_);
lean_ctor_set_uint8(v___x_209_, sizeof(void*)*1, v___x_202_);
return v___x_209_;
}
else
{
uint8_t v___x_210_; lean_object* v___x_211_; 
v___x_210_ = 0;
v___x_211_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_211_, 0, v___x_205_);
lean_ctor_set_uint8(v___x_211_, sizeof(void*)*1, v___x_210_);
return v___x_211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_getD___boxed(lean_object* v_00_u03b1_212_, lean_object* v_inst_213_, lean_object* v_inst_214_, lean_object* v_aig_215_, lean_object* v_len_216_, lean_object* v_s_217_, lean_object* v_idx_218_, lean_object* v_alt_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Std_Sat_AIG_RefVec_getD(v_00_u03b1_212_, v_inst_213_, v_inst_214_, v_aig_215_, v_len_216_, v_s_217_, v_idx_218_, v_alt_219_);
lean_dec_ref(v_alt_219_);
lean_dec(v_idx_218_);
lean_dec_ref(v_s_217_);
lean_dec(v_len_216_);
lean_dec_ref(v_aig_215_);
lean_dec_ref(v_inst_214_);
lean_dec_ref(v_inst_213_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown_go___redArg(lean_object* v_len_221_, lean_object* v_aig_222_, lean_object* v_s_223_, lean_object* v_idx_224_, lean_object* v_acc_225_){
_start:
{
uint8_t v___x_226_; 
v___x_226_ = lean_nat_dec_lt(v_idx_224_, v_len_221_);
if (v___x_226_ == 0)
{
lean_dec(v_idx_224_);
return v_acc_225_;
}
else
{
lean_object* v_decls_227_; lean_object* v_ref_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v_decl_231_; 
v_decls_227_ = lean_ctor_get(v_aig_222_, 0);
v_ref_228_ = lean_array_fget_borrowed(v_s_223_, v_idx_224_);
v___x_229_ = lean_unsigned_to_nat(1u);
v___x_230_ = lean_nat_shiftr(v_ref_228_, v___x_229_);
v_decl_231_ = lean_array_fget_borrowed(v_decls_227_, v___x_230_);
lean_dec(v___x_230_);
if (lean_obj_tag(v_decl_231_) == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_nat_add(v_idx_224_, v___x_229_);
lean_dec(v_idx_224_);
v___x_233_ = lean_nat_add(v_acc_225_, v___x_229_);
lean_dec(v_acc_225_);
v_idx_224_ = v___x_232_;
v_acc_225_ = v___x_233_;
goto _start;
}
else
{
lean_object* v___x_235_; 
v___x_235_ = lean_nat_add(v_idx_224_, v___x_229_);
lean_dec(v_idx_224_);
v_idx_224_ = v___x_235_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown_go___redArg___boxed(lean_object* v_len_237_, lean_object* v_aig_238_, lean_object* v_s_239_, lean_object* v_idx_240_, lean_object* v_acc_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Std_Sat_AIG_RefVec_countKnown_go___redArg(v_len_237_, v_aig_238_, v_s_239_, v_idx_240_, v_acc_241_);
lean_dec_ref(v_s_239_);
lean_dec_ref(v_aig_238_);
lean_dec(v_len_237_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown_go(lean_object* v_00_u03b1_243_, lean_object* v_inst_244_, lean_object* v_inst_245_, lean_object* v_len_246_, lean_object* v_aig_247_, lean_object* v_s_248_, lean_object* v_idx_249_, lean_object* v_acc_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l_Std_Sat_AIG_RefVec_countKnown_go___redArg(v_len_246_, v_aig_247_, v_s_248_, v_idx_249_, v_acc_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown_go___boxed(lean_object* v_00_u03b1_252_, lean_object* v_inst_253_, lean_object* v_inst_254_, lean_object* v_len_255_, lean_object* v_aig_256_, lean_object* v_s_257_, lean_object* v_idx_258_, lean_object* v_acc_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Std_Sat_AIG_RefVec_countKnown_go(v_00_u03b1_252_, v_inst_253_, v_inst_254_, v_len_255_, v_aig_256_, v_s_257_, v_idx_258_, v_acc_259_);
lean_dec_ref(v_s_257_);
lean_dec_ref(v_aig_256_);
lean_dec(v_len_255_);
lean_dec_ref(v_inst_254_);
lean_dec_ref(v_inst_253_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_countKnown_go_match__1_splitter___redArg(lean_object* v_decl_261_, lean_object* v_h__1_262_, lean_object* v_h__2_263_){
_start:
{
if (lean_obj_tag(v_decl_261_) == 0)
{
lean_object* v___x_264_; lean_object* v___x_265_; 
lean_dec(v_h__2_263_);
v___x_264_ = lean_box(0);
v___x_265_ = lean_apply_1(v_h__1_262_, v___x_264_);
return v___x_265_;
}
else
{
lean_object* v___x_266_; 
lean_dec(v_h__1_262_);
v___x_266_ = lean_apply_2(v_h__2_263_, v_decl_261_, lean_box(0));
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_countKnown_go_match__1_splitter(lean_object* v_00_u03b1_267_, lean_object* v_motive_268_, lean_object* v_decl_269_, lean_object* v_h__1_270_, lean_object* v_h__2_271_){
_start:
{
if (lean_obj_tag(v_decl_269_) == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; 
lean_dec(v_h__2_271_);
v___x_272_ = lean_box(0);
v___x_273_ = lean_apply_1(v_h__1_270_, v___x_272_);
return v___x_273_;
}
else
{
lean_object* v___x_274_; 
lean_dec(v_h__1_270_);
v___x_274_ = lean_apply_2(v_h__2_271_, v_decl_269_, lean_box(0));
return v___x_274_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___redArg(lean_object* v_len_275_, lean_object* v_aig_276_, lean_object* v_s_277_){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_unsigned_to_nat(0u);
v___x_279_ = l_Std_Sat_AIG_RefVec_countKnown_go___redArg(v_len_275_, v_aig_276_, v_s_277_, v___x_278_, v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___redArg___boxed(lean_object* v_len_280_, lean_object* v_aig_281_, lean_object* v_s_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Std_Sat_AIG_RefVec_countKnown___redArg(v_len_280_, v_aig_281_, v_s_282_);
lean_dec_ref(v_s_282_);
lean_dec_ref(v_aig_281_);
lean_dec(v_len_280_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown(lean_object* v_00_u03b1_284_, lean_object* v_inst_285_, lean_object* v_inst_286_, lean_object* v_len_287_, lean_object* v_aig_288_, lean_object* v_s_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Std_Sat_AIG_RefVec_countKnown___redArg(v_len_287_, v_aig_288_, v_s_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_countKnown___boxed(lean_object* v_00_u03b1_291_, lean_object* v_inst_292_, lean_object* v_inst_293_, lean_object* v_len_294_, lean_object* v_aig_295_, lean_object* v_s_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Std_Sat_AIG_RefVec_countKnown(v_00_u03b1_291_, v_inst_292_, v_inst_293_, v_len_294_, v_aig_295_, v_s_296_);
lean_dec_ref(v_s_296_);
lean_dec_ref(v_aig_295_);
lean_dec(v_len_294_);
lean_dec_ref(v_inst_293_);
lean_dec_ref(v_inst_292_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryRefVec_cast___redArg(lean_object* v_s_298_){
_start:
{
lean_object* v_lhs_299_; lean_object* v_rhs_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
v_lhs_299_ = lean_ctor_get(v_s_298_, 0);
v_rhs_300_ = lean_ctor_get(v_s_298_, 1);
v_isSharedCheck_307_ = !lean_is_exclusive(v_s_298_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v_s_298_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_rhs_300_);
lean_inc(v_lhs_299_);
lean_dec(v_s_298_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_lhs_299_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v_rhs_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryRefVec_cast(lean_object* v_00_u03b1_308_, lean_object* v_inst_309_, lean_object* v_inst_310_, lean_object* v_len_311_, lean_object* v_aig1_312_, lean_object* v_aig2_313_, lean_object* v_s_314_, lean_object* v_h_315_){
_start:
{
lean_object* v_lhs_316_; lean_object* v_rhs_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
v_lhs_316_ = lean_ctor_get(v_s_314_, 0);
v_rhs_317_ = lean_ctor_get(v_s_314_, 1);
v_isSharedCheck_324_ = !lean_is_exclusive(v_s_314_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v_s_314_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_rhs_317_);
lean_inc(v_lhs_316_);
lean_dec(v_s_314_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_lhs_316_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v_rhs_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_BinaryRefVec_cast___boxed(lean_object* v_00_u03b1_325_, lean_object* v_inst_326_, lean_object* v_inst_327_, lean_object* v_len_328_, lean_object* v_aig1_329_, lean_object* v_aig2_330_, lean_object* v_s_331_, lean_object* v_h_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Std_Sat_AIG_BinaryRefVec_cast(v_00_u03b1_325_, v_inst_326_, v_inst_327_, v_len_328_, v_aig1_329_, v_aig2_330_, v_s_331_, v_h_332_);
lean_dec_ref(v_aig2_330_);
lean_dec_ref(v_aig1_329_);
lean_dec(v_len_328_);
lean_dec_ref(v_inst_327_);
lean_dec_ref(v_inst_326_);
return v_res_333_;
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
