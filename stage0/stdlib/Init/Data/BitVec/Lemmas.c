// Lean compiler output
// Module: Init.Data.BitVec.Lemmas
// Imports: import all Init.Data.BitVec.Basic import all Init.Data.BitVec.BasicAux public import Init.Data.Fin.Lemmas public import Init.Data.List.BasicAux import Init.Data.List.Lemmas public import Init.Data.BitVec.Basic import Init.ByCases import Init.Data.BitVec.Bootstrap import Init.Data.Int.Bitwise.Lemmas import Init.Data.Int.DivMod.Lemmas import Init.Data.Int.LemmasAux import Init.Data.Int.Pow import Init.Data.Nat.Div.Lemmas import Init.Data.Nat.MinMax import Init.Data.Nat.Mod import Init.Data.Nat.Simproc import Init.TacticsExtra
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
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_ofBoolListBE_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_ofBoolListBE_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_1_; lean_object* v_intZero_2_; 
v_natZero_1_ = lean_unsigned_to_nat(0u);
v_intZero_2_ = lean_nat_to_int(v_natZero_1_);
return v_intZero_2_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg(lean_object* v_x_3_, lean_object* v_h__1_4_, lean_object* v_h__2_5_){
_start:
{
lean_object* v_intZero_6_; uint8_t v_isNeg_7_; 
v_intZero_6_ = lean_obj_once(&l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0, &l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0);
v_isNeg_7_ = lean_int_dec_lt(v_x_3_, v_intZero_6_);
if (v_isNeg_7_ == 0)
{
lean_object* v_a_8_; lean_object* v___x_9_; 
lean_dec(v_h__2_5_);
v_a_8_ = lean_nat_abs(v_x_3_);
v___x_9_ = lean_apply_1(v_h__1_4_, v_a_8_);
return v___x_9_;
}
else
{
lean_object* v_abs_10_; lean_object* v_one_11_; lean_object* v_a_12_; lean_object* v___x_13_; 
lean_dec(v_h__1_4_);
v_abs_10_ = lean_nat_abs(v_x_3_);
v_one_11_ = lean_unsigned_to_nat(1u);
v_a_12_ = lean_nat_sub(v_abs_10_, v_one_11_);
lean_dec(v_abs_10_);
v___x_13_ = lean_apply_1(v_h__2_5_, v_a_12_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___boxed(lean_object* v_x_14_, lean_object* v_h__1_15_, lean_object* v_h__2_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg(v_x_14_, v_h__1_15_, v_h__2_16_);
lean_dec(v_x_14_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter(lean_object* v_motive_18_, lean_object* v_x_19_, lean_object* v_h__1_20_, lean_object* v_h__2_21_){
_start:
{
lean_object* v_intZero_22_; uint8_t v_isNeg_23_; 
v_intZero_22_ = lean_obj_once(&l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0, &l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0);
v_isNeg_23_ = lean_int_dec_lt(v_x_19_, v_intZero_22_);
if (v_isNeg_23_ == 0)
{
lean_object* v_a_24_; lean_object* v___x_25_; 
lean_dec(v_h__2_21_);
v_a_24_ = lean_nat_abs(v_x_19_);
v___x_25_ = lean_apply_1(v_h__1_20_, v_a_24_);
return v___x_25_;
}
else
{
lean_object* v_abs_26_; lean_object* v_one_27_; lean_object* v_a_28_; lean_object* v___x_29_; 
lean_dec(v_h__1_20_);
v_abs_26_ = lean_nat_abs(v_x_19_);
v_one_27_ = lean_unsigned_to_nat(1u);
v_a_28_ = lean_nat_sub(v_abs_26_, v_one_27_);
lean_dec(v_abs_26_);
v___x_29_ = lean_apply_1(v_h__2_21_, v_a_28_);
return v___x_29_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___boxed(lean_object* v_motive_30_, lean_object* v_x_31_, lean_object* v_h__1_32_, lean_object* v_h__2_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter(v_motive_30_, v_x_31_, v_h__1_32_, v_h__2_33_);
lean_dec(v_x_31_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___redArg(uint8_t v_x_35_, uint8_t v_x_36_, lean_object* v_h__1_37_, lean_object* v_h__2_38_, lean_object* v_h__3_39_, lean_object* v_h__4_40_){
_start:
{
if (v_x_35_ == 0)
{
lean_dec(v_h__4_40_);
lean_dec(v_h__3_39_);
if (v_x_36_ == 0)
{
lean_object* v___x_41_; lean_object* v___x_42_; 
lean_dec(v_h__2_38_);
v___x_41_ = lean_box(0);
v___x_42_ = lean_apply_1(v_h__1_37_, v___x_41_);
return v___x_42_;
}
else
{
lean_object* v___x_43_; lean_object* v___x_44_; 
lean_dec(v_h__1_37_);
v___x_43_ = lean_box(0);
v___x_44_ = lean_apply_1(v_h__2_38_, v___x_43_);
return v___x_44_;
}
}
else
{
lean_dec(v_h__2_38_);
lean_dec(v_h__1_37_);
if (v_x_36_ == 0)
{
lean_object* v___x_45_; lean_object* v___x_46_; 
lean_dec(v_h__4_40_);
v___x_45_ = lean_box(0);
v___x_46_ = lean_apply_1(v_h__3_39_, v___x_45_);
return v___x_46_;
}
else
{
lean_object* v___x_47_; lean_object* v___x_48_; 
lean_dec(v_h__3_39_);
v___x_47_ = lean_box(0);
v___x_48_ = lean_apply_1(v_h__4_40_, v___x_47_);
return v___x_48_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___redArg___boxed(lean_object* v_x_49_, lean_object* v_x_50_, lean_object* v_h__1_51_, lean_object* v_h__2_52_, lean_object* v_h__3_53_, lean_object* v_h__4_54_){
_start:
{
uint8_t v_x_50__boxed_55_; uint8_t v_x_51__boxed_56_; lean_object* v_res_57_; 
v_x_50__boxed_55_ = lean_unbox(v_x_49_);
v_x_51__boxed_56_ = lean_unbox(v_x_50_);
v_res_57_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___redArg(v_x_50__boxed_55_, v_x_51__boxed_56_, v_h__1_51_, v_h__2_52_, v_h__3_53_, v_h__4_54_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter(lean_object* v_motive_58_, uint8_t v_x_59_, uint8_t v_x_60_, lean_object* v_h__1_61_, lean_object* v_h__2_62_, lean_object* v_h__3_63_, lean_object* v_h__4_64_){
_start:
{
if (v_x_59_ == 0)
{
lean_dec(v_h__4_64_);
lean_dec(v_h__3_63_);
if (v_x_60_ == 0)
{
lean_object* v___x_65_; lean_object* v___x_66_; 
lean_dec(v_h__2_62_);
v___x_65_ = lean_box(0);
v___x_66_ = lean_apply_1(v_h__1_61_, v___x_65_);
return v___x_66_;
}
else
{
lean_object* v___x_67_; lean_object* v___x_68_; 
lean_dec(v_h__1_61_);
v___x_67_ = lean_box(0);
v___x_68_ = lean_apply_1(v_h__2_62_, v___x_67_);
return v___x_68_;
}
}
else
{
lean_dec(v_h__2_62_);
lean_dec(v_h__1_61_);
if (v_x_60_ == 0)
{
lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec(v_h__4_64_);
v___x_69_ = lean_box(0);
v___x_70_ = lean_apply_1(v_h__3_63_, v___x_69_);
return v___x_70_;
}
else
{
lean_object* v___x_71_; lean_object* v___x_72_; 
lean_dec(v_h__3_63_);
v___x_71_ = lean_box(0);
v___x_72_ = lean_apply_1(v_h__4_64_, v___x_71_);
return v___x_72_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___boxed(lean_object* v_motive_73_, lean_object* v_x_74_, lean_object* v_x_75_, lean_object* v_h__1_76_, lean_object* v_h__2_77_, lean_object* v_h__3_78_, lean_object* v_h__4_79_){
_start:
{
uint8_t v_x_72__boxed_80_; uint8_t v_x_73__boxed_81_; lean_object* v_res_82_; 
v_x_72__boxed_80_ = lean_unbox(v_x_74_);
v_x_73__boxed_81_ = lean_unbox(v_x_75_);
v_res_82_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter(v_motive_73_, v_x_72__boxed_80_, v_x_73__boxed_81_, v_h__1_76_, v_h__2_77_, v_h__3_78_, v_h__4_79_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_ofBoolListBE_match__1_splitter___redArg(lean_object* v_x_83_, lean_object* v_h__1_84_, lean_object* v_h__2_85_){
_start:
{
if (lean_obj_tag(v_x_83_) == 0)
{
lean_object* v___x_86_; lean_object* v___x_87_; 
lean_dec(v_h__2_85_);
v___x_86_ = lean_box(0);
v___x_87_ = lean_apply_1(v_h__1_84_, v___x_86_);
return v___x_87_;
}
else
{
lean_object* v_head_88_; lean_object* v_tail_89_; lean_object* v___x_90_; 
lean_dec(v_h__1_84_);
v_head_88_ = lean_ctor_get(v_x_83_, 0);
lean_inc(v_head_88_);
v_tail_89_ = lean_ctor_get(v_x_83_, 1);
lean_inc(v_tail_89_);
lean_dec_ref(v_x_83_);
v___x_90_ = lean_apply_2(v_h__2_85_, v_head_88_, v_tail_89_);
return v___x_90_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_ofBoolListBE_match__1_splitter(lean_object* v_motive_91_, lean_object* v_x_92_, lean_object* v_h__1_93_, lean_object* v_h__2_94_){
_start:
{
if (lean_obj_tag(v_x_92_) == 0)
{
lean_object* v___x_95_; lean_object* v___x_96_; 
lean_dec(v_h__2_94_);
v___x_95_ = lean_box(0);
v___x_96_ = lean_apply_1(v_h__1_93_, v___x_95_);
return v___x_96_;
}
else
{
lean_object* v_head_97_; lean_object* v_tail_98_; lean_object* v___x_99_; 
lean_dec(v_h__1_93_);
v_head_97_ = lean_ctor_get(v_x_92_, 0);
lean_inc(v_head_97_);
v_tail_98_ = lean_ctor_get(v_x_92_, 1);
lean_inc(v_tail_98_);
lean_dec_ref(v_x_92_);
v___x_99_ = lean_apply_2(v_h__2_94_, v_head_97_, v_tail_98_);
return v___x_99_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___redArg(lean_object* v_x_100_, lean_object* v_x_101_, lean_object* v_h__1_102_, lean_object* v_h__2_103_){
_start:
{
lean_object* v_zero_104_; uint8_t v_isZero_105_; 
v_zero_104_ = lean_unsigned_to_nat(0u);
v_isZero_105_ = lean_nat_dec_eq(v_x_100_, v_zero_104_);
if (v_isZero_105_ == 1)
{
lean_object* v___x_106_; 
lean_dec(v_h__2_103_);
v___x_106_ = lean_apply_1(v_h__1_102_, v_x_101_);
return v___x_106_;
}
else
{
lean_object* v_one_107_; lean_object* v_n_108_; lean_object* v___x_109_; 
lean_dec(v_h__1_102_);
v_one_107_ = lean_unsigned_to_nat(1u);
v_n_108_ = lean_nat_sub(v_x_100_, v_one_107_);
v___x_109_ = lean_apply_2(v_h__2_103_, v_n_108_, v_x_101_);
return v___x_109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___redArg___boxed(lean_object* v_x_110_, lean_object* v_x_111_, lean_object* v_h__1_112_, lean_object* v_h__2_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___redArg(v_x_110_, v_x_111_, v_h__1_112_, v_h__2_113_);
lean_dec(v_x_110_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter(lean_object* v_w_115_, lean_object* v_motive_116_, lean_object* v_x_117_, lean_object* v_x_118_, lean_object* v_h__1_119_, lean_object* v_h__2_120_){
_start:
{
lean_object* v_zero_121_; uint8_t v_isZero_122_; 
v_zero_121_ = lean_unsigned_to_nat(0u);
v_isZero_122_ = lean_nat_dec_eq(v_x_117_, v_zero_121_);
if (v_isZero_122_ == 1)
{
lean_object* v___x_123_; 
lean_dec(v_h__2_120_);
v___x_123_ = lean_apply_1(v_h__1_119_, v_x_118_);
return v___x_123_;
}
else
{
lean_object* v_one_124_; lean_object* v_n_125_; lean_object* v___x_126_; 
lean_dec(v_h__1_119_);
v_one_124_ = lean_unsigned_to_nat(1u);
v_n_125_ = lean_nat_sub(v_x_117_, v_one_124_);
v___x_126_ = lean_apply_2(v_h__2_120_, v_n_125_, v_x_118_);
return v___x_126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___boxed(lean_object* v_w_127_, lean_object* v_motive_128_, lean_object* v_x_129_, lean_object* v_x_130_, lean_object* v_h__1_131_, lean_object* v_h__2_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter(v_w_127_, v_motive_128_, v_x_129_, v_x_130_, v_h__1_131_, v_h__2_132_);
lean_dec(v_x_129_);
lean_dec(v_w_127_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___redArg(lean_object* v_x_134_, lean_object* v_x_135_, lean_object* v_h__1_136_, lean_object* v_h__2_137_){
_start:
{
lean_object* v_zero_138_; uint8_t v_isZero_139_; 
v_zero_138_ = lean_unsigned_to_nat(0u);
v_isZero_139_ = lean_nat_dec_eq(v_x_134_, v_zero_138_);
if (v_isZero_139_ == 1)
{
lean_object* v___x_140_; 
lean_dec(v_h__2_137_);
v___x_140_ = lean_apply_1(v_h__1_136_, v_x_135_);
return v___x_140_;
}
else
{
lean_object* v_one_141_; lean_object* v_n_142_; lean_object* v___x_143_; 
lean_dec(v_h__1_136_);
v_one_141_ = lean_unsigned_to_nat(1u);
v_n_142_ = lean_nat_sub(v_x_134_, v_one_141_);
v___x_143_ = lean_apply_2(v_h__2_137_, v_n_142_, v_x_135_);
return v___x_143_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___redArg___boxed(lean_object* v_x_144_, lean_object* v_x_145_, lean_object* v_h__1_146_, lean_object* v_h__2_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___redArg(v_x_144_, v_x_145_, v_h__1_146_, v_h__2_147_);
lean_dec(v_x_144_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter(lean_object* v_motive_149_, lean_object* v_x_150_, lean_object* v_x_151_, lean_object* v_h__1_152_, lean_object* v_h__2_153_){
_start:
{
lean_object* v_zero_154_; uint8_t v_isZero_155_; 
v_zero_154_ = lean_unsigned_to_nat(0u);
v_isZero_155_ = lean_nat_dec_eq(v_x_150_, v_zero_154_);
if (v_isZero_155_ == 1)
{
lean_object* v___x_156_; 
lean_dec(v_h__2_153_);
v___x_156_ = lean_apply_1(v_h__1_152_, v_x_151_);
return v___x_156_;
}
else
{
lean_object* v_one_157_; lean_object* v_n_158_; lean_object* v___x_159_; 
lean_dec(v_h__1_152_);
v_one_157_ = lean_unsigned_to_nat(1u);
v_n_158_ = lean_nat_sub(v_x_150_, v_one_157_);
v___x_159_ = lean_apply_2(v_h__2_153_, v_n_158_, v_x_151_);
return v___x_159_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___boxed(lean_object* v_motive_160_, lean_object* v_x_161_, lean_object* v_x_162_, lean_object* v_h__1_163_, lean_object* v_h__2_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter(v_motive_160_, v_x_161_, v_x_162_, v_h__1_163_, v_h__2_164_);
lean_dec(v_x_161_);
return v_res_165_;
}
}
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Bitwise_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_BitVec_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Bitwise_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Div_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Mod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_BitVec_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_BasicAux(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_BasicAux(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Bitwise_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Div_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_BitVec_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Bitwise_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Mod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_BitVec_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
