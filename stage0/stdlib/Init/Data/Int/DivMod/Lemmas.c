// Lean compiler output
// Module: Init.Data.Int.DivMod.Lemmas
// Imports: import Init.TacticsExtra public import Init.Data.Int.DivMod.Basic public import Init.Data.Nat.Div.Basic public import Init.NotationExtra import Init.ByCases import Init.Data.Bool import Init.Data.Nat.Div.Lemmas import Init.Data.Nat.Lemmas import Init.Omega import Init.RCases
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
static lean_once_cell_t l_Int_decidableDvd___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_decidableDvd___closed__0;
LEAN_EXPORT uint8_t l_Int_decidableDvd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_decidableDvd___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Int_decidableDvd___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT uint8_t l_Int_decidableDvd(lean_object* v_a_3_, lean_object* v_b_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_5_ = lean_int_emod(v_b_4_, v_a_3_);
v___x_6_ = lean_obj_once(&l_Int_decidableDvd___closed__0, &l_Int_decidableDvd___closed__0_once, _init_l_Int_decidableDvd___closed__0);
v___x_7_ = lean_int_dec_eq(v___x_5_, v___x_6_);
lean_dec(v___x_5_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Int_decidableDvd___boxed(lean_object* v_a_8_, lean_object* v_b_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_Int_decidableDvd(v_a_8_, v_b_9_);
lean_dec(v_b_9_);
lean_dec(v_a_8_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
static lean_object* _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_12_; lean_object* v_intZero_13_; 
v_natZero_12_ = lean_unsigned_to_nat(0u);
v_intZero_13_ = lean_nat_to_int(v_natZero_12_);
return v_intZero_13_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg(lean_object* v_x_14_, lean_object* v_x_15_, lean_object* v_h__1_16_, lean_object* v_h__2_17_, lean_object* v_h__3_18_, lean_object* v_h__4_19_, lean_object* v_h__5_20_, lean_object* v_h__6_21_){
_start:
{
lean_object* v_natZero_22_; lean_object* v_intZero_23_; uint8_t v_isNeg_24_; 
v_natZero_22_ = lean_unsigned_to_nat(0u);
v_intZero_23_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0);
v_isNeg_24_ = lean_int_dec_lt(v_x_14_, v_intZero_23_);
if (v_isNeg_24_ == 0)
{
lean_object* v_a_25_; uint8_t v_isZero_26_; 
lean_dec(v_h__6_21_);
lean_dec(v_h__5_20_);
lean_dec(v_h__4_19_);
v_a_25_ = lean_nat_abs(v_x_14_);
v_isZero_26_ = lean_nat_dec_eq(v_a_25_, v_natZero_22_);
if (v_isZero_26_ == 1)
{
lean_object* v___x_27_; 
lean_dec(v_a_25_);
lean_dec(v_h__3_18_);
lean_dec(v_h__2_17_);
v___x_27_ = lean_apply_1(v_h__1_16_, v_x_15_);
return v___x_27_;
}
else
{
uint8_t v_isNeg_28_; 
lean_dec(v_h__1_16_);
v_isNeg_28_ = lean_int_dec_lt(v_x_15_, v_intZero_23_);
if (v_isNeg_28_ == 0)
{
lean_object* v_a_29_; lean_object* v___x_30_; 
lean_dec(v_h__3_18_);
v_a_29_ = lean_nat_abs(v_x_15_);
lean_dec(v_x_15_);
v___x_30_ = lean_apply_3(v_h__2_17_, v_a_25_, v_a_29_, lean_box(0));
return v___x_30_;
}
else
{
lean_object* v_one_31_; lean_object* v_n_32_; lean_object* v_abs_33_; lean_object* v_a_34_; lean_object* v___x_35_; 
lean_dec(v_h__2_17_);
v_one_31_ = lean_unsigned_to_nat(1u);
v_n_32_ = lean_nat_sub(v_a_25_, v_one_31_);
lean_dec(v_a_25_);
v_abs_33_ = lean_nat_abs(v_x_15_);
lean_dec(v_x_15_);
v_a_34_ = lean_nat_sub(v_abs_33_, v_one_31_);
lean_dec(v_abs_33_);
v___x_35_ = lean_apply_2(v_h__3_18_, v_n_32_, v_a_34_);
return v___x_35_;
}
}
}
else
{
lean_object* v_abs_36_; lean_object* v_one_37_; lean_object* v_a_38_; uint8_t v_isNeg_39_; 
lean_dec(v_h__3_18_);
lean_dec(v_h__2_17_);
lean_dec(v_h__1_16_);
v_abs_36_ = lean_nat_abs(v_x_14_);
v_one_37_ = lean_unsigned_to_nat(1u);
v_a_38_ = lean_nat_sub(v_abs_36_, v_one_37_);
lean_dec(v_abs_36_);
v_isNeg_39_ = lean_int_dec_lt(v_x_15_, v_intZero_23_);
if (v_isNeg_39_ == 0)
{
lean_object* v_a_40_; uint8_t v_isZero_41_; 
lean_dec(v_h__6_21_);
v_a_40_ = lean_nat_abs(v_x_15_);
lean_dec(v_x_15_);
v_isZero_41_ = lean_nat_dec_eq(v_a_40_, v_natZero_22_);
if (v_isZero_41_ == 1)
{
lean_object* v___x_42_; 
lean_dec(v_a_40_);
lean_dec(v_h__5_20_);
v___x_42_ = lean_apply_1(v_h__4_19_, v_a_38_);
return v___x_42_;
}
else
{
lean_object* v_n_43_; lean_object* v___x_44_; 
lean_dec(v_h__4_19_);
v_n_43_ = lean_nat_sub(v_a_40_, v_one_37_);
lean_dec(v_a_40_);
v___x_44_ = lean_apply_2(v_h__5_20_, v_a_38_, v_n_43_);
return v___x_44_;
}
}
else
{
lean_object* v_abs_45_; lean_object* v_a_46_; lean_object* v___x_47_; 
lean_dec(v_h__5_20_);
lean_dec(v_h__4_19_);
v_abs_45_ = lean_nat_abs(v_x_15_);
lean_dec(v_x_15_);
v_a_46_ = lean_nat_sub(v_abs_45_, v_one_37_);
lean_dec(v_abs_45_);
v___x_47_ = lean_apply_2(v_h__6_21_, v_a_38_, v_a_46_);
return v___x_47_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___boxed(lean_object* v_x_48_, lean_object* v_x_49_, lean_object* v_h__1_50_, lean_object* v_h__2_51_, lean_object* v_h__3_52_, lean_object* v_h__4_53_, lean_object* v_h__5_54_, lean_object* v_h__6_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg(v_x_48_, v_x_49_, v_h__1_50_, v_h__2_51_, v_h__3_52_, v_h__4_53_, v_h__5_54_, v_h__6_55_);
lean_dec(v_x_48_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter(lean_object* v_motive_57_, lean_object* v_x_58_, lean_object* v_x_59_, lean_object* v_h__1_60_, lean_object* v_h__2_61_, lean_object* v_h__3_62_, lean_object* v_h__4_63_, lean_object* v_h__5_64_, lean_object* v_h__6_65_){
_start:
{
lean_object* v_natZero_66_; lean_object* v_intZero_67_; uint8_t v_isNeg_68_; 
v_natZero_66_ = lean_unsigned_to_nat(0u);
v_intZero_67_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0);
v_isNeg_68_ = lean_int_dec_lt(v_x_58_, v_intZero_67_);
if (v_isNeg_68_ == 0)
{
lean_object* v_a_69_; uint8_t v_isZero_70_; 
lean_dec(v_h__6_65_);
lean_dec(v_h__5_64_);
lean_dec(v_h__4_63_);
v_a_69_ = lean_nat_abs(v_x_58_);
v_isZero_70_ = lean_nat_dec_eq(v_a_69_, v_natZero_66_);
if (v_isZero_70_ == 1)
{
lean_object* v___x_71_; 
lean_dec(v_a_69_);
lean_dec(v_h__3_62_);
lean_dec(v_h__2_61_);
v___x_71_ = lean_apply_1(v_h__1_60_, v_x_59_);
return v___x_71_;
}
else
{
uint8_t v_isNeg_72_; 
lean_dec(v_h__1_60_);
v_isNeg_72_ = lean_int_dec_lt(v_x_59_, v_intZero_67_);
if (v_isNeg_72_ == 0)
{
lean_object* v_a_73_; lean_object* v___x_74_; 
lean_dec(v_h__3_62_);
v_a_73_ = lean_nat_abs(v_x_59_);
lean_dec(v_x_59_);
v___x_74_ = lean_apply_3(v_h__2_61_, v_a_69_, v_a_73_, lean_box(0));
return v___x_74_;
}
else
{
lean_object* v_one_75_; lean_object* v_n_76_; lean_object* v_abs_77_; lean_object* v_a_78_; lean_object* v___x_79_; 
lean_dec(v_h__2_61_);
v_one_75_ = lean_unsigned_to_nat(1u);
v_n_76_ = lean_nat_sub(v_a_69_, v_one_75_);
lean_dec(v_a_69_);
v_abs_77_ = lean_nat_abs(v_x_59_);
lean_dec(v_x_59_);
v_a_78_ = lean_nat_sub(v_abs_77_, v_one_75_);
lean_dec(v_abs_77_);
v___x_79_ = lean_apply_2(v_h__3_62_, v_n_76_, v_a_78_);
return v___x_79_;
}
}
}
else
{
lean_object* v_abs_80_; lean_object* v_one_81_; lean_object* v_a_82_; uint8_t v_isNeg_83_; 
lean_dec(v_h__3_62_);
lean_dec(v_h__2_61_);
lean_dec(v_h__1_60_);
v_abs_80_ = lean_nat_abs(v_x_58_);
v_one_81_ = lean_unsigned_to_nat(1u);
v_a_82_ = lean_nat_sub(v_abs_80_, v_one_81_);
lean_dec(v_abs_80_);
v_isNeg_83_ = lean_int_dec_lt(v_x_59_, v_intZero_67_);
if (v_isNeg_83_ == 0)
{
lean_object* v_a_84_; uint8_t v_isZero_85_; 
lean_dec(v_h__6_65_);
v_a_84_ = lean_nat_abs(v_x_59_);
lean_dec(v_x_59_);
v_isZero_85_ = lean_nat_dec_eq(v_a_84_, v_natZero_66_);
if (v_isZero_85_ == 1)
{
lean_object* v___x_86_; 
lean_dec(v_a_84_);
lean_dec(v_h__5_64_);
v___x_86_ = lean_apply_1(v_h__4_63_, v_a_82_);
return v___x_86_;
}
else
{
lean_object* v_n_87_; lean_object* v___x_88_; 
lean_dec(v_h__4_63_);
v_n_87_ = lean_nat_sub(v_a_84_, v_one_81_);
lean_dec(v_a_84_);
v___x_88_ = lean_apply_2(v_h__5_64_, v_a_82_, v_n_87_);
return v___x_88_;
}
}
else
{
lean_object* v_abs_89_; lean_object* v_a_90_; lean_object* v___x_91_; 
lean_dec(v_h__5_64_);
lean_dec(v_h__4_63_);
v_abs_89_ = lean_nat_abs(v_x_59_);
lean_dec(v_x_59_);
v_a_90_ = lean_nat_sub(v_abs_89_, v_one_81_);
lean_dec(v_abs_89_);
v___x_91_ = lean_apply_2(v_h__6_65_, v_a_82_, v_a_90_);
return v___x_91_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___boxed(lean_object* v_motive_92_, lean_object* v_x_93_, lean_object* v_x_94_, lean_object* v_h__1_95_, lean_object* v_h__2_96_, lean_object* v_h__3_97_, lean_object* v_h__4_98_, lean_object* v_h__5_99_, lean_object* v_h__6_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter(v_motive_92_, v_x_93_, v_x_94_, v_h__1_95_, v_h__2_96_, v_h__3_97_, v_h__4_98_, v_h__5_99_, v_h__6_100_);
lean_dec(v_x_93_);
return v_res_101_;
}
}
static lean_object* _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_102_; lean_object* v_intZero_103_; 
v_natZero_102_ = lean_unsigned_to_nat(0u);
v_intZero_103_ = lean_nat_to_int(v_natZero_102_);
return v_intZero_103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg(lean_object* v_x_104_, lean_object* v_x_105_, lean_object* v_h__1_106_, lean_object* v_h__2_107_, lean_object* v_h__3_108_, lean_object* v_h__4_109_, lean_object* v_h__5_110_){
_start:
{
lean_object* v_natZero_111_; lean_object* v_intZero_112_; uint8_t v_isNeg_113_; 
v_natZero_111_ = lean_unsigned_to_nat(0u);
v_intZero_112_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0);
v_isNeg_113_ = lean_int_dec_lt(v_x_104_, v_intZero_112_);
if (v_isNeg_113_ == 0)
{
lean_object* v_a_114_; uint8_t v_isZero_115_; 
lean_dec(v_h__5_110_);
lean_dec(v_h__4_109_);
v_a_114_ = lean_nat_abs(v_x_104_);
v_isZero_115_ = lean_nat_dec_eq(v_a_114_, v_natZero_111_);
if (v_isZero_115_ == 1)
{
lean_object* v___x_116_; 
lean_dec(v_a_114_);
lean_dec(v_h__3_108_);
lean_dec(v_h__2_107_);
v___x_116_ = lean_apply_1(v_h__1_106_, v_x_105_);
return v___x_116_;
}
else
{
uint8_t v_isNeg_117_; 
lean_dec(v_h__1_106_);
v_isNeg_117_ = lean_int_dec_lt(v_x_105_, v_intZero_112_);
if (v_isNeg_117_ == 0)
{
lean_object* v_a_118_; lean_object* v___x_119_; 
lean_dec(v_h__3_108_);
v_a_118_ = lean_nat_abs(v_x_105_);
lean_dec(v_x_105_);
v___x_119_ = lean_apply_3(v_h__2_107_, v_a_114_, v_a_118_, lean_box(0));
return v___x_119_;
}
else
{
lean_object* v_one_120_; lean_object* v_n_121_; lean_object* v_abs_122_; lean_object* v_a_123_; lean_object* v___x_124_; 
lean_dec(v_h__2_107_);
v_one_120_ = lean_unsigned_to_nat(1u);
v_n_121_ = lean_nat_sub(v_a_114_, v_one_120_);
lean_dec(v_a_114_);
v_abs_122_ = lean_nat_abs(v_x_105_);
lean_dec(v_x_105_);
v_a_123_ = lean_nat_sub(v_abs_122_, v_one_120_);
lean_dec(v_abs_122_);
v___x_124_ = lean_apply_2(v_h__3_108_, v_n_121_, v_a_123_);
return v___x_124_;
}
}
}
else
{
lean_object* v_abs_125_; lean_object* v_one_126_; lean_object* v_a_127_; uint8_t v_isNeg_128_; 
lean_dec(v_h__3_108_);
lean_dec(v_h__2_107_);
lean_dec(v_h__1_106_);
v_abs_125_ = lean_nat_abs(v_x_104_);
v_one_126_ = lean_unsigned_to_nat(1u);
v_a_127_ = lean_nat_sub(v_abs_125_, v_one_126_);
lean_dec(v_abs_125_);
v_isNeg_128_ = lean_int_dec_lt(v_x_105_, v_intZero_112_);
if (v_isNeg_128_ == 0)
{
lean_object* v_a_129_; lean_object* v___x_130_; 
lean_dec(v_h__5_110_);
v_a_129_ = lean_nat_abs(v_x_105_);
lean_dec(v_x_105_);
v___x_130_ = lean_apply_2(v_h__4_109_, v_a_127_, v_a_129_);
return v___x_130_;
}
else
{
lean_object* v_abs_131_; lean_object* v_a_132_; lean_object* v___x_133_; 
lean_dec(v_h__4_109_);
v_abs_131_ = lean_nat_abs(v_x_105_);
lean_dec(v_x_105_);
v_a_132_ = lean_nat_sub(v_abs_131_, v_one_126_);
lean_dec(v_abs_131_);
v___x_133_ = lean_apply_2(v_h__5_110_, v_a_127_, v_a_132_);
return v___x_133_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___boxed(lean_object* v_x_134_, lean_object* v_x_135_, lean_object* v_h__1_136_, lean_object* v_h__2_137_, lean_object* v_h__3_138_, lean_object* v_h__4_139_, lean_object* v_h__5_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg(v_x_134_, v_x_135_, v_h__1_136_, v_h__2_137_, v_h__3_138_, v_h__4_139_, v_h__5_140_);
lean_dec(v_x_134_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter(lean_object* v_motive_142_, lean_object* v_x_143_, lean_object* v_x_144_, lean_object* v_h__1_145_, lean_object* v_h__2_146_, lean_object* v_h__3_147_, lean_object* v_h__4_148_, lean_object* v_h__5_149_){
_start:
{
lean_object* v_natZero_150_; lean_object* v_intZero_151_; uint8_t v_isNeg_152_; 
v_natZero_150_ = lean_unsigned_to_nat(0u);
v_intZero_151_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0);
v_isNeg_152_ = lean_int_dec_lt(v_x_143_, v_intZero_151_);
if (v_isNeg_152_ == 0)
{
lean_object* v_a_153_; uint8_t v_isZero_154_; 
lean_dec(v_h__5_149_);
lean_dec(v_h__4_148_);
v_a_153_ = lean_nat_abs(v_x_143_);
v_isZero_154_ = lean_nat_dec_eq(v_a_153_, v_natZero_150_);
if (v_isZero_154_ == 1)
{
lean_object* v___x_155_; 
lean_dec(v_a_153_);
lean_dec(v_h__3_147_);
lean_dec(v_h__2_146_);
v___x_155_ = lean_apply_1(v_h__1_145_, v_x_144_);
return v___x_155_;
}
else
{
uint8_t v_isNeg_156_; 
lean_dec(v_h__1_145_);
v_isNeg_156_ = lean_int_dec_lt(v_x_144_, v_intZero_151_);
if (v_isNeg_156_ == 0)
{
lean_object* v_a_157_; lean_object* v___x_158_; 
lean_dec(v_h__3_147_);
v_a_157_ = lean_nat_abs(v_x_144_);
lean_dec(v_x_144_);
v___x_158_ = lean_apply_3(v_h__2_146_, v_a_153_, v_a_157_, lean_box(0));
return v___x_158_;
}
else
{
lean_object* v_one_159_; lean_object* v_n_160_; lean_object* v_abs_161_; lean_object* v_a_162_; lean_object* v___x_163_; 
lean_dec(v_h__2_146_);
v_one_159_ = lean_unsigned_to_nat(1u);
v_n_160_ = lean_nat_sub(v_a_153_, v_one_159_);
lean_dec(v_a_153_);
v_abs_161_ = lean_nat_abs(v_x_144_);
lean_dec(v_x_144_);
v_a_162_ = lean_nat_sub(v_abs_161_, v_one_159_);
lean_dec(v_abs_161_);
v___x_163_ = lean_apply_2(v_h__3_147_, v_n_160_, v_a_162_);
return v___x_163_;
}
}
}
else
{
lean_object* v_abs_164_; lean_object* v_one_165_; lean_object* v_a_166_; uint8_t v_isNeg_167_; 
lean_dec(v_h__3_147_);
lean_dec(v_h__2_146_);
lean_dec(v_h__1_145_);
v_abs_164_ = lean_nat_abs(v_x_143_);
v_one_165_ = lean_unsigned_to_nat(1u);
v_a_166_ = lean_nat_sub(v_abs_164_, v_one_165_);
lean_dec(v_abs_164_);
v_isNeg_167_ = lean_int_dec_lt(v_x_144_, v_intZero_151_);
if (v_isNeg_167_ == 0)
{
lean_object* v_a_168_; lean_object* v___x_169_; 
lean_dec(v_h__5_149_);
v_a_168_ = lean_nat_abs(v_x_144_);
lean_dec(v_x_144_);
v___x_169_ = lean_apply_2(v_h__4_148_, v_a_166_, v_a_168_);
return v___x_169_;
}
else
{
lean_object* v_abs_170_; lean_object* v_a_171_; lean_object* v___x_172_; 
lean_dec(v_h__4_148_);
v_abs_170_ = lean_nat_abs(v_x_144_);
lean_dec(v_x_144_);
v_a_171_ = lean_nat_sub(v_abs_170_, v_one_165_);
lean_dec(v_abs_170_);
v___x_172_ = lean_apply_2(v_h__5_149_, v_a_166_, v_a_171_);
return v___x_172_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___boxed(lean_object* v_motive_173_, lean_object* v_x_174_, lean_object* v_x_175_, lean_object* v_h__1_176_, lean_object* v_h__2_177_, lean_object* v_h__3_178_, lean_object* v_h__4_179_, lean_object* v_h__5_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter(v_motive_173_, v_x_174_, v_x_175_, v_h__1_176_, v_h__2_177_, v_h__3_178_, v_h__4_179_, v_h__5_180_);
lean_dec(v_x_174_);
return v_res_181_;
}
}
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Div_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
lean_object* initialize_Init_NotationExtra(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Div_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_RCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Int_DivMod_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
