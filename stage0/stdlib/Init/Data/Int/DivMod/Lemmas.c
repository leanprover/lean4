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
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
static lean_once_cell_t l_Int_decidableDvd___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_decidableDvd___closed__0;
LEAN_EXPORT uint8_t l_Int_decidableDvd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_decidableDvd___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_12_; lean_object* v_intZero_13_; 
v_natZero_12_ = lean_unsigned_to_nat(0u);
v_intZero_13_ = lean_nat_to_int(v_natZero_12_);
return v_intZero_13_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___redArg(lean_object* v_x_14_, lean_object* v_x_15_, lean_object* v_h__1_16_, lean_object* v_h__2_17_, lean_object* v_h__3_18_, lean_object* v_h__4_19_){
_start:
{
lean_object* v_intZero_20_; uint8_t v_isNeg_21_; 
v_intZero_20_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___redArg___closed__0);
v_isNeg_21_ = lean_int_dec_lt(v_x_14_, v_intZero_20_);
if (v_isNeg_21_ == 0)
{
lean_object* v_a_22_; uint8_t v_isNeg_23_; 
lean_dec(v_h__4_19_);
lean_dec(v_h__3_18_);
v_a_22_ = lean_nat_abs(v_x_14_);
v_isNeg_23_ = lean_int_dec_lt(v_x_15_, v_intZero_20_);
if (v_isNeg_23_ == 0)
{
lean_object* v_a_24_; lean_object* v___x_25_; 
lean_dec(v_h__2_17_);
v_a_24_ = lean_nat_abs(v_x_15_);
v___x_25_ = lean_apply_2(v_h__1_16_, v_a_22_, v_a_24_);
return v___x_25_;
}
else
{
lean_object* v_abs_26_; lean_object* v_one_27_; lean_object* v_a_28_; lean_object* v___x_29_; 
lean_dec(v_h__1_16_);
v_abs_26_ = lean_nat_abs(v_x_15_);
v_one_27_ = lean_unsigned_to_nat(1u);
v_a_28_ = lean_nat_sub(v_abs_26_, v_one_27_);
lean_dec(v_abs_26_);
v___x_29_ = lean_apply_2(v_h__2_17_, v_a_22_, v_a_28_);
return v___x_29_;
}
}
else
{
lean_object* v_abs_30_; lean_object* v_one_31_; lean_object* v_a_32_; uint8_t v_isNeg_33_; 
lean_dec(v_h__2_17_);
lean_dec(v_h__1_16_);
v_abs_30_ = lean_nat_abs(v_x_14_);
v_one_31_ = lean_unsigned_to_nat(1u);
v_a_32_ = lean_nat_sub(v_abs_30_, v_one_31_);
lean_dec(v_abs_30_);
v_isNeg_33_ = lean_int_dec_lt(v_x_15_, v_intZero_20_);
if (v_isNeg_33_ == 0)
{
lean_object* v_a_34_; lean_object* v___x_35_; 
lean_dec(v_h__4_19_);
v_a_34_ = lean_nat_abs(v_x_15_);
v___x_35_ = lean_apply_2(v_h__3_18_, v_a_32_, v_a_34_);
return v___x_35_;
}
else
{
lean_object* v_abs_36_; lean_object* v_a_37_; lean_object* v___x_38_; 
lean_dec(v_h__3_18_);
v_abs_36_ = lean_nat_abs(v_x_15_);
v_a_37_ = lean_nat_sub(v_abs_36_, v_one_31_);
lean_dec(v_abs_36_);
v___x_38_ = lean_apply_2(v_h__4_19_, v_a_32_, v_a_37_);
return v___x_38_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___redArg___boxed(lean_object* v_x_39_, lean_object* v_x_40_, lean_object* v_h__1_41_, lean_object* v_h__2_42_, lean_object* v_h__3_43_, lean_object* v_h__4_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___redArg(v_x_39_, v_x_40_, v_h__1_41_, v_h__2_42_, v_h__3_43_, v_h__4_44_);
lean_dec(v_x_40_);
lean_dec(v_x_39_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter(lean_object* v_motive_46_, lean_object* v_x_47_, lean_object* v_x_48_, lean_object* v_h__1_49_, lean_object* v_h__2_50_, lean_object* v_h__3_51_, lean_object* v_h__4_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___redArg(v_x_47_, v_x_48_, v_h__1_49_, v_h__2_50_, v_h__3_51_, v_h__4_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___boxed(lean_object* v_motive_54_, lean_object* v_x_55_, lean_object* v_x_56_, lean_object* v_h__1_57_, lean_object* v_h__2_58_, lean_object* v_h__3_59_, lean_object* v_h__4_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter(v_motive_54_, v_x_55_, v_x_56_, v_h__1_57_, v_h__2_58_, v_h__3_59_, v_h__4_60_);
lean_dec(v_x_56_);
lean_dec(v_x_55_);
return v_res_61_;
}
}
static lean_object* _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_62_; lean_object* v_intZero_63_; 
v_natZero_62_ = lean_unsigned_to_nat(0u);
v_intZero_63_ = lean_nat_to_int(v_natZero_62_);
return v_intZero_63_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg(lean_object* v_x_64_, lean_object* v_x_65_, lean_object* v_h__1_66_, lean_object* v_h__2_67_){
_start:
{
lean_object* v_intZero_68_; uint8_t v_isNeg_69_; 
v_intZero_68_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0);
v_isNeg_69_ = lean_int_dec_lt(v_x_64_, v_intZero_68_);
if (v_isNeg_69_ == 0)
{
lean_object* v_a_70_; lean_object* v___x_71_; 
lean_dec(v_h__2_67_);
v_a_70_ = lean_nat_abs(v_x_64_);
v___x_71_ = lean_apply_2(v_h__1_66_, v_a_70_, v_x_65_);
return v___x_71_;
}
else
{
lean_object* v_abs_72_; lean_object* v_one_73_; lean_object* v_a_74_; lean_object* v___x_75_; 
lean_dec(v_h__1_66_);
v_abs_72_ = lean_nat_abs(v_x_64_);
v_one_73_ = lean_unsigned_to_nat(1u);
v_a_74_ = lean_nat_sub(v_abs_72_, v_one_73_);
lean_dec(v_abs_72_);
v___x_75_ = lean_apply_2(v_h__2_67_, v_a_74_, v_x_65_);
return v___x_75_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___boxed(lean_object* v_x_76_, lean_object* v_x_77_, lean_object* v_h__1_78_, lean_object* v_h__2_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg(v_x_76_, v_x_77_, v_h__1_78_, v_h__2_79_);
lean_dec(v_x_76_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter(lean_object* v_motive_81_, lean_object* v_x_82_, lean_object* v_x_83_, lean_object* v_h__1_84_, lean_object* v_h__2_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg(v_x_82_, v_x_83_, v_h__1_84_, v_h__2_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___boxed(lean_object* v_motive_87_, lean_object* v_x_88_, lean_object* v_x_89_, lean_object* v_h__1_90_, lean_object* v_h__2_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter(v_motive_87_, v_x_88_, v_x_89_, v_h__1_90_, v_h__2_91_);
lean_dec(v_x_88_);
return v_res_92_;
}
}
static lean_object* _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_93_; lean_object* v_intZero_94_; 
v_natZero_93_ = lean_unsigned_to_nat(0u);
v_intZero_94_ = lean_nat_to_int(v_natZero_93_);
return v_intZero_94_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg(lean_object* v_x_95_, lean_object* v_x_96_, lean_object* v_h__1_97_, lean_object* v_h__2_98_, lean_object* v_h__3_99_, lean_object* v_h__4_100_, lean_object* v_h__5_101_, lean_object* v_h__6_102_){
_start:
{
lean_object* v_natZero_103_; lean_object* v_intZero_104_; uint8_t v_isNeg_105_; 
v_natZero_103_ = lean_unsigned_to_nat(0u);
v_intZero_104_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0);
v_isNeg_105_ = lean_int_dec_lt(v_x_95_, v_intZero_104_);
if (v_isNeg_105_ == 0)
{
lean_object* v_a_106_; uint8_t v_isZero_107_; 
lean_dec(v_h__6_102_);
lean_dec(v_h__5_101_);
lean_dec(v_h__4_100_);
v_a_106_ = lean_nat_abs(v_x_95_);
v_isZero_107_ = lean_nat_dec_eq(v_a_106_, v_natZero_103_);
if (v_isZero_107_ == 1)
{
lean_object* v___x_108_; 
lean_dec(v_a_106_);
lean_dec(v_h__3_99_);
lean_dec(v_h__2_98_);
v___x_108_ = lean_apply_1(v_h__1_97_, v_x_96_);
return v___x_108_;
}
else
{
uint8_t v_isNeg_109_; 
lean_dec(v_h__1_97_);
v_isNeg_109_ = lean_int_dec_lt(v_x_96_, v_intZero_104_);
if (v_isNeg_109_ == 0)
{
lean_object* v_a_110_; lean_object* v___x_111_; 
lean_dec(v_h__3_99_);
v_a_110_ = lean_nat_abs(v_x_96_);
lean_dec(v_x_96_);
v___x_111_ = lean_apply_3(v_h__2_98_, v_a_106_, v_a_110_, lean_box(0));
return v___x_111_;
}
else
{
lean_object* v_one_112_; lean_object* v_n_113_; lean_object* v_abs_114_; lean_object* v_a_115_; lean_object* v___x_116_; 
lean_dec(v_h__2_98_);
v_one_112_ = lean_unsigned_to_nat(1u);
v_n_113_ = lean_nat_sub(v_a_106_, v_one_112_);
lean_dec(v_a_106_);
v_abs_114_ = lean_nat_abs(v_x_96_);
lean_dec(v_x_96_);
v_a_115_ = lean_nat_sub(v_abs_114_, v_one_112_);
lean_dec(v_abs_114_);
v___x_116_ = lean_apply_2(v_h__3_99_, v_n_113_, v_a_115_);
return v___x_116_;
}
}
}
else
{
lean_object* v_abs_117_; lean_object* v_one_118_; lean_object* v_a_119_; uint8_t v_isNeg_120_; 
lean_dec(v_h__3_99_);
lean_dec(v_h__2_98_);
lean_dec(v_h__1_97_);
v_abs_117_ = lean_nat_abs(v_x_95_);
v_one_118_ = lean_unsigned_to_nat(1u);
v_a_119_ = lean_nat_sub(v_abs_117_, v_one_118_);
lean_dec(v_abs_117_);
v_isNeg_120_ = lean_int_dec_lt(v_x_96_, v_intZero_104_);
if (v_isNeg_120_ == 0)
{
lean_object* v_a_121_; uint8_t v_isZero_122_; 
lean_dec(v_h__6_102_);
v_a_121_ = lean_nat_abs(v_x_96_);
lean_dec(v_x_96_);
v_isZero_122_ = lean_nat_dec_eq(v_a_121_, v_natZero_103_);
if (v_isZero_122_ == 1)
{
lean_object* v___x_123_; 
lean_dec(v_a_121_);
lean_dec(v_h__5_101_);
v___x_123_ = lean_apply_1(v_h__4_100_, v_a_119_);
return v___x_123_;
}
else
{
lean_object* v_n_124_; lean_object* v___x_125_; 
lean_dec(v_h__4_100_);
v_n_124_ = lean_nat_sub(v_a_121_, v_one_118_);
lean_dec(v_a_121_);
v___x_125_ = lean_apply_2(v_h__5_101_, v_a_119_, v_n_124_);
return v___x_125_;
}
}
else
{
lean_object* v_abs_126_; lean_object* v_a_127_; lean_object* v___x_128_; 
lean_dec(v_h__5_101_);
lean_dec(v_h__4_100_);
v_abs_126_ = lean_nat_abs(v_x_96_);
lean_dec(v_x_96_);
v_a_127_ = lean_nat_sub(v_abs_126_, v_one_118_);
lean_dec(v_abs_126_);
v___x_128_ = lean_apply_2(v_h__6_102_, v_a_119_, v_a_127_);
return v___x_128_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___boxed(lean_object* v_x_129_, lean_object* v_x_130_, lean_object* v_h__1_131_, lean_object* v_h__2_132_, lean_object* v_h__3_133_, lean_object* v_h__4_134_, lean_object* v_h__5_135_, lean_object* v_h__6_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg(v_x_129_, v_x_130_, v_h__1_131_, v_h__2_132_, v_h__3_133_, v_h__4_134_, v_h__5_135_, v_h__6_136_);
lean_dec(v_x_129_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter(lean_object* v_motive_138_, lean_object* v_x_139_, lean_object* v_x_140_, lean_object* v_h__1_141_, lean_object* v_h__2_142_, lean_object* v_h__3_143_, lean_object* v_h__4_144_, lean_object* v_h__5_145_, lean_object* v_h__6_146_){
_start:
{
lean_object* v_natZero_147_; lean_object* v_intZero_148_; uint8_t v_isNeg_149_; 
v_natZero_147_ = lean_unsigned_to_nat(0u);
v_intZero_148_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0);
v_isNeg_149_ = lean_int_dec_lt(v_x_139_, v_intZero_148_);
if (v_isNeg_149_ == 0)
{
lean_object* v_a_150_; uint8_t v_isZero_151_; 
lean_dec(v_h__6_146_);
lean_dec(v_h__5_145_);
lean_dec(v_h__4_144_);
v_a_150_ = lean_nat_abs(v_x_139_);
v_isZero_151_ = lean_nat_dec_eq(v_a_150_, v_natZero_147_);
if (v_isZero_151_ == 1)
{
lean_object* v___x_152_; 
lean_dec(v_a_150_);
lean_dec(v_h__3_143_);
lean_dec(v_h__2_142_);
v___x_152_ = lean_apply_1(v_h__1_141_, v_x_140_);
return v___x_152_;
}
else
{
uint8_t v_isNeg_153_; 
lean_dec(v_h__1_141_);
v_isNeg_153_ = lean_int_dec_lt(v_x_140_, v_intZero_148_);
if (v_isNeg_153_ == 0)
{
lean_object* v_a_154_; lean_object* v___x_155_; 
lean_dec(v_h__3_143_);
v_a_154_ = lean_nat_abs(v_x_140_);
lean_dec(v_x_140_);
v___x_155_ = lean_apply_3(v_h__2_142_, v_a_150_, v_a_154_, lean_box(0));
return v___x_155_;
}
else
{
lean_object* v_one_156_; lean_object* v_n_157_; lean_object* v_abs_158_; lean_object* v_a_159_; lean_object* v___x_160_; 
lean_dec(v_h__2_142_);
v_one_156_ = lean_unsigned_to_nat(1u);
v_n_157_ = lean_nat_sub(v_a_150_, v_one_156_);
lean_dec(v_a_150_);
v_abs_158_ = lean_nat_abs(v_x_140_);
lean_dec(v_x_140_);
v_a_159_ = lean_nat_sub(v_abs_158_, v_one_156_);
lean_dec(v_abs_158_);
v___x_160_ = lean_apply_2(v_h__3_143_, v_n_157_, v_a_159_);
return v___x_160_;
}
}
}
else
{
lean_object* v_abs_161_; lean_object* v_one_162_; lean_object* v_a_163_; uint8_t v_isNeg_164_; 
lean_dec(v_h__3_143_);
lean_dec(v_h__2_142_);
lean_dec(v_h__1_141_);
v_abs_161_ = lean_nat_abs(v_x_139_);
v_one_162_ = lean_unsigned_to_nat(1u);
v_a_163_ = lean_nat_sub(v_abs_161_, v_one_162_);
lean_dec(v_abs_161_);
v_isNeg_164_ = lean_int_dec_lt(v_x_140_, v_intZero_148_);
if (v_isNeg_164_ == 0)
{
lean_object* v_a_165_; uint8_t v_isZero_166_; 
lean_dec(v_h__6_146_);
v_a_165_ = lean_nat_abs(v_x_140_);
lean_dec(v_x_140_);
v_isZero_166_ = lean_nat_dec_eq(v_a_165_, v_natZero_147_);
if (v_isZero_166_ == 1)
{
lean_object* v___x_167_; 
lean_dec(v_a_165_);
lean_dec(v_h__5_145_);
v___x_167_ = lean_apply_1(v_h__4_144_, v_a_163_);
return v___x_167_;
}
else
{
lean_object* v_n_168_; lean_object* v___x_169_; 
lean_dec(v_h__4_144_);
v_n_168_ = lean_nat_sub(v_a_165_, v_one_162_);
lean_dec(v_a_165_);
v___x_169_ = lean_apply_2(v_h__5_145_, v_a_163_, v_n_168_);
return v___x_169_;
}
}
else
{
lean_object* v_abs_170_; lean_object* v_a_171_; lean_object* v___x_172_; 
lean_dec(v_h__5_145_);
lean_dec(v_h__4_144_);
v_abs_170_ = lean_nat_abs(v_x_140_);
lean_dec(v_x_140_);
v_a_171_ = lean_nat_sub(v_abs_170_, v_one_162_);
lean_dec(v_abs_170_);
v___x_172_ = lean_apply_2(v_h__6_146_, v_a_163_, v_a_171_);
return v___x_172_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___boxed(lean_object* v_motive_173_, lean_object* v_x_174_, lean_object* v_x_175_, lean_object* v_h__1_176_, lean_object* v_h__2_177_, lean_object* v_h__3_178_, lean_object* v_h__4_179_, lean_object* v_h__5_180_, lean_object* v_h__6_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter(v_motive_173_, v_x_174_, v_x_175_, v_h__1_176_, v_h__2_177_, v_h__3_178_, v_h__4_179_, v_h__5_180_, v_h__6_181_);
lean_dec(v_x_174_);
return v_res_182_;
}
}
static lean_object* _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_183_; lean_object* v_intZero_184_; 
v_natZero_183_ = lean_unsigned_to_nat(0u);
v_intZero_184_ = lean_nat_to_int(v_natZero_183_);
return v_intZero_184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg(lean_object* v_x_185_, lean_object* v_x_186_, lean_object* v_h__1_187_, lean_object* v_h__2_188_, lean_object* v_h__3_189_, lean_object* v_h__4_190_, lean_object* v_h__5_191_){
_start:
{
lean_object* v_natZero_192_; lean_object* v_intZero_193_; uint8_t v_isNeg_194_; 
v_natZero_192_ = lean_unsigned_to_nat(0u);
v_intZero_193_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0);
v_isNeg_194_ = lean_int_dec_lt(v_x_185_, v_intZero_193_);
if (v_isNeg_194_ == 0)
{
lean_object* v_a_195_; uint8_t v_isZero_196_; 
lean_dec(v_h__5_191_);
lean_dec(v_h__4_190_);
v_a_195_ = lean_nat_abs(v_x_185_);
v_isZero_196_ = lean_nat_dec_eq(v_a_195_, v_natZero_192_);
if (v_isZero_196_ == 1)
{
lean_object* v___x_197_; 
lean_dec(v_a_195_);
lean_dec(v_h__3_189_);
lean_dec(v_h__2_188_);
v___x_197_ = lean_apply_1(v_h__1_187_, v_x_186_);
return v___x_197_;
}
else
{
uint8_t v_isNeg_198_; 
lean_dec(v_h__1_187_);
v_isNeg_198_ = lean_int_dec_lt(v_x_186_, v_intZero_193_);
if (v_isNeg_198_ == 0)
{
lean_object* v_a_199_; lean_object* v___x_200_; 
lean_dec(v_h__3_189_);
v_a_199_ = lean_nat_abs(v_x_186_);
lean_dec(v_x_186_);
v___x_200_ = lean_apply_3(v_h__2_188_, v_a_195_, v_a_199_, lean_box(0));
return v___x_200_;
}
else
{
lean_object* v_one_201_; lean_object* v_n_202_; lean_object* v_abs_203_; lean_object* v_a_204_; lean_object* v___x_205_; 
lean_dec(v_h__2_188_);
v_one_201_ = lean_unsigned_to_nat(1u);
v_n_202_ = lean_nat_sub(v_a_195_, v_one_201_);
lean_dec(v_a_195_);
v_abs_203_ = lean_nat_abs(v_x_186_);
lean_dec(v_x_186_);
v_a_204_ = lean_nat_sub(v_abs_203_, v_one_201_);
lean_dec(v_abs_203_);
v___x_205_ = lean_apply_2(v_h__3_189_, v_n_202_, v_a_204_);
return v___x_205_;
}
}
}
else
{
lean_object* v_abs_206_; lean_object* v_one_207_; lean_object* v_a_208_; uint8_t v_isNeg_209_; 
lean_dec(v_h__3_189_);
lean_dec(v_h__2_188_);
lean_dec(v_h__1_187_);
v_abs_206_ = lean_nat_abs(v_x_185_);
v_one_207_ = lean_unsigned_to_nat(1u);
v_a_208_ = lean_nat_sub(v_abs_206_, v_one_207_);
lean_dec(v_abs_206_);
v_isNeg_209_ = lean_int_dec_lt(v_x_186_, v_intZero_193_);
if (v_isNeg_209_ == 0)
{
lean_object* v_a_210_; lean_object* v___x_211_; 
lean_dec(v_h__5_191_);
v_a_210_ = lean_nat_abs(v_x_186_);
lean_dec(v_x_186_);
v___x_211_ = lean_apply_2(v_h__4_190_, v_a_208_, v_a_210_);
return v___x_211_;
}
else
{
lean_object* v_abs_212_; lean_object* v_a_213_; lean_object* v___x_214_; 
lean_dec(v_h__4_190_);
v_abs_212_ = lean_nat_abs(v_x_186_);
lean_dec(v_x_186_);
v_a_213_ = lean_nat_sub(v_abs_212_, v_one_207_);
lean_dec(v_abs_212_);
v___x_214_ = lean_apply_2(v_h__5_191_, v_a_208_, v_a_213_);
return v___x_214_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___boxed(lean_object* v_x_215_, lean_object* v_x_216_, lean_object* v_h__1_217_, lean_object* v_h__2_218_, lean_object* v_h__3_219_, lean_object* v_h__4_220_, lean_object* v_h__5_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg(v_x_215_, v_x_216_, v_h__1_217_, v_h__2_218_, v_h__3_219_, v_h__4_220_, v_h__5_221_);
lean_dec(v_x_215_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter(lean_object* v_motive_223_, lean_object* v_x_224_, lean_object* v_x_225_, lean_object* v_h__1_226_, lean_object* v_h__2_227_, lean_object* v_h__3_228_, lean_object* v_h__4_229_, lean_object* v_h__5_230_){
_start:
{
lean_object* v_natZero_231_; lean_object* v_intZero_232_; uint8_t v_isNeg_233_; 
v_natZero_231_ = lean_unsigned_to_nat(0u);
v_intZero_232_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0);
v_isNeg_233_ = lean_int_dec_lt(v_x_224_, v_intZero_232_);
if (v_isNeg_233_ == 0)
{
lean_object* v_a_234_; uint8_t v_isZero_235_; 
lean_dec(v_h__5_230_);
lean_dec(v_h__4_229_);
v_a_234_ = lean_nat_abs(v_x_224_);
v_isZero_235_ = lean_nat_dec_eq(v_a_234_, v_natZero_231_);
if (v_isZero_235_ == 1)
{
lean_object* v___x_236_; 
lean_dec(v_a_234_);
lean_dec(v_h__3_228_);
lean_dec(v_h__2_227_);
v___x_236_ = lean_apply_1(v_h__1_226_, v_x_225_);
return v___x_236_;
}
else
{
uint8_t v_isNeg_237_; 
lean_dec(v_h__1_226_);
v_isNeg_237_ = lean_int_dec_lt(v_x_225_, v_intZero_232_);
if (v_isNeg_237_ == 0)
{
lean_object* v_a_238_; lean_object* v___x_239_; 
lean_dec(v_h__3_228_);
v_a_238_ = lean_nat_abs(v_x_225_);
lean_dec(v_x_225_);
v___x_239_ = lean_apply_3(v_h__2_227_, v_a_234_, v_a_238_, lean_box(0));
return v___x_239_;
}
else
{
lean_object* v_one_240_; lean_object* v_n_241_; lean_object* v_abs_242_; lean_object* v_a_243_; lean_object* v___x_244_; 
lean_dec(v_h__2_227_);
v_one_240_ = lean_unsigned_to_nat(1u);
v_n_241_ = lean_nat_sub(v_a_234_, v_one_240_);
lean_dec(v_a_234_);
v_abs_242_ = lean_nat_abs(v_x_225_);
lean_dec(v_x_225_);
v_a_243_ = lean_nat_sub(v_abs_242_, v_one_240_);
lean_dec(v_abs_242_);
v___x_244_ = lean_apply_2(v_h__3_228_, v_n_241_, v_a_243_);
return v___x_244_;
}
}
}
else
{
lean_object* v_abs_245_; lean_object* v_one_246_; lean_object* v_a_247_; uint8_t v_isNeg_248_; 
lean_dec(v_h__3_228_);
lean_dec(v_h__2_227_);
lean_dec(v_h__1_226_);
v_abs_245_ = lean_nat_abs(v_x_224_);
v_one_246_ = lean_unsigned_to_nat(1u);
v_a_247_ = lean_nat_sub(v_abs_245_, v_one_246_);
lean_dec(v_abs_245_);
v_isNeg_248_ = lean_int_dec_lt(v_x_225_, v_intZero_232_);
if (v_isNeg_248_ == 0)
{
lean_object* v_a_249_; lean_object* v___x_250_; 
lean_dec(v_h__5_230_);
v_a_249_ = lean_nat_abs(v_x_225_);
lean_dec(v_x_225_);
v___x_250_ = lean_apply_2(v_h__4_229_, v_a_247_, v_a_249_);
return v___x_250_;
}
else
{
lean_object* v_abs_251_; lean_object* v_a_252_; lean_object* v___x_253_; 
lean_dec(v_h__4_229_);
v_abs_251_ = lean_nat_abs(v_x_225_);
lean_dec(v_x_225_);
v_a_252_ = lean_nat_sub(v_abs_251_, v_one_246_);
lean_dec(v_abs_251_);
v___x_253_ = lean_apply_2(v_h__5_230_, v_a_247_, v_a_252_);
return v___x_253_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___boxed(lean_object* v_motive_254_, lean_object* v_x_255_, lean_object* v_x_256_, lean_object* v_h__1_257_, lean_object* v_h__2_258_, lean_object* v_h__3_259_, lean_object* v_h__4_260_, lean_object* v_h__5_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter(v_motive_254_, v_x_255_, v_x_256_, v_h__1_257_, v_h__2_258_, v_h__3_259_, v_h__4_260_, v_h__5_261_);
lean_dec(v_x_255_);
return v_res_262_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
