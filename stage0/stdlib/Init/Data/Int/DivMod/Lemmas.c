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
lean_object* v_intZero_53_; uint8_t v_isNeg_54_; 
v_intZero_53_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___redArg___closed__0);
v_isNeg_54_ = lean_int_dec_lt(v_x_47_, v_intZero_53_);
if (v_isNeg_54_ == 0)
{
lean_object* v_a_55_; uint8_t v_isNeg_56_; 
lean_dec(v_h__4_52_);
lean_dec(v_h__3_51_);
v_a_55_ = lean_nat_abs(v_x_47_);
v_isNeg_56_ = lean_int_dec_lt(v_x_48_, v_intZero_53_);
if (v_isNeg_56_ == 0)
{
lean_object* v_a_57_; lean_object* v___x_58_; 
lean_dec(v_h__2_50_);
v_a_57_ = lean_nat_abs(v_x_48_);
v___x_58_ = lean_apply_2(v_h__1_49_, v_a_55_, v_a_57_);
return v___x_58_;
}
else
{
lean_object* v_abs_59_; lean_object* v_one_60_; lean_object* v_a_61_; lean_object* v___x_62_; 
lean_dec(v_h__1_49_);
v_abs_59_ = lean_nat_abs(v_x_48_);
v_one_60_ = lean_unsigned_to_nat(1u);
v_a_61_ = lean_nat_sub(v_abs_59_, v_one_60_);
lean_dec(v_abs_59_);
v___x_62_ = lean_apply_2(v_h__2_50_, v_a_55_, v_a_61_);
return v___x_62_;
}
}
else
{
lean_object* v_abs_63_; lean_object* v_one_64_; lean_object* v_a_65_; uint8_t v_isNeg_66_; 
lean_dec(v_h__2_50_);
lean_dec(v_h__1_49_);
v_abs_63_ = lean_nat_abs(v_x_47_);
v_one_64_ = lean_unsigned_to_nat(1u);
v_a_65_ = lean_nat_sub(v_abs_63_, v_one_64_);
lean_dec(v_abs_63_);
v_isNeg_66_ = lean_int_dec_lt(v_x_48_, v_intZero_53_);
if (v_isNeg_66_ == 0)
{
lean_object* v_a_67_; lean_object* v___x_68_; 
lean_dec(v_h__4_52_);
v_a_67_ = lean_nat_abs(v_x_48_);
v___x_68_ = lean_apply_2(v_h__3_51_, v_a_65_, v_a_67_);
return v___x_68_;
}
else
{
lean_object* v_abs_69_; lean_object* v_a_70_; lean_object* v___x_71_; 
lean_dec(v_h__3_51_);
v_abs_69_ = lean_nat_abs(v_x_48_);
v_a_70_ = lean_nat_sub(v_abs_69_, v_one_64_);
lean_dec(v_abs_69_);
v___x_71_ = lean_apply_2(v_h__4_52_, v_a_65_, v_a_70_);
return v___x_71_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___boxed(lean_object* v_motive_72_, lean_object* v_x_73_, lean_object* v_x_74_, lean_object* v_h__1_75_, lean_object* v_h__2_76_, lean_object* v_h__3_77_, lean_object* v_h__4_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter(v_motive_72_, v_x_73_, v_x_74_, v_h__1_75_, v_h__2_76_, v_h__3_77_, v_h__4_78_);
lean_dec(v_x_74_);
lean_dec(v_x_73_);
return v_res_79_;
}
}
static lean_object* _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_80_; lean_object* v_intZero_81_; 
v_natZero_80_ = lean_unsigned_to_nat(0u);
v_intZero_81_ = lean_nat_to_int(v_natZero_80_);
return v_intZero_81_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg(lean_object* v_x_82_, lean_object* v_x_83_, lean_object* v_h__1_84_, lean_object* v_h__2_85_){
_start:
{
lean_object* v_intZero_86_; uint8_t v_isNeg_87_; 
v_intZero_86_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0);
v_isNeg_87_ = lean_int_dec_lt(v_x_82_, v_intZero_86_);
if (v_isNeg_87_ == 0)
{
lean_object* v_a_88_; lean_object* v___x_89_; 
lean_dec(v_h__2_85_);
v_a_88_ = lean_nat_abs(v_x_82_);
v___x_89_ = lean_apply_2(v_h__1_84_, v_a_88_, v_x_83_);
return v___x_89_;
}
else
{
lean_object* v_abs_90_; lean_object* v_one_91_; lean_object* v_a_92_; lean_object* v___x_93_; 
lean_dec(v_h__1_84_);
v_abs_90_ = lean_nat_abs(v_x_82_);
v_one_91_ = lean_unsigned_to_nat(1u);
v_a_92_ = lean_nat_sub(v_abs_90_, v_one_91_);
lean_dec(v_abs_90_);
v___x_93_ = lean_apply_2(v_h__2_85_, v_a_92_, v_x_83_);
return v___x_93_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___boxed(lean_object* v_x_94_, lean_object* v_x_95_, lean_object* v_h__1_96_, lean_object* v_h__2_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg(v_x_94_, v_x_95_, v_h__1_96_, v_h__2_97_);
lean_dec(v_x_94_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter(lean_object* v_motive_99_, lean_object* v_x_100_, lean_object* v_x_101_, lean_object* v_h__1_102_, lean_object* v_h__2_103_){
_start:
{
lean_object* v_intZero_104_; uint8_t v_isNeg_105_; 
v_intZero_104_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0);
v_isNeg_105_ = lean_int_dec_lt(v_x_100_, v_intZero_104_);
if (v_isNeg_105_ == 0)
{
lean_object* v_a_106_; lean_object* v___x_107_; 
lean_dec(v_h__2_103_);
v_a_106_ = lean_nat_abs(v_x_100_);
v___x_107_ = lean_apply_2(v_h__1_102_, v_a_106_, v_x_101_);
return v___x_107_;
}
else
{
lean_object* v_abs_108_; lean_object* v_one_109_; lean_object* v_a_110_; lean_object* v___x_111_; 
lean_dec(v_h__1_102_);
v_abs_108_ = lean_nat_abs(v_x_100_);
v_one_109_ = lean_unsigned_to_nat(1u);
v_a_110_ = lean_nat_sub(v_abs_108_, v_one_109_);
lean_dec(v_abs_108_);
v___x_111_ = lean_apply_2(v_h__2_103_, v_a_110_, v_x_101_);
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___boxed(lean_object* v_motive_112_, lean_object* v_x_113_, lean_object* v_x_114_, lean_object* v_h__1_115_, lean_object* v_h__2_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter(v_motive_112_, v_x_113_, v_x_114_, v_h__1_115_, v_h__2_116_);
lean_dec(v_x_113_);
return v_res_117_;
}
}
static lean_object* _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_118_; lean_object* v_intZero_119_; 
v_natZero_118_ = lean_unsigned_to_nat(0u);
v_intZero_119_ = lean_nat_to_int(v_natZero_118_);
return v_intZero_119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg(lean_object* v_x_120_, lean_object* v_x_121_, lean_object* v_h__1_122_, lean_object* v_h__2_123_, lean_object* v_h__3_124_, lean_object* v_h__4_125_, lean_object* v_h__5_126_, lean_object* v_h__6_127_){
_start:
{
lean_object* v_natZero_128_; lean_object* v_intZero_129_; uint8_t v_isNeg_130_; 
v_natZero_128_ = lean_unsigned_to_nat(0u);
v_intZero_129_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0);
v_isNeg_130_ = lean_int_dec_lt(v_x_120_, v_intZero_129_);
if (v_isNeg_130_ == 0)
{
lean_object* v_a_131_; uint8_t v_isZero_132_; 
lean_dec(v_h__6_127_);
lean_dec(v_h__5_126_);
lean_dec(v_h__4_125_);
v_a_131_ = lean_nat_abs(v_x_120_);
v_isZero_132_ = lean_nat_dec_eq(v_a_131_, v_natZero_128_);
if (v_isZero_132_ == 1)
{
lean_object* v___x_133_; 
lean_dec(v_a_131_);
lean_dec(v_h__3_124_);
lean_dec(v_h__2_123_);
v___x_133_ = lean_apply_1(v_h__1_122_, v_x_121_);
return v___x_133_;
}
else
{
uint8_t v_isNeg_134_; 
lean_dec(v_h__1_122_);
v_isNeg_134_ = lean_int_dec_lt(v_x_121_, v_intZero_129_);
if (v_isNeg_134_ == 0)
{
lean_object* v_a_135_; lean_object* v___x_136_; 
lean_dec(v_h__3_124_);
v_a_135_ = lean_nat_abs(v_x_121_);
lean_dec(v_x_121_);
v___x_136_ = lean_apply_3(v_h__2_123_, v_a_131_, v_a_135_, lean_box(0));
return v___x_136_;
}
else
{
lean_object* v_one_137_; lean_object* v_n_138_; lean_object* v_abs_139_; lean_object* v_a_140_; lean_object* v___x_141_; 
lean_dec(v_h__2_123_);
v_one_137_ = lean_unsigned_to_nat(1u);
v_n_138_ = lean_nat_sub(v_a_131_, v_one_137_);
lean_dec(v_a_131_);
v_abs_139_ = lean_nat_abs(v_x_121_);
lean_dec(v_x_121_);
v_a_140_ = lean_nat_sub(v_abs_139_, v_one_137_);
lean_dec(v_abs_139_);
v___x_141_ = lean_apply_2(v_h__3_124_, v_n_138_, v_a_140_);
return v___x_141_;
}
}
}
else
{
lean_object* v_abs_142_; lean_object* v_one_143_; lean_object* v_a_144_; uint8_t v_isNeg_145_; 
lean_dec(v_h__3_124_);
lean_dec(v_h__2_123_);
lean_dec(v_h__1_122_);
v_abs_142_ = lean_nat_abs(v_x_120_);
v_one_143_ = lean_unsigned_to_nat(1u);
v_a_144_ = lean_nat_sub(v_abs_142_, v_one_143_);
lean_dec(v_abs_142_);
v_isNeg_145_ = lean_int_dec_lt(v_x_121_, v_intZero_129_);
if (v_isNeg_145_ == 0)
{
lean_object* v_a_146_; uint8_t v_isZero_147_; 
lean_dec(v_h__6_127_);
v_a_146_ = lean_nat_abs(v_x_121_);
lean_dec(v_x_121_);
v_isZero_147_ = lean_nat_dec_eq(v_a_146_, v_natZero_128_);
if (v_isZero_147_ == 1)
{
lean_object* v___x_148_; 
lean_dec(v_a_146_);
lean_dec(v_h__5_126_);
v___x_148_ = lean_apply_1(v_h__4_125_, v_a_144_);
return v___x_148_;
}
else
{
lean_object* v_n_149_; lean_object* v___x_150_; 
lean_dec(v_h__4_125_);
v_n_149_ = lean_nat_sub(v_a_146_, v_one_143_);
lean_dec(v_a_146_);
v___x_150_ = lean_apply_2(v_h__5_126_, v_a_144_, v_n_149_);
return v___x_150_;
}
}
else
{
lean_object* v_abs_151_; lean_object* v_a_152_; lean_object* v___x_153_; 
lean_dec(v_h__5_126_);
lean_dec(v_h__4_125_);
v_abs_151_ = lean_nat_abs(v_x_121_);
lean_dec(v_x_121_);
v_a_152_ = lean_nat_sub(v_abs_151_, v_one_143_);
lean_dec(v_abs_151_);
v___x_153_ = lean_apply_2(v_h__6_127_, v_a_144_, v_a_152_);
return v___x_153_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___boxed(lean_object* v_x_154_, lean_object* v_x_155_, lean_object* v_h__1_156_, lean_object* v_h__2_157_, lean_object* v_h__3_158_, lean_object* v_h__4_159_, lean_object* v_h__5_160_, lean_object* v_h__6_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg(v_x_154_, v_x_155_, v_h__1_156_, v_h__2_157_, v_h__3_158_, v_h__4_159_, v_h__5_160_, v_h__6_161_);
lean_dec(v_x_154_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter(lean_object* v_motive_163_, lean_object* v_x_164_, lean_object* v_x_165_, lean_object* v_h__1_166_, lean_object* v_h__2_167_, lean_object* v_h__3_168_, lean_object* v_h__4_169_, lean_object* v_h__5_170_, lean_object* v_h__6_171_){
_start:
{
lean_object* v_natZero_172_; lean_object* v_intZero_173_; uint8_t v_isNeg_174_; 
v_natZero_172_ = lean_unsigned_to_nat(0u);
v_intZero_173_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0);
v_isNeg_174_ = lean_int_dec_lt(v_x_164_, v_intZero_173_);
if (v_isNeg_174_ == 0)
{
lean_object* v_a_175_; uint8_t v_isZero_176_; 
lean_dec(v_h__6_171_);
lean_dec(v_h__5_170_);
lean_dec(v_h__4_169_);
v_a_175_ = lean_nat_abs(v_x_164_);
v_isZero_176_ = lean_nat_dec_eq(v_a_175_, v_natZero_172_);
if (v_isZero_176_ == 1)
{
lean_object* v___x_177_; 
lean_dec(v_a_175_);
lean_dec(v_h__3_168_);
lean_dec(v_h__2_167_);
v___x_177_ = lean_apply_1(v_h__1_166_, v_x_165_);
return v___x_177_;
}
else
{
uint8_t v_isNeg_178_; 
lean_dec(v_h__1_166_);
v_isNeg_178_ = lean_int_dec_lt(v_x_165_, v_intZero_173_);
if (v_isNeg_178_ == 0)
{
lean_object* v_a_179_; lean_object* v___x_180_; 
lean_dec(v_h__3_168_);
v_a_179_ = lean_nat_abs(v_x_165_);
lean_dec(v_x_165_);
v___x_180_ = lean_apply_3(v_h__2_167_, v_a_175_, v_a_179_, lean_box(0));
return v___x_180_;
}
else
{
lean_object* v_one_181_; lean_object* v_n_182_; lean_object* v_abs_183_; lean_object* v_a_184_; lean_object* v___x_185_; 
lean_dec(v_h__2_167_);
v_one_181_ = lean_unsigned_to_nat(1u);
v_n_182_ = lean_nat_sub(v_a_175_, v_one_181_);
lean_dec(v_a_175_);
v_abs_183_ = lean_nat_abs(v_x_165_);
lean_dec(v_x_165_);
v_a_184_ = lean_nat_sub(v_abs_183_, v_one_181_);
lean_dec(v_abs_183_);
v___x_185_ = lean_apply_2(v_h__3_168_, v_n_182_, v_a_184_);
return v___x_185_;
}
}
}
else
{
lean_object* v_abs_186_; lean_object* v_one_187_; lean_object* v_a_188_; uint8_t v_isNeg_189_; 
lean_dec(v_h__3_168_);
lean_dec(v_h__2_167_);
lean_dec(v_h__1_166_);
v_abs_186_ = lean_nat_abs(v_x_164_);
v_one_187_ = lean_unsigned_to_nat(1u);
v_a_188_ = lean_nat_sub(v_abs_186_, v_one_187_);
lean_dec(v_abs_186_);
v_isNeg_189_ = lean_int_dec_lt(v_x_165_, v_intZero_173_);
if (v_isNeg_189_ == 0)
{
lean_object* v_a_190_; uint8_t v_isZero_191_; 
lean_dec(v_h__6_171_);
v_a_190_ = lean_nat_abs(v_x_165_);
lean_dec(v_x_165_);
v_isZero_191_ = lean_nat_dec_eq(v_a_190_, v_natZero_172_);
if (v_isZero_191_ == 1)
{
lean_object* v___x_192_; 
lean_dec(v_a_190_);
lean_dec(v_h__5_170_);
v___x_192_ = lean_apply_1(v_h__4_169_, v_a_188_);
return v___x_192_;
}
else
{
lean_object* v_n_193_; lean_object* v___x_194_; 
lean_dec(v_h__4_169_);
v_n_193_ = lean_nat_sub(v_a_190_, v_one_187_);
lean_dec(v_a_190_);
v___x_194_ = lean_apply_2(v_h__5_170_, v_a_188_, v_n_193_);
return v___x_194_;
}
}
else
{
lean_object* v_abs_195_; lean_object* v_a_196_; lean_object* v___x_197_; 
lean_dec(v_h__5_170_);
lean_dec(v_h__4_169_);
v_abs_195_ = lean_nat_abs(v_x_165_);
lean_dec(v_x_165_);
v_a_196_ = lean_nat_sub(v_abs_195_, v_one_187_);
lean_dec(v_abs_195_);
v___x_197_ = lean_apply_2(v_h__6_171_, v_a_188_, v_a_196_);
return v___x_197_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___boxed(lean_object* v_motive_198_, lean_object* v_x_199_, lean_object* v_x_200_, lean_object* v_h__1_201_, lean_object* v_h__2_202_, lean_object* v_h__3_203_, lean_object* v_h__4_204_, lean_object* v_h__5_205_, lean_object* v_h__6_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter(v_motive_198_, v_x_199_, v_x_200_, v_h__1_201_, v_h__2_202_, v_h__3_203_, v_h__4_204_, v_h__5_205_, v_h__6_206_);
lean_dec(v_x_199_);
return v_res_207_;
}
}
static lean_object* _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_208_; lean_object* v_intZero_209_; 
v_natZero_208_ = lean_unsigned_to_nat(0u);
v_intZero_209_ = lean_nat_to_int(v_natZero_208_);
return v_intZero_209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg(lean_object* v_x_210_, lean_object* v_x_211_, lean_object* v_h__1_212_, lean_object* v_h__2_213_, lean_object* v_h__3_214_, lean_object* v_h__4_215_, lean_object* v_h__5_216_){
_start:
{
lean_object* v_natZero_217_; lean_object* v_intZero_218_; uint8_t v_isNeg_219_; 
v_natZero_217_ = lean_unsigned_to_nat(0u);
v_intZero_218_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0);
v_isNeg_219_ = lean_int_dec_lt(v_x_210_, v_intZero_218_);
if (v_isNeg_219_ == 0)
{
lean_object* v_a_220_; uint8_t v_isZero_221_; 
lean_dec(v_h__5_216_);
lean_dec(v_h__4_215_);
v_a_220_ = lean_nat_abs(v_x_210_);
v_isZero_221_ = lean_nat_dec_eq(v_a_220_, v_natZero_217_);
if (v_isZero_221_ == 1)
{
lean_object* v___x_222_; 
lean_dec(v_a_220_);
lean_dec(v_h__3_214_);
lean_dec(v_h__2_213_);
v___x_222_ = lean_apply_1(v_h__1_212_, v_x_211_);
return v___x_222_;
}
else
{
uint8_t v_isNeg_223_; 
lean_dec(v_h__1_212_);
v_isNeg_223_ = lean_int_dec_lt(v_x_211_, v_intZero_218_);
if (v_isNeg_223_ == 0)
{
lean_object* v_a_224_; lean_object* v___x_225_; 
lean_dec(v_h__3_214_);
v_a_224_ = lean_nat_abs(v_x_211_);
lean_dec(v_x_211_);
v___x_225_ = lean_apply_3(v_h__2_213_, v_a_220_, v_a_224_, lean_box(0));
return v___x_225_;
}
else
{
lean_object* v_one_226_; lean_object* v_n_227_; lean_object* v_abs_228_; lean_object* v_a_229_; lean_object* v___x_230_; 
lean_dec(v_h__2_213_);
v_one_226_ = lean_unsigned_to_nat(1u);
v_n_227_ = lean_nat_sub(v_a_220_, v_one_226_);
lean_dec(v_a_220_);
v_abs_228_ = lean_nat_abs(v_x_211_);
lean_dec(v_x_211_);
v_a_229_ = lean_nat_sub(v_abs_228_, v_one_226_);
lean_dec(v_abs_228_);
v___x_230_ = lean_apply_2(v_h__3_214_, v_n_227_, v_a_229_);
return v___x_230_;
}
}
}
else
{
lean_object* v_abs_231_; lean_object* v_one_232_; lean_object* v_a_233_; uint8_t v_isNeg_234_; 
lean_dec(v_h__3_214_);
lean_dec(v_h__2_213_);
lean_dec(v_h__1_212_);
v_abs_231_ = lean_nat_abs(v_x_210_);
v_one_232_ = lean_unsigned_to_nat(1u);
v_a_233_ = lean_nat_sub(v_abs_231_, v_one_232_);
lean_dec(v_abs_231_);
v_isNeg_234_ = lean_int_dec_lt(v_x_211_, v_intZero_218_);
if (v_isNeg_234_ == 0)
{
lean_object* v_a_235_; lean_object* v___x_236_; 
lean_dec(v_h__5_216_);
v_a_235_ = lean_nat_abs(v_x_211_);
lean_dec(v_x_211_);
v___x_236_ = lean_apply_2(v_h__4_215_, v_a_233_, v_a_235_);
return v___x_236_;
}
else
{
lean_object* v_abs_237_; lean_object* v_a_238_; lean_object* v___x_239_; 
lean_dec(v_h__4_215_);
v_abs_237_ = lean_nat_abs(v_x_211_);
lean_dec(v_x_211_);
v_a_238_ = lean_nat_sub(v_abs_237_, v_one_232_);
lean_dec(v_abs_237_);
v___x_239_ = lean_apply_2(v_h__5_216_, v_a_233_, v_a_238_);
return v___x_239_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___boxed(lean_object* v_x_240_, lean_object* v_x_241_, lean_object* v_h__1_242_, lean_object* v_h__2_243_, lean_object* v_h__3_244_, lean_object* v_h__4_245_, lean_object* v_h__5_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg(v_x_240_, v_x_241_, v_h__1_242_, v_h__2_243_, v_h__3_244_, v_h__4_245_, v_h__5_246_);
lean_dec(v_x_240_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter(lean_object* v_motive_248_, lean_object* v_x_249_, lean_object* v_x_250_, lean_object* v_h__1_251_, lean_object* v_h__2_252_, lean_object* v_h__3_253_, lean_object* v_h__4_254_, lean_object* v_h__5_255_){
_start:
{
lean_object* v_natZero_256_; lean_object* v_intZero_257_; uint8_t v_isNeg_258_; 
v_natZero_256_ = lean_unsigned_to_nat(0u);
v_intZero_257_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0);
v_isNeg_258_ = lean_int_dec_lt(v_x_249_, v_intZero_257_);
if (v_isNeg_258_ == 0)
{
lean_object* v_a_259_; uint8_t v_isZero_260_; 
lean_dec(v_h__5_255_);
lean_dec(v_h__4_254_);
v_a_259_ = lean_nat_abs(v_x_249_);
v_isZero_260_ = lean_nat_dec_eq(v_a_259_, v_natZero_256_);
if (v_isZero_260_ == 1)
{
lean_object* v___x_261_; 
lean_dec(v_a_259_);
lean_dec(v_h__3_253_);
lean_dec(v_h__2_252_);
v___x_261_ = lean_apply_1(v_h__1_251_, v_x_250_);
return v___x_261_;
}
else
{
uint8_t v_isNeg_262_; 
lean_dec(v_h__1_251_);
v_isNeg_262_ = lean_int_dec_lt(v_x_250_, v_intZero_257_);
if (v_isNeg_262_ == 0)
{
lean_object* v_a_263_; lean_object* v___x_264_; 
lean_dec(v_h__3_253_);
v_a_263_ = lean_nat_abs(v_x_250_);
lean_dec(v_x_250_);
v___x_264_ = lean_apply_3(v_h__2_252_, v_a_259_, v_a_263_, lean_box(0));
return v___x_264_;
}
else
{
lean_object* v_one_265_; lean_object* v_n_266_; lean_object* v_abs_267_; lean_object* v_a_268_; lean_object* v___x_269_; 
lean_dec(v_h__2_252_);
v_one_265_ = lean_unsigned_to_nat(1u);
v_n_266_ = lean_nat_sub(v_a_259_, v_one_265_);
lean_dec(v_a_259_);
v_abs_267_ = lean_nat_abs(v_x_250_);
lean_dec(v_x_250_);
v_a_268_ = lean_nat_sub(v_abs_267_, v_one_265_);
lean_dec(v_abs_267_);
v___x_269_ = lean_apply_2(v_h__3_253_, v_n_266_, v_a_268_);
return v___x_269_;
}
}
}
else
{
lean_object* v_abs_270_; lean_object* v_one_271_; lean_object* v_a_272_; uint8_t v_isNeg_273_; 
lean_dec(v_h__3_253_);
lean_dec(v_h__2_252_);
lean_dec(v_h__1_251_);
v_abs_270_ = lean_nat_abs(v_x_249_);
v_one_271_ = lean_unsigned_to_nat(1u);
v_a_272_ = lean_nat_sub(v_abs_270_, v_one_271_);
lean_dec(v_abs_270_);
v_isNeg_273_ = lean_int_dec_lt(v_x_250_, v_intZero_257_);
if (v_isNeg_273_ == 0)
{
lean_object* v_a_274_; lean_object* v___x_275_; 
lean_dec(v_h__5_255_);
v_a_274_ = lean_nat_abs(v_x_250_);
lean_dec(v_x_250_);
v___x_275_ = lean_apply_2(v_h__4_254_, v_a_272_, v_a_274_);
return v___x_275_;
}
else
{
lean_object* v_abs_276_; lean_object* v_a_277_; lean_object* v___x_278_; 
lean_dec(v_h__4_254_);
v_abs_276_ = lean_nat_abs(v_x_250_);
lean_dec(v_x_250_);
v_a_277_ = lean_nat_sub(v_abs_276_, v_one_271_);
lean_dec(v_abs_276_);
v___x_278_ = lean_apply_2(v_h__5_255_, v_a_272_, v_a_277_);
return v___x_278_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___boxed(lean_object* v_motive_279_, lean_object* v_x_280_, lean_object* v_x_281_, lean_object* v_h__1_282_, lean_object* v_h__2_283_, lean_object* v_h__3_284_, lean_object* v_h__4_285_, lean_object* v_h__5_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter(v_motive_279_, v_x_280_, v_x_281_, v_h__1_282_, v_h__2_283_, v_h__3_284_, v_h__4_285_, v_h__5_286_);
lean_dec(v_x_280_);
return v_res_287_;
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
