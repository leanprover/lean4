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
static lean_once_cell_t l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Int_DivMod_Lemmas_0__Int_ediv_match__1_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_ediv_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_ediv_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_ediv_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_ediv_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_ediv_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Int_DivMod_Lemmas_0__Int_sign_match__1_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_sign_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_sign_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_sign_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_sign_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_sign_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_80_; lean_object* v_intZero_81_; 
v_natZero_80_ = lean_unsigned_to_nat(0u);
v_intZero_81_ = lean_nat_to_int(v_natZero_80_);
return v_intZero_81_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg(lean_object* v_x_82_, lean_object* v_x_83_, lean_object* v_h__1_84_, lean_object* v_h__2_85_, lean_object* v_h__3_86_, lean_object* v_h__4_87_, lean_object* v_h__5_88_, lean_object* v_h__6_89_){
_start:
{
lean_object* v_natZero_90_; lean_object* v_intZero_91_; uint8_t v_isNeg_92_; 
v_natZero_90_ = lean_unsigned_to_nat(0u);
v_intZero_91_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0);
v_isNeg_92_ = lean_int_dec_lt(v_x_82_, v_intZero_91_);
if (v_isNeg_92_ == 0)
{
lean_object* v_a_93_; uint8_t v_isZero_94_; 
lean_dec(v_h__6_89_);
lean_dec(v_h__5_88_);
lean_dec(v_h__4_87_);
v_a_93_ = lean_nat_abs(v_x_82_);
v_isZero_94_ = lean_nat_dec_eq(v_a_93_, v_natZero_90_);
if (v_isZero_94_ == 1)
{
lean_object* v___x_95_; 
lean_dec(v_a_93_);
lean_dec(v_h__3_86_);
lean_dec(v_h__2_85_);
v___x_95_ = lean_apply_1(v_h__1_84_, v_x_83_);
return v___x_95_;
}
else
{
uint8_t v_isNeg_96_; 
lean_dec(v_h__1_84_);
v_isNeg_96_ = lean_int_dec_lt(v_x_83_, v_intZero_91_);
if (v_isNeg_96_ == 0)
{
lean_object* v_a_97_; lean_object* v___x_98_; 
lean_dec(v_h__3_86_);
v_a_97_ = lean_nat_abs(v_x_83_);
lean_dec(v_x_83_);
v___x_98_ = lean_apply_3(v_h__2_85_, v_a_93_, v_a_97_, lean_box(0));
return v___x_98_;
}
else
{
lean_object* v_one_99_; lean_object* v_n_100_; lean_object* v_abs_101_; lean_object* v_a_102_; lean_object* v___x_103_; 
lean_dec(v_h__2_85_);
v_one_99_ = lean_unsigned_to_nat(1u);
v_n_100_ = lean_nat_sub(v_a_93_, v_one_99_);
lean_dec(v_a_93_);
v_abs_101_ = lean_nat_abs(v_x_83_);
lean_dec(v_x_83_);
v_a_102_ = lean_nat_sub(v_abs_101_, v_one_99_);
lean_dec(v_abs_101_);
v___x_103_ = lean_apply_2(v_h__3_86_, v_n_100_, v_a_102_);
return v___x_103_;
}
}
}
else
{
lean_object* v_abs_104_; lean_object* v_one_105_; lean_object* v_a_106_; uint8_t v_isNeg_107_; 
lean_dec(v_h__3_86_);
lean_dec(v_h__2_85_);
lean_dec(v_h__1_84_);
v_abs_104_ = lean_nat_abs(v_x_82_);
v_one_105_ = lean_unsigned_to_nat(1u);
v_a_106_ = lean_nat_sub(v_abs_104_, v_one_105_);
lean_dec(v_abs_104_);
v_isNeg_107_ = lean_int_dec_lt(v_x_83_, v_intZero_91_);
if (v_isNeg_107_ == 0)
{
lean_object* v_a_108_; uint8_t v_isZero_109_; 
lean_dec(v_h__6_89_);
v_a_108_ = lean_nat_abs(v_x_83_);
lean_dec(v_x_83_);
v_isZero_109_ = lean_nat_dec_eq(v_a_108_, v_natZero_90_);
if (v_isZero_109_ == 1)
{
lean_object* v___x_110_; 
lean_dec(v_a_108_);
lean_dec(v_h__5_88_);
v___x_110_ = lean_apply_1(v_h__4_87_, v_a_106_);
return v___x_110_;
}
else
{
lean_object* v_n_111_; lean_object* v___x_112_; 
lean_dec(v_h__4_87_);
v_n_111_ = lean_nat_sub(v_a_108_, v_one_105_);
lean_dec(v_a_108_);
v___x_112_ = lean_apply_2(v_h__5_88_, v_a_106_, v_n_111_);
return v___x_112_;
}
}
else
{
lean_object* v_abs_113_; lean_object* v_a_114_; lean_object* v___x_115_; 
lean_dec(v_h__5_88_);
lean_dec(v_h__4_87_);
v_abs_113_ = lean_nat_abs(v_x_83_);
lean_dec(v_x_83_);
v_a_114_ = lean_nat_sub(v_abs_113_, v_one_105_);
lean_dec(v_abs_113_);
v___x_115_ = lean_apply_2(v_h__6_89_, v_a_106_, v_a_114_);
return v___x_115_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___boxed(lean_object* v_x_116_, lean_object* v_x_117_, lean_object* v_h__1_118_, lean_object* v_h__2_119_, lean_object* v_h__3_120_, lean_object* v_h__4_121_, lean_object* v_h__5_122_, lean_object* v_h__6_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg(v_x_116_, v_x_117_, v_h__1_118_, v_h__2_119_, v_h__3_120_, v_h__4_121_, v_h__5_122_, v_h__6_123_);
lean_dec(v_x_116_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter(lean_object* v_motive_125_, lean_object* v_x_126_, lean_object* v_x_127_, lean_object* v_h__1_128_, lean_object* v_h__2_129_, lean_object* v_h__3_130_, lean_object* v_h__4_131_, lean_object* v_h__5_132_, lean_object* v_h__6_133_){
_start:
{
lean_object* v_natZero_134_; lean_object* v_intZero_135_; uint8_t v_isNeg_136_; 
v_natZero_134_ = lean_unsigned_to_nat(0u);
v_intZero_135_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0);
v_isNeg_136_ = lean_int_dec_lt(v_x_126_, v_intZero_135_);
if (v_isNeg_136_ == 0)
{
lean_object* v_a_137_; uint8_t v_isZero_138_; 
lean_dec(v_h__6_133_);
lean_dec(v_h__5_132_);
lean_dec(v_h__4_131_);
v_a_137_ = lean_nat_abs(v_x_126_);
v_isZero_138_ = lean_nat_dec_eq(v_a_137_, v_natZero_134_);
if (v_isZero_138_ == 1)
{
lean_object* v___x_139_; 
lean_dec(v_a_137_);
lean_dec(v_h__3_130_);
lean_dec(v_h__2_129_);
v___x_139_ = lean_apply_1(v_h__1_128_, v_x_127_);
return v___x_139_;
}
else
{
uint8_t v_isNeg_140_; 
lean_dec(v_h__1_128_);
v_isNeg_140_ = lean_int_dec_lt(v_x_127_, v_intZero_135_);
if (v_isNeg_140_ == 0)
{
lean_object* v_a_141_; lean_object* v___x_142_; 
lean_dec(v_h__3_130_);
v_a_141_ = lean_nat_abs(v_x_127_);
lean_dec(v_x_127_);
v___x_142_ = lean_apply_3(v_h__2_129_, v_a_137_, v_a_141_, lean_box(0));
return v___x_142_;
}
else
{
lean_object* v_one_143_; lean_object* v_n_144_; lean_object* v_abs_145_; lean_object* v_a_146_; lean_object* v___x_147_; 
lean_dec(v_h__2_129_);
v_one_143_ = lean_unsigned_to_nat(1u);
v_n_144_ = lean_nat_sub(v_a_137_, v_one_143_);
lean_dec(v_a_137_);
v_abs_145_ = lean_nat_abs(v_x_127_);
lean_dec(v_x_127_);
v_a_146_ = lean_nat_sub(v_abs_145_, v_one_143_);
lean_dec(v_abs_145_);
v___x_147_ = lean_apply_2(v_h__3_130_, v_n_144_, v_a_146_);
return v___x_147_;
}
}
}
else
{
lean_object* v_abs_148_; lean_object* v_one_149_; lean_object* v_a_150_; uint8_t v_isNeg_151_; 
lean_dec(v_h__3_130_);
lean_dec(v_h__2_129_);
lean_dec(v_h__1_128_);
v_abs_148_ = lean_nat_abs(v_x_126_);
v_one_149_ = lean_unsigned_to_nat(1u);
v_a_150_ = lean_nat_sub(v_abs_148_, v_one_149_);
lean_dec(v_abs_148_);
v_isNeg_151_ = lean_int_dec_lt(v_x_127_, v_intZero_135_);
if (v_isNeg_151_ == 0)
{
lean_object* v_a_152_; uint8_t v_isZero_153_; 
lean_dec(v_h__6_133_);
v_a_152_ = lean_nat_abs(v_x_127_);
lean_dec(v_x_127_);
v_isZero_153_ = lean_nat_dec_eq(v_a_152_, v_natZero_134_);
if (v_isZero_153_ == 1)
{
lean_object* v___x_154_; 
lean_dec(v_a_152_);
lean_dec(v_h__5_132_);
v___x_154_ = lean_apply_1(v_h__4_131_, v_a_150_);
return v___x_154_;
}
else
{
lean_object* v_n_155_; lean_object* v___x_156_; 
lean_dec(v_h__4_131_);
v_n_155_ = lean_nat_sub(v_a_152_, v_one_149_);
lean_dec(v_a_152_);
v___x_156_ = lean_apply_2(v_h__5_132_, v_a_150_, v_n_155_);
return v___x_156_;
}
}
else
{
lean_object* v_abs_157_; lean_object* v_a_158_; lean_object* v___x_159_; 
lean_dec(v_h__5_132_);
lean_dec(v_h__4_131_);
v_abs_157_ = lean_nat_abs(v_x_127_);
lean_dec(v_x_127_);
v_a_158_ = lean_nat_sub(v_abs_157_, v_one_149_);
lean_dec(v_abs_157_);
v___x_159_ = lean_apply_2(v_h__6_133_, v_a_150_, v_a_158_);
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___boxed(lean_object* v_motive_160_, lean_object* v_x_161_, lean_object* v_x_162_, lean_object* v_h__1_163_, lean_object* v_h__2_164_, lean_object* v_h__3_165_, lean_object* v_h__4_166_, lean_object* v_h__5_167_, lean_object* v_h__6_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter(v_motive_160_, v_x_161_, v_x_162_, v_h__1_163_, v_h__2_164_, v_h__3_165_, v_h__4_166_, v_h__5_167_, v_h__6_168_);
lean_dec(v_x_161_);
return v_res_169_;
}
}
static lean_object* _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_170_; lean_object* v_intZero_171_; 
v_natZero_170_ = lean_unsigned_to_nat(0u);
v_intZero_171_ = lean_nat_to_int(v_natZero_170_);
return v_intZero_171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg(lean_object* v_x_172_, lean_object* v_x_173_, lean_object* v_h__1_174_, lean_object* v_h__2_175_){
_start:
{
lean_object* v_intZero_176_; uint8_t v_isNeg_177_; 
v_intZero_176_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0);
v_isNeg_177_ = lean_int_dec_lt(v_x_172_, v_intZero_176_);
if (v_isNeg_177_ == 0)
{
lean_object* v_a_178_; lean_object* v___x_179_; 
lean_dec(v_h__2_175_);
v_a_178_ = lean_nat_abs(v_x_172_);
v___x_179_ = lean_apply_2(v_h__1_174_, v_a_178_, v_x_173_);
return v___x_179_;
}
else
{
lean_object* v_abs_180_; lean_object* v_one_181_; lean_object* v_a_182_; lean_object* v___x_183_; 
lean_dec(v_h__1_174_);
v_abs_180_ = lean_nat_abs(v_x_172_);
v_one_181_ = lean_unsigned_to_nat(1u);
v_a_182_ = lean_nat_sub(v_abs_180_, v_one_181_);
lean_dec(v_abs_180_);
v___x_183_ = lean_apply_2(v_h__2_175_, v_a_182_, v_x_173_);
return v___x_183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___boxed(lean_object* v_x_184_, lean_object* v_x_185_, lean_object* v_h__1_186_, lean_object* v_h__2_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg(v_x_184_, v_x_185_, v_h__1_186_, v_h__2_187_);
lean_dec(v_x_184_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter(lean_object* v_motive_189_, lean_object* v_x_190_, lean_object* v_x_191_, lean_object* v_h__1_192_, lean_object* v_h__2_193_){
_start:
{
lean_object* v_intZero_194_; uint8_t v_isNeg_195_; 
v_intZero_194_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0);
v_isNeg_195_ = lean_int_dec_lt(v_x_190_, v_intZero_194_);
if (v_isNeg_195_ == 0)
{
lean_object* v_a_196_; lean_object* v___x_197_; 
lean_dec(v_h__2_193_);
v_a_196_ = lean_nat_abs(v_x_190_);
v___x_197_ = lean_apply_2(v_h__1_192_, v_a_196_, v_x_191_);
return v___x_197_;
}
else
{
lean_object* v_abs_198_; lean_object* v_one_199_; lean_object* v_a_200_; lean_object* v___x_201_; 
lean_dec(v_h__1_192_);
v_abs_198_ = lean_nat_abs(v_x_190_);
v_one_199_ = lean_unsigned_to_nat(1u);
v_a_200_ = lean_nat_sub(v_abs_198_, v_one_199_);
lean_dec(v_abs_198_);
v___x_201_ = lean_apply_2(v_h__2_193_, v_a_200_, v_x_191_);
return v___x_201_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___boxed(lean_object* v_motive_202_, lean_object* v_x_203_, lean_object* v_x_204_, lean_object* v_h__1_205_, lean_object* v_h__2_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter(v_motive_202_, v_x_203_, v_x_204_, v_h__1_205_, v_h__2_206_);
lean_dec(v_x_203_);
return v_res_207_;
}
}
static lean_object* _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_ediv_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_208_; lean_object* v_intZero_209_; 
v_natZero_208_ = lean_unsigned_to_nat(0u);
v_intZero_209_ = lean_nat_to_int(v_natZero_208_);
return v_intZero_209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_ediv_match__1_splitter___redArg(lean_object* v_x_210_, lean_object* v_x_211_, lean_object* v_h__1_212_, lean_object* v_h__2_213_, lean_object* v_h__3_214_, lean_object* v_h__4_215_, lean_object* v_h__5_216_){
_start:
{
lean_object* v_natZero_217_; lean_object* v_intZero_218_; uint8_t v_isNeg_219_; 
v_natZero_217_ = lean_unsigned_to_nat(0u);
v_intZero_218_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_ediv_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_ediv_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_ediv_match__1_splitter___redArg___closed__0);
v_isNeg_219_ = lean_int_dec_lt(v_x_210_, v_intZero_218_);
if (v_isNeg_219_ == 0)
{
lean_object* v_a_220_; uint8_t v_isNeg_221_; 
lean_dec(v_h__5_216_);
lean_dec(v_h__4_215_);
lean_dec(v_h__3_214_);
v_a_220_ = lean_nat_abs(v_x_210_);
v_isNeg_221_ = lean_int_dec_lt(v_x_211_, v_intZero_218_);
if (v_isNeg_221_ == 0)
{
lean_object* v_a_222_; lean_object* v___x_223_; 
lean_dec(v_h__2_213_);
v_a_222_ = lean_nat_abs(v_x_211_);
v___x_223_ = lean_apply_2(v_h__1_212_, v_a_220_, v_a_222_);
return v___x_223_;
}
else
{
lean_object* v_abs_224_; lean_object* v_one_225_; lean_object* v_a_226_; lean_object* v___x_227_; 
lean_dec(v_h__1_212_);
v_abs_224_ = lean_nat_abs(v_x_211_);
v_one_225_ = lean_unsigned_to_nat(1u);
v_a_226_ = lean_nat_sub(v_abs_224_, v_one_225_);
lean_dec(v_abs_224_);
v___x_227_ = lean_apply_2(v_h__2_213_, v_a_220_, v_a_226_);
return v___x_227_;
}
}
else
{
lean_object* v_abs_228_; lean_object* v_one_229_; lean_object* v_a_230_; uint8_t v_isNeg_231_; 
lean_dec(v_h__2_213_);
lean_dec(v_h__1_212_);
v_abs_228_ = lean_nat_abs(v_x_210_);
v_one_229_ = lean_unsigned_to_nat(1u);
v_a_230_ = lean_nat_sub(v_abs_228_, v_one_229_);
lean_dec(v_abs_228_);
v_isNeg_231_ = lean_int_dec_lt(v_x_211_, v_intZero_218_);
if (v_isNeg_231_ == 0)
{
lean_object* v_a_232_; uint8_t v_isZero_233_; 
lean_dec(v_h__5_216_);
v_a_232_ = lean_nat_abs(v_x_211_);
v_isZero_233_ = lean_nat_dec_eq(v_a_232_, v_natZero_217_);
if (v_isZero_233_ == 1)
{
lean_object* v___x_234_; 
lean_dec(v_a_232_);
lean_dec(v_h__4_215_);
v___x_234_ = lean_apply_1(v_h__3_214_, v_a_230_);
return v___x_234_;
}
else
{
lean_object* v_n_235_; lean_object* v___x_236_; 
lean_dec(v_h__3_214_);
v_n_235_ = lean_nat_sub(v_a_232_, v_one_229_);
lean_dec(v_a_232_);
v___x_236_ = lean_apply_2(v_h__4_215_, v_a_230_, v_n_235_);
return v___x_236_;
}
}
else
{
lean_object* v_abs_237_; lean_object* v_a_238_; lean_object* v___x_239_; 
lean_dec(v_h__4_215_);
lean_dec(v_h__3_214_);
v_abs_237_ = lean_nat_abs(v_x_211_);
v_a_238_ = lean_nat_sub(v_abs_237_, v_one_229_);
lean_dec(v_abs_237_);
v___x_239_ = lean_apply_2(v_h__5_216_, v_a_230_, v_a_238_);
return v___x_239_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_ediv_match__1_splitter___redArg___boxed(lean_object* v_x_240_, lean_object* v_x_241_, lean_object* v_h__1_242_, lean_object* v_h__2_243_, lean_object* v_h__3_244_, lean_object* v_h__4_245_, lean_object* v_h__5_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_ediv_match__1_splitter___redArg(v_x_240_, v_x_241_, v_h__1_242_, v_h__2_243_, v_h__3_244_, v_h__4_245_, v_h__5_246_);
lean_dec(v_x_241_);
lean_dec(v_x_240_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_ediv_match__1_splitter(lean_object* v_motive_248_, lean_object* v_x_249_, lean_object* v_x_250_, lean_object* v_h__1_251_, lean_object* v_h__2_252_, lean_object* v_h__3_253_, lean_object* v_h__4_254_, lean_object* v_h__5_255_){
_start:
{
lean_object* v_natZero_256_; lean_object* v_intZero_257_; uint8_t v_isNeg_258_; 
v_natZero_256_ = lean_unsigned_to_nat(0u);
v_intZero_257_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_ediv_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_ediv_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_ediv_match__1_splitter___redArg___closed__0);
v_isNeg_258_ = lean_int_dec_lt(v_x_249_, v_intZero_257_);
if (v_isNeg_258_ == 0)
{
lean_object* v_a_259_; uint8_t v_isNeg_260_; 
lean_dec(v_h__5_255_);
lean_dec(v_h__4_254_);
lean_dec(v_h__3_253_);
v_a_259_ = lean_nat_abs(v_x_249_);
v_isNeg_260_ = lean_int_dec_lt(v_x_250_, v_intZero_257_);
if (v_isNeg_260_ == 0)
{
lean_object* v_a_261_; lean_object* v___x_262_; 
lean_dec(v_h__2_252_);
v_a_261_ = lean_nat_abs(v_x_250_);
v___x_262_ = lean_apply_2(v_h__1_251_, v_a_259_, v_a_261_);
return v___x_262_;
}
else
{
lean_object* v_abs_263_; lean_object* v_one_264_; lean_object* v_a_265_; lean_object* v___x_266_; 
lean_dec(v_h__1_251_);
v_abs_263_ = lean_nat_abs(v_x_250_);
v_one_264_ = lean_unsigned_to_nat(1u);
v_a_265_ = lean_nat_sub(v_abs_263_, v_one_264_);
lean_dec(v_abs_263_);
v___x_266_ = lean_apply_2(v_h__2_252_, v_a_259_, v_a_265_);
return v___x_266_;
}
}
else
{
lean_object* v_abs_267_; lean_object* v_one_268_; lean_object* v_a_269_; uint8_t v_isNeg_270_; 
lean_dec(v_h__2_252_);
lean_dec(v_h__1_251_);
v_abs_267_ = lean_nat_abs(v_x_249_);
v_one_268_ = lean_unsigned_to_nat(1u);
v_a_269_ = lean_nat_sub(v_abs_267_, v_one_268_);
lean_dec(v_abs_267_);
v_isNeg_270_ = lean_int_dec_lt(v_x_250_, v_intZero_257_);
if (v_isNeg_270_ == 0)
{
lean_object* v_a_271_; uint8_t v_isZero_272_; 
lean_dec(v_h__5_255_);
v_a_271_ = lean_nat_abs(v_x_250_);
v_isZero_272_ = lean_nat_dec_eq(v_a_271_, v_natZero_256_);
if (v_isZero_272_ == 1)
{
lean_object* v___x_273_; 
lean_dec(v_a_271_);
lean_dec(v_h__4_254_);
v___x_273_ = lean_apply_1(v_h__3_253_, v_a_269_);
return v___x_273_;
}
else
{
lean_object* v_n_274_; lean_object* v___x_275_; 
lean_dec(v_h__3_253_);
v_n_274_ = lean_nat_sub(v_a_271_, v_one_268_);
lean_dec(v_a_271_);
v___x_275_ = lean_apply_2(v_h__4_254_, v_a_269_, v_n_274_);
return v___x_275_;
}
}
else
{
lean_object* v_abs_276_; lean_object* v_a_277_; lean_object* v___x_278_; 
lean_dec(v_h__4_254_);
lean_dec(v_h__3_253_);
v_abs_276_ = lean_nat_abs(v_x_250_);
v_a_277_ = lean_nat_sub(v_abs_276_, v_one_268_);
lean_dec(v_abs_276_);
v___x_278_ = lean_apply_2(v_h__5_255_, v_a_269_, v_a_277_);
return v___x_278_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_ediv_match__1_splitter___boxed(lean_object* v_motive_279_, lean_object* v_x_280_, lean_object* v_x_281_, lean_object* v_h__1_282_, lean_object* v_h__2_283_, lean_object* v_h__3_284_, lean_object* v_h__4_285_, lean_object* v_h__5_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_ediv_match__1_splitter(v_motive_279_, v_x_280_, v_x_281_, v_h__1_282_, v_h__2_283_, v_h__3_284_, v_h__4_285_, v_h__5_286_);
lean_dec(v_x_281_);
lean_dec(v_x_280_);
return v_res_287_;
}
}
static lean_object* _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_sign_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_288_; lean_object* v_intZero_289_; 
v_natZero_288_ = lean_unsigned_to_nat(0u);
v_intZero_289_ = lean_nat_to_int(v_natZero_288_);
return v_intZero_289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_sign_match__1_splitter___redArg(lean_object* v_x_290_, lean_object* v_h__1_291_, lean_object* v_h__2_292_, lean_object* v_h__3_293_){
_start:
{
lean_object* v_natZero_294_; lean_object* v_intZero_295_; uint8_t v_isNeg_296_; 
v_natZero_294_ = lean_unsigned_to_nat(0u);
v_intZero_295_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_sign_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_sign_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_sign_match__1_splitter___redArg___closed__0);
v_isNeg_296_ = lean_int_dec_lt(v_x_290_, v_intZero_295_);
if (v_isNeg_296_ == 0)
{
lean_object* v_a_297_; uint8_t v_isZero_298_; 
lean_dec(v_h__3_293_);
v_a_297_ = lean_nat_abs(v_x_290_);
v_isZero_298_ = lean_nat_dec_eq(v_a_297_, v_natZero_294_);
if (v_isZero_298_ == 1)
{
lean_object* v___x_299_; lean_object* v___x_300_; 
lean_dec(v_a_297_);
lean_dec(v_h__1_291_);
v___x_299_ = lean_box(0);
v___x_300_ = lean_apply_1(v_h__2_292_, v___x_299_);
return v___x_300_;
}
else
{
lean_object* v_one_301_; lean_object* v_n_302_; lean_object* v___x_303_; 
lean_dec(v_h__2_292_);
v_one_301_ = lean_unsigned_to_nat(1u);
v_n_302_ = lean_nat_sub(v_a_297_, v_one_301_);
lean_dec(v_a_297_);
v___x_303_ = lean_apply_1(v_h__1_291_, v_n_302_);
return v___x_303_;
}
}
else
{
lean_object* v_abs_304_; lean_object* v_one_305_; lean_object* v_a_306_; lean_object* v___x_307_; 
lean_dec(v_h__2_292_);
lean_dec(v_h__1_291_);
v_abs_304_ = lean_nat_abs(v_x_290_);
v_one_305_ = lean_unsigned_to_nat(1u);
v_a_306_ = lean_nat_sub(v_abs_304_, v_one_305_);
lean_dec(v_abs_304_);
v___x_307_ = lean_apply_1(v_h__3_293_, v_a_306_);
return v___x_307_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_sign_match__1_splitter___redArg___boxed(lean_object* v_x_308_, lean_object* v_h__1_309_, lean_object* v_h__2_310_, lean_object* v_h__3_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_sign_match__1_splitter___redArg(v_x_308_, v_h__1_309_, v_h__2_310_, v_h__3_311_);
lean_dec(v_x_308_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_sign_match__1_splitter(lean_object* v_motive_313_, lean_object* v_x_314_, lean_object* v_h__1_315_, lean_object* v_h__2_316_, lean_object* v_h__3_317_){
_start:
{
lean_object* v_natZero_318_; lean_object* v_intZero_319_; uint8_t v_isNeg_320_; 
v_natZero_318_ = lean_unsigned_to_nat(0u);
v_intZero_319_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_sign_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_sign_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_sign_match__1_splitter___redArg___closed__0);
v_isNeg_320_ = lean_int_dec_lt(v_x_314_, v_intZero_319_);
if (v_isNeg_320_ == 0)
{
lean_object* v_a_321_; uint8_t v_isZero_322_; 
lean_dec(v_h__3_317_);
v_a_321_ = lean_nat_abs(v_x_314_);
v_isZero_322_ = lean_nat_dec_eq(v_a_321_, v_natZero_318_);
if (v_isZero_322_ == 1)
{
lean_object* v___x_323_; lean_object* v___x_324_; 
lean_dec(v_a_321_);
lean_dec(v_h__1_315_);
v___x_323_ = lean_box(0);
v___x_324_ = lean_apply_1(v_h__2_316_, v___x_323_);
return v___x_324_;
}
else
{
lean_object* v_one_325_; lean_object* v_n_326_; lean_object* v___x_327_; 
lean_dec(v_h__2_316_);
v_one_325_ = lean_unsigned_to_nat(1u);
v_n_326_ = lean_nat_sub(v_a_321_, v_one_325_);
lean_dec(v_a_321_);
v___x_327_ = lean_apply_1(v_h__1_315_, v_n_326_);
return v___x_327_;
}
}
else
{
lean_object* v_abs_328_; lean_object* v_one_329_; lean_object* v_a_330_; lean_object* v___x_331_; 
lean_dec(v_h__2_316_);
lean_dec(v_h__1_315_);
v_abs_328_ = lean_nat_abs(v_x_314_);
v_one_329_ = lean_unsigned_to_nat(1u);
v_a_330_ = lean_nat_sub(v_abs_328_, v_one_329_);
lean_dec(v_abs_328_);
v___x_331_ = lean_apply_1(v_h__3_317_, v_a_330_);
return v___x_331_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_sign_match__1_splitter___boxed(lean_object* v_motive_332_, lean_object* v_x_333_, lean_object* v_h__1_334_, lean_object* v_h__2_335_, lean_object* v_h__3_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_sign_match__1_splitter(v_motive_332_, v_x_333_, v_h__1_334_, v_h__2_335_, v_h__3_336_);
lean_dec(v_x_333_);
return v_res_337_;
}
}
static lean_object* _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_338_; lean_object* v_intZero_339_; 
v_natZero_338_ = lean_unsigned_to_nat(0u);
v_intZero_339_ = lean_nat_to_int(v_natZero_338_);
return v_intZero_339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg(lean_object* v_x_340_, lean_object* v_x_341_, lean_object* v_h__1_342_, lean_object* v_h__2_343_, lean_object* v_h__3_344_, lean_object* v_h__4_345_, lean_object* v_h__5_346_){
_start:
{
lean_object* v_natZero_347_; lean_object* v_intZero_348_; uint8_t v_isNeg_349_; 
v_natZero_347_ = lean_unsigned_to_nat(0u);
v_intZero_348_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0);
v_isNeg_349_ = lean_int_dec_lt(v_x_340_, v_intZero_348_);
if (v_isNeg_349_ == 0)
{
lean_object* v_a_350_; uint8_t v_isZero_351_; 
lean_dec(v_h__5_346_);
lean_dec(v_h__4_345_);
v_a_350_ = lean_nat_abs(v_x_340_);
v_isZero_351_ = lean_nat_dec_eq(v_a_350_, v_natZero_347_);
if (v_isZero_351_ == 1)
{
lean_object* v___x_352_; 
lean_dec(v_a_350_);
lean_dec(v_h__3_344_);
lean_dec(v_h__2_343_);
v___x_352_ = lean_apply_1(v_h__1_342_, v_x_341_);
return v___x_352_;
}
else
{
uint8_t v_isNeg_353_; 
lean_dec(v_h__1_342_);
v_isNeg_353_ = lean_int_dec_lt(v_x_341_, v_intZero_348_);
if (v_isNeg_353_ == 0)
{
lean_object* v_a_354_; lean_object* v___x_355_; 
lean_dec(v_h__3_344_);
v_a_354_ = lean_nat_abs(v_x_341_);
lean_dec(v_x_341_);
v___x_355_ = lean_apply_3(v_h__2_343_, v_a_350_, v_a_354_, lean_box(0));
return v___x_355_;
}
else
{
lean_object* v_one_356_; lean_object* v_n_357_; lean_object* v_abs_358_; lean_object* v_a_359_; lean_object* v___x_360_; 
lean_dec(v_h__2_343_);
v_one_356_ = lean_unsigned_to_nat(1u);
v_n_357_ = lean_nat_sub(v_a_350_, v_one_356_);
lean_dec(v_a_350_);
v_abs_358_ = lean_nat_abs(v_x_341_);
lean_dec(v_x_341_);
v_a_359_ = lean_nat_sub(v_abs_358_, v_one_356_);
lean_dec(v_abs_358_);
v___x_360_ = lean_apply_2(v_h__3_344_, v_n_357_, v_a_359_);
return v___x_360_;
}
}
}
else
{
lean_object* v_abs_361_; lean_object* v_one_362_; lean_object* v_a_363_; uint8_t v_isNeg_364_; 
lean_dec(v_h__3_344_);
lean_dec(v_h__2_343_);
lean_dec(v_h__1_342_);
v_abs_361_ = lean_nat_abs(v_x_340_);
v_one_362_ = lean_unsigned_to_nat(1u);
v_a_363_ = lean_nat_sub(v_abs_361_, v_one_362_);
lean_dec(v_abs_361_);
v_isNeg_364_ = lean_int_dec_lt(v_x_341_, v_intZero_348_);
if (v_isNeg_364_ == 0)
{
lean_object* v_a_365_; lean_object* v___x_366_; 
lean_dec(v_h__5_346_);
v_a_365_ = lean_nat_abs(v_x_341_);
lean_dec(v_x_341_);
v___x_366_ = lean_apply_2(v_h__4_345_, v_a_363_, v_a_365_);
return v___x_366_;
}
else
{
lean_object* v_abs_367_; lean_object* v_a_368_; lean_object* v___x_369_; 
lean_dec(v_h__4_345_);
v_abs_367_ = lean_nat_abs(v_x_341_);
lean_dec(v_x_341_);
v_a_368_ = lean_nat_sub(v_abs_367_, v_one_362_);
lean_dec(v_abs_367_);
v___x_369_ = lean_apply_2(v_h__5_346_, v_a_363_, v_a_368_);
return v___x_369_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___boxed(lean_object* v_x_370_, lean_object* v_x_371_, lean_object* v_h__1_372_, lean_object* v_h__2_373_, lean_object* v_h__3_374_, lean_object* v_h__4_375_, lean_object* v_h__5_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg(v_x_370_, v_x_371_, v_h__1_372_, v_h__2_373_, v_h__3_374_, v_h__4_375_, v_h__5_376_);
lean_dec(v_x_370_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter(lean_object* v_motive_378_, lean_object* v_x_379_, lean_object* v_x_380_, lean_object* v_h__1_381_, lean_object* v_h__2_382_, lean_object* v_h__3_383_, lean_object* v_h__4_384_, lean_object* v_h__5_385_){
_start:
{
lean_object* v_natZero_386_; lean_object* v_intZero_387_; uint8_t v_isNeg_388_; 
v_natZero_386_ = lean_unsigned_to_nat(0u);
v_intZero_387_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0);
v_isNeg_388_ = lean_int_dec_lt(v_x_379_, v_intZero_387_);
if (v_isNeg_388_ == 0)
{
lean_object* v_a_389_; uint8_t v_isZero_390_; 
lean_dec(v_h__5_385_);
lean_dec(v_h__4_384_);
v_a_389_ = lean_nat_abs(v_x_379_);
v_isZero_390_ = lean_nat_dec_eq(v_a_389_, v_natZero_386_);
if (v_isZero_390_ == 1)
{
lean_object* v___x_391_; 
lean_dec(v_a_389_);
lean_dec(v_h__3_383_);
lean_dec(v_h__2_382_);
v___x_391_ = lean_apply_1(v_h__1_381_, v_x_380_);
return v___x_391_;
}
else
{
uint8_t v_isNeg_392_; 
lean_dec(v_h__1_381_);
v_isNeg_392_ = lean_int_dec_lt(v_x_380_, v_intZero_387_);
if (v_isNeg_392_ == 0)
{
lean_object* v_a_393_; lean_object* v___x_394_; 
lean_dec(v_h__3_383_);
v_a_393_ = lean_nat_abs(v_x_380_);
lean_dec(v_x_380_);
v___x_394_ = lean_apply_3(v_h__2_382_, v_a_389_, v_a_393_, lean_box(0));
return v___x_394_;
}
else
{
lean_object* v_one_395_; lean_object* v_n_396_; lean_object* v_abs_397_; lean_object* v_a_398_; lean_object* v___x_399_; 
lean_dec(v_h__2_382_);
v_one_395_ = lean_unsigned_to_nat(1u);
v_n_396_ = lean_nat_sub(v_a_389_, v_one_395_);
lean_dec(v_a_389_);
v_abs_397_ = lean_nat_abs(v_x_380_);
lean_dec(v_x_380_);
v_a_398_ = lean_nat_sub(v_abs_397_, v_one_395_);
lean_dec(v_abs_397_);
v___x_399_ = lean_apply_2(v_h__3_383_, v_n_396_, v_a_398_);
return v___x_399_;
}
}
}
else
{
lean_object* v_abs_400_; lean_object* v_one_401_; lean_object* v_a_402_; uint8_t v_isNeg_403_; 
lean_dec(v_h__3_383_);
lean_dec(v_h__2_382_);
lean_dec(v_h__1_381_);
v_abs_400_ = lean_nat_abs(v_x_379_);
v_one_401_ = lean_unsigned_to_nat(1u);
v_a_402_ = lean_nat_sub(v_abs_400_, v_one_401_);
lean_dec(v_abs_400_);
v_isNeg_403_ = lean_int_dec_lt(v_x_380_, v_intZero_387_);
if (v_isNeg_403_ == 0)
{
lean_object* v_a_404_; lean_object* v___x_405_; 
lean_dec(v_h__5_385_);
v_a_404_ = lean_nat_abs(v_x_380_);
lean_dec(v_x_380_);
v___x_405_ = lean_apply_2(v_h__4_384_, v_a_402_, v_a_404_);
return v___x_405_;
}
else
{
lean_object* v_abs_406_; lean_object* v_a_407_; lean_object* v___x_408_; 
lean_dec(v_h__4_384_);
v_abs_406_ = lean_nat_abs(v_x_380_);
lean_dec(v_x_380_);
v_a_407_ = lean_nat_sub(v_abs_406_, v_one_401_);
lean_dec(v_abs_406_);
v___x_408_ = lean_apply_2(v_h__5_385_, v_a_402_, v_a_407_);
return v___x_408_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___boxed(lean_object* v_motive_409_, lean_object* v_x_410_, lean_object* v_x_411_, lean_object* v_h__1_412_, lean_object* v_h__2_413_, lean_object* v_h__3_414_, lean_object* v_h__4_415_, lean_object* v_h__5_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter(v_motive_409_, v_x_410_, v_x_411_, v_h__1_412_, v_h__2_413_, v_h__3_414_, v_h__4_415_, v_h__5_416_);
lean_dec(v_x_410_);
return v_res_417_;
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
