// Lean compiler output
// Module: Init.Data.Nat.Lemmas
// Imports: import all Init.Data.Nat.Bitwise.Basic public import Init.Data.Nat.Log2 import all Init.Data.Nat.Log2 import Init.TacticsExtra public import Init.Data.Nat.Div.Basic public import Init.PropLemmas import Init.ByCases import Init.Data.Nat.Dvd import Init.Data.Nat.Linear import Init.Data.Nat.MinMax import Init.Data.Nat.Mod import Init.Omega import Init.RCases
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_allLTTR(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_allLTTR___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_anyLTTR(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyLTTR___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableBallLTTR___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableBallLTTR___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableBallLTTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableBallLTTR___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableBallLTTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableBallLTTR___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableForallFin___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableForallFin___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableForallFin___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableForallFin___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableForallFin(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableForallFin___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableBallLE___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableBallLE___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableBallLE___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableBallLE___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableBallLE(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableBallLE___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsLTTR___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsLTTR___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsLTTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsLTTR___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsLTTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsLTTR___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsLT_x27TR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsLT_x27TR___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsLT_x27TR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsLT_x27TR___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE_x27___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsFin___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsFin___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsFin___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsFin___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_decidableExistsFin(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsFin___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___redArg(lean_object* v_n_1_, lean_object* v_f_2_, lean_object* v_i_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_i_3_, v_zero_4_);
if (v_isZero_5_ == 1)
{
lean_dec(v_i_3_);
lean_dec_ref(v_f_2_);
return v_isZero_5_;
}
else
{
lean_object* v_one_6_; lean_object* v_n_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; uint8_t v___x_11_; 
v_one_6_ = lean_unsigned_to_nat(1u);
v_n_7_ = lean_nat_sub(v_i_3_, v_one_6_);
lean_dec(v_i_3_);
v___x_8_ = lean_nat_add(v_n_7_, v_one_6_);
v___x_9_ = lean_nat_sub(v_n_1_, v___x_8_);
lean_dec(v___x_8_);
lean_inc_ref(v_f_2_);
v___x_10_ = lean_apply_2(v_f_2_, v___x_9_, lean_box(0));
v___x_11_ = lean_unbox(v___x_10_);
if (v___x_11_ == 0)
{
uint8_t v___x_12_; 
lean_dec(v_n_7_);
lean_dec_ref(v_f_2_);
v___x_12_ = lean_unbox(v___x_10_);
return v___x_12_;
}
else
{
v_i_3_ = v_n_7_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___redArg___boxed(lean_object* v_n_14_, lean_object* v_f_15_, lean_object* v_i_16_){
_start:
{
uint8_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___redArg(v_n_14_, v_f_15_, v_i_16_);
lean_dec(v_n_14_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop(lean_object* v_n_19_, lean_object* v_f_20_, lean_object* v_i_21_, lean_object* v_a_22_){
_start:
{
uint8_t v___x_23_; 
v___x_23_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___redArg(v_n_19_, v_f_20_, v_i_21_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___boxed(lean_object* v_n_24_, lean_object* v_f_25_, lean_object* v_i_26_, lean_object* v_a_27_){
_start:
{
uint8_t v_res_28_; lean_object* v_r_29_; 
v_res_28_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop(v_n_24_, v_f_25_, v_i_26_, v_a_27_);
lean_dec(v_n_24_);
v_r_29_ = lean_box(v_res_28_);
return v_r_29_;
}
}
LEAN_EXPORT uint8_t l_Nat_allLTTR(lean_object* v_n_30_, lean_object* v_f_31_){
_start:
{
uint8_t v___x_32_; 
lean_inc(v_n_30_);
v___x_32_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___redArg(v_n_30_, v_f_31_, v_n_30_);
lean_dec(v_n_30_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Nat_allLTTR___boxed(lean_object* v_n_33_, lean_object* v_f_34_){
_start:
{
uint8_t v_res_35_; lean_object* v_r_36_; 
v_res_35_ = l_Nat_allLTTR(v_n_33_, v_f_34_);
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop_match__1_splitter___redArg(lean_object* v_x_37_, lean_object* v_h__1_38_, lean_object* v_h__2_39_){
_start:
{
lean_object* v_zero_40_; uint8_t v_isZero_41_; 
v_zero_40_ = lean_unsigned_to_nat(0u);
v_isZero_41_ = lean_nat_dec_eq(v_x_37_, v_zero_40_);
if (v_isZero_41_ == 1)
{
lean_object* v___x_42_; 
lean_dec(v_h__2_39_);
v___x_42_ = lean_apply_1(v_h__1_38_, lean_box(0));
return v___x_42_;
}
else
{
lean_object* v_one_43_; lean_object* v_n_44_; lean_object* v___x_45_; 
lean_dec(v_h__1_38_);
v_one_43_ = lean_unsigned_to_nat(1u);
v_n_44_ = lean_nat_sub(v_x_37_, v_one_43_);
v___x_45_ = lean_apply_2(v_h__2_39_, v_n_44_, lean_box(0));
return v___x_45_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop_match__1_splitter___redArg___boxed(lean_object* v_x_46_, lean_object* v_h__1_47_, lean_object* v_h__2_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop_match__1_splitter___redArg(v_x_46_, v_h__1_47_, v_h__2_48_);
lean_dec(v_x_46_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop_match__1_splitter(lean_object* v_n_50_, lean_object* v_motive_51_, lean_object* v_x_52_, lean_object* v_x_53_, lean_object* v_h__1_54_, lean_object* v_h__2_55_){
_start:
{
lean_object* v_zero_56_; uint8_t v_isZero_57_; 
v_zero_56_ = lean_unsigned_to_nat(0u);
v_isZero_57_ = lean_nat_dec_eq(v_x_52_, v_zero_56_);
if (v_isZero_57_ == 1)
{
lean_object* v___x_58_; 
lean_dec(v_h__2_55_);
v___x_58_ = lean_apply_1(v_h__1_54_, lean_box(0));
return v___x_58_;
}
else
{
lean_object* v_one_59_; lean_object* v_n_60_; lean_object* v___x_61_; 
lean_dec(v_h__1_54_);
v_one_59_ = lean_unsigned_to_nat(1u);
v_n_60_ = lean_nat_sub(v_x_52_, v_one_59_);
v___x_61_ = lean_apply_2(v_h__2_55_, v_n_60_, lean_box(0));
return v___x_61_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop_match__1_splitter___boxed(lean_object* v_n_62_, lean_object* v_motive_63_, lean_object* v_x_64_, lean_object* v_x_65_, lean_object* v_h__1_66_, lean_object* v_h__2_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop_match__1_splitter(v_n_62_, v_motive_63_, v_x_64_, v_x_65_, v_h__1_66_, v_h__2_67_);
lean_dec(v_x_64_);
lean_dec(v_n_62_);
return v_res_68_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(lean_object* v_n_69_, lean_object* v_f_70_, lean_object* v_i_71_){
_start:
{
lean_object* v_zero_72_; uint8_t v_isZero_73_; 
v_zero_72_ = lean_unsigned_to_nat(0u);
v_isZero_73_ = lean_nat_dec_eq(v_i_71_, v_zero_72_);
if (v_isZero_73_ == 1)
{
uint8_t v___x_74_; 
lean_dec(v_i_71_);
lean_dec_ref(v_f_70_);
v___x_74_ = 0;
return v___x_74_;
}
else
{
lean_object* v_one_75_; lean_object* v_n_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v_one_75_ = lean_unsigned_to_nat(1u);
v_n_76_ = lean_nat_sub(v_i_71_, v_one_75_);
lean_dec(v_i_71_);
v___x_77_ = lean_nat_add(v_n_76_, v_one_75_);
v___x_78_ = lean_nat_sub(v_n_69_, v___x_77_);
lean_dec(v___x_77_);
lean_inc_ref(v_f_70_);
v___x_79_ = lean_apply_2(v_f_70_, v___x_78_, lean_box(0));
v___x_80_ = lean_unbox(v___x_79_);
if (v___x_80_ == 0)
{
v_i_71_ = v_n_76_;
goto _start;
}
else
{
uint8_t v___x_82_; 
lean_dec(v_n_76_);
lean_dec_ref(v_f_70_);
v___x_82_ = lean_unbox(v___x_79_);
return v___x_82_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg___boxed(lean_object* v_n_83_, lean_object* v_f_84_, lean_object* v_i_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(v_n_83_, v_f_84_, v_i_85_);
lean_dec(v_n_83_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop(lean_object* v_n_88_, lean_object* v_f_89_, lean_object* v_i_90_, lean_object* v_a_91_){
_start:
{
uint8_t v___x_92_; 
v___x_92_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(v_n_88_, v_f_89_, v_i_90_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___boxed(lean_object* v_n_93_, lean_object* v_f_94_, lean_object* v_i_95_, lean_object* v_a_96_){
_start:
{
uint8_t v_res_97_; lean_object* v_r_98_; 
v_res_97_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop(v_n_93_, v_f_94_, v_i_95_, v_a_96_);
lean_dec(v_n_93_);
v_r_98_ = lean_box(v_res_97_);
return v_r_98_;
}
}
LEAN_EXPORT uint8_t l_Nat_anyLTTR(lean_object* v_n_99_, lean_object* v_f_100_){
_start:
{
uint8_t v___x_101_; 
lean_inc(v_n_99_);
v___x_101_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(v_n_99_, v_f_100_, v_n_99_);
lean_dec(v_n_99_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Nat_anyLTTR___boxed(lean_object* v_n_102_, lean_object* v_f_103_){
_start:
{
uint8_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = l_Nat_anyLTTR(v_n_102_, v_f_103_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableBallLTTR___redArg___lam__0(lean_object* v_inst_106_, lean_object* v_i_107_, lean_object* v_h_108_){
_start:
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = lean_apply_2(v_inst_106_, v_i_107_, lean_box(0));
v___x_110_ = lean_unbox(v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableBallLTTR___redArg___lam__0___boxed(lean_object* v_inst_111_, lean_object* v_i_112_, lean_object* v_h_113_){
_start:
{
uint8_t v_res_114_; lean_object* v_r_115_; 
v_res_114_ = l_Nat_decidableBallLTTR___redArg___lam__0(v_inst_111_, v_i_112_, v_h_113_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableBallLTTR___redArg(lean_object* v_n_116_, lean_object* v_inst_117_){
_start:
{
lean_object* v___f_118_; uint8_t v___x_119_; 
v___f_118_ = lean_alloc_closure((void*)(l_Nat_decidableBallLTTR___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_118_, 0, v_inst_117_);
lean_inc(v_n_116_);
v___x_119_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___redArg(v_n_116_, v___f_118_, v_n_116_);
lean_dec(v_n_116_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableBallLTTR___redArg___boxed(lean_object* v_n_120_, lean_object* v_inst_121_){
_start:
{
uint8_t v_res_122_; lean_object* v_r_123_; 
v_res_122_ = l_Nat_decidableBallLTTR___redArg(v_n_120_, v_inst_121_);
v_r_123_ = lean_box(v_res_122_);
return v_r_123_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableBallLTTR(lean_object* v_n_124_, lean_object* v_P_125_, lean_object* v_inst_126_){
_start:
{
uint8_t v___x_127_; 
v___x_127_ = l_Nat_decidableBallLTTR___redArg(v_n_124_, v_inst_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableBallLTTR___boxed(lean_object* v_n_128_, lean_object* v_P_129_, lean_object* v_inst_130_){
_start:
{
uint8_t v_res_131_; lean_object* v_r_132_; 
v_res_131_ = l_Nat_decidableBallLTTR(v_n_128_, v_P_129_, v_inst_130_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableForallFin___redArg___lam__0(lean_object* v_inst_133_, lean_object* v_n_134_, lean_object* v_h_135_){
_start:
{
lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_136_ = lean_apply_1(v_inst_133_, v_n_134_);
v___x_137_ = lean_unbox(v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableForallFin___redArg___lam__0___boxed(lean_object* v_inst_138_, lean_object* v_n_139_, lean_object* v_h_140_){
_start:
{
uint8_t v_res_141_; lean_object* v_r_142_; 
v_res_141_ = l_Nat_decidableForallFin___redArg___lam__0(v_inst_138_, v_n_139_, v_h_140_);
v_r_142_ = lean_box(v_res_141_);
return v_r_142_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableForallFin___redArg(lean_object* v_n_143_, lean_object* v_inst_144_){
_start:
{
lean_object* v___f_145_; uint8_t v___x_146_; 
v___f_145_ = lean_alloc_closure((void*)(l_Nat_decidableForallFin___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_145_, 0, v_inst_144_);
v___x_146_ = l_Nat_decidableBallLTTR___redArg(v_n_143_, v___f_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableForallFin___redArg___boxed(lean_object* v_n_147_, lean_object* v_inst_148_){
_start:
{
uint8_t v_res_149_; lean_object* v_r_150_; 
v_res_149_ = l_Nat_decidableForallFin___redArg(v_n_147_, v_inst_148_);
v_r_150_ = lean_box(v_res_149_);
return v_r_150_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableForallFin(lean_object* v_n_151_, lean_object* v_P_152_, lean_object* v_inst_153_){
_start:
{
uint8_t v___x_154_; 
v___x_154_ = l_Nat_decidableForallFin___redArg(v_n_151_, v_inst_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableForallFin___boxed(lean_object* v_n_155_, lean_object* v_P_156_, lean_object* v_inst_157_){
_start:
{
uint8_t v_res_158_; lean_object* v_r_159_; 
v_res_158_ = l_Nat_decidableForallFin(v_n_155_, v_P_156_, v_inst_157_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableBallLE___redArg___lam__0(lean_object* v_inst_160_, lean_object* v_n_161_, lean_object* v_h_162_){
_start:
{
lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = lean_apply_2(v_inst_160_, v_n_161_, lean_box(0));
v___x_164_ = lean_unbox(v___x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableBallLE___redArg___lam__0___boxed(lean_object* v_inst_165_, lean_object* v_n_166_, lean_object* v_h_167_){
_start:
{
uint8_t v_res_168_; lean_object* v_r_169_; 
v_res_168_ = l_Nat_decidableBallLE___redArg___lam__0(v_inst_165_, v_n_166_, v_h_167_);
v_r_169_ = lean_box(v_res_168_);
return v_r_169_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableBallLE___redArg(lean_object* v_n_170_, lean_object* v_inst_171_){
_start:
{
lean_object* v___f_172_; lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v___f_172_ = lean_alloc_closure((void*)(l_Nat_decidableBallLE___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_172_, 0, v_inst_171_);
v___x_173_ = lean_unsigned_to_nat(1u);
v___x_174_ = lean_nat_add(v_n_170_, v___x_173_);
v___x_175_ = l_Nat_decidableBallLTTR___redArg(v___x_174_, v___f_172_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableBallLE___redArg___boxed(lean_object* v_n_176_, lean_object* v_inst_177_){
_start:
{
uint8_t v_res_178_; lean_object* v_r_179_; 
v_res_178_ = l_Nat_decidableBallLE___redArg(v_n_176_, v_inst_177_);
lean_dec(v_n_176_);
v_r_179_ = lean_box(v_res_178_);
return v_r_179_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableBallLE(lean_object* v_n_180_, lean_object* v_P_181_, lean_object* v_inst_182_){
_start:
{
uint8_t v___x_183_; 
v___x_183_ = l_Nat_decidableBallLE___redArg(v_n_180_, v_inst_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableBallLE___boxed(lean_object* v_n_184_, lean_object* v_P_185_, lean_object* v_inst_186_){
_start:
{
uint8_t v_res_187_; lean_object* v_r_188_; 
v_res_187_ = l_Nat_decidableBallLE(v_n_184_, v_P_185_, v_inst_186_);
lean_dec(v_n_184_);
v_r_188_ = lean_box(v_res_187_);
return v_r_188_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLTTR___redArg___lam__0(lean_object* v_inst_189_, lean_object* v_i_190_, lean_object* v_x_191_){
_start:
{
lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_192_ = lean_apply_1(v_inst_189_, v_i_190_);
v___x_193_ = lean_unbox(v___x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLTTR___redArg___lam__0___boxed(lean_object* v_inst_194_, lean_object* v_i_195_, lean_object* v_x_196_){
_start:
{
uint8_t v_res_197_; lean_object* v_r_198_; 
v_res_197_ = l_Nat_decidableExistsLTTR___redArg___lam__0(v_inst_194_, v_i_195_, v_x_196_);
v_r_198_ = lean_box(v_res_197_);
return v_r_198_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLTTR___redArg(lean_object* v_inst_199_, lean_object* v_n_200_){
_start:
{
lean_object* v___f_201_; uint8_t v___x_202_; 
v___f_201_ = lean_alloc_closure((void*)(l_Nat_decidableExistsLTTR___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_201_, 0, v_inst_199_);
lean_inc(v_n_200_);
v___x_202_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(v_n_200_, v___f_201_, v_n_200_);
lean_dec(v_n_200_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLTTR___redArg___boxed(lean_object* v_inst_203_, lean_object* v_n_204_){
_start:
{
uint8_t v_res_205_; lean_object* v_r_206_; 
v_res_205_ = l_Nat_decidableExistsLTTR___redArg(v_inst_203_, v_n_204_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLTTR(lean_object* v_p_207_, lean_object* v_inst_208_, lean_object* v_n_209_){
_start:
{
uint8_t v___x_210_; 
v___x_210_ = l_Nat_decidableExistsLTTR___redArg(v_inst_208_, v_n_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLTTR___boxed(lean_object* v_p_211_, lean_object* v_inst_212_, lean_object* v_n_213_){
_start:
{
uint8_t v_res_214_; lean_object* v_r_215_; 
v_res_214_ = l_Nat_decidableExistsLTTR(v_p_211_, v_inst_212_, v_n_213_);
v_r_215_ = lean_box(v_res_214_);
return v_r_215_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE___redArg(lean_object* v_inst_216_, lean_object* v_n_217_){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_218_ = lean_unsigned_to_nat(1u);
v___x_219_ = lean_nat_add(v_n_217_, v___x_218_);
v___x_220_ = l_Nat_decidableExistsLTTR___redArg(v_inst_216_, v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE___redArg___boxed(lean_object* v_inst_221_, lean_object* v_n_222_){
_start:
{
uint8_t v_res_223_; lean_object* v_r_224_; 
v_res_223_ = l_Nat_decidableExistsLE___redArg(v_inst_221_, v_n_222_);
lean_dec(v_n_222_);
v_r_224_ = lean_box(v_res_223_);
return v_r_224_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE(lean_object* v_p_225_, lean_object* v_inst_226_, lean_object* v_n_227_){
_start:
{
uint8_t v___x_228_; 
v___x_228_ = l_Nat_decidableExistsLE___redArg(v_inst_226_, v_n_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE___boxed(lean_object* v_p_229_, lean_object* v_inst_230_, lean_object* v_n_231_){
_start:
{
uint8_t v_res_232_; lean_object* v_r_233_; 
v_res_232_ = l_Nat_decidableExistsLE(v_p_229_, v_inst_230_, v_n_231_);
lean_dec(v_n_231_);
v_r_233_ = lean_box(v_res_232_);
return v_r_233_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLT_x27TR___redArg(lean_object* v_k_234_, lean_object* v_inst_235_){
_start:
{
lean_object* v___f_236_; uint8_t v___x_237_; 
v___f_236_ = lean_alloc_closure((void*)(l_Nat_decidableBallLTTR___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_236_, 0, v_inst_235_);
lean_inc(v_k_234_);
v___x_237_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(v_k_234_, v___f_236_, v_k_234_);
lean_dec(v_k_234_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLT_x27TR___redArg___boxed(lean_object* v_k_238_, lean_object* v_inst_239_){
_start:
{
uint8_t v_res_240_; lean_object* v_r_241_; 
v_res_240_ = l_Nat_decidableExistsLT_x27TR___redArg(v_k_238_, v_inst_239_);
v_r_241_ = lean_box(v_res_240_);
return v_r_241_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLT_x27TR(lean_object* v_k_242_, lean_object* v_p_243_, lean_object* v_inst_244_){
_start:
{
uint8_t v___x_245_; 
v___x_245_ = l_Nat_decidableExistsLT_x27TR___redArg(v_k_242_, v_inst_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLT_x27TR___boxed(lean_object* v_k_246_, lean_object* v_p_247_, lean_object* v_inst_248_){
_start:
{
uint8_t v_res_249_; lean_object* v_r_250_; 
v_res_249_ = l_Nat_decidableExistsLT_x27TR(v_k_246_, v_p_247_, v_inst_248_);
v_r_250_ = lean_box(v_res_249_);
return v_r_250_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE_x27___redArg___lam__0(lean_object* v_I_251_, lean_object* v_m_252_, lean_object* v_h_253_){
_start:
{
lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_254_ = lean_apply_2(v_I_251_, v_m_252_, lean_box(0));
v___x_255_ = lean_unbox(v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE_x27___redArg___lam__0___boxed(lean_object* v_I_256_, lean_object* v_m_257_, lean_object* v_h_258_){
_start:
{
uint8_t v_res_259_; lean_object* v_r_260_; 
v_res_259_ = l_Nat_decidableExistsLE_x27___redArg___lam__0(v_I_256_, v_m_257_, v_h_258_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE_x27___redArg(lean_object* v_k_261_, lean_object* v_I_262_){
_start:
{
lean_object* v___f_263_; lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v___f_263_ = lean_alloc_closure((void*)(l_Nat_decidableExistsLE_x27___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_263_, 0, v_I_262_);
v___x_264_ = lean_unsigned_to_nat(1u);
v___x_265_ = lean_nat_add(v_k_261_, v___x_264_);
v___x_266_ = l_Nat_decidableExistsLT_x27TR___redArg(v___x_265_, v___f_263_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE_x27___redArg___boxed(lean_object* v_k_267_, lean_object* v_I_268_){
_start:
{
uint8_t v_res_269_; lean_object* v_r_270_; 
v_res_269_ = l_Nat_decidableExistsLE_x27___redArg(v_k_267_, v_I_268_);
lean_dec(v_k_267_);
v_r_270_ = lean_box(v_res_269_);
return v_r_270_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE_x27(lean_object* v_k_271_, lean_object* v_p_272_, lean_object* v_I_273_){
_start:
{
uint8_t v___x_274_; 
v___x_274_ = l_Nat_decidableExistsLE_x27___redArg(v_k_271_, v_I_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE_x27___boxed(lean_object* v_k_275_, lean_object* v_p_276_, lean_object* v_I_277_){
_start:
{
uint8_t v_res_278_; lean_object* v_r_279_; 
v_res_278_ = l_Nat_decidableExistsLE_x27(v_k_275_, v_p_276_, v_I_277_);
lean_dec(v_k_275_);
v_r_279_ = lean_box(v_res_278_);
return v_r_279_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsFin___redArg___lam__0(lean_object* v_n_280_, lean_object* v_inst_281_, lean_object* v_a_282_){
_start:
{
uint8_t v___x_283_; 
v___x_283_ = lean_nat_dec_lt(v_a_282_, v_n_280_);
if (v___x_283_ == 0)
{
uint8_t v___x_284_; 
lean_dec(v_a_282_);
lean_dec_ref(v_inst_281_);
v___x_284_ = 1;
return v___x_284_;
}
else
{
lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_285_ = lean_apply_1(v_inst_281_, v_a_282_);
v___x_286_ = lean_unbox(v___x_285_);
return v___x_286_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsFin___redArg___lam__0___boxed(lean_object* v_n_287_, lean_object* v_inst_288_, lean_object* v_a_289_){
_start:
{
uint8_t v_res_290_; lean_object* v_r_291_; 
v_res_290_ = l_Nat_decidableExistsFin___redArg___lam__0(v_n_287_, v_inst_288_, v_a_289_);
lean_dec(v_n_287_);
v_r_291_ = lean_box(v_res_290_);
return v_r_291_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsFin___redArg(lean_object* v_n_292_, lean_object* v_inst_293_){
_start:
{
lean_object* v___f_294_; uint8_t v___x_295_; 
lean_inc(v_n_292_);
v___f_294_ = lean_alloc_closure((void*)(l_Nat_decidableExistsFin___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_294_, 0, v_n_292_);
lean_closure_set(v___f_294_, 1, v_inst_293_);
v___x_295_ = l_Nat_decidableExistsLTTR___redArg(v___f_294_, v_n_292_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsFin___redArg___boxed(lean_object* v_n_296_, lean_object* v_inst_297_){
_start:
{
uint8_t v_res_298_; lean_object* v_r_299_; 
v_res_298_ = l_Nat_decidableExistsFin___redArg(v_n_296_, v_inst_297_);
v_r_299_ = lean_box(v_res_298_);
return v_r_299_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsFin(lean_object* v_n_300_, lean_object* v_P_301_, lean_object* v_inst_302_){
_start:
{
uint8_t v___x_303_; 
v___x_303_ = l_Nat_decidableExistsFin___redArg(v_n_300_, v_inst_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsFin___boxed(lean_object* v_n_304_, lean_object* v_P_305_, lean_object* v_inst_306_){
_start:
{
uint8_t v_res_307_; lean_object* v_r_308_; 
v_res_307_ = l_Nat_decidableExistsFin(v_n_304_, v_P_305_, v_inst_306_);
v_r_308_ = lean_box(v_res_307_);
return v_r_308_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Log2(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Log2(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Dvd(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Nat_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Mod(builtin);
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
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Nat_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Log2(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Log2(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
lean_object* initialize_Init_PropLemmas(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Dvd(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_RCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Mod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Nat_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
