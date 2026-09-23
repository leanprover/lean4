// Lean compiler output
// Module: Init.Data.Nat.Lemmas
// Imports: import all Init.Data.Nat.Bitwise.Basic public import Init.Data.Nat.Log2 import all Init.Data.Nat.Log2 import Init.TacticsExtra public import Init.Data.Nat.Div.Basic public import Init.PropLemmas import Init.ByCases import Init.Data.Nat.Dvd import Init.Data.Nat.Internal.Linear import Init.Data.Nat.MinMax import Init.Data.Nat.Mod import Init.Omega import Init.RCases
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
LEAN_EXPORT uint8_t l_Nat_decidableExistsFin___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_decidableExistsFin___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Nat_decidableForallFin___redArg___lam__0(lean_object* v_inst_133_, lean_object* v_i_134_, lean_object* v_h_135_){
_start:
{
lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_136_ = lean_apply_1(v_inst_133_, v_i_134_);
v___x_137_ = lean_unbox(v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableForallFin___redArg___lam__0___boxed(lean_object* v_inst_138_, lean_object* v_i_139_, lean_object* v_h_140_){
_start:
{
uint8_t v_res_141_; lean_object* v_r_142_; 
v_res_141_ = l_Nat_decidableForallFin___redArg___lam__0(v_inst_138_, v_i_139_, v_h_140_);
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
lean_inc(v_n_143_);
v___x_146_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___redArg(v_n_143_, v___f_145_, v_n_143_);
lean_dec(v_n_143_);
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
LEAN_EXPORT uint8_t l_Nat_decidableBallLE___redArg(lean_object* v_n_160_, lean_object* v_inst_161_){
_start:
{
lean_object* v___f_162_; lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v___f_162_ = lean_alloc_closure((void*)(l_Nat_decidableBallLTTR___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_162_, 0, v_inst_161_);
v___x_163_ = lean_unsigned_to_nat(1u);
v___x_164_ = lean_nat_add(v_n_160_, v___x_163_);
lean_inc(v___x_164_);
v___x_165_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___redArg(v___x_164_, v___f_162_, v___x_164_);
lean_dec(v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableBallLE___redArg___boxed(lean_object* v_n_166_, lean_object* v_inst_167_){
_start:
{
uint8_t v_res_168_; lean_object* v_r_169_; 
v_res_168_ = l_Nat_decidableBallLE___redArg(v_n_166_, v_inst_167_);
lean_dec(v_n_166_);
v_r_169_ = lean_box(v_res_168_);
return v_r_169_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableBallLE(lean_object* v_n_170_, lean_object* v_P_171_, lean_object* v_inst_172_){
_start:
{
uint8_t v___x_173_; 
v___x_173_ = l_Nat_decidableBallLE___redArg(v_n_170_, v_inst_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableBallLE___boxed(lean_object* v_n_174_, lean_object* v_P_175_, lean_object* v_inst_176_){
_start:
{
uint8_t v_res_177_; lean_object* v_r_178_; 
v_res_177_ = l_Nat_decidableBallLE(v_n_174_, v_P_175_, v_inst_176_);
lean_dec(v_n_174_);
v_r_178_ = lean_box(v_res_177_);
return v_r_178_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLTTR___redArg___lam__0(lean_object* v_inst_179_, lean_object* v_i_180_, lean_object* v_x_181_){
_start:
{
lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_182_ = lean_apply_1(v_inst_179_, v_i_180_);
v___x_183_ = lean_unbox(v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLTTR___redArg___lam__0___boxed(lean_object* v_inst_184_, lean_object* v_i_185_, lean_object* v_x_186_){
_start:
{
uint8_t v_res_187_; lean_object* v_r_188_; 
v_res_187_ = l_Nat_decidableExistsLTTR___redArg___lam__0(v_inst_184_, v_i_185_, v_x_186_);
v_r_188_ = lean_box(v_res_187_);
return v_r_188_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLTTR___redArg(lean_object* v_inst_189_, lean_object* v_n_190_){
_start:
{
lean_object* v___f_191_; uint8_t v___x_192_; 
v___f_191_ = lean_alloc_closure((void*)(l_Nat_decidableExistsLTTR___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_191_, 0, v_inst_189_);
lean_inc(v_n_190_);
v___x_192_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(v_n_190_, v___f_191_, v_n_190_);
lean_dec(v_n_190_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLTTR___redArg___boxed(lean_object* v_inst_193_, lean_object* v_n_194_){
_start:
{
uint8_t v_res_195_; lean_object* v_r_196_; 
v_res_195_ = l_Nat_decidableExistsLTTR___redArg(v_inst_193_, v_n_194_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLTTR(lean_object* v_p_197_, lean_object* v_inst_198_, lean_object* v_n_199_){
_start:
{
uint8_t v___x_200_; 
v___x_200_ = l_Nat_decidableExistsLTTR___redArg(v_inst_198_, v_n_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLTTR___boxed(lean_object* v_p_201_, lean_object* v_inst_202_, lean_object* v_n_203_){
_start:
{
uint8_t v_res_204_; lean_object* v_r_205_; 
v_res_204_ = l_Nat_decidableExistsLTTR(v_p_201_, v_inst_202_, v_n_203_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE___redArg(lean_object* v_inst_206_, lean_object* v_n_207_){
_start:
{
lean_object* v___f_208_; lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v___f_208_ = lean_alloc_closure((void*)(l_Nat_decidableExistsLTTR___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_208_, 0, v_inst_206_);
v___x_209_ = lean_unsigned_to_nat(1u);
v___x_210_ = lean_nat_add(v_n_207_, v___x_209_);
lean_inc(v___x_210_);
v___x_211_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(v___x_210_, v___f_208_, v___x_210_);
lean_dec(v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE___redArg___boxed(lean_object* v_inst_212_, lean_object* v_n_213_){
_start:
{
uint8_t v_res_214_; lean_object* v_r_215_; 
v_res_214_ = l_Nat_decidableExistsLE___redArg(v_inst_212_, v_n_213_);
lean_dec(v_n_213_);
v_r_215_ = lean_box(v_res_214_);
return v_r_215_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE(lean_object* v_p_216_, lean_object* v_inst_217_, lean_object* v_n_218_){
_start:
{
uint8_t v___x_219_; 
v___x_219_ = l_Nat_decidableExistsLE___redArg(v_inst_217_, v_n_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE___boxed(lean_object* v_p_220_, lean_object* v_inst_221_, lean_object* v_n_222_){
_start:
{
uint8_t v_res_223_; lean_object* v_r_224_; 
v_res_223_ = l_Nat_decidableExistsLE(v_p_220_, v_inst_221_, v_n_222_);
lean_dec(v_n_222_);
v_r_224_ = lean_box(v_res_223_);
return v_r_224_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLT_x27TR___redArg(lean_object* v_k_225_, lean_object* v_inst_226_){
_start:
{
lean_object* v___f_227_; uint8_t v___x_228_; 
v___f_227_ = lean_alloc_closure((void*)(l_Nat_decidableBallLTTR___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_227_, 0, v_inst_226_);
lean_inc(v_k_225_);
v___x_228_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(v_k_225_, v___f_227_, v_k_225_);
lean_dec(v_k_225_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLT_x27TR___redArg___boxed(lean_object* v_k_229_, lean_object* v_inst_230_){
_start:
{
uint8_t v_res_231_; lean_object* v_r_232_; 
v_res_231_ = l_Nat_decidableExistsLT_x27TR___redArg(v_k_229_, v_inst_230_);
v_r_232_ = lean_box(v_res_231_);
return v_r_232_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLT_x27TR(lean_object* v_k_233_, lean_object* v_p_234_, lean_object* v_inst_235_){
_start:
{
uint8_t v___x_236_; 
v___x_236_ = l_Nat_decidableExistsLT_x27TR___redArg(v_k_233_, v_inst_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLT_x27TR___boxed(lean_object* v_k_237_, lean_object* v_p_238_, lean_object* v_inst_239_){
_start:
{
uint8_t v_res_240_; lean_object* v_r_241_; 
v_res_240_ = l_Nat_decidableExistsLT_x27TR(v_k_237_, v_p_238_, v_inst_239_);
v_r_241_ = lean_box(v_res_240_);
return v_r_241_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE_x27___redArg___lam__0(lean_object* v_I_242_, lean_object* v_i_243_, lean_object* v_h_244_){
_start:
{
lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_245_ = lean_apply_2(v_I_242_, v_i_243_, lean_box(0));
v___x_246_ = lean_unbox(v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE_x27___redArg___lam__0___boxed(lean_object* v_I_247_, lean_object* v_i_248_, lean_object* v_h_249_){
_start:
{
uint8_t v_res_250_; lean_object* v_r_251_; 
v_res_250_ = l_Nat_decidableExistsLE_x27___redArg___lam__0(v_I_247_, v_i_248_, v_h_249_);
v_r_251_ = lean_box(v_res_250_);
return v_r_251_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE_x27___redArg(lean_object* v_k_252_, lean_object* v_I_253_){
_start:
{
lean_object* v___f_254_; lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___f_254_ = lean_alloc_closure((void*)(l_Nat_decidableExistsLE_x27___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_254_, 0, v_I_253_);
v___x_255_ = lean_unsigned_to_nat(1u);
v___x_256_ = lean_nat_add(v_k_252_, v___x_255_);
lean_inc(v___x_256_);
v___x_257_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(v___x_256_, v___f_254_, v___x_256_);
lean_dec(v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE_x27___redArg___boxed(lean_object* v_k_258_, lean_object* v_I_259_){
_start:
{
uint8_t v_res_260_; lean_object* v_r_261_; 
v_res_260_ = l_Nat_decidableExistsLE_x27___redArg(v_k_258_, v_I_259_);
lean_dec(v_k_258_);
v_r_261_ = lean_box(v_res_260_);
return v_r_261_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE_x27(lean_object* v_k_262_, lean_object* v_p_263_, lean_object* v_I_264_){
_start:
{
uint8_t v___x_265_; 
v___x_265_ = l_Nat_decidableExistsLE_x27___redArg(v_k_262_, v_I_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE_x27___boxed(lean_object* v_k_266_, lean_object* v_p_267_, lean_object* v_I_268_){
_start:
{
uint8_t v_res_269_; lean_object* v_r_270_; 
v_res_269_ = l_Nat_decidableExistsLE_x27(v_k_266_, v_p_267_, v_I_268_);
lean_dec(v_k_266_);
v_r_270_ = lean_box(v_res_269_);
return v_r_270_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsFin___redArg___lam__0(lean_object* v_n_271_, lean_object* v_inst_272_, lean_object* v_i_273_, lean_object* v_x_274_){
_start:
{
uint8_t v___x_275_; 
v___x_275_ = lean_nat_dec_lt(v_i_273_, v_n_271_);
if (v___x_275_ == 0)
{
uint8_t v___x_276_; 
lean_dec(v_i_273_);
lean_dec_ref(v_inst_272_);
v___x_276_ = 1;
return v___x_276_;
}
else
{
lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_277_ = lean_apply_1(v_inst_272_, v_i_273_);
v___x_278_ = lean_unbox(v___x_277_);
return v___x_278_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsFin___redArg___lam__0___boxed(lean_object* v_n_279_, lean_object* v_inst_280_, lean_object* v_i_281_, lean_object* v_x_282_){
_start:
{
uint8_t v_res_283_; lean_object* v_r_284_; 
v_res_283_ = l_Nat_decidableExistsFin___redArg___lam__0(v_n_279_, v_inst_280_, v_i_281_, v_x_282_);
lean_dec(v_n_279_);
v_r_284_ = lean_box(v_res_283_);
return v_r_284_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsFin___redArg(lean_object* v_n_285_, lean_object* v_inst_286_){
_start:
{
lean_object* v___f_287_; uint8_t v___x_288_; 
lean_inc_n(v_n_285_, 2);
v___f_287_ = lean_alloc_closure((void*)(l_Nat_decidableExistsFin___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_287_, 0, v_n_285_);
lean_closure_set(v___f_287_, 1, v_inst_286_);
v___x_288_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(v_n_285_, v___f_287_, v_n_285_);
lean_dec(v_n_285_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsFin___redArg___boxed(lean_object* v_n_289_, lean_object* v_inst_290_){
_start:
{
uint8_t v_res_291_; lean_object* v_r_292_; 
v_res_291_ = l_Nat_decidableExistsFin___redArg(v_n_289_, v_inst_290_);
v_r_292_ = lean_box(v_res_291_);
return v_r_292_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsFin(lean_object* v_n_293_, lean_object* v_P_294_, lean_object* v_inst_295_){
_start:
{
uint8_t v___x_296_; 
v___x_296_ = l_Nat_decidableExistsFin___redArg(v_n_293_, v_inst_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsFin___boxed(lean_object* v_n_297_, lean_object* v_P_298_, lean_object* v_inst_299_){
_start:
{
uint8_t v_res_300_; lean_object* v_r_301_; 
v_res_300_ = l_Nat_decidableExistsFin(v_n_297_, v_P_298_, v_inst_299_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
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
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = runtime_initialize_Init_Data_Nat_Internal_Linear(builtin);
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
lean_object* initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
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
res = initialize_Init_Data_Nat_Internal_Linear(builtin);
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
