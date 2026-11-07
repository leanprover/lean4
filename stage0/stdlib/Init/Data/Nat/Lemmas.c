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
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(lean_object* v_n_37_, lean_object* v_f_38_, lean_object* v_i_39_){
_start:
{
lean_object* v_zero_40_; uint8_t v_isZero_41_; 
v_zero_40_ = lean_unsigned_to_nat(0u);
v_isZero_41_ = lean_nat_dec_eq(v_i_39_, v_zero_40_);
if (v_isZero_41_ == 1)
{
uint8_t v___x_42_; 
lean_dec(v_i_39_);
lean_dec_ref(v_f_38_);
v___x_42_ = 0;
return v___x_42_;
}
else
{
lean_object* v_one_43_; lean_object* v_n_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; uint8_t v___x_48_; 
v_one_43_ = lean_unsigned_to_nat(1u);
v_n_44_ = lean_nat_sub(v_i_39_, v_one_43_);
lean_dec(v_i_39_);
v___x_45_ = lean_nat_add(v_n_44_, v_one_43_);
v___x_46_ = lean_nat_sub(v_n_37_, v___x_45_);
lean_dec(v___x_45_);
lean_inc_ref(v_f_38_);
v___x_47_ = lean_apply_2(v_f_38_, v___x_46_, lean_box(0));
v___x_48_ = lean_unbox(v___x_47_);
if (v___x_48_ == 0)
{
v_i_39_ = v_n_44_;
goto _start;
}
else
{
uint8_t v___x_50_; 
lean_dec(v_n_44_);
lean_dec_ref(v_f_38_);
v___x_50_ = lean_unbox(v___x_47_);
return v___x_50_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg___boxed(lean_object* v_n_51_, lean_object* v_f_52_, lean_object* v_i_53_){
_start:
{
uint8_t v_res_54_; lean_object* v_r_55_; 
v_res_54_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(v_n_51_, v_f_52_, v_i_53_);
lean_dec(v_n_51_);
v_r_55_ = lean_box(v_res_54_);
return v_r_55_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop(lean_object* v_n_56_, lean_object* v_f_57_, lean_object* v_i_58_, lean_object* v_a_59_){
_start:
{
uint8_t v___x_60_; 
v___x_60_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(v_n_56_, v_f_57_, v_i_58_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___boxed(lean_object* v_n_61_, lean_object* v_f_62_, lean_object* v_i_63_, lean_object* v_a_64_){
_start:
{
uint8_t v_res_65_; lean_object* v_r_66_; 
v_res_65_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop(v_n_61_, v_f_62_, v_i_63_, v_a_64_);
lean_dec(v_n_61_);
v_r_66_ = lean_box(v_res_65_);
return v_r_66_;
}
}
LEAN_EXPORT uint8_t l_Nat_anyLTTR(lean_object* v_n_67_, lean_object* v_f_68_){
_start:
{
uint8_t v___x_69_; 
lean_inc(v_n_67_);
v___x_69_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(v_n_67_, v_f_68_, v_n_67_);
lean_dec(v_n_67_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Nat_anyLTTR___boxed(lean_object* v_n_70_, lean_object* v_f_71_){
_start:
{
uint8_t v_res_72_; lean_object* v_r_73_; 
v_res_72_ = l_Nat_anyLTTR(v_n_70_, v_f_71_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableBallLTTR___redArg___lam__0(lean_object* v_inst_74_, lean_object* v_i_75_, lean_object* v_h_76_){
_start:
{
lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_77_ = lean_apply_2(v_inst_74_, v_i_75_, lean_box(0));
v___x_78_ = lean_unbox(v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableBallLTTR___redArg___lam__0___boxed(lean_object* v_inst_79_, lean_object* v_i_80_, lean_object* v_h_81_){
_start:
{
uint8_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = l_Nat_decidableBallLTTR___redArg___lam__0(v_inst_79_, v_i_80_, v_h_81_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableBallLTTR___redArg(lean_object* v_n_84_, lean_object* v_inst_85_){
_start:
{
lean_object* v___f_86_; uint8_t v___x_87_; 
v___f_86_ = lean_alloc_closure((void*)(l_Nat_decidableBallLTTR___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_86_, 0, v_inst_85_);
lean_inc(v_n_84_);
v___x_87_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___redArg(v_n_84_, v___f_86_, v_n_84_);
lean_dec(v_n_84_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableBallLTTR___redArg___boxed(lean_object* v_n_88_, lean_object* v_inst_89_){
_start:
{
uint8_t v_res_90_; lean_object* v_r_91_; 
v_res_90_ = l_Nat_decidableBallLTTR___redArg(v_n_88_, v_inst_89_);
v_r_91_ = lean_box(v_res_90_);
return v_r_91_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableBallLTTR(lean_object* v_n_92_, lean_object* v_P_93_, lean_object* v_inst_94_){
_start:
{
uint8_t v___x_95_; 
v___x_95_ = l_Nat_decidableBallLTTR___redArg(v_n_92_, v_inst_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableBallLTTR___boxed(lean_object* v_n_96_, lean_object* v_P_97_, lean_object* v_inst_98_){
_start:
{
uint8_t v_res_99_; lean_object* v_r_100_; 
v_res_99_ = l_Nat_decidableBallLTTR(v_n_96_, v_P_97_, v_inst_98_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableForallFin___redArg___lam__0(lean_object* v_inst_101_, lean_object* v_i_102_, lean_object* v_h_103_){
_start:
{
lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_104_ = lean_apply_1(v_inst_101_, v_i_102_);
v___x_105_ = lean_unbox(v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableForallFin___redArg___lam__0___boxed(lean_object* v_inst_106_, lean_object* v_i_107_, lean_object* v_h_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Nat_decidableForallFin___redArg___lam__0(v_inst_106_, v_i_107_, v_h_108_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableForallFin___redArg(lean_object* v_n_111_, lean_object* v_inst_112_){
_start:
{
lean_object* v___f_113_; uint8_t v___x_114_; 
v___f_113_ = lean_alloc_closure((void*)(l_Nat_decidableForallFin___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_113_, 0, v_inst_112_);
lean_inc(v_n_111_);
v___x_114_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___redArg(v_n_111_, v___f_113_, v_n_111_);
lean_dec(v_n_111_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableForallFin___redArg___boxed(lean_object* v_n_115_, lean_object* v_inst_116_){
_start:
{
uint8_t v_res_117_; lean_object* v_r_118_; 
v_res_117_ = l_Nat_decidableForallFin___redArg(v_n_115_, v_inst_116_);
v_r_118_ = lean_box(v_res_117_);
return v_r_118_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableForallFin(lean_object* v_n_119_, lean_object* v_P_120_, lean_object* v_inst_121_){
_start:
{
uint8_t v___x_122_; 
v___x_122_ = l_Nat_decidableForallFin___redArg(v_n_119_, v_inst_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableForallFin___boxed(lean_object* v_n_123_, lean_object* v_P_124_, lean_object* v_inst_125_){
_start:
{
uint8_t v_res_126_; lean_object* v_r_127_; 
v_res_126_ = l_Nat_decidableForallFin(v_n_123_, v_P_124_, v_inst_125_);
v_r_127_ = lean_box(v_res_126_);
return v_r_127_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableBallLE___redArg(lean_object* v_n_128_, lean_object* v_inst_129_){
_start:
{
lean_object* v___f_130_; lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v___f_130_ = lean_alloc_closure((void*)(l_Nat_decidableBallLTTR___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_130_, 0, v_inst_129_);
v___x_131_ = lean_unsigned_to_nat(1u);
v___x_132_ = lean_nat_add(v_n_128_, v___x_131_);
lean_inc(v___x_132_);
v___x_133_ = l___private_Init_Data_Nat_Lemmas_0__Nat_allLTTR_loop___redArg(v___x_132_, v___f_130_, v___x_132_);
lean_dec(v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableBallLE___redArg___boxed(lean_object* v_n_134_, lean_object* v_inst_135_){
_start:
{
uint8_t v_res_136_; lean_object* v_r_137_; 
v_res_136_ = l_Nat_decidableBallLE___redArg(v_n_134_, v_inst_135_);
lean_dec(v_n_134_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableBallLE(lean_object* v_n_138_, lean_object* v_P_139_, lean_object* v_inst_140_){
_start:
{
uint8_t v___x_141_; 
v___x_141_ = l_Nat_decidableBallLE___redArg(v_n_138_, v_inst_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableBallLE___boxed(lean_object* v_n_142_, lean_object* v_P_143_, lean_object* v_inst_144_){
_start:
{
uint8_t v_res_145_; lean_object* v_r_146_; 
v_res_145_ = l_Nat_decidableBallLE(v_n_142_, v_P_143_, v_inst_144_);
lean_dec(v_n_142_);
v_r_146_ = lean_box(v_res_145_);
return v_r_146_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLTTR___redArg___lam__0(lean_object* v_inst_147_, lean_object* v_i_148_, lean_object* v_x_149_){
_start:
{
lean_object* v___x_150_; uint8_t v___x_151_; 
v___x_150_ = lean_apply_1(v_inst_147_, v_i_148_);
v___x_151_ = lean_unbox(v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLTTR___redArg___lam__0___boxed(lean_object* v_inst_152_, lean_object* v_i_153_, lean_object* v_x_154_){
_start:
{
uint8_t v_res_155_; lean_object* v_r_156_; 
v_res_155_ = l_Nat_decidableExistsLTTR___redArg___lam__0(v_inst_152_, v_i_153_, v_x_154_);
v_r_156_ = lean_box(v_res_155_);
return v_r_156_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLTTR___redArg(lean_object* v_inst_157_, lean_object* v_n_158_){
_start:
{
lean_object* v___f_159_; uint8_t v___x_160_; 
v___f_159_ = lean_alloc_closure((void*)(l_Nat_decidableExistsLTTR___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_159_, 0, v_inst_157_);
lean_inc(v_n_158_);
v___x_160_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(v_n_158_, v___f_159_, v_n_158_);
lean_dec(v_n_158_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLTTR___redArg___boxed(lean_object* v_inst_161_, lean_object* v_n_162_){
_start:
{
uint8_t v_res_163_; lean_object* v_r_164_; 
v_res_163_ = l_Nat_decidableExistsLTTR___redArg(v_inst_161_, v_n_162_);
v_r_164_ = lean_box(v_res_163_);
return v_r_164_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLTTR(lean_object* v_p_165_, lean_object* v_inst_166_, lean_object* v_n_167_){
_start:
{
uint8_t v___x_168_; 
v___x_168_ = l_Nat_decidableExistsLTTR___redArg(v_inst_166_, v_n_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLTTR___boxed(lean_object* v_p_169_, lean_object* v_inst_170_, lean_object* v_n_171_){
_start:
{
uint8_t v_res_172_; lean_object* v_r_173_; 
v_res_172_ = l_Nat_decidableExistsLTTR(v_p_169_, v_inst_170_, v_n_171_);
v_r_173_ = lean_box(v_res_172_);
return v_r_173_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE___redArg(lean_object* v_inst_174_, lean_object* v_n_175_){
_start:
{
lean_object* v___f_176_; lean_object* v___x_177_; lean_object* v___x_178_; uint8_t v___x_179_; 
v___f_176_ = lean_alloc_closure((void*)(l_Nat_decidableExistsLTTR___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_176_, 0, v_inst_174_);
v___x_177_ = lean_unsigned_to_nat(1u);
v___x_178_ = lean_nat_add(v_n_175_, v___x_177_);
lean_inc(v___x_178_);
v___x_179_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(v___x_178_, v___f_176_, v___x_178_);
lean_dec(v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE___redArg___boxed(lean_object* v_inst_180_, lean_object* v_n_181_){
_start:
{
uint8_t v_res_182_; lean_object* v_r_183_; 
v_res_182_ = l_Nat_decidableExistsLE___redArg(v_inst_180_, v_n_181_);
lean_dec(v_n_181_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE(lean_object* v_p_184_, lean_object* v_inst_185_, lean_object* v_n_186_){
_start:
{
uint8_t v___x_187_; 
v___x_187_ = l_Nat_decidableExistsLE___redArg(v_inst_185_, v_n_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE___boxed(lean_object* v_p_188_, lean_object* v_inst_189_, lean_object* v_n_190_){
_start:
{
uint8_t v_res_191_; lean_object* v_r_192_; 
v_res_191_ = l_Nat_decidableExistsLE(v_p_188_, v_inst_189_, v_n_190_);
lean_dec(v_n_190_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLT_x27TR___redArg(lean_object* v_k_193_, lean_object* v_inst_194_){
_start:
{
lean_object* v___f_195_; uint8_t v___x_196_; 
v___f_195_ = lean_alloc_closure((void*)(l_Nat_decidableBallLTTR___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_195_, 0, v_inst_194_);
lean_inc(v_k_193_);
v___x_196_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(v_k_193_, v___f_195_, v_k_193_);
lean_dec(v_k_193_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLT_x27TR___redArg___boxed(lean_object* v_k_197_, lean_object* v_inst_198_){
_start:
{
uint8_t v_res_199_; lean_object* v_r_200_; 
v_res_199_ = l_Nat_decidableExistsLT_x27TR___redArg(v_k_197_, v_inst_198_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLT_x27TR(lean_object* v_k_201_, lean_object* v_p_202_, lean_object* v_inst_203_){
_start:
{
uint8_t v___x_204_; 
v___x_204_ = l_Nat_decidableExistsLT_x27TR___redArg(v_k_201_, v_inst_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLT_x27TR___boxed(lean_object* v_k_205_, lean_object* v_p_206_, lean_object* v_inst_207_){
_start:
{
uint8_t v_res_208_; lean_object* v_r_209_; 
v_res_208_ = l_Nat_decidableExistsLT_x27TR(v_k_205_, v_p_206_, v_inst_207_);
v_r_209_ = lean_box(v_res_208_);
return v_r_209_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE_x27___redArg___lam__0(lean_object* v_I_210_, lean_object* v_i_211_, lean_object* v_h_212_){
_start:
{
lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_213_ = lean_apply_2(v_I_210_, v_i_211_, lean_box(0));
v___x_214_ = lean_unbox(v___x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE_x27___redArg___lam__0___boxed(lean_object* v_I_215_, lean_object* v_i_216_, lean_object* v_h_217_){
_start:
{
uint8_t v_res_218_; lean_object* v_r_219_; 
v_res_218_ = l_Nat_decidableExistsLE_x27___redArg___lam__0(v_I_215_, v_i_216_, v_h_217_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE_x27___redArg(lean_object* v_k_220_, lean_object* v_I_221_){
_start:
{
lean_object* v___f_222_; lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v___f_222_ = lean_alloc_closure((void*)(l_Nat_decidableExistsLE_x27___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_222_, 0, v_I_221_);
v___x_223_ = lean_unsigned_to_nat(1u);
v___x_224_ = lean_nat_add(v_k_220_, v___x_223_);
lean_inc(v___x_224_);
v___x_225_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(v___x_224_, v___f_222_, v___x_224_);
lean_dec(v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE_x27___redArg___boxed(lean_object* v_k_226_, lean_object* v_I_227_){
_start:
{
uint8_t v_res_228_; lean_object* v_r_229_; 
v_res_228_ = l_Nat_decidableExistsLE_x27___redArg(v_k_226_, v_I_227_);
lean_dec(v_k_226_);
v_r_229_ = lean_box(v_res_228_);
return v_r_229_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsLE_x27(lean_object* v_k_230_, lean_object* v_p_231_, lean_object* v_I_232_){
_start:
{
uint8_t v___x_233_; 
v___x_233_ = l_Nat_decidableExistsLE_x27___redArg(v_k_230_, v_I_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsLE_x27___boxed(lean_object* v_k_234_, lean_object* v_p_235_, lean_object* v_I_236_){
_start:
{
uint8_t v_res_237_; lean_object* v_r_238_; 
v_res_237_ = l_Nat_decidableExistsLE_x27(v_k_234_, v_p_235_, v_I_236_);
lean_dec(v_k_234_);
v_r_238_ = lean_box(v_res_237_);
return v_r_238_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsFin___redArg___lam__0(lean_object* v_n_239_, lean_object* v_inst_240_, lean_object* v_i_241_, lean_object* v_x_242_){
_start:
{
uint8_t v___x_243_; 
v___x_243_ = lean_nat_dec_lt(v_i_241_, v_n_239_);
if (v___x_243_ == 0)
{
uint8_t v___x_244_; 
lean_dec(v_i_241_);
lean_dec_ref(v_inst_240_);
v___x_244_ = 1;
return v___x_244_;
}
else
{
lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_245_ = lean_apply_1(v_inst_240_, v_i_241_);
v___x_246_ = lean_unbox(v___x_245_);
return v___x_246_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsFin___redArg___lam__0___boxed(lean_object* v_n_247_, lean_object* v_inst_248_, lean_object* v_i_249_, lean_object* v_x_250_){
_start:
{
uint8_t v_res_251_; lean_object* v_r_252_; 
v_res_251_ = l_Nat_decidableExistsFin___redArg___lam__0(v_n_247_, v_inst_248_, v_i_249_, v_x_250_);
lean_dec(v_n_247_);
v_r_252_ = lean_box(v_res_251_);
return v_r_252_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsFin___redArg(lean_object* v_n_253_, lean_object* v_inst_254_){
_start:
{
lean_object* v___f_255_; uint8_t v___x_256_; 
lean_inc_n(v_n_253_, 2);
v___f_255_ = lean_alloc_closure((void*)(l_Nat_decidableExistsFin___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_255_, 0, v_n_253_);
lean_closure_set(v___f_255_, 1, v_inst_254_);
v___x_256_ = l___private_Init_Data_Nat_Lemmas_0__Nat_anyLTTR_loop___redArg(v_n_253_, v___f_255_, v_n_253_);
lean_dec(v_n_253_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsFin___redArg___boxed(lean_object* v_n_257_, lean_object* v_inst_258_){
_start:
{
uint8_t v_res_259_; lean_object* v_r_260_; 
v_res_259_ = l_Nat_decidableExistsFin___redArg(v_n_257_, v_inst_258_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
LEAN_EXPORT uint8_t l_Nat_decidableExistsFin(lean_object* v_n_261_, lean_object* v_P_262_, lean_object* v_inst_263_){
_start:
{
uint8_t v___x_264_; 
v___x_264_ = l_Nat_decidableExistsFin___redArg(v_n_261_, v_inst_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Nat_decidableExistsFin___boxed(lean_object* v_n_265_, lean_object* v_P_266_, lean_object* v_inst_267_){
_start:
{
uint8_t v_res_268_; lean_object* v_r_269_; 
v_res_268_ = l_Nat_decidableExistsFin(v_n_265_, v_P_266_, v_inst_267_);
v_r_269_ = lean_box(v_res_268_);
return v_r_269_;
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
