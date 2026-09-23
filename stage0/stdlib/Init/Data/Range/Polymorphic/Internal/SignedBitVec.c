// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Internal.SignedBitVec
// Imports: public import Init.Data.BitVec.Bootstrap public import Init.Data.BitVec.Lemmas public import Init.Data.Int.DivMod.Lemmas public import Init.Data.Int.Pow public import Init.Data.Nat.Div.Lemmas public import Init.Data.Nat.Lemmas public import Init.Data.Nat.Mod public import Init.Data.Option.Lemmas public import Init.Data.Range.Polymorphic.BitVec public import Init.Omega
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* l_BitVec_add(lean_object*, lean_object*, lean_object*);
uint8_t l_BitVec_slt(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_BitVec_sle(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_intMinSealed_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_intMinSealed_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_intMinSealed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_intMinSealed___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_intMaxSealed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_intMaxSealed___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_rotate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_rotate___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instUpwardEnumerable___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instUpwardEnumerable___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instUpwardEnumerable___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instUpwardEnumerable___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instUpwardEnumerable(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instLE___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instLE___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instLE(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instLE___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instLT___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instLT___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instLT(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instLT___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instDecidableLE(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instDecidableLE___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instDecidableLT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instDecidableLT___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxcHasSize___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxcHasSize___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxcHasSize(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxoHasSize___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxoHasSize___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxoHasSize(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxiHasSize___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxiHasSize___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxiHasSize(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_intMinSealed_spec__0(lean_object* v_n_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = l_BitVec_ofNat(v_n_1_, v_a_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_intMinSealed_spec__0___boxed(lean_object* v_n_4_, lean_object* v_a_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Nat_cast___at___00__private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_intMinSealed_spec__0(v_n_4_, v_a_5_);
lean_dec(v_a_5_);
lean_dec(v_n_4_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_intMinSealed(lean_object* v_n_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_8_ = lean_unsigned_to_nat(2u);
v___x_9_ = lean_unsigned_to_nat(1u);
v___x_10_ = lean_nat_sub(v_n_7_, v___x_9_);
v___x_11_ = lean_nat_pow(v___x_8_, v___x_10_);
lean_dec(v___x_10_);
v___x_12_ = l_BitVec_ofNat(v_n_7_, v___x_11_);
lean_dec(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_intMinSealed___boxed(lean_object* v_n_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_intMinSealed(v_n_13_);
lean_dec(v_n_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_intMaxSealed(lean_object* v_n_15_){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_16_ = lean_unsigned_to_nat(2u);
v___x_17_ = lean_unsigned_to_nat(1u);
v___x_18_ = lean_nat_sub(v_n_15_, v___x_17_);
v___x_19_ = lean_nat_pow(v___x_16_, v___x_18_);
lean_dec(v___x_18_);
v___x_20_ = lean_nat_sub(v___x_19_, v___x_17_);
lean_dec(v___x_19_);
v___x_21_ = l_BitVec_ofNat(v_n_15_, v___x_20_);
lean_dec(v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_intMaxSealed___boxed(lean_object* v_n_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_intMaxSealed(v_n_22_);
lean_dec(v_n_22_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_rotate(lean_object* v_n_24_, lean_object* v_x_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_intMinSealed(v_n_24_);
v___x_27_ = l_BitVec_add(v_n_24_, v_x_25_, v___x_26_);
lean_dec(v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_rotate___boxed(lean_object* v_n_28_, lean_object* v_x_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_rotate(v_n_28_, v_x_29_);
lean_dec(v_x_29_);
lean_dec(v_n_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instUpwardEnumerable___lam__0(lean_object* v_n_31_, lean_object* v_x_32_){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; uint8_t v___x_39_; 
v___x_33_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_rotate(v_n_31_, v_x_32_);
v___x_34_ = lean_unsigned_to_nat(1u);
v___x_35_ = l_BitVec_ofNat(v_n_31_, v___x_34_);
v___x_36_ = l_BitVec_add(v_n_31_, v___x_33_, v___x_35_);
lean_dec(v___x_35_);
lean_dec(v___x_33_);
v___x_37_ = lean_unsigned_to_nat(0u);
v___x_38_ = l_BitVec_ofNat(v_n_31_, v___x_37_);
v___x_39_ = lean_nat_dec_eq(v___x_36_, v___x_38_);
lean_dec(v___x_38_);
if (v___x_39_ == 0)
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_rotate(v_n_31_, v___x_36_);
lean_dec(v___x_36_);
v___x_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
return v___x_41_;
}
else
{
lean_object* v___x_42_; 
lean_dec(v___x_36_);
v___x_42_ = lean_box(0);
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instUpwardEnumerable___lam__0___boxed(lean_object* v_n_43_, lean_object* v_x_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instUpwardEnumerable___lam__0(v_n_43_, v_x_44_);
lean_dec(v_x_44_);
lean_dec(v_n_43_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instUpwardEnumerable___lam__1(lean_object* v_n_46_, lean_object* v_n_47_, lean_object* v_x_48_){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; uint8_t v___x_53_; 
v___x_49_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_rotate(v_n_46_, v_x_48_);
v___x_50_ = lean_nat_add(v___x_49_, v_n_47_);
lean_dec(v___x_49_);
v___x_51_ = lean_unsigned_to_nat(2u);
v___x_52_ = lean_nat_pow(v___x_51_, v_n_46_);
v___x_53_ = lean_nat_dec_lt(v___x_50_, v___x_52_);
lean_dec(v___x_52_);
if (v___x_53_ == 0)
{
lean_object* v___x_54_; 
lean_dec(v___x_50_);
v___x_54_ = lean_box(0);
return v___x_54_;
}
else
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_rotate(v_n_46_, v___x_50_);
lean_dec(v___x_50_);
v___x_56_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
return v___x_56_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instUpwardEnumerable___lam__1___boxed(lean_object* v_n_57_, lean_object* v_n_58_, lean_object* v_x_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instUpwardEnumerable___lam__1(v_n_57_, v_n_58_, v_x_59_);
lean_dec(v_x_59_);
lean_dec(v_n_58_);
lean_dec(v_n_57_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instUpwardEnumerable(lean_object* v_n_61_){
_start:
{
lean_object* v___f_62_; lean_object* v___f_63_; lean_object* v___x_64_; 
lean_inc(v_n_61_);
v___f_62_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instUpwardEnumerable___lam__0___boxed), 2, 1);
lean_closure_set(v___f_62_, 0, v_n_61_);
v___f_63_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instUpwardEnumerable___lam__1___boxed), 3, 1);
lean_closure_set(v___f_63_, 0, v_n_61_);
v___x_64_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_64_, 0, v___f_62_);
lean_ctor_set(v___x_64_, 1, v___f_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instLE___redArg(){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_box(0);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instLE___redArg___boxed(lean_object* v___dummy_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instLE___redArg();
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instLE(lean_object* v_n_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lean_box(0);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instLE___boxed(lean_object* v_n_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instLE(v_n_71_);
lean_dec(v_n_71_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instLT___redArg(){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_box(0);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instLT___redArg___boxed(lean_object* v___dummy_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instLT___redArg();
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instLT(lean_object* v_n_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_box(0);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instLT___boxed(lean_object* v_n_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instLT(v_n_79_);
lean_dec(v_n_79_);
return v_res_80_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instDecidableLE(lean_object* v_n_81_, lean_object* v_x_82_, lean_object* v_y_83_){
_start:
{
uint8_t v___x_84_; 
v___x_84_ = l_BitVec_sle(v_n_81_, v_x_82_, v_y_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instDecidableLE___boxed(lean_object* v_n_85_, lean_object* v_x_86_, lean_object* v_y_87_){
_start:
{
uint8_t v_res_88_; lean_object* v_r_89_; 
v_res_88_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instDecidableLE(v_n_85_, v_x_86_, v_y_87_);
lean_dec(v_n_85_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instDecidableLT(lean_object* v_n_90_, lean_object* v_x_91_, lean_object* v_y_92_){
_start:
{
uint8_t v___x_93_; 
v___x_93_ = l_BitVec_slt(v_n_90_, v_x_91_, v_y_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instDecidableLT___boxed(lean_object* v_n_94_, lean_object* v_x_95_, lean_object* v_y_96_){
_start:
{
uint8_t v_res_97_; lean_object* v_r_98_; 
v_res_97_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instDecidableLT(v_n_94_, v_x_95_, v_y_96_);
lean_dec(v_n_94_);
v_r_98_ = lean_box(v_res_97_);
return v_r_98_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxcHasSize___lam__0(lean_object* v_n_99_, lean_object* v_lo_100_, lean_object* v_hi_101_){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_102_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_rotate(v_n_99_, v_lo_100_);
v___x_103_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_rotate(v_n_99_, v_hi_101_);
v___x_104_ = lean_unsigned_to_nat(1u);
v___x_105_ = lean_nat_add(v___x_103_, v___x_104_);
lean_dec(v___x_103_);
v___x_106_ = lean_nat_sub(v___x_105_, v___x_102_);
lean_dec(v___x_102_);
lean_dec(v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxcHasSize___lam__0___boxed(lean_object* v_n_107_, lean_object* v_lo_108_, lean_object* v_hi_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxcHasSize___lam__0(v_n_107_, v_lo_108_, v_hi_109_);
lean_dec(v_hi_109_);
lean_dec(v_lo_108_);
lean_dec(v_n_107_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxcHasSize(lean_object* v_n_111_){
_start:
{
lean_object* v___f_112_; 
v___f_112_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxcHasSize___lam__0___boxed), 3, 1);
lean_closure_set(v___f_112_, 0, v_n_111_);
return v___f_112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxoHasSize___lam__0(lean_object* v_n_113_, lean_object* v_lo_114_, lean_object* v_hi_115_){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_116_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_rotate(v_n_113_, v_lo_114_);
v___x_117_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_rotate(v_n_113_, v_hi_115_);
v___x_118_ = lean_unsigned_to_nat(1u);
v___x_119_ = lean_nat_add(v___x_117_, v___x_118_);
lean_dec(v___x_117_);
v___x_120_ = lean_nat_sub(v___x_119_, v___x_116_);
lean_dec(v___x_116_);
lean_dec(v___x_119_);
v___x_121_ = lean_nat_sub(v___x_120_, v___x_118_);
lean_dec(v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxoHasSize___lam__0___boxed(lean_object* v_n_122_, lean_object* v_lo_123_, lean_object* v_hi_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxoHasSize___lam__0(v_n_122_, v_lo_123_, v_hi_124_);
lean_dec(v_hi_124_);
lean_dec(v_lo_123_);
lean_dec(v_n_122_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxoHasSize(lean_object* v_n_126_){
_start:
{
lean_object* v___f_127_; 
v___f_127_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxoHasSize___lam__0___boxed), 3, 1);
lean_closure_set(v___f_127_, 0, v_n_126_);
return v___f_127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxiHasSize___lam__0(lean_object* v_n_128_, lean_object* v_lo_129_){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_130_ = lean_unsigned_to_nat(2u);
v___x_131_ = lean_nat_pow(v___x_130_, v_n_128_);
v___x_132_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_rotate(v_n_128_, v_lo_129_);
v___x_133_ = lean_nat_sub(v___x_131_, v___x_132_);
lean_dec(v___x_132_);
lean_dec(v___x_131_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxiHasSize___lam__0___boxed(lean_object* v_n_134_, lean_object* v_lo_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxiHasSize___lam__0(v_n_134_, v_lo_135_);
lean_dec(v_lo_135_);
lean_dec(v_n_134_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxiHasSize(lean_object* v_n_137_){
_start:
{
lean_object* v___f_138_; 
v___f_138_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxiHasSize___lam__0___boxed), 2, 1);
lean_closure_set(v___f_138_, 0, v_n_137_);
return v___f_138_;
}
}
lean_object* runtime_initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_BitVec(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Internal_SignedBitVec(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Div_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Mod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Range_Polymorphic_Internal_SignedBitVec(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Div_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_BitVec(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Polymorphic_Internal_SignedBitVec(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Mod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Internal_SignedBitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Range_Polymorphic_Internal_SignedBitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Range_Polymorphic_Internal_SignedBitVec(builtin);
}
#ifdef __cplusplus
}
#endif
