// Lean compiler output
// Module: Init.Data.Float.Model.Unpacked.Round
// Imports: public import Init.Data.Float.Model.Unpacked.Basic public import Init.Data.Float.Model.Format.Basic public import Init.Data.Float.Model.Unpacked.Sign
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
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Float_Model_totalExponent(lean_object*, lean_object*);
lean_object* l_Float_Model_Format_targetExponent(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_ctorElim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_exact_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_exact_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_exact_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_exact_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_inexact_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_inexact_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_inexact_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_inexact_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_roundToNearestEven(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_roundToNearestEven___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Float_Model_UnpackedFloat_ExtendedMantissa_accuracy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_accuracy___closed__0 = (const lean_object*)&l_Float_Model_UnpackedFloat_ExtendedMantissa_accuracy___closed__0_value;
static const lean_ctor_object l_Float_Model_UnpackedFloat_ExtendedMantissa_accuracy___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_accuracy___closed__1 = (const lean_object*)&l_Float_Model_UnpackedFloat_ExtendedMantissa_accuracy___closed__1_value;
static const lean_ctor_object l_Float_Model_UnpackedFloat_ExtendedMantissa_accuracy___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_accuracy___closed__2 = (const lean_object*)&l_Float_Model_UnpackedFloat_ExtendedMantissa_accuracy___closed__2_value;
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_accuracy(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_accuracy___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_roundedMantissa(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_roundedMantissa___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_ofMantissaAndAccuracy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_ofMantissaAndAccuracy___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_shiftRightOne(lean_object*);
static const lean_closure_object l_Float_Model_UnpackedFloat_ExtendedMantissa_instHShiftRightNat___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_Model_UnpackedFloat_ExtendedMantissa_shiftRightOne, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_instHShiftRightNat___lam__0___closed__0 = (const lean_object*)&l_Float_Model_UnpackedFloat_ExtendedMantissa_instHShiftRightNat___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_instHShiftRightNat___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Float_Model_UnpackedFloat_ExtendedMantissa_instHShiftRightNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_Model_UnpackedFloat_ExtendedMantissa_instHShiftRightNat___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_instHShiftRightNat___closed__0 = (const lean_object*)&l_Float_Model_UnpackedFloat_ExtendedMantissa_instHShiftRightNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_instHShiftRightNat = (const lean_object*)&l_Float_Model_UnpackedFloat_ExtendedMantissa_instHShiftRightNat___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Float_Model_UnpackedFloat_shiftToExponent_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Float_Model_UnpackedFloat_shiftToExponent_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_shiftToExponent(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_shiftToExponent___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_shiftToTargetExponent(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_shiftToTargetExponent___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_roundWithAccuracy(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_roundWithAccuracy___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_decreaseExponent(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_decreaseExponent___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_round(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_round___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Float_Model_UnpackedFloat_normalize___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_normalize___closed__0;
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_normalize(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_normalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Float_Model_UnpackedFloat_Accuracy_ctorIdx(v_x_4_);
lean_dec(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
return v_k_7_;
}
else
{
uint8_t v_relativeToPlusOneHalfUlp_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v_relativeToPlusOneHalfUlp_8_ = lean_ctor_get_uint8(v_t_6_, 0);
v___x_9_ = lean_box(v_relativeToPlusOneHalfUlp_8_);
v___x_10_ = lean_apply_1(v_k_7_, v___x_9_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_ctorElim___redArg___boxed(lean_object* v_t_11_, lean_object* v_k_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Float_Model_UnpackedFloat_Accuracy_ctorElim___redArg(v_t_11_, v_k_12_);
lean_dec(v_t_11_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_ctorElim(lean_object* v_motive_14_, lean_object* v_ctorIdx_15_, lean_object* v_t_16_, lean_object* v_h_17_, lean_object* v_k_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Float_Model_UnpackedFloat_Accuracy_ctorElim___redArg(v_t_16_, v_k_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_ctorElim___boxed(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Float_Model_UnpackedFloat_Accuracy_ctorElim(v_motive_20_, v_ctorIdx_21_, v_t_22_, v_h_23_, v_k_24_);
lean_dec(v_t_22_);
lean_dec(v_ctorIdx_21_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_exact_elim___redArg(lean_object* v_t_26_, lean_object* v_exact_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Float_Model_UnpackedFloat_Accuracy_ctorElim___redArg(v_t_26_, v_exact_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_exact_elim___redArg___boxed(lean_object* v_t_29_, lean_object* v_exact_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Float_Model_UnpackedFloat_Accuracy_exact_elim___redArg(v_t_29_, v_exact_30_);
lean_dec(v_t_29_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_exact_elim(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_exact_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Float_Model_UnpackedFloat_Accuracy_ctorElim___redArg(v_t_33_, v_exact_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_exact_elim___boxed(lean_object* v_motive_37_, lean_object* v_t_38_, lean_object* v_h_39_, lean_object* v_exact_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Float_Model_UnpackedFloat_Accuracy_exact_elim(v_motive_37_, v_t_38_, v_h_39_, v_exact_40_);
lean_dec(v_t_38_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_inexact_elim___redArg(lean_object* v_t_42_, lean_object* v_inexact_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Float_Model_UnpackedFloat_Accuracy_ctorElim___redArg(v_t_42_, v_inexact_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_inexact_elim___redArg___boxed(lean_object* v_t_45_, lean_object* v_inexact_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Float_Model_UnpackedFloat_Accuracy_inexact_elim___redArg(v_t_45_, v_inexact_46_);
lean_dec(v_t_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_inexact_elim(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_inexact_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Float_Model_UnpackedFloat_Accuracy_ctorElim___redArg(v_t_49_, v_inexact_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_inexact_elim___boxed(lean_object* v_motive_53_, lean_object* v_t_54_, lean_object* v_h_55_, lean_object* v_inexact_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Float_Model_UnpackedFloat_Accuracy_inexact_elim(v_motive_53_, v_t_54_, v_h_55_, v_inexact_56_);
lean_dec(v_t_54_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_roundToNearestEven(lean_object* v_mantissa_58_, lean_object* v_x_59_){
_start:
{
if (lean_obj_tag(v_x_59_) == 0)
{
lean_inc(v_mantissa_58_);
return v_mantissa_58_;
}
else
{
uint8_t v_relativeToPlusOneHalfUlp_60_; 
v_relativeToPlusOneHalfUlp_60_ = lean_ctor_get_uint8(v_x_59_, 0);
switch(v_relativeToPlusOneHalfUlp_60_)
{
case 0:
{
lean_inc(v_mantissa_58_);
return v_mantissa_58_;
}
case 1:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = lean_unsigned_to_nat(2u);
v___x_62_ = lean_nat_mod(v_mantissa_58_, v___x_61_);
v___x_63_ = lean_nat_add(v_mantissa_58_, v___x_62_);
lean_dec(v___x_62_);
return v___x_63_;
}
default: 
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = lean_unsigned_to_nat(1u);
v___x_65_ = lean_nat_add(v_mantissa_58_, v___x_64_);
return v___x_65_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_roundToNearestEven___boxed(lean_object* v_mantissa_66_, lean_object* v_x_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Float_Model_UnpackedFloat_Accuracy_roundToNearestEven(v_mantissa_66_, v_x_67_);
lean_dec(v_x_67_);
lean_dec(v_mantissa_66_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_accuracy(lean_object* v_x_75_){
_start:
{
uint8_t v_roundBit_76_; 
v_roundBit_76_ = lean_ctor_get_uint8(v_x_75_, sizeof(void*)*1);
if (v_roundBit_76_ == 0)
{
uint8_t v_stickyBit_77_; 
v_stickyBit_77_ = lean_ctor_get_uint8(v_x_75_, sizeof(void*)*1 + 1);
if (v_stickyBit_77_ == 0)
{
lean_object* v___x_78_; 
v___x_78_ = lean_box(0);
return v___x_78_;
}
else
{
lean_object* v___x_79_; 
v___x_79_ = ((lean_object*)(l_Float_Model_UnpackedFloat_ExtendedMantissa_accuracy___closed__0));
return v___x_79_;
}
}
else
{
uint8_t v_stickyBit_80_; 
v_stickyBit_80_ = lean_ctor_get_uint8(v_x_75_, sizeof(void*)*1 + 1);
if (v_stickyBit_80_ == 0)
{
lean_object* v___x_81_; 
v___x_81_ = ((lean_object*)(l_Float_Model_UnpackedFloat_ExtendedMantissa_accuracy___closed__1));
return v___x_81_;
}
else
{
lean_object* v___x_82_; 
v___x_82_ = ((lean_object*)(l_Float_Model_UnpackedFloat_ExtendedMantissa_accuracy___closed__2));
return v___x_82_;
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_accuracy___boxed(lean_object* v_x_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Float_Model_UnpackedFloat_ExtendedMantissa_accuracy(v_x_83_);
lean_dec_ref(v_x_83_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_roundedMantissa(lean_object* v_em_85_){
_start:
{
lean_object* v_mantissa_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v_mantissa_86_ = lean_ctor_get(v_em_85_, 0);
v___x_87_ = l_Float_Model_UnpackedFloat_ExtendedMantissa_accuracy(v_em_85_);
v___x_88_ = l_Float_Model_UnpackedFloat_Accuracy_roundToNearestEven(v_mantissa_86_, v___x_87_);
lean_dec(v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_roundedMantissa___boxed(lean_object* v_em_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Float_Model_UnpackedFloat_ExtendedMantissa_roundedMantissa(v_em_89_);
lean_dec_ref(v_em_89_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_ofMantissaAndAccuracy(lean_object* v_mantissa_91_, lean_object* v_accuracy_92_){
_start:
{
if (lean_obj_tag(v_accuracy_92_) == 0)
{
uint8_t v___x_93_; lean_object* v___x_94_; 
v___x_93_ = 0;
v___x_94_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_94_, 0, v_mantissa_91_);
lean_ctor_set_uint8(v___x_94_, sizeof(void*)*1, v___x_93_);
lean_ctor_set_uint8(v___x_94_, sizeof(void*)*1 + 1, v___x_93_);
return v___x_94_;
}
else
{
uint8_t v_relativeToPlusOneHalfUlp_95_; 
v_relativeToPlusOneHalfUlp_95_ = lean_ctor_get_uint8(v_accuracy_92_, 0);
switch(v_relativeToPlusOneHalfUlp_95_)
{
case 0:
{
uint8_t v___x_96_; uint8_t v___x_97_; lean_object* v___x_98_; 
v___x_96_ = 0;
v___x_97_ = 1;
v___x_98_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_98_, 0, v_mantissa_91_);
lean_ctor_set_uint8(v___x_98_, sizeof(void*)*1, v___x_96_);
lean_ctor_set_uint8(v___x_98_, sizeof(void*)*1 + 1, v___x_97_);
return v___x_98_;
}
case 1:
{
uint8_t v___x_99_; uint8_t v___x_100_; lean_object* v___x_101_; 
v___x_99_ = 1;
v___x_100_ = 0;
v___x_101_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_101_, 0, v_mantissa_91_);
lean_ctor_set_uint8(v___x_101_, sizeof(void*)*1, v___x_99_);
lean_ctor_set_uint8(v___x_101_, sizeof(void*)*1 + 1, v___x_100_);
return v___x_101_;
}
default: 
{
uint8_t v___x_102_; lean_object* v___x_103_; 
v___x_102_ = 1;
v___x_103_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_103_, 0, v_mantissa_91_);
lean_ctor_set_uint8(v___x_103_, sizeof(void*)*1, v___x_102_);
lean_ctor_set_uint8(v___x_103_, sizeof(void*)*1 + 1, v___x_102_);
return v___x_103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_ofMantissaAndAccuracy___boxed(lean_object* v_mantissa_104_, lean_object* v_accuracy_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Float_Model_UnpackedFloat_ExtendedMantissa_ofMantissaAndAccuracy(v_mantissa_104_, v_accuracy_105_);
lean_dec(v_accuracy_105_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_shiftRightOne(lean_object* v_em_107_){
_start:
{
lean_object* v_mantissa_108_; uint8_t v_roundBit_109_; uint8_t v_stickyBit_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_130_; 
v_mantissa_108_ = lean_ctor_get(v_em_107_, 0);
v_roundBit_109_ = lean_ctor_get_uint8(v_em_107_, sizeof(void*)*1);
v_stickyBit_110_ = lean_ctor_get_uint8(v_em_107_, sizeof(void*)*1 + 1);
v_isSharedCheck_130_ = !lean_is_exclusive(v_em_107_);
if (v_isSharedCheck_130_ == 0)
{
v___x_112_ = v_em_107_;
v_isShared_113_ = v_isSharedCheck_130_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_mantissa_108_);
lean_dec(v_em_107_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_130_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___y_118_; lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_114_ = lean_unsigned_to_nat(2u);
v___x_115_ = lean_unsigned_to_nat(1u);
v___x_116_ = lean_nat_shiftr(v_mantissa_108_, v___x_115_);
v___x_125_ = lean_nat_mod(v_mantissa_108_, v___x_114_);
lean_dec(v_mantissa_108_);
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_nat_dec_eq(v___x_125_, v___x_126_);
lean_dec(v___x_125_);
if (v___x_127_ == 0)
{
uint8_t v___x_128_; 
v___x_128_ = 1;
v___y_118_ = v___x_128_;
goto v___jp_117_;
}
else
{
uint8_t v___x_129_; 
v___x_129_ = 0;
v___y_118_ = v___x_129_;
goto v___jp_117_;
}
v___jp_117_:
{
if (v_roundBit_109_ == 0)
{
lean_object* v___x_120_; 
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 0, v___x_116_);
v___x_120_ = v___x_112_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_116_);
lean_ctor_set_uint8(v_reuseFailAlloc_121_, sizeof(void*)*1 + 1, v_stickyBit_110_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
lean_ctor_set_uint8(v___x_120_, sizeof(void*)*1, v___y_118_);
return v___x_120_;
}
}
else
{
lean_object* v___x_123_; 
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 0, v___x_116_);
v___x_123_ = v___x_112_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_116_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
lean_ctor_set_uint8(v___x_123_, sizeof(void*)*1, v___y_118_);
lean_ctor_set_uint8(v___x_123_, sizeof(void*)*1 + 1, v_roundBit_109_);
return v___x_123_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_instHShiftRightNat___lam__0(lean_object* v_em_132_, lean_object* v_n_133_){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = ((lean_object*)(l_Float_Model_UnpackedFloat_ExtendedMantissa_instHShiftRightNat___lam__0___closed__0));
v___x_135_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___x_134_, v_n_133_, v_em_132_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Float_Model_UnpackedFloat_shiftToExponent_spec__1(lean_object* v_a_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = lean_nat_to_int(v_a_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Float_Model_UnpackedFloat_shiftToExponent_spec__0(lean_object* v_x_140_, lean_object* v_x_141_){
_start:
{
lean_object* v_zero_142_; uint8_t v_isZero_143_; 
v_zero_142_ = lean_unsigned_to_nat(0u);
v_isZero_143_ = lean_nat_dec_eq(v_x_140_, v_zero_142_);
if (v_isZero_143_ == 1)
{
lean_dec(v_x_140_);
return v_x_141_;
}
else
{
lean_object* v_one_144_; lean_object* v_n_145_; lean_object* v___x_146_; 
v_one_144_ = lean_unsigned_to_nat(1u);
v_n_145_ = lean_nat_sub(v_x_140_, v_one_144_);
lean_dec(v_x_140_);
v___x_146_ = l_Float_Model_UnpackedFloat_ExtendedMantissa_shiftRightOne(v_x_141_);
v_x_140_ = v_n_145_;
v_x_141_ = v___x_146_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_shiftToExponent(lean_object* v_mantissa_148_, lean_object* v_exponent_149_, lean_object* v_accuracy_150_, lean_object* v_targetExponent_151_){
_start:
{
lean_object* v___x_152_; lean_object* v_shiftAmount_153_; lean_object* v_initialExtendedMantissa_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_152_ = lean_int_sub(v_targetExponent_151_, v_exponent_149_);
v_shiftAmount_153_ = l_Int_toNat(v___x_152_);
lean_dec(v___x_152_);
v_initialExtendedMantissa_154_ = l_Float_Model_UnpackedFloat_ExtendedMantissa_ofMantissaAndAccuracy(v_mantissa_148_, v_accuracy_150_);
lean_inc(v_shiftAmount_153_);
v___x_155_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Float_Model_UnpackedFloat_shiftToExponent_spec__0(v_shiftAmount_153_, v_initialExtendedMantissa_154_);
v___x_156_ = lean_nat_to_int(v_shiftAmount_153_);
v___x_157_ = lean_int_add(v_exponent_149_, v___x_156_);
lean_dec(v___x_156_);
v___x_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_155_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_shiftToExponent___boxed(lean_object* v_mantissa_159_, lean_object* v_exponent_160_, lean_object* v_accuracy_161_, lean_object* v_targetExponent_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Float_Model_UnpackedFloat_shiftToExponent(v_mantissa_159_, v_exponent_160_, v_accuracy_161_, v_targetExponent_162_);
lean_dec(v_targetExponent_162_);
lean_dec(v_accuracy_161_);
lean_dec(v_exponent_160_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_shiftToTargetExponent(lean_object* v_spec_164_, lean_object* v_mantissa_165_, lean_object* v_exponent_166_, lean_object* v_accuracy_167_){
_start:
{
lean_object* v___x_168_; lean_object* v_targetExponent_169_; lean_object* v___x_170_; 
v___x_168_ = l_Float_Model_totalExponent(v_mantissa_165_, v_exponent_166_);
v_targetExponent_169_ = l_Float_Model_Format_targetExponent(v_spec_164_, v___x_168_);
lean_dec(v___x_168_);
v___x_170_ = l_Float_Model_UnpackedFloat_shiftToExponent(v_mantissa_165_, v_exponent_166_, v_accuracy_167_, v_targetExponent_169_);
lean_dec(v_targetExponent_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_shiftToTargetExponent___boxed(lean_object* v_spec_171_, lean_object* v_mantissa_172_, lean_object* v_exponent_173_, lean_object* v_accuracy_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Float_Model_UnpackedFloat_shiftToTargetExponent(v_spec_171_, v_mantissa_172_, v_exponent_173_, v_accuracy_174_);
lean_dec(v_accuracy_174_);
lean_dec(v_exponent_173_);
lean_dec_ref(v_spec_171_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_roundWithAccuracy(lean_object* v_spec_176_, uint8_t v_sign_177_, lean_object* v_mantissa_178_, lean_object* v_exponent_179_, lean_object* v_accuracy_180_){
_start:
{
lean_object* v___x_181_; lean_object* v_fst_182_; lean_object* v_snd_183_; lean_object* v_roundedEm_u2081_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v_fst_187_; lean_object* v_snd_188_; lean_object* v_mantissa_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v___x_181_ = l_Float_Model_UnpackedFloat_shiftToTargetExponent(v_spec_176_, v_mantissa_178_, v_exponent_179_, v_accuracy_180_);
v_fst_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_fst_182_);
v_snd_183_ = lean_ctor_get(v___x_181_, 1);
lean_inc(v_snd_183_);
lean_dec_ref(v___x_181_);
v_roundedEm_u2081_184_ = l_Float_Model_UnpackedFloat_ExtendedMantissa_roundedMantissa(v_fst_182_);
lean_dec(v_fst_182_);
v___x_185_ = lean_box(0);
v___x_186_ = l_Float_Model_UnpackedFloat_shiftToTargetExponent(v_spec_176_, v_roundedEm_u2081_184_, v_snd_183_, v___x_185_);
lean_dec(v_snd_183_);
v_fst_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_fst_187_);
v_snd_188_ = lean_ctor_get(v___x_186_, 1);
lean_inc(v_snd_188_);
lean_dec_ref(v___x_186_);
v_mantissa_189_ = lean_ctor_get(v_fst_187_, 0);
lean_inc(v_mantissa_189_);
lean_dec(v_fst_187_);
v___x_190_ = lean_unsigned_to_nat(0u);
v___x_191_ = lean_nat_dec_eq(v_mantissa_189_, v___x_190_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; 
v___x_192_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_192_, 0, v_mantissa_189_);
lean_ctor_set(v___x_192_, 1, v_snd_188_);
lean_ctor_set_uint8(v___x_192_, sizeof(void*)*2, v_sign_177_);
return v___x_192_;
}
else
{
lean_object* v___x_193_; 
lean_dec(v_mantissa_189_);
lean_dec(v_snd_188_);
v___x_193_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_193_, 0, v_sign_177_);
return v___x_193_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_roundWithAccuracy___boxed(lean_object* v_spec_194_, lean_object* v_sign_195_, lean_object* v_mantissa_196_, lean_object* v_exponent_197_, lean_object* v_accuracy_198_){
_start:
{
uint8_t v_sign_boxed_199_; lean_object* v_res_200_; 
v_sign_boxed_199_ = lean_unbox(v_sign_195_);
v_res_200_ = l_Float_Model_UnpackedFloat_roundWithAccuracy(v_spec_194_, v_sign_boxed_199_, v_mantissa_196_, v_exponent_197_, v_accuracy_198_);
lean_dec(v_accuracy_198_);
lean_dec(v_exponent_197_);
lean_dec_ref(v_spec_194_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_decreaseExponent(lean_object* v_mantissa_201_, lean_object* v_exponent_202_, lean_object* v_targetExponent_203_){
_start:
{
lean_object* v___x_204_; lean_object* v_shiftAmount_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_204_ = lean_int_sub(v_exponent_202_, v_targetExponent_203_);
v_shiftAmount_205_ = l_Int_toNat(v___x_204_);
lean_dec(v___x_204_);
v___x_206_ = lean_nat_shiftl(v_mantissa_201_, v_shiftAmount_205_);
v___x_207_ = lean_nat_to_int(v_shiftAmount_205_);
v___x_208_ = lean_int_sub(v_exponent_202_, v___x_207_);
lean_dec(v___x_207_);
v___x_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_206_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_decreaseExponent___boxed(lean_object* v_mantissa_210_, lean_object* v_exponent_211_, lean_object* v_targetExponent_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Float_Model_UnpackedFloat_decreaseExponent(v_mantissa_210_, v_exponent_211_, v_targetExponent_212_);
lean_dec(v_targetExponent_212_);
lean_dec(v_exponent_211_);
lean_dec(v_mantissa_210_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_round(lean_object* v_spec_214_, uint8_t v_sign_215_, lean_object* v_mantissa_216_, lean_object* v_exponent_217_){
_start:
{
lean_object* v___x_218_; lean_object* v_targetExponent_219_; lean_object* v___x_220_; lean_object* v_fst_221_; lean_object* v_snd_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_218_ = l_Float_Model_totalExponent(v_mantissa_216_, v_exponent_217_);
v_targetExponent_219_ = l_Float_Model_Format_targetExponent(v_spec_214_, v___x_218_);
lean_dec(v___x_218_);
v___x_220_ = l_Float_Model_UnpackedFloat_decreaseExponent(v_mantissa_216_, v_exponent_217_, v_targetExponent_219_);
lean_dec(v_targetExponent_219_);
v_fst_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_fst_221_);
v_snd_222_ = lean_ctor_get(v___x_220_, 1);
lean_inc(v_snd_222_);
lean_dec_ref(v___x_220_);
v___x_223_ = lean_box(0);
v___x_224_ = l_Float_Model_UnpackedFloat_roundWithAccuracy(v_spec_214_, v_sign_215_, v_fst_221_, v_snd_222_, v___x_223_);
lean_dec(v_snd_222_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_round___boxed(lean_object* v_spec_225_, lean_object* v_sign_226_, lean_object* v_mantissa_227_, lean_object* v_exponent_228_){
_start:
{
uint8_t v_sign_boxed_229_; lean_object* v_res_230_; 
v_sign_boxed_229_ = lean_unbox(v_sign_226_);
v_res_230_ = l_Float_Model_UnpackedFloat_round(v_spec_225_, v_sign_boxed_229_, v_mantissa_227_, v_exponent_228_);
lean_dec(v_exponent_228_);
lean_dec(v_mantissa_227_);
lean_dec_ref(v_spec_225_);
return v_res_230_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_normalize___closed__0(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = lean_nat_to_int(v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_normalize(lean_object* v_spec_233_, lean_object* v_mantissa_234_, lean_object* v_exponent_235_, uint8_t v_zeroSign_236_){
_start:
{
lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_237_ = lean_obj_once(&l_Float_Model_UnpackedFloat_normalize___closed__0, &l_Float_Model_UnpackedFloat_normalize___closed__0_once, _init_l_Float_Model_UnpackedFloat_normalize___closed__0);
v___x_238_ = lean_int_dec_lt(v_mantissa_234_, v___x_237_);
if (v___x_238_ == 0)
{
uint8_t v___x_239_; 
v___x_239_ = lean_int_dec_eq(v_mantissa_234_, v___x_237_);
if (v___x_239_ == 0)
{
uint8_t v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_240_ = 1;
v___x_241_ = l_Int_toNat(v_mantissa_234_);
v___x_242_ = l_Float_Model_UnpackedFloat_round(v_spec_233_, v___x_240_, v___x_241_, v_exponent_235_);
lean_dec(v___x_241_);
return v___x_242_;
}
else
{
lean_object* v___x_243_; 
v___x_243_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_243_, 0, v_zeroSign_236_);
return v___x_243_;
}
}
else
{
uint8_t v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_244_ = 0;
v___x_245_ = lean_int_neg(v_mantissa_234_);
v___x_246_ = l_Int_toNat(v___x_245_);
lean_dec(v___x_245_);
v___x_247_ = l_Float_Model_UnpackedFloat_round(v_spec_233_, v___x_244_, v___x_246_, v_exponent_235_);
lean_dec(v___x_246_);
return v___x_247_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_normalize___boxed(lean_object* v_spec_248_, lean_object* v_mantissa_249_, lean_object* v_exponent_250_, lean_object* v_zeroSign_251_){
_start:
{
uint8_t v_zeroSign_boxed_252_; lean_object* v_res_253_; 
v_zeroSign_boxed_252_ = lean_unbox(v_zeroSign_251_);
v_res_253_ = l_Float_Model_UnpackedFloat_normalize(v_spec_248_, v_mantissa_249_, v_exponent_250_, v_zeroSign_boxed_252_);
lean_dec(v_exponent_250_);
lean_dec(v_mantissa_249_);
lean_dec_ref(v_spec_248_);
return v_res_253_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Float_Model_Format_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Sign(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Round(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Model_Format_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Sign(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Float_Model_Unpacked_Round(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Float_Model_Unpacked_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Float_Model_Format_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Float_Model_Unpacked_Sign(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Float_Model_Unpacked_Round(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float_Model_Unpacked_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Float_Model_Format_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Float_Model_Unpacked_Sign(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Round(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Float_Model_Unpacked_Round(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Float_Model_Unpacked_Round(builtin);
}
#ifdef __cplusplus
}
#endif
