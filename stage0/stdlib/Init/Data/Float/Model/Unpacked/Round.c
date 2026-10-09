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
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Float_Model_totalExponent(lean_object*, lean_object*);
lean_object* l_Float_Model_Format_targetExponent(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Float_Model_UnpackedFloat_Accuracy_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
return v_k_6_;
}
else
{
uint8_t v_relativeToPlusOneHalfUlp_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_relativeToPlusOneHalfUlp_7_ = lean_ctor_get_uint8(v_t_5_, 0);
v___x_8_ = lean_box(v_relativeToPlusOneHalfUlp_7_);
v___x_9_ = lean_apply_1(v_k_6_, v___x_8_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_ctorElim___redArg___boxed(lean_object* v_t_10_, lean_object* v_k_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Float_Model_UnpackedFloat_Accuracy_ctorElim___redArg(v_t_10_, v_k_11_);
lean_dec(v_t_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_ctorElim(lean_object* v_motive_13_, lean_object* v_ctorIdx_14_, lean_object* v_t_15_, lean_object* v_h_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Float_Model_UnpackedFloat_Accuracy_ctorElim___redArg(v_t_15_, v_k_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Float_Model_UnpackedFloat_Accuracy_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_21_, v_h_22_, v_k_23_);
lean_dec(v_t_21_);
lean_dec(v_ctorIdx_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_exact_elim___redArg(lean_object* v_t_25_, lean_object* v_exact_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Float_Model_UnpackedFloat_Accuracy_ctorElim___redArg(v_t_25_, v_exact_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_exact_elim___redArg___boxed(lean_object* v_t_28_, lean_object* v_exact_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Float_Model_UnpackedFloat_Accuracy_exact_elim___redArg(v_t_28_, v_exact_29_);
lean_dec(v_t_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_exact_elim(lean_object* v_motive_31_, lean_object* v_t_32_, lean_object* v_h_33_, lean_object* v_exact_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Float_Model_UnpackedFloat_Accuracy_ctorElim___redArg(v_t_32_, v_exact_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_exact_elim___boxed(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_exact_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Float_Model_UnpackedFloat_Accuracy_exact_elim(v_motive_36_, v_t_37_, v_h_38_, v_exact_39_);
lean_dec(v_t_37_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_inexact_elim___redArg(lean_object* v_t_41_, lean_object* v_inexact_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Float_Model_UnpackedFloat_Accuracy_ctorElim___redArg(v_t_41_, v_inexact_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_inexact_elim___redArg___boxed(lean_object* v_t_44_, lean_object* v_inexact_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Float_Model_UnpackedFloat_Accuracy_inexact_elim___redArg(v_t_44_, v_inexact_45_);
lean_dec(v_t_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_inexact_elim(lean_object* v_motive_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_inexact_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Float_Model_UnpackedFloat_Accuracy_ctorElim___redArg(v_t_48_, v_inexact_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_inexact_elim___boxed(lean_object* v_motive_52_, lean_object* v_t_53_, lean_object* v_h_54_, lean_object* v_inexact_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Float_Model_UnpackedFloat_Accuracy_inexact_elim(v_motive_52_, v_t_53_, v_h_54_, v_inexact_55_);
lean_dec(v_t_53_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_roundToNearestEven(lean_object* v_mantissa_57_, lean_object* v_x_58_){
_start:
{
if (lean_obj_tag(v_x_58_) == 0)
{
lean_inc(v_mantissa_57_);
return v_mantissa_57_;
}
else
{
uint8_t v_relativeToPlusOneHalfUlp_59_; 
v_relativeToPlusOneHalfUlp_59_ = lean_ctor_get_uint8(v_x_58_, 0);
switch(v_relativeToPlusOneHalfUlp_59_)
{
case 0:
{
lean_inc(v_mantissa_57_);
return v_mantissa_57_;
}
case 1:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_unsigned_to_nat(2u);
v___x_61_ = lean_nat_mod(v_mantissa_57_, v___x_60_);
v___x_62_ = lean_nat_add(v_mantissa_57_, v___x_61_);
lean_dec(v___x_61_);
return v___x_62_;
}
default: 
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = lean_unsigned_to_nat(1u);
v___x_64_ = lean_nat_add(v_mantissa_57_, v___x_63_);
return v___x_64_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_Accuracy_roundToNearestEven___boxed(lean_object* v_mantissa_65_, lean_object* v_x_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Float_Model_UnpackedFloat_Accuracy_roundToNearestEven(v_mantissa_65_, v_x_66_);
lean_dec(v_x_66_);
lean_dec(v_mantissa_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_accuracy(lean_object* v_x_74_){
_start:
{
uint8_t v_roundBit_75_; 
v_roundBit_75_ = lean_ctor_get_uint8(v_x_74_, sizeof(void*)*1);
if (v_roundBit_75_ == 0)
{
uint8_t v_stickyBit_76_; 
v_stickyBit_76_ = lean_ctor_get_uint8(v_x_74_, sizeof(void*)*1 + 1);
if (v_stickyBit_76_ == 0)
{
lean_object* v___x_77_; 
v___x_77_ = lean_box(0);
return v___x_77_;
}
else
{
lean_object* v___x_78_; 
v___x_78_ = ((lean_object*)(l_Float_Model_UnpackedFloat_ExtendedMantissa_accuracy___closed__0));
return v___x_78_;
}
}
else
{
uint8_t v_stickyBit_79_; 
v_stickyBit_79_ = lean_ctor_get_uint8(v_x_74_, sizeof(void*)*1 + 1);
if (v_stickyBit_79_ == 0)
{
lean_object* v___x_80_; 
v___x_80_ = ((lean_object*)(l_Float_Model_UnpackedFloat_ExtendedMantissa_accuracy___closed__1));
return v___x_80_;
}
else
{
lean_object* v___x_81_; 
v___x_81_ = ((lean_object*)(l_Float_Model_UnpackedFloat_ExtendedMantissa_accuracy___closed__2));
return v___x_81_;
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_accuracy___boxed(lean_object* v_x_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Float_Model_UnpackedFloat_ExtendedMantissa_accuracy(v_x_82_);
lean_dec_ref(v_x_82_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_roundedMantissa(lean_object* v_em_84_){
_start:
{
lean_object* v_mantissa_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v_mantissa_85_ = lean_ctor_get(v_em_84_, 0);
v___x_86_ = l_Float_Model_UnpackedFloat_ExtendedMantissa_accuracy(v_em_84_);
v___x_87_ = l_Float_Model_UnpackedFloat_Accuracy_roundToNearestEven(v_mantissa_85_, v___x_86_);
lean_dec(v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_roundedMantissa___boxed(lean_object* v_em_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Float_Model_UnpackedFloat_ExtendedMantissa_roundedMantissa(v_em_88_);
lean_dec_ref(v_em_88_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_ofMantissaAndAccuracy(lean_object* v_mantissa_90_, lean_object* v_accuracy_91_){
_start:
{
if (lean_obj_tag(v_accuracy_91_) == 0)
{
uint8_t v___x_92_; lean_object* v___x_93_; 
v___x_92_ = 0;
v___x_93_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_93_, 0, v_mantissa_90_);
lean_ctor_set_uint8(v___x_93_, sizeof(void*)*1, v___x_92_);
lean_ctor_set_uint8(v___x_93_, sizeof(void*)*1 + 1, v___x_92_);
return v___x_93_;
}
else
{
uint8_t v_relativeToPlusOneHalfUlp_94_; 
v_relativeToPlusOneHalfUlp_94_ = lean_ctor_get_uint8(v_accuracy_91_, 0);
switch(v_relativeToPlusOneHalfUlp_94_)
{
case 0:
{
uint8_t v___x_95_; uint8_t v___x_96_; lean_object* v___x_97_; 
v___x_95_ = 0;
v___x_96_ = 1;
v___x_97_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_97_, 0, v_mantissa_90_);
lean_ctor_set_uint8(v___x_97_, sizeof(void*)*1, v___x_95_);
lean_ctor_set_uint8(v___x_97_, sizeof(void*)*1 + 1, v___x_96_);
return v___x_97_;
}
case 1:
{
uint8_t v___x_98_; uint8_t v___x_99_; lean_object* v___x_100_; 
v___x_98_ = 1;
v___x_99_ = 0;
v___x_100_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_100_, 0, v_mantissa_90_);
lean_ctor_set_uint8(v___x_100_, sizeof(void*)*1, v___x_98_);
lean_ctor_set_uint8(v___x_100_, sizeof(void*)*1 + 1, v___x_99_);
return v___x_100_;
}
default: 
{
uint8_t v___x_101_; lean_object* v___x_102_; 
v___x_101_ = 1;
v___x_102_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_102_, 0, v_mantissa_90_);
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*1, v___x_101_);
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*1 + 1, v___x_101_);
return v___x_102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_ofMantissaAndAccuracy___boxed(lean_object* v_mantissa_103_, lean_object* v_accuracy_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Float_Model_UnpackedFloat_ExtendedMantissa_ofMantissaAndAccuracy(v_mantissa_103_, v_accuracy_104_);
lean_dec(v_accuracy_104_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_shiftRightOne(lean_object* v_em_106_){
_start:
{
lean_object* v_mantissa_107_; uint8_t v_roundBit_108_; uint8_t v_stickyBit_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_129_; 
v_mantissa_107_ = lean_ctor_get(v_em_106_, 0);
v_roundBit_108_ = lean_ctor_get_uint8(v_em_106_, sizeof(void*)*1);
v_stickyBit_109_ = lean_ctor_get_uint8(v_em_106_, sizeof(void*)*1 + 1);
v_isSharedCheck_129_ = !lean_is_exclusive(v_em_106_);
if (v_isSharedCheck_129_ == 0)
{
v___x_111_ = v_em_106_;
v_isShared_112_ = v_isSharedCheck_129_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_mantissa_107_);
lean_dec(v_em_106_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_129_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; uint8_t v___y_117_; lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_113_ = lean_unsigned_to_nat(2u);
v___x_114_ = lean_unsigned_to_nat(1u);
v___x_115_ = lean_nat_shiftr(v_mantissa_107_, v___x_114_);
v___x_124_ = lean_nat_mod(v_mantissa_107_, v___x_113_);
lean_dec(v_mantissa_107_);
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = lean_nat_dec_eq(v___x_124_, v___x_125_);
lean_dec(v___x_124_);
if (v___x_126_ == 0)
{
uint8_t v___x_127_; 
v___x_127_ = 1;
v___y_117_ = v___x_127_;
goto v___jp_116_;
}
else
{
uint8_t v___x_128_; 
v___x_128_ = 0;
v___y_117_ = v___x_128_;
goto v___jp_116_;
}
v___jp_116_:
{
if (v_roundBit_108_ == 0)
{
lean_object* v___x_119_; 
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_115_);
v___x_119_ = v___x_111_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_115_);
lean_ctor_set_uint8(v_reuseFailAlloc_120_, sizeof(void*)*1 + 1, v_stickyBit_109_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
lean_ctor_set_uint8(v___x_119_, sizeof(void*)*1, v___y_117_);
return v___x_119_;
}
}
else
{
lean_object* v___x_122_; 
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_115_);
v___x_122_ = v___x_111_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_115_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
lean_ctor_set_uint8(v___x_122_, sizeof(void*)*1, v___y_117_);
lean_ctor_set_uint8(v___x_122_, sizeof(void*)*1 + 1, v_roundBit_108_);
return v___x_122_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ExtendedMantissa_instHShiftRightNat___lam__0(lean_object* v_em_131_, lean_object* v_n_132_){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = ((lean_object*)(l_Float_Model_UnpackedFloat_ExtendedMantissa_instHShiftRightNat___lam__0___closed__0));
v___x_134_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(lean_box(0), v___x_133_, v_n_132_, v_em_131_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Float_Model_UnpackedFloat_shiftToExponent_spec__1(lean_object* v_a_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = lean_nat_to_int(v_a_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Float_Model_UnpackedFloat_shiftToExponent_spec__0(lean_object* v_x_139_, lean_object* v_x_140_){
_start:
{
lean_object* v_zero_141_; uint8_t v_isZero_142_; 
v_zero_141_ = lean_unsigned_to_nat(0u);
v_isZero_142_ = lean_nat_dec_eq(v_x_139_, v_zero_141_);
if (v_isZero_142_ == 1)
{
lean_dec(v_x_139_);
return v_x_140_;
}
else
{
lean_object* v_one_143_; lean_object* v_n_144_; lean_object* v___x_145_; 
v_one_143_ = lean_unsigned_to_nat(1u);
v_n_144_ = lean_nat_sub(v_x_139_, v_one_143_);
lean_dec(v_x_139_);
v___x_145_ = l_Float_Model_UnpackedFloat_ExtendedMantissa_shiftRightOne(v_x_140_);
v_x_139_ = v_n_144_;
v_x_140_ = v___x_145_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_shiftToExponent(lean_object* v_mantissa_147_, lean_object* v_exponent_148_, lean_object* v_accuracy_149_, lean_object* v_targetExponent_150_){
_start:
{
lean_object* v___x_151_; lean_object* v_shiftAmount_152_; lean_object* v_initialExtendedMantissa_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_151_ = lean_int_sub(v_targetExponent_150_, v_exponent_148_);
v_shiftAmount_152_ = l_Int_toNat(v___x_151_);
lean_dec(v___x_151_);
v_initialExtendedMantissa_153_ = l_Float_Model_UnpackedFloat_ExtendedMantissa_ofMantissaAndAccuracy(v_mantissa_147_, v_accuracy_149_);
lean_inc(v_shiftAmount_152_);
v___x_154_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Float_Model_UnpackedFloat_shiftToExponent_spec__0(v_shiftAmount_152_, v_initialExtendedMantissa_153_);
v___x_155_ = lean_nat_to_int(v_shiftAmount_152_);
v___x_156_ = lean_int_add(v_exponent_148_, v___x_155_);
lean_dec(v___x_155_);
v___x_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_154_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_shiftToExponent___boxed(lean_object* v_mantissa_158_, lean_object* v_exponent_159_, lean_object* v_accuracy_160_, lean_object* v_targetExponent_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Float_Model_UnpackedFloat_shiftToExponent(v_mantissa_158_, v_exponent_159_, v_accuracy_160_, v_targetExponent_161_);
lean_dec(v_targetExponent_161_);
lean_dec(v_accuracy_160_);
lean_dec(v_exponent_159_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_shiftToTargetExponent(lean_object* v_spec_163_, lean_object* v_mantissa_164_, lean_object* v_exponent_165_, lean_object* v_accuracy_166_){
_start:
{
lean_object* v___x_167_; lean_object* v_targetExponent_168_; lean_object* v___x_169_; 
v___x_167_ = l_Float_Model_totalExponent(v_mantissa_164_, v_exponent_165_);
v_targetExponent_168_ = l_Float_Model_Format_targetExponent(v_spec_163_, v___x_167_);
lean_dec(v___x_167_);
v___x_169_ = l_Float_Model_UnpackedFloat_shiftToExponent(v_mantissa_164_, v_exponent_165_, v_accuracy_166_, v_targetExponent_168_);
lean_dec(v_targetExponent_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_shiftToTargetExponent___boxed(lean_object* v_spec_170_, lean_object* v_mantissa_171_, lean_object* v_exponent_172_, lean_object* v_accuracy_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Float_Model_UnpackedFloat_shiftToTargetExponent(v_spec_170_, v_mantissa_171_, v_exponent_172_, v_accuracy_173_);
lean_dec(v_accuracy_173_);
lean_dec(v_exponent_172_);
lean_dec_ref(v_spec_170_);
return v_res_174_;
}
}
lean_object* l_Float_Model_UnpackedFloat_roundWithAccuracy(lean_object* v_spec_175_, uint8_t v_sign_176_, lean_object* v_mantissa_177_, lean_object* v_exponent_178_, lean_object* v_accuracy_179_){
_start:
{
lean_object* v___x_180_; lean_object* v_fst_181_; lean_object* v_snd_182_; lean_object* v_roundedEm_u2081_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v_fst_186_; lean_object* v_snd_187_; lean_object* v_mantissa_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_180_ = l_Float_Model_UnpackedFloat_shiftToTargetExponent(v_spec_175_, v_mantissa_177_, v_exponent_178_, v_accuracy_179_);
v_fst_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_fst_181_);
v_snd_182_ = lean_ctor_get(v___x_180_, 1);
lean_inc(v_snd_182_);
lean_dec_ref(v___x_180_);
v_roundedEm_u2081_183_ = l_Float_Model_UnpackedFloat_ExtendedMantissa_roundedMantissa(v_fst_181_);
lean_dec(v_fst_181_);
v___x_184_ = lean_box(0);
v___x_185_ = l_Float_Model_UnpackedFloat_shiftToTargetExponent(v_spec_175_, v_roundedEm_u2081_183_, v_snd_182_, v___x_184_);
lean_dec(v_snd_182_);
v_fst_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_fst_186_);
v_snd_187_ = lean_ctor_get(v___x_185_, 1);
lean_inc(v_snd_187_);
lean_dec_ref(v___x_185_);
v_mantissa_188_ = lean_ctor_get(v_fst_186_, 0);
lean_inc(v_mantissa_188_);
lean_dec(v_fst_186_);
v___x_189_ = lean_unsigned_to_nat(0u);
v___x_190_ = lean_nat_dec_eq(v_mantissa_188_, v___x_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; 
v___x_191_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_191_, 0, v_mantissa_188_);
lean_ctor_set(v___x_191_, 1, v_snd_187_);
lean_ctor_set_uint8(v___x_191_, sizeof(void*)*2, v_sign_176_);
return v___x_191_;
}
else
{
lean_object* v___x_192_; 
lean_dec(v_mantissa_188_);
lean_dec(v_snd_187_);
v___x_192_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_192_, 0, v_sign_176_);
return v___x_192_;
}
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_roundWithAccuracy_0interp(lean_interpreter_value* stack)
{
lean_object* v_spec_175_ = stack[0].m_obj;
uint8_t v_sign_176_ = stack[1].m_num;
lean_object* v_mantissa_177_ = stack[2].m_obj;
lean_object* v_exponent_178_ = stack[3].m_obj;
lean_object* v_accuracy_179_ = stack[4].m_obj;
lean_object* v_res_193_;
v_res_193_ = l_Float_Model_UnpackedFloat_roundWithAccuracy(v_spec_175_, v_sign_176_, v_mantissa_177_, v_exponent_178_, v_accuracy_179_);
stack->m_obj
 = v_res_193_;
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
lean_object* l_Float_Model_UnpackedFloat_round(lean_object* v_spec_214_, uint8_t v_sign_215_, lean_object* v_mantissa_216_, lean_object* v_exponent_217_){
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
LEAN_EXPORT void l_Float_Model_UnpackedFloat_round_0interp(lean_interpreter_value* stack)
{
lean_object* v_spec_214_ = stack[0].m_obj;
uint8_t v_sign_215_ = stack[1].m_num;
lean_object* v_mantissa_216_ = stack[2].m_obj;
lean_object* v_exponent_217_ = stack[3].m_obj;
lean_object* v_res_225_;
v_res_225_ = l_Float_Model_UnpackedFloat_round(v_spec_214_, v_sign_215_, v_mantissa_216_, v_exponent_217_);
stack->m_obj
 = v_res_225_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_round___boxed(lean_object* v_spec_226_, lean_object* v_sign_227_, lean_object* v_mantissa_228_, lean_object* v_exponent_229_){
_start:
{
uint8_t v_sign_boxed_230_; lean_object* v_res_231_; 
v_sign_boxed_230_ = lean_unbox(v_sign_227_);
v_res_231_ = l_Float_Model_UnpackedFloat_round(v_spec_226_, v_sign_boxed_230_, v_mantissa_228_, v_exponent_229_);
lean_dec(v_exponent_229_);
lean_dec(v_mantissa_228_);
lean_dec_ref(v_spec_226_);
return v_res_231_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_normalize___closed__0(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_unsigned_to_nat(0u);
v___x_233_ = lean_nat_to_int(v___x_232_);
return v___x_233_;
}
}
lean_object* l_Float_Model_UnpackedFloat_normalize(lean_object* v_spec_234_, lean_object* v_mantissa_235_, lean_object* v_exponent_236_, uint8_t v_zeroSign_237_){
_start:
{
lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_238_ = lean_obj_once(&l_Float_Model_UnpackedFloat_normalize___closed__0, &l_Float_Model_UnpackedFloat_normalize___closed__0_once, _init_l_Float_Model_UnpackedFloat_normalize___closed__0);
v___x_239_ = lean_int_dec_lt(v_mantissa_235_, v___x_238_);
if (v___x_239_ == 0)
{
uint8_t v___x_240_; 
v___x_240_ = lean_int_dec_eq(v_mantissa_235_, v___x_238_);
if (v___x_240_ == 0)
{
uint8_t v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_241_ = 1;
v___x_242_ = l_Int_toNat(v_mantissa_235_);
v___x_243_ = l_Float_Model_UnpackedFloat_round(v_spec_234_, v___x_241_, v___x_242_, v_exponent_236_);
lean_dec(v___x_242_);
return v___x_243_;
}
else
{
lean_object* v___x_244_; 
v___x_244_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_244_, 0, v_zeroSign_237_);
return v___x_244_;
}
}
else
{
uint8_t v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_245_ = 0;
v___x_246_ = lean_int_neg(v_mantissa_235_);
v___x_247_ = l_Int_toNat(v___x_246_);
lean_dec(v___x_246_);
v___x_248_ = l_Float_Model_UnpackedFloat_round(v_spec_234_, v___x_245_, v___x_247_, v_exponent_236_);
lean_dec(v___x_247_);
return v___x_248_;
}
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_normalize_0interp(lean_interpreter_value* stack)
{
lean_object* v_spec_234_ = stack[0].m_obj;
lean_object* v_mantissa_235_ = stack[1].m_obj;
lean_object* v_exponent_236_ = stack[2].m_obj;
uint8_t v_zeroSign_237_ = stack[3].m_num;
lean_object* v_res_249_;
v_res_249_ = l_Float_Model_UnpackedFloat_normalize(v_spec_234_, v_mantissa_235_, v_exponent_236_, v_zeroSign_237_);
stack->m_obj
 = v_res_249_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_normalize___boxed(lean_object* v_spec_250_, lean_object* v_mantissa_251_, lean_object* v_exponent_252_, lean_object* v_zeroSign_253_){
_start:
{
uint8_t v_zeroSign_boxed_254_; lean_object* v_res_255_; 
v_zeroSign_boxed_254_ = lean_unbox(v_zeroSign_253_);
v_res_255_ = l_Float_Model_UnpackedFloat_normalize(v_spec_250_, v_mantissa_251_, v_exponent_252_, v_zeroSign_boxed_254_);
lean_dec(v_exponent_252_);
lean_dec(v_mantissa_251_);
lean_dec_ref(v_spec_250_);
return v_res_255_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Float_Model_Format_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Sign(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Round(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
