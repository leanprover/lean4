// Lean compiler output
// Module: Init.Data.Float.Model.Unpacked.Operations.ToNat
// Imports: public import Init.Data.Float.Model.Unpacked.Round public import Init.Data.SInt.Basic
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
uint64_t lean_int64_of_nat(lean_object*);
uint64_t lean_int64_neg(uint64_t);
lean_object* lean_int64_to_int_sint(uint64_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_decreaseExponent(lean_object*, lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_shiftToExponent(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_Sign_apply(uint8_t, lean_object*);
uint64_t l_Int64_ofIntClamp(lean_object*);
extern lean_object* l_System_Platform_numBits;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
size_t lean_isize_of_int(lean_object*);
lean_object* lean_isize_to_int(size_t);
lean_object* lean_int_sub(lean_object*, lean_object*);
size_t l_ISize_ofIntClamp(lean_object*);
lean_object* l_Int_toNat(lean_object*);
uint16_t l_UInt16_ofNatClamp(lean_object*);
uint32_t lean_int32_of_nat(lean_object*);
uint32_t lean_int32_neg(uint32_t);
lean_object* lean_int32_to_int(uint32_t);
uint32_t l_Int32_ofIntClamp(lean_object*);
uint64_t l_UInt64_ofNatClamp(lean_object*);
uint8_t lean_int8_of_nat(lean_object*);
uint8_t lean_int8_neg(uint8_t);
lean_object* lean_int8_to_int(uint8_t);
uint16_t lean_int16_of_nat(lean_object*);
uint16_t lean_int16_neg(uint16_t);
lean_object* lean_int16_to_int(uint16_t);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t l_UInt8_ofNatClamp(lean_object*);
size_t l_USize_ofNatClamp(lean_object*);
uint16_t l_Int16_ofIntClamp(lean_object*);
uint8_t l_Int8_ofIntClamp(lean_object*);
uint32_t l_UInt32_ofNatClamp(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Float_Model_UnpackedFloat_roundToInt_spec__0(lean_object*);
static lean_once_cell_t l_Float_Model_UnpackedFloat_roundToInt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_roundToInt___closed__0;
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_roundToInt(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_roundToInt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toInt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toInt___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Float_Model_UnpackedFloat_toUInt8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_toUInt8___closed__0;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toUInt8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_toUInt8___closed__1;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toUInt8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_toUInt8___closed__2;
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_toUInt8(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toUInt8___boxed(lean_object*);
static lean_once_cell_t l_Float_Model_UnpackedFloat_toUInt16___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_toUInt16___closed__0;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toUInt16___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_toUInt16___closed__1;
LEAN_EXPORT uint16_t l_Float_Model_UnpackedFloat_toUInt16(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toUInt16___boxed(lean_object*);
static lean_once_cell_t l_Float_Model_UnpackedFloat_toUInt32___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_toUInt32___closed__0;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toUInt32___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_toUInt32___closed__1;
LEAN_EXPORT uint32_t l_Float_Model_UnpackedFloat_toUInt32(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toUInt32___boxed(lean_object*);
static lean_once_cell_t l_Float_Model_UnpackedFloat_toUInt64___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_toUInt64___closed__0;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toUInt64___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_toUInt64___closed__1;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toUInt64___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_toUInt64___closed__2;
LEAN_EXPORT uint64_t l_Float_Model_UnpackedFloat_toUInt64(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toUInt64___boxed(lean_object*);
static lean_once_cell_t l_Float_Model_UnpackedFloat_toUSize___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_toUSize___closed__0;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toUSize___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_toUSize___closed__1;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toUSize___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_toUSize___closed__2;
LEAN_EXPORT size_t l_Float_Model_UnpackedFloat_toUSize(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toUSize___boxed(lean_object*);
static lean_once_cell_t l_Float_Model_UnpackedFloat_toInt8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Float_Model_UnpackedFloat_toInt8___closed__0;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toInt8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Float_Model_UnpackedFloat_toInt8___closed__1;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toInt8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_toInt8___closed__2;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toInt8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Float_Model_UnpackedFloat_toInt8___closed__3;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toInt8___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_toInt8___closed__4;
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_toInt8(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toInt8___boxed(lean_object*);
static lean_once_cell_t l_Float_Model_UnpackedFloat_toInt16___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_Float_Model_UnpackedFloat_toInt16___closed__0;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toInt16___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_Float_Model_UnpackedFloat_toInt16___closed__1;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toInt16___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_toInt16___closed__2;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toInt16___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_Float_Model_UnpackedFloat_toInt16___closed__3;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toInt16___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_toInt16___closed__4;
LEAN_EXPORT uint16_t l_Float_Model_UnpackedFloat_toInt16(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toInt16___boxed(lean_object*);
static lean_once_cell_t l_Float_Model_UnpackedFloat_toInt32___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Float_Model_UnpackedFloat_toInt32___closed__0;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toInt32___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Float_Model_UnpackedFloat_toInt32___closed__1;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toInt32___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_toInt32___closed__2;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toInt32___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Float_Model_UnpackedFloat_toInt32___closed__3;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toInt32___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_toInt32___closed__4;
LEAN_EXPORT uint32_t l_Float_Model_UnpackedFloat_toInt32(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toInt32___boxed(lean_object*);
static lean_once_cell_t l_Float_Model_UnpackedFloat_toInt64___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_toInt64___closed__0;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toInt64___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Float_Model_UnpackedFloat_toInt64___closed__1;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toInt64___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Float_Model_UnpackedFloat_toInt64___closed__2;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toInt64___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_toInt64___closed__3;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toInt64___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Float_Model_UnpackedFloat_toInt64___closed__4;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toInt64___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_toInt64___closed__5;
LEAN_EXPORT uint64_t l_Float_Model_UnpackedFloat_toInt64(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toInt64___boxed(lean_object*);
static lean_once_cell_t l_Float_Model_UnpackedFloat_toISize___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_toISize___closed__0;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toISize___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_toISize___closed__1;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toISize___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_toISize___closed__2;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toISize___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_toISize___closed__3;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toISize___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Float_Model_UnpackedFloat_toISize___closed__4;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toISize___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_toISize___closed__5;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toISize___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_toISize___closed__6;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toISize___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Float_Model_UnpackedFloat_toISize___closed__7;
static lean_once_cell_t l_Float_Model_UnpackedFloat_toISize___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_toISize___closed__8;
LEAN_EXPORT size_t l_Float_Model_UnpackedFloat_toISize(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toISize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Float_Model_UnpackedFloat_roundToInt_spec__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_nat_to_int(v_a_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_roundToInt___closed__0(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(0u);
v___x_4_ = lean_nat_to_int(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_roundToInt(uint8_t v_sign_5_, lean_object* v_mantissa_6_, lean_object* v_exponent_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v_fst_10_; lean_object* v_snd_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v_fst_14_; lean_object* v_mantissa_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_8_ = lean_obj_once(&l_Float_Model_UnpackedFloat_roundToInt___closed__0, &l_Float_Model_UnpackedFloat_roundToInt___closed__0_once, _init_l_Float_Model_UnpackedFloat_roundToInt___closed__0);
v___x_9_ = l_Float_Model_UnpackedFloat_decreaseExponent(v_mantissa_6_, v_exponent_7_, v___x_8_);
v_fst_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc(v_fst_10_);
v_snd_11_ = lean_ctor_get(v___x_9_, 1);
lean_inc(v_snd_11_);
lean_dec_ref(v___x_9_);
v___x_12_ = lean_box(0);
v___x_13_ = l_Float_Model_UnpackedFloat_shiftToExponent(v_fst_10_, v_snd_11_, v___x_12_, v___x_8_);
lean_dec(v_snd_11_);
v_fst_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc(v_fst_14_);
lean_dec_ref(v___x_13_);
v_mantissa_15_ = lean_ctor_get(v_fst_14_, 0);
lean_inc(v_mantissa_15_);
lean_dec(v_fst_14_);
v___x_16_ = lean_nat_to_int(v_mantissa_15_);
v___x_17_ = l_Float_Model_UnpackedFloat_Sign_apply(v_sign_5_, v___x_16_);
lean_dec(v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_roundToInt___boxed(lean_object* v_sign_18_, lean_object* v_mantissa_19_, lean_object* v_exponent_20_){
_start:
{
uint8_t v_sign_boxed_21_; lean_object* v_res_22_; 
v_sign_boxed_21_ = lean_unbox(v_sign_18_);
v_res_22_ = l_Float_Model_UnpackedFloat_roundToInt(v_sign_boxed_21_, v_mantissa_19_, v_exponent_20_);
lean_dec(v_exponent_20_);
lean_dec(v_mantissa_19_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toInt(lean_object* v_negativeInfinity_23_, lean_object* v_positiveInfinity_24_, lean_object* v_x_25_){
_start:
{
switch(lean_obj_tag(v_x_25_))
{
case 0:
{
uint8_t v_sign_26_; 
v_sign_26_ = lean_ctor_get_uint8(v_x_25_, 0);
if (v_sign_26_ == 0)
{
lean_inc(v_negativeInfinity_23_);
return v_negativeInfinity_23_;
}
else
{
lean_inc(v_positiveInfinity_24_);
return v_positiveInfinity_24_;
}
}
case 3:
{
uint8_t v_sign_27_; lean_object* v_mantissa_28_; lean_object* v_exponent_29_; lean_object* v___x_30_; 
v_sign_27_ = lean_ctor_get_uint8(v_x_25_, sizeof(void*)*2);
v_mantissa_28_ = lean_ctor_get(v_x_25_, 0);
v_exponent_29_ = lean_ctor_get(v_x_25_, 1);
v___x_30_ = l_Float_Model_UnpackedFloat_roundToInt(v_sign_27_, v_mantissa_28_, v_exponent_29_);
return v___x_30_;
}
default: 
{
lean_object* v___x_31_; 
v___x_31_ = lean_obj_once(&l_Float_Model_UnpackedFloat_roundToInt___closed__0, &l_Float_Model_UnpackedFloat_roundToInt___closed__0_once, _init_l_Float_Model_UnpackedFloat_roundToInt___closed__0);
return v___x_31_;
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toInt___boxed(lean_object* v_negativeInfinity_32_, lean_object* v_positiveInfinity_33_, lean_object* v_x_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Float_Model_UnpackedFloat_toInt(v_negativeInfinity_32_, v_positiveInfinity_33_, v_x_34_);
lean_dec(v_x_34_);
lean_dec(v_positiveInfinity_33_);
lean_dec(v_negativeInfinity_32_);
return v_res_35_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toUInt8___closed__0(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_unsigned_to_nat(256u);
v___x_37_ = lean_nat_to_int(v___x_36_);
return v___x_37_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toUInt8___closed__1(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lean_unsigned_to_nat(1u);
v___x_39_ = lean_nat_to_int(v___x_38_);
return v___x_39_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toUInt8___closed__2(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_40_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt8___closed__1, &l_Float_Model_UnpackedFloat_toUInt8___closed__1_once, _init_l_Float_Model_UnpackedFloat_toUInt8___closed__1);
v___x_41_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt8___closed__0, &l_Float_Model_UnpackedFloat_toUInt8___closed__0_once, _init_l_Float_Model_UnpackedFloat_toUInt8___closed__0);
v___x_42_ = lean_int_sub(v___x_41_, v___x_40_);
return v___x_42_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_toUInt8(lean_object* v_f_43_){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; uint8_t v___x_48_; 
v___x_44_ = lean_obj_once(&l_Float_Model_UnpackedFloat_roundToInt___closed__0, &l_Float_Model_UnpackedFloat_roundToInt___closed__0_once, _init_l_Float_Model_UnpackedFloat_roundToInt___closed__0);
v___x_45_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt8___closed__2, &l_Float_Model_UnpackedFloat_toUInt8___closed__2_once, _init_l_Float_Model_UnpackedFloat_toUInt8___closed__2);
v___x_46_ = l_Float_Model_UnpackedFloat_toInt(v___x_44_, v___x_45_, v_f_43_);
v___x_47_ = l_Int_toNat(v___x_46_);
lean_dec(v___x_46_);
v___x_48_ = l_UInt8_ofNatClamp(v___x_47_);
lean_dec(v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toUInt8___boxed(lean_object* v_f_49_){
_start:
{
uint8_t v_res_50_; lean_object* v_r_51_; 
v_res_50_ = l_Float_Model_UnpackedFloat_toUInt8(v_f_49_);
lean_dec(v_f_49_);
v_r_51_ = lean_box(v_res_50_);
return v_r_51_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toUInt16___closed__0(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_unsigned_to_nat(65536u);
v___x_53_ = lean_nat_to_int(v___x_52_);
return v___x_53_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toUInt16___closed__1(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt8___closed__1, &l_Float_Model_UnpackedFloat_toUInt8___closed__1_once, _init_l_Float_Model_UnpackedFloat_toUInt8___closed__1);
v___x_55_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt16___closed__0, &l_Float_Model_UnpackedFloat_toUInt16___closed__0_once, _init_l_Float_Model_UnpackedFloat_toUInt16___closed__0);
v___x_56_ = lean_int_sub(v___x_55_, v___x_54_);
return v___x_56_;
}
}
LEAN_EXPORT uint16_t l_Float_Model_UnpackedFloat_toUInt16(lean_object* v_f_57_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; uint16_t v___x_62_; 
v___x_58_ = lean_obj_once(&l_Float_Model_UnpackedFloat_roundToInt___closed__0, &l_Float_Model_UnpackedFloat_roundToInt___closed__0_once, _init_l_Float_Model_UnpackedFloat_roundToInt___closed__0);
v___x_59_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt16___closed__1, &l_Float_Model_UnpackedFloat_toUInt16___closed__1_once, _init_l_Float_Model_UnpackedFloat_toUInt16___closed__1);
v___x_60_ = l_Float_Model_UnpackedFloat_toInt(v___x_58_, v___x_59_, v_f_57_);
v___x_61_ = l_Int_toNat(v___x_60_);
lean_dec(v___x_60_);
v___x_62_ = l_UInt16_ofNatClamp(v___x_61_);
lean_dec(v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toUInt16___boxed(lean_object* v_f_63_){
_start:
{
uint16_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = l_Float_Model_UnpackedFloat_toUInt16(v_f_63_);
lean_dec(v_f_63_);
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toUInt32___closed__0(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = lean_cstr_to_nat("4294967296");
v___x_67_ = lean_nat_to_int(v___x_66_);
return v___x_67_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toUInt32___closed__1(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt8___closed__1, &l_Float_Model_UnpackedFloat_toUInt8___closed__1_once, _init_l_Float_Model_UnpackedFloat_toUInt8___closed__1);
v___x_69_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt32___closed__0, &l_Float_Model_UnpackedFloat_toUInt32___closed__0_once, _init_l_Float_Model_UnpackedFloat_toUInt32___closed__0);
v___x_70_ = lean_int_sub(v___x_69_, v___x_68_);
return v___x_70_;
}
}
LEAN_EXPORT uint32_t l_Float_Model_UnpackedFloat_toUInt32(lean_object* v_f_71_){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; uint32_t v___x_76_; 
v___x_72_ = lean_obj_once(&l_Float_Model_UnpackedFloat_roundToInt___closed__0, &l_Float_Model_UnpackedFloat_roundToInt___closed__0_once, _init_l_Float_Model_UnpackedFloat_roundToInt___closed__0);
v___x_73_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt32___closed__1, &l_Float_Model_UnpackedFloat_toUInt32___closed__1_once, _init_l_Float_Model_UnpackedFloat_toUInt32___closed__1);
v___x_74_ = l_Float_Model_UnpackedFloat_toInt(v___x_72_, v___x_73_, v_f_71_);
v___x_75_ = l_Int_toNat(v___x_74_);
lean_dec(v___x_74_);
v___x_76_ = l_UInt32_ofNatClamp(v___x_75_);
lean_dec(v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toUInt32___boxed(lean_object* v_f_77_){
_start:
{
uint32_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = l_Float_Model_UnpackedFloat_toUInt32(v_f_77_);
lean_dec(v_f_77_);
v_r_79_ = lean_box_uint32(v_res_78_);
return v_r_79_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toUInt64___closed__0(void){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_cstr_to_nat("18446744073709551616");
return v___x_80_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toUInt64___closed__1(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt64___closed__0, &l_Float_Model_UnpackedFloat_toUInt64___closed__0_once, _init_l_Float_Model_UnpackedFloat_toUInt64___closed__0);
v___x_82_ = lean_nat_to_int(v___x_81_);
return v___x_82_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toUInt64___closed__2(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_83_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt8___closed__1, &l_Float_Model_UnpackedFloat_toUInt8___closed__1_once, _init_l_Float_Model_UnpackedFloat_toUInt8___closed__1);
v___x_84_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt64___closed__1, &l_Float_Model_UnpackedFloat_toUInt64___closed__1_once, _init_l_Float_Model_UnpackedFloat_toUInt64___closed__1);
v___x_85_ = lean_int_sub(v___x_84_, v___x_83_);
return v___x_85_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_UnpackedFloat_toUInt64(lean_object* v_f_86_){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; uint64_t v___x_91_; 
v___x_87_ = lean_obj_once(&l_Float_Model_UnpackedFloat_roundToInt___closed__0, &l_Float_Model_UnpackedFloat_roundToInt___closed__0_once, _init_l_Float_Model_UnpackedFloat_roundToInt___closed__0);
v___x_88_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt64___closed__2, &l_Float_Model_UnpackedFloat_toUInt64___closed__2_once, _init_l_Float_Model_UnpackedFloat_toUInt64___closed__2);
v___x_89_ = l_Float_Model_UnpackedFloat_toInt(v___x_87_, v___x_88_, v_f_86_);
v___x_90_ = l_Int_toNat(v___x_89_);
lean_dec(v___x_89_);
v___x_91_ = l_UInt64_ofNatClamp(v___x_90_);
lean_dec(v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toUInt64___boxed(lean_object* v_f_92_){
_start:
{
uint64_t v_res_93_; lean_object* v_r_94_; 
v_res_93_ = l_Float_Model_UnpackedFloat_toUInt64(v_f_92_);
lean_dec(v_f_92_);
v_r_94_ = lean_box_uint64(v_res_93_);
return v_r_94_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toUSize___closed__0(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = l_System_Platform_numBits;
v___x_96_ = lean_unsigned_to_nat(2u);
v___x_97_ = lean_nat_pow(v___x_96_, v___x_95_);
return v___x_97_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toUSize___closed__1(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUSize___closed__0, &l_Float_Model_UnpackedFloat_toUSize___closed__0_once, _init_l_Float_Model_UnpackedFloat_toUSize___closed__0);
v___x_99_ = lean_nat_to_int(v___x_98_);
return v___x_99_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toUSize___closed__2(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_100_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt8___closed__1, &l_Float_Model_UnpackedFloat_toUInt8___closed__1_once, _init_l_Float_Model_UnpackedFloat_toUInt8___closed__1);
v___x_101_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUSize___closed__1, &l_Float_Model_UnpackedFloat_toUSize___closed__1_once, _init_l_Float_Model_UnpackedFloat_toUSize___closed__1);
v___x_102_ = lean_int_sub(v___x_101_, v___x_100_);
return v___x_102_;
}
}
LEAN_EXPORT size_t l_Float_Model_UnpackedFloat_toUSize(lean_object* v_f_103_){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; size_t v___x_108_; 
v___x_104_ = lean_obj_once(&l_Float_Model_UnpackedFloat_roundToInt___closed__0, &l_Float_Model_UnpackedFloat_roundToInt___closed__0_once, _init_l_Float_Model_UnpackedFloat_roundToInt___closed__0);
v___x_105_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUSize___closed__2, &l_Float_Model_UnpackedFloat_toUSize___closed__2_once, _init_l_Float_Model_UnpackedFloat_toUSize___closed__2);
v___x_106_ = l_Float_Model_UnpackedFloat_toInt(v___x_104_, v___x_105_, v_f_103_);
v___x_107_ = l_Int_toNat(v___x_106_);
lean_dec(v___x_106_);
v___x_108_ = l_USize_ofNatClamp(v___x_107_);
lean_dec(v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toUSize___boxed(lean_object* v_f_109_){
_start:
{
size_t v_res_110_; lean_object* v_r_111_; 
v_res_110_ = l_Float_Model_UnpackedFloat_toUSize(v_f_109_);
lean_dec(v_f_109_);
v_r_111_ = lean_box_usize(v_res_110_);
return v_r_111_;
}
}
static uint8_t _init_l_Float_Model_UnpackedFloat_toInt8___closed__0(void){
_start:
{
lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_112_ = lean_unsigned_to_nat(128u);
v___x_113_ = lean_int8_of_nat(v___x_112_);
return v___x_113_;
}
}
static uint8_t _init_l_Float_Model_UnpackedFloat_toInt8___closed__1(void){
_start:
{
uint8_t v___x_114_; uint8_t v___x_115_; 
v___x_114_ = lean_uint8_once(&l_Float_Model_UnpackedFloat_toInt8___closed__0, &l_Float_Model_UnpackedFloat_toInt8___closed__0_once, _init_l_Float_Model_UnpackedFloat_toInt8___closed__0);
v___x_115_ = lean_int8_neg(v___x_114_);
return v___x_115_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toInt8___closed__2(void){
_start:
{
uint8_t v___x_116_; lean_object* v___x_117_; 
v___x_116_ = lean_uint8_once(&l_Float_Model_UnpackedFloat_toInt8___closed__1, &l_Float_Model_UnpackedFloat_toInt8___closed__1_once, _init_l_Float_Model_UnpackedFloat_toInt8___closed__1);
v___x_117_ = lean_int8_to_int(v___x_116_);
return v___x_117_;
}
}
static uint8_t _init_l_Float_Model_UnpackedFloat_toInt8___closed__3(void){
_start:
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = lean_unsigned_to_nat(127u);
v___x_119_ = lean_int8_of_nat(v___x_118_);
return v___x_119_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toInt8___closed__4(void){
_start:
{
uint8_t v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_uint8_once(&l_Float_Model_UnpackedFloat_toInt8___closed__3, &l_Float_Model_UnpackedFloat_toInt8___closed__3_once, _init_l_Float_Model_UnpackedFloat_toInt8___closed__3);
v___x_121_ = lean_int8_to_int(v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_toInt8(lean_object* v_f_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_123_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toInt8___closed__2, &l_Float_Model_UnpackedFloat_toInt8___closed__2_once, _init_l_Float_Model_UnpackedFloat_toInt8___closed__2);
v___x_124_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toInt8___closed__4, &l_Float_Model_UnpackedFloat_toInt8___closed__4_once, _init_l_Float_Model_UnpackedFloat_toInt8___closed__4);
v___x_125_ = l_Float_Model_UnpackedFloat_toInt(v___x_123_, v___x_124_, v_f_122_);
v___x_126_ = l_Int8_ofIntClamp(v___x_125_);
lean_dec(v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toInt8___boxed(lean_object* v_f_127_){
_start:
{
uint8_t v_res_128_; lean_object* v_r_129_; 
v_res_128_ = l_Float_Model_UnpackedFloat_toInt8(v_f_127_);
lean_dec(v_f_127_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
static uint16_t _init_l_Float_Model_UnpackedFloat_toInt16___closed__0(void){
_start:
{
lean_object* v___x_130_; uint16_t v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(32768u);
v___x_131_ = lean_int16_of_nat(v___x_130_);
return v___x_131_;
}
}
static uint16_t _init_l_Float_Model_UnpackedFloat_toInt16___closed__1(void){
_start:
{
uint16_t v___x_132_; uint16_t v___x_133_; 
v___x_132_ = lean_uint16_once(&l_Float_Model_UnpackedFloat_toInt16___closed__0, &l_Float_Model_UnpackedFloat_toInt16___closed__0_once, _init_l_Float_Model_UnpackedFloat_toInt16___closed__0);
v___x_133_ = lean_int16_neg(v___x_132_);
return v___x_133_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toInt16___closed__2(void){
_start:
{
uint16_t v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_uint16_once(&l_Float_Model_UnpackedFloat_toInt16___closed__1, &l_Float_Model_UnpackedFloat_toInt16___closed__1_once, _init_l_Float_Model_UnpackedFloat_toInt16___closed__1);
v___x_135_ = lean_int16_to_int(v___x_134_);
return v___x_135_;
}
}
static uint16_t _init_l_Float_Model_UnpackedFloat_toInt16___closed__3(void){
_start:
{
lean_object* v___x_136_; uint16_t v___x_137_; 
v___x_136_ = lean_unsigned_to_nat(32767u);
v___x_137_ = lean_int16_of_nat(v___x_136_);
return v___x_137_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toInt16___closed__4(void){
_start:
{
uint16_t v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_uint16_once(&l_Float_Model_UnpackedFloat_toInt16___closed__3, &l_Float_Model_UnpackedFloat_toInt16___closed__3_once, _init_l_Float_Model_UnpackedFloat_toInt16___closed__3);
v___x_139_ = lean_int16_to_int(v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT uint16_t l_Float_Model_UnpackedFloat_toInt16(lean_object* v_f_140_){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; uint16_t v___x_144_; 
v___x_141_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toInt16___closed__2, &l_Float_Model_UnpackedFloat_toInt16___closed__2_once, _init_l_Float_Model_UnpackedFloat_toInt16___closed__2);
v___x_142_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toInt16___closed__4, &l_Float_Model_UnpackedFloat_toInt16___closed__4_once, _init_l_Float_Model_UnpackedFloat_toInt16___closed__4);
v___x_143_ = l_Float_Model_UnpackedFloat_toInt(v___x_141_, v___x_142_, v_f_140_);
v___x_144_ = l_Int16_ofIntClamp(v___x_143_);
lean_dec(v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toInt16___boxed(lean_object* v_f_145_){
_start:
{
uint16_t v_res_146_; lean_object* v_r_147_; 
v_res_146_ = l_Float_Model_UnpackedFloat_toInt16(v_f_145_);
lean_dec(v_f_145_);
v_r_147_ = lean_box(v_res_146_);
return v_r_147_;
}
}
static uint32_t _init_l_Float_Model_UnpackedFloat_toInt32___closed__0(void){
_start:
{
lean_object* v___x_148_; uint32_t v___x_149_; 
v___x_148_ = lean_unsigned_to_nat(2147483648u);
v___x_149_ = lean_int32_of_nat(v___x_148_);
return v___x_149_;
}
}
static uint32_t _init_l_Float_Model_UnpackedFloat_toInt32___closed__1(void){
_start:
{
uint32_t v___x_150_; uint32_t v___x_151_; 
v___x_150_ = lean_uint32_once(&l_Float_Model_UnpackedFloat_toInt32___closed__0, &l_Float_Model_UnpackedFloat_toInt32___closed__0_once, _init_l_Float_Model_UnpackedFloat_toInt32___closed__0);
v___x_151_ = lean_int32_neg(v___x_150_);
return v___x_151_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toInt32___closed__2(void){
_start:
{
uint32_t v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_uint32_once(&l_Float_Model_UnpackedFloat_toInt32___closed__1, &l_Float_Model_UnpackedFloat_toInt32___closed__1_once, _init_l_Float_Model_UnpackedFloat_toInt32___closed__1);
v___x_153_ = lean_int32_to_int(v___x_152_);
return v___x_153_;
}
}
static uint32_t _init_l_Float_Model_UnpackedFloat_toInt32___closed__3(void){
_start:
{
lean_object* v___x_154_; uint32_t v___x_155_; 
v___x_154_ = lean_unsigned_to_nat(2147483647u);
v___x_155_ = lean_int32_of_nat(v___x_154_);
return v___x_155_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toInt32___closed__4(void){
_start:
{
uint32_t v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_uint32_once(&l_Float_Model_UnpackedFloat_toInt32___closed__3, &l_Float_Model_UnpackedFloat_toInt32___closed__3_once, _init_l_Float_Model_UnpackedFloat_toInt32___closed__3);
v___x_157_ = lean_int32_to_int(v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT uint32_t l_Float_Model_UnpackedFloat_toInt32(lean_object* v_f_158_){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; uint32_t v___x_162_; 
v___x_159_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toInt32___closed__2, &l_Float_Model_UnpackedFloat_toInt32___closed__2_once, _init_l_Float_Model_UnpackedFloat_toInt32___closed__2);
v___x_160_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toInt32___closed__4, &l_Float_Model_UnpackedFloat_toInt32___closed__4_once, _init_l_Float_Model_UnpackedFloat_toInt32___closed__4);
v___x_161_ = l_Float_Model_UnpackedFloat_toInt(v___x_159_, v___x_160_, v_f_158_);
v___x_162_ = l_Int32_ofIntClamp(v___x_161_);
lean_dec(v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toInt32___boxed(lean_object* v_f_163_){
_start:
{
uint32_t v_res_164_; lean_object* v_r_165_; 
v_res_164_ = l_Float_Model_UnpackedFloat_toInt32(v_f_163_);
lean_dec(v_f_163_);
v_r_165_ = lean_box_uint32(v_res_164_);
return v_r_165_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toInt64___closed__0(void){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_cstr_to_nat("9223372036854775808");
return v___x_166_;
}
}
static uint64_t _init_l_Float_Model_UnpackedFloat_toInt64___closed__1(void){
_start:
{
lean_object* v___x_167_; uint64_t v___x_168_; 
v___x_167_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toInt64___closed__0, &l_Float_Model_UnpackedFloat_toInt64___closed__0_once, _init_l_Float_Model_UnpackedFloat_toInt64___closed__0);
v___x_168_ = lean_int64_of_nat(v___x_167_);
return v___x_168_;
}
}
static uint64_t _init_l_Float_Model_UnpackedFloat_toInt64___closed__2(void){
_start:
{
uint64_t v___x_169_; uint64_t v___x_170_; 
v___x_169_ = lean_uint64_once(&l_Float_Model_UnpackedFloat_toInt64___closed__1, &l_Float_Model_UnpackedFloat_toInt64___closed__1_once, _init_l_Float_Model_UnpackedFloat_toInt64___closed__1);
v___x_170_ = lean_int64_neg(v___x_169_);
return v___x_170_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toInt64___closed__3(void){
_start:
{
uint64_t v___x_171_; lean_object* v___x_172_; 
v___x_171_ = lean_uint64_once(&l_Float_Model_UnpackedFloat_toInt64___closed__2, &l_Float_Model_UnpackedFloat_toInt64___closed__2_once, _init_l_Float_Model_UnpackedFloat_toInt64___closed__2);
v___x_172_ = lean_int64_to_int_sint(v___x_171_);
return v___x_172_;
}
}
static uint64_t _init_l_Float_Model_UnpackedFloat_toInt64___closed__4(void){
_start:
{
lean_object* v___x_173_; uint64_t v___x_174_; 
v___x_173_ = lean_cstr_to_nat("9223372036854775807");
v___x_174_ = lean_int64_of_nat(v___x_173_);
return v___x_174_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toInt64___closed__5(void){
_start:
{
uint64_t v___x_175_; lean_object* v___x_176_; 
v___x_175_ = lean_uint64_once(&l_Float_Model_UnpackedFloat_toInt64___closed__4, &l_Float_Model_UnpackedFloat_toInt64___closed__4_once, _init_l_Float_Model_UnpackedFloat_toInt64___closed__4);
v___x_176_ = lean_int64_to_int_sint(v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_UnpackedFloat_toInt64(lean_object* v_f_177_){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; uint64_t v___x_181_; 
v___x_178_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toInt64___closed__3, &l_Float_Model_UnpackedFloat_toInt64___closed__3_once, _init_l_Float_Model_UnpackedFloat_toInt64___closed__3);
v___x_179_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toInt64___closed__5, &l_Float_Model_UnpackedFloat_toInt64___closed__5_once, _init_l_Float_Model_UnpackedFloat_toInt64___closed__5);
v___x_180_ = l_Float_Model_UnpackedFloat_toInt(v___x_178_, v___x_179_, v_f_177_);
v___x_181_ = l_Int64_ofIntClamp(v___x_180_);
lean_dec(v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toInt64___boxed(lean_object* v_f_182_){
_start:
{
uint64_t v_res_183_; lean_object* v_r_184_; 
v_res_183_ = l_Float_Model_UnpackedFloat_toInt64(v_f_182_);
lean_dec(v_f_182_);
v_r_184_ = lean_box_uint64(v_res_183_);
return v_r_184_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toISize___closed__0(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_unsigned_to_nat(2u);
v___x_186_ = lean_nat_to_int(v___x_185_);
return v___x_186_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toISize___closed__1(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_187_ = lean_unsigned_to_nat(1u);
v___x_188_ = l_System_Platform_numBits;
v___x_189_ = lean_nat_sub(v___x_188_, v___x_187_);
return v___x_189_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toISize___closed__2(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toISize___closed__1, &l_Float_Model_UnpackedFloat_toISize___closed__1_once, _init_l_Float_Model_UnpackedFloat_toISize___closed__1);
v___x_191_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toISize___closed__0, &l_Float_Model_UnpackedFloat_toISize___closed__0_once, _init_l_Float_Model_UnpackedFloat_toISize___closed__0);
v___x_192_ = l_Int_pow(v___x_191_, v___x_190_);
return v___x_192_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toISize___closed__3(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toISize___closed__2, &l_Float_Model_UnpackedFloat_toISize___closed__2_once, _init_l_Float_Model_UnpackedFloat_toISize___closed__2);
v___x_194_ = lean_int_neg(v___x_193_);
return v___x_194_;
}
}
static size_t _init_l_Float_Model_UnpackedFloat_toISize___closed__4(void){
_start:
{
lean_object* v___x_195_; size_t v___x_196_; 
v___x_195_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toISize___closed__3, &l_Float_Model_UnpackedFloat_toISize___closed__3_once, _init_l_Float_Model_UnpackedFloat_toISize___closed__3);
v___x_196_ = lean_isize_of_int(v___x_195_);
return v___x_196_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toISize___closed__5(void){
_start:
{
size_t v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_usize_once(&l_Float_Model_UnpackedFloat_toISize___closed__4, &l_Float_Model_UnpackedFloat_toISize___closed__4_once, _init_l_Float_Model_UnpackedFloat_toISize___closed__4);
v___x_198_ = lean_isize_to_int(v___x_197_);
return v___x_198_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toISize___closed__6(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_199_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt8___closed__1, &l_Float_Model_UnpackedFloat_toUInt8___closed__1_once, _init_l_Float_Model_UnpackedFloat_toUInt8___closed__1);
v___x_200_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toISize___closed__2, &l_Float_Model_UnpackedFloat_toISize___closed__2_once, _init_l_Float_Model_UnpackedFloat_toISize___closed__2);
v___x_201_ = lean_int_sub(v___x_200_, v___x_199_);
return v___x_201_;
}
}
static size_t _init_l_Float_Model_UnpackedFloat_toISize___closed__7(void){
_start:
{
lean_object* v___x_202_; size_t v___x_203_; 
v___x_202_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toISize___closed__6, &l_Float_Model_UnpackedFloat_toISize___closed__6_once, _init_l_Float_Model_UnpackedFloat_toISize___closed__6);
v___x_203_ = lean_isize_of_int(v___x_202_);
return v___x_203_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toISize___closed__8(void){
_start:
{
size_t v___x_204_; lean_object* v___x_205_; 
v___x_204_ = lean_usize_once(&l_Float_Model_UnpackedFloat_toISize___closed__7, &l_Float_Model_UnpackedFloat_toISize___closed__7_once, _init_l_Float_Model_UnpackedFloat_toISize___closed__7);
v___x_205_ = lean_isize_to_int(v___x_204_);
return v___x_205_;
}
}
LEAN_EXPORT size_t l_Float_Model_UnpackedFloat_toISize(lean_object* v_f_206_){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; size_t v___x_210_; 
v___x_207_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toISize___closed__5, &l_Float_Model_UnpackedFloat_toISize___closed__5_once, _init_l_Float_Model_UnpackedFloat_toISize___closed__5);
v___x_208_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toISize___closed__8, &l_Float_Model_UnpackedFloat_toISize___closed__8_once, _init_l_Float_Model_UnpackedFloat_toISize___closed__8);
v___x_209_ = l_Float_Model_UnpackedFloat_toInt(v___x_207_, v___x_208_, v_f_206_);
v___x_210_ = l_ISize_ofIntClamp(v___x_209_);
lean_dec(v___x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toISize___boxed(lean_object* v_f_211_){
_start:
{
size_t v_res_212_; lean_object* v_r_213_; 
v_res_212_ = l_Float_Model_UnpackedFloat_toISize(v_f_211_);
lean_dec(v_f_211_);
v_r_213_ = lean_box_usize(v_res_212_);
return v_r_213_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Round(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_ToNat(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Round(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Float_Model_Unpacked_Operations_ToNat(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Float_Model_Unpacked_Round(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Float_Model_Unpacked_Operations_ToNat(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float_Model_Unpacked_Round(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_ToNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Float_Model_Unpacked_Operations_ToNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Float_Model_Unpacked_Operations_ToNat(builtin);
}
#ifdef __cplusplus
}
#endif
