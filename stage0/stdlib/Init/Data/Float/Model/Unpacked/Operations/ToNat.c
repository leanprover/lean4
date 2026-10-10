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
lean_object* l_Float_Model_UnpackedFloat_roundToInt(uint8_t v_sign_5_, lean_object* v_mantissa_6_, lean_object* v_exponent_7_){
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
LEAN_EXPORT void l_Float_Model_UnpackedFloat_roundToInt_0interp(lean_interpreter_value* stack)
{
uint8_t v_sign_5_ = stack[0].m_num;
lean_object* v_mantissa_6_ = stack[1].m_obj;
lean_object* v_exponent_7_ = stack[2].m_obj;
lean_object* v_res_18_;
v_res_18_ = l_Float_Model_UnpackedFloat_roundToInt(v_sign_5_, v_mantissa_6_, v_exponent_7_);
stack->m_obj
 = v_res_18_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_roundToInt___boxed(lean_object* v_sign_19_, lean_object* v_mantissa_20_, lean_object* v_exponent_21_){
_start:
{
uint8_t v_sign_boxed_22_; lean_object* v_res_23_; 
v_sign_boxed_22_ = lean_unbox(v_sign_19_);
v_res_23_ = l_Float_Model_UnpackedFloat_roundToInt(v_sign_boxed_22_, v_mantissa_20_, v_exponent_21_);
lean_dec(v_exponent_21_);
lean_dec(v_mantissa_20_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toInt(lean_object* v_negativeInfinity_24_, lean_object* v_positiveInfinity_25_, lean_object* v_x_26_){
_start:
{
switch(lean_obj_tag(v_x_26_))
{
case 0:
{
uint8_t v_sign_27_; 
v_sign_27_ = lean_ctor_get_uint8(v_x_26_, 0);
if (v_sign_27_ == 0)
{
lean_inc(v_negativeInfinity_24_);
return v_negativeInfinity_24_;
}
else
{
lean_inc(v_positiveInfinity_25_);
return v_positiveInfinity_25_;
}
}
case 3:
{
uint8_t v_sign_28_; lean_object* v_mantissa_29_; lean_object* v_exponent_30_; lean_object* v___x_31_; 
v_sign_28_ = lean_ctor_get_uint8(v_x_26_, sizeof(void*)*2);
v_mantissa_29_ = lean_ctor_get(v_x_26_, 0);
v_exponent_30_ = lean_ctor_get(v_x_26_, 1);
v___x_31_ = l_Float_Model_UnpackedFloat_roundToInt(v_sign_28_, v_mantissa_29_, v_exponent_30_);
return v___x_31_;
}
default: 
{
lean_object* v___x_32_; 
v___x_32_ = lean_obj_once(&l_Float_Model_UnpackedFloat_roundToInt___closed__0, &l_Float_Model_UnpackedFloat_roundToInt___closed__0_once, _init_l_Float_Model_UnpackedFloat_roundToInt___closed__0);
return v___x_32_;
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toInt___boxed(lean_object* v_negativeInfinity_33_, lean_object* v_positiveInfinity_34_, lean_object* v_x_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Float_Model_UnpackedFloat_toInt(v_negativeInfinity_33_, v_positiveInfinity_34_, v_x_35_);
lean_dec(v_x_35_);
lean_dec(v_positiveInfinity_34_);
lean_dec(v_negativeInfinity_33_);
return v_res_36_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toUInt8___closed__0(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_unsigned_to_nat(256u);
v___x_38_ = lean_nat_to_int(v___x_37_);
return v___x_38_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toUInt8___closed__1(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = lean_unsigned_to_nat(1u);
v___x_40_ = lean_nat_to_int(v___x_39_);
return v___x_40_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toUInt8___closed__2(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_41_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt8___closed__1, &l_Float_Model_UnpackedFloat_toUInt8___closed__1_once, _init_l_Float_Model_UnpackedFloat_toUInt8___closed__1);
v___x_42_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt8___closed__0, &l_Float_Model_UnpackedFloat_toUInt8___closed__0_once, _init_l_Float_Model_UnpackedFloat_toUInt8___closed__0);
v___x_43_ = lean_int_sub(v___x_42_, v___x_41_);
return v___x_43_;
}
}
uint8_t l_Float_Model_UnpackedFloat_toUInt8(lean_object* v_f_44_){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; uint8_t v___x_49_; 
v___x_45_ = lean_obj_once(&l_Float_Model_UnpackedFloat_roundToInt___closed__0, &l_Float_Model_UnpackedFloat_roundToInt___closed__0_once, _init_l_Float_Model_UnpackedFloat_roundToInt___closed__0);
v___x_46_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt8___closed__2, &l_Float_Model_UnpackedFloat_toUInt8___closed__2_once, _init_l_Float_Model_UnpackedFloat_toUInt8___closed__2);
v___x_47_ = l_Float_Model_UnpackedFloat_toInt(v___x_45_, v___x_46_, v_f_44_);
v___x_48_ = l_Int_toNat(v___x_47_);
lean_dec(v___x_47_);
v___x_49_ = l_UInt8_ofNatClamp(v___x_48_);
lean_dec(v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_toUInt8_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_44_ = stack[0].m_obj;
uint8_t v_res_50_;
v_res_50_ = l_Float_Model_UnpackedFloat_toUInt8(v_f_44_);
stack->m_num = v_res_50_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toUInt8___boxed(lean_object* v_f_51_){
_start:
{
uint8_t v_res_52_; lean_object* v_r_53_; 
v_res_52_ = l_Float_Model_UnpackedFloat_toUInt8(v_f_51_);
lean_dec(v_f_51_);
v_r_53_ = lean_box(v_res_52_);
return v_r_53_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toUInt16___closed__0(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_unsigned_to_nat(65536u);
v___x_55_ = lean_nat_to_int(v___x_54_);
return v___x_55_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toUInt16___closed__1(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt8___closed__1, &l_Float_Model_UnpackedFloat_toUInt8___closed__1_once, _init_l_Float_Model_UnpackedFloat_toUInt8___closed__1);
v___x_57_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt16___closed__0, &l_Float_Model_UnpackedFloat_toUInt16___closed__0_once, _init_l_Float_Model_UnpackedFloat_toUInt16___closed__0);
v___x_58_ = lean_int_sub(v___x_57_, v___x_56_);
return v___x_58_;
}
}
uint16_t l_Float_Model_UnpackedFloat_toUInt16(lean_object* v_f_59_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; uint16_t v___x_64_; 
v___x_60_ = lean_obj_once(&l_Float_Model_UnpackedFloat_roundToInt___closed__0, &l_Float_Model_UnpackedFloat_roundToInt___closed__0_once, _init_l_Float_Model_UnpackedFloat_roundToInt___closed__0);
v___x_61_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt16___closed__1, &l_Float_Model_UnpackedFloat_toUInt16___closed__1_once, _init_l_Float_Model_UnpackedFloat_toUInt16___closed__1);
v___x_62_ = l_Float_Model_UnpackedFloat_toInt(v___x_60_, v___x_61_, v_f_59_);
v___x_63_ = l_Int_toNat(v___x_62_);
lean_dec(v___x_62_);
v___x_64_ = l_UInt16_ofNatClamp(v___x_63_);
lean_dec(v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_toUInt16_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_59_ = stack[0].m_obj;
uint16_t v_res_65_;
v_res_65_ = l_Float_Model_UnpackedFloat_toUInt16(v_f_59_);
stack->m_num = v_res_65_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toUInt16___boxed(lean_object* v_f_66_){
_start:
{
uint16_t v_res_67_; lean_object* v_r_68_; 
v_res_67_ = l_Float_Model_UnpackedFloat_toUInt16(v_f_66_);
lean_dec(v_f_66_);
v_r_68_ = lean_box(v_res_67_);
return v_r_68_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toUInt32___closed__0(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_cstr_to_nat("4294967296");
v___x_70_ = lean_nat_to_int(v___x_69_);
return v___x_70_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toUInt32___closed__1(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_71_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt8___closed__1, &l_Float_Model_UnpackedFloat_toUInt8___closed__1_once, _init_l_Float_Model_UnpackedFloat_toUInt8___closed__1);
v___x_72_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt32___closed__0, &l_Float_Model_UnpackedFloat_toUInt32___closed__0_once, _init_l_Float_Model_UnpackedFloat_toUInt32___closed__0);
v___x_73_ = lean_int_sub(v___x_72_, v___x_71_);
return v___x_73_;
}
}
uint32_t l_Float_Model_UnpackedFloat_toUInt32(lean_object* v_f_74_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; uint32_t v___x_79_; 
v___x_75_ = lean_obj_once(&l_Float_Model_UnpackedFloat_roundToInt___closed__0, &l_Float_Model_UnpackedFloat_roundToInt___closed__0_once, _init_l_Float_Model_UnpackedFloat_roundToInt___closed__0);
v___x_76_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt32___closed__1, &l_Float_Model_UnpackedFloat_toUInt32___closed__1_once, _init_l_Float_Model_UnpackedFloat_toUInt32___closed__1);
v___x_77_ = l_Float_Model_UnpackedFloat_toInt(v___x_75_, v___x_76_, v_f_74_);
v___x_78_ = l_Int_toNat(v___x_77_);
lean_dec(v___x_77_);
v___x_79_ = l_UInt32_ofNatClamp(v___x_78_);
lean_dec(v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_toUInt32_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_74_ = stack[0].m_obj;
uint32_t v_res_80_;
v_res_80_ = l_Float_Model_UnpackedFloat_toUInt32(v_f_74_);
stack->m_num = v_res_80_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toUInt32___boxed(lean_object* v_f_81_){
_start:
{
uint32_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = l_Float_Model_UnpackedFloat_toUInt32(v_f_81_);
lean_dec(v_f_81_);
v_r_83_ = lean_box_uint32(v_res_82_);
return v_r_83_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toUInt64___closed__0(void){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lean_cstr_to_nat("18446744073709551616");
return v___x_84_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toUInt64___closed__1(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt64___closed__0, &l_Float_Model_UnpackedFloat_toUInt64___closed__0_once, _init_l_Float_Model_UnpackedFloat_toUInt64___closed__0);
v___x_86_ = lean_nat_to_int(v___x_85_);
return v___x_86_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toUInt64___closed__2(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt8___closed__1, &l_Float_Model_UnpackedFloat_toUInt8___closed__1_once, _init_l_Float_Model_UnpackedFloat_toUInt8___closed__1);
v___x_88_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt64___closed__1, &l_Float_Model_UnpackedFloat_toUInt64___closed__1_once, _init_l_Float_Model_UnpackedFloat_toUInt64___closed__1);
v___x_89_ = lean_int_sub(v___x_88_, v___x_87_);
return v___x_89_;
}
}
uint64_t l_Float_Model_UnpackedFloat_toUInt64(lean_object* v_f_90_){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; uint64_t v___x_95_; 
v___x_91_ = lean_obj_once(&l_Float_Model_UnpackedFloat_roundToInt___closed__0, &l_Float_Model_UnpackedFloat_roundToInt___closed__0_once, _init_l_Float_Model_UnpackedFloat_roundToInt___closed__0);
v___x_92_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt64___closed__2, &l_Float_Model_UnpackedFloat_toUInt64___closed__2_once, _init_l_Float_Model_UnpackedFloat_toUInt64___closed__2);
v___x_93_ = l_Float_Model_UnpackedFloat_toInt(v___x_91_, v___x_92_, v_f_90_);
v___x_94_ = l_Int_toNat(v___x_93_);
lean_dec(v___x_93_);
v___x_95_ = l_UInt64_ofNatClamp(v___x_94_);
lean_dec(v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_toUInt64_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_90_ = stack[0].m_obj;
uint64_t v_res_96_;
v_res_96_ = l_Float_Model_UnpackedFloat_toUInt64(v_f_90_);
stack->m_num = v_res_96_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toUInt64___boxed(lean_object* v_f_97_){
_start:
{
uint64_t v_res_98_; lean_object* v_r_99_; 
v_res_98_ = l_Float_Model_UnpackedFloat_toUInt64(v_f_97_);
lean_dec(v_f_97_);
v_r_99_ = lean_box_uint64(v_res_98_);
return v_r_99_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toUSize___closed__0(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_100_ = l_System_Platform_numBits;
v___x_101_ = lean_unsigned_to_nat(2u);
v___x_102_ = lean_nat_pow(v___x_101_, v___x_100_);
return v___x_102_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toUSize___closed__1(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUSize___closed__0, &l_Float_Model_UnpackedFloat_toUSize___closed__0_once, _init_l_Float_Model_UnpackedFloat_toUSize___closed__0);
v___x_104_ = lean_nat_to_int(v___x_103_);
return v___x_104_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toUSize___closed__2(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_105_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt8___closed__1, &l_Float_Model_UnpackedFloat_toUInt8___closed__1_once, _init_l_Float_Model_UnpackedFloat_toUInt8___closed__1);
v___x_106_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUSize___closed__1, &l_Float_Model_UnpackedFloat_toUSize___closed__1_once, _init_l_Float_Model_UnpackedFloat_toUSize___closed__1);
v___x_107_ = lean_int_sub(v___x_106_, v___x_105_);
return v___x_107_;
}
}
size_t l_Float_Model_UnpackedFloat_toUSize(lean_object* v_f_108_){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; size_t v___x_113_; 
v___x_109_ = lean_obj_once(&l_Float_Model_UnpackedFloat_roundToInt___closed__0, &l_Float_Model_UnpackedFloat_roundToInt___closed__0_once, _init_l_Float_Model_UnpackedFloat_roundToInt___closed__0);
v___x_110_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUSize___closed__2, &l_Float_Model_UnpackedFloat_toUSize___closed__2_once, _init_l_Float_Model_UnpackedFloat_toUSize___closed__2);
v___x_111_ = l_Float_Model_UnpackedFloat_toInt(v___x_109_, v___x_110_, v_f_108_);
v___x_112_ = l_Int_toNat(v___x_111_);
lean_dec(v___x_111_);
v___x_113_ = l_USize_ofNatClamp(v___x_112_);
lean_dec(v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_toUSize_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_108_ = stack[0].m_obj;
size_t v_res_114_;
v_res_114_ = l_Float_Model_UnpackedFloat_toUSize(v_f_108_);
stack->m_num = v_res_114_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toUSize___boxed(lean_object* v_f_115_){
_start:
{
size_t v_res_116_; lean_object* v_r_117_; 
v_res_116_ = l_Float_Model_UnpackedFloat_toUSize(v_f_115_);
lean_dec(v_f_115_);
v_r_117_ = lean_box_usize(v_res_116_);
return v_r_117_;
}
}
static uint8_t _init_l_Float_Model_UnpackedFloat_toInt8___closed__0(void){
_start:
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = lean_unsigned_to_nat(128u);
v___x_119_ = lean_int8_of_nat(v___x_118_);
return v___x_119_;
}
}
static uint8_t _init_l_Float_Model_UnpackedFloat_toInt8___closed__1(void){
_start:
{
uint8_t v___x_120_; uint8_t v___x_121_; 
v___x_120_ = lean_uint8_once(&l_Float_Model_UnpackedFloat_toInt8___closed__0, &l_Float_Model_UnpackedFloat_toInt8___closed__0_once, _init_l_Float_Model_UnpackedFloat_toInt8___closed__0);
v___x_121_ = lean_int8_neg(v___x_120_);
return v___x_121_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toInt8___closed__2(void){
_start:
{
uint8_t v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_uint8_once(&l_Float_Model_UnpackedFloat_toInt8___closed__1, &l_Float_Model_UnpackedFloat_toInt8___closed__1_once, _init_l_Float_Model_UnpackedFloat_toInt8___closed__1);
v___x_123_ = lean_int8_to_int(v___x_122_);
return v___x_123_;
}
}
static uint8_t _init_l_Float_Model_UnpackedFloat_toInt8___closed__3(void){
_start:
{
lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(127u);
v___x_125_ = lean_int8_of_nat(v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toInt8___closed__4(void){
_start:
{
uint8_t v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_uint8_once(&l_Float_Model_UnpackedFloat_toInt8___closed__3, &l_Float_Model_UnpackedFloat_toInt8___closed__3_once, _init_l_Float_Model_UnpackedFloat_toInt8___closed__3);
v___x_127_ = lean_int8_to_int(v___x_126_);
return v___x_127_;
}
}
uint8_t l_Float_Model_UnpackedFloat_toInt8(lean_object* v_f_128_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_129_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toInt8___closed__2, &l_Float_Model_UnpackedFloat_toInt8___closed__2_once, _init_l_Float_Model_UnpackedFloat_toInt8___closed__2);
v___x_130_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toInt8___closed__4, &l_Float_Model_UnpackedFloat_toInt8___closed__4_once, _init_l_Float_Model_UnpackedFloat_toInt8___closed__4);
v___x_131_ = l_Float_Model_UnpackedFloat_toInt(v___x_129_, v___x_130_, v_f_128_);
v___x_132_ = l_Int8_ofIntClamp(v___x_131_);
lean_dec(v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_toInt8_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_128_ = stack[0].m_obj;
uint8_t v_res_133_;
v_res_133_ = l_Float_Model_UnpackedFloat_toInt8(v_f_128_);
stack->m_num = v_res_133_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toInt8___boxed(lean_object* v_f_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = l_Float_Model_UnpackedFloat_toInt8(v_f_134_);
lean_dec(v_f_134_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
static uint16_t _init_l_Float_Model_UnpackedFloat_toInt16___closed__0(void){
_start:
{
lean_object* v___x_137_; uint16_t v___x_138_; 
v___x_137_ = lean_unsigned_to_nat(32768u);
v___x_138_ = lean_int16_of_nat(v___x_137_);
return v___x_138_;
}
}
static uint16_t _init_l_Float_Model_UnpackedFloat_toInt16___closed__1(void){
_start:
{
uint16_t v___x_139_; uint16_t v___x_140_; 
v___x_139_ = lean_uint16_once(&l_Float_Model_UnpackedFloat_toInt16___closed__0, &l_Float_Model_UnpackedFloat_toInt16___closed__0_once, _init_l_Float_Model_UnpackedFloat_toInt16___closed__0);
v___x_140_ = lean_int16_neg(v___x_139_);
return v___x_140_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toInt16___closed__2(void){
_start:
{
uint16_t v___x_141_; lean_object* v___x_142_; 
v___x_141_ = lean_uint16_once(&l_Float_Model_UnpackedFloat_toInt16___closed__1, &l_Float_Model_UnpackedFloat_toInt16___closed__1_once, _init_l_Float_Model_UnpackedFloat_toInt16___closed__1);
v___x_142_ = lean_int16_to_int(v___x_141_);
return v___x_142_;
}
}
static uint16_t _init_l_Float_Model_UnpackedFloat_toInt16___closed__3(void){
_start:
{
lean_object* v___x_143_; uint16_t v___x_144_; 
v___x_143_ = lean_unsigned_to_nat(32767u);
v___x_144_ = lean_int16_of_nat(v___x_143_);
return v___x_144_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toInt16___closed__4(void){
_start:
{
uint16_t v___x_145_; lean_object* v___x_146_; 
v___x_145_ = lean_uint16_once(&l_Float_Model_UnpackedFloat_toInt16___closed__3, &l_Float_Model_UnpackedFloat_toInt16___closed__3_once, _init_l_Float_Model_UnpackedFloat_toInt16___closed__3);
v___x_146_ = lean_int16_to_int(v___x_145_);
return v___x_146_;
}
}
uint16_t l_Float_Model_UnpackedFloat_toInt16(lean_object* v_f_147_){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; uint16_t v___x_151_; 
v___x_148_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toInt16___closed__2, &l_Float_Model_UnpackedFloat_toInt16___closed__2_once, _init_l_Float_Model_UnpackedFloat_toInt16___closed__2);
v___x_149_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toInt16___closed__4, &l_Float_Model_UnpackedFloat_toInt16___closed__4_once, _init_l_Float_Model_UnpackedFloat_toInt16___closed__4);
v___x_150_ = l_Float_Model_UnpackedFloat_toInt(v___x_148_, v___x_149_, v_f_147_);
v___x_151_ = l_Int16_ofIntClamp(v___x_150_);
lean_dec(v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_toInt16_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_147_ = stack[0].m_obj;
uint16_t v_res_152_;
v_res_152_ = l_Float_Model_UnpackedFloat_toInt16(v_f_147_);
stack->m_num = v_res_152_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toInt16___boxed(lean_object* v_f_153_){
_start:
{
uint16_t v_res_154_; lean_object* v_r_155_; 
v_res_154_ = l_Float_Model_UnpackedFloat_toInt16(v_f_153_);
lean_dec(v_f_153_);
v_r_155_ = lean_box(v_res_154_);
return v_r_155_;
}
}
static uint32_t _init_l_Float_Model_UnpackedFloat_toInt32___closed__0(void){
_start:
{
lean_object* v___x_156_; uint32_t v___x_157_; 
v___x_156_ = lean_unsigned_to_nat(2147483648u);
v___x_157_ = lean_int32_of_nat(v___x_156_);
return v___x_157_;
}
}
static uint32_t _init_l_Float_Model_UnpackedFloat_toInt32___closed__1(void){
_start:
{
uint32_t v___x_158_; uint32_t v___x_159_; 
v___x_158_ = lean_uint32_once(&l_Float_Model_UnpackedFloat_toInt32___closed__0, &l_Float_Model_UnpackedFloat_toInt32___closed__0_once, _init_l_Float_Model_UnpackedFloat_toInt32___closed__0);
v___x_159_ = lean_int32_neg(v___x_158_);
return v___x_159_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toInt32___closed__2(void){
_start:
{
uint32_t v___x_160_; lean_object* v___x_161_; 
v___x_160_ = lean_uint32_once(&l_Float_Model_UnpackedFloat_toInt32___closed__1, &l_Float_Model_UnpackedFloat_toInt32___closed__1_once, _init_l_Float_Model_UnpackedFloat_toInt32___closed__1);
v___x_161_ = lean_int32_to_int(v___x_160_);
return v___x_161_;
}
}
static uint32_t _init_l_Float_Model_UnpackedFloat_toInt32___closed__3(void){
_start:
{
lean_object* v___x_162_; uint32_t v___x_163_; 
v___x_162_ = lean_unsigned_to_nat(2147483647u);
v___x_163_ = lean_int32_of_nat(v___x_162_);
return v___x_163_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toInt32___closed__4(void){
_start:
{
uint32_t v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_uint32_once(&l_Float_Model_UnpackedFloat_toInt32___closed__3, &l_Float_Model_UnpackedFloat_toInt32___closed__3_once, _init_l_Float_Model_UnpackedFloat_toInt32___closed__3);
v___x_165_ = lean_int32_to_int(v___x_164_);
return v___x_165_;
}
}
uint32_t l_Float_Model_UnpackedFloat_toInt32(lean_object* v_f_166_){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; uint32_t v___x_170_; 
v___x_167_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toInt32___closed__2, &l_Float_Model_UnpackedFloat_toInt32___closed__2_once, _init_l_Float_Model_UnpackedFloat_toInt32___closed__2);
v___x_168_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toInt32___closed__4, &l_Float_Model_UnpackedFloat_toInt32___closed__4_once, _init_l_Float_Model_UnpackedFloat_toInt32___closed__4);
v___x_169_ = l_Float_Model_UnpackedFloat_toInt(v___x_167_, v___x_168_, v_f_166_);
v___x_170_ = l_Int32_ofIntClamp(v___x_169_);
lean_dec(v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_toInt32_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_166_ = stack[0].m_obj;
uint32_t v_res_171_;
v_res_171_ = l_Float_Model_UnpackedFloat_toInt32(v_f_166_);
stack->m_num = v_res_171_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toInt32___boxed(lean_object* v_f_172_){
_start:
{
uint32_t v_res_173_; lean_object* v_r_174_; 
v_res_173_ = l_Float_Model_UnpackedFloat_toInt32(v_f_172_);
lean_dec(v_f_172_);
v_r_174_ = lean_box_uint32(v_res_173_);
return v_r_174_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toInt64___closed__0(void){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = lean_cstr_to_nat("9223372036854775808");
return v___x_175_;
}
}
static uint64_t _init_l_Float_Model_UnpackedFloat_toInt64___closed__1(void){
_start:
{
lean_object* v___x_176_; uint64_t v___x_177_; 
v___x_176_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toInt64___closed__0, &l_Float_Model_UnpackedFloat_toInt64___closed__0_once, _init_l_Float_Model_UnpackedFloat_toInt64___closed__0);
v___x_177_ = lean_int64_of_nat(v___x_176_);
return v___x_177_;
}
}
static uint64_t _init_l_Float_Model_UnpackedFloat_toInt64___closed__2(void){
_start:
{
uint64_t v___x_178_; uint64_t v___x_179_; 
v___x_178_ = lean_uint64_once(&l_Float_Model_UnpackedFloat_toInt64___closed__1, &l_Float_Model_UnpackedFloat_toInt64___closed__1_once, _init_l_Float_Model_UnpackedFloat_toInt64___closed__1);
v___x_179_ = lean_int64_neg(v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toInt64___closed__3(void){
_start:
{
uint64_t v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_uint64_once(&l_Float_Model_UnpackedFloat_toInt64___closed__2, &l_Float_Model_UnpackedFloat_toInt64___closed__2_once, _init_l_Float_Model_UnpackedFloat_toInt64___closed__2);
v___x_181_ = lean_int64_to_int_sint(v___x_180_);
return v___x_181_;
}
}
static uint64_t _init_l_Float_Model_UnpackedFloat_toInt64___closed__4(void){
_start:
{
lean_object* v___x_182_; uint64_t v___x_183_; 
v___x_182_ = lean_cstr_to_nat("9223372036854775807");
v___x_183_ = lean_int64_of_nat(v___x_182_);
return v___x_183_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toInt64___closed__5(void){
_start:
{
uint64_t v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_uint64_once(&l_Float_Model_UnpackedFloat_toInt64___closed__4, &l_Float_Model_UnpackedFloat_toInt64___closed__4_once, _init_l_Float_Model_UnpackedFloat_toInt64___closed__4);
v___x_185_ = lean_int64_to_int_sint(v___x_184_);
return v___x_185_;
}
}
uint64_t l_Float_Model_UnpackedFloat_toInt64(lean_object* v_f_186_){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; uint64_t v___x_190_; 
v___x_187_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toInt64___closed__3, &l_Float_Model_UnpackedFloat_toInt64___closed__3_once, _init_l_Float_Model_UnpackedFloat_toInt64___closed__3);
v___x_188_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toInt64___closed__5, &l_Float_Model_UnpackedFloat_toInt64___closed__5_once, _init_l_Float_Model_UnpackedFloat_toInt64___closed__5);
v___x_189_ = l_Float_Model_UnpackedFloat_toInt(v___x_187_, v___x_188_, v_f_186_);
v___x_190_ = l_Int64_ofIntClamp(v___x_189_);
lean_dec(v___x_189_);
return v___x_190_;
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_toInt64_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_186_ = stack[0].m_obj;
uint64_t v_res_191_;
v_res_191_ = l_Float_Model_UnpackedFloat_toInt64(v_f_186_);
stack->m_num = v_res_191_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toInt64___boxed(lean_object* v_f_192_){
_start:
{
uint64_t v_res_193_; lean_object* v_r_194_; 
v_res_193_ = l_Float_Model_UnpackedFloat_toInt64(v_f_192_);
lean_dec(v_f_192_);
v_r_194_ = lean_box_uint64(v_res_193_);
return v_r_194_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toISize___closed__0(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_unsigned_to_nat(2u);
v___x_196_ = lean_nat_to_int(v___x_195_);
return v___x_196_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toISize___closed__1(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_197_ = lean_unsigned_to_nat(1u);
v___x_198_ = l_System_Platform_numBits;
v___x_199_ = lean_nat_sub(v___x_198_, v___x_197_);
return v___x_199_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toISize___closed__2(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_200_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toISize___closed__1, &l_Float_Model_UnpackedFloat_toISize___closed__1_once, _init_l_Float_Model_UnpackedFloat_toISize___closed__1);
v___x_201_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toISize___closed__0, &l_Float_Model_UnpackedFloat_toISize___closed__0_once, _init_l_Float_Model_UnpackedFloat_toISize___closed__0);
v___x_202_ = l_Int_pow(v___x_201_, v___x_200_);
return v___x_202_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toISize___closed__3(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toISize___closed__2, &l_Float_Model_UnpackedFloat_toISize___closed__2_once, _init_l_Float_Model_UnpackedFloat_toISize___closed__2);
v___x_204_ = lean_int_neg(v___x_203_);
return v___x_204_;
}
}
static size_t _init_l_Float_Model_UnpackedFloat_toISize___closed__4(void){
_start:
{
lean_object* v___x_205_; size_t v___x_206_; 
v___x_205_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toISize___closed__3, &l_Float_Model_UnpackedFloat_toISize___closed__3_once, _init_l_Float_Model_UnpackedFloat_toISize___closed__3);
v___x_206_ = lean_isize_of_int(v___x_205_);
return v___x_206_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toISize___closed__5(void){
_start:
{
size_t v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_usize_once(&l_Float_Model_UnpackedFloat_toISize___closed__4, &l_Float_Model_UnpackedFloat_toISize___closed__4_once, _init_l_Float_Model_UnpackedFloat_toISize___closed__4);
v___x_208_ = lean_isize_to_int(v___x_207_);
return v___x_208_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toISize___closed__6(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_209_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toUInt8___closed__1, &l_Float_Model_UnpackedFloat_toUInt8___closed__1_once, _init_l_Float_Model_UnpackedFloat_toUInt8___closed__1);
v___x_210_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toISize___closed__2, &l_Float_Model_UnpackedFloat_toISize___closed__2_once, _init_l_Float_Model_UnpackedFloat_toISize___closed__2);
v___x_211_ = lean_int_sub(v___x_210_, v___x_209_);
return v___x_211_;
}
}
static size_t _init_l_Float_Model_UnpackedFloat_toISize___closed__7(void){
_start:
{
lean_object* v___x_212_; size_t v___x_213_; 
v___x_212_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toISize___closed__6, &l_Float_Model_UnpackedFloat_toISize___closed__6_once, _init_l_Float_Model_UnpackedFloat_toISize___closed__6);
v___x_213_ = lean_isize_of_int(v___x_212_);
return v___x_213_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_toISize___closed__8(void){
_start:
{
size_t v___x_214_; lean_object* v___x_215_; 
v___x_214_ = lean_usize_once(&l_Float_Model_UnpackedFloat_toISize___closed__7, &l_Float_Model_UnpackedFloat_toISize___closed__7_once, _init_l_Float_Model_UnpackedFloat_toISize___closed__7);
v___x_215_ = lean_isize_to_int(v___x_214_);
return v___x_215_;
}
}
size_t l_Float_Model_UnpackedFloat_toISize(lean_object* v_f_216_){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; size_t v___x_220_; 
v___x_217_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toISize___closed__5, &l_Float_Model_UnpackedFloat_toISize___closed__5_once, _init_l_Float_Model_UnpackedFloat_toISize___closed__5);
v___x_218_ = lean_obj_once(&l_Float_Model_UnpackedFloat_toISize___closed__8, &l_Float_Model_UnpackedFloat_toISize___closed__8_once, _init_l_Float_Model_UnpackedFloat_toISize___closed__8);
v___x_219_ = l_Float_Model_UnpackedFloat_toInt(v___x_217_, v___x_218_, v_f_216_);
v___x_220_ = l_ISize_ofIntClamp(v___x_219_);
lean_dec(v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_toISize_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_216_ = stack[0].m_obj;
size_t v_res_221_;
v_res_221_ = l_Float_Model_UnpackedFloat_toISize(v_f_216_);
stack->m_num = v_res_221_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_toISize___boxed(lean_object* v_f_222_){
_start:
{
size_t v_res_223_; lean_object* v_r_224_; 
v_res_223_ = l_Float_Model_UnpackedFloat_toISize(v_f_222_);
lean_dec(v_f_222_);
v_r_224_ = lean_box_usize(v_res_223_);
return v_r_224_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Round(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_ToNat(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
