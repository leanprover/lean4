// Lean compiler output
// Module: Init.Data.Float.Model.Float
// Imports: public import Init.Data.Float.Model.Format.Valid public import Init.Data.Float.Model.Unpacked.Pack.Lemmas public import Init.Data.Float.Model.Unpacked.Operations public import Init.Data.Order.Factories
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
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_Float_Model_UnpackedFloat_unpack(lean_object*, lean_object*);
uint8_t l_Float_Model_UnpackedFloat_toInt8(lean_object*);
uint8_t l_Float_Model_UnpackedFloat_beq(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofInt8(lean_object*, uint8_t);
lean_object* l_Float_Model_UnpackedFloat_pack(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat_mk(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofISize(lean_object*, size_t);
lean_object* l_Float_Model_UnpackedFloat_neg(lean_object*);
uint8_t l_Float_Model_UnpackedFloat_lt(lean_object*, lean_object*);
uint32_t l_Float_Model_UnpackedFloat_toUInt32(lean_object*);
uint8_t l_Float_Model_UnpackedFloat_le(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofInt32(lean_object*, uint32_t);
lean_object* l_Float_Model_UnpackedFloat_mul(lean_object*, lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofInt(lean_object*, lean_object*);
uint16_t l_Float_Model_UnpackedFloat_toInt16(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofInt64(lean_object*, uint64_t);
lean_object* l_Float_Model_UnpackedFloat_sqrt(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofUInt16(lean_object*, uint16_t);
size_t l_Float_Model_UnpackedFloat_toUSize(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_sub(lean_object*, lean_object*, lean_object*);
uint8_t l_Float_Model_UnpackedFloat_isFinite(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_add(lean_object*, lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofUInt64(lean_object*, uint64_t);
lean_object* l_Float_Model_UnpackedFloat_compare(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofScientific(lean_object*, lean_object*, lean_object*);
uint8_t l_Float_Model_UnpackedFloat_isNaN(lean_object*);
size_t l_Float_Model_UnpackedFloat_toISize(lean_object*);
uint64_t l_Float_Model_UnpackedFloat_toInt64(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofNat(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_div(lean_object*, lean_object*, lean_object*);
uint64_t l_Float_Model_UnpackedFloat_toUInt64(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofUInt32(lean_object*, uint32_t);
lean_object* l_Float_Model_UnpackedFloat_ofInt16(lean_object*, uint16_t);
uint32_t l_Float_Model_UnpackedFloat_toInt32(lean_object*);
uint8_t l_Float_Model_UnpackedFloat_isInf(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofUInt8(lean_object*, uint8_t);
lean_object* l_Float_Model_UnpackedFloat_abs(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofUSize(lean_object*, size_t);
uint16_t l_Float_Model_UnpackedFloat_toUInt16(lean_object*);
uint8_t l_Float_Model_UnpackedFloat_toUInt8(lean_object*);
static const lean_ctor_object l_Float_Model_unpack___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(52) << 1) | 1)),((lean_object*)(((size_t)(11) << 1) | 1))}};
static const lean_object* l_Float_Model_unpack___closed__0 = (const lean_object*)&l_Float_Model_unpack___closed__0_value;
LEAN_EXPORT lean_object* l_Float_Model_unpack(uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_unpack___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Float_Model_pack(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_pack___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Float_Model_add(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_add___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Float_Model_sub(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_sub___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Float_Model_mul(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_mul___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Float_Model_div(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_div___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Float_Model_instAdd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_Model_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Float_Model_instAdd___closed__0 = (const lean_object*)&l_Float_Model_instAdd___closed__0_value;
LEAN_EXPORT const lean_object* l_Float_Model_instAdd = (const lean_object*)&l_Float_Model_instAdd___closed__0_value;
static const lean_closure_object l_Float_Model_instSub___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_Model_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Float_Model_instSub___closed__0 = (const lean_object*)&l_Float_Model_instSub___closed__0_value;
LEAN_EXPORT const lean_object* l_Float_Model_instSub = (const lean_object*)&l_Float_Model_instSub___closed__0_value;
static const lean_closure_object l_Float_Model_instMul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_Model_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Float_Model_instMul___closed__0 = (const lean_object*)&l_Float_Model_instMul___closed__0_value;
LEAN_EXPORT const lean_object* l_Float_Model_instMul = (const lean_object*)&l_Float_Model_instMul___closed__0_value;
static const lean_closure_object l_Float_Model_instDiv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_Model_div___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Float_Model_instDiv___closed__0 = (const lean_object*)&l_Float_Model_instDiv___closed__0_value;
LEAN_EXPORT const lean_object* l_Float_Model_instDiv = (const lean_object*)&l_Float_Model_instDiv___closed__0_value;
LEAN_EXPORT uint64_t l_Float_Model_sqrt(uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_sqrt___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Float_Model_neg(uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_neg___boxed(lean_object*);
static const lean_closure_object l_Float_Model_instNeg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_Model_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Float_Model_instNeg___closed__0 = (const lean_object*)&l_Float_Model_instNeg___closed__0_value;
LEAN_EXPORT const lean_object* l_Float_Model_instNeg = (const lean_object*)&l_Float_Model_instNeg___closed__0_value;
LEAN_EXPORT uint64_t l_Float_Model_abs(uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_abs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_compare(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_compare___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Float_Model_le(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_le___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Float_Model_lt(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Float_Model_beq(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_instLE;
LEAN_EXPORT uint8_t l_Float_Model_instDecidableLE(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_instDecidableLE___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_instLT;
LEAN_EXPORT uint8_t l_Float_Model_instDecidableLT(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_instDecidableLT___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Float_Model_instBEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_Model_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Float_Model_instBEq___closed__0 = (const lean_object*)&l_Float_Model_instBEq___closed__0_value;
LEAN_EXPORT const lean_object* l_Float_Model_instBEq = (const lean_object*)&l_Float_Model_instBEq___closed__0_value;
LEAN_EXPORT uint64_t l_Float_Model_instMin___lam__0(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_instMin___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Float_Model_instMin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_Model_instMin___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Float_Model_instMin___closed__0 = (const lean_object*)&l_Float_Model_instMin___closed__0_value;
LEAN_EXPORT const lean_object* l_Float_Model_instMin = (const lean_object*)&l_Float_Model_instMin___closed__0_value;
LEAN_EXPORT uint64_t l_Float_Model_instMax___lam__0(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_instMax___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Float_Model_instMax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_Model_instMax___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Float_Model_instMax___closed__0 = (const lean_object*)&l_Float_Model_instMax___closed__0_value;
LEAN_EXPORT const lean_object* l_Float_Model_instMax = (const lean_object*)&l_Float_Model_instMax___closed__0_value;
LEAN_EXPORT uint8_t l_Float_Model_isFinite(uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_isFinite___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Float_Model_isInf(uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_isInf___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Float_Model_isNaN(uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_isNaN___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Float_Model_ofBits(uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_ofBits___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Float_Model_ofInt(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_ofInt___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Float_Model_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_ofNat___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Float_Model_ofUInt8(uint8_t);
LEAN_EXPORT lean_object* l_Float_Model_ofUInt8___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Float_Model_ofUInt16(uint16_t);
LEAN_EXPORT lean_object* l_Float_Model_ofUInt16___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Float_Model_ofUInt32(uint32_t);
LEAN_EXPORT lean_object* l_Float_Model_ofUInt32___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Float_Model_ofUInt64(uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_ofUInt64___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Float_Model_ofUSize(size_t);
LEAN_EXPORT lean_object* l_Float_Model_ofUSize___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Float_Model_ofInt8(uint8_t);
LEAN_EXPORT lean_object* l_Float_Model_ofInt8___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Float_Model_ofInt16(uint16_t);
LEAN_EXPORT lean_object* l_Float_Model_ofInt16___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Float_Model_ofInt32(uint32_t);
LEAN_EXPORT lean_object* l_Float_Model_ofInt32___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Float_Model_ofInt64(uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_ofInt64___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Float_Model_ofISize(size_t);
LEAN_EXPORT lean_object* l_Float_Model_ofISize___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Float_Model_toUInt8(uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_toUInt8___boxed(lean_object*);
LEAN_EXPORT uint16_t l_Float_Model_toUInt16(uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_toUInt16___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Float_Model_toUInt32(uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_toUInt32___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Float_Model_toUInt64(uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_toUInt64___boxed(lean_object*);
LEAN_EXPORT size_t l_Float_Model_toUSize(uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_toUSize___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Float_Model_toInt8(uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_toInt8___boxed(lean_object*);
LEAN_EXPORT uint16_t l_Float_Model_toInt16(uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_toInt16___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Float_Model_toInt32(uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_toInt32___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Float_Model_toInt64(uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_toInt64___boxed(lean_object*);
LEAN_EXPORT size_t l_Float_Model_toISize(uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_toISize___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Float_Model_ofScientific(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_ofScientific___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Float_Model_instInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Float_Model_instInhabited___closed__0;
LEAN_EXPORT uint64_t l_Float_Model_instInhabited;
LEAN_EXPORT lean_object* l_Float_Model_unpack(uint64_t v_f_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_5_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_6_ = lean_uint64_to_nat(v_f_4_);
v___x_7_ = l_Float_Model_UnpackedFloat_unpack(v___x_5_, v___x_6_);
lean_dec(v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_unpack___boxed(lean_object* v_f_8_){
_start:
{
uint64_t v_f_boxed_9_; lean_object* v_res_10_; 
v_f_boxed_9_ = lean_unbox_uint64(v_f_8_);
lean_dec_ref(v_f_8_);
v_res_10_ = l_Float_Model_unpack(v_f_boxed_9_);
return v_res_10_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_pack(lean_object* v_f_11_){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; uint64_t v___x_14_; 
v___x_12_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_13_ = l_Float_Model_UnpackedFloat_pack(v___x_12_, v_f_11_);
v___x_14_ = lean_uint64_of_nat_mk(v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_pack___boxed(lean_object* v_f_15_){
_start:
{
uint64_t v_res_16_; lean_object* v_r_17_; 
v_res_16_ = l_Float_Model_pack(v_f_15_);
lean_dec(v_f_15_);
v_r_17_ = lean_box_uint64(v_res_16_);
return v_r_17_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_add(uint64_t v_a_18_, uint64_t v_b_19_){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; uint64_t v___x_24_; 
v___x_20_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_21_ = l_Float_Model_unpack(v_a_18_);
v___x_22_ = l_Float_Model_unpack(v_b_19_);
v___x_23_ = l_Float_Model_UnpackedFloat_add(v___x_20_, v___x_21_, v___x_22_);
v___x_24_ = l_Float_Model_pack(v___x_23_);
lean_dec(v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_add___boxed(lean_object* v_a_25_, lean_object* v_b_26_){
_start:
{
uint64_t v_a_boxed_27_; uint64_t v_b_boxed_28_; uint64_t v_res_29_; lean_object* v_r_30_; 
v_a_boxed_27_ = lean_unbox_uint64(v_a_25_);
lean_dec_ref(v_a_25_);
v_b_boxed_28_ = lean_unbox_uint64(v_b_26_);
lean_dec_ref(v_b_26_);
v_res_29_ = l_Float_Model_add(v_a_boxed_27_, v_b_boxed_28_);
v_r_30_ = lean_box_uint64(v_res_29_);
return v_r_30_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_sub(uint64_t v_a_31_, uint64_t v_b_32_){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; uint64_t v___x_37_; 
v___x_33_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_34_ = l_Float_Model_unpack(v_a_31_);
v___x_35_ = l_Float_Model_unpack(v_b_32_);
v___x_36_ = l_Float_Model_UnpackedFloat_sub(v___x_33_, v___x_34_, v___x_35_);
v___x_37_ = l_Float_Model_pack(v___x_36_);
lean_dec(v___x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_sub___boxed(lean_object* v_a_38_, lean_object* v_b_39_){
_start:
{
uint64_t v_a_boxed_40_; uint64_t v_b_boxed_41_; uint64_t v_res_42_; lean_object* v_r_43_; 
v_a_boxed_40_ = lean_unbox_uint64(v_a_38_);
lean_dec_ref(v_a_38_);
v_b_boxed_41_ = lean_unbox_uint64(v_b_39_);
lean_dec_ref(v_b_39_);
v_res_42_ = l_Float_Model_sub(v_a_boxed_40_, v_b_boxed_41_);
v_r_43_ = lean_box_uint64(v_res_42_);
return v_r_43_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_mul(uint64_t v_a_44_, uint64_t v_b_45_){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; uint64_t v___x_50_; 
v___x_46_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_47_ = l_Float_Model_unpack(v_a_44_);
v___x_48_ = l_Float_Model_unpack(v_b_45_);
v___x_49_ = l_Float_Model_UnpackedFloat_mul(v___x_46_, v___x_47_, v___x_48_);
v___x_50_ = l_Float_Model_pack(v___x_49_);
lean_dec(v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_mul___boxed(lean_object* v_a_51_, lean_object* v_b_52_){
_start:
{
uint64_t v_a_boxed_53_; uint64_t v_b_boxed_54_; uint64_t v_res_55_; lean_object* v_r_56_; 
v_a_boxed_53_ = lean_unbox_uint64(v_a_51_);
lean_dec_ref(v_a_51_);
v_b_boxed_54_ = lean_unbox_uint64(v_b_52_);
lean_dec_ref(v_b_52_);
v_res_55_ = l_Float_Model_mul(v_a_boxed_53_, v_b_boxed_54_);
v_r_56_ = lean_box_uint64(v_res_55_);
return v_r_56_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_div(uint64_t v_a_57_, uint64_t v_b_58_){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; uint64_t v___x_63_; 
v___x_59_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_60_ = l_Float_Model_unpack(v_a_57_);
v___x_61_ = l_Float_Model_unpack(v_b_58_);
v___x_62_ = l_Float_Model_UnpackedFloat_div(v___x_59_, v___x_60_, v___x_61_);
v___x_63_ = l_Float_Model_pack(v___x_62_);
lean_dec(v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_div___boxed(lean_object* v_a_64_, lean_object* v_b_65_){
_start:
{
uint64_t v_a_boxed_66_; uint64_t v_b_boxed_67_; uint64_t v_res_68_; lean_object* v_r_69_; 
v_a_boxed_66_ = lean_unbox_uint64(v_a_64_);
lean_dec_ref(v_a_64_);
v_b_boxed_67_ = lean_unbox_uint64(v_b_65_);
lean_dec_ref(v_b_65_);
v_res_68_ = l_Float_Model_div(v_a_boxed_66_, v_b_boxed_67_);
v_r_69_ = lean_box_uint64(v_res_68_);
return v_r_69_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_sqrt(uint64_t v_a_78_){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; uint64_t v___x_82_; 
v___x_79_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_80_ = l_Float_Model_unpack(v_a_78_);
v___x_81_ = l_Float_Model_UnpackedFloat_sqrt(v___x_79_, v___x_80_);
lean_dec(v___x_80_);
v___x_82_ = l_Float_Model_pack(v___x_81_);
lean_dec(v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_sqrt___boxed(lean_object* v_a_83_){
_start:
{
uint64_t v_a_boxed_84_; uint64_t v_res_85_; lean_object* v_r_86_; 
v_a_boxed_84_ = lean_unbox_uint64(v_a_83_);
lean_dec_ref(v_a_83_);
v_res_85_ = l_Float_Model_sqrt(v_a_boxed_84_);
v_r_86_ = lean_box_uint64(v_res_85_);
return v_r_86_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_neg(uint64_t v_a_87_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; uint64_t v___x_90_; 
v___x_88_ = l_Float_Model_unpack(v_a_87_);
v___x_89_ = l_Float_Model_UnpackedFloat_neg(v___x_88_);
v___x_90_ = l_Float_Model_pack(v___x_89_);
lean_dec(v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_neg___boxed(lean_object* v_a_91_){
_start:
{
uint64_t v_a_boxed_92_; uint64_t v_res_93_; lean_object* v_r_94_; 
v_a_boxed_92_ = lean_unbox_uint64(v_a_91_);
lean_dec_ref(v_a_91_);
v_res_93_ = l_Float_Model_neg(v_a_boxed_92_);
v_r_94_ = lean_box_uint64(v_res_93_);
return v_r_94_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_abs(uint64_t v_a_97_){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; uint64_t v___x_100_; 
v___x_98_ = l_Float_Model_unpack(v_a_97_);
v___x_99_ = l_Float_Model_UnpackedFloat_abs(v___x_98_);
v___x_100_ = l_Float_Model_pack(v___x_99_);
lean_dec(v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_abs___boxed(lean_object* v_a_101_){
_start:
{
uint64_t v_a_boxed_102_; uint64_t v_res_103_; lean_object* v_r_104_; 
v_a_boxed_102_ = lean_unbox_uint64(v_a_101_);
lean_dec_ref(v_a_101_);
v_res_103_ = l_Float_Model_abs(v_a_boxed_102_);
v_r_104_ = lean_box_uint64(v_res_103_);
return v_r_104_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_compare(uint64_t v_a_105_, uint64_t v_b_106_){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_107_ = l_Float_Model_unpack(v_a_105_);
v___x_108_ = l_Float_Model_unpack(v_b_106_);
v___x_109_ = l_Float_Model_UnpackedFloat_compare(v___x_107_, v___x_108_);
lean_dec(v___x_108_);
lean_dec(v___x_107_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_compare___boxed(lean_object* v_a_110_, lean_object* v_b_111_){
_start:
{
uint64_t v_a_boxed_112_; uint64_t v_b_boxed_113_; lean_object* v_res_114_; 
v_a_boxed_112_ = lean_unbox_uint64(v_a_110_);
lean_dec_ref(v_a_110_);
v_b_boxed_113_ = lean_unbox_uint64(v_b_111_);
lean_dec_ref(v_b_111_);
v_res_114_ = l_Float_Model_compare(v_a_boxed_112_, v_b_boxed_113_);
return v_res_114_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_le(uint64_t v_a_115_, uint64_t v_b_116_){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_117_ = l_Float_Model_unpack(v_a_115_);
v___x_118_ = l_Float_Model_unpack(v_b_116_);
v___x_119_ = l_Float_Model_UnpackedFloat_le(v___x_117_, v___x_118_);
lean_dec(v___x_118_);
lean_dec(v___x_117_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_le___boxed(lean_object* v_a_120_, lean_object* v_b_121_){
_start:
{
uint64_t v_a_boxed_122_; uint64_t v_b_boxed_123_; uint8_t v_res_124_; lean_object* v_r_125_; 
v_a_boxed_122_ = lean_unbox_uint64(v_a_120_);
lean_dec_ref(v_a_120_);
v_b_boxed_123_ = lean_unbox_uint64(v_b_121_);
lean_dec_ref(v_b_121_);
v_res_124_ = l_Float_Model_le(v_a_boxed_122_, v_b_boxed_123_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_lt(uint64_t v_a_126_, uint64_t v_b_127_){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_128_ = l_Float_Model_unpack(v_a_126_);
v___x_129_ = l_Float_Model_unpack(v_b_127_);
v___x_130_ = l_Float_Model_UnpackedFloat_lt(v___x_128_, v___x_129_);
lean_dec(v___x_129_);
lean_dec(v___x_128_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_lt___boxed(lean_object* v_a_131_, lean_object* v_b_132_){
_start:
{
uint64_t v_a_boxed_133_; uint64_t v_b_boxed_134_; uint8_t v_res_135_; lean_object* v_r_136_; 
v_a_boxed_133_ = lean_unbox_uint64(v_a_131_);
lean_dec_ref(v_a_131_);
v_b_boxed_134_ = lean_unbox_uint64(v_b_132_);
lean_dec_ref(v_b_132_);
v_res_135_ = l_Float_Model_lt(v_a_boxed_133_, v_b_boxed_134_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_beq(uint64_t v_a_137_, uint64_t v_b_138_){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_139_ = l_Float_Model_unpack(v_a_137_);
v___x_140_ = l_Float_Model_unpack(v_b_138_);
v___x_141_ = l_Float_Model_UnpackedFloat_beq(v___x_139_, v___x_140_);
lean_dec(v___x_140_);
lean_dec(v___x_139_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_beq___boxed(lean_object* v_a_142_, lean_object* v_b_143_){
_start:
{
uint64_t v_a_boxed_144_; uint64_t v_b_boxed_145_; uint8_t v_res_146_; lean_object* v_r_147_; 
v_a_boxed_144_ = lean_unbox_uint64(v_a_142_);
lean_dec_ref(v_a_142_);
v_b_boxed_145_ = lean_unbox_uint64(v_b_143_);
lean_dec_ref(v_b_143_);
v_res_146_ = l_Float_Model_beq(v_a_boxed_144_, v_b_boxed_145_);
v_r_147_ = lean_box(v_res_146_);
return v_r_147_;
}
}
static lean_object* _init_l_Float_Model_instLE(void){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = lean_box(0);
return v___x_148_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_instDecidableLE(uint64_t v_a_149_, uint64_t v_b_150_){
_start:
{
uint8_t v___x_151_; 
v___x_151_ = l_Float_Model_le(v_a_149_, v_b_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_instDecidableLE___boxed(lean_object* v_a_152_, lean_object* v_b_153_){
_start:
{
uint64_t v_a_boxed_154_; uint64_t v_b_boxed_155_; uint8_t v_res_156_; lean_object* v_r_157_; 
v_a_boxed_154_ = lean_unbox_uint64(v_a_152_);
lean_dec_ref(v_a_152_);
v_b_boxed_155_ = lean_unbox_uint64(v_b_153_);
lean_dec_ref(v_b_153_);
v_res_156_ = l_Float_Model_instDecidableLE(v_a_boxed_154_, v_b_boxed_155_);
v_r_157_ = lean_box(v_res_156_);
return v_r_157_;
}
}
static lean_object* _init_l_Float_Model_instLT(void){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = lean_box(0);
return v___x_158_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_instDecidableLT(uint64_t v_a_159_, uint64_t v_b_160_){
_start:
{
uint8_t v___x_161_; 
v___x_161_ = l_Float_Model_lt(v_a_159_, v_b_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_instDecidableLT___boxed(lean_object* v_a_162_, lean_object* v_b_163_){
_start:
{
uint64_t v_a_boxed_164_; uint64_t v_b_boxed_165_; uint8_t v_res_166_; lean_object* v_r_167_; 
v_a_boxed_164_ = lean_unbox_uint64(v_a_162_);
lean_dec_ref(v_a_162_);
v_b_boxed_165_ = lean_unbox_uint64(v_b_163_);
lean_dec_ref(v_b_163_);
v_res_166_ = l_Float_Model_instDecidableLT(v_a_boxed_164_, v_b_boxed_165_);
v_r_167_ = lean_box(v_res_166_);
return v_r_167_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_instMin___lam__0(uint64_t v_a_170_, uint64_t v_b_171_){
_start:
{
uint8_t v___x_172_; 
v___x_172_ = l_Float_Model_le(v_a_170_, v_b_171_);
if (v___x_172_ == 0)
{
return v_b_171_;
}
else
{
return v_a_170_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_instMin___lam__0___boxed(lean_object* v_a_173_, lean_object* v_b_174_){
_start:
{
uint64_t v_a_boxed_175_; uint64_t v_b_boxed_176_; uint64_t v_res_177_; lean_object* v_r_178_; 
v_a_boxed_175_ = lean_unbox_uint64(v_a_173_);
lean_dec_ref(v_a_173_);
v_b_boxed_176_ = lean_unbox_uint64(v_b_174_);
lean_dec_ref(v_b_174_);
v_res_177_ = l_Float_Model_instMin___lam__0(v_a_boxed_175_, v_b_boxed_176_);
v_r_178_ = lean_box_uint64(v_res_177_);
return v_r_178_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_instMax___lam__0(uint64_t v_a_181_, uint64_t v_b_182_){
_start:
{
uint8_t v___x_183_; 
v___x_183_ = l_Float_Model_le(v_b_182_, v_a_181_);
if (v___x_183_ == 0)
{
return v_b_182_;
}
else
{
return v_a_181_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_instMax___lam__0___boxed(lean_object* v_a_184_, lean_object* v_b_185_){
_start:
{
uint64_t v_a_boxed_186_; uint64_t v_b_boxed_187_; uint64_t v_res_188_; lean_object* v_r_189_; 
v_a_boxed_186_ = lean_unbox_uint64(v_a_184_);
lean_dec_ref(v_a_184_);
v_b_boxed_187_ = lean_unbox_uint64(v_b_185_);
lean_dec_ref(v_b_185_);
v_res_188_ = l_Float_Model_instMax___lam__0(v_a_boxed_186_, v_b_boxed_187_);
v_r_189_ = lean_box_uint64(v_res_188_);
return v_r_189_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_isFinite(uint64_t v_a_192_){
_start:
{
lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = l_Float_Model_unpack(v_a_192_);
v___x_194_ = l_Float_Model_UnpackedFloat_isFinite(v___x_193_);
lean_dec(v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_isFinite___boxed(lean_object* v_a_195_){
_start:
{
uint64_t v_a_boxed_196_; uint8_t v_res_197_; lean_object* v_r_198_; 
v_a_boxed_196_ = lean_unbox_uint64(v_a_195_);
lean_dec_ref(v_a_195_);
v_res_197_ = l_Float_Model_isFinite(v_a_boxed_196_);
v_r_198_ = lean_box(v_res_197_);
return v_r_198_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_isInf(uint64_t v_a_199_){
_start:
{
lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_200_ = l_Float_Model_unpack(v_a_199_);
v___x_201_ = l_Float_Model_UnpackedFloat_isInf(v___x_200_);
lean_dec(v___x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_isInf___boxed(lean_object* v_a_202_){
_start:
{
uint64_t v_a_boxed_203_; uint8_t v_res_204_; lean_object* v_r_205_; 
v_a_boxed_203_ = lean_unbox_uint64(v_a_202_);
lean_dec_ref(v_a_202_);
v_res_204_ = l_Float_Model_isInf(v_a_boxed_203_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_isNaN(uint64_t v_a_206_){
_start:
{
lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_207_ = l_Float_Model_unpack(v_a_206_);
v___x_208_ = l_Float_Model_UnpackedFloat_isNaN(v___x_207_);
lean_dec(v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_isNaN___boxed(lean_object* v_a_209_){
_start:
{
uint64_t v_a_boxed_210_; uint8_t v_res_211_; lean_object* v_r_212_; 
v_a_boxed_210_ = lean_unbox_uint64(v_a_209_);
lean_dec_ref(v_a_209_);
v_res_211_ = l_Float_Model_isNaN(v_a_boxed_210_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofBits(uint64_t v_a_213_){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; uint64_t v___x_217_; 
v___x_214_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_215_ = lean_uint64_to_nat(v_a_213_);
v___x_216_ = l_Float_Model_UnpackedFloat_unpack(v___x_214_, v___x_215_);
lean_dec(v___x_215_);
v___x_217_ = l_Float_Model_pack(v___x_216_);
lean_dec(v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofBits___boxed(lean_object* v_a_218_){
_start:
{
uint64_t v_a_boxed_219_; uint64_t v_res_220_; lean_object* v_r_221_; 
v_a_boxed_219_ = lean_unbox_uint64(v_a_218_);
lean_dec_ref(v_a_218_);
v_res_220_ = l_Float_Model_ofBits(v_a_boxed_219_);
v_r_221_ = lean_box_uint64(v_res_220_);
return v_r_221_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofInt(lean_object* v_n_222_){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; uint64_t v___x_225_; 
v___x_223_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_224_ = l_Float_Model_UnpackedFloat_ofInt(v___x_223_, v_n_222_);
v___x_225_ = l_Float_Model_pack(v___x_224_);
lean_dec(v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofInt___boxed(lean_object* v_n_226_){
_start:
{
uint64_t v_res_227_; lean_object* v_r_228_; 
v_res_227_ = l_Float_Model_ofInt(v_n_226_);
lean_dec(v_n_226_);
v_r_228_ = lean_box_uint64(v_res_227_);
return v_r_228_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofNat(lean_object* v_n_229_){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; uint64_t v___x_232_; 
v___x_230_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_231_ = l_Float_Model_UnpackedFloat_ofNat(v___x_230_, v_n_229_);
v___x_232_ = l_Float_Model_pack(v___x_231_);
lean_dec(v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofNat___boxed(lean_object* v_n_233_){
_start:
{
uint64_t v_res_234_; lean_object* v_r_235_; 
v_res_234_ = l_Float_Model_ofNat(v_n_233_);
v_r_235_ = lean_box_uint64(v_res_234_);
return v_r_235_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofUInt8(uint8_t v_n_236_){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; uint64_t v___x_239_; 
v___x_237_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_238_ = l_Float_Model_UnpackedFloat_ofUInt8(v___x_237_, v_n_236_);
v___x_239_ = l_Float_Model_pack(v___x_238_);
lean_dec(v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofUInt8___boxed(lean_object* v_n_240_){
_start:
{
uint8_t v_n_boxed_241_; uint64_t v_res_242_; lean_object* v_r_243_; 
v_n_boxed_241_ = lean_unbox(v_n_240_);
v_res_242_ = l_Float_Model_ofUInt8(v_n_boxed_241_);
v_r_243_ = lean_box_uint64(v_res_242_);
return v_r_243_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofUInt16(uint16_t v_n_244_){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; uint64_t v___x_247_; 
v___x_245_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_246_ = l_Float_Model_UnpackedFloat_ofUInt16(v___x_245_, v_n_244_);
v___x_247_ = l_Float_Model_pack(v___x_246_);
lean_dec(v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofUInt16___boxed(lean_object* v_n_248_){
_start:
{
uint16_t v_n_boxed_249_; uint64_t v_res_250_; lean_object* v_r_251_; 
v_n_boxed_249_ = lean_unbox(v_n_248_);
v_res_250_ = l_Float_Model_ofUInt16(v_n_boxed_249_);
v_r_251_ = lean_box_uint64(v_res_250_);
return v_r_251_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofUInt32(uint32_t v_n_252_){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; uint64_t v___x_255_; 
v___x_253_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_254_ = l_Float_Model_UnpackedFloat_ofUInt32(v___x_253_, v_n_252_);
v___x_255_ = l_Float_Model_pack(v___x_254_);
lean_dec(v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofUInt32___boxed(lean_object* v_n_256_){
_start:
{
uint32_t v_n_boxed_257_; uint64_t v_res_258_; lean_object* v_r_259_; 
v_n_boxed_257_ = lean_unbox_uint32(v_n_256_);
lean_dec(v_n_256_);
v_res_258_ = l_Float_Model_ofUInt32(v_n_boxed_257_);
v_r_259_ = lean_box_uint64(v_res_258_);
return v_r_259_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofUInt64(uint64_t v_n_260_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; uint64_t v___x_263_; 
v___x_261_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_262_ = l_Float_Model_UnpackedFloat_ofUInt64(v___x_261_, v_n_260_);
v___x_263_ = l_Float_Model_pack(v___x_262_);
lean_dec(v___x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofUInt64___boxed(lean_object* v_n_264_){
_start:
{
uint64_t v_n_boxed_265_; uint64_t v_res_266_; lean_object* v_r_267_; 
v_n_boxed_265_ = lean_unbox_uint64(v_n_264_);
lean_dec_ref(v_n_264_);
v_res_266_ = l_Float_Model_ofUInt64(v_n_boxed_265_);
v_r_267_ = lean_box_uint64(v_res_266_);
return v_r_267_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofUSize(size_t v_n_268_){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; uint64_t v___x_271_; 
v___x_269_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_270_ = l_Float_Model_UnpackedFloat_ofUSize(v___x_269_, v_n_268_);
v___x_271_ = l_Float_Model_pack(v___x_270_);
lean_dec(v___x_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofUSize___boxed(lean_object* v_n_272_){
_start:
{
size_t v_n_boxed_273_; uint64_t v_res_274_; lean_object* v_r_275_; 
v_n_boxed_273_ = lean_unbox_usize(v_n_272_);
lean_dec(v_n_272_);
v_res_274_ = l_Float_Model_ofUSize(v_n_boxed_273_);
v_r_275_ = lean_box_uint64(v_res_274_);
return v_r_275_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofInt8(uint8_t v_n_276_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; uint64_t v___x_279_; 
v___x_277_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_278_ = l_Float_Model_UnpackedFloat_ofInt8(v___x_277_, v_n_276_);
v___x_279_ = l_Float_Model_pack(v___x_278_);
lean_dec(v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofInt8___boxed(lean_object* v_n_280_){
_start:
{
uint8_t v_n_boxed_281_; uint64_t v_res_282_; lean_object* v_r_283_; 
v_n_boxed_281_ = lean_unbox(v_n_280_);
v_res_282_ = l_Float_Model_ofInt8(v_n_boxed_281_);
v_r_283_ = lean_box_uint64(v_res_282_);
return v_r_283_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofInt16(uint16_t v_n_284_){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; uint64_t v___x_287_; 
v___x_285_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_286_ = l_Float_Model_UnpackedFloat_ofInt16(v___x_285_, v_n_284_);
v___x_287_ = l_Float_Model_pack(v___x_286_);
lean_dec(v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofInt16___boxed(lean_object* v_n_288_){
_start:
{
uint16_t v_n_boxed_289_; uint64_t v_res_290_; lean_object* v_r_291_; 
v_n_boxed_289_ = lean_unbox(v_n_288_);
v_res_290_ = l_Float_Model_ofInt16(v_n_boxed_289_);
v_r_291_ = lean_box_uint64(v_res_290_);
return v_r_291_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofInt32(uint32_t v_n_292_){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; uint64_t v___x_295_; 
v___x_293_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_294_ = l_Float_Model_UnpackedFloat_ofInt32(v___x_293_, v_n_292_);
v___x_295_ = l_Float_Model_pack(v___x_294_);
lean_dec(v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofInt32___boxed(lean_object* v_n_296_){
_start:
{
uint32_t v_n_boxed_297_; uint64_t v_res_298_; lean_object* v_r_299_; 
v_n_boxed_297_ = lean_unbox_uint32(v_n_296_);
lean_dec(v_n_296_);
v_res_298_ = l_Float_Model_ofInt32(v_n_boxed_297_);
v_r_299_ = lean_box_uint64(v_res_298_);
return v_r_299_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofInt64(uint64_t v_n_300_){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; uint64_t v___x_303_; 
v___x_301_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_302_ = l_Float_Model_UnpackedFloat_ofInt64(v___x_301_, v_n_300_);
v___x_303_ = l_Float_Model_pack(v___x_302_);
lean_dec(v___x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofInt64___boxed(lean_object* v_n_304_){
_start:
{
uint64_t v_n_boxed_305_; uint64_t v_res_306_; lean_object* v_r_307_; 
v_n_boxed_305_ = lean_unbox_uint64(v_n_304_);
lean_dec_ref(v_n_304_);
v_res_306_ = l_Float_Model_ofInt64(v_n_boxed_305_);
v_r_307_ = lean_box_uint64(v_res_306_);
return v_r_307_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofISize(size_t v_n_308_){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; uint64_t v___x_311_; 
v___x_309_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_310_ = l_Float_Model_UnpackedFloat_ofISize(v___x_309_, v_n_308_);
v___x_311_ = l_Float_Model_pack(v___x_310_);
lean_dec(v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofISize___boxed(lean_object* v_n_312_){
_start:
{
size_t v_n_boxed_313_; uint64_t v_res_314_; lean_object* v_r_315_; 
v_n_boxed_313_ = lean_unbox_usize(v_n_312_);
lean_dec(v_n_312_);
v_res_314_ = l_Float_Model_ofISize(v_n_boxed_313_);
v_r_315_ = lean_box_uint64(v_res_314_);
return v_r_315_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_toUInt8(uint64_t v_f_316_){
_start:
{
lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_317_ = l_Float_Model_unpack(v_f_316_);
v___x_318_ = l_Float_Model_UnpackedFloat_toUInt8(v___x_317_);
lean_dec(v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toUInt8___boxed(lean_object* v_f_319_){
_start:
{
uint64_t v_f_boxed_320_; uint8_t v_res_321_; lean_object* v_r_322_; 
v_f_boxed_320_ = lean_unbox_uint64(v_f_319_);
lean_dec_ref(v_f_319_);
v_res_321_ = l_Float_Model_toUInt8(v_f_boxed_320_);
v_r_322_ = lean_box(v_res_321_);
return v_r_322_;
}
}
LEAN_EXPORT uint16_t l_Float_Model_toUInt16(uint64_t v_f_323_){
_start:
{
lean_object* v___x_324_; uint16_t v___x_325_; 
v___x_324_ = l_Float_Model_unpack(v_f_323_);
v___x_325_ = l_Float_Model_UnpackedFloat_toUInt16(v___x_324_);
lean_dec(v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toUInt16___boxed(lean_object* v_f_326_){
_start:
{
uint64_t v_f_boxed_327_; uint16_t v_res_328_; lean_object* v_r_329_; 
v_f_boxed_327_ = lean_unbox_uint64(v_f_326_);
lean_dec_ref(v_f_326_);
v_res_328_ = l_Float_Model_toUInt16(v_f_boxed_327_);
v_r_329_ = lean_box(v_res_328_);
return v_r_329_;
}
}
LEAN_EXPORT uint32_t l_Float_Model_toUInt32(uint64_t v_f_330_){
_start:
{
lean_object* v___x_331_; uint32_t v___x_332_; 
v___x_331_ = l_Float_Model_unpack(v_f_330_);
v___x_332_ = l_Float_Model_UnpackedFloat_toUInt32(v___x_331_);
lean_dec(v___x_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toUInt32___boxed(lean_object* v_f_333_){
_start:
{
uint64_t v_f_boxed_334_; uint32_t v_res_335_; lean_object* v_r_336_; 
v_f_boxed_334_ = lean_unbox_uint64(v_f_333_);
lean_dec_ref(v_f_333_);
v_res_335_ = l_Float_Model_toUInt32(v_f_boxed_334_);
v_r_336_ = lean_box_uint32(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_toUInt64(uint64_t v_f_337_){
_start:
{
lean_object* v___x_338_; uint64_t v___x_339_; 
v___x_338_ = l_Float_Model_unpack(v_f_337_);
v___x_339_ = l_Float_Model_UnpackedFloat_toUInt64(v___x_338_);
lean_dec(v___x_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toUInt64___boxed(lean_object* v_f_340_){
_start:
{
uint64_t v_f_boxed_341_; uint64_t v_res_342_; lean_object* v_r_343_; 
v_f_boxed_341_ = lean_unbox_uint64(v_f_340_);
lean_dec_ref(v_f_340_);
v_res_342_ = l_Float_Model_toUInt64(v_f_boxed_341_);
v_r_343_ = lean_box_uint64(v_res_342_);
return v_r_343_;
}
}
LEAN_EXPORT size_t l_Float_Model_toUSize(uint64_t v_f_344_){
_start:
{
lean_object* v___x_345_; size_t v___x_346_; 
v___x_345_ = l_Float_Model_unpack(v_f_344_);
v___x_346_ = l_Float_Model_UnpackedFloat_toUSize(v___x_345_);
lean_dec(v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toUSize___boxed(lean_object* v_f_347_){
_start:
{
uint64_t v_f_boxed_348_; size_t v_res_349_; lean_object* v_r_350_; 
v_f_boxed_348_ = lean_unbox_uint64(v_f_347_);
lean_dec_ref(v_f_347_);
v_res_349_ = l_Float_Model_toUSize(v_f_boxed_348_);
v_r_350_ = lean_box_usize(v_res_349_);
return v_r_350_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_toInt8(uint64_t v_f_351_){
_start:
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = l_Float_Model_unpack(v_f_351_);
v___x_353_ = l_Float_Model_UnpackedFloat_toInt8(v___x_352_);
lean_dec(v___x_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toInt8___boxed(lean_object* v_f_354_){
_start:
{
uint64_t v_f_boxed_355_; uint8_t v_res_356_; lean_object* v_r_357_; 
v_f_boxed_355_ = lean_unbox_uint64(v_f_354_);
lean_dec_ref(v_f_354_);
v_res_356_ = l_Float_Model_toInt8(v_f_boxed_355_);
v_r_357_ = lean_box(v_res_356_);
return v_r_357_;
}
}
LEAN_EXPORT uint16_t l_Float_Model_toInt16(uint64_t v_f_358_){
_start:
{
lean_object* v___x_359_; uint16_t v___x_360_; 
v___x_359_ = l_Float_Model_unpack(v_f_358_);
v___x_360_ = l_Float_Model_UnpackedFloat_toInt16(v___x_359_);
lean_dec(v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toInt16___boxed(lean_object* v_f_361_){
_start:
{
uint64_t v_f_boxed_362_; uint16_t v_res_363_; lean_object* v_r_364_; 
v_f_boxed_362_ = lean_unbox_uint64(v_f_361_);
lean_dec_ref(v_f_361_);
v_res_363_ = l_Float_Model_toInt16(v_f_boxed_362_);
v_r_364_ = lean_box(v_res_363_);
return v_r_364_;
}
}
LEAN_EXPORT uint32_t l_Float_Model_toInt32(uint64_t v_f_365_){
_start:
{
lean_object* v___x_366_; uint32_t v___x_367_; 
v___x_366_ = l_Float_Model_unpack(v_f_365_);
v___x_367_ = l_Float_Model_UnpackedFloat_toInt32(v___x_366_);
lean_dec(v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toInt32___boxed(lean_object* v_f_368_){
_start:
{
uint64_t v_f_boxed_369_; uint32_t v_res_370_; lean_object* v_r_371_; 
v_f_boxed_369_ = lean_unbox_uint64(v_f_368_);
lean_dec_ref(v_f_368_);
v_res_370_ = l_Float_Model_toInt32(v_f_boxed_369_);
v_r_371_ = lean_box_uint32(v_res_370_);
return v_r_371_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_toInt64(uint64_t v_f_372_){
_start:
{
lean_object* v___x_373_; uint64_t v___x_374_; 
v___x_373_ = l_Float_Model_unpack(v_f_372_);
v___x_374_ = l_Float_Model_UnpackedFloat_toInt64(v___x_373_);
lean_dec(v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toInt64___boxed(lean_object* v_f_375_){
_start:
{
uint64_t v_f_boxed_376_; uint64_t v_res_377_; lean_object* v_r_378_; 
v_f_boxed_376_ = lean_unbox_uint64(v_f_375_);
lean_dec_ref(v_f_375_);
v_res_377_ = l_Float_Model_toInt64(v_f_boxed_376_);
v_r_378_ = lean_box_uint64(v_res_377_);
return v_r_378_;
}
}
LEAN_EXPORT size_t l_Float_Model_toISize(uint64_t v_f_379_){
_start:
{
lean_object* v___x_380_; size_t v___x_381_; 
v___x_380_ = l_Float_Model_unpack(v_f_379_);
v___x_381_ = l_Float_Model_UnpackedFloat_toISize(v___x_380_);
lean_dec(v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toISize___boxed(lean_object* v_f_382_){
_start:
{
uint64_t v_f_boxed_383_; size_t v_res_384_; lean_object* v_r_385_; 
v_f_boxed_383_ = lean_unbox_uint64(v_f_382_);
lean_dec_ref(v_f_382_);
v_res_384_ = l_Float_Model_toISize(v_f_boxed_383_);
v_r_385_ = lean_box_usize(v_res_384_);
return v_r_385_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofScientific(lean_object* v_m_386_, lean_object* v_e_387_){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; uint64_t v___x_390_; 
v___x_388_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_389_ = l_Float_Model_UnpackedFloat_ofScientific(v___x_388_, v_m_386_, v_e_387_);
v___x_390_ = l_Float_Model_pack(v___x_389_);
lean_dec(v___x_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofScientific___boxed(lean_object* v_m_391_, lean_object* v_e_392_){
_start:
{
uint64_t v_res_393_; lean_object* v_r_394_; 
v_res_393_ = l_Float_Model_ofScientific(v_m_391_, v_e_392_);
lean_dec(v_e_392_);
v_r_394_ = lean_box_uint64(v_res_393_);
return v_r_394_;
}
}
static uint64_t _init_l_Float_Model_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_395_; uint64_t v___x_396_; 
v___x_395_ = lean_unsigned_to_nat(0u);
v___x_396_ = l_Float_Model_ofNat(v___x_395_);
return v___x_396_;
}
}
static uint64_t _init_l_Float_Model_instInhabited(void){
_start:
{
uint64_t v___x_397_; 
v___x_397_ = lean_uint64_once(&l_Float_Model_instInhabited___closed__0, &l_Float_Model_instInhabited___closed__0_once, _init_l_Float_Model_instInhabited___closed__0);
return v___x_397_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Format_Valid(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Pack_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Operations(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Factories(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Float(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Float_Model_Format_Valid(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Pack_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Operations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Factories(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Float_Model_instLE = _init_l_Float_Model_instLE();
lean_mark_persistent(l_Float_Model_instLE);
l_Float_Model_instLT = _init_l_Float_Model_instLT();
lean_mark_persistent(l_Float_Model_instLT);
l_Float_Model_instInhabited = _init_l_Float_Model_instInhabited();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Float_Model_Float(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Float_Model_Format_Valid(uint8_t builtin);
lean_object* initialize_Init_Data_Float_Model_Unpacked_Pack_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Float_Model_Unpacked_Operations(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Factories(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Float_Model_Float(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float_Model_Format_Valid(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Float_Model_Unpacked_Pack_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Float_Model_Unpacked_Operations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Factories(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Model_Float(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Float_Model_Float(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Float_Model_Float(builtin);
}
#ifdef __cplusplus
}
#endif
