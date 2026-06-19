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
lean_object* l_Float_Model_UnpackedFloat_neg(lean_object*);
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
LEAN_EXPORT uint64_t l_Float_Model_abs(uint64_t v_a_95_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; uint64_t v___x_98_; 
v___x_96_ = l_Float_Model_unpack(v_a_95_);
v___x_97_ = l_Float_Model_UnpackedFloat_abs(v___x_96_);
v___x_98_ = l_Float_Model_pack(v___x_97_);
lean_dec(v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_abs___boxed(lean_object* v_a_99_){
_start:
{
uint64_t v_a_boxed_100_; uint64_t v_res_101_; lean_object* v_r_102_; 
v_a_boxed_100_ = lean_unbox_uint64(v_a_99_);
lean_dec_ref(v_a_99_);
v_res_101_ = l_Float_Model_abs(v_a_boxed_100_);
v_r_102_ = lean_box_uint64(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_compare(uint64_t v_a_103_, uint64_t v_b_104_){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_105_ = l_Float_Model_unpack(v_a_103_);
v___x_106_ = l_Float_Model_unpack(v_b_104_);
v___x_107_ = l_Float_Model_UnpackedFloat_compare(v___x_105_, v___x_106_);
lean_dec(v___x_106_);
lean_dec(v___x_105_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_compare___boxed(lean_object* v_a_108_, lean_object* v_b_109_){
_start:
{
uint64_t v_a_boxed_110_; uint64_t v_b_boxed_111_; lean_object* v_res_112_; 
v_a_boxed_110_ = lean_unbox_uint64(v_a_108_);
lean_dec_ref(v_a_108_);
v_b_boxed_111_ = lean_unbox_uint64(v_b_109_);
lean_dec_ref(v_b_109_);
v_res_112_ = l_Float_Model_compare(v_a_boxed_110_, v_b_boxed_111_);
return v_res_112_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_le(uint64_t v_a_113_, uint64_t v_b_114_){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_115_ = l_Float_Model_unpack(v_a_113_);
v___x_116_ = l_Float_Model_unpack(v_b_114_);
v___x_117_ = l_Float_Model_UnpackedFloat_le(v___x_115_, v___x_116_);
lean_dec(v___x_116_);
lean_dec(v___x_115_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_le___boxed(lean_object* v_a_118_, lean_object* v_b_119_){
_start:
{
uint64_t v_a_boxed_120_; uint64_t v_b_boxed_121_; uint8_t v_res_122_; lean_object* v_r_123_; 
v_a_boxed_120_ = lean_unbox_uint64(v_a_118_);
lean_dec_ref(v_a_118_);
v_b_boxed_121_ = lean_unbox_uint64(v_b_119_);
lean_dec_ref(v_b_119_);
v_res_122_ = l_Float_Model_le(v_a_boxed_120_, v_b_boxed_121_);
v_r_123_ = lean_box(v_res_122_);
return v_r_123_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_lt(uint64_t v_a_124_, uint64_t v_b_125_){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_126_ = l_Float_Model_unpack(v_a_124_);
v___x_127_ = l_Float_Model_unpack(v_b_125_);
v___x_128_ = l_Float_Model_UnpackedFloat_lt(v___x_126_, v___x_127_);
lean_dec(v___x_127_);
lean_dec(v___x_126_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_lt___boxed(lean_object* v_a_129_, lean_object* v_b_130_){
_start:
{
uint64_t v_a_boxed_131_; uint64_t v_b_boxed_132_; uint8_t v_res_133_; lean_object* v_r_134_; 
v_a_boxed_131_ = lean_unbox_uint64(v_a_129_);
lean_dec_ref(v_a_129_);
v_b_boxed_132_ = lean_unbox_uint64(v_b_130_);
lean_dec_ref(v_b_130_);
v_res_133_ = l_Float_Model_lt(v_a_boxed_131_, v_b_boxed_132_);
v_r_134_ = lean_box(v_res_133_);
return v_r_134_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_beq(uint64_t v_a_135_, uint64_t v_b_136_){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_137_ = l_Float_Model_unpack(v_a_135_);
v___x_138_ = l_Float_Model_unpack(v_b_136_);
v___x_139_ = l_Float_Model_UnpackedFloat_beq(v___x_137_, v___x_138_);
lean_dec(v___x_138_);
lean_dec(v___x_137_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_beq___boxed(lean_object* v_a_140_, lean_object* v_b_141_){
_start:
{
uint64_t v_a_boxed_142_; uint64_t v_b_boxed_143_; uint8_t v_res_144_; lean_object* v_r_145_; 
v_a_boxed_142_ = lean_unbox_uint64(v_a_140_);
lean_dec_ref(v_a_140_);
v_b_boxed_143_ = lean_unbox_uint64(v_b_141_);
lean_dec_ref(v_b_141_);
v_res_144_ = l_Float_Model_beq(v_a_boxed_142_, v_b_boxed_143_);
v_r_145_ = lean_box(v_res_144_);
return v_r_145_;
}
}
static lean_object* _init_l_Float_Model_instLE(void){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = lean_box(0);
return v___x_146_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_instDecidableLE(uint64_t v_a_147_, uint64_t v_b_148_){
_start:
{
uint8_t v___x_149_; 
v___x_149_ = l_Float_Model_le(v_a_147_, v_b_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_instDecidableLE___boxed(lean_object* v_a_150_, lean_object* v_b_151_){
_start:
{
uint64_t v_a_boxed_152_; uint64_t v_b_boxed_153_; uint8_t v_res_154_; lean_object* v_r_155_; 
v_a_boxed_152_ = lean_unbox_uint64(v_a_150_);
lean_dec_ref(v_a_150_);
v_b_boxed_153_ = lean_unbox_uint64(v_b_151_);
lean_dec_ref(v_b_151_);
v_res_154_ = l_Float_Model_instDecidableLE(v_a_boxed_152_, v_b_boxed_153_);
v_r_155_ = lean_box(v_res_154_);
return v_r_155_;
}
}
static lean_object* _init_l_Float_Model_instLT(void){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = lean_box(0);
return v___x_156_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_instDecidableLT(uint64_t v_a_157_, uint64_t v_b_158_){
_start:
{
uint8_t v___x_159_; 
v___x_159_ = l_Float_Model_lt(v_a_157_, v_b_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_instDecidableLT___boxed(lean_object* v_a_160_, lean_object* v_b_161_){
_start:
{
uint64_t v_a_boxed_162_; uint64_t v_b_boxed_163_; uint8_t v_res_164_; lean_object* v_r_165_; 
v_a_boxed_162_ = lean_unbox_uint64(v_a_160_);
lean_dec_ref(v_a_160_);
v_b_boxed_163_ = lean_unbox_uint64(v_b_161_);
lean_dec_ref(v_b_161_);
v_res_164_ = l_Float_Model_instDecidableLT(v_a_boxed_162_, v_b_boxed_163_);
v_r_165_ = lean_box(v_res_164_);
return v_r_165_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_instMin___lam__0(uint64_t v_a_168_, uint64_t v_b_169_){
_start:
{
uint8_t v___x_170_; 
v___x_170_ = l_Float_Model_le(v_a_168_, v_b_169_);
if (v___x_170_ == 0)
{
return v_b_169_;
}
else
{
return v_a_168_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_instMin___lam__0___boxed(lean_object* v_a_171_, lean_object* v_b_172_){
_start:
{
uint64_t v_a_boxed_173_; uint64_t v_b_boxed_174_; uint64_t v_res_175_; lean_object* v_r_176_; 
v_a_boxed_173_ = lean_unbox_uint64(v_a_171_);
lean_dec_ref(v_a_171_);
v_b_boxed_174_ = lean_unbox_uint64(v_b_172_);
lean_dec_ref(v_b_172_);
v_res_175_ = l_Float_Model_instMin___lam__0(v_a_boxed_173_, v_b_boxed_174_);
v_r_176_ = lean_box_uint64(v_res_175_);
return v_r_176_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_instMax___lam__0(uint64_t v_a_179_, uint64_t v_b_180_){
_start:
{
uint8_t v___x_181_; 
v___x_181_ = l_Float_Model_le(v_b_180_, v_a_179_);
if (v___x_181_ == 0)
{
return v_b_180_;
}
else
{
return v_a_179_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_instMax___lam__0___boxed(lean_object* v_a_182_, lean_object* v_b_183_){
_start:
{
uint64_t v_a_boxed_184_; uint64_t v_b_boxed_185_; uint64_t v_res_186_; lean_object* v_r_187_; 
v_a_boxed_184_ = lean_unbox_uint64(v_a_182_);
lean_dec_ref(v_a_182_);
v_b_boxed_185_ = lean_unbox_uint64(v_b_183_);
lean_dec_ref(v_b_183_);
v_res_186_ = l_Float_Model_instMax___lam__0(v_a_boxed_184_, v_b_boxed_185_);
v_r_187_ = lean_box_uint64(v_res_186_);
return v_r_187_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_isFinite(uint64_t v_a_190_){
_start:
{
lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_191_ = l_Float_Model_unpack(v_a_190_);
v___x_192_ = l_Float_Model_UnpackedFloat_isFinite(v___x_191_);
lean_dec(v___x_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_isFinite___boxed(lean_object* v_a_193_){
_start:
{
uint64_t v_a_boxed_194_; uint8_t v_res_195_; lean_object* v_r_196_; 
v_a_boxed_194_ = lean_unbox_uint64(v_a_193_);
lean_dec_ref(v_a_193_);
v_res_195_ = l_Float_Model_isFinite(v_a_boxed_194_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_isInf(uint64_t v_a_197_){
_start:
{
lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_198_ = l_Float_Model_unpack(v_a_197_);
v___x_199_ = l_Float_Model_UnpackedFloat_isInf(v___x_198_);
lean_dec(v___x_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_isInf___boxed(lean_object* v_a_200_){
_start:
{
uint64_t v_a_boxed_201_; uint8_t v_res_202_; lean_object* v_r_203_; 
v_a_boxed_201_ = lean_unbox_uint64(v_a_200_);
lean_dec_ref(v_a_200_);
v_res_202_ = l_Float_Model_isInf(v_a_boxed_201_);
v_r_203_ = lean_box(v_res_202_);
return v_r_203_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_isNaN(uint64_t v_a_204_){
_start:
{
lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_205_ = l_Float_Model_unpack(v_a_204_);
v___x_206_ = l_Float_Model_UnpackedFloat_isNaN(v___x_205_);
lean_dec(v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_isNaN___boxed(lean_object* v_a_207_){
_start:
{
uint64_t v_a_boxed_208_; uint8_t v_res_209_; lean_object* v_r_210_; 
v_a_boxed_208_ = lean_unbox_uint64(v_a_207_);
lean_dec_ref(v_a_207_);
v_res_209_ = l_Float_Model_isNaN(v_a_boxed_208_);
v_r_210_ = lean_box(v_res_209_);
return v_r_210_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofBits(uint64_t v_a_211_){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; uint64_t v___x_215_; 
v___x_212_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_213_ = lean_uint64_to_nat(v_a_211_);
v___x_214_ = l_Float_Model_UnpackedFloat_unpack(v___x_212_, v___x_213_);
lean_dec(v___x_213_);
v___x_215_ = l_Float_Model_pack(v___x_214_);
lean_dec(v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofBits___boxed(lean_object* v_a_216_){
_start:
{
uint64_t v_a_boxed_217_; uint64_t v_res_218_; lean_object* v_r_219_; 
v_a_boxed_217_ = lean_unbox_uint64(v_a_216_);
lean_dec_ref(v_a_216_);
v_res_218_ = l_Float_Model_ofBits(v_a_boxed_217_);
v_r_219_ = lean_box_uint64(v_res_218_);
return v_r_219_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofInt(lean_object* v_n_220_){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; uint64_t v___x_223_; 
v___x_221_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_222_ = l_Float_Model_UnpackedFloat_ofInt(v___x_221_, v_n_220_);
v___x_223_ = l_Float_Model_pack(v___x_222_);
lean_dec(v___x_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofInt___boxed(lean_object* v_n_224_){
_start:
{
uint64_t v_res_225_; lean_object* v_r_226_; 
v_res_225_ = l_Float_Model_ofInt(v_n_224_);
lean_dec(v_n_224_);
v_r_226_ = lean_box_uint64(v_res_225_);
return v_r_226_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofNat(lean_object* v_n_227_){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; uint64_t v___x_230_; 
v___x_228_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_229_ = l_Float_Model_UnpackedFloat_ofNat(v___x_228_, v_n_227_);
v___x_230_ = l_Float_Model_pack(v___x_229_);
lean_dec(v___x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofNat___boxed(lean_object* v_n_231_){
_start:
{
uint64_t v_res_232_; lean_object* v_r_233_; 
v_res_232_ = l_Float_Model_ofNat(v_n_231_);
v_r_233_ = lean_box_uint64(v_res_232_);
return v_r_233_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofUInt8(uint8_t v_n_234_){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; uint64_t v___x_237_; 
v___x_235_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_236_ = l_Float_Model_UnpackedFloat_ofUInt8(v___x_235_, v_n_234_);
v___x_237_ = l_Float_Model_pack(v___x_236_);
lean_dec(v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofUInt8___boxed(lean_object* v_n_238_){
_start:
{
uint8_t v_n_boxed_239_; uint64_t v_res_240_; lean_object* v_r_241_; 
v_n_boxed_239_ = lean_unbox(v_n_238_);
v_res_240_ = l_Float_Model_ofUInt8(v_n_boxed_239_);
v_r_241_ = lean_box_uint64(v_res_240_);
return v_r_241_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofUInt16(uint16_t v_n_242_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; uint64_t v___x_245_; 
v___x_243_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_244_ = l_Float_Model_UnpackedFloat_ofUInt16(v___x_243_, v_n_242_);
v___x_245_ = l_Float_Model_pack(v___x_244_);
lean_dec(v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofUInt16___boxed(lean_object* v_n_246_){
_start:
{
uint16_t v_n_boxed_247_; uint64_t v_res_248_; lean_object* v_r_249_; 
v_n_boxed_247_ = lean_unbox(v_n_246_);
v_res_248_ = l_Float_Model_ofUInt16(v_n_boxed_247_);
v_r_249_ = lean_box_uint64(v_res_248_);
return v_r_249_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofUInt32(uint32_t v_n_250_){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; uint64_t v___x_253_; 
v___x_251_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_252_ = l_Float_Model_UnpackedFloat_ofUInt32(v___x_251_, v_n_250_);
v___x_253_ = l_Float_Model_pack(v___x_252_);
lean_dec(v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofUInt32___boxed(lean_object* v_n_254_){
_start:
{
uint32_t v_n_boxed_255_; uint64_t v_res_256_; lean_object* v_r_257_; 
v_n_boxed_255_ = lean_unbox_uint32(v_n_254_);
lean_dec(v_n_254_);
v_res_256_ = l_Float_Model_ofUInt32(v_n_boxed_255_);
v_r_257_ = lean_box_uint64(v_res_256_);
return v_r_257_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofUInt64(uint64_t v_n_258_){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; uint64_t v___x_261_; 
v___x_259_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_260_ = l_Float_Model_UnpackedFloat_ofUInt64(v___x_259_, v_n_258_);
v___x_261_ = l_Float_Model_pack(v___x_260_);
lean_dec(v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofUInt64___boxed(lean_object* v_n_262_){
_start:
{
uint64_t v_n_boxed_263_; uint64_t v_res_264_; lean_object* v_r_265_; 
v_n_boxed_263_ = lean_unbox_uint64(v_n_262_);
lean_dec_ref(v_n_262_);
v_res_264_ = l_Float_Model_ofUInt64(v_n_boxed_263_);
v_r_265_ = lean_box_uint64(v_res_264_);
return v_r_265_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofUSize(size_t v_n_266_){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; uint64_t v___x_269_; 
v___x_267_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_268_ = l_Float_Model_UnpackedFloat_ofUSize(v___x_267_, v_n_266_);
v___x_269_ = l_Float_Model_pack(v___x_268_);
lean_dec(v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofUSize___boxed(lean_object* v_n_270_){
_start:
{
size_t v_n_boxed_271_; uint64_t v_res_272_; lean_object* v_r_273_; 
v_n_boxed_271_ = lean_unbox_usize(v_n_270_);
lean_dec(v_n_270_);
v_res_272_ = l_Float_Model_ofUSize(v_n_boxed_271_);
v_r_273_ = lean_box_uint64(v_res_272_);
return v_r_273_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofInt8(uint8_t v_n_274_){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; uint64_t v___x_277_; 
v___x_275_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_276_ = l_Float_Model_UnpackedFloat_ofInt8(v___x_275_, v_n_274_);
v___x_277_ = l_Float_Model_pack(v___x_276_);
lean_dec(v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofInt8___boxed(lean_object* v_n_278_){
_start:
{
uint8_t v_n_boxed_279_; uint64_t v_res_280_; lean_object* v_r_281_; 
v_n_boxed_279_ = lean_unbox(v_n_278_);
v_res_280_ = l_Float_Model_ofInt8(v_n_boxed_279_);
v_r_281_ = lean_box_uint64(v_res_280_);
return v_r_281_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofInt16(uint16_t v_n_282_){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; uint64_t v___x_285_; 
v___x_283_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_284_ = l_Float_Model_UnpackedFloat_ofInt16(v___x_283_, v_n_282_);
v___x_285_ = l_Float_Model_pack(v___x_284_);
lean_dec(v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofInt16___boxed(lean_object* v_n_286_){
_start:
{
uint16_t v_n_boxed_287_; uint64_t v_res_288_; lean_object* v_r_289_; 
v_n_boxed_287_ = lean_unbox(v_n_286_);
v_res_288_ = l_Float_Model_ofInt16(v_n_boxed_287_);
v_r_289_ = lean_box_uint64(v_res_288_);
return v_r_289_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofInt32(uint32_t v_n_290_){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; uint64_t v___x_293_; 
v___x_291_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_292_ = l_Float_Model_UnpackedFloat_ofInt32(v___x_291_, v_n_290_);
v___x_293_ = l_Float_Model_pack(v___x_292_);
lean_dec(v___x_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofInt32___boxed(lean_object* v_n_294_){
_start:
{
uint32_t v_n_boxed_295_; uint64_t v_res_296_; lean_object* v_r_297_; 
v_n_boxed_295_ = lean_unbox_uint32(v_n_294_);
lean_dec(v_n_294_);
v_res_296_ = l_Float_Model_ofInt32(v_n_boxed_295_);
v_r_297_ = lean_box_uint64(v_res_296_);
return v_r_297_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofInt64(uint64_t v_n_298_){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; uint64_t v___x_301_; 
v___x_299_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_300_ = l_Float_Model_UnpackedFloat_ofInt64(v___x_299_, v_n_298_);
v___x_301_ = l_Float_Model_pack(v___x_300_);
lean_dec(v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofInt64___boxed(lean_object* v_n_302_){
_start:
{
uint64_t v_n_boxed_303_; uint64_t v_res_304_; lean_object* v_r_305_; 
v_n_boxed_303_ = lean_unbox_uint64(v_n_302_);
lean_dec_ref(v_n_302_);
v_res_304_ = l_Float_Model_ofInt64(v_n_boxed_303_);
v_r_305_ = lean_box_uint64(v_res_304_);
return v_r_305_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofISize(size_t v_n_306_){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; uint64_t v___x_309_; 
v___x_307_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_308_ = l_Float_Model_UnpackedFloat_ofISize(v___x_307_, v_n_306_);
v___x_309_ = l_Float_Model_pack(v___x_308_);
lean_dec(v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofISize___boxed(lean_object* v_n_310_){
_start:
{
size_t v_n_boxed_311_; uint64_t v_res_312_; lean_object* v_r_313_; 
v_n_boxed_311_ = lean_unbox_usize(v_n_310_);
lean_dec(v_n_310_);
v_res_312_ = l_Float_Model_ofISize(v_n_boxed_311_);
v_r_313_ = lean_box_uint64(v_res_312_);
return v_r_313_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_toUInt8(uint64_t v_f_314_){
_start:
{
lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_315_ = l_Float_Model_unpack(v_f_314_);
v___x_316_ = l_Float_Model_UnpackedFloat_toUInt8(v___x_315_);
lean_dec(v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toUInt8___boxed(lean_object* v_f_317_){
_start:
{
uint64_t v_f_boxed_318_; uint8_t v_res_319_; lean_object* v_r_320_; 
v_f_boxed_318_ = lean_unbox_uint64(v_f_317_);
lean_dec_ref(v_f_317_);
v_res_319_ = l_Float_Model_toUInt8(v_f_boxed_318_);
v_r_320_ = lean_box(v_res_319_);
return v_r_320_;
}
}
LEAN_EXPORT uint16_t l_Float_Model_toUInt16(uint64_t v_f_321_){
_start:
{
lean_object* v___x_322_; uint16_t v___x_323_; 
v___x_322_ = l_Float_Model_unpack(v_f_321_);
v___x_323_ = l_Float_Model_UnpackedFloat_toUInt16(v___x_322_);
lean_dec(v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toUInt16___boxed(lean_object* v_f_324_){
_start:
{
uint64_t v_f_boxed_325_; uint16_t v_res_326_; lean_object* v_r_327_; 
v_f_boxed_325_ = lean_unbox_uint64(v_f_324_);
lean_dec_ref(v_f_324_);
v_res_326_ = l_Float_Model_toUInt16(v_f_boxed_325_);
v_r_327_ = lean_box(v_res_326_);
return v_r_327_;
}
}
LEAN_EXPORT uint32_t l_Float_Model_toUInt32(uint64_t v_f_328_){
_start:
{
lean_object* v___x_329_; uint32_t v___x_330_; 
v___x_329_ = l_Float_Model_unpack(v_f_328_);
v___x_330_ = l_Float_Model_UnpackedFloat_toUInt32(v___x_329_);
lean_dec(v___x_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toUInt32___boxed(lean_object* v_f_331_){
_start:
{
uint64_t v_f_boxed_332_; uint32_t v_res_333_; lean_object* v_r_334_; 
v_f_boxed_332_ = lean_unbox_uint64(v_f_331_);
lean_dec_ref(v_f_331_);
v_res_333_ = l_Float_Model_toUInt32(v_f_boxed_332_);
v_r_334_ = lean_box_uint32(v_res_333_);
return v_r_334_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_toUInt64(uint64_t v_f_335_){
_start:
{
lean_object* v___x_336_; uint64_t v___x_337_; 
v___x_336_ = l_Float_Model_unpack(v_f_335_);
v___x_337_ = l_Float_Model_UnpackedFloat_toUInt64(v___x_336_);
lean_dec(v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toUInt64___boxed(lean_object* v_f_338_){
_start:
{
uint64_t v_f_boxed_339_; uint64_t v_res_340_; lean_object* v_r_341_; 
v_f_boxed_339_ = lean_unbox_uint64(v_f_338_);
lean_dec_ref(v_f_338_);
v_res_340_ = l_Float_Model_toUInt64(v_f_boxed_339_);
v_r_341_ = lean_box_uint64(v_res_340_);
return v_r_341_;
}
}
LEAN_EXPORT size_t l_Float_Model_toUSize(uint64_t v_f_342_){
_start:
{
lean_object* v___x_343_; size_t v___x_344_; 
v___x_343_ = l_Float_Model_unpack(v_f_342_);
v___x_344_ = l_Float_Model_UnpackedFloat_toUSize(v___x_343_);
lean_dec(v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toUSize___boxed(lean_object* v_f_345_){
_start:
{
uint64_t v_f_boxed_346_; size_t v_res_347_; lean_object* v_r_348_; 
v_f_boxed_346_ = lean_unbox_uint64(v_f_345_);
lean_dec_ref(v_f_345_);
v_res_347_ = l_Float_Model_toUSize(v_f_boxed_346_);
v_r_348_ = lean_box_usize(v_res_347_);
return v_r_348_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_toInt8(uint64_t v_f_349_){
_start:
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = l_Float_Model_unpack(v_f_349_);
v___x_351_ = l_Float_Model_UnpackedFloat_toInt8(v___x_350_);
lean_dec(v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toInt8___boxed(lean_object* v_f_352_){
_start:
{
uint64_t v_f_boxed_353_; uint8_t v_res_354_; lean_object* v_r_355_; 
v_f_boxed_353_ = lean_unbox_uint64(v_f_352_);
lean_dec_ref(v_f_352_);
v_res_354_ = l_Float_Model_toInt8(v_f_boxed_353_);
v_r_355_ = lean_box(v_res_354_);
return v_r_355_;
}
}
LEAN_EXPORT uint16_t l_Float_Model_toInt16(uint64_t v_f_356_){
_start:
{
lean_object* v___x_357_; uint16_t v___x_358_; 
v___x_357_ = l_Float_Model_unpack(v_f_356_);
v___x_358_ = l_Float_Model_UnpackedFloat_toInt16(v___x_357_);
lean_dec(v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toInt16___boxed(lean_object* v_f_359_){
_start:
{
uint64_t v_f_boxed_360_; uint16_t v_res_361_; lean_object* v_r_362_; 
v_f_boxed_360_ = lean_unbox_uint64(v_f_359_);
lean_dec_ref(v_f_359_);
v_res_361_ = l_Float_Model_toInt16(v_f_boxed_360_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT uint32_t l_Float_Model_toInt32(uint64_t v_f_363_){
_start:
{
lean_object* v___x_364_; uint32_t v___x_365_; 
v___x_364_ = l_Float_Model_unpack(v_f_363_);
v___x_365_ = l_Float_Model_UnpackedFloat_toInt32(v___x_364_);
lean_dec(v___x_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toInt32___boxed(lean_object* v_f_366_){
_start:
{
uint64_t v_f_boxed_367_; uint32_t v_res_368_; lean_object* v_r_369_; 
v_f_boxed_367_ = lean_unbox_uint64(v_f_366_);
lean_dec_ref(v_f_366_);
v_res_368_ = l_Float_Model_toInt32(v_f_boxed_367_);
v_r_369_ = lean_box_uint32(v_res_368_);
return v_r_369_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_toInt64(uint64_t v_f_370_){
_start:
{
lean_object* v___x_371_; uint64_t v___x_372_; 
v___x_371_ = l_Float_Model_unpack(v_f_370_);
v___x_372_ = l_Float_Model_UnpackedFloat_toInt64(v___x_371_);
lean_dec(v___x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toInt64___boxed(lean_object* v_f_373_){
_start:
{
uint64_t v_f_boxed_374_; uint64_t v_res_375_; lean_object* v_r_376_; 
v_f_boxed_374_ = lean_unbox_uint64(v_f_373_);
lean_dec_ref(v_f_373_);
v_res_375_ = l_Float_Model_toInt64(v_f_boxed_374_);
v_r_376_ = lean_box_uint64(v_res_375_);
return v_r_376_;
}
}
LEAN_EXPORT size_t l_Float_Model_toISize(uint64_t v_f_377_){
_start:
{
lean_object* v___x_378_; size_t v___x_379_; 
v___x_378_ = l_Float_Model_unpack(v_f_377_);
v___x_379_ = l_Float_Model_UnpackedFloat_toISize(v___x_378_);
lean_dec(v___x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toISize___boxed(lean_object* v_f_380_){
_start:
{
uint64_t v_f_boxed_381_; size_t v_res_382_; lean_object* v_r_383_; 
v_f_boxed_381_ = lean_unbox_uint64(v_f_380_);
lean_dec_ref(v_f_380_);
v_res_382_ = l_Float_Model_toISize(v_f_boxed_381_);
v_r_383_ = lean_box_usize(v_res_382_);
return v_r_383_;
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
