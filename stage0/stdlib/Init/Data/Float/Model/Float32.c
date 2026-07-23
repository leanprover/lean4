// Lean compiler output
// Module: Init.Data.Float.Model.Float32
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
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Float_Model_UnpackedFloat_unpack(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_div(lean_object*, lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_pack(lean_object*, lean_object*);
uint32_t lean_uint32_of_nat_mk(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofUInt32(lean_object*, uint32_t);
uint8_t l_Float_Model_UnpackedFloat_beq(lean_object*, lean_object*);
uint8_t l_Float_Model_UnpackedFloat_isNaN(lean_object*);
uint8_t l_Float_Model_UnpackedFloat_le(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_mul(lean_object*, lean_object*, lean_object*);
uint16_t l_Float_Model_UnpackedFloat_toInt16(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_sub(lean_object*, lean_object*, lean_object*);
uint64_t l_Float_Model_UnpackedFloat_toInt64(lean_object*);
size_t l_Float_Model_UnpackedFloat_toISize(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_add(lean_object*, lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofUInt64(lean_object*, uint64_t);
uint8_t l_Float_Model_UnpackedFloat_lt(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofInt32(lean_object*, uint32_t);
lean_object* l_Float_Model_UnpackedFloat_ofUInt16(lean_object*, uint16_t);
size_t l_Float_Model_UnpackedFloat_toUSize(lean_object*);
uint8_t l_Float_Model_UnpackedFloat_isFinite(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_sqrt(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofInt64(lean_object*, uint64_t);
lean_object* l_Float_Model_UnpackedFloat_abs(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofInt(lean_object*, lean_object*);
uint32_t l_Float_Model_UnpackedFloat_toInt32(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofScientific(lean_object*, lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofNat(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_neg(lean_object*);
uint32_t l_Float_Model_UnpackedFloat_toUInt32(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofISize(lean_object*, size_t);
lean_object* l_Float_Model_UnpackedFloat_ofInt8(lean_object*, uint8_t);
lean_object* l_Float_Model_UnpackedFloat_ofUInt8(lean_object*, uint8_t);
uint8_t l_Float_Model_UnpackedFloat_isInf(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_compare(lean_object*, lean_object*);
uint64_t l_Float_Model_UnpackedFloat_toUInt64(lean_object*);
uint8_t l_Float_Model_UnpackedFloat_toUInt8(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofUSize(lean_object*, size_t);
uint16_t l_Float_Model_UnpackedFloat_toUInt16(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofInt16(lean_object*, uint16_t);
uint8_t l_Float_Model_UnpackedFloat_toInt8(lean_object*);
LEAN_EXPORT uint8_t l_Float32_instDecidableEqModel_decEq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Float32_instDecidableEqModel_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Float32_instDecidableEqModel(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Float32_instDecidableEqModel___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Float32_Model_unpack___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1))}};
static const lean_object* l_Float32_Model_unpack___closed__0 = (const lean_object*)&l_Float32_Model_unpack___closed__0_value;
LEAN_EXPORT lean_object* l_Float32_Model_unpack(uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_unpack___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Float32_Model_pack(lean_object*);
LEAN_EXPORT lean_object* l_Float32_Model_pack___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Float32_Model_add(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_add___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Float32_Model_sub(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_sub___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Float32_Model_mul(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_mul___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Float32_Model_div(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_div___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Float32_Model_instAdd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float32_Model_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Float32_Model_instAdd___closed__0 = (const lean_object*)&l_Float32_Model_instAdd___closed__0_value;
LEAN_EXPORT const lean_object* l_Float32_Model_instAdd = (const lean_object*)&l_Float32_Model_instAdd___closed__0_value;
static const lean_closure_object l_Float32_Model_instSub___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float32_Model_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Float32_Model_instSub___closed__0 = (const lean_object*)&l_Float32_Model_instSub___closed__0_value;
LEAN_EXPORT const lean_object* l_Float32_Model_instSub = (const lean_object*)&l_Float32_Model_instSub___closed__0_value;
static const lean_closure_object l_Float32_Model_instMul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float32_Model_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Float32_Model_instMul___closed__0 = (const lean_object*)&l_Float32_Model_instMul___closed__0_value;
LEAN_EXPORT const lean_object* l_Float32_Model_instMul = (const lean_object*)&l_Float32_Model_instMul___closed__0_value;
static const lean_closure_object l_Float32_Model_instDiv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float32_Model_div___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Float32_Model_instDiv___closed__0 = (const lean_object*)&l_Float32_Model_instDiv___closed__0_value;
LEAN_EXPORT const lean_object* l_Float32_Model_instDiv = (const lean_object*)&l_Float32_Model_instDiv___closed__0_value;
LEAN_EXPORT uint32_t l_Float32_Model_sqrt(uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_sqrt___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Float32_Model_neg(uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_neg___boxed(lean_object*);
static const lean_closure_object l_Float32_Model_instNeg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float32_Model_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Float32_Model_instNeg___closed__0 = (const lean_object*)&l_Float32_Model_instNeg___closed__0_value;
LEAN_EXPORT const lean_object* l_Float32_Model_instNeg = (const lean_object*)&l_Float32_Model_instNeg___closed__0_value;
LEAN_EXPORT uint32_t l_Float32_Model_abs(uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_abs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float32_Model_compare(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_compare___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Float32_Model_le(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_le___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Float32_Model_lt(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Float32_Model_beq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float32_Model_instLE;
LEAN_EXPORT uint8_t l_Float32_Model_instDecidableLE(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_instDecidableLE___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float32_Model_instLT;
LEAN_EXPORT uint8_t l_Float32_Model_instDecidableLT(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_instDecidableLT___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Float32_Model_instBEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float32_Model_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Float32_Model_instBEq___closed__0 = (const lean_object*)&l_Float32_Model_instBEq___closed__0_value;
LEAN_EXPORT const lean_object* l_Float32_Model_instBEq = (const lean_object*)&l_Float32_Model_instBEq___closed__0_value;
LEAN_EXPORT uint32_t l_Float32_Model_instMin___lam__0(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_instMin___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Float32_Model_instMin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float32_Model_instMin___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Float32_Model_instMin___closed__0 = (const lean_object*)&l_Float32_Model_instMin___closed__0_value;
LEAN_EXPORT const lean_object* l_Float32_Model_instMin = (const lean_object*)&l_Float32_Model_instMin___closed__0_value;
LEAN_EXPORT uint32_t l_Float32_Model_instMax___lam__0(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_instMax___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Float32_Model_instMax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float32_Model_instMax___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Float32_Model_instMax___closed__0 = (const lean_object*)&l_Float32_Model_instMax___closed__0_value;
LEAN_EXPORT const lean_object* l_Float32_Model_instMax = (const lean_object*)&l_Float32_Model_instMax___closed__0_value;
LEAN_EXPORT uint8_t l_Float32_Model_isFinite(uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_isFinite___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Float32_Model_isInf(uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_isInf___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Float32_Model_isNaN(uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_isNaN___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Float32_Model_ofBits(uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_ofBits___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Float32_Model_ofInt(lean_object*);
LEAN_EXPORT lean_object* l_Float32_Model_ofInt___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Float32_Model_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Float32_Model_ofNat___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Float32_Model_ofUInt8(uint8_t);
LEAN_EXPORT lean_object* l_Float32_Model_ofUInt8___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Float32_Model_ofUInt16(uint16_t);
LEAN_EXPORT lean_object* l_Float32_Model_ofUInt16___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Float32_Model_ofUInt32(uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_ofUInt32___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Float32_Model_ofUInt64(uint64_t);
LEAN_EXPORT lean_object* l_Float32_Model_ofUInt64___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Float32_Model_ofUSize(size_t);
LEAN_EXPORT lean_object* l_Float32_Model_ofUSize___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Float32_Model_ofInt8(uint8_t);
LEAN_EXPORT lean_object* l_Float32_Model_ofInt8___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Float32_Model_ofInt16(uint16_t);
LEAN_EXPORT lean_object* l_Float32_Model_ofInt16___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Float32_Model_ofInt32(uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_ofInt32___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Float32_Model_ofInt64(uint64_t);
LEAN_EXPORT lean_object* l_Float32_Model_ofInt64___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Float32_Model_ofISize(size_t);
LEAN_EXPORT lean_object* l_Float32_Model_ofISize___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Float32_Model_toUInt8(uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_toUInt8___boxed(lean_object*);
LEAN_EXPORT uint16_t l_Float32_Model_toUInt16(uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_toUInt16___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Float32_Model_toUInt32(uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_toUInt32___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Float32_Model_toUInt64(uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_toUInt64___boxed(lean_object*);
LEAN_EXPORT size_t l_Float32_Model_toUSize(uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_toUSize___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Float32_Model_toInt8(uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_toInt8___boxed(lean_object*);
LEAN_EXPORT uint16_t l_Float32_Model_toInt16(uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_toInt16___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Float32_Model_toInt32(uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_toInt32___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Float32_Model_toInt64(uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_toInt64___boxed(lean_object*);
LEAN_EXPORT size_t l_Float32_Model_toISize(uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_toISize___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Float32_Model_ofScientific(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float32_Model_ofScientific___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Float32_Model_instInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Float32_Model_instInhabited___closed__0;
LEAN_EXPORT uint32_t l_Float32_Model_instInhabited;
LEAN_EXPORT uint8_t l_Float32_instDecidableEqModel_decEq(uint32_t v_x_1_, uint32_t v_x_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = lean_uint32_dec_eq(v_x_1_, v_x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Float32_instDecidableEqModel_decEq___boxed(lean_object* v_x_4_, lean_object* v_x_5_){
_start:
{
uint32_t v_x_33__boxed_6_; uint32_t v_x_34__boxed_7_; uint8_t v_res_8_; lean_object* v_r_9_; 
v_x_33__boxed_6_ = lean_unbox_uint32(v_x_4_);
lean_dec(v_x_4_);
v_x_34__boxed_7_ = lean_unbox_uint32(v_x_5_);
lean_dec(v_x_5_);
v_res_8_ = l_Float32_instDecidableEqModel_decEq(v_x_33__boxed_6_, v_x_34__boxed_7_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
LEAN_EXPORT uint8_t l_Float32_instDecidableEqModel(uint32_t v_x_10_, uint32_t v_x_11_){
_start:
{
uint8_t v___x_12_; 
v___x_12_ = lean_uint32_dec_eq(v_x_10_, v_x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Float32_instDecidableEqModel___boxed(lean_object* v_x_13_, lean_object* v_x_14_){
_start:
{
uint32_t v_x_6__boxed_15_; uint32_t v_x_7__boxed_16_; uint8_t v_res_17_; lean_object* v_r_18_; 
v_x_6__boxed_15_ = lean_unbox_uint32(v_x_13_);
lean_dec(v_x_13_);
v_x_7__boxed_16_ = lean_unbox_uint32(v_x_14_);
lean_dec(v_x_14_);
v_res_17_ = l_Float32_instDecidableEqModel(v_x_6__boxed_15_, v_x_7__boxed_16_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_unpack(uint32_t v_f_22_){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_23_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_24_ = lean_uint32_to_nat(v_f_22_);
v___x_25_ = l_Float_Model_UnpackedFloat_unpack(v___x_23_, v___x_24_);
lean_dec(v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_unpack___boxed(lean_object* v_f_26_){
_start:
{
uint32_t v_f_boxed_27_; lean_object* v_res_28_; 
v_f_boxed_27_ = lean_unbox_uint32(v_f_26_);
lean_dec(v_f_26_);
v_res_28_ = l_Float32_Model_unpack(v_f_boxed_27_);
return v_res_28_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_pack(lean_object* v_f_29_){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; uint32_t v___x_32_; 
v___x_30_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_31_ = l_Float_Model_UnpackedFloat_pack(v___x_30_, v_f_29_);
v___x_32_ = lean_uint32_of_nat_mk(v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_pack___boxed(lean_object* v_f_33_){
_start:
{
uint32_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l_Float32_Model_pack(v_f_33_);
lean_dec(v_f_33_);
v_r_35_ = lean_box_uint32(v_res_34_);
return v_r_35_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_add(uint32_t v_a_36_, uint32_t v_b_37_){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; uint32_t v___x_42_; 
v___x_38_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_39_ = l_Float32_Model_unpack(v_a_36_);
v___x_40_ = l_Float32_Model_unpack(v_b_37_);
v___x_41_ = l_Float_Model_UnpackedFloat_add(v___x_38_, v___x_39_, v___x_40_);
v___x_42_ = l_Float32_Model_pack(v___x_41_);
lean_dec(v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_add___boxed(lean_object* v_a_43_, lean_object* v_b_44_){
_start:
{
uint32_t v_a_boxed_45_; uint32_t v_b_boxed_46_; uint32_t v_res_47_; lean_object* v_r_48_; 
v_a_boxed_45_ = lean_unbox_uint32(v_a_43_);
lean_dec(v_a_43_);
v_b_boxed_46_ = lean_unbox_uint32(v_b_44_);
lean_dec(v_b_44_);
v_res_47_ = l_Float32_Model_add(v_a_boxed_45_, v_b_boxed_46_);
v_r_48_ = lean_box_uint32(v_res_47_);
return v_r_48_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_sub(uint32_t v_a_49_, uint32_t v_b_50_){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; uint32_t v___x_55_; 
v___x_51_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_52_ = l_Float32_Model_unpack(v_a_49_);
v___x_53_ = l_Float32_Model_unpack(v_b_50_);
v___x_54_ = l_Float_Model_UnpackedFloat_sub(v___x_51_, v___x_52_, v___x_53_);
v___x_55_ = l_Float32_Model_pack(v___x_54_);
lean_dec(v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_sub___boxed(lean_object* v_a_56_, lean_object* v_b_57_){
_start:
{
uint32_t v_a_boxed_58_; uint32_t v_b_boxed_59_; uint32_t v_res_60_; lean_object* v_r_61_; 
v_a_boxed_58_ = lean_unbox_uint32(v_a_56_);
lean_dec(v_a_56_);
v_b_boxed_59_ = lean_unbox_uint32(v_b_57_);
lean_dec(v_b_57_);
v_res_60_ = l_Float32_Model_sub(v_a_boxed_58_, v_b_boxed_59_);
v_r_61_ = lean_box_uint32(v_res_60_);
return v_r_61_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_mul(uint32_t v_a_62_, uint32_t v_b_63_){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; uint32_t v___x_68_; 
v___x_64_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_65_ = l_Float32_Model_unpack(v_a_62_);
v___x_66_ = l_Float32_Model_unpack(v_b_63_);
v___x_67_ = l_Float_Model_UnpackedFloat_mul(v___x_64_, v___x_65_, v___x_66_);
v___x_68_ = l_Float32_Model_pack(v___x_67_);
lean_dec(v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_mul___boxed(lean_object* v_a_69_, lean_object* v_b_70_){
_start:
{
uint32_t v_a_boxed_71_; uint32_t v_b_boxed_72_; uint32_t v_res_73_; lean_object* v_r_74_; 
v_a_boxed_71_ = lean_unbox_uint32(v_a_69_);
lean_dec(v_a_69_);
v_b_boxed_72_ = lean_unbox_uint32(v_b_70_);
lean_dec(v_b_70_);
v_res_73_ = l_Float32_Model_mul(v_a_boxed_71_, v_b_boxed_72_);
v_r_74_ = lean_box_uint32(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_div(uint32_t v_a_75_, uint32_t v_b_76_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; uint32_t v___x_81_; 
v___x_77_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_78_ = l_Float32_Model_unpack(v_a_75_);
v___x_79_ = l_Float32_Model_unpack(v_b_76_);
v___x_80_ = l_Float_Model_UnpackedFloat_div(v___x_77_, v___x_78_, v___x_79_);
v___x_81_ = l_Float32_Model_pack(v___x_80_);
lean_dec(v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_div___boxed(lean_object* v_a_82_, lean_object* v_b_83_){
_start:
{
uint32_t v_a_boxed_84_; uint32_t v_b_boxed_85_; uint32_t v_res_86_; lean_object* v_r_87_; 
v_a_boxed_84_ = lean_unbox_uint32(v_a_82_);
lean_dec(v_a_82_);
v_b_boxed_85_ = lean_unbox_uint32(v_b_83_);
lean_dec(v_b_83_);
v_res_86_ = l_Float32_Model_div(v_a_boxed_84_, v_b_boxed_85_);
v_r_87_ = lean_box_uint32(v_res_86_);
return v_r_87_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_sqrt(uint32_t v_a_96_){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; uint32_t v___x_100_; 
v___x_97_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_98_ = l_Float32_Model_unpack(v_a_96_);
v___x_99_ = l_Float_Model_UnpackedFloat_sqrt(v___x_97_, v___x_98_);
lean_dec(v___x_98_);
v___x_100_ = l_Float32_Model_pack(v___x_99_);
lean_dec(v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_sqrt___boxed(lean_object* v_a_101_){
_start:
{
uint32_t v_a_boxed_102_; uint32_t v_res_103_; lean_object* v_r_104_; 
v_a_boxed_102_ = lean_unbox_uint32(v_a_101_);
lean_dec(v_a_101_);
v_res_103_ = l_Float32_Model_sqrt(v_a_boxed_102_);
v_r_104_ = lean_box_uint32(v_res_103_);
return v_r_104_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_neg(uint32_t v_a_105_){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; uint32_t v___x_108_; 
v___x_106_ = l_Float32_Model_unpack(v_a_105_);
v___x_107_ = l_Float_Model_UnpackedFloat_neg(v___x_106_);
v___x_108_ = l_Float32_Model_pack(v___x_107_);
lean_dec(v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_neg___boxed(lean_object* v_a_109_){
_start:
{
uint32_t v_a_boxed_110_; uint32_t v_res_111_; lean_object* v_r_112_; 
v_a_boxed_110_ = lean_unbox_uint32(v_a_109_);
lean_dec(v_a_109_);
v_res_111_ = l_Float32_Model_neg(v_a_boxed_110_);
v_r_112_ = lean_box_uint32(v_res_111_);
return v_r_112_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_abs(uint32_t v_a_115_){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; uint32_t v___x_118_; 
v___x_116_ = l_Float32_Model_unpack(v_a_115_);
v___x_117_ = l_Float_Model_UnpackedFloat_abs(v___x_116_);
v___x_118_ = l_Float32_Model_pack(v___x_117_);
lean_dec(v___x_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_abs___boxed(lean_object* v_a_119_){
_start:
{
uint32_t v_a_boxed_120_; uint32_t v_res_121_; lean_object* v_r_122_; 
v_a_boxed_120_ = lean_unbox_uint32(v_a_119_);
lean_dec(v_a_119_);
v_res_121_ = l_Float32_Model_abs(v_a_boxed_120_);
v_r_122_ = lean_box_uint32(v_res_121_);
return v_r_122_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_compare(uint32_t v_a_123_, uint32_t v_b_124_){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_125_ = l_Float32_Model_unpack(v_a_123_);
v___x_126_ = l_Float32_Model_unpack(v_b_124_);
v___x_127_ = l_Float_Model_UnpackedFloat_compare(v___x_125_, v___x_126_);
lean_dec(v___x_126_);
lean_dec(v___x_125_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_compare___boxed(lean_object* v_a_128_, lean_object* v_b_129_){
_start:
{
uint32_t v_a_boxed_130_; uint32_t v_b_boxed_131_; lean_object* v_res_132_; 
v_a_boxed_130_ = lean_unbox_uint32(v_a_128_);
lean_dec(v_a_128_);
v_b_boxed_131_ = lean_unbox_uint32(v_b_129_);
lean_dec(v_b_129_);
v_res_132_ = l_Float32_Model_compare(v_a_boxed_130_, v_b_boxed_131_);
return v_res_132_;
}
}
LEAN_EXPORT uint8_t l_Float32_Model_le(uint32_t v_a_133_, uint32_t v_b_134_){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_135_ = l_Float32_Model_unpack(v_a_133_);
v___x_136_ = l_Float32_Model_unpack(v_b_134_);
v___x_137_ = l_Float_Model_UnpackedFloat_le(v___x_135_, v___x_136_);
lean_dec(v___x_136_);
lean_dec(v___x_135_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_le___boxed(lean_object* v_a_138_, lean_object* v_b_139_){
_start:
{
uint32_t v_a_boxed_140_; uint32_t v_b_boxed_141_; uint8_t v_res_142_; lean_object* v_r_143_; 
v_a_boxed_140_ = lean_unbox_uint32(v_a_138_);
lean_dec(v_a_138_);
v_b_boxed_141_ = lean_unbox_uint32(v_b_139_);
lean_dec(v_b_139_);
v_res_142_ = l_Float32_Model_le(v_a_boxed_140_, v_b_boxed_141_);
v_r_143_ = lean_box(v_res_142_);
return v_r_143_;
}
}
LEAN_EXPORT uint8_t l_Float32_Model_lt(uint32_t v_a_144_, uint32_t v_b_145_){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_146_ = l_Float32_Model_unpack(v_a_144_);
v___x_147_ = l_Float32_Model_unpack(v_b_145_);
v___x_148_ = l_Float_Model_UnpackedFloat_lt(v___x_146_, v___x_147_);
lean_dec(v___x_147_);
lean_dec(v___x_146_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_lt___boxed(lean_object* v_a_149_, lean_object* v_b_150_){
_start:
{
uint32_t v_a_boxed_151_; uint32_t v_b_boxed_152_; uint8_t v_res_153_; lean_object* v_r_154_; 
v_a_boxed_151_ = lean_unbox_uint32(v_a_149_);
lean_dec(v_a_149_);
v_b_boxed_152_ = lean_unbox_uint32(v_b_150_);
lean_dec(v_b_150_);
v_res_153_ = l_Float32_Model_lt(v_a_boxed_151_, v_b_boxed_152_);
v_r_154_ = lean_box(v_res_153_);
return v_r_154_;
}
}
LEAN_EXPORT uint8_t l_Float32_Model_beq(uint32_t v_a_155_, uint32_t v_b_156_){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_157_ = l_Float32_Model_unpack(v_a_155_);
v___x_158_ = l_Float32_Model_unpack(v_b_156_);
v___x_159_ = l_Float_Model_UnpackedFloat_beq(v___x_157_, v___x_158_);
lean_dec(v___x_158_);
lean_dec(v___x_157_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_beq___boxed(lean_object* v_a_160_, lean_object* v_b_161_){
_start:
{
uint32_t v_a_boxed_162_; uint32_t v_b_boxed_163_; uint8_t v_res_164_; lean_object* v_r_165_; 
v_a_boxed_162_ = lean_unbox_uint32(v_a_160_);
lean_dec(v_a_160_);
v_b_boxed_163_ = lean_unbox_uint32(v_b_161_);
lean_dec(v_b_161_);
v_res_164_ = l_Float32_Model_beq(v_a_boxed_162_, v_b_boxed_163_);
v_r_165_ = lean_box(v_res_164_);
return v_r_165_;
}
}
static lean_object* _init_l_Float32_Model_instLE(void){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_box(0);
return v___x_166_;
}
}
LEAN_EXPORT uint8_t l_Float32_Model_instDecidableLE(uint32_t v_a_167_, uint32_t v_b_168_){
_start:
{
uint8_t v___x_169_; 
v___x_169_ = l_Float32_Model_le(v_a_167_, v_b_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_instDecidableLE___boxed(lean_object* v_a_170_, lean_object* v_b_171_){
_start:
{
uint32_t v_a_boxed_172_; uint32_t v_b_boxed_173_; uint8_t v_res_174_; lean_object* v_r_175_; 
v_a_boxed_172_ = lean_unbox_uint32(v_a_170_);
lean_dec(v_a_170_);
v_b_boxed_173_ = lean_unbox_uint32(v_b_171_);
lean_dec(v_b_171_);
v_res_174_ = l_Float32_Model_instDecidableLE(v_a_boxed_172_, v_b_boxed_173_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
static lean_object* _init_l_Float32_Model_instLT(void){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = lean_box(0);
return v___x_176_;
}
}
LEAN_EXPORT uint8_t l_Float32_Model_instDecidableLT(uint32_t v_a_177_, uint32_t v_b_178_){
_start:
{
uint8_t v___x_179_; 
v___x_179_ = l_Float32_Model_lt(v_a_177_, v_b_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_instDecidableLT___boxed(lean_object* v_a_180_, lean_object* v_b_181_){
_start:
{
uint32_t v_a_boxed_182_; uint32_t v_b_boxed_183_; uint8_t v_res_184_; lean_object* v_r_185_; 
v_a_boxed_182_ = lean_unbox_uint32(v_a_180_);
lean_dec(v_a_180_);
v_b_boxed_183_ = lean_unbox_uint32(v_b_181_);
lean_dec(v_b_181_);
v_res_184_ = l_Float32_Model_instDecidableLT(v_a_boxed_182_, v_b_boxed_183_);
v_r_185_ = lean_box(v_res_184_);
return v_r_185_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_instMin___lam__0(uint32_t v_a_188_, uint32_t v_b_189_){
_start:
{
uint8_t v___x_190_; 
v___x_190_ = l_Float32_Model_le(v_a_188_, v_b_189_);
if (v___x_190_ == 0)
{
return v_b_189_;
}
else
{
return v_a_188_;
}
}
}
LEAN_EXPORT lean_object* l_Float32_Model_instMin___lam__0___boxed(lean_object* v_a_191_, lean_object* v_b_192_){
_start:
{
uint32_t v_a_boxed_193_; uint32_t v_b_boxed_194_; uint32_t v_res_195_; lean_object* v_r_196_; 
v_a_boxed_193_ = lean_unbox_uint32(v_a_191_);
lean_dec(v_a_191_);
v_b_boxed_194_ = lean_unbox_uint32(v_b_192_);
lean_dec(v_b_192_);
v_res_195_ = l_Float32_Model_instMin___lam__0(v_a_boxed_193_, v_b_boxed_194_);
v_r_196_ = lean_box_uint32(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_instMax___lam__0(uint32_t v_a_199_, uint32_t v_b_200_){
_start:
{
uint8_t v___x_201_; 
v___x_201_ = l_Float32_Model_le(v_b_200_, v_a_199_);
if (v___x_201_ == 0)
{
return v_b_200_;
}
else
{
return v_a_199_;
}
}
}
LEAN_EXPORT lean_object* l_Float32_Model_instMax___lam__0___boxed(lean_object* v_a_202_, lean_object* v_b_203_){
_start:
{
uint32_t v_a_boxed_204_; uint32_t v_b_boxed_205_; uint32_t v_res_206_; lean_object* v_r_207_; 
v_a_boxed_204_ = lean_unbox_uint32(v_a_202_);
lean_dec(v_a_202_);
v_b_boxed_205_ = lean_unbox_uint32(v_b_203_);
lean_dec(v_b_203_);
v_res_206_ = l_Float32_Model_instMax___lam__0(v_a_boxed_204_, v_b_boxed_205_);
v_r_207_ = lean_box_uint32(v_res_206_);
return v_r_207_;
}
}
LEAN_EXPORT uint8_t l_Float32_Model_isFinite(uint32_t v_a_210_){
_start:
{
lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_211_ = l_Float32_Model_unpack(v_a_210_);
v___x_212_ = l_Float_Model_UnpackedFloat_isFinite(v___x_211_);
lean_dec(v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_isFinite___boxed(lean_object* v_a_213_){
_start:
{
uint32_t v_a_boxed_214_; uint8_t v_res_215_; lean_object* v_r_216_; 
v_a_boxed_214_ = lean_unbox_uint32(v_a_213_);
lean_dec(v_a_213_);
v_res_215_ = l_Float32_Model_isFinite(v_a_boxed_214_);
v_r_216_ = lean_box(v_res_215_);
return v_r_216_;
}
}
LEAN_EXPORT uint8_t l_Float32_Model_isInf(uint32_t v_a_217_){
_start:
{
lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_218_ = l_Float32_Model_unpack(v_a_217_);
v___x_219_ = l_Float_Model_UnpackedFloat_isInf(v___x_218_);
lean_dec(v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_isInf___boxed(lean_object* v_a_220_){
_start:
{
uint32_t v_a_boxed_221_; uint8_t v_res_222_; lean_object* v_r_223_; 
v_a_boxed_221_ = lean_unbox_uint32(v_a_220_);
lean_dec(v_a_220_);
v_res_222_ = l_Float32_Model_isInf(v_a_boxed_221_);
v_r_223_ = lean_box(v_res_222_);
return v_r_223_;
}
}
LEAN_EXPORT uint8_t l_Float32_Model_isNaN(uint32_t v_a_224_){
_start:
{
lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_225_ = l_Float32_Model_unpack(v_a_224_);
v___x_226_ = l_Float_Model_UnpackedFloat_isNaN(v___x_225_);
lean_dec(v___x_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_isNaN___boxed(lean_object* v_a_227_){
_start:
{
uint32_t v_a_boxed_228_; uint8_t v_res_229_; lean_object* v_r_230_; 
v_a_boxed_228_ = lean_unbox_uint32(v_a_227_);
lean_dec(v_a_227_);
v_res_229_ = l_Float32_Model_isNaN(v_a_boxed_228_);
v_r_230_ = lean_box(v_res_229_);
return v_r_230_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_ofBits(uint32_t v_a_231_){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; uint32_t v___x_235_; 
v___x_232_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_233_ = lean_uint32_to_nat(v_a_231_);
v___x_234_ = l_Float_Model_UnpackedFloat_unpack(v___x_232_, v___x_233_);
lean_dec(v___x_233_);
v___x_235_ = l_Float32_Model_pack(v___x_234_);
lean_dec(v___x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_ofBits___boxed(lean_object* v_a_236_){
_start:
{
uint32_t v_a_boxed_237_; uint32_t v_res_238_; lean_object* v_r_239_; 
v_a_boxed_237_ = lean_unbox_uint32(v_a_236_);
lean_dec(v_a_236_);
v_res_238_ = l_Float32_Model_ofBits(v_a_boxed_237_);
v_r_239_ = lean_box_uint32(v_res_238_);
return v_r_239_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_ofInt(lean_object* v_n_240_){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; uint32_t v___x_243_; 
v___x_241_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_242_ = l_Float_Model_UnpackedFloat_ofInt(v___x_241_, v_n_240_);
v___x_243_ = l_Float32_Model_pack(v___x_242_);
lean_dec(v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_ofInt___boxed(lean_object* v_n_244_){
_start:
{
uint32_t v_res_245_; lean_object* v_r_246_; 
v_res_245_ = l_Float32_Model_ofInt(v_n_244_);
lean_dec(v_n_244_);
v_r_246_ = lean_box_uint32(v_res_245_);
return v_r_246_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_ofNat(lean_object* v_n_247_){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; uint32_t v___x_250_; 
v___x_248_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_249_ = l_Float_Model_UnpackedFloat_ofNat(v___x_248_, v_n_247_);
v___x_250_ = l_Float32_Model_pack(v___x_249_);
lean_dec(v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_ofNat___boxed(lean_object* v_n_251_){
_start:
{
uint32_t v_res_252_; lean_object* v_r_253_; 
v_res_252_ = l_Float32_Model_ofNat(v_n_251_);
v_r_253_ = lean_box_uint32(v_res_252_);
return v_r_253_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_ofUInt8(uint8_t v_n_254_){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; uint32_t v___x_257_; 
v___x_255_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_256_ = l_Float_Model_UnpackedFloat_ofUInt8(v___x_255_, v_n_254_);
v___x_257_ = l_Float32_Model_pack(v___x_256_);
lean_dec(v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_ofUInt8___boxed(lean_object* v_n_258_){
_start:
{
uint8_t v_n_boxed_259_; uint32_t v_res_260_; lean_object* v_r_261_; 
v_n_boxed_259_ = lean_unbox(v_n_258_);
v_res_260_ = l_Float32_Model_ofUInt8(v_n_boxed_259_);
v_r_261_ = lean_box_uint32(v_res_260_);
return v_r_261_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_ofUInt16(uint16_t v_n_262_){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; uint32_t v___x_265_; 
v___x_263_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_264_ = l_Float_Model_UnpackedFloat_ofUInt16(v___x_263_, v_n_262_);
v___x_265_ = l_Float32_Model_pack(v___x_264_);
lean_dec(v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_ofUInt16___boxed(lean_object* v_n_266_){
_start:
{
uint16_t v_n_boxed_267_; uint32_t v_res_268_; lean_object* v_r_269_; 
v_n_boxed_267_ = lean_unbox(v_n_266_);
v_res_268_ = l_Float32_Model_ofUInt16(v_n_boxed_267_);
v_r_269_ = lean_box_uint32(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_ofUInt32(uint32_t v_n_270_){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; uint32_t v___x_273_; 
v___x_271_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_272_ = l_Float_Model_UnpackedFloat_ofUInt32(v___x_271_, v_n_270_);
v___x_273_ = l_Float32_Model_pack(v___x_272_);
lean_dec(v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_ofUInt32___boxed(lean_object* v_n_274_){
_start:
{
uint32_t v_n_boxed_275_; uint32_t v_res_276_; lean_object* v_r_277_; 
v_n_boxed_275_ = lean_unbox_uint32(v_n_274_);
lean_dec(v_n_274_);
v_res_276_ = l_Float32_Model_ofUInt32(v_n_boxed_275_);
v_r_277_ = lean_box_uint32(v_res_276_);
return v_r_277_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_ofUInt64(uint64_t v_n_278_){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; uint32_t v___x_281_; 
v___x_279_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_280_ = l_Float_Model_UnpackedFloat_ofUInt64(v___x_279_, v_n_278_);
v___x_281_ = l_Float32_Model_pack(v___x_280_);
lean_dec(v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_ofUInt64___boxed(lean_object* v_n_282_){
_start:
{
uint64_t v_n_boxed_283_; uint32_t v_res_284_; lean_object* v_r_285_; 
v_n_boxed_283_ = lean_unbox_uint64(v_n_282_);
lean_dec_ref(v_n_282_);
v_res_284_ = l_Float32_Model_ofUInt64(v_n_boxed_283_);
v_r_285_ = lean_box_uint32(v_res_284_);
return v_r_285_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_ofUSize(size_t v_n_286_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; uint32_t v___x_289_; 
v___x_287_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_288_ = l_Float_Model_UnpackedFloat_ofUSize(v___x_287_, v_n_286_);
v___x_289_ = l_Float32_Model_pack(v___x_288_);
lean_dec(v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_ofUSize___boxed(lean_object* v_n_290_){
_start:
{
size_t v_n_boxed_291_; uint32_t v_res_292_; lean_object* v_r_293_; 
v_n_boxed_291_ = lean_unbox_usize(v_n_290_);
lean_dec(v_n_290_);
v_res_292_ = l_Float32_Model_ofUSize(v_n_boxed_291_);
v_r_293_ = lean_box_uint32(v_res_292_);
return v_r_293_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_ofInt8(uint8_t v_n_294_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; uint32_t v___x_297_; 
v___x_295_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_296_ = l_Float_Model_UnpackedFloat_ofInt8(v___x_295_, v_n_294_);
v___x_297_ = l_Float32_Model_pack(v___x_296_);
lean_dec(v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_ofInt8___boxed(lean_object* v_n_298_){
_start:
{
uint8_t v_n_boxed_299_; uint32_t v_res_300_; lean_object* v_r_301_; 
v_n_boxed_299_ = lean_unbox(v_n_298_);
v_res_300_ = l_Float32_Model_ofInt8(v_n_boxed_299_);
v_r_301_ = lean_box_uint32(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_ofInt16(uint16_t v_n_302_){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; uint32_t v___x_305_; 
v___x_303_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_304_ = l_Float_Model_UnpackedFloat_ofInt16(v___x_303_, v_n_302_);
v___x_305_ = l_Float32_Model_pack(v___x_304_);
lean_dec(v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_ofInt16___boxed(lean_object* v_n_306_){
_start:
{
uint16_t v_n_boxed_307_; uint32_t v_res_308_; lean_object* v_r_309_; 
v_n_boxed_307_ = lean_unbox(v_n_306_);
v_res_308_ = l_Float32_Model_ofInt16(v_n_boxed_307_);
v_r_309_ = lean_box_uint32(v_res_308_);
return v_r_309_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_ofInt32(uint32_t v_n_310_){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; uint32_t v___x_313_; 
v___x_311_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_312_ = l_Float_Model_UnpackedFloat_ofInt32(v___x_311_, v_n_310_);
v___x_313_ = l_Float32_Model_pack(v___x_312_);
lean_dec(v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_ofInt32___boxed(lean_object* v_n_314_){
_start:
{
uint32_t v_n_boxed_315_; uint32_t v_res_316_; lean_object* v_r_317_; 
v_n_boxed_315_ = lean_unbox_uint32(v_n_314_);
lean_dec(v_n_314_);
v_res_316_ = l_Float32_Model_ofInt32(v_n_boxed_315_);
v_r_317_ = lean_box_uint32(v_res_316_);
return v_r_317_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_ofInt64(uint64_t v_n_318_){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; uint32_t v___x_321_; 
v___x_319_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_320_ = l_Float_Model_UnpackedFloat_ofInt64(v___x_319_, v_n_318_);
v___x_321_ = l_Float32_Model_pack(v___x_320_);
lean_dec(v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_ofInt64___boxed(lean_object* v_n_322_){
_start:
{
uint64_t v_n_boxed_323_; uint32_t v_res_324_; lean_object* v_r_325_; 
v_n_boxed_323_ = lean_unbox_uint64(v_n_322_);
lean_dec_ref(v_n_322_);
v_res_324_ = l_Float32_Model_ofInt64(v_n_boxed_323_);
v_r_325_ = lean_box_uint32(v_res_324_);
return v_r_325_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_ofISize(size_t v_n_326_){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; uint32_t v___x_329_; 
v___x_327_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_328_ = l_Float_Model_UnpackedFloat_ofISize(v___x_327_, v_n_326_);
v___x_329_ = l_Float32_Model_pack(v___x_328_);
lean_dec(v___x_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_ofISize___boxed(lean_object* v_n_330_){
_start:
{
size_t v_n_boxed_331_; uint32_t v_res_332_; lean_object* v_r_333_; 
v_n_boxed_331_ = lean_unbox_usize(v_n_330_);
lean_dec(v_n_330_);
v_res_332_ = l_Float32_Model_ofISize(v_n_boxed_331_);
v_r_333_ = lean_box_uint32(v_res_332_);
return v_r_333_;
}
}
LEAN_EXPORT uint8_t l_Float32_Model_toUInt8(uint32_t v_f_334_){
_start:
{
lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_335_ = l_Float32_Model_unpack(v_f_334_);
v___x_336_ = l_Float_Model_UnpackedFloat_toUInt8(v___x_335_);
lean_dec(v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_toUInt8___boxed(lean_object* v_f_337_){
_start:
{
uint32_t v_f_boxed_338_; uint8_t v_res_339_; lean_object* v_r_340_; 
v_f_boxed_338_ = lean_unbox_uint32(v_f_337_);
lean_dec(v_f_337_);
v_res_339_ = l_Float32_Model_toUInt8(v_f_boxed_338_);
v_r_340_ = lean_box(v_res_339_);
return v_r_340_;
}
}
LEAN_EXPORT uint16_t l_Float32_Model_toUInt16(uint32_t v_f_341_){
_start:
{
lean_object* v___x_342_; uint16_t v___x_343_; 
v___x_342_ = l_Float32_Model_unpack(v_f_341_);
v___x_343_ = l_Float_Model_UnpackedFloat_toUInt16(v___x_342_);
lean_dec(v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_toUInt16___boxed(lean_object* v_f_344_){
_start:
{
uint32_t v_f_boxed_345_; uint16_t v_res_346_; lean_object* v_r_347_; 
v_f_boxed_345_ = lean_unbox_uint32(v_f_344_);
lean_dec(v_f_344_);
v_res_346_ = l_Float32_Model_toUInt16(v_f_boxed_345_);
v_r_347_ = lean_box(v_res_346_);
return v_r_347_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_toUInt32(uint32_t v_f_348_){
_start:
{
lean_object* v___x_349_; uint32_t v___x_350_; 
v___x_349_ = l_Float32_Model_unpack(v_f_348_);
v___x_350_ = l_Float_Model_UnpackedFloat_toUInt32(v___x_349_);
lean_dec(v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_toUInt32___boxed(lean_object* v_f_351_){
_start:
{
uint32_t v_f_boxed_352_; uint32_t v_res_353_; lean_object* v_r_354_; 
v_f_boxed_352_ = lean_unbox_uint32(v_f_351_);
lean_dec(v_f_351_);
v_res_353_ = l_Float32_Model_toUInt32(v_f_boxed_352_);
v_r_354_ = lean_box_uint32(v_res_353_);
return v_r_354_;
}
}
LEAN_EXPORT uint64_t l_Float32_Model_toUInt64(uint32_t v_f_355_){
_start:
{
lean_object* v___x_356_; uint64_t v___x_357_; 
v___x_356_ = l_Float32_Model_unpack(v_f_355_);
v___x_357_ = l_Float_Model_UnpackedFloat_toUInt64(v___x_356_);
lean_dec(v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_toUInt64___boxed(lean_object* v_f_358_){
_start:
{
uint32_t v_f_boxed_359_; uint64_t v_res_360_; lean_object* v_r_361_; 
v_f_boxed_359_ = lean_unbox_uint32(v_f_358_);
lean_dec(v_f_358_);
v_res_360_ = l_Float32_Model_toUInt64(v_f_boxed_359_);
v_r_361_ = lean_box_uint64(v_res_360_);
return v_r_361_;
}
}
LEAN_EXPORT size_t l_Float32_Model_toUSize(uint32_t v_f_362_){
_start:
{
lean_object* v___x_363_; size_t v___x_364_; 
v___x_363_ = l_Float32_Model_unpack(v_f_362_);
v___x_364_ = l_Float_Model_UnpackedFloat_toUSize(v___x_363_);
lean_dec(v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_toUSize___boxed(lean_object* v_f_365_){
_start:
{
uint32_t v_f_boxed_366_; size_t v_res_367_; lean_object* v_r_368_; 
v_f_boxed_366_ = lean_unbox_uint32(v_f_365_);
lean_dec(v_f_365_);
v_res_367_ = l_Float32_Model_toUSize(v_f_boxed_366_);
v_r_368_ = lean_box_usize(v_res_367_);
return v_r_368_;
}
}
LEAN_EXPORT uint8_t l_Float32_Model_toInt8(uint32_t v_f_369_){
_start:
{
lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_370_ = l_Float32_Model_unpack(v_f_369_);
v___x_371_ = l_Float_Model_UnpackedFloat_toInt8(v___x_370_);
lean_dec(v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_toInt8___boxed(lean_object* v_f_372_){
_start:
{
uint32_t v_f_boxed_373_; uint8_t v_res_374_; lean_object* v_r_375_; 
v_f_boxed_373_ = lean_unbox_uint32(v_f_372_);
lean_dec(v_f_372_);
v_res_374_ = l_Float32_Model_toInt8(v_f_boxed_373_);
v_r_375_ = lean_box(v_res_374_);
return v_r_375_;
}
}
LEAN_EXPORT uint16_t l_Float32_Model_toInt16(uint32_t v_f_376_){
_start:
{
lean_object* v___x_377_; uint16_t v___x_378_; 
v___x_377_ = l_Float32_Model_unpack(v_f_376_);
v___x_378_ = l_Float_Model_UnpackedFloat_toInt16(v___x_377_);
lean_dec(v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_toInt16___boxed(lean_object* v_f_379_){
_start:
{
uint32_t v_f_boxed_380_; uint16_t v_res_381_; lean_object* v_r_382_; 
v_f_boxed_380_ = lean_unbox_uint32(v_f_379_);
lean_dec(v_f_379_);
v_res_381_ = l_Float32_Model_toInt16(v_f_boxed_380_);
v_r_382_ = lean_box(v_res_381_);
return v_r_382_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_toInt32(uint32_t v_f_383_){
_start:
{
lean_object* v___x_384_; uint32_t v___x_385_; 
v___x_384_ = l_Float32_Model_unpack(v_f_383_);
v___x_385_ = l_Float_Model_UnpackedFloat_toInt32(v___x_384_);
lean_dec(v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_toInt32___boxed(lean_object* v_f_386_){
_start:
{
uint32_t v_f_boxed_387_; uint32_t v_res_388_; lean_object* v_r_389_; 
v_f_boxed_387_ = lean_unbox_uint32(v_f_386_);
lean_dec(v_f_386_);
v_res_388_ = l_Float32_Model_toInt32(v_f_boxed_387_);
v_r_389_ = lean_box_uint32(v_res_388_);
return v_r_389_;
}
}
LEAN_EXPORT uint64_t l_Float32_Model_toInt64(uint32_t v_f_390_){
_start:
{
lean_object* v___x_391_; uint64_t v___x_392_; 
v___x_391_ = l_Float32_Model_unpack(v_f_390_);
v___x_392_ = l_Float_Model_UnpackedFloat_toInt64(v___x_391_);
lean_dec(v___x_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_toInt64___boxed(lean_object* v_f_393_){
_start:
{
uint32_t v_f_boxed_394_; uint64_t v_res_395_; lean_object* v_r_396_; 
v_f_boxed_394_ = lean_unbox_uint32(v_f_393_);
lean_dec(v_f_393_);
v_res_395_ = l_Float32_Model_toInt64(v_f_boxed_394_);
v_r_396_ = lean_box_uint64(v_res_395_);
return v_r_396_;
}
}
LEAN_EXPORT size_t l_Float32_Model_toISize(uint32_t v_f_397_){
_start:
{
lean_object* v___x_398_; size_t v___x_399_; 
v___x_398_ = l_Float32_Model_unpack(v_f_397_);
v___x_399_ = l_Float_Model_UnpackedFloat_toISize(v___x_398_);
lean_dec(v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_toISize___boxed(lean_object* v_f_400_){
_start:
{
uint32_t v_f_boxed_401_; size_t v_res_402_; lean_object* v_r_403_; 
v_f_boxed_401_ = lean_unbox_uint32(v_f_400_);
lean_dec(v_f_400_);
v_res_402_ = l_Float32_Model_toISize(v_f_boxed_401_);
v_r_403_ = lean_box_usize(v_res_402_);
return v_r_403_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_ofScientific(lean_object* v_m_404_, lean_object* v_e_405_){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; uint32_t v___x_408_; 
v___x_406_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_407_ = l_Float_Model_UnpackedFloat_ofScientific(v___x_406_, v_m_404_, v_e_405_);
v___x_408_ = l_Float32_Model_pack(v___x_407_);
lean_dec(v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_ofScientific___boxed(lean_object* v_m_409_, lean_object* v_e_410_){
_start:
{
uint32_t v_res_411_; lean_object* v_r_412_; 
v_res_411_ = l_Float32_Model_ofScientific(v_m_409_, v_e_410_);
lean_dec(v_e_410_);
v_r_412_ = lean_box_uint32(v_res_411_);
return v_r_412_;
}
}
static uint32_t _init_l_Float32_Model_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_413_; uint32_t v___x_414_; 
v___x_413_ = lean_unsigned_to_nat(0u);
v___x_414_ = l_Float32_Model_ofNat(v___x_413_);
return v___x_414_;
}
}
static uint32_t _init_l_Float32_Model_instInhabited(void){
_start:
{
uint32_t v___x_415_; 
v___x_415_ = lean_uint32_once(&l_Float32_Model_instInhabited___closed__0, &l_Float32_Model_instInhabited___closed__0_once, _init_l_Float32_Model_instInhabited___closed__0);
return v___x_415_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Format_Valid(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Pack_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Operations(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Factories(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Float32(uint8_t builtin) {
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
l_Float32_Model_instLE = _init_l_Float32_Model_instLE();
lean_mark_persistent(l_Float32_Model_instLE);
l_Float32_Model_instLT = _init_l_Float32_Model_instLT();
lean_mark_persistent(l_Float32_Model_instLT);
l_Float32_Model_instInhabited = _init_l_Float32_Model_instInhabited();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Float_Model_Float32(uint8_t builtin) {
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
LEAN_EXPORT lean_object* initialize_Init_Data_Float_Model_Float32(uint8_t builtin) {
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
res = runtime_initialize_Init_Data_Float_Model_Float32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Float_Model_Float32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Float_Model_Float32(builtin);
}
#ifdef __cplusplus
}
#endif
