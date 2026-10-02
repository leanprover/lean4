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
lean_object* l_Float_Model_UnpackedFloat_fma(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Float32_Model_nan___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Float32_Model_nan___closed__0;
LEAN_EXPORT uint32_t l_Float32_Model_nan;
static const lean_ctor_object l_Float32_Model_inf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Float32_Model_inf___closed__0 = (const lean_object*)&l_Float32_Model_inf___closed__0_value;
static lean_once_cell_t l_Float32_Model_inf___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Float32_Model_inf___closed__1;
LEAN_EXPORT uint32_t l_Float32_Model_inf;
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
LEAN_EXPORT uint32_t l_Float32_Model_fma(uint32_t, uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_fma___boxed(lean_object*, lean_object*, lean_object*);
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
uint32_t v_x_39__boxed_6_; uint32_t v_x_40__boxed_7_; uint8_t v_res_8_; lean_object* v_r_9_; 
v_x_39__boxed_6_ = lean_unbox_uint32(v_x_4_);
lean_dec(v_x_4_);
v_x_40__boxed_7_ = lean_unbox_uint32(v_x_5_);
lean_dec(v_x_5_);
v_res_8_ = l_Float32_instDecidableEqModel_decEq(v_x_39__boxed_6_, v_x_40__boxed_7_);
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
static uint32_t _init_l_Float32_Model_nan___closed__0(void){
_start:
{
lean_object* v___x_36_; uint32_t v___x_37_; 
v___x_36_ = lean_box(1);
v___x_37_ = l_Float32_Model_pack(v___x_36_);
return v___x_37_;
}
}
static uint32_t _init_l_Float32_Model_nan(void){
_start:
{
uint32_t v___x_38_; 
v___x_38_ = lean_uint32_once(&l_Float32_Model_nan___closed__0, &l_Float32_Model_nan___closed__0_once, _init_l_Float32_Model_nan___closed__0);
return v___x_38_;
}
}
static uint32_t _init_l_Float32_Model_inf___closed__1(void){
_start:
{
lean_object* v___x_41_; uint32_t v___x_42_; 
v___x_41_ = ((lean_object*)(l_Float32_Model_inf___closed__0));
v___x_42_ = l_Float32_Model_pack(v___x_41_);
return v___x_42_;
}
}
static uint32_t _init_l_Float32_Model_inf(void){
_start:
{
uint32_t v___x_43_; 
v___x_43_ = lean_uint32_once(&l_Float32_Model_inf___closed__1, &l_Float32_Model_inf___closed__1_once, _init_l_Float32_Model_inf___closed__1);
return v___x_43_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_add(uint32_t v_a_44_, uint32_t v_b_45_){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; uint32_t v___x_50_; 
v___x_46_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_47_ = l_Float32_Model_unpack(v_a_44_);
v___x_48_ = l_Float32_Model_unpack(v_b_45_);
v___x_49_ = l_Float_Model_UnpackedFloat_add(v___x_46_, v___x_47_, v___x_48_);
v___x_50_ = l_Float32_Model_pack(v___x_49_);
lean_dec(v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_add___boxed(lean_object* v_a_51_, lean_object* v_b_52_){
_start:
{
uint32_t v_a_boxed_53_; uint32_t v_b_boxed_54_; uint32_t v_res_55_; lean_object* v_r_56_; 
v_a_boxed_53_ = lean_unbox_uint32(v_a_51_);
lean_dec(v_a_51_);
v_b_boxed_54_ = lean_unbox_uint32(v_b_52_);
lean_dec(v_b_52_);
v_res_55_ = l_Float32_Model_add(v_a_boxed_53_, v_b_boxed_54_);
v_r_56_ = lean_box_uint32(v_res_55_);
return v_r_56_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_sub(uint32_t v_a_57_, uint32_t v_b_58_){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; uint32_t v___x_63_; 
v___x_59_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_60_ = l_Float32_Model_unpack(v_a_57_);
v___x_61_ = l_Float32_Model_unpack(v_b_58_);
v___x_62_ = l_Float_Model_UnpackedFloat_sub(v___x_59_, v___x_60_, v___x_61_);
v___x_63_ = l_Float32_Model_pack(v___x_62_);
lean_dec(v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_sub___boxed(lean_object* v_a_64_, lean_object* v_b_65_){
_start:
{
uint32_t v_a_boxed_66_; uint32_t v_b_boxed_67_; uint32_t v_res_68_; lean_object* v_r_69_; 
v_a_boxed_66_ = lean_unbox_uint32(v_a_64_);
lean_dec(v_a_64_);
v_b_boxed_67_ = lean_unbox_uint32(v_b_65_);
lean_dec(v_b_65_);
v_res_68_ = l_Float32_Model_sub(v_a_boxed_66_, v_b_boxed_67_);
v_r_69_ = lean_box_uint32(v_res_68_);
return v_r_69_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_mul(uint32_t v_a_70_, uint32_t v_b_71_){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; uint32_t v___x_76_; 
v___x_72_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_73_ = l_Float32_Model_unpack(v_a_70_);
v___x_74_ = l_Float32_Model_unpack(v_b_71_);
v___x_75_ = l_Float_Model_UnpackedFloat_mul(v___x_72_, v___x_73_, v___x_74_);
v___x_76_ = l_Float32_Model_pack(v___x_75_);
lean_dec(v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_mul___boxed(lean_object* v_a_77_, lean_object* v_b_78_){
_start:
{
uint32_t v_a_boxed_79_; uint32_t v_b_boxed_80_; uint32_t v_res_81_; lean_object* v_r_82_; 
v_a_boxed_79_ = lean_unbox_uint32(v_a_77_);
lean_dec(v_a_77_);
v_b_boxed_80_ = lean_unbox_uint32(v_b_78_);
lean_dec(v_b_78_);
v_res_81_ = l_Float32_Model_mul(v_a_boxed_79_, v_b_boxed_80_);
v_r_82_ = lean_box_uint32(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_div(uint32_t v_a_83_, uint32_t v_b_84_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; uint32_t v___x_89_; 
v___x_85_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_86_ = l_Float32_Model_unpack(v_a_83_);
v___x_87_ = l_Float32_Model_unpack(v_b_84_);
v___x_88_ = l_Float_Model_UnpackedFloat_div(v___x_85_, v___x_86_, v___x_87_);
v___x_89_ = l_Float32_Model_pack(v___x_88_);
lean_dec(v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_div___boxed(lean_object* v_a_90_, lean_object* v_b_91_){
_start:
{
uint32_t v_a_boxed_92_; uint32_t v_b_boxed_93_; uint32_t v_res_94_; lean_object* v_r_95_; 
v_a_boxed_92_ = lean_unbox_uint32(v_a_90_);
lean_dec(v_a_90_);
v_b_boxed_93_ = lean_unbox_uint32(v_b_91_);
lean_dec(v_b_91_);
v_res_94_ = l_Float32_Model_div(v_a_boxed_92_, v_b_boxed_93_);
v_r_95_ = lean_box_uint32(v_res_94_);
return v_r_95_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_sqrt(uint32_t v_a_104_){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; uint32_t v___x_108_; 
v___x_105_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_106_ = l_Float32_Model_unpack(v_a_104_);
v___x_107_ = l_Float_Model_UnpackedFloat_sqrt(v___x_105_, v___x_106_);
lean_dec(v___x_106_);
v___x_108_ = l_Float32_Model_pack(v___x_107_);
lean_dec(v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_sqrt___boxed(lean_object* v_a_109_){
_start:
{
uint32_t v_a_boxed_110_; uint32_t v_res_111_; lean_object* v_r_112_; 
v_a_boxed_110_ = lean_unbox_uint32(v_a_109_);
lean_dec(v_a_109_);
v_res_111_ = l_Float32_Model_sqrt(v_a_boxed_110_);
v_r_112_ = lean_box_uint32(v_res_111_);
return v_r_112_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_fma(uint32_t v_a_113_, uint32_t v_b_114_, uint32_t v_c_115_){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; uint32_t v___x_121_; 
v___x_116_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_117_ = l_Float32_Model_unpack(v_a_113_);
v___x_118_ = l_Float32_Model_unpack(v_b_114_);
v___x_119_ = l_Float32_Model_unpack(v_c_115_);
v___x_120_ = l_Float_Model_UnpackedFloat_fma(v___x_116_, v___x_117_, v___x_118_, v___x_119_);
v___x_121_ = l_Float32_Model_pack(v___x_120_);
lean_dec(v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_fma___boxed(lean_object* v_a_122_, lean_object* v_b_123_, lean_object* v_c_124_){
_start:
{
uint32_t v_a_boxed_125_; uint32_t v_b_boxed_126_; uint32_t v_c_boxed_127_; uint32_t v_res_128_; lean_object* v_r_129_; 
v_a_boxed_125_ = lean_unbox_uint32(v_a_122_);
lean_dec(v_a_122_);
v_b_boxed_126_ = lean_unbox_uint32(v_b_123_);
lean_dec(v_b_123_);
v_c_boxed_127_ = lean_unbox_uint32(v_c_124_);
lean_dec(v_c_124_);
v_res_128_ = l_Float32_Model_fma(v_a_boxed_125_, v_b_boxed_126_, v_c_boxed_127_);
v_r_129_ = lean_box_uint32(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_neg(uint32_t v_a_130_){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; uint32_t v___x_133_; 
v___x_131_ = l_Float32_Model_unpack(v_a_130_);
v___x_132_ = l_Float_Model_UnpackedFloat_neg(v___x_131_);
v___x_133_ = l_Float32_Model_pack(v___x_132_);
lean_dec(v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_neg___boxed(lean_object* v_a_134_){
_start:
{
uint32_t v_a_boxed_135_; uint32_t v_res_136_; lean_object* v_r_137_; 
v_a_boxed_135_ = lean_unbox_uint32(v_a_134_);
lean_dec(v_a_134_);
v_res_136_ = l_Float32_Model_neg(v_a_boxed_135_);
v_r_137_ = lean_box_uint32(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_abs(uint32_t v_a_140_){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; uint32_t v___x_143_; 
v___x_141_ = l_Float32_Model_unpack(v_a_140_);
v___x_142_ = l_Float_Model_UnpackedFloat_abs(v___x_141_);
v___x_143_ = l_Float32_Model_pack(v___x_142_);
lean_dec(v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_abs___boxed(lean_object* v_a_144_){
_start:
{
uint32_t v_a_boxed_145_; uint32_t v_res_146_; lean_object* v_r_147_; 
v_a_boxed_145_ = lean_unbox_uint32(v_a_144_);
lean_dec(v_a_144_);
v_res_146_ = l_Float32_Model_abs(v_a_boxed_145_);
v_r_147_ = lean_box_uint32(v_res_146_);
return v_r_147_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_compare(uint32_t v_a_148_, uint32_t v_b_149_){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_150_ = l_Float32_Model_unpack(v_a_148_);
v___x_151_ = l_Float32_Model_unpack(v_b_149_);
v___x_152_ = l_Float_Model_UnpackedFloat_compare(v___x_150_, v___x_151_);
lean_dec(v___x_151_);
lean_dec(v___x_150_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_compare___boxed(lean_object* v_a_153_, lean_object* v_b_154_){
_start:
{
uint32_t v_a_boxed_155_; uint32_t v_b_boxed_156_; lean_object* v_res_157_; 
v_a_boxed_155_ = lean_unbox_uint32(v_a_153_);
lean_dec(v_a_153_);
v_b_boxed_156_ = lean_unbox_uint32(v_b_154_);
lean_dec(v_b_154_);
v_res_157_ = l_Float32_Model_compare(v_a_boxed_155_, v_b_boxed_156_);
return v_res_157_;
}
}
LEAN_EXPORT uint8_t l_Float32_Model_le(uint32_t v_a_158_, uint32_t v_b_159_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_160_ = l_Float32_Model_unpack(v_a_158_);
v___x_161_ = l_Float32_Model_unpack(v_b_159_);
v___x_162_ = l_Float_Model_UnpackedFloat_le(v___x_160_, v___x_161_);
lean_dec(v___x_161_);
lean_dec(v___x_160_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_le___boxed(lean_object* v_a_163_, lean_object* v_b_164_){
_start:
{
uint32_t v_a_boxed_165_; uint32_t v_b_boxed_166_; uint8_t v_res_167_; lean_object* v_r_168_; 
v_a_boxed_165_ = lean_unbox_uint32(v_a_163_);
lean_dec(v_a_163_);
v_b_boxed_166_ = lean_unbox_uint32(v_b_164_);
lean_dec(v_b_164_);
v_res_167_ = l_Float32_Model_le(v_a_boxed_165_, v_b_boxed_166_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
LEAN_EXPORT uint8_t l_Float32_Model_lt(uint32_t v_a_169_, uint32_t v_b_170_){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_171_ = l_Float32_Model_unpack(v_a_169_);
v___x_172_ = l_Float32_Model_unpack(v_b_170_);
v___x_173_ = l_Float_Model_UnpackedFloat_lt(v___x_171_, v___x_172_);
lean_dec(v___x_172_);
lean_dec(v___x_171_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_lt___boxed(lean_object* v_a_174_, lean_object* v_b_175_){
_start:
{
uint32_t v_a_boxed_176_; uint32_t v_b_boxed_177_; uint8_t v_res_178_; lean_object* v_r_179_; 
v_a_boxed_176_ = lean_unbox_uint32(v_a_174_);
lean_dec(v_a_174_);
v_b_boxed_177_ = lean_unbox_uint32(v_b_175_);
lean_dec(v_b_175_);
v_res_178_ = l_Float32_Model_lt(v_a_boxed_176_, v_b_boxed_177_);
v_r_179_ = lean_box(v_res_178_);
return v_r_179_;
}
}
LEAN_EXPORT uint8_t l_Float32_Model_beq(uint32_t v_a_180_, uint32_t v_b_181_){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_182_ = l_Float32_Model_unpack(v_a_180_);
v___x_183_ = l_Float32_Model_unpack(v_b_181_);
v___x_184_ = l_Float_Model_UnpackedFloat_beq(v___x_182_, v___x_183_);
lean_dec(v___x_183_);
lean_dec(v___x_182_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_beq___boxed(lean_object* v_a_185_, lean_object* v_b_186_){
_start:
{
uint32_t v_a_boxed_187_; uint32_t v_b_boxed_188_; uint8_t v_res_189_; lean_object* v_r_190_; 
v_a_boxed_187_ = lean_unbox_uint32(v_a_185_);
lean_dec(v_a_185_);
v_b_boxed_188_ = lean_unbox_uint32(v_b_186_);
lean_dec(v_b_186_);
v_res_189_ = l_Float32_Model_beq(v_a_boxed_187_, v_b_boxed_188_);
v_r_190_ = lean_box(v_res_189_);
return v_r_190_;
}
}
static lean_object* _init_l_Float32_Model_instLE(void){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = lean_box(0);
return v___x_191_;
}
}
LEAN_EXPORT uint8_t l_Float32_Model_instDecidableLE(uint32_t v_a_192_, uint32_t v_b_193_){
_start:
{
uint8_t v___x_194_; 
v___x_194_ = l_Float32_Model_le(v_a_192_, v_b_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_instDecidableLE___boxed(lean_object* v_a_195_, lean_object* v_b_196_){
_start:
{
uint32_t v_a_boxed_197_; uint32_t v_b_boxed_198_; uint8_t v_res_199_; lean_object* v_r_200_; 
v_a_boxed_197_ = lean_unbox_uint32(v_a_195_);
lean_dec(v_a_195_);
v_b_boxed_198_ = lean_unbox_uint32(v_b_196_);
lean_dec(v_b_196_);
v_res_199_ = l_Float32_Model_instDecidableLE(v_a_boxed_197_, v_b_boxed_198_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
static lean_object* _init_l_Float32_Model_instLT(void){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = lean_box(0);
return v___x_201_;
}
}
LEAN_EXPORT uint8_t l_Float32_Model_instDecidableLT(uint32_t v_a_202_, uint32_t v_b_203_){
_start:
{
uint8_t v___x_204_; 
v___x_204_ = l_Float32_Model_lt(v_a_202_, v_b_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_instDecidableLT___boxed(lean_object* v_a_205_, lean_object* v_b_206_){
_start:
{
uint32_t v_a_boxed_207_; uint32_t v_b_boxed_208_; uint8_t v_res_209_; lean_object* v_r_210_; 
v_a_boxed_207_ = lean_unbox_uint32(v_a_205_);
lean_dec(v_a_205_);
v_b_boxed_208_ = lean_unbox_uint32(v_b_206_);
lean_dec(v_b_206_);
v_res_209_ = l_Float32_Model_instDecidableLT(v_a_boxed_207_, v_b_boxed_208_);
v_r_210_ = lean_box(v_res_209_);
return v_r_210_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_instMin___lam__0(uint32_t v_a_213_, uint32_t v_b_214_){
_start:
{
uint8_t v___x_215_; 
v___x_215_ = l_Float32_Model_le(v_a_213_, v_b_214_);
if (v___x_215_ == 0)
{
return v_b_214_;
}
else
{
return v_a_213_;
}
}
}
LEAN_EXPORT lean_object* l_Float32_Model_instMin___lam__0___boxed(lean_object* v_a_216_, lean_object* v_b_217_){
_start:
{
uint32_t v_a_boxed_218_; uint32_t v_b_boxed_219_; uint32_t v_res_220_; lean_object* v_r_221_; 
v_a_boxed_218_ = lean_unbox_uint32(v_a_216_);
lean_dec(v_a_216_);
v_b_boxed_219_ = lean_unbox_uint32(v_b_217_);
lean_dec(v_b_217_);
v_res_220_ = l_Float32_Model_instMin___lam__0(v_a_boxed_218_, v_b_boxed_219_);
v_r_221_ = lean_box_uint32(v_res_220_);
return v_r_221_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_instMax___lam__0(uint32_t v_a_224_, uint32_t v_b_225_){
_start:
{
uint8_t v___x_226_; 
v___x_226_ = l_Float32_Model_le(v_b_225_, v_a_224_);
if (v___x_226_ == 0)
{
return v_b_225_;
}
else
{
return v_a_224_;
}
}
}
LEAN_EXPORT lean_object* l_Float32_Model_instMax___lam__0___boxed(lean_object* v_a_227_, lean_object* v_b_228_){
_start:
{
uint32_t v_a_boxed_229_; uint32_t v_b_boxed_230_; uint32_t v_res_231_; lean_object* v_r_232_; 
v_a_boxed_229_ = lean_unbox_uint32(v_a_227_);
lean_dec(v_a_227_);
v_b_boxed_230_ = lean_unbox_uint32(v_b_228_);
lean_dec(v_b_228_);
v_res_231_ = l_Float32_Model_instMax___lam__0(v_a_boxed_229_, v_b_boxed_230_);
v_r_232_ = lean_box_uint32(v_res_231_);
return v_r_232_;
}
}
LEAN_EXPORT uint8_t l_Float32_Model_isFinite(uint32_t v_a_235_){
_start:
{
lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_236_ = l_Float32_Model_unpack(v_a_235_);
v___x_237_ = l_Float_Model_UnpackedFloat_isFinite(v___x_236_);
lean_dec(v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_isFinite___boxed(lean_object* v_a_238_){
_start:
{
uint32_t v_a_boxed_239_; uint8_t v_res_240_; lean_object* v_r_241_; 
v_a_boxed_239_ = lean_unbox_uint32(v_a_238_);
lean_dec(v_a_238_);
v_res_240_ = l_Float32_Model_isFinite(v_a_boxed_239_);
v_r_241_ = lean_box(v_res_240_);
return v_r_241_;
}
}
LEAN_EXPORT uint8_t l_Float32_Model_isInf(uint32_t v_a_242_){
_start:
{
lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_243_ = l_Float32_Model_unpack(v_a_242_);
v___x_244_ = l_Float_Model_UnpackedFloat_isInf(v___x_243_);
lean_dec(v___x_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_isInf___boxed(lean_object* v_a_245_){
_start:
{
uint32_t v_a_boxed_246_; uint8_t v_res_247_; lean_object* v_r_248_; 
v_a_boxed_246_ = lean_unbox_uint32(v_a_245_);
lean_dec(v_a_245_);
v_res_247_ = l_Float32_Model_isInf(v_a_boxed_246_);
v_r_248_ = lean_box(v_res_247_);
return v_r_248_;
}
}
LEAN_EXPORT uint8_t l_Float32_Model_isNaN(uint32_t v_a_249_){
_start:
{
lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_250_ = l_Float32_Model_unpack(v_a_249_);
v___x_251_ = l_Float_Model_UnpackedFloat_isNaN(v___x_250_);
lean_dec(v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_isNaN___boxed(lean_object* v_a_252_){
_start:
{
uint32_t v_a_boxed_253_; uint8_t v_res_254_; lean_object* v_r_255_; 
v_a_boxed_253_ = lean_unbox_uint32(v_a_252_);
lean_dec(v_a_252_);
v_res_254_ = l_Float32_Model_isNaN(v_a_boxed_253_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_ofBits(uint32_t v_a_256_){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; uint32_t v___x_260_; 
v___x_257_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_258_ = lean_uint32_to_nat(v_a_256_);
v___x_259_ = l_Float_Model_UnpackedFloat_unpack(v___x_257_, v___x_258_);
lean_dec(v___x_258_);
v___x_260_ = l_Float32_Model_pack(v___x_259_);
lean_dec(v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_ofBits___boxed(lean_object* v_a_261_){
_start:
{
uint32_t v_a_boxed_262_; uint32_t v_res_263_; lean_object* v_r_264_; 
v_a_boxed_262_ = lean_unbox_uint32(v_a_261_);
lean_dec(v_a_261_);
v_res_263_ = l_Float32_Model_ofBits(v_a_boxed_262_);
v_r_264_ = lean_box_uint32(v_res_263_);
return v_r_264_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_ofInt(lean_object* v_n_265_){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; uint32_t v___x_268_; 
v___x_266_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_267_ = l_Float_Model_UnpackedFloat_ofInt(v___x_266_, v_n_265_);
v___x_268_ = l_Float32_Model_pack(v___x_267_);
lean_dec(v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_ofInt___boxed(lean_object* v_n_269_){
_start:
{
uint32_t v_res_270_; lean_object* v_r_271_; 
v_res_270_ = l_Float32_Model_ofInt(v_n_269_);
lean_dec(v_n_269_);
v_r_271_ = lean_box_uint32(v_res_270_);
return v_r_271_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_ofNat(lean_object* v_n_272_){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; uint32_t v___x_275_; 
v___x_273_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_274_ = l_Float_Model_UnpackedFloat_ofNat(v___x_273_, v_n_272_);
v___x_275_ = l_Float32_Model_pack(v___x_274_);
lean_dec(v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_ofNat___boxed(lean_object* v_n_276_){
_start:
{
uint32_t v_res_277_; lean_object* v_r_278_; 
v_res_277_ = l_Float32_Model_ofNat(v_n_276_);
v_r_278_ = lean_box_uint32(v_res_277_);
return v_r_278_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_ofUInt8(uint8_t v_n_279_){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; uint32_t v___x_282_; 
v___x_280_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_281_ = l_Float_Model_UnpackedFloat_ofUInt8(v___x_280_, v_n_279_);
v___x_282_ = l_Float32_Model_pack(v___x_281_);
lean_dec(v___x_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_ofUInt8___boxed(lean_object* v_n_283_){
_start:
{
uint8_t v_n_boxed_284_; uint32_t v_res_285_; lean_object* v_r_286_; 
v_n_boxed_284_ = lean_unbox(v_n_283_);
v_res_285_ = l_Float32_Model_ofUInt8(v_n_boxed_284_);
v_r_286_ = lean_box_uint32(v_res_285_);
return v_r_286_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_ofUInt16(uint16_t v_n_287_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; uint32_t v___x_290_; 
v___x_288_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_289_ = l_Float_Model_UnpackedFloat_ofUInt16(v___x_288_, v_n_287_);
v___x_290_ = l_Float32_Model_pack(v___x_289_);
lean_dec(v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_ofUInt16___boxed(lean_object* v_n_291_){
_start:
{
uint16_t v_n_boxed_292_; uint32_t v_res_293_; lean_object* v_r_294_; 
v_n_boxed_292_ = lean_unbox(v_n_291_);
v_res_293_ = l_Float32_Model_ofUInt16(v_n_boxed_292_);
v_r_294_ = lean_box_uint32(v_res_293_);
return v_r_294_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_ofUInt32(uint32_t v_n_295_){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; uint32_t v___x_298_; 
v___x_296_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_297_ = l_Float_Model_UnpackedFloat_ofUInt32(v___x_296_, v_n_295_);
v___x_298_ = l_Float32_Model_pack(v___x_297_);
lean_dec(v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_ofUInt32___boxed(lean_object* v_n_299_){
_start:
{
uint32_t v_n_boxed_300_; uint32_t v_res_301_; lean_object* v_r_302_; 
v_n_boxed_300_ = lean_unbox_uint32(v_n_299_);
lean_dec(v_n_299_);
v_res_301_ = l_Float32_Model_ofUInt32(v_n_boxed_300_);
v_r_302_ = lean_box_uint32(v_res_301_);
return v_r_302_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_ofUInt64(uint64_t v_n_303_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; uint32_t v___x_306_; 
v___x_304_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_305_ = l_Float_Model_UnpackedFloat_ofUInt64(v___x_304_, v_n_303_);
v___x_306_ = l_Float32_Model_pack(v___x_305_);
lean_dec(v___x_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_ofUInt64___boxed(lean_object* v_n_307_){
_start:
{
uint64_t v_n_boxed_308_; uint32_t v_res_309_; lean_object* v_r_310_; 
v_n_boxed_308_ = lean_unbox_uint64(v_n_307_);
lean_dec_ref(v_n_307_);
v_res_309_ = l_Float32_Model_ofUInt64(v_n_boxed_308_);
v_r_310_ = lean_box_uint32(v_res_309_);
return v_r_310_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_ofUSize(size_t v_n_311_){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; uint32_t v___x_314_; 
v___x_312_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_313_ = l_Float_Model_UnpackedFloat_ofUSize(v___x_312_, v_n_311_);
v___x_314_ = l_Float32_Model_pack(v___x_313_);
lean_dec(v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_ofUSize___boxed(lean_object* v_n_315_){
_start:
{
size_t v_n_boxed_316_; uint32_t v_res_317_; lean_object* v_r_318_; 
v_n_boxed_316_ = lean_unbox_usize(v_n_315_);
lean_dec(v_n_315_);
v_res_317_ = l_Float32_Model_ofUSize(v_n_boxed_316_);
v_r_318_ = lean_box_uint32(v_res_317_);
return v_r_318_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_ofInt8(uint8_t v_n_319_){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; uint32_t v___x_322_; 
v___x_320_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_321_ = l_Float_Model_UnpackedFloat_ofInt8(v___x_320_, v_n_319_);
v___x_322_ = l_Float32_Model_pack(v___x_321_);
lean_dec(v___x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_ofInt8___boxed(lean_object* v_n_323_){
_start:
{
uint8_t v_n_boxed_324_; uint32_t v_res_325_; lean_object* v_r_326_; 
v_n_boxed_324_ = lean_unbox(v_n_323_);
v_res_325_ = l_Float32_Model_ofInt8(v_n_boxed_324_);
v_r_326_ = lean_box_uint32(v_res_325_);
return v_r_326_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_ofInt16(uint16_t v_n_327_){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; uint32_t v___x_330_; 
v___x_328_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_329_ = l_Float_Model_UnpackedFloat_ofInt16(v___x_328_, v_n_327_);
v___x_330_ = l_Float32_Model_pack(v___x_329_);
lean_dec(v___x_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_ofInt16___boxed(lean_object* v_n_331_){
_start:
{
uint16_t v_n_boxed_332_; uint32_t v_res_333_; lean_object* v_r_334_; 
v_n_boxed_332_ = lean_unbox(v_n_331_);
v_res_333_ = l_Float32_Model_ofInt16(v_n_boxed_332_);
v_r_334_ = lean_box_uint32(v_res_333_);
return v_r_334_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_ofInt32(uint32_t v_n_335_){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; uint32_t v___x_338_; 
v___x_336_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_337_ = l_Float_Model_UnpackedFloat_ofInt32(v___x_336_, v_n_335_);
v___x_338_ = l_Float32_Model_pack(v___x_337_);
lean_dec(v___x_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_ofInt32___boxed(lean_object* v_n_339_){
_start:
{
uint32_t v_n_boxed_340_; uint32_t v_res_341_; lean_object* v_r_342_; 
v_n_boxed_340_ = lean_unbox_uint32(v_n_339_);
lean_dec(v_n_339_);
v_res_341_ = l_Float32_Model_ofInt32(v_n_boxed_340_);
v_r_342_ = lean_box_uint32(v_res_341_);
return v_r_342_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_ofInt64(uint64_t v_n_343_){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; uint32_t v___x_346_; 
v___x_344_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_345_ = l_Float_Model_UnpackedFloat_ofInt64(v___x_344_, v_n_343_);
v___x_346_ = l_Float32_Model_pack(v___x_345_);
lean_dec(v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_ofInt64___boxed(lean_object* v_n_347_){
_start:
{
uint64_t v_n_boxed_348_; uint32_t v_res_349_; lean_object* v_r_350_; 
v_n_boxed_348_ = lean_unbox_uint64(v_n_347_);
lean_dec_ref(v_n_347_);
v_res_349_ = l_Float32_Model_ofInt64(v_n_boxed_348_);
v_r_350_ = lean_box_uint32(v_res_349_);
return v_r_350_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_ofISize(size_t v_n_351_){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; uint32_t v___x_354_; 
v___x_352_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_353_ = l_Float_Model_UnpackedFloat_ofISize(v___x_352_, v_n_351_);
v___x_354_ = l_Float32_Model_pack(v___x_353_);
lean_dec(v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_ofISize___boxed(lean_object* v_n_355_){
_start:
{
size_t v_n_boxed_356_; uint32_t v_res_357_; lean_object* v_r_358_; 
v_n_boxed_356_ = lean_unbox_usize(v_n_355_);
lean_dec(v_n_355_);
v_res_357_ = l_Float32_Model_ofISize(v_n_boxed_356_);
v_r_358_ = lean_box_uint32(v_res_357_);
return v_r_358_;
}
}
LEAN_EXPORT uint8_t l_Float32_Model_toUInt8(uint32_t v_f_359_){
_start:
{
lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_360_ = l_Float32_Model_unpack(v_f_359_);
v___x_361_ = l_Float_Model_UnpackedFloat_toUInt8(v___x_360_);
lean_dec(v___x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_toUInt8___boxed(lean_object* v_f_362_){
_start:
{
uint32_t v_f_boxed_363_; uint8_t v_res_364_; lean_object* v_r_365_; 
v_f_boxed_363_ = lean_unbox_uint32(v_f_362_);
lean_dec(v_f_362_);
v_res_364_ = l_Float32_Model_toUInt8(v_f_boxed_363_);
v_r_365_ = lean_box(v_res_364_);
return v_r_365_;
}
}
LEAN_EXPORT uint16_t l_Float32_Model_toUInt16(uint32_t v_f_366_){
_start:
{
lean_object* v___x_367_; uint16_t v___x_368_; 
v___x_367_ = l_Float32_Model_unpack(v_f_366_);
v___x_368_ = l_Float_Model_UnpackedFloat_toUInt16(v___x_367_);
lean_dec(v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_toUInt16___boxed(lean_object* v_f_369_){
_start:
{
uint32_t v_f_boxed_370_; uint16_t v_res_371_; lean_object* v_r_372_; 
v_f_boxed_370_ = lean_unbox_uint32(v_f_369_);
lean_dec(v_f_369_);
v_res_371_ = l_Float32_Model_toUInt16(v_f_boxed_370_);
v_r_372_ = lean_box(v_res_371_);
return v_r_372_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_toUInt32(uint32_t v_f_373_){
_start:
{
lean_object* v___x_374_; uint32_t v___x_375_; 
v___x_374_ = l_Float32_Model_unpack(v_f_373_);
v___x_375_ = l_Float_Model_UnpackedFloat_toUInt32(v___x_374_);
lean_dec(v___x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_toUInt32___boxed(lean_object* v_f_376_){
_start:
{
uint32_t v_f_boxed_377_; uint32_t v_res_378_; lean_object* v_r_379_; 
v_f_boxed_377_ = lean_unbox_uint32(v_f_376_);
lean_dec(v_f_376_);
v_res_378_ = l_Float32_Model_toUInt32(v_f_boxed_377_);
v_r_379_ = lean_box_uint32(v_res_378_);
return v_r_379_;
}
}
LEAN_EXPORT uint64_t l_Float32_Model_toUInt64(uint32_t v_f_380_){
_start:
{
lean_object* v___x_381_; uint64_t v___x_382_; 
v___x_381_ = l_Float32_Model_unpack(v_f_380_);
v___x_382_ = l_Float_Model_UnpackedFloat_toUInt64(v___x_381_);
lean_dec(v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_toUInt64___boxed(lean_object* v_f_383_){
_start:
{
uint32_t v_f_boxed_384_; uint64_t v_res_385_; lean_object* v_r_386_; 
v_f_boxed_384_ = lean_unbox_uint32(v_f_383_);
lean_dec(v_f_383_);
v_res_385_ = l_Float32_Model_toUInt64(v_f_boxed_384_);
v_r_386_ = lean_box_uint64(v_res_385_);
return v_r_386_;
}
}
LEAN_EXPORT size_t l_Float32_Model_toUSize(uint32_t v_f_387_){
_start:
{
lean_object* v___x_388_; size_t v___x_389_; 
v___x_388_ = l_Float32_Model_unpack(v_f_387_);
v___x_389_ = l_Float_Model_UnpackedFloat_toUSize(v___x_388_);
lean_dec(v___x_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_toUSize___boxed(lean_object* v_f_390_){
_start:
{
uint32_t v_f_boxed_391_; size_t v_res_392_; lean_object* v_r_393_; 
v_f_boxed_391_ = lean_unbox_uint32(v_f_390_);
lean_dec(v_f_390_);
v_res_392_ = l_Float32_Model_toUSize(v_f_boxed_391_);
v_r_393_ = lean_box_usize(v_res_392_);
return v_r_393_;
}
}
LEAN_EXPORT uint8_t l_Float32_Model_toInt8(uint32_t v_f_394_){
_start:
{
lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_395_ = l_Float32_Model_unpack(v_f_394_);
v___x_396_ = l_Float_Model_UnpackedFloat_toInt8(v___x_395_);
lean_dec(v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_toInt8___boxed(lean_object* v_f_397_){
_start:
{
uint32_t v_f_boxed_398_; uint8_t v_res_399_; lean_object* v_r_400_; 
v_f_boxed_398_ = lean_unbox_uint32(v_f_397_);
lean_dec(v_f_397_);
v_res_399_ = l_Float32_Model_toInt8(v_f_boxed_398_);
v_r_400_ = lean_box(v_res_399_);
return v_r_400_;
}
}
LEAN_EXPORT uint16_t l_Float32_Model_toInt16(uint32_t v_f_401_){
_start:
{
lean_object* v___x_402_; uint16_t v___x_403_; 
v___x_402_ = l_Float32_Model_unpack(v_f_401_);
v___x_403_ = l_Float_Model_UnpackedFloat_toInt16(v___x_402_);
lean_dec(v___x_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_toInt16___boxed(lean_object* v_f_404_){
_start:
{
uint32_t v_f_boxed_405_; uint16_t v_res_406_; lean_object* v_r_407_; 
v_f_boxed_405_ = lean_unbox_uint32(v_f_404_);
lean_dec(v_f_404_);
v_res_406_ = l_Float32_Model_toInt16(v_f_boxed_405_);
v_r_407_ = lean_box(v_res_406_);
return v_r_407_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_toInt32(uint32_t v_f_408_){
_start:
{
lean_object* v___x_409_; uint32_t v___x_410_; 
v___x_409_ = l_Float32_Model_unpack(v_f_408_);
v___x_410_ = l_Float_Model_UnpackedFloat_toInt32(v___x_409_);
lean_dec(v___x_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_toInt32___boxed(lean_object* v_f_411_){
_start:
{
uint32_t v_f_boxed_412_; uint32_t v_res_413_; lean_object* v_r_414_; 
v_f_boxed_412_ = lean_unbox_uint32(v_f_411_);
lean_dec(v_f_411_);
v_res_413_ = l_Float32_Model_toInt32(v_f_boxed_412_);
v_r_414_ = lean_box_uint32(v_res_413_);
return v_r_414_;
}
}
LEAN_EXPORT uint64_t l_Float32_Model_toInt64(uint32_t v_f_415_){
_start:
{
lean_object* v___x_416_; uint64_t v___x_417_; 
v___x_416_ = l_Float32_Model_unpack(v_f_415_);
v___x_417_ = l_Float_Model_UnpackedFloat_toInt64(v___x_416_);
lean_dec(v___x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_toInt64___boxed(lean_object* v_f_418_){
_start:
{
uint32_t v_f_boxed_419_; uint64_t v_res_420_; lean_object* v_r_421_; 
v_f_boxed_419_ = lean_unbox_uint32(v_f_418_);
lean_dec(v_f_418_);
v_res_420_ = l_Float32_Model_toInt64(v_f_boxed_419_);
v_r_421_ = lean_box_uint64(v_res_420_);
return v_r_421_;
}
}
LEAN_EXPORT size_t l_Float32_Model_toISize(uint32_t v_f_422_){
_start:
{
lean_object* v___x_423_; size_t v___x_424_; 
v___x_423_ = l_Float32_Model_unpack(v_f_422_);
v___x_424_ = l_Float_Model_UnpackedFloat_toISize(v___x_423_);
lean_dec(v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_toISize___boxed(lean_object* v_f_425_){
_start:
{
uint32_t v_f_boxed_426_; size_t v_res_427_; lean_object* v_r_428_; 
v_f_boxed_426_ = lean_unbox_uint32(v_f_425_);
lean_dec(v_f_425_);
v_res_427_ = l_Float32_Model_toISize(v_f_boxed_426_);
v_r_428_ = lean_box_usize(v_res_427_);
return v_r_428_;
}
}
LEAN_EXPORT uint32_t l_Float32_Model_ofScientific(lean_object* v_m_429_, lean_object* v_e_430_){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; uint32_t v___x_433_; 
v___x_431_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_432_ = l_Float_Model_UnpackedFloat_ofScientific(v___x_431_, v_m_429_, v_e_430_);
v___x_433_ = l_Float32_Model_pack(v___x_432_);
lean_dec(v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Float32_Model_ofScientific___boxed(lean_object* v_m_434_, lean_object* v_e_435_){
_start:
{
uint32_t v_res_436_; lean_object* v_r_437_; 
v_res_436_ = l_Float32_Model_ofScientific(v_m_434_, v_e_435_);
lean_dec(v_e_435_);
v_r_437_ = lean_box_uint32(v_res_436_);
return v_r_437_;
}
}
static uint32_t _init_l_Float32_Model_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_438_; uint32_t v___x_439_; 
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = l_Float32_Model_ofNat(v___x_438_);
return v___x_439_;
}
}
static uint32_t _init_l_Float32_Model_instInhabited(void){
_start:
{
uint32_t v___x_440_; 
v___x_440_ = lean_uint32_once(&l_Float32_Model_instInhabited___closed__0, &l_Float32_Model_instInhabited___closed__0_once, _init_l_Float32_Model_instInhabited___closed__0);
return v___x_440_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Format_Valid(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Pack_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Operations(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Factories(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Float32(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
l_Float32_Model_nan = _init_l_Float32_Model_nan();
l_Float32_Model_inf = _init_l_Float32_Model_inf();
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
