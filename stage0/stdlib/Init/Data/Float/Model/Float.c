// Lean compiler output
// Module: Init.Data.Float.Model.Float
// Imports: public import Init.Data.Float.Model.Format.Valid public import Init.Data.Float.Model.Unpacked.Pack.Lemmas public import Init.Data.Float.Model.Unpacked.Operations
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
lean_object* l_Float_Model_UnpackedFloat_neg(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_maximumNumber(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofInt32(lean_object*, uint32_t);
lean_object* l_Float_Model_UnpackedFloat_mul(lean_object*, lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_minimumNumber(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofInt(lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
uint16_t l_Float_Model_UnpackedFloat_toInt16(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofInt64(lean_object*, uint64_t);
lean_object* l_Float_Model_UnpackedFloat_sqrt(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_fma(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofUInt16(lean_object*, uint16_t);
size_t l_Float_Model_UnpackedFloat_toUSize(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_sub(lean_object*, lean_object*, lean_object*);
uint8_t l_Float_Model_UnpackedFloat_isFinite(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_add(lean_object*, lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofUInt64(lean_object*, uint64_t);
lean_object* l_Float_Model_UnpackedFloat_compare(lean_object*, lean_object*);
uint8_t l_Float_Model_UnpackedFloat_le(lean_object*, lean_object*);
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
lean_object* l_Float_Model_UnpackedFloat_maximum(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_abs(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofUSize(lean_object*, size_t);
lean_object* l_Float_Model_UnpackedFloat_minimum(lean_object*, lean_object*);
uint16_t l_Float_Model_UnpackedFloat_toUInt16(lean_object*);
uint8_t l_Float_Model_UnpackedFloat_toUInt8(lean_object*);
LEAN_EXPORT uint8_t l_Float_instDecidableEqModel_decEq(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Float_instDecidableEqModel_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Float_instDecidableEqModel(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Float_instDecidableEqModel___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Float_Model_unpack___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(52) << 1) | 1)),((lean_object*)(((size_t)(11) << 1) | 1))}};
static const lean_object* l_Float_Model_unpack___closed__0 = (const lean_object*)&l_Float_Model_unpack___closed__0_value;
LEAN_EXPORT lean_object* l_Float_Model_unpack(uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_unpack___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Float_Model_pack(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_pack___boxed(lean_object*);
static lean_once_cell_t l_Float_Model_nan___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Float_Model_nan___closed__0;
LEAN_EXPORT uint64_t l_Float_Model_nan;
static const lean_ctor_object l_Float_Model_inf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Float_Model_inf___closed__0 = (const lean_object*)&l_Float_Model_inf___closed__0_value;
static lean_once_cell_t l_Float_Model_inf___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Float_Model_inf___closed__1;
LEAN_EXPORT uint64_t l_Float_Model_inf;
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
LEAN_EXPORT uint64_t l_Float_Model_fma(uint64_t, uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_fma___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint64_t l_Float_Model_minimum(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_minimum___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Float_Model_minimumNumber(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_minimumNumber___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Float_Model_maximum(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_maximum___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Float_Model_maximumNumber(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Float_Model_maximumNumber___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Float_Model_instMin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_Model_minimum___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Float_Model_instMin___closed__0 = (const lean_object*)&l_Float_Model_instMin___closed__0_value;
LEAN_EXPORT const lean_object* l_Float_Model_instMin = (const lean_object*)&l_Float_Model_instMin___closed__0_value;
static const lean_closure_object l_Float_Model_instMax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_Model_maximum___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT uint8_t l_Float_instDecidableEqModel_decEq(uint64_t v_x_1_, uint64_t v_x_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = lean_uint64_dec_eq(v_x_1_, v_x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Float_instDecidableEqModel_decEq___boxed(lean_object* v_x_4_, lean_object* v_x_5_){
_start:
{
uint64_t v_x_39__boxed_6_; uint64_t v_x_40__boxed_7_; uint8_t v_res_8_; lean_object* v_r_9_; 
v_x_39__boxed_6_ = lean_unbox_uint64(v_x_4_);
lean_dec_ref(v_x_4_);
v_x_40__boxed_7_ = lean_unbox_uint64(v_x_5_);
lean_dec_ref(v_x_5_);
v_res_8_ = l_Float_instDecidableEqModel_decEq(v_x_39__boxed_6_, v_x_40__boxed_7_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
LEAN_EXPORT uint8_t l_Float_instDecidableEqModel(uint64_t v_x_10_, uint64_t v_x_11_){
_start:
{
uint8_t v___x_12_; 
v___x_12_ = lean_uint64_dec_eq(v_x_10_, v_x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Float_instDecidableEqModel___boxed(lean_object* v_x_13_, lean_object* v_x_14_){
_start:
{
uint64_t v_x_6__boxed_15_; uint64_t v_x_7__boxed_16_; uint8_t v_res_17_; lean_object* v_r_18_; 
v_x_6__boxed_15_ = lean_unbox_uint64(v_x_13_);
lean_dec_ref(v_x_13_);
v_x_7__boxed_16_ = lean_unbox_uint64(v_x_14_);
lean_dec_ref(v_x_14_);
v_res_17_ = l_Float_instDecidableEqModel(v_x_6__boxed_15_, v_x_7__boxed_16_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_unpack(uint64_t v_f_22_){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_23_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_24_ = lean_uint64_to_nat(v_f_22_);
v___x_25_ = l_Float_Model_UnpackedFloat_unpack(v___x_23_, v___x_24_);
lean_dec(v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_unpack___boxed(lean_object* v_f_26_){
_start:
{
uint64_t v_f_boxed_27_; lean_object* v_res_28_; 
v_f_boxed_27_ = lean_unbox_uint64(v_f_26_);
lean_dec_ref(v_f_26_);
v_res_28_ = l_Float_Model_unpack(v_f_boxed_27_);
return v_res_28_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_pack(lean_object* v_f_29_){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; uint64_t v___x_32_; 
v___x_30_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_31_ = l_Float_Model_UnpackedFloat_pack(v___x_30_, v_f_29_);
v___x_32_ = lean_uint64_of_nat_mk(v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_pack___boxed(lean_object* v_f_33_){
_start:
{
uint64_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l_Float_Model_pack(v_f_33_);
lean_dec(v_f_33_);
v_r_35_ = lean_box_uint64(v_res_34_);
return v_r_35_;
}
}
static uint64_t _init_l_Float_Model_nan___closed__0(void){
_start:
{
lean_object* v___x_36_; uint64_t v___x_37_; 
v___x_36_ = lean_box(1);
v___x_37_ = l_Float_Model_pack(v___x_36_);
return v___x_37_;
}
}
static uint64_t _init_l_Float_Model_nan(void){
_start:
{
uint64_t v___x_38_; 
v___x_38_ = lean_uint64_once(&l_Float_Model_nan___closed__0, &l_Float_Model_nan___closed__0_once, _init_l_Float_Model_nan___closed__0);
return v___x_38_;
}
}
static uint64_t _init_l_Float_Model_inf___closed__1(void){
_start:
{
lean_object* v___x_41_; uint64_t v___x_42_; 
v___x_41_ = ((lean_object*)(l_Float_Model_inf___closed__0));
v___x_42_ = l_Float_Model_pack(v___x_41_);
return v___x_42_;
}
}
static uint64_t _init_l_Float_Model_inf(void){
_start:
{
uint64_t v___x_43_; 
v___x_43_ = lean_uint64_once(&l_Float_Model_inf___closed__1, &l_Float_Model_inf___closed__1_once, _init_l_Float_Model_inf___closed__1);
return v___x_43_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_add(uint64_t v_a_44_, uint64_t v_b_45_){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; uint64_t v___x_50_; 
v___x_46_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_47_ = l_Float_Model_unpack(v_a_44_);
v___x_48_ = l_Float_Model_unpack(v_b_45_);
v___x_49_ = l_Float_Model_UnpackedFloat_add(v___x_46_, v___x_47_, v___x_48_);
v___x_50_ = l_Float_Model_pack(v___x_49_);
lean_dec(v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_add___boxed(lean_object* v_a_51_, lean_object* v_b_52_){
_start:
{
uint64_t v_a_boxed_53_; uint64_t v_b_boxed_54_; uint64_t v_res_55_; lean_object* v_r_56_; 
v_a_boxed_53_ = lean_unbox_uint64(v_a_51_);
lean_dec_ref(v_a_51_);
v_b_boxed_54_ = lean_unbox_uint64(v_b_52_);
lean_dec_ref(v_b_52_);
v_res_55_ = l_Float_Model_add(v_a_boxed_53_, v_b_boxed_54_);
v_r_56_ = lean_box_uint64(v_res_55_);
return v_r_56_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_sub(uint64_t v_a_57_, uint64_t v_b_58_){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; uint64_t v___x_63_; 
v___x_59_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_60_ = l_Float_Model_unpack(v_a_57_);
v___x_61_ = l_Float_Model_unpack(v_b_58_);
v___x_62_ = l_Float_Model_UnpackedFloat_sub(v___x_59_, v___x_60_, v___x_61_);
v___x_63_ = l_Float_Model_pack(v___x_62_);
lean_dec(v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_sub___boxed(lean_object* v_a_64_, lean_object* v_b_65_){
_start:
{
uint64_t v_a_boxed_66_; uint64_t v_b_boxed_67_; uint64_t v_res_68_; lean_object* v_r_69_; 
v_a_boxed_66_ = lean_unbox_uint64(v_a_64_);
lean_dec_ref(v_a_64_);
v_b_boxed_67_ = lean_unbox_uint64(v_b_65_);
lean_dec_ref(v_b_65_);
v_res_68_ = l_Float_Model_sub(v_a_boxed_66_, v_b_boxed_67_);
v_r_69_ = lean_box_uint64(v_res_68_);
return v_r_69_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_mul(uint64_t v_a_70_, uint64_t v_b_71_){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; uint64_t v___x_76_; 
v___x_72_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_73_ = l_Float_Model_unpack(v_a_70_);
v___x_74_ = l_Float_Model_unpack(v_b_71_);
v___x_75_ = l_Float_Model_UnpackedFloat_mul(v___x_72_, v___x_73_, v___x_74_);
v___x_76_ = l_Float_Model_pack(v___x_75_);
lean_dec(v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_mul___boxed(lean_object* v_a_77_, lean_object* v_b_78_){
_start:
{
uint64_t v_a_boxed_79_; uint64_t v_b_boxed_80_; uint64_t v_res_81_; lean_object* v_r_82_; 
v_a_boxed_79_ = lean_unbox_uint64(v_a_77_);
lean_dec_ref(v_a_77_);
v_b_boxed_80_ = lean_unbox_uint64(v_b_78_);
lean_dec_ref(v_b_78_);
v_res_81_ = l_Float_Model_mul(v_a_boxed_79_, v_b_boxed_80_);
v_r_82_ = lean_box_uint64(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_div(uint64_t v_a_83_, uint64_t v_b_84_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; uint64_t v___x_89_; 
v___x_85_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_86_ = l_Float_Model_unpack(v_a_83_);
v___x_87_ = l_Float_Model_unpack(v_b_84_);
v___x_88_ = l_Float_Model_UnpackedFloat_div(v___x_85_, v___x_86_, v___x_87_);
v___x_89_ = l_Float_Model_pack(v___x_88_);
lean_dec(v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_div___boxed(lean_object* v_a_90_, lean_object* v_b_91_){
_start:
{
uint64_t v_a_boxed_92_; uint64_t v_b_boxed_93_; uint64_t v_res_94_; lean_object* v_r_95_; 
v_a_boxed_92_ = lean_unbox_uint64(v_a_90_);
lean_dec_ref(v_a_90_);
v_b_boxed_93_ = lean_unbox_uint64(v_b_91_);
lean_dec_ref(v_b_91_);
v_res_94_ = l_Float_Model_div(v_a_boxed_92_, v_b_boxed_93_);
v_r_95_ = lean_box_uint64(v_res_94_);
return v_r_95_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_sqrt(uint64_t v_a_104_){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; uint64_t v___x_108_; 
v___x_105_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_106_ = l_Float_Model_unpack(v_a_104_);
v___x_107_ = l_Float_Model_UnpackedFloat_sqrt(v___x_105_, v___x_106_);
lean_dec(v___x_106_);
v___x_108_ = l_Float_Model_pack(v___x_107_);
lean_dec(v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_sqrt___boxed(lean_object* v_a_109_){
_start:
{
uint64_t v_a_boxed_110_; uint64_t v_res_111_; lean_object* v_r_112_; 
v_a_boxed_110_ = lean_unbox_uint64(v_a_109_);
lean_dec_ref(v_a_109_);
v_res_111_ = l_Float_Model_sqrt(v_a_boxed_110_);
v_r_112_ = lean_box_uint64(v_res_111_);
return v_r_112_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_fma(uint64_t v_a_113_, uint64_t v_b_114_, uint64_t v_c_115_){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; uint64_t v___x_121_; 
v___x_116_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_117_ = l_Float_Model_unpack(v_a_113_);
v___x_118_ = l_Float_Model_unpack(v_b_114_);
v___x_119_ = l_Float_Model_unpack(v_c_115_);
v___x_120_ = l_Float_Model_UnpackedFloat_fma(v___x_116_, v___x_117_, v___x_118_, v___x_119_);
v___x_121_ = l_Float_Model_pack(v___x_120_);
lean_dec(v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_fma___boxed(lean_object* v_a_122_, lean_object* v_b_123_, lean_object* v_c_124_){
_start:
{
uint64_t v_a_boxed_125_; uint64_t v_b_boxed_126_; uint64_t v_c_boxed_127_; uint64_t v_res_128_; lean_object* v_r_129_; 
v_a_boxed_125_ = lean_unbox_uint64(v_a_122_);
lean_dec_ref(v_a_122_);
v_b_boxed_126_ = lean_unbox_uint64(v_b_123_);
lean_dec_ref(v_b_123_);
v_c_boxed_127_ = lean_unbox_uint64(v_c_124_);
lean_dec_ref(v_c_124_);
v_res_128_ = l_Float_Model_fma(v_a_boxed_125_, v_b_boxed_126_, v_c_boxed_127_);
v_r_129_ = lean_box_uint64(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_neg(uint64_t v_a_130_){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; uint64_t v___x_133_; 
v___x_131_ = l_Float_Model_unpack(v_a_130_);
v___x_132_ = l_Float_Model_UnpackedFloat_neg(v___x_131_);
v___x_133_ = l_Float_Model_pack(v___x_132_);
lean_dec(v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_neg___boxed(lean_object* v_a_134_){
_start:
{
uint64_t v_a_boxed_135_; uint64_t v_res_136_; lean_object* v_r_137_; 
v_a_boxed_135_ = lean_unbox_uint64(v_a_134_);
lean_dec_ref(v_a_134_);
v_res_136_ = l_Float_Model_neg(v_a_boxed_135_);
v_r_137_ = lean_box_uint64(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_abs(uint64_t v_a_140_){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; uint64_t v___x_143_; 
v___x_141_ = l_Float_Model_unpack(v_a_140_);
v___x_142_ = l_Float_Model_UnpackedFloat_abs(v___x_141_);
v___x_143_ = l_Float_Model_pack(v___x_142_);
lean_dec(v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_abs___boxed(lean_object* v_a_144_){
_start:
{
uint64_t v_a_boxed_145_; uint64_t v_res_146_; lean_object* v_r_147_; 
v_a_boxed_145_ = lean_unbox_uint64(v_a_144_);
lean_dec_ref(v_a_144_);
v_res_146_ = l_Float_Model_abs(v_a_boxed_145_);
v_r_147_ = lean_box_uint64(v_res_146_);
return v_r_147_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_compare(uint64_t v_a_148_, uint64_t v_b_149_){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_150_ = l_Float_Model_unpack(v_a_148_);
v___x_151_ = l_Float_Model_unpack(v_b_149_);
v___x_152_ = l_Float_Model_UnpackedFloat_compare(v___x_150_, v___x_151_);
lean_dec(v___x_151_);
lean_dec(v___x_150_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_compare___boxed(lean_object* v_a_153_, lean_object* v_b_154_){
_start:
{
uint64_t v_a_boxed_155_; uint64_t v_b_boxed_156_; lean_object* v_res_157_; 
v_a_boxed_155_ = lean_unbox_uint64(v_a_153_);
lean_dec_ref(v_a_153_);
v_b_boxed_156_ = lean_unbox_uint64(v_b_154_);
lean_dec_ref(v_b_154_);
v_res_157_ = l_Float_Model_compare(v_a_boxed_155_, v_b_boxed_156_);
return v_res_157_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_le(uint64_t v_a_158_, uint64_t v_b_159_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_160_ = l_Float_Model_unpack(v_a_158_);
v___x_161_ = l_Float_Model_unpack(v_b_159_);
v___x_162_ = l_Float_Model_UnpackedFloat_le(v___x_160_, v___x_161_);
lean_dec(v___x_161_);
lean_dec(v___x_160_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_le___boxed(lean_object* v_a_163_, lean_object* v_b_164_){
_start:
{
uint64_t v_a_boxed_165_; uint64_t v_b_boxed_166_; uint8_t v_res_167_; lean_object* v_r_168_; 
v_a_boxed_165_ = lean_unbox_uint64(v_a_163_);
lean_dec_ref(v_a_163_);
v_b_boxed_166_ = lean_unbox_uint64(v_b_164_);
lean_dec_ref(v_b_164_);
v_res_167_ = l_Float_Model_le(v_a_boxed_165_, v_b_boxed_166_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_lt(uint64_t v_a_169_, uint64_t v_b_170_){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_171_ = l_Float_Model_unpack(v_a_169_);
v___x_172_ = l_Float_Model_unpack(v_b_170_);
v___x_173_ = l_Float_Model_UnpackedFloat_lt(v___x_171_, v___x_172_);
lean_dec(v___x_172_);
lean_dec(v___x_171_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_lt___boxed(lean_object* v_a_174_, lean_object* v_b_175_){
_start:
{
uint64_t v_a_boxed_176_; uint64_t v_b_boxed_177_; uint8_t v_res_178_; lean_object* v_r_179_; 
v_a_boxed_176_ = lean_unbox_uint64(v_a_174_);
lean_dec_ref(v_a_174_);
v_b_boxed_177_ = lean_unbox_uint64(v_b_175_);
lean_dec_ref(v_b_175_);
v_res_178_ = l_Float_Model_lt(v_a_boxed_176_, v_b_boxed_177_);
v_r_179_ = lean_box(v_res_178_);
return v_r_179_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_beq(uint64_t v_a_180_, uint64_t v_b_181_){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_182_ = l_Float_Model_unpack(v_a_180_);
v___x_183_ = l_Float_Model_unpack(v_b_181_);
v___x_184_ = l_Float_Model_UnpackedFloat_beq(v___x_182_, v___x_183_);
lean_dec(v___x_183_);
lean_dec(v___x_182_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_beq___boxed(lean_object* v_a_185_, lean_object* v_b_186_){
_start:
{
uint64_t v_a_boxed_187_; uint64_t v_b_boxed_188_; uint8_t v_res_189_; lean_object* v_r_190_; 
v_a_boxed_187_ = lean_unbox_uint64(v_a_185_);
lean_dec_ref(v_a_185_);
v_b_boxed_188_ = lean_unbox_uint64(v_b_186_);
lean_dec_ref(v_b_186_);
v_res_189_ = l_Float_Model_beq(v_a_boxed_187_, v_b_boxed_188_);
v_r_190_ = lean_box(v_res_189_);
return v_r_190_;
}
}
static lean_object* _init_l_Float_Model_instLE(void){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = lean_box(0);
return v___x_191_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_instDecidableLE(uint64_t v_a_192_, uint64_t v_b_193_){
_start:
{
uint8_t v___x_194_; 
v___x_194_ = l_Float_Model_le(v_a_192_, v_b_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_instDecidableLE___boxed(lean_object* v_a_195_, lean_object* v_b_196_){
_start:
{
uint64_t v_a_boxed_197_; uint64_t v_b_boxed_198_; uint8_t v_res_199_; lean_object* v_r_200_; 
v_a_boxed_197_ = lean_unbox_uint64(v_a_195_);
lean_dec_ref(v_a_195_);
v_b_boxed_198_ = lean_unbox_uint64(v_b_196_);
lean_dec_ref(v_b_196_);
v_res_199_ = l_Float_Model_instDecidableLE(v_a_boxed_197_, v_b_boxed_198_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
static lean_object* _init_l_Float_Model_instLT(void){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = lean_box(0);
return v___x_201_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_instDecidableLT(uint64_t v_a_202_, uint64_t v_b_203_){
_start:
{
uint8_t v___x_204_; 
v___x_204_ = l_Float_Model_lt(v_a_202_, v_b_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_instDecidableLT___boxed(lean_object* v_a_205_, lean_object* v_b_206_){
_start:
{
uint64_t v_a_boxed_207_; uint64_t v_b_boxed_208_; uint8_t v_res_209_; lean_object* v_r_210_; 
v_a_boxed_207_ = lean_unbox_uint64(v_a_205_);
lean_dec_ref(v_a_205_);
v_b_boxed_208_ = lean_unbox_uint64(v_b_206_);
lean_dec_ref(v_b_206_);
v_res_209_ = l_Float_Model_instDecidableLT(v_a_boxed_207_, v_b_boxed_208_);
v_r_210_ = lean_box(v_res_209_);
return v_r_210_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_minimum(uint64_t v_a_213_, uint64_t v_b_214_){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; uint64_t v___x_218_; 
v___x_215_ = l_Float_Model_unpack(v_a_213_);
v___x_216_ = l_Float_Model_unpack(v_b_214_);
v___x_217_ = l_Float_Model_UnpackedFloat_minimum(v___x_215_, v___x_216_);
lean_dec(v___x_216_);
lean_dec(v___x_215_);
v___x_218_ = l_Float_Model_pack(v___x_217_);
lean_dec(v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_minimum___boxed(lean_object* v_a_219_, lean_object* v_b_220_){
_start:
{
uint64_t v_a_boxed_221_; uint64_t v_b_boxed_222_; uint64_t v_res_223_; lean_object* v_r_224_; 
v_a_boxed_221_ = lean_unbox_uint64(v_a_219_);
lean_dec_ref(v_a_219_);
v_b_boxed_222_ = lean_unbox_uint64(v_b_220_);
lean_dec_ref(v_b_220_);
v_res_223_ = l_Float_Model_minimum(v_a_boxed_221_, v_b_boxed_222_);
v_r_224_ = lean_box_uint64(v_res_223_);
return v_r_224_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_minimumNumber(uint64_t v_a_225_, uint64_t v_b_226_){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; uint64_t v___x_230_; 
v___x_227_ = l_Float_Model_unpack(v_a_225_);
v___x_228_ = l_Float_Model_unpack(v_b_226_);
v___x_229_ = l_Float_Model_UnpackedFloat_minimumNumber(v___x_227_, v___x_228_);
lean_dec(v___x_228_);
lean_dec(v___x_227_);
v___x_230_ = l_Float_Model_pack(v___x_229_);
lean_dec(v___x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_minimumNumber___boxed(lean_object* v_a_231_, lean_object* v_b_232_){
_start:
{
uint64_t v_a_boxed_233_; uint64_t v_b_boxed_234_; uint64_t v_res_235_; lean_object* v_r_236_; 
v_a_boxed_233_ = lean_unbox_uint64(v_a_231_);
lean_dec_ref(v_a_231_);
v_b_boxed_234_ = lean_unbox_uint64(v_b_232_);
lean_dec_ref(v_b_232_);
v_res_235_ = l_Float_Model_minimumNumber(v_a_boxed_233_, v_b_boxed_234_);
v_r_236_ = lean_box_uint64(v_res_235_);
return v_r_236_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_maximum(uint64_t v_a_237_, uint64_t v_b_238_){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; uint64_t v___x_242_; 
v___x_239_ = l_Float_Model_unpack(v_a_237_);
v___x_240_ = l_Float_Model_unpack(v_b_238_);
v___x_241_ = l_Float_Model_UnpackedFloat_maximum(v___x_239_, v___x_240_);
lean_dec(v___x_240_);
lean_dec(v___x_239_);
v___x_242_ = l_Float_Model_pack(v___x_241_);
lean_dec(v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_maximum___boxed(lean_object* v_a_243_, lean_object* v_b_244_){
_start:
{
uint64_t v_a_boxed_245_; uint64_t v_b_boxed_246_; uint64_t v_res_247_; lean_object* v_r_248_; 
v_a_boxed_245_ = lean_unbox_uint64(v_a_243_);
lean_dec_ref(v_a_243_);
v_b_boxed_246_ = lean_unbox_uint64(v_b_244_);
lean_dec_ref(v_b_244_);
v_res_247_ = l_Float_Model_maximum(v_a_boxed_245_, v_b_boxed_246_);
v_r_248_ = lean_box_uint64(v_res_247_);
return v_r_248_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_maximumNumber(uint64_t v_a_249_, uint64_t v_b_250_){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint64_t v___x_254_; 
v___x_251_ = l_Float_Model_unpack(v_a_249_);
v___x_252_ = l_Float_Model_unpack(v_b_250_);
v___x_253_ = l_Float_Model_UnpackedFloat_maximumNumber(v___x_251_, v___x_252_);
lean_dec(v___x_252_);
lean_dec(v___x_251_);
v___x_254_ = l_Float_Model_pack(v___x_253_);
lean_dec(v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_maximumNumber___boxed(lean_object* v_a_255_, lean_object* v_b_256_){
_start:
{
uint64_t v_a_boxed_257_; uint64_t v_b_boxed_258_; uint64_t v_res_259_; lean_object* v_r_260_; 
v_a_boxed_257_ = lean_unbox_uint64(v_a_255_);
lean_dec_ref(v_a_255_);
v_b_boxed_258_ = lean_unbox_uint64(v_b_256_);
lean_dec_ref(v_b_256_);
v_res_259_ = l_Float_Model_maximumNumber(v_a_boxed_257_, v_b_boxed_258_);
v_r_260_ = lean_box_uint64(v_res_259_);
return v_r_260_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_isFinite(uint64_t v_a_265_){
_start:
{
lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = l_Float_Model_unpack(v_a_265_);
v___x_267_ = l_Float_Model_UnpackedFloat_isFinite(v___x_266_);
lean_dec(v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_isFinite___boxed(lean_object* v_a_268_){
_start:
{
uint64_t v_a_boxed_269_; uint8_t v_res_270_; lean_object* v_r_271_; 
v_a_boxed_269_ = lean_unbox_uint64(v_a_268_);
lean_dec_ref(v_a_268_);
v_res_270_ = l_Float_Model_isFinite(v_a_boxed_269_);
v_r_271_ = lean_box(v_res_270_);
return v_r_271_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_isInf(uint64_t v_a_272_){
_start:
{
lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_273_ = l_Float_Model_unpack(v_a_272_);
v___x_274_ = l_Float_Model_UnpackedFloat_isInf(v___x_273_);
lean_dec(v___x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_isInf___boxed(lean_object* v_a_275_){
_start:
{
uint64_t v_a_boxed_276_; uint8_t v_res_277_; lean_object* v_r_278_; 
v_a_boxed_276_ = lean_unbox_uint64(v_a_275_);
lean_dec_ref(v_a_275_);
v_res_277_ = l_Float_Model_isInf(v_a_boxed_276_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_isNaN(uint64_t v_a_279_){
_start:
{
lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_280_ = l_Float_Model_unpack(v_a_279_);
v___x_281_ = l_Float_Model_UnpackedFloat_isNaN(v___x_280_);
lean_dec(v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_isNaN___boxed(lean_object* v_a_282_){
_start:
{
uint64_t v_a_boxed_283_; uint8_t v_res_284_; lean_object* v_r_285_; 
v_a_boxed_283_ = lean_unbox_uint64(v_a_282_);
lean_dec_ref(v_a_282_);
v_res_284_ = l_Float_Model_isNaN(v_a_boxed_283_);
v_r_285_ = lean_box(v_res_284_);
return v_r_285_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofBits(uint64_t v_a_286_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; uint64_t v___x_290_; 
v___x_287_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_288_ = lean_uint64_to_nat(v_a_286_);
v___x_289_ = l_Float_Model_UnpackedFloat_unpack(v___x_287_, v___x_288_);
lean_dec(v___x_288_);
v___x_290_ = l_Float_Model_pack(v___x_289_);
lean_dec(v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofBits___boxed(lean_object* v_a_291_){
_start:
{
uint64_t v_a_boxed_292_; uint64_t v_res_293_; lean_object* v_r_294_; 
v_a_boxed_292_ = lean_unbox_uint64(v_a_291_);
lean_dec_ref(v_a_291_);
v_res_293_ = l_Float_Model_ofBits(v_a_boxed_292_);
v_r_294_ = lean_box_uint64(v_res_293_);
return v_r_294_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofInt(lean_object* v_n_295_){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; uint64_t v___x_298_; 
v___x_296_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_297_ = l_Float_Model_UnpackedFloat_ofInt(v___x_296_, v_n_295_);
v___x_298_ = l_Float_Model_pack(v___x_297_);
lean_dec(v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofInt___boxed(lean_object* v_n_299_){
_start:
{
uint64_t v_res_300_; lean_object* v_r_301_; 
v_res_300_ = l_Float_Model_ofInt(v_n_299_);
lean_dec(v_n_299_);
v_r_301_ = lean_box_uint64(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofNat(lean_object* v_n_302_){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; uint64_t v___x_305_; 
v___x_303_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_304_ = l_Float_Model_UnpackedFloat_ofNat(v___x_303_, v_n_302_);
v___x_305_ = l_Float_Model_pack(v___x_304_);
lean_dec(v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofNat___boxed(lean_object* v_n_306_){
_start:
{
uint64_t v_res_307_; lean_object* v_r_308_; 
v_res_307_ = l_Float_Model_ofNat(v_n_306_);
v_r_308_ = lean_box_uint64(v_res_307_);
return v_r_308_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofUInt8(uint8_t v_n_309_){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; uint64_t v___x_312_; 
v___x_310_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_311_ = l_Float_Model_UnpackedFloat_ofUInt8(v___x_310_, v_n_309_);
v___x_312_ = l_Float_Model_pack(v___x_311_);
lean_dec(v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofUInt8___boxed(lean_object* v_n_313_){
_start:
{
uint8_t v_n_boxed_314_; uint64_t v_res_315_; lean_object* v_r_316_; 
v_n_boxed_314_ = lean_unbox(v_n_313_);
v_res_315_ = l_Float_Model_ofUInt8(v_n_boxed_314_);
v_r_316_ = lean_box_uint64(v_res_315_);
return v_r_316_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofUInt16(uint16_t v_n_317_){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; uint64_t v___x_320_; 
v___x_318_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_319_ = l_Float_Model_UnpackedFloat_ofUInt16(v___x_318_, v_n_317_);
v___x_320_ = l_Float_Model_pack(v___x_319_);
lean_dec(v___x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofUInt16___boxed(lean_object* v_n_321_){
_start:
{
uint16_t v_n_boxed_322_; uint64_t v_res_323_; lean_object* v_r_324_; 
v_n_boxed_322_ = lean_unbox(v_n_321_);
v_res_323_ = l_Float_Model_ofUInt16(v_n_boxed_322_);
v_r_324_ = lean_box_uint64(v_res_323_);
return v_r_324_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofUInt32(uint32_t v_n_325_){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; uint64_t v___x_328_; 
v___x_326_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_327_ = l_Float_Model_UnpackedFloat_ofUInt32(v___x_326_, v_n_325_);
v___x_328_ = l_Float_Model_pack(v___x_327_);
lean_dec(v___x_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofUInt32___boxed(lean_object* v_n_329_){
_start:
{
uint32_t v_n_boxed_330_; uint64_t v_res_331_; lean_object* v_r_332_; 
v_n_boxed_330_ = lean_unbox_uint32(v_n_329_);
lean_dec(v_n_329_);
v_res_331_ = l_Float_Model_ofUInt32(v_n_boxed_330_);
v_r_332_ = lean_box_uint64(v_res_331_);
return v_r_332_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofUInt64(uint64_t v_n_333_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; uint64_t v___x_336_; 
v___x_334_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_335_ = l_Float_Model_UnpackedFloat_ofUInt64(v___x_334_, v_n_333_);
v___x_336_ = l_Float_Model_pack(v___x_335_);
lean_dec(v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofUInt64___boxed(lean_object* v_n_337_){
_start:
{
uint64_t v_n_boxed_338_; uint64_t v_res_339_; lean_object* v_r_340_; 
v_n_boxed_338_ = lean_unbox_uint64(v_n_337_);
lean_dec_ref(v_n_337_);
v_res_339_ = l_Float_Model_ofUInt64(v_n_boxed_338_);
v_r_340_ = lean_box_uint64(v_res_339_);
return v_r_340_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofUSize(size_t v_n_341_){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; uint64_t v___x_344_; 
v___x_342_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_343_ = l_Float_Model_UnpackedFloat_ofUSize(v___x_342_, v_n_341_);
v___x_344_ = l_Float_Model_pack(v___x_343_);
lean_dec(v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofUSize___boxed(lean_object* v_n_345_){
_start:
{
size_t v_n_boxed_346_; uint64_t v_res_347_; lean_object* v_r_348_; 
v_n_boxed_346_ = lean_unbox_usize(v_n_345_);
lean_dec(v_n_345_);
v_res_347_ = l_Float_Model_ofUSize(v_n_boxed_346_);
v_r_348_ = lean_box_uint64(v_res_347_);
return v_r_348_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofInt8(uint8_t v_n_349_){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; uint64_t v___x_352_; 
v___x_350_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_351_ = l_Float_Model_UnpackedFloat_ofInt8(v___x_350_, v_n_349_);
v___x_352_ = l_Float_Model_pack(v___x_351_);
lean_dec(v___x_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofInt8___boxed(lean_object* v_n_353_){
_start:
{
uint8_t v_n_boxed_354_; uint64_t v_res_355_; lean_object* v_r_356_; 
v_n_boxed_354_ = lean_unbox(v_n_353_);
v_res_355_ = l_Float_Model_ofInt8(v_n_boxed_354_);
v_r_356_ = lean_box_uint64(v_res_355_);
return v_r_356_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofInt16(uint16_t v_n_357_){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; uint64_t v___x_360_; 
v___x_358_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_359_ = l_Float_Model_UnpackedFloat_ofInt16(v___x_358_, v_n_357_);
v___x_360_ = l_Float_Model_pack(v___x_359_);
lean_dec(v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofInt16___boxed(lean_object* v_n_361_){
_start:
{
uint16_t v_n_boxed_362_; uint64_t v_res_363_; lean_object* v_r_364_; 
v_n_boxed_362_ = lean_unbox(v_n_361_);
v_res_363_ = l_Float_Model_ofInt16(v_n_boxed_362_);
v_r_364_ = lean_box_uint64(v_res_363_);
return v_r_364_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofInt32(uint32_t v_n_365_){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; uint64_t v___x_368_; 
v___x_366_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_367_ = l_Float_Model_UnpackedFloat_ofInt32(v___x_366_, v_n_365_);
v___x_368_ = l_Float_Model_pack(v___x_367_);
lean_dec(v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofInt32___boxed(lean_object* v_n_369_){
_start:
{
uint32_t v_n_boxed_370_; uint64_t v_res_371_; lean_object* v_r_372_; 
v_n_boxed_370_ = lean_unbox_uint32(v_n_369_);
lean_dec(v_n_369_);
v_res_371_ = l_Float_Model_ofInt32(v_n_boxed_370_);
v_r_372_ = lean_box_uint64(v_res_371_);
return v_r_372_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofInt64(uint64_t v_n_373_){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; uint64_t v___x_376_; 
v___x_374_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_375_ = l_Float_Model_UnpackedFloat_ofInt64(v___x_374_, v_n_373_);
v___x_376_ = l_Float_Model_pack(v___x_375_);
lean_dec(v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofInt64___boxed(lean_object* v_n_377_){
_start:
{
uint64_t v_n_boxed_378_; uint64_t v_res_379_; lean_object* v_r_380_; 
v_n_boxed_378_ = lean_unbox_uint64(v_n_377_);
lean_dec_ref(v_n_377_);
v_res_379_ = l_Float_Model_ofInt64(v_n_boxed_378_);
v_r_380_ = lean_box_uint64(v_res_379_);
return v_r_380_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofISize(size_t v_n_381_){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; uint64_t v___x_384_; 
v___x_382_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_383_ = l_Float_Model_UnpackedFloat_ofISize(v___x_382_, v_n_381_);
v___x_384_ = l_Float_Model_pack(v___x_383_);
lean_dec(v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofISize___boxed(lean_object* v_n_385_){
_start:
{
size_t v_n_boxed_386_; uint64_t v_res_387_; lean_object* v_r_388_; 
v_n_boxed_386_ = lean_unbox_usize(v_n_385_);
lean_dec(v_n_385_);
v_res_387_ = l_Float_Model_ofISize(v_n_boxed_386_);
v_r_388_ = lean_box_uint64(v_res_387_);
return v_r_388_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_toUInt8(uint64_t v_f_389_){
_start:
{
lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_390_ = l_Float_Model_unpack(v_f_389_);
v___x_391_ = l_Float_Model_UnpackedFloat_toUInt8(v___x_390_);
lean_dec(v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toUInt8___boxed(lean_object* v_f_392_){
_start:
{
uint64_t v_f_boxed_393_; uint8_t v_res_394_; lean_object* v_r_395_; 
v_f_boxed_393_ = lean_unbox_uint64(v_f_392_);
lean_dec_ref(v_f_392_);
v_res_394_ = l_Float_Model_toUInt8(v_f_boxed_393_);
v_r_395_ = lean_box(v_res_394_);
return v_r_395_;
}
}
LEAN_EXPORT uint16_t l_Float_Model_toUInt16(uint64_t v_f_396_){
_start:
{
lean_object* v___x_397_; uint16_t v___x_398_; 
v___x_397_ = l_Float_Model_unpack(v_f_396_);
v___x_398_ = l_Float_Model_UnpackedFloat_toUInt16(v___x_397_);
lean_dec(v___x_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toUInt16___boxed(lean_object* v_f_399_){
_start:
{
uint64_t v_f_boxed_400_; uint16_t v_res_401_; lean_object* v_r_402_; 
v_f_boxed_400_ = lean_unbox_uint64(v_f_399_);
lean_dec_ref(v_f_399_);
v_res_401_ = l_Float_Model_toUInt16(v_f_boxed_400_);
v_r_402_ = lean_box(v_res_401_);
return v_r_402_;
}
}
LEAN_EXPORT uint32_t l_Float_Model_toUInt32(uint64_t v_f_403_){
_start:
{
lean_object* v___x_404_; uint32_t v___x_405_; 
v___x_404_ = l_Float_Model_unpack(v_f_403_);
v___x_405_ = l_Float_Model_UnpackedFloat_toUInt32(v___x_404_);
lean_dec(v___x_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toUInt32___boxed(lean_object* v_f_406_){
_start:
{
uint64_t v_f_boxed_407_; uint32_t v_res_408_; lean_object* v_r_409_; 
v_f_boxed_407_ = lean_unbox_uint64(v_f_406_);
lean_dec_ref(v_f_406_);
v_res_408_ = l_Float_Model_toUInt32(v_f_boxed_407_);
v_r_409_ = lean_box_uint32(v_res_408_);
return v_r_409_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_toUInt64(uint64_t v_f_410_){
_start:
{
lean_object* v___x_411_; uint64_t v___x_412_; 
v___x_411_ = l_Float_Model_unpack(v_f_410_);
v___x_412_ = l_Float_Model_UnpackedFloat_toUInt64(v___x_411_);
lean_dec(v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toUInt64___boxed(lean_object* v_f_413_){
_start:
{
uint64_t v_f_boxed_414_; uint64_t v_res_415_; lean_object* v_r_416_; 
v_f_boxed_414_ = lean_unbox_uint64(v_f_413_);
lean_dec_ref(v_f_413_);
v_res_415_ = l_Float_Model_toUInt64(v_f_boxed_414_);
v_r_416_ = lean_box_uint64(v_res_415_);
return v_r_416_;
}
}
LEAN_EXPORT size_t l_Float_Model_toUSize(uint64_t v_f_417_){
_start:
{
lean_object* v___x_418_; size_t v___x_419_; 
v___x_418_ = l_Float_Model_unpack(v_f_417_);
v___x_419_ = l_Float_Model_UnpackedFloat_toUSize(v___x_418_);
lean_dec(v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toUSize___boxed(lean_object* v_f_420_){
_start:
{
uint64_t v_f_boxed_421_; size_t v_res_422_; lean_object* v_r_423_; 
v_f_boxed_421_ = lean_unbox_uint64(v_f_420_);
lean_dec_ref(v_f_420_);
v_res_422_ = l_Float_Model_toUSize(v_f_boxed_421_);
v_r_423_ = lean_box_usize(v_res_422_);
return v_r_423_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_toInt8(uint64_t v_f_424_){
_start:
{
lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_425_ = l_Float_Model_unpack(v_f_424_);
v___x_426_ = l_Float_Model_UnpackedFloat_toInt8(v___x_425_);
lean_dec(v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toInt8___boxed(lean_object* v_f_427_){
_start:
{
uint64_t v_f_boxed_428_; uint8_t v_res_429_; lean_object* v_r_430_; 
v_f_boxed_428_ = lean_unbox_uint64(v_f_427_);
lean_dec_ref(v_f_427_);
v_res_429_ = l_Float_Model_toInt8(v_f_boxed_428_);
v_r_430_ = lean_box(v_res_429_);
return v_r_430_;
}
}
LEAN_EXPORT uint16_t l_Float_Model_toInt16(uint64_t v_f_431_){
_start:
{
lean_object* v___x_432_; uint16_t v___x_433_; 
v___x_432_ = l_Float_Model_unpack(v_f_431_);
v___x_433_ = l_Float_Model_UnpackedFloat_toInt16(v___x_432_);
lean_dec(v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toInt16___boxed(lean_object* v_f_434_){
_start:
{
uint64_t v_f_boxed_435_; uint16_t v_res_436_; lean_object* v_r_437_; 
v_f_boxed_435_ = lean_unbox_uint64(v_f_434_);
lean_dec_ref(v_f_434_);
v_res_436_ = l_Float_Model_toInt16(v_f_boxed_435_);
v_r_437_ = lean_box(v_res_436_);
return v_r_437_;
}
}
LEAN_EXPORT uint32_t l_Float_Model_toInt32(uint64_t v_f_438_){
_start:
{
lean_object* v___x_439_; uint32_t v___x_440_; 
v___x_439_ = l_Float_Model_unpack(v_f_438_);
v___x_440_ = l_Float_Model_UnpackedFloat_toInt32(v___x_439_);
lean_dec(v___x_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toInt32___boxed(lean_object* v_f_441_){
_start:
{
uint64_t v_f_boxed_442_; uint32_t v_res_443_; lean_object* v_r_444_; 
v_f_boxed_442_ = lean_unbox_uint64(v_f_441_);
lean_dec_ref(v_f_441_);
v_res_443_ = l_Float_Model_toInt32(v_f_boxed_442_);
v_r_444_ = lean_box_uint32(v_res_443_);
return v_r_444_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_toInt64(uint64_t v_f_445_){
_start:
{
lean_object* v___x_446_; uint64_t v___x_447_; 
v___x_446_ = l_Float_Model_unpack(v_f_445_);
v___x_447_ = l_Float_Model_UnpackedFloat_toInt64(v___x_446_);
lean_dec(v___x_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toInt64___boxed(lean_object* v_f_448_){
_start:
{
uint64_t v_f_boxed_449_; uint64_t v_res_450_; lean_object* v_r_451_; 
v_f_boxed_449_ = lean_unbox_uint64(v_f_448_);
lean_dec_ref(v_f_448_);
v_res_450_ = l_Float_Model_toInt64(v_f_boxed_449_);
v_r_451_ = lean_box_uint64(v_res_450_);
return v_r_451_;
}
}
LEAN_EXPORT size_t l_Float_Model_toISize(uint64_t v_f_452_){
_start:
{
lean_object* v___x_453_; size_t v___x_454_; 
v___x_453_ = l_Float_Model_unpack(v_f_452_);
v___x_454_ = l_Float_Model_UnpackedFloat_toISize(v___x_453_);
lean_dec(v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toISize___boxed(lean_object* v_f_455_){
_start:
{
uint64_t v_f_boxed_456_; size_t v_res_457_; lean_object* v_r_458_; 
v_f_boxed_456_ = lean_unbox_uint64(v_f_455_);
lean_dec_ref(v_f_455_);
v_res_457_ = l_Float_Model_toISize(v_f_boxed_456_);
v_r_458_ = lean_box_usize(v_res_457_);
return v_r_458_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofScientific(lean_object* v_m_459_, lean_object* v_e_460_){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; uint64_t v___x_463_; 
v___x_461_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_462_ = l_Float_Model_UnpackedFloat_ofScientific(v___x_461_, v_m_459_, v_e_460_);
v___x_463_ = l_Float_Model_pack(v___x_462_);
lean_dec(v___x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofScientific___boxed(lean_object* v_m_464_, lean_object* v_e_465_){
_start:
{
uint64_t v_res_466_; lean_object* v_r_467_; 
v_res_466_ = l_Float_Model_ofScientific(v_m_464_, v_e_465_);
lean_dec(v_e_465_);
v_r_467_ = lean_box_uint64(v_res_466_);
return v_r_467_;
}
}
static uint64_t _init_l_Float_Model_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_468_; uint64_t v___x_469_; 
v___x_468_ = lean_unsigned_to_nat(0u);
v___x_469_ = l_Float_Model_ofNat(v___x_468_);
return v___x_469_;
}
}
static uint64_t _init_l_Float_Model_instInhabited(void){
_start:
{
uint64_t v___x_470_; 
v___x_470_ = lean_uint64_once(&l_Float_Model_instInhabited___closed__0, &l_Float_Model_instInhabited___closed__0_once, _init_l_Float_Model_instInhabited___closed__0);
return v___x_470_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Format_Valid(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Pack_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Operations(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Float(uint8_t builtin) {
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
l_Float_Model_nan = _init_l_Float_Model_nan();
l_Float_Model_inf = _init_l_Float_Model_inf();
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
