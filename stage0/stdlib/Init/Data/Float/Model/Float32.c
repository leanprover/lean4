// Lean compiler output
// Module: Init.Data.Float.Model.Float32
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
lean_object* l_Float_Model_UnpackedFloat_maximum(lean_object*, lean_object*);
uint8_t l_Float_Model_UnpackedFloat_isFinite(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_minimum(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_sqrt(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofInt64(lean_object*, uint64_t);
lean_object* l_Float_Model_UnpackedFloat_minimumNumber(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_abs(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofInt(lean_object*, lean_object*);
uint32_t l_Float_Model_UnpackedFloat_toInt32(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofScientific(lean_object*, lean_object*, lean_object*);
uint8_t l_Float_Model_UnpackedFloat_le(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofNat(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_neg(lean_object*);
uint32_t l_Float_Model_UnpackedFloat_toUInt32(lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofISize(lean_object*, size_t);
lean_object* l_Float_Model_UnpackedFloat_ofInt8(lean_object*, uint8_t);
lean_object* l_Float_Model_UnpackedFloat_maximumNumber(lean_object*, lean_object*);
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
LEAN_EXPORT uint32_t l_Float32_Model_minimum(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_minimum___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Float32_Model_minimumNumber(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_minimumNumber___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Float32_Model_maximum(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_maximum___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Float32_Model_maximumNumber(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Float32_Model_maximumNumber___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Float32_Model_instMin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float32_Model_minimum___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Float32_Model_instMin___closed__0 = (const lean_object*)&l_Float32_Model_instMin___closed__0_value;
LEAN_EXPORT const lean_object* l_Float32_Model_instMin = (const lean_object*)&l_Float32_Model_instMin___closed__0_value;
static const lean_closure_object l_Float32_Model_instMax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float32_Model_maximum___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
uint8_t l_Float32_instDecidableEqModel_decEq(uint32_t v_x_1_, uint32_t v_x_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = lean_uint32_dec_eq(v_x_1_, v_x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Float32_instDecidableEqModel_decEq_0interp(lean_interpreter_value* stack)
{
uint32_t v_x_1_ = stack[0].m_num;
uint32_t v_x_2_ = stack[1].m_num;
uint8_t v_res_4_;
v_res_4_ = l_Float32_instDecidableEqModel_decEq(v_x_1_, v_x_2_);
stack->m_num = v_res_4_;
}
LEAN_EXPORT lean_object* l_Float32_instDecidableEqModel_decEq___boxed(lean_object* v_x_5_, lean_object* v_x_6_){
_start:
{
uint32_t v_x_39__boxed_7_; uint32_t v_x_40__boxed_8_; uint8_t v_res_9_; lean_object* v_r_10_; 
v_x_39__boxed_7_ = lean_unbox_uint32(v_x_5_);
lean_dec(v_x_5_);
v_x_40__boxed_8_ = lean_unbox_uint32(v_x_6_);
lean_dec(v_x_6_);
v_res_9_ = l_Float32_instDecidableEqModel_decEq(v_x_39__boxed_7_, v_x_40__boxed_8_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
uint8_t l_Float32_instDecidableEqModel(uint32_t v_x_11_, uint32_t v_x_12_){
_start:
{
uint8_t v___x_13_; 
v___x_13_ = lean_uint32_dec_eq(v_x_11_, v_x_12_);
return v___x_13_;
}
}
LEAN_EXPORT void l_Float32_instDecidableEqModel_0interp(lean_interpreter_value* stack)
{
uint32_t v_x_11_ = stack[0].m_num;
uint32_t v_x_12_ = stack[1].m_num;
uint8_t v_res_14_;
v_res_14_ = l_Float32_instDecidableEqModel(v_x_11_, v_x_12_);
stack->m_num = v_res_14_;
}
LEAN_EXPORT lean_object* l_Float32_instDecidableEqModel___boxed(lean_object* v_x_15_, lean_object* v_x_16_){
_start:
{
uint32_t v_x_6__boxed_17_; uint32_t v_x_7__boxed_18_; uint8_t v_res_19_; lean_object* v_r_20_; 
v_x_6__boxed_17_ = lean_unbox_uint32(v_x_15_);
lean_dec(v_x_15_);
v_x_7__boxed_18_ = lean_unbox_uint32(v_x_16_);
lean_dec(v_x_16_);
v_res_19_ = l_Float32_instDecidableEqModel(v_x_6__boxed_17_, v_x_7__boxed_18_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
lean_object* l_Float32_Model_unpack(uint32_t v_f_24_){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_25_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_26_ = lean_uint32_to_nat(v_f_24_);
v___x_27_ = l_Float_Model_UnpackedFloat_unpack(v___x_25_, v___x_26_);
lean_dec(v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT void l_Float32_Model_unpack_0interp(lean_interpreter_value* stack)
{
uint32_t v_f_24_ = stack[0].m_num;
lean_object* v_res_28_;
v_res_28_ = l_Float32_Model_unpack(v_f_24_);
stack->m_obj
 = v_res_28_;
}
LEAN_EXPORT lean_object* l_Float32_Model_unpack___boxed(lean_object* v_f_29_){
_start:
{
uint32_t v_f_boxed_30_; lean_object* v_res_31_; 
v_f_boxed_30_ = lean_unbox_uint32(v_f_29_);
lean_dec(v_f_29_);
v_res_31_ = l_Float32_Model_unpack(v_f_boxed_30_);
return v_res_31_;
}
}
uint32_t l_Float32_Model_pack(lean_object* v_f_32_){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; uint32_t v___x_35_; 
v___x_33_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_34_ = l_Float_Model_UnpackedFloat_pack(v___x_33_, v_f_32_);
v___x_35_ = lean_uint32_of_nat_mk(v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT void l_Float32_Model_pack_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_32_ = stack[0].m_obj;
uint32_t v_res_36_;
v_res_36_ = l_Float32_Model_pack(v_f_32_);
stack->m_num = v_res_36_;
}
LEAN_EXPORT lean_object* l_Float32_Model_pack___boxed(lean_object* v_f_37_){
_start:
{
uint32_t v_res_38_; lean_object* v_r_39_; 
v_res_38_ = l_Float32_Model_pack(v_f_37_);
lean_dec(v_f_37_);
v_r_39_ = lean_box_uint32(v_res_38_);
return v_r_39_;
}
}
static uint32_t _init_l_Float32_Model_nan___closed__0(void){
_start:
{
lean_object* v___x_40_; uint32_t v___x_41_; 
v___x_40_ = lean_box(1);
v___x_41_ = l_Float32_Model_pack(v___x_40_);
return v___x_41_;
}
}
static uint32_t _init_l_Float32_Model_nan(void){
_start:
{
uint32_t v___x_42_; 
v___x_42_ = lean_uint32_once(&l_Float32_Model_nan___closed__0, &l_Float32_Model_nan___closed__0_once, _init_l_Float32_Model_nan___closed__0);
return v___x_42_;
}
}
static uint32_t _init_l_Float32_Model_inf___closed__1(void){
_start:
{
lean_object* v___x_45_; uint32_t v___x_46_; 
v___x_45_ = ((lean_object*)(l_Float32_Model_inf___closed__0));
v___x_46_ = l_Float32_Model_pack(v___x_45_);
return v___x_46_;
}
}
static uint32_t _init_l_Float32_Model_inf(void){
_start:
{
uint32_t v___x_47_; 
v___x_47_ = lean_uint32_once(&l_Float32_Model_inf___closed__1, &l_Float32_Model_inf___closed__1_once, _init_l_Float32_Model_inf___closed__1);
return v___x_47_;
}
}
uint32_t l_Float32_Model_add(uint32_t v_a_48_, uint32_t v_b_49_){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; uint32_t v___x_54_; 
v___x_50_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_51_ = l_Float32_Model_unpack(v_a_48_);
v___x_52_ = l_Float32_Model_unpack(v_b_49_);
v___x_53_ = l_Float_Model_UnpackedFloat_add(v___x_50_, v___x_51_, v___x_52_);
v___x_54_ = l_Float32_Model_pack(v___x_53_);
lean_dec(v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT void l_Float32_Model_add_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_48_ = stack[0].m_num;
uint32_t v_b_49_ = stack[1].m_num;
uint32_t v_res_55_;
v_res_55_ = l_Float32_Model_add(v_a_48_, v_b_49_);
stack->m_num = v_res_55_;
}
LEAN_EXPORT lean_object* l_Float32_Model_add___boxed(lean_object* v_a_56_, lean_object* v_b_57_){
_start:
{
uint32_t v_a_boxed_58_; uint32_t v_b_boxed_59_; uint32_t v_res_60_; lean_object* v_r_61_; 
v_a_boxed_58_ = lean_unbox_uint32(v_a_56_);
lean_dec(v_a_56_);
v_b_boxed_59_ = lean_unbox_uint32(v_b_57_);
lean_dec(v_b_57_);
v_res_60_ = l_Float32_Model_add(v_a_boxed_58_, v_b_boxed_59_);
v_r_61_ = lean_box_uint32(v_res_60_);
return v_r_61_;
}
}
uint32_t l_Float32_Model_sub(uint32_t v_a_62_, uint32_t v_b_63_){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; uint32_t v___x_68_; 
v___x_64_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_65_ = l_Float32_Model_unpack(v_a_62_);
v___x_66_ = l_Float32_Model_unpack(v_b_63_);
v___x_67_ = l_Float_Model_UnpackedFloat_sub(v___x_64_, v___x_65_, v___x_66_);
v___x_68_ = l_Float32_Model_pack(v___x_67_);
lean_dec(v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT void l_Float32_Model_sub_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_62_ = stack[0].m_num;
uint32_t v_b_63_ = stack[1].m_num;
uint32_t v_res_69_;
v_res_69_ = l_Float32_Model_sub(v_a_62_, v_b_63_);
stack->m_num = v_res_69_;
}
LEAN_EXPORT lean_object* l_Float32_Model_sub___boxed(lean_object* v_a_70_, lean_object* v_b_71_){
_start:
{
uint32_t v_a_boxed_72_; uint32_t v_b_boxed_73_; uint32_t v_res_74_; lean_object* v_r_75_; 
v_a_boxed_72_ = lean_unbox_uint32(v_a_70_);
lean_dec(v_a_70_);
v_b_boxed_73_ = lean_unbox_uint32(v_b_71_);
lean_dec(v_b_71_);
v_res_74_ = l_Float32_Model_sub(v_a_boxed_72_, v_b_boxed_73_);
v_r_75_ = lean_box_uint32(v_res_74_);
return v_r_75_;
}
}
uint32_t l_Float32_Model_mul(uint32_t v_a_76_, uint32_t v_b_77_){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; uint32_t v___x_82_; 
v___x_78_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_79_ = l_Float32_Model_unpack(v_a_76_);
v___x_80_ = l_Float32_Model_unpack(v_b_77_);
v___x_81_ = l_Float_Model_UnpackedFloat_mul(v___x_78_, v___x_79_, v___x_80_);
v___x_82_ = l_Float32_Model_pack(v___x_81_);
lean_dec(v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT void l_Float32_Model_mul_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_76_ = stack[0].m_num;
uint32_t v_b_77_ = stack[1].m_num;
uint32_t v_res_83_;
v_res_83_ = l_Float32_Model_mul(v_a_76_, v_b_77_);
stack->m_num = v_res_83_;
}
LEAN_EXPORT lean_object* l_Float32_Model_mul___boxed(lean_object* v_a_84_, lean_object* v_b_85_){
_start:
{
uint32_t v_a_boxed_86_; uint32_t v_b_boxed_87_; uint32_t v_res_88_; lean_object* v_r_89_; 
v_a_boxed_86_ = lean_unbox_uint32(v_a_84_);
lean_dec(v_a_84_);
v_b_boxed_87_ = lean_unbox_uint32(v_b_85_);
lean_dec(v_b_85_);
v_res_88_ = l_Float32_Model_mul(v_a_boxed_86_, v_b_boxed_87_);
v_r_89_ = lean_box_uint32(v_res_88_);
return v_r_89_;
}
}
uint32_t l_Float32_Model_div(uint32_t v_a_90_, uint32_t v_b_91_){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; uint32_t v___x_96_; 
v___x_92_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_93_ = l_Float32_Model_unpack(v_a_90_);
v___x_94_ = l_Float32_Model_unpack(v_b_91_);
v___x_95_ = l_Float_Model_UnpackedFloat_div(v___x_92_, v___x_93_, v___x_94_);
v___x_96_ = l_Float32_Model_pack(v___x_95_);
lean_dec(v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT void l_Float32_Model_div_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_90_ = stack[0].m_num;
uint32_t v_b_91_ = stack[1].m_num;
uint32_t v_res_97_;
v_res_97_ = l_Float32_Model_div(v_a_90_, v_b_91_);
stack->m_num = v_res_97_;
}
LEAN_EXPORT lean_object* l_Float32_Model_div___boxed(lean_object* v_a_98_, lean_object* v_b_99_){
_start:
{
uint32_t v_a_boxed_100_; uint32_t v_b_boxed_101_; uint32_t v_res_102_; lean_object* v_r_103_; 
v_a_boxed_100_ = lean_unbox_uint32(v_a_98_);
lean_dec(v_a_98_);
v_b_boxed_101_ = lean_unbox_uint32(v_b_99_);
lean_dec(v_b_99_);
v_res_102_ = l_Float32_Model_div(v_a_boxed_100_, v_b_boxed_101_);
v_r_103_ = lean_box_uint32(v_res_102_);
return v_r_103_;
}
}
uint32_t l_Float32_Model_sqrt(uint32_t v_a_112_){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; uint32_t v___x_116_; 
v___x_113_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_114_ = l_Float32_Model_unpack(v_a_112_);
v___x_115_ = l_Float_Model_UnpackedFloat_sqrt(v___x_113_, v___x_114_);
lean_dec(v___x_114_);
v___x_116_ = l_Float32_Model_pack(v___x_115_);
lean_dec(v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT void l_Float32_Model_sqrt_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_112_ = stack[0].m_num;
uint32_t v_res_117_;
v_res_117_ = l_Float32_Model_sqrt(v_a_112_);
stack->m_num = v_res_117_;
}
LEAN_EXPORT lean_object* l_Float32_Model_sqrt___boxed(lean_object* v_a_118_){
_start:
{
uint32_t v_a_boxed_119_; uint32_t v_res_120_; lean_object* v_r_121_; 
v_a_boxed_119_ = lean_unbox_uint32(v_a_118_);
lean_dec(v_a_118_);
v_res_120_ = l_Float32_Model_sqrt(v_a_boxed_119_);
v_r_121_ = lean_box_uint32(v_res_120_);
return v_r_121_;
}
}
uint32_t l_Float32_Model_fma(uint32_t v_a_122_, uint32_t v_b_123_, uint32_t v_c_124_){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; uint32_t v___x_130_; 
v___x_125_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_126_ = l_Float32_Model_unpack(v_a_122_);
v___x_127_ = l_Float32_Model_unpack(v_b_123_);
v___x_128_ = l_Float32_Model_unpack(v_c_124_);
v___x_129_ = l_Float_Model_UnpackedFloat_fma(v___x_125_, v___x_126_, v___x_127_, v___x_128_);
v___x_130_ = l_Float32_Model_pack(v___x_129_);
lean_dec(v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT void l_Float32_Model_fma_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_122_ = stack[0].m_num;
uint32_t v_b_123_ = stack[1].m_num;
uint32_t v_c_124_ = stack[2].m_num;
uint32_t v_res_131_;
v_res_131_ = l_Float32_Model_fma(v_a_122_, v_b_123_, v_c_124_);
stack->m_num = v_res_131_;
}
LEAN_EXPORT lean_object* l_Float32_Model_fma___boxed(lean_object* v_a_132_, lean_object* v_b_133_, lean_object* v_c_134_){
_start:
{
uint32_t v_a_boxed_135_; uint32_t v_b_boxed_136_; uint32_t v_c_boxed_137_; uint32_t v_res_138_; lean_object* v_r_139_; 
v_a_boxed_135_ = lean_unbox_uint32(v_a_132_);
lean_dec(v_a_132_);
v_b_boxed_136_ = lean_unbox_uint32(v_b_133_);
lean_dec(v_b_133_);
v_c_boxed_137_ = lean_unbox_uint32(v_c_134_);
lean_dec(v_c_134_);
v_res_138_ = l_Float32_Model_fma(v_a_boxed_135_, v_b_boxed_136_, v_c_boxed_137_);
v_r_139_ = lean_box_uint32(v_res_138_);
return v_r_139_;
}
}
uint32_t l_Float32_Model_neg(uint32_t v_a_140_){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; uint32_t v___x_143_; 
v___x_141_ = l_Float32_Model_unpack(v_a_140_);
v___x_142_ = l_Float_Model_UnpackedFloat_neg(v___x_141_);
v___x_143_ = l_Float32_Model_pack(v___x_142_);
lean_dec(v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT void l_Float32_Model_neg_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_140_ = stack[0].m_num;
uint32_t v_res_144_;
v_res_144_ = l_Float32_Model_neg(v_a_140_);
stack->m_num = v_res_144_;
}
LEAN_EXPORT lean_object* l_Float32_Model_neg___boxed(lean_object* v_a_145_){
_start:
{
uint32_t v_a_boxed_146_; uint32_t v_res_147_; lean_object* v_r_148_; 
v_a_boxed_146_ = lean_unbox_uint32(v_a_145_);
lean_dec(v_a_145_);
v_res_147_ = l_Float32_Model_neg(v_a_boxed_146_);
v_r_148_ = lean_box_uint32(v_res_147_);
return v_r_148_;
}
}
uint32_t l_Float32_Model_abs(uint32_t v_a_151_){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; uint32_t v___x_154_; 
v___x_152_ = l_Float32_Model_unpack(v_a_151_);
v___x_153_ = l_Float_Model_UnpackedFloat_abs(v___x_152_);
v___x_154_ = l_Float32_Model_pack(v___x_153_);
lean_dec(v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT void l_Float32_Model_abs_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_151_ = stack[0].m_num;
uint32_t v_res_155_;
v_res_155_ = l_Float32_Model_abs(v_a_151_);
stack->m_num = v_res_155_;
}
LEAN_EXPORT lean_object* l_Float32_Model_abs___boxed(lean_object* v_a_156_){
_start:
{
uint32_t v_a_boxed_157_; uint32_t v_res_158_; lean_object* v_r_159_; 
v_a_boxed_157_ = lean_unbox_uint32(v_a_156_);
lean_dec(v_a_156_);
v_res_158_ = l_Float32_Model_abs(v_a_boxed_157_);
v_r_159_ = lean_box_uint32(v_res_158_);
return v_r_159_;
}
}
lean_object* l_Float32_Model_compare(uint32_t v_a_160_, uint32_t v_b_161_){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_162_ = l_Float32_Model_unpack(v_a_160_);
v___x_163_ = l_Float32_Model_unpack(v_b_161_);
v___x_164_ = l_Float_Model_UnpackedFloat_compare(v___x_162_, v___x_163_);
lean_dec(v___x_163_);
lean_dec(v___x_162_);
return v___x_164_;
}
}
LEAN_EXPORT void l_Float32_Model_compare_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_160_ = stack[0].m_num;
uint32_t v_b_161_ = stack[1].m_num;
lean_object* v_res_165_;
v_res_165_ = l_Float32_Model_compare(v_a_160_, v_b_161_);
stack->m_obj
 = v_res_165_;
}
LEAN_EXPORT lean_object* l_Float32_Model_compare___boxed(lean_object* v_a_166_, lean_object* v_b_167_){
_start:
{
uint32_t v_a_boxed_168_; uint32_t v_b_boxed_169_; lean_object* v_res_170_; 
v_a_boxed_168_ = lean_unbox_uint32(v_a_166_);
lean_dec(v_a_166_);
v_b_boxed_169_ = lean_unbox_uint32(v_b_167_);
lean_dec(v_b_167_);
v_res_170_ = l_Float32_Model_compare(v_a_boxed_168_, v_b_boxed_169_);
return v_res_170_;
}
}
uint8_t l_Float32_Model_le(uint32_t v_a_171_, uint32_t v_b_172_){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_173_ = l_Float32_Model_unpack(v_a_171_);
v___x_174_ = l_Float32_Model_unpack(v_b_172_);
v___x_175_ = l_Float_Model_UnpackedFloat_le(v___x_173_, v___x_174_);
lean_dec(v___x_174_);
lean_dec(v___x_173_);
return v___x_175_;
}
}
LEAN_EXPORT void l_Float32_Model_le_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_171_ = stack[0].m_num;
uint32_t v_b_172_ = stack[1].m_num;
uint8_t v_res_176_;
v_res_176_ = l_Float32_Model_le(v_a_171_, v_b_172_);
stack->m_num = v_res_176_;
}
LEAN_EXPORT lean_object* l_Float32_Model_le___boxed(lean_object* v_a_177_, lean_object* v_b_178_){
_start:
{
uint32_t v_a_boxed_179_; uint32_t v_b_boxed_180_; uint8_t v_res_181_; lean_object* v_r_182_; 
v_a_boxed_179_ = lean_unbox_uint32(v_a_177_);
lean_dec(v_a_177_);
v_b_boxed_180_ = lean_unbox_uint32(v_b_178_);
lean_dec(v_b_178_);
v_res_181_ = l_Float32_Model_le(v_a_boxed_179_, v_b_boxed_180_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
uint8_t l_Float32_Model_lt(uint32_t v_a_183_, uint32_t v_b_184_){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_185_ = l_Float32_Model_unpack(v_a_183_);
v___x_186_ = l_Float32_Model_unpack(v_b_184_);
v___x_187_ = l_Float_Model_UnpackedFloat_lt(v___x_185_, v___x_186_);
lean_dec(v___x_186_);
lean_dec(v___x_185_);
return v___x_187_;
}
}
LEAN_EXPORT void l_Float32_Model_lt_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_183_ = stack[0].m_num;
uint32_t v_b_184_ = stack[1].m_num;
uint8_t v_res_188_;
v_res_188_ = l_Float32_Model_lt(v_a_183_, v_b_184_);
stack->m_num = v_res_188_;
}
LEAN_EXPORT lean_object* l_Float32_Model_lt___boxed(lean_object* v_a_189_, lean_object* v_b_190_){
_start:
{
uint32_t v_a_boxed_191_; uint32_t v_b_boxed_192_; uint8_t v_res_193_; lean_object* v_r_194_; 
v_a_boxed_191_ = lean_unbox_uint32(v_a_189_);
lean_dec(v_a_189_);
v_b_boxed_192_ = lean_unbox_uint32(v_b_190_);
lean_dec(v_b_190_);
v_res_193_ = l_Float32_Model_lt(v_a_boxed_191_, v_b_boxed_192_);
v_r_194_ = lean_box(v_res_193_);
return v_r_194_;
}
}
uint8_t l_Float32_Model_beq(uint32_t v_a_195_, uint32_t v_b_196_){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_197_ = l_Float32_Model_unpack(v_a_195_);
v___x_198_ = l_Float32_Model_unpack(v_b_196_);
v___x_199_ = l_Float_Model_UnpackedFloat_beq(v___x_197_, v___x_198_);
lean_dec(v___x_198_);
lean_dec(v___x_197_);
return v___x_199_;
}
}
LEAN_EXPORT void l_Float32_Model_beq_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_195_ = stack[0].m_num;
uint32_t v_b_196_ = stack[1].m_num;
uint8_t v_res_200_;
v_res_200_ = l_Float32_Model_beq(v_a_195_, v_b_196_);
stack->m_num = v_res_200_;
}
LEAN_EXPORT lean_object* l_Float32_Model_beq___boxed(lean_object* v_a_201_, lean_object* v_b_202_){
_start:
{
uint32_t v_a_boxed_203_; uint32_t v_b_boxed_204_; uint8_t v_res_205_; lean_object* v_r_206_; 
v_a_boxed_203_ = lean_unbox_uint32(v_a_201_);
lean_dec(v_a_201_);
v_b_boxed_204_ = lean_unbox_uint32(v_b_202_);
lean_dec(v_b_202_);
v_res_205_ = l_Float32_Model_beq(v_a_boxed_203_, v_b_boxed_204_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
static lean_object* _init_l_Float32_Model_instLE(void){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = lean_box(0);
return v___x_207_;
}
}
uint8_t l_Float32_Model_instDecidableLE(uint32_t v_a_208_, uint32_t v_b_209_){
_start:
{
uint8_t v___x_210_; 
v___x_210_ = l_Float32_Model_le(v_a_208_, v_b_209_);
return v___x_210_;
}
}
LEAN_EXPORT void l_Float32_Model_instDecidableLE_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_208_ = stack[0].m_num;
uint32_t v_b_209_ = stack[1].m_num;
uint8_t v_res_211_;
v_res_211_ = l_Float32_Model_instDecidableLE(v_a_208_, v_b_209_);
stack->m_num = v_res_211_;
}
LEAN_EXPORT lean_object* l_Float32_Model_instDecidableLE___boxed(lean_object* v_a_212_, lean_object* v_b_213_){
_start:
{
uint32_t v_a_boxed_214_; uint32_t v_b_boxed_215_; uint8_t v_res_216_; lean_object* v_r_217_; 
v_a_boxed_214_ = lean_unbox_uint32(v_a_212_);
lean_dec(v_a_212_);
v_b_boxed_215_ = lean_unbox_uint32(v_b_213_);
lean_dec(v_b_213_);
v_res_216_ = l_Float32_Model_instDecidableLE(v_a_boxed_214_, v_b_boxed_215_);
v_r_217_ = lean_box(v_res_216_);
return v_r_217_;
}
}
static lean_object* _init_l_Float32_Model_instLT(void){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = lean_box(0);
return v___x_218_;
}
}
uint8_t l_Float32_Model_instDecidableLT(uint32_t v_a_219_, uint32_t v_b_220_){
_start:
{
uint8_t v___x_221_; 
v___x_221_ = l_Float32_Model_lt(v_a_219_, v_b_220_);
return v___x_221_;
}
}
LEAN_EXPORT void l_Float32_Model_instDecidableLT_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_219_ = stack[0].m_num;
uint32_t v_b_220_ = stack[1].m_num;
uint8_t v_res_222_;
v_res_222_ = l_Float32_Model_instDecidableLT(v_a_219_, v_b_220_);
stack->m_num = v_res_222_;
}
LEAN_EXPORT lean_object* l_Float32_Model_instDecidableLT___boxed(lean_object* v_a_223_, lean_object* v_b_224_){
_start:
{
uint32_t v_a_boxed_225_; uint32_t v_b_boxed_226_; uint8_t v_res_227_; lean_object* v_r_228_; 
v_a_boxed_225_ = lean_unbox_uint32(v_a_223_);
lean_dec(v_a_223_);
v_b_boxed_226_ = lean_unbox_uint32(v_b_224_);
lean_dec(v_b_224_);
v_res_227_ = l_Float32_Model_instDecidableLT(v_a_boxed_225_, v_b_boxed_226_);
v_r_228_ = lean_box(v_res_227_);
return v_r_228_;
}
}
uint32_t l_Float32_Model_minimum(uint32_t v_a_231_, uint32_t v_b_232_){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; uint32_t v___x_236_; 
v___x_233_ = l_Float32_Model_unpack(v_a_231_);
v___x_234_ = l_Float32_Model_unpack(v_b_232_);
v___x_235_ = l_Float_Model_UnpackedFloat_minimum(v___x_233_, v___x_234_);
lean_dec(v___x_234_);
lean_dec(v___x_233_);
v___x_236_ = l_Float32_Model_pack(v___x_235_);
lean_dec(v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT void l_Float32_Model_minimum_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_231_ = stack[0].m_num;
uint32_t v_b_232_ = stack[1].m_num;
uint32_t v_res_237_;
v_res_237_ = l_Float32_Model_minimum(v_a_231_, v_b_232_);
stack->m_num = v_res_237_;
}
LEAN_EXPORT lean_object* l_Float32_Model_minimum___boxed(lean_object* v_a_238_, lean_object* v_b_239_){
_start:
{
uint32_t v_a_boxed_240_; uint32_t v_b_boxed_241_; uint32_t v_res_242_; lean_object* v_r_243_; 
v_a_boxed_240_ = lean_unbox_uint32(v_a_238_);
lean_dec(v_a_238_);
v_b_boxed_241_ = lean_unbox_uint32(v_b_239_);
lean_dec(v_b_239_);
v_res_242_ = l_Float32_Model_minimum(v_a_boxed_240_, v_b_boxed_241_);
v_r_243_ = lean_box_uint32(v_res_242_);
return v_r_243_;
}
}
uint32_t l_Float32_Model_minimumNumber(uint32_t v_a_244_, uint32_t v_b_245_){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; uint32_t v___x_249_; 
v___x_246_ = l_Float32_Model_unpack(v_a_244_);
v___x_247_ = l_Float32_Model_unpack(v_b_245_);
v___x_248_ = l_Float_Model_UnpackedFloat_minimumNumber(v___x_246_, v___x_247_);
lean_dec(v___x_247_);
lean_dec(v___x_246_);
v___x_249_ = l_Float32_Model_pack(v___x_248_);
lean_dec(v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT void l_Float32_Model_minimumNumber_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_244_ = stack[0].m_num;
uint32_t v_b_245_ = stack[1].m_num;
uint32_t v_res_250_;
v_res_250_ = l_Float32_Model_minimumNumber(v_a_244_, v_b_245_);
stack->m_num = v_res_250_;
}
LEAN_EXPORT lean_object* l_Float32_Model_minimumNumber___boxed(lean_object* v_a_251_, lean_object* v_b_252_){
_start:
{
uint32_t v_a_boxed_253_; uint32_t v_b_boxed_254_; uint32_t v_res_255_; lean_object* v_r_256_; 
v_a_boxed_253_ = lean_unbox_uint32(v_a_251_);
lean_dec(v_a_251_);
v_b_boxed_254_ = lean_unbox_uint32(v_b_252_);
lean_dec(v_b_252_);
v_res_255_ = l_Float32_Model_minimumNumber(v_a_boxed_253_, v_b_boxed_254_);
v_r_256_ = lean_box_uint32(v_res_255_);
return v_r_256_;
}
}
uint32_t l_Float32_Model_maximum(uint32_t v_a_257_, uint32_t v_b_258_){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; uint32_t v___x_262_; 
v___x_259_ = l_Float32_Model_unpack(v_a_257_);
v___x_260_ = l_Float32_Model_unpack(v_b_258_);
v___x_261_ = l_Float_Model_UnpackedFloat_maximum(v___x_259_, v___x_260_);
lean_dec(v___x_260_);
lean_dec(v___x_259_);
v___x_262_ = l_Float32_Model_pack(v___x_261_);
lean_dec(v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT void l_Float32_Model_maximum_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_257_ = stack[0].m_num;
uint32_t v_b_258_ = stack[1].m_num;
uint32_t v_res_263_;
v_res_263_ = l_Float32_Model_maximum(v_a_257_, v_b_258_);
stack->m_num = v_res_263_;
}
LEAN_EXPORT lean_object* l_Float32_Model_maximum___boxed(lean_object* v_a_264_, lean_object* v_b_265_){
_start:
{
uint32_t v_a_boxed_266_; uint32_t v_b_boxed_267_; uint32_t v_res_268_; lean_object* v_r_269_; 
v_a_boxed_266_ = lean_unbox_uint32(v_a_264_);
lean_dec(v_a_264_);
v_b_boxed_267_ = lean_unbox_uint32(v_b_265_);
lean_dec(v_b_265_);
v_res_268_ = l_Float32_Model_maximum(v_a_boxed_266_, v_b_boxed_267_);
v_r_269_ = lean_box_uint32(v_res_268_);
return v_r_269_;
}
}
uint32_t l_Float32_Model_maximumNumber(uint32_t v_a_270_, uint32_t v_b_271_){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; uint32_t v___x_275_; 
v___x_272_ = l_Float32_Model_unpack(v_a_270_);
v___x_273_ = l_Float32_Model_unpack(v_b_271_);
v___x_274_ = l_Float_Model_UnpackedFloat_maximumNumber(v___x_272_, v___x_273_);
lean_dec(v___x_273_);
lean_dec(v___x_272_);
v___x_275_ = l_Float32_Model_pack(v___x_274_);
lean_dec(v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT void l_Float32_Model_maximumNumber_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_270_ = stack[0].m_num;
uint32_t v_b_271_ = stack[1].m_num;
uint32_t v_res_276_;
v_res_276_ = l_Float32_Model_maximumNumber(v_a_270_, v_b_271_);
stack->m_num = v_res_276_;
}
LEAN_EXPORT lean_object* l_Float32_Model_maximumNumber___boxed(lean_object* v_a_277_, lean_object* v_b_278_){
_start:
{
uint32_t v_a_boxed_279_; uint32_t v_b_boxed_280_; uint32_t v_res_281_; lean_object* v_r_282_; 
v_a_boxed_279_ = lean_unbox_uint32(v_a_277_);
lean_dec(v_a_277_);
v_b_boxed_280_ = lean_unbox_uint32(v_b_278_);
lean_dec(v_b_278_);
v_res_281_ = l_Float32_Model_maximumNumber(v_a_boxed_279_, v_b_boxed_280_);
v_r_282_ = lean_box_uint32(v_res_281_);
return v_r_282_;
}
}
uint8_t l_Float32_Model_isFinite(uint32_t v_a_287_){
_start:
{
lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_288_ = l_Float32_Model_unpack(v_a_287_);
v___x_289_ = l_Float_Model_UnpackedFloat_isFinite(v___x_288_);
lean_dec(v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT void l_Float32_Model_isFinite_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_287_ = stack[0].m_num;
uint8_t v_res_290_;
v_res_290_ = l_Float32_Model_isFinite(v_a_287_);
stack->m_num = v_res_290_;
}
LEAN_EXPORT lean_object* l_Float32_Model_isFinite___boxed(lean_object* v_a_291_){
_start:
{
uint32_t v_a_boxed_292_; uint8_t v_res_293_; lean_object* v_r_294_; 
v_a_boxed_292_ = lean_unbox_uint32(v_a_291_);
lean_dec(v_a_291_);
v_res_293_ = l_Float32_Model_isFinite(v_a_boxed_292_);
v_r_294_ = lean_box(v_res_293_);
return v_r_294_;
}
}
uint8_t l_Float32_Model_isInf(uint32_t v_a_295_){
_start:
{
lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_296_ = l_Float32_Model_unpack(v_a_295_);
v___x_297_ = l_Float_Model_UnpackedFloat_isInf(v___x_296_);
lean_dec(v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT void l_Float32_Model_isInf_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_295_ = stack[0].m_num;
uint8_t v_res_298_;
v_res_298_ = l_Float32_Model_isInf(v_a_295_);
stack->m_num = v_res_298_;
}
LEAN_EXPORT lean_object* l_Float32_Model_isInf___boxed(lean_object* v_a_299_){
_start:
{
uint32_t v_a_boxed_300_; uint8_t v_res_301_; lean_object* v_r_302_; 
v_a_boxed_300_ = lean_unbox_uint32(v_a_299_);
lean_dec(v_a_299_);
v_res_301_ = l_Float32_Model_isInf(v_a_boxed_300_);
v_r_302_ = lean_box(v_res_301_);
return v_r_302_;
}
}
uint8_t l_Float32_Model_isNaN(uint32_t v_a_303_){
_start:
{
lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_304_ = l_Float32_Model_unpack(v_a_303_);
v___x_305_ = l_Float_Model_UnpackedFloat_isNaN(v___x_304_);
lean_dec(v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT void l_Float32_Model_isNaN_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_303_ = stack[0].m_num;
uint8_t v_res_306_;
v_res_306_ = l_Float32_Model_isNaN(v_a_303_);
stack->m_num = v_res_306_;
}
LEAN_EXPORT lean_object* l_Float32_Model_isNaN___boxed(lean_object* v_a_307_){
_start:
{
uint32_t v_a_boxed_308_; uint8_t v_res_309_; lean_object* v_r_310_; 
v_a_boxed_308_ = lean_unbox_uint32(v_a_307_);
lean_dec(v_a_307_);
v_res_309_ = l_Float32_Model_isNaN(v_a_boxed_308_);
v_r_310_ = lean_box(v_res_309_);
return v_r_310_;
}
}
uint32_t l_Float32_Model_ofBits(uint32_t v_a_311_){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint32_t v___x_315_; 
v___x_312_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_313_ = lean_uint32_to_nat(v_a_311_);
v___x_314_ = l_Float_Model_UnpackedFloat_unpack(v___x_312_, v___x_313_);
lean_dec(v___x_313_);
v___x_315_ = l_Float32_Model_pack(v___x_314_);
lean_dec(v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT void l_Float32_Model_ofBits_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_311_ = stack[0].m_num;
uint32_t v_res_316_;
v_res_316_ = l_Float32_Model_ofBits(v_a_311_);
stack->m_num = v_res_316_;
}
LEAN_EXPORT lean_object* l_Float32_Model_ofBits___boxed(lean_object* v_a_317_){
_start:
{
uint32_t v_a_boxed_318_; uint32_t v_res_319_; lean_object* v_r_320_; 
v_a_boxed_318_ = lean_unbox_uint32(v_a_317_);
lean_dec(v_a_317_);
v_res_319_ = l_Float32_Model_ofBits(v_a_boxed_318_);
v_r_320_ = lean_box_uint32(v_res_319_);
return v_r_320_;
}
}
uint32_t l_Float32_Model_ofInt(lean_object* v_n_321_){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; uint32_t v___x_324_; 
v___x_322_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_323_ = l_Float_Model_UnpackedFloat_ofInt(v___x_322_, v_n_321_);
v___x_324_ = l_Float32_Model_pack(v___x_323_);
lean_dec(v___x_323_);
return v___x_324_;
}
}
LEAN_EXPORT void l_Float32_Model_ofInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_321_ = stack[0].m_obj;
uint32_t v_res_325_;
v_res_325_ = l_Float32_Model_ofInt(v_n_321_);
stack->m_num = v_res_325_;
}
LEAN_EXPORT lean_object* l_Float32_Model_ofInt___boxed(lean_object* v_n_326_){
_start:
{
uint32_t v_res_327_; lean_object* v_r_328_; 
v_res_327_ = l_Float32_Model_ofInt(v_n_326_);
lean_dec(v_n_326_);
v_r_328_ = lean_box_uint32(v_res_327_);
return v_r_328_;
}
}
uint32_t l_Float32_Model_ofNat(lean_object* v_n_329_){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; uint32_t v___x_332_; 
v___x_330_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_331_ = l_Float_Model_UnpackedFloat_ofNat(v___x_330_, v_n_329_);
v___x_332_ = l_Float32_Model_pack(v___x_331_);
lean_dec(v___x_331_);
return v___x_332_;
}
}
LEAN_EXPORT void l_Float32_Model_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_329_ = stack[0].m_obj;
uint32_t v_res_333_;
v_res_333_ = l_Float32_Model_ofNat(v_n_329_);
stack->m_num = v_res_333_;
}
LEAN_EXPORT lean_object* l_Float32_Model_ofNat___boxed(lean_object* v_n_334_){
_start:
{
uint32_t v_res_335_; lean_object* v_r_336_; 
v_res_335_ = l_Float32_Model_ofNat(v_n_334_);
v_r_336_ = lean_box_uint32(v_res_335_);
return v_r_336_;
}
}
uint32_t l_Float32_Model_ofUInt8(uint8_t v_n_337_){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; uint32_t v___x_340_; 
v___x_338_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_339_ = l_Float_Model_UnpackedFloat_ofUInt8(v___x_338_, v_n_337_);
v___x_340_ = l_Float32_Model_pack(v___x_339_);
lean_dec(v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT void l_Float32_Model_ofUInt8_0interp(lean_interpreter_value* stack)
{
uint8_t v_n_337_ = stack[0].m_num;
uint32_t v_res_341_;
v_res_341_ = l_Float32_Model_ofUInt8(v_n_337_);
stack->m_num = v_res_341_;
}
LEAN_EXPORT lean_object* l_Float32_Model_ofUInt8___boxed(lean_object* v_n_342_){
_start:
{
uint8_t v_n_boxed_343_; uint32_t v_res_344_; lean_object* v_r_345_; 
v_n_boxed_343_ = lean_unbox(v_n_342_);
v_res_344_ = l_Float32_Model_ofUInt8(v_n_boxed_343_);
v_r_345_ = lean_box_uint32(v_res_344_);
return v_r_345_;
}
}
uint32_t l_Float32_Model_ofUInt16(uint16_t v_n_346_){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; uint32_t v___x_349_; 
v___x_347_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_348_ = l_Float_Model_UnpackedFloat_ofUInt16(v___x_347_, v_n_346_);
v___x_349_ = l_Float32_Model_pack(v___x_348_);
lean_dec(v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT void l_Float32_Model_ofUInt16_0interp(lean_interpreter_value* stack)
{
uint16_t v_n_346_ = stack[0].m_num;
uint32_t v_res_350_;
v_res_350_ = l_Float32_Model_ofUInt16(v_n_346_);
stack->m_num = v_res_350_;
}
LEAN_EXPORT lean_object* l_Float32_Model_ofUInt16___boxed(lean_object* v_n_351_){
_start:
{
uint16_t v_n_boxed_352_; uint32_t v_res_353_; lean_object* v_r_354_; 
v_n_boxed_352_ = lean_unbox(v_n_351_);
v_res_353_ = l_Float32_Model_ofUInt16(v_n_boxed_352_);
v_r_354_ = lean_box_uint32(v_res_353_);
return v_r_354_;
}
}
uint32_t l_Float32_Model_ofUInt32(uint32_t v_n_355_){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; uint32_t v___x_358_; 
v___x_356_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_357_ = l_Float_Model_UnpackedFloat_ofUInt32(v___x_356_, v_n_355_);
v___x_358_ = l_Float32_Model_pack(v___x_357_);
lean_dec(v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT void l_Float32_Model_ofUInt32_0interp(lean_interpreter_value* stack)
{
uint32_t v_n_355_ = stack[0].m_num;
uint32_t v_res_359_;
v_res_359_ = l_Float32_Model_ofUInt32(v_n_355_);
stack->m_num = v_res_359_;
}
LEAN_EXPORT lean_object* l_Float32_Model_ofUInt32___boxed(lean_object* v_n_360_){
_start:
{
uint32_t v_n_boxed_361_; uint32_t v_res_362_; lean_object* v_r_363_; 
v_n_boxed_361_ = lean_unbox_uint32(v_n_360_);
lean_dec(v_n_360_);
v_res_362_ = l_Float32_Model_ofUInt32(v_n_boxed_361_);
v_r_363_ = lean_box_uint32(v_res_362_);
return v_r_363_;
}
}
uint32_t l_Float32_Model_ofUInt64(uint64_t v_n_364_){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; uint32_t v___x_367_; 
v___x_365_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_366_ = l_Float_Model_UnpackedFloat_ofUInt64(v___x_365_, v_n_364_);
v___x_367_ = l_Float32_Model_pack(v___x_366_);
lean_dec(v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT void l_Float32_Model_ofUInt64_0interp(lean_interpreter_value* stack)
{
uint64_t v_n_364_ = stack[0].m_num;
uint32_t v_res_368_;
v_res_368_ = l_Float32_Model_ofUInt64(v_n_364_);
stack->m_num = v_res_368_;
}
LEAN_EXPORT lean_object* l_Float32_Model_ofUInt64___boxed(lean_object* v_n_369_){
_start:
{
uint64_t v_n_boxed_370_; uint32_t v_res_371_; lean_object* v_r_372_; 
v_n_boxed_370_ = lean_unbox_uint64(v_n_369_);
lean_dec_ref(v_n_369_);
v_res_371_ = l_Float32_Model_ofUInt64(v_n_boxed_370_);
v_r_372_ = lean_box_uint32(v_res_371_);
return v_r_372_;
}
}
uint32_t l_Float32_Model_ofUSize(size_t v_n_373_){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; uint32_t v___x_376_; 
v___x_374_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_375_ = l_Float_Model_UnpackedFloat_ofUSize(v___x_374_, v_n_373_);
v___x_376_ = l_Float32_Model_pack(v___x_375_);
lean_dec(v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT void l_Float32_Model_ofUSize_0interp(lean_interpreter_value* stack)
{
size_t v_n_373_ = stack[0].m_num;
uint32_t v_res_377_;
v_res_377_ = l_Float32_Model_ofUSize(v_n_373_);
stack->m_num = v_res_377_;
}
LEAN_EXPORT lean_object* l_Float32_Model_ofUSize___boxed(lean_object* v_n_378_){
_start:
{
size_t v_n_boxed_379_; uint32_t v_res_380_; lean_object* v_r_381_; 
v_n_boxed_379_ = lean_unbox_usize(v_n_378_);
lean_dec(v_n_378_);
v_res_380_ = l_Float32_Model_ofUSize(v_n_boxed_379_);
v_r_381_ = lean_box_uint32(v_res_380_);
return v_r_381_;
}
}
uint32_t l_Float32_Model_ofInt8(uint8_t v_n_382_){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; uint32_t v___x_385_; 
v___x_383_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_384_ = l_Float_Model_UnpackedFloat_ofInt8(v___x_383_, v_n_382_);
v___x_385_ = l_Float32_Model_pack(v___x_384_);
lean_dec(v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT void l_Float32_Model_ofInt8_0interp(lean_interpreter_value* stack)
{
uint8_t v_n_382_ = stack[0].m_num;
uint32_t v_res_386_;
v_res_386_ = l_Float32_Model_ofInt8(v_n_382_);
stack->m_num = v_res_386_;
}
LEAN_EXPORT lean_object* l_Float32_Model_ofInt8___boxed(lean_object* v_n_387_){
_start:
{
uint8_t v_n_boxed_388_; uint32_t v_res_389_; lean_object* v_r_390_; 
v_n_boxed_388_ = lean_unbox(v_n_387_);
v_res_389_ = l_Float32_Model_ofInt8(v_n_boxed_388_);
v_r_390_ = lean_box_uint32(v_res_389_);
return v_r_390_;
}
}
uint32_t l_Float32_Model_ofInt16(uint16_t v_n_391_){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; uint32_t v___x_394_; 
v___x_392_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_393_ = l_Float_Model_UnpackedFloat_ofInt16(v___x_392_, v_n_391_);
v___x_394_ = l_Float32_Model_pack(v___x_393_);
lean_dec(v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT void l_Float32_Model_ofInt16_0interp(lean_interpreter_value* stack)
{
uint16_t v_n_391_ = stack[0].m_num;
uint32_t v_res_395_;
v_res_395_ = l_Float32_Model_ofInt16(v_n_391_);
stack->m_num = v_res_395_;
}
LEAN_EXPORT lean_object* l_Float32_Model_ofInt16___boxed(lean_object* v_n_396_){
_start:
{
uint16_t v_n_boxed_397_; uint32_t v_res_398_; lean_object* v_r_399_; 
v_n_boxed_397_ = lean_unbox(v_n_396_);
v_res_398_ = l_Float32_Model_ofInt16(v_n_boxed_397_);
v_r_399_ = lean_box_uint32(v_res_398_);
return v_r_399_;
}
}
uint32_t l_Float32_Model_ofInt32(uint32_t v_n_400_){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; uint32_t v___x_403_; 
v___x_401_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_402_ = l_Float_Model_UnpackedFloat_ofInt32(v___x_401_, v_n_400_);
v___x_403_ = l_Float32_Model_pack(v___x_402_);
lean_dec(v___x_402_);
return v___x_403_;
}
}
LEAN_EXPORT void l_Float32_Model_ofInt32_0interp(lean_interpreter_value* stack)
{
uint32_t v_n_400_ = stack[0].m_num;
uint32_t v_res_404_;
v_res_404_ = l_Float32_Model_ofInt32(v_n_400_);
stack->m_num = v_res_404_;
}
LEAN_EXPORT lean_object* l_Float32_Model_ofInt32___boxed(lean_object* v_n_405_){
_start:
{
uint32_t v_n_boxed_406_; uint32_t v_res_407_; lean_object* v_r_408_; 
v_n_boxed_406_ = lean_unbox_uint32(v_n_405_);
lean_dec(v_n_405_);
v_res_407_ = l_Float32_Model_ofInt32(v_n_boxed_406_);
v_r_408_ = lean_box_uint32(v_res_407_);
return v_r_408_;
}
}
uint32_t l_Float32_Model_ofInt64(uint64_t v_n_409_){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; uint32_t v___x_412_; 
v___x_410_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_411_ = l_Float_Model_UnpackedFloat_ofInt64(v___x_410_, v_n_409_);
v___x_412_ = l_Float32_Model_pack(v___x_411_);
lean_dec(v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT void l_Float32_Model_ofInt64_0interp(lean_interpreter_value* stack)
{
uint64_t v_n_409_ = stack[0].m_num;
uint32_t v_res_413_;
v_res_413_ = l_Float32_Model_ofInt64(v_n_409_);
stack->m_num = v_res_413_;
}
LEAN_EXPORT lean_object* l_Float32_Model_ofInt64___boxed(lean_object* v_n_414_){
_start:
{
uint64_t v_n_boxed_415_; uint32_t v_res_416_; lean_object* v_r_417_; 
v_n_boxed_415_ = lean_unbox_uint64(v_n_414_);
lean_dec_ref(v_n_414_);
v_res_416_ = l_Float32_Model_ofInt64(v_n_boxed_415_);
v_r_417_ = lean_box_uint32(v_res_416_);
return v_r_417_;
}
}
uint32_t l_Float32_Model_ofISize(size_t v_n_418_){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; uint32_t v___x_421_; 
v___x_419_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_420_ = l_Float_Model_UnpackedFloat_ofISize(v___x_419_, v_n_418_);
v___x_421_ = l_Float32_Model_pack(v___x_420_);
lean_dec(v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT void l_Float32_Model_ofISize_0interp(lean_interpreter_value* stack)
{
size_t v_n_418_ = stack[0].m_num;
uint32_t v_res_422_;
v_res_422_ = l_Float32_Model_ofISize(v_n_418_);
stack->m_num = v_res_422_;
}
LEAN_EXPORT lean_object* l_Float32_Model_ofISize___boxed(lean_object* v_n_423_){
_start:
{
size_t v_n_boxed_424_; uint32_t v_res_425_; lean_object* v_r_426_; 
v_n_boxed_424_ = lean_unbox_usize(v_n_423_);
lean_dec(v_n_423_);
v_res_425_ = l_Float32_Model_ofISize(v_n_boxed_424_);
v_r_426_ = lean_box_uint32(v_res_425_);
return v_r_426_;
}
}
uint8_t l_Float32_Model_toUInt8(uint32_t v_f_427_){
_start:
{
lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_428_ = l_Float32_Model_unpack(v_f_427_);
v___x_429_ = l_Float_Model_UnpackedFloat_toUInt8(v___x_428_);
lean_dec(v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT void l_Float32_Model_toUInt8_0interp(lean_interpreter_value* stack)
{
uint32_t v_f_427_ = stack[0].m_num;
uint8_t v_res_430_;
v_res_430_ = l_Float32_Model_toUInt8(v_f_427_);
stack->m_num = v_res_430_;
}
LEAN_EXPORT lean_object* l_Float32_Model_toUInt8___boxed(lean_object* v_f_431_){
_start:
{
uint32_t v_f_boxed_432_; uint8_t v_res_433_; lean_object* v_r_434_; 
v_f_boxed_432_ = lean_unbox_uint32(v_f_431_);
lean_dec(v_f_431_);
v_res_433_ = l_Float32_Model_toUInt8(v_f_boxed_432_);
v_r_434_ = lean_box(v_res_433_);
return v_r_434_;
}
}
uint16_t l_Float32_Model_toUInt16(uint32_t v_f_435_){
_start:
{
lean_object* v___x_436_; uint16_t v___x_437_; 
v___x_436_ = l_Float32_Model_unpack(v_f_435_);
v___x_437_ = l_Float_Model_UnpackedFloat_toUInt16(v___x_436_);
lean_dec(v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT void l_Float32_Model_toUInt16_0interp(lean_interpreter_value* stack)
{
uint32_t v_f_435_ = stack[0].m_num;
uint16_t v_res_438_;
v_res_438_ = l_Float32_Model_toUInt16(v_f_435_);
stack->m_num = v_res_438_;
}
LEAN_EXPORT lean_object* l_Float32_Model_toUInt16___boxed(lean_object* v_f_439_){
_start:
{
uint32_t v_f_boxed_440_; uint16_t v_res_441_; lean_object* v_r_442_; 
v_f_boxed_440_ = lean_unbox_uint32(v_f_439_);
lean_dec(v_f_439_);
v_res_441_ = l_Float32_Model_toUInt16(v_f_boxed_440_);
v_r_442_ = lean_box(v_res_441_);
return v_r_442_;
}
}
uint32_t l_Float32_Model_toUInt32(uint32_t v_f_443_){
_start:
{
lean_object* v___x_444_; uint32_t v___x_445_; 
v___x_444_ = l_Float32_Model_unpack(v_f_443_);
v___x_445_ = l_Float_Model_UnpackedFloat_toUInt32(v___x_444_);
lean_dec(v___x_444_);
return v___x_445_;
}
}
LEAN_EXPORT void l_Float32_Model_toUInt32_0interp(lean_interpreter_value* stack)
{
uint32_t v_f_443_ = stack[0].m_num;
uint32_t v_res_446_;
v_res_446_ = l_Float32_Model_toUInt32(v_f_443_);
stack->m_num = v_res_446_;
}
LEAN_EXPORT lean_object* l_Float32_Model_toUInt32___boxed(lean_object* v_f_447_){
_start:
{
uint32_t v_f_boxed_448_; uint32_t v_res_449_; lean_object* v_r_450_; 
v_f_boxed_448_ = lean_unbox_uint32(v_f_447_);
lean_dec(v_f_447_);
v_res_449_ = l_Float32_Model_toUInt32(v_f_boxed_448_);
v_r_450_ = lean_box_uint32(v_res_449_);
return v_r_450_;
}
}
uint64_t l_Float32_Model_toUInt64(uint32_t v_f_451_){
_start:
{
lean_object* v___x_452_; uint64_t v___x_453_; 
v___x_452_ = l_Float32_Model_unpack(v_f_451_);
v___x_453_ = l_Float_Model_UnpackedFloat_toUInt64(v___x_452_);
lean_dec(v___x_452_);
return v___x_453_;
}
}
LEAN_EXPORT void l_Float32_Model_toUInt64_0interp(lean_interpreter_value* stack)
{
uint32_t v_f_451_ = stack[0].m_num;
uint64_t v_res_454_;
v_res_454_ = l_Float32_Model_toUInt64(v_f_451_);
stack->m_num = v_res_454_;
}
LEAN_EXPORT lean_object* l_Float32_Model_toUInt64___boxed(lean_object* v_f_455_){
_start:
{
uint32_t v_f_boxed_456_; uint64_t v_res_457_; lean_object* v_r_458_; 
v_f_boxed_456_ = lean_unbox_uint32(v_f_455_);
lean_dec(v_f_455_);
v_res_457_ = l_Float32_Model_toUInt64(v_f_boxed_456_);
v_r_458_ = lean_box_uint64(v_res_457_);
return v_r_458_;
}
}
size_t l_Float32_Model_toUSize(uint32_t v_f_459_){
_start:
{
lean_object* v___x_460_; size_t v___x_461_; 
v___x_460_ = l_Float32_Model_unpack(v_f_459_);
v___x_461_ = l_Float_Model_UnpackedFloat_toUSize(v___x_460_);
lean_dec(v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT void l_Float32_Model_toUSize_0interp(lean_interpreter_value* stack)
{
uint32_t v_f_459_ = stack[0].m_num;
size_t v_res_462_;
v_res_462_ = l_Float32_Model_toUSize(v_f_459_);
stack->m_num = v_res_462_;
}
LEAN_EXPORT lean_object* l_Float32_Model_toUSize___boxed(lean_object* v_f_463_){
_start:
{
uint32_t v_f_boxed_464_; size_t v_res_465_; lean_object* v_r_466_; 
v_f_boxed_464_ = lean_unbox_uint32(v_f_463_);
lean_dec(v_f_463_);
v_res_465_ = l_Float32_Model_toUSize(v_f_boxed_464_);
v_r_466_ = lean_box_usize(v_res_465_);
return v_r_466_;
}
}
uint8_t l_Float32_Model_toInt8(uint32_t v_f_467_){
_start:
{
lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_468_ = l_Float32_Model_unpack(v_f_467_);
v___x_469_ = l_Float_Model_UnpackedFloat_toInt8(v___x_468_);
lean_dec(v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT void l_Float32_Model_toInt8_0interp(lean_interpreter_value* stack)
{
uint32_t v_f_467_ = stack[0].m_num;
uint8_t v_res_470_;
v_res_470_ = l_Float32_Model_toInt8(v_f_467_);
stack->m_num = v_res_470_;
}
LEAN_EXPORT lean_object* l_Float32_Model_toInt8___boxed(lean_object* v_f_471_){
_start:
{
uint32_t v_f_boxed_472_; uint8_t v_res_473_; lean_object* v_r_474_; 
v_f_boxed_472_ = lean_unbox_uint32(v_f_471_);
lean_dec(v_f_471_);
v_res_473_ = l_Float32_Model_toInt8(v_f_boxed_472_);
v_r_474_ = lean_box(v_res_473_);
return v_r_474_;
}
}
uint16_t l_Float32_Model_toInt16(uint32_t v_f_475_){
_start:
{
lean_object* v___x_476_; uint16_t v___x_477_; 
v___x_476_ = l_Float32_Model_unpack(v_f_475_);
v___x_477_ = l_Float_Model_UnpackedFloat_toInt16(v___x_476_);
lean_dec(v___x_476_);
return v___x_477_;
}
}
LEAN_EXPORT void l_Float32_Model_toInt16_0interp(lean_interpreter_value* stack)
{
uint32_t v_f_475_ = stack[0].m_num;
uint16_t v_res_478_;
v_res_478_ = l_Float32_Model_toInt16(v_f_475_);
stack->m_num = v_res_478_;
}
LEAN_EXPORT lean_object* l_Float32_Model_toInt16___boxed(lean_object* v_f_479_){
_start:
{
uint32_t v_f_boxed_480_; uint16_t v_res_481_; lean_object* v_r_482_; 
v_f_boxed_480_ = lean_unbox_uint32(v_f_479_);
lean_dec(v_f_479_);
v_res_481_ = l_Float32_Model_toInt16(v_f_boxed_480_);
v_r_482_ = lean_box(v_res_481_);
return v_r_482_;
}
}
uint32_t l_Float32_Model_toInt32(uint32_t v_f_483_){
_start:
{
lean_object* v___x_484_; uint32_t v___x_485_; 
v___x_484_ = l_Float32_Model_unpack(v_f_483_);
v___x_485_ = l_Float_Model_UnpackedFloat_toInt32(v___x_484_);
lean_dec(v___x_484_);
return v___x_485_;
}
}
LEAN_EXPORT void l_Float32_Model_toInt32_0interp(lean_interpreter_value* stack)
{
uint32_t v_f_483_ = stack[0].m_num;
uint32_t v_res_486_;
v_res_486_ = l_Float32_Model_toInt32(v_f_483_);
stack->m_num = v_res_486_;
}
LEAN_EXPORT lean_object* l_Float32_Model_toInt32___boxed(lean_object* v_f_487_){
_start:
{
uint32_t v_f_boxed_488_; uint32_t v_res_489_; lean_object* v_r_490_; 
v_f_boxed_488_ = lean_unbox_uint32(v_f_487_);
lean_dec(v_f_487_);
v_res_489_ = l_Float32_Model_toInt32(v_f_boxed_488_);
v_r_490_ = lean_box_uint32(v_res_489_);
return v_r_490_;
}
}
uint64_t l_Float32_Model_toInt64(uint32_t v_f_491_){
_start:
{
lean_object* v___x_492_; uint64_t v___x_493_; 
v___x_492_ = l_Float32_Model_unpack(v_f_491_);
v___x_493_ = l_Float_Model_UnpackedFloat_toInt64(v___x_492_);
lean_dec(v___x_492_);
return v___x_493_;
}
}
LEAN_EXPORT void l_Float32_Model_toInt64_0interp(lean_interpreter_value* stack)
{
uint32_t v_f_491_ = stack[0].m_num;
uint64_t v_res_494_;
v_res_494_ = l_Float32_Model_toInt64(v_f_491_);
stack->m_num = v_res_494_;
}
LEAN_EXPORT lean_object* l_Float32_Model_toInt64___boxed(lean_object* v_f_495_){
_start:
{
uint32_t v_f_boxed_496_; uint64_t v_res_497_; lean_object* v_r_498_; 
v_f_boxed_496_ = lean_unbox_uint32(v_f_495_);
lean_dec(v_f_495_);
v_res_497_ = l_Float32_Model_toInt64(v_f_boxed_496_);
v_r_498_ = lean_box_uint64(v_res_497_);
return v_r_498_;
}
}
size_t l_Float32_Model_toISize(uint32_t v_f_499_){
_start:
{
lean_object* v___x_500_; size_t v___x_501_; 
v___x_500_ = l_Float32_Model_unpack(v_f_499_);
v___x_501_ = l_Float_Model_UnpackedFloat_toISize(v___x_500_);
lean_dec(v___x_500_);
return v___x_501_;
}
}
LEAN_EXPORT void l_Float32_Model_toISize_0interp(lean_interpreter_value* stack)
{
uint32_t v_f_499_ = stack[0].m_num;
size_t v_res_502_;
v_res_502_ = l_Float32_Model_toISize(v_f_499_);
stack->m_num = v_res_502_;
}
LEAN_EXPORT lean_object* l_Float32_Model_toISize___boxed(lean_object* v_f_503_){
_start:
{
uint32_t v_f_boxed_504_; size_t v_res_505_; lean_object* v_r_506_; 
v_f_boxed_504_ = lean_unbox_uint32(v_f_503_);
lean_dec(v_f_503_);
v_res_505_ = l_Float32_Model_toISize(v_f_boxed_504_);
v_r_506_ = lean_box_usize(v_res_505_);
return v_r_506_;
}
}
uint32_t l_Float32_Model_ofScientific(lean_object* v_m_507_, lean_object* v_e_508_){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; uint32_t v___x_511_; 
v___x_509_ = ((lean_object*)(l_Float32_Model_unpack___closed__0));
v___x_510_ = l_Float_Model_UnpackedFloat_ofScientific(v___x_509_, v_m_507_, v_e_508_);
v___x_511_ = l_Float32_Model_pack(v___x_510_);
lean_dec(v___x_510_);
return v___x_511_;
}
}
LEAN_EXPORT void l_Float32_Model_ofScientific_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_507_ = stack[0].m_obj;
lean_object* v_e_508_ = stack[1].m_obj;
uint32_t v_res_512_;
v_res_512_ = l_Float32_Model_ofScientific(v_m_507_, v_e_508_);
stack->m_num = v_res_512_;
}
LEAN_EXPORT lean_object* l_Float32_Model_ofScientific___boxed(lean_object* v_m_513_, lean_object* v_e_514_){
_start:
{
uint32_t v_res_515_; lean_object* v_r_516_; 
v_res_515_ = l_Float32_Model_ofScientific(v_m_513_, v_e_514_);
lean_dec(v_e_514_);
v_r_516_ = lean_box_uint32(v_res_515_);
return v_r_516_;
}
}
static uint32_t _init_l_Float32_Model_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_517_; uint32_t v___x_518_; 
v___x_517_ = lean_unsigned_to_nat(0u);
v___x_518_ = l_Float32_Model_ofNat(v___x_517_);
return v___x_518_;
}
}
static uint32_t _init_l_Float32_Model_instInhabited(void){
_start:
{
uint32_t v___x_519_; 
v___x_519_ = lean_uint32_once(&l_Float32_Model_instInhabited___closed__0, &l_Float32_Model_instInhabited___closed__0_once, _init_l_Float32_Model_instInhabited___closed__0);
return v___x_519_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Format_Valid(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Pack_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Operations(uint8_t builtin);
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
