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
lean_object* l_Float_Model_UnpackedFloat_neg(lean_object*);
uint8_t l_Float_Model_UnpackedFloat_le(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofInt32(lean_object*, uint32_t);
lean_object* l_Float_Model_UnpackedFloat_mul(lean_object*, lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_ofInt(lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
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
uint64_t v_x_33__boxed_6_; uint64_t v_x_34__boxed_7_; uint8_t v_res_8_; lean_object* v_r_9_; 
v_x_33__boxed_6_ = lean_unbox_uint64(v_x_4_);
lean_dec_ref(v_x_4_);
v_x_34__boxed_7_ = lean_unbox_uint64(v_x_5_);
lean_dec_ref(v_x_5_);
v_res_8_ = l_Float_instDecidableEqModel_decEq(v_x_33__boxed_6_, v_x_34__boxed_7_);
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
LEAN_EXPORT uint64_t l_Float_Model_neg(uint64_t v_a_113_){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; uint64_t v___x_116_; 
v___x_114_ = l_Float_Model_unpack(v_a_113_);
v___x_115_ = l_Float_Model_UnpackedFloat_neg(v___x_114_);
v___x_116_ = l_Float_Model_pack(v___x_115_);
lean_dec(v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_neg___boxed(lean_object* v_a_117_){
_start:
{
uint64_t v_a_boxed_118_; uint64_t v_res_119_; lean_object* v_r_120_; 
v_a_boxed_118_ = lean_unbox_uint64(v_a_117_);
lean_dec_ref(v_a_117_);
v_res_119_ = l_Float_Model_neg(v_a_boxed_118_);
v_r_120_ = lean_box_uint64(v_res_119_);
return v_r_120_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_abs(uint64_t v_a_123_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; uint64_t v___x_126_; 
v___x_124_ = l_Float_Model_unpack(v_a_123_);
v___x_125_ = l_Float_Model_UnpackedFloat_abs(v___x_124_);
v___x_126_ = l_Float_Model_pack(v___x_125_);
lean_dec(v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_abs___boxed(lean_object* v_a_127_){
_start:
{
uint64_t v_a_boxed_128_; uint64_t v_res_129_; lean_object* v_r_130_; 
v_a_boxed_128_ = lean_unbox_uint64(v_a_127_);
lean_dec_ref(v_a_127_);
v_res_129_ = l_Float_Model_abs(v_a_boxed_128_);
v_r_130_ = lean_box_uint64(v_res_129_);
return v_r_130_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_compare(uint64_t v_a_131_, uint64_t v_b_132_){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_133_ = l_Float_Model_unpack(v_a_131_);
v___x_134_ = l_Float_Model_unpack(v_b_132_);
v___x_135_ = l_Float_Model_UnpackedFloat_compare(v___x_133_, v___x_134_);
lean_dec(v___x_134_);
lean_dec(v___x_133_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_compare___boxed(lean_object* v_a_136_, lean_object* v_b_137_){
_start:
{
uint64_t v_a_boxed_138_; uint64_t v_b_boxed_139_; lean_object* v_res_140_; 
v_a_boxed_138_ = lean_unbox_uint64(v_a_136_);
lean_dec_ref(v_a_136_);
v_b_boxed_139_ = lean_unbox_uint64(v_b_137_);
lean_dec_ref(v_b_137_);
v_res_140_ = l_Float_Model_compare(v_a_boxed_138_, v_b_boxed_139_);
return v_res_140_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_le(uint64_t v_a_141_, uint64_t v_b_142_){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_143_ = l_Float_Model_unpack(v_a_141_);
v___x_144_ = l_Float_Model_unpack(v_b_142_);
v___x_145_ = l_Float_Model_UnpackedFloat_le(v___x_143_, v___x_144_);
lean_dec(v___x_144_);
lean_dec(v___x_143_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_le___boxed(lean_object* v_a_146_, lean_object* v_b_147_){
_start:
{
uint64_t v_a_boxed_148_; uint64_t v_b_boxed_149_; uint8_t v_res_150_; lean_object* v_r_151_; 
v_a_boxed_148_ = lean_unbox_uint64(v_a_146_);
lean_dec_ref(v_a_146_);
v_b_boxed_149_ = lean_unbox_uint64(v_b_147_);
lean_dec_ref(v_b_147_);
v_res_150_ = l_Float_Model_le(v_a_boxed_148_, v_b_boxed_149_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_lt(uint64_t v_a_152_, uint64_t v_b_153_){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_154_ = l_Float_Model_unpack(v_a_152_);
v___x_155_ = l_Float_Model_unpack(v_b_153_);
v___x_156_ = l_Float_Model_UnpackedFloat_lt(v___x_154_, v___x_155_);
lean_dec(v___x_155_);
lean_dec(v___x_154_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_lt___boxed(lean_object* v_a_157_, lean_object* v_b_158_){
_start:
{
uint64_t v_a_boxed_159_; uint64_t v_b_boxed_160_; uint8_t v_res_161_; lean_object* v_r_162_; 
v_a_boxed_159_ = lean_unbox_uint64(v_a_157_);
lean_dec_ref(v_a_157_);
v_b_boxed_160_ = lean_unbox_uint64(v_b_158_);
lean_dec_ref(v_b_158_);
v_res_161_ = l_Float_Model_lt(v_a_boxed_159_, v_b_boxed_160_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_beq(uint64_t v_a_163_, uint64_t v_b_164_){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_165_ = l_Float_Model_unpack(v_a_163_);
v___x_166_ = l_Float_Model_unpack(v_b_164_);
v___x_167_ = l_Float_Model_UnpackedFloat_beq(v___x_165_, v___x_166_);
lean_dec(v___x_166_);
lean_dec(v___x_165_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_beq___boxed(lean_object* v_a_168_, lean_object* v_b_169_){
_start:
{
uint64_t v_a_boxed_170_; uint64_t v_b_boxed_171_; uint8_t v_res_172_; lean_object* v_r_173_; 
v_a_boxed_170_ = lean_unbox_uint64(v_a_168_);
lean_dec_ref(v_a_168_);
v_b_boxed_171_ = lean_unbox_uint64(v_b_169_);
lean_dec_ref(v_b_169_);
v_res_172_ = l_Float_Model_beq(v_a_boxed_170_, v_b_boxed_171_);
v_r_173_ = lean_box(v_res_172_);
return v_r_173_;
}
}
static lean_object* _init_l_Float_Model_instLE(void){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lean_box(0);
return v___x_174_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_instDecidableLE(uint64_t v_a_175_, uint64_t v_b_176_){
_start:
{
uint8_t v___x_177_; 
v___x_177_ = l_Float_Model_le(v_a_175_, v_b_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_instDecidableLE___boxed(lean_object* v_a_178_, lean_object* v_b_179_){
_start:
{
uint64_t v_a_boxed_180_; uint64_t v_b_boxed_181_; uint8_t v_res_182_; lean_object* v_r_183_; 
v_a_boxed_180_ = lean_unbox_uint64(v_a_178_);
lean_dec_ref(v_a_178_);
v_b_boxed_181_ = lean_unbox_uint64(v_b_179_);
lean_dec_ref(v_b_179_);
v_res_182_ = l_Float_Model_instDecidableLE(v_a_boxed_180_, v_b_boxed_181_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
static lean_object* _init_l_Float_Model_instLT(void){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = lean_box(0);
return v___x_184_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_instDecidableLT(uint64_t v_a_185_, uint64_t v_b_186_){
_start:
{
uint8_t v___x_187_; 
v___x_187_ = l_Float_Model_lt(v_a_185_, v_b_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_instDecidableLT___boxed(lean_object* v_a_188_, lean_object* v_b_189_){
_start:
{
uint64_t v_a_boxed_190_; uint64_t v_b_boxed_191_; uint8_t v_res_192_; lean_object* v_r_193_; 
v_a_boxed_190_ = lean_unbox_uint64(v_a_188_);
lean_dec_ref(v_a_188_);
v_b_boxed_191_ = lean_unbox_uint64(v_b_189_);
lean_dec_ref(v_b_189_);
v_res_192_ = l_Float_Model_instDecidableLT(v_a_boxed_190_, v_b_boxed_191_);
v_r_193_ = lean_box(v_res_192_);
return v_r_193_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_instMin___lam__0(uint64_t v_a_196_, uint64_t v_b_197_){
_start:
{
uint8_t v___x_198_; 
v___x_198_ = l_Float_Model_le(v_a_196_, v_b_197_);
if (v___x_198_ == 0)
{
return v_b_197_;
}
else
{
return v_a_196_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_instMin___lam__0___boxed(lean_object* v_a_199_, lean_object* v_b_200_){
_start:
{
uint64_t v_a_boxed_201_; uint64_t v_b_boxed_202_; uint64_t v_res_203_; lean_object* v_r_204_; 
v_a_boxed_201_ = lean_unbox_uint64(v_a_199_);
lean_dec_ref(v_a_199_);
v_b_boxed_202_ = lean_unbox_uint64(v_b_200_);
lean_dec_ref(v_b_200_);
v_res_203_ = l_Float_Model_instMin___lam__0(v_a_boxed_201_, v_b_boxed_202_);
v_r_204_ = lean_box_uint64(v_res_203_);
return v_r_204_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_instMax___lam__0(uint64_t v_a_207_, uint64_t v_b_208_){
_start:
{
uint8_t v___x_209_; 
v___x_209_ = l_Float_Model_le(v_b_208_, v_a_207_);
if (v___x_209_ == 0)
{
return v_b_208_;
}
else
{
return v_a_207_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_instMax___lam__0___boxed(lean_object* v_a_210_, lean_object* v_b_211_){
_start:
{
uint64_t v_a_boxed_212_; uint64_t v_b_boxed_213_; uint64_t v_res_214_; lean_object* v_r_215_; 
v_a_boxed_212_ = lean_unbox_uint64(v_a_210_);
lean_dec_ref(v_a_210_);
v_b_boxed_213_ = lean_unbox_uint64(v_b_211_);
lean_dec_ref(v_b_211_);
v_res_214_ = l_Float_Model_instMax___lam__0(v_a_boxed_212_, v_b_boxed_213_);
v_r_215_ = lean_box_uint64(v_res_214_);
return v_r_215_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_isFinite(uint64_t v_a_218_){
_start:
{
lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_219_ = l_Float_Model_unpack(v_a_218_);
v___x_220_ = l_Float_Model_UnpackedFloat_isFinite(v___x_219_);
lean_dec(v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_isFinite___boxed(lean_object* v_a_221_){
_start:
{
uint64_t v_a_boxed_222_; uint8_t v_res_223_; lean_object* v_r_224_; 
v_a_boxed_222_ = lean_unbox_uint64(v_a_221_);
lean_dec_ref(v_a_221_);
v_res_223_ = l_Float_Model_isFinite(v_a_boxed_222_);
v_r_224_ = lean_box(v_res_223_);
return v_r_224_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_isInf(uint64_t v_a_225_){
_start:
{
lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_226_ = l_Float_Model_unpack(v_a_225_);
v___x_227_ = l_Float_Model_UnpackedFloat_isInf(v___x_226_);
lean_dec(v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_isInf___boxed(lean_object* v_a_228_){
_start:
{
uint64_t v_a_boxed_229_; uint8_t v_res_230_; lean_object* v_r_231_; 
v_a_boxed_229_ = lean_unbox_uint64(v_a_228_);
lean_dec_ref(v_a_228_);
v_res_230_ = l_Float_Model_isInf(v_a_boxed_229_);
v_r_231_ = lean_box(v_res_230_);
return v_r_231_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_isNaN(uint64_t v_a_232_){
_start:
{
lean_object* v___x_233_; uint8_t v___x_234_; 
v___x_233_ = l_Float_Model_unpack(v_a_232_);
v___x_234_ = l_Float_Model_UnpackedFloat_isNaN(v___x_233_);
lean_dec(v___x_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_isNaN___boxed(lean_object* v_a_235_){
_start:
{
uint64_t v_a_boxed_236_; uint8_t v_res_237_; lean_object* v_r_238_; 
v_a_boxed_236_ = lean_unbox_uint64(v_a_235_);
lean_dec_ref(v_a_235_);
v_res_237_ = l_Float_Model_isNaN(v_a_boxed_236_);
v_r_238_ = lean_box(v_res_237_);
return v_r_238_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofBits(uint64_t v_a_239_){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; uint64_t v___x_243_; 
v___x_240_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_241_ = lean_uint64_to_nat(v_a_239_);
v___x_242_ = l_Float_Model_UnpackedFloat_unpack(v___x_240_, v___x_241_);
lean_dec(v___x_241_);
v___x_243_ = l_Float_Model_pack(v___x_242_);
lean_dec(v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofBits___boxed(lean_object* v_a_244_){
_start:
{
uint64_t v_a_boxed_245_; uint64_t v_res_246_; lean_object* v_r_247_; 
v_a_boxed_245_ = lean_unbox_uint64(v_a_244_);
lean_dec_ref(v_a_244_);
v_res_246_ = l_Float_Model_ofBits(v_a_boxed_245_);
v_r_247_ = lean_box_uint64(v_res_246_);
return v_r_247_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofInt(lean_object* v_n_248_){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; uint64_t v___x_251_; 
v___x_249_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_250_ = l_Float_Model_UnpackedFloat_ofInt(v___x_249_, v_n_248_);
v___x_251_ = l_Float_Model_pack(v___x_250_);
lean_dec(v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofInt___boxed(lean_object* v_n_252_){
_start:
{
uint64_t v_res_253_; lean_object* v_r_254_; 
v_res_253_ = l_Float_Model_ofInt(v_n_252_);
lean_dec(v_n_252_);
v_r_254_ = lean_box_uint64(v_res_253_);
return v_r_254_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofNat(lean_object* v_n_255_){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; uint64_t v___x_258_; 
v___x_256_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_257_ = l_Float_Model_UnpackedFloat_ofNat(v___x_256_, v_n_255_);
v___x_258_ = l_Float_Model_pack(v___x_257_);
lean_dec(v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofNat___boxed(lean_object* v_n_259_){
_start:
{
uint64_t v_res_260_; lean_object* v_r_261_; 
v_res_260_ = l_Float_Model_ofNat(v_n_259_);
v_r_261_ = lean_box_uint64(v_res_260_);
return v_r_261_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofUInt8(uint8_t v_n_262_){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; uint64_t v___x_265_; 
v___x_263_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_264_ = l_Float_Model_UnpackedFloat_ofUInt8(v___x_263_, v_n_262_);
v___x_265_ = l_Float_Model_pack(v___x_264_);
lean_dec(v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofUInt8___boxed(lean_object* v_n_266_){
_start:
{
uint8_t v_n_boxed_267_; uint64_t v_res_268_; lean_object* v_r_269_; 
v_n_boxed_267_ = lean_unbox(v_n_266_);
v_res_268_ = l_Float_Model_ofUInt8(v_n_boxed_267_);
v_r_269_ = lean_box_uint64(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofUInt16(uint16_t v_n_270_){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; uint64_t v___x_273_; 
v___x_271_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_272_ = l_Float_Model_UnpackedFloat_ofUInt16(v___x_271_, v_n_270_);
v___x_273_ = l_Float_Model_pack(v___x_272_);
lean_dec(v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofUInt16___boxed(lean_object* v_n_274_){
_start:
{
uint16_t v_n_boxed_275_; uint64_t v_res_276_; lean_object* v_r_277_; 
v_n_boxed_275_ = lean_unbox(v_n_274_);
v_res_276_ = l_Float_Model_ofUInt16(v_n_boxed_275_);
v_r_277_ = lean_box_uint64(v_res_276_);
return v_r_277_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofUInt32(uint32_t v_n_278_){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; uint64_t v___x_281_; 
v___x_279_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_280_ = l_Float_Model_UnpackedFloat_ofUInt32(v___x_279_, v_n_278_);
v___x_281_ = l_Float_Model_pack(v___x_280_);
lean_dec(v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofUInt32___boxed(lean_object* v_n_282_){
_start:
{
uint32_t v_n_boxed_283_; uint64_t v_res_284_; lean_object* v_r_285_; 
v_n_boxed_283_ = lean_unbox_uint32(v_n_282_);
lean_dec(v_n_282_);
v_res_284_ = l_Float_Model_ofUInt32(v_n_boxed_283_);
v_r_285_ = lean_box_uint64(v_res_284_);
return v_r_285_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofUInt64(uint64_t v_n_286_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; uint64_t v___x_289_; 
v___x_287_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_288_ = l_Float_Model_UnpackedFloat_ofUInt64(v___x_287_, v_n_286_);
v___x_289_ = l_Float_Model_pack(v___x_288_);
lean_dec(v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofUInt64___boxed(lean_object* v_n_290_){
_start:
{
uint64_t v_n_boxed_291_; uint64_t v_res_292_; lean_object* v_r_293_; 
v_n_boxed_291_ = lean_unbox_uint64(v_n_290_);
lean_dec_ref(v_n_290_);
v_res_292_ = l_Float_Model_ofUInt64(v_n_boxed_291_);
v_r_293_ = lean_box_uint64(v_res_292_);
return v_r_293_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofUSize(size_t v_n_294_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; uint64_t v___x_297_; 
v___x_295_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_296_ = l_Float_Model_UnpackedFloat_ofUSize(v___x_295_, v_n_294_);
v___x_297_ = l_Float_Model_pack(v___x_296_);
lean_dec(v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofUSize___boxed(lean_object* v_n_298_){
_start:
{
size_t v_n_boxed_299_; uint64_t v_res_300_; lean_object* v_r_301_; 
v_n_boxed_299_ = lean_unbox_usize(v_n_298_);
lean_dec(v_n_298_);
v_res_300_ = l_Float_Model_ofUSize(v_n_boxed_299_);
v_r_301_ = lean_box_uint64(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofInt8(uint8_t v_n_302_){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; uint64_t v___x_305_; 
v___x_303_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_304_ = l_Float_Model_UnpackedFloat_ofInt8(v___x_303_, v_n_302_);
v___x_305_ = l_Float_Model_pack(v___x_304_);
lean_dec(v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofInt8___boxed(lean_object* v_n_306_){
_start:
{
uint8_t v_n_boxed_307_; uint64_t v_res_308_; lean_object* v_r_309_; 
v_n_boxed_307_ = lean_unbox(v_n_306_);
v_res_308_ = l_Float_Model_ofInt8(v_n_boxed_307_);
v_r_309_ = lean_box_uint64(v_res_308_);
return v_r_309_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofInt16(uint16_t v_n_310_){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; uint64_t v___x_313_; 
v___x_311_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_312_ = l_Float_Model_UnpackedFloat_ofInt16(v___x_311_, v_n_310_);
v___x_313_ = l_Float_Model_pack(v___x_312_);
lean_dec(v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofInt16___boxed(lean_object* v_n_314_){
_start:
{
uint16_t v_n_boxed_315_; uint64_t v_res_316_; lean_object* v_r_317_; 
v_n_boxed_315_ = lean_unbox(v_n_314_);
v_res_316_ = l_Float_Model_ofInt16(v_n_boxed_315_);
v_r_317_ = lean_box_uint64(v_res_316_);
return v_r_317_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofInt32(uint32_t v_n_318_){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; uint64_t v___x_321_; 
v___x_319_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_320_ = l_Float_Model_UnpackedFloat_ofInt32(v___x_319_, v_n_318_);
v___x_321_ = l_Float_Model_pack(v___x_320_);
lean_dec(v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofInt32___boxed(lean_object* v_n_322_){
_start:
{
uint32_t v_n_boxed_323_; uint64_t v_res_324_; lean_object* v_r_325_; 
v_n_boxed_323_ = lean_unbox_uint32(v_n_322_);
lean_dec(v_n_322_);
v_res_324_ = l_Float_Model_ofInt32(v_n_boxed_323_);
v_r_325_ = lean_box_uint64(v_res_324_);
return v_r_325_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofInt64(uint64_t v_n_326_){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; uint64_t v___x_329_; 
v___x_327_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_328_ = l_Float_Model_UnpackedFloat_ofInt64(v___x_327_, v_n_326_);
v___x_329_ = l_Float_Model_pack(v___x_328_);
lean_dec(v___x_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofInt64___boxed(lean_object* v_n_330_){
_start:
{
uint64_t v_n_boxed_331_; uint64_t v_res_332_; lean_object* v_r_333_; 
v_n_boxed_331_ = lean_unbox_uint64(v_n_330_);
lean_dec_ref(v_n_330_);
v_res_332_ = l_Float_Model_ofInt64(v_n_boxed_331_);
v_r_333_ = lean_box_uint64(v_res_332_);
return v_r_333_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofISize(size_t v_n_334_){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; uint64_t v___x_337_; 
v___x_335_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_336_ = l_Float_Model_UnpackedFloat_ofISize(v___x_335_, v_n_334_);
v___x_337_ = l_Float_Model_pack(v___x_336_);
lean_dec(v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofISize___boxed(lean_object* v_n_338_){
_start:
{
size_t v_n_boxed_339_; uint64_t v_res_340_; lean_object* v_r_341_; 
v_n_boxed_339_ = lean_unbox_usize(v_n_338_);
lean_dec(v_n_338_);
v_res_340_ = l_Float_Model_ofISize(v_n_boxed_339_);
v_r_341_ = lean_box_uint64(v_res_340_);
return v_r_341_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_toUInt8(uint64_t v_f_342_){
_start:
{
lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_343_ = l_Float_Model_unpack(v_f_342_);
v___x_344_ = l_Float_Model_UnpackedFloat_toUInt8(v___x_343_);
lean_dec(v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toUInt8___boxed(lean_object* v_f_345_){
_start:
{
uint64_t v_f_boxed_346_; uint8_t v_res_347_; lean_object* v_r_348_; 
v_f_boxed_346_ = lean_unbox_uint64(v_f_345_);
lean_dec_ref(v_f_345_);
v_res_347_ = l_Float_Model_toUInt8(v_f_boxed_346_);
v_r_348_ = lean_box(v_res_347_);
return v_r_348_;
}
}
LEAN_EXPORT uint16_t l_Float_Model_toUInt16(uint64_t v_f_349_){
_start:
{
lean_object* v___x_350_; uint16_t v___x_351_; 
v___x_350_ = l_Float_Model_unpack(v_f_349_);
v___x_351_ = l_Float_Model_UnpackedFloat_toUInt16(v___x_350_);
lean_dec(v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toUInt16___boxed(lean_object* v_f_352_){
_start:
{
uint64_t v_f_boxed_353_; uint16_t v_res_354_; lean_object* v_r_355_; 
v_f_boxed_353_ = lean_unbox_uint64(v_f_352_);
lean_dec_ref(v_f_352_);
v_res_354_ = l_Float_Model_toUInt16(v_f_boxed_353_);
v_r_355_ = lean_box(v_res_354_);
return v_r_355_;
}
}
LEAN_EXPORT uint32_t l_Float_Model_toUInt32(uint64_t v_f_356_){
_start:
{
lean_object* v___x_357_; uint32_t v___x_358_; 
v___x_357_ = l_Float_Model_unpack(v_f_356_);
v___x_358_ = l_Float_Model_UnpackedFloat_toUInt32(v___x_357_);
lean_dec(v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toUInt32___boxed(lean_object* v_f_359_){
_start:
{
uint64_t v_f_boxed_360_; uint32_t v_res_361_; lean_object* v_r_362_; 
v_f_boxed_360_ = lean_unbox_uint64(v_f_359_);
lean_dec_ref(v_f_359_);
v_res_361_ = l_Float_Model_toUInt32(v_f_boxed_360_);
v_r_362_ = lean_box_uint32(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_toUInt64(uint64_t v_f_363_){
_start:
{
lean_object* v___x_364_; uint64_t v___x_365_; 
v___x_364_ = l_Float_Model_unpack(v_f_363_);
v___x_365_ = l_Float_Model_UnpackedFloat_toUInt64(v___x_364_);
lean_dec(v___x_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toUInt64___boxed(lean_object* v_f_366_){
_start:
{
uint64_t v_f_boxed_367_; uint64_t v_res_368_; lean_object* v_r_369_; 
v_f_boxed_367_ = lean_unbox_uint64(v_f_366_);
lean_dec_ref(v_f_366_);
v_res_368_ = l_Float_Model_toUInt64(v_f_boxed_367_);
v_r_369_ = lean_box_uint64(v_res_368_);
return v_r_369_;
}
}
LEAN_EXPORT size_t l_Float_Model_toUSize(uint64_t v_f_370_){
_start:
{
lean_object* v___x_371_; size_t v___x_372_; 
v___x_371_ = l_Float_Model_unpack(v_f_370_);
v___x_372_ = l_Float_Model_UnpackedFloat_toUSize(v___x_371_);
lean_dec(v___x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toUSize___boxed(lean_object* v_f_373_){
_start:
{
uint64_t v_f_boxed_374_; size_t v_res_375_; lean_object* v_r_376_; 
v_f_boxed_374_ = lean_unbox_uint64(v_f_373_);
lean_dec_ref(v_f_373_);
v_res_375_ = l_Float_Model_toUSize(v_f_boxed_374_);
v_r_376_ = lean_box_usize(v_res_375_);
return v_r_376_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_toInt8(uint64_t v_f_377_){
_start:
{
lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_378_ = l_Float_Model_unpack(v_f_377_);
v___x_379_ = l_Float_Model_UnpackedFloat_toInt8(v___x_378_);
lean_dec(v___x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toInt8___boxed(lean_object* v_f_380_){
_start:
{
uint64_t v_f_boxed_381_; uint8_t v_res_382_; lean_object* v_r_383_; 
v_f_boxed_381_ = lean_unbox_uint64(v_f_380_);
lean_dec_ref(v_f_380_);
v_res_382_ = l_Float_Model_toInt8(v_f_boxed_381_);
v_r_383_ = lean_box(v_res_382_);
return v_r_383_;
}
}
LEAN_EXPORT uint16_t l_Float_Model_toInt16(uint64_t v_f_384_){
_start:
{
lean_object* v___x_385_; uint16_t v___x_386_; 
v___x_385_ = l_Float_Model_unpack(v_f_384_);
v___x_386_ = l_Float_Model_UnpackedFloat_toInt16(v___x_385_);
lean_dec(v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toInt16___boxed(lean_object* v_f_387_){
_start:
{
uint64_t v_f_boxed_388_; uint16_t v_res_389_; lean_object* v_r_390_; 
v_f_boxed_388_ = lean_unbox_uint64(v_f_387_);
lean_dec_ref(v_f_387_);
v_res_389_ = l_Float_Model_toInt16(v_f_boxed_388_);
v_r_390_ = lean_box(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT uint32_t l_Float_Model_toInt32(uint64_t v_f_391_){
_start:
{
lean_object* v___x_392_; uint32_t v___x_393_; 
v___x_392_ = l_Float_Model_unpack(v_f_391_);
v___x_393_ = l_Float_Model_UnpackedFloat_toInt32(v___x_392_);
lean_dec(v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toInt32___boxed(lean_object* v_f_394_){
_start:
{
uint64_t v_f_boxed_395_; uint32_t v_res_396_; lean_object* v_r_397_; 
v_f_boxed_395_ = lean_unbox_uint64(v_f_394_);
lean_dec_ref(v_f_394_);
v_res_396_ = l_Float_Model_toInt32(v_f_boxed_395_);
v_r_397_ = lean_box_uint32(v_res_396_);
return v_r_397_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_toInt64(uint64_t v_f_398_){
_start:
{
lean_object* v___x_399_; uint64_t v___x_400_; 
v___x_399_ = l_Float_Model_unpack(v_f_398_);
v___x_400_ = l_Float_Model_UnpackedFloat_toInt64(v___x_399_);
lean_dec(v___x_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toInt64___boxed(lean_object* v_f_401_){
_start:
{
uint64_t v_f_boxed_402_; uint64_t v_res_403_; lean_object* v_r_404_; 
v_f_boxed_402_ = lean_unbox_uint64(v_f_401_);
lean_dec_ref(v_f_401_);
v_res_403_ = l_Float_Model_toInt64(v_f_boxed_402_);
v_r_404_ = lean_box_uint64(v_res_403_);
return v_r_404_;
}
}
LEAN_EXPORT size_t l_Float_Model_toISize(uint64_t v_f_405_){
_start:
{
lean_object* v___x_406_; size_t v___x_407_; 
v___x_406_ = l_Float_Model_unpack(v_f_405_);
v___x_407_ = l_Float_Model_UnpackedFloat_toISize(v___x_406_);
lean_dec(v___x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_toISize___boxed(lean_object* v_f_408_){
_start:
{
uint64_t v_f_boxed_409_; size_t v_res_410_; lean_object* v_r_411_; 
v_f_boxed_409_ = lean_unbox_uint64(v_f_408_);
lean_dec_ref(v_f_408_);
v_res_410_ = l_Float_Model_toISize(v_f_boxed_409_);
v_r_411_ = lean_box_usize(v_res_410_);
return v_r_411_;
}
}
LEAN_EXPORT uint64_t l_Float_Model_ofScientific(lean_object* v_m_412_, lean_object* v_e_413_){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; uint64_t v___x_416_; 
v___x_414_ = ((lean_object*)(l_Float_Model_unpack___closed__0));
v___x_415_ = l_Float_Model_UnpackedFloat_ofScientific(v___x_414_, v_m_412_, v_e_413_);
v___x_416_ = l_Float_Model_pack(v___x_415_);
lean_dec(v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_ofScientific___boxed(lean_object* v_m_417_, lean_object* v_e_418_){
_start:
{
uint64_t v_res_419_; lean_object* v_r_420_; 
v_res_419_ = l_Float_Model_ofScientific(v_m_417_, v_e_418_);
lean_dec(v_e_418_);
v_r_420_ = lean_box_uint64(v_res_419_);
return v_r_420_;
}
}
static uint64_t _init_l_Float_Model_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_421_; uint64_t v___x_422_; 
v___x_421_ = lean_unsigned_to_nat(0u);
v___x_422_ = l_Float_Model_ofNat(v___x_421_);
return v___x_422_;
}
}
static uint64_t _init_l_Float_Model_instInhabited(void){
_start:
{
uint64_t v___x_423_; 
v___x_423_ = lean_uint64_once(&l_Float_Model_instInhabited___closed__0, &l_Float_Model_instInhabited___closed__0_once, _init_l_Float_Model_instInhabited___closed__0);
return v___x_423_;
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
