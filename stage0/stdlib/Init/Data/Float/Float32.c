// Lean compiler output
// Module: Init.Data.Float.Float32
// Imports: public import Init.Data.Float.Float public import Init.Data.Float.Model.Float32
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
extern uint32_t l_Float32_Model_nan;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
extern uint32_t l_Float32_Model_inf;
uint32_t lean_float32_to_bits(float);
LEAN_EXPORT lean_object* l_Float32_toModel___boxed(lean_object*);
float lean_float32_of_bits(uint32_t);
LEAN_EXPORT lean_object* l_Float32_ofModel___boxed(lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqFloat32_decEq(float, float);
LEAN_EXPORT lean_object* l_instDecidableEqFloat32_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqFloat32(float, float);
LEAN_EXPORT lean_object* l_instDecidableEqFloat32___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Float32_nan___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static float l_Float32_nan___closed__0;
LEAN_EXPORT float l_Float32_nan;
static lean_once_cell_t l_Float32_inf___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static float l_Float32_inf___closed__0;
LEAN_EXPORT float l_Float32_inf;
float lean_float32_add(float, float);
LEAN_EXPORT lean_object* l_Float32_add___boxed(lean_object*, lean_object*);
float lean_float32_sub(float, float);
LEAN_EXPORT lean_object* l_Float32_sub___boxed(lean_object*, lean_object*);
float lean_float32_mul(float, float);
LEAN_EXPORT lean_object* l_Float32_mul___boxed(lean_object*, lean_object*);
float lean_float32_div(float, float);
LEAN_EXPORT lean_object* l_Float32_div___boxed(lean_object*, lean_object*);
float lean_float32_negate(float);
LEAN_EXPORT lean_object* l_Float32_neg___boxed(lean_object*);
uint8_t lean_float32_decLt(float, float);
LEAN_EXPORT lean_object* l_Float32_lt___boxed(lean_object*, lean_object*);
uint8_t lean_float32_decLe(float, float);
LEAN_EXPORT lean_object* l_Float32_le___boxed(lean_object*, lean_object*);
float lean_float32_of_bits(uint32_t);
LEAN_EXPORT lean_object* l_Float32_ofBits___boxed(lean_object*);
uint32_t lean_float32_to_bits(float);
LEAN_EXPORT lean_object* l_Float32_toBits___boxed(lean_object*);
static const lean_closure_object l_instAddFloat32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float32_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instAddFloat32___closed__0 = (const lean_object*)&l_instAddFloat32___closed__0_value;
LEAN_EXPORT const lean_object* l_instAddFloat32 = (const lean_object*)&l_instAddFloat32___closed__0_value;
static const lean_closure_object l_instSubFloat32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float32_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSubFloat32___closed__0 = (const lean_object*)&l_instSubFloat32___closed__0_value;
LEAN_EXPORT const lean_object* l_instSubFloat32 = (const lean_object*)&l_instSubFloat32___closed__0_value;
static const lean_closure_object l_instMulFloat32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float32_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMulFloat32___closed__0 = (const lean_object*)&l_instMulFloat32___closed__0_value;
LEAN_EXPORT const lean_object* l_instMulFloat32 = (const lean_object*)&l_instMulFloat32___closed__0_value;
static const lean_closure_object l_instDivFloat32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float32_div___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instDivFloat32___closed__0 = (const lean_object*)&l_instDivFloat32___closed__0_value;
LEAN_EXPORT const lean_object* l_instDivFloat32 = (const lean_object*)&l_instDivFloat32___closed__0_value;
static const lean_closure_object l_instNegFloat32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float32_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instNegFloat32___closed__0 = (const lean_object*)&l_instNegFloat32___closed__0_value;
LEAN_EXPORT const lean_object* l_instNegFloat32 = (const lean_object*)&l_instNegFloat32___closed__0_value;
LEAN_EXPORT lean_object* l_instLTFloat32;
LEAN_EXPORT lean_object* l_instLEFloat32;
uint8_t lean_float32_beq(float, float);
LEAN_EXPORT lean_object* l_Float32_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instBEqFloat32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float32_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instBEqFloat32___closed__0 = (const lean_object*)&l_instBEqFloat32___closed__0_value;
LEAN_EXPORT const lean_object* l_instBEqFloat32 = (const lean_object*)&l_instBEqFloat32___closed__0_value;
uint8_t lean_float32_decLt(float, float);
LEAN_EXPORT lean_object* l_Float32_decLt___boxed(lean_object*, lean_object*);
uint8_t lean_float32_decLe(float, float);
LEAN_EXPORT lean_object* l_Float32_decLe___boxed(lean_object*, lean_object*);
lean_object* lean_float32_to_string(float);
LEAN_EXPORT lean_object* l_Float32_toString___boxed(lean_object*);
uint8_t lean_float32_to_uint8(float);
LEAN_EXPORT lean_object* l_Float32_toUInt8___boxed(lean_object*);
uint16_t lean_float32_to_uint16(float);
LEAN_EXPORT lean_object* l_Float32_toUInt16___boxed(lean_object*);
uint32_t lean_float32_to_uint32(float);
LEAN_EXPORT lean_object* l_Float32_toUInt32___boxed(lean_object*);
uint64_t lean_float32_to_uint64(float);
LEAN_EXPORT lean_object* l_Float32_toUInt64___boxed(lean_object*);
size_t lean_float32_to_usize(float);
LEAN_EXPORT lean_object* l_Float32_toUSize___boxed(lean_object*);
uint8_t lean_float32_isnan(float);
LEAN_EXPORT lean_object* l_Float32_isNaN___boxed(lean_object*);
uint8_t lean_float32_isfinite(float);
LEAN_EXPORT lean_object* l_Float32_isFinite___boxed(lean_object*);
uint8_t lean_float32_isinf(float);
LEAN_EXPORT lean_object* l_Float32_isInf___boxed(lean_object*);
lean_object* lean_float32_frexp(float);
LEAN_EXPORT lean_object* l_Float32_frExp___boxed(lean_object*);
static const lean_closure_object l_instToStringFloat32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float32_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringFloat32___closed__0 = (const lean_object*)&l_instToStringFloat32___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringFloat32 = (const lean_object*)&l_instToStringFloat32___closed__0_value;
float lean_uint8_to_float32(uint8_t);
LEAN_EXPORT lean_object* l_UInt8_toFloat32___boxed(lean_object*);
float lean_uint16_to_float32(uint16_t);
LEAN_EXPORT lean_object* l_UInt16_toFloat32___boxed(lean_object*);
float lean_uint32_to_float32(uint32_t);
LEAN_EXPORT lean_object* l_UInt32_toFloat32___boxed(lean_object*);
float lean_uint64_to_float32(uint64_t);
LEAN_EXPORT lean_object* l_UInt64_toFloat32___boxed(lean_object*);
float lean_usize_to_float32(size_t);
LEAN_EXPORT lean_object* l_USize_toFloat32___boxed(lean_object*);
static lean_once_cell_t l_instInhabitedFloat32___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static float l_instInhabitedFloat32___closed__0;
LEAN_EXPORT float l_instInhabitedFloat32;
LEAN_EXPORT lean_object* l_Float32_repr(float, lean_object*);
LEAN_EXPORT lean_object* l_Float32_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprFloat32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float32_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprFloat32___closed__0 = (const lean_object*)&l_instReprFloat32___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprFloat32 = (const lean_object*)&l_instReprFloat32___closed__0_value;
LEAN_EXPORT lean_object* l_instReprAtomFloat32;
float sinf(float);
LEAN_EXPORT lean_object* l_Float32_sin___boxed(lean_object*);
float cosf(float);
LEAN_EXPORT lean_object* l_Float32_cos___boxed(lean_object*);
float tanf(float);
LEAN_EXPORT lean_object* l_Float32_tan___boxed(lean_object*);
float asinf(float);
LEAN_EXPORT lean_object* l_Float32_asin___boxed(lean_object*);
float acosf(float);
LEAN_EXPORT lean_object* l_Float32_acos___boxed(lean_object*);
float atanf(float);
LEAN_EXPORT lean_object* l_Float32_atan___boxed(lean_object*);
float atan2f(float, float);
LEAN_EXPORT lean_object* l_Float32_atan2___boxed(lean_object*, lean_object*);
float sinhf(float);
LEAN_EXPORT lean_object* l_Float32_sinh___boxed(lean_object*);
float coshf(float);
LEAN_EXPORT lean_object* l_Float32_cosh___boxed(lean_object*);
float tanhf(float);
LEAN_EXPORT lean_object* l_Float32_tanh___boxed(lean_object*);
float asinhf(float);
LEAN_EXPORT lean_object* l_Float32_asinh___boxed(lean_object*);
float acoshf(float);
LEAN_EXPORT lean_object* l_Float32_acosh___boxed(lean_object*);
float atanhf(float);
LEAN_EXPORT lean_object* l_Float32_atanh___boxed(lean_object*);
float expf(float);
LEAN_EXPORT lean_object* l_Float32_exp___boxed(lean_object*);
float exp2f(float);
LEAN_EXPORT lean_object* l_Float32_exp2___boxed(lean_object*);
float logf(float);
LEAN_EXPORT lean_object* l_Float32_log___boxed(lean_object*);
float log2f(float);
LEAN_EXPORT lean_object* l_Float32_log2___boxed(lean_object*);
float log10f(float);
LEAN_EXPORT lean_object* l_Float32_log10___boxed(lean_object*);
float powf(float, float);
LEAN_EXPORT lean_object* l_Float32_pow___boxed(lean_object*, lean_object*);
float sqrtf(float);
LEAN_EXPORT lean_object* l_Float32_sqrt___boxed(lean_object*);
float cbrtf(float);
LEAN_EXPORT lean_object* l_Float32_cbrt___boxed(lean_object*);
float ceilf(float);
LEAN_EXPORT lean_object* l_Float32_ceil___boxed(lean_object*);
float floorf(float);
LEAN_EXPORT lean_object* l_Float32_floor___boxed(lean_object*);
float roundf(float);
LEAN_EXPORT lean_object* l_Float32_round___boxed(lean_object*);
float fabsf(float);
LEAN_EXPORT lean_object* l_Float32_abs___boxed(lean_object*);
static const lean_closure_object l_instHomogeneousPowFloat32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float32_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHomogeneousPowFloat32___closed__0 = (const lean_object*)&l_instHomogeneousPowFloat32___closed__0_value;
LEAN_EXPORT const lean_object* l_instHomogeneousPowFloat32 = (const lean_object*)&l_instHomogeneousPowFloat32___closed__0_value;
LEAN_EXPORT float l_instMinFloat32___lam__0(float, float);
LEAN_EXPORT lean_object* l_instMinFloat32___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instMinFloat32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMinFloat32___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMinFloat32___closed__0 = (const lean_object*)&l_instMinFloat32___closed__0_value;
LEAN_EXPORT const lean_object* l_instMinFloat32 = (const lean_object*)&l_instMinFloat32___closed__0_value;
LEAN_EXPORT float l_instMaxFloat32___lam__0(float, float);
LEAN_EXPORT lean_object* l_instMaxFloat32___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instMaxFloat32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMaxFloat32___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMaxFloat32___closed__0 = (const lean_object*)&l_instMaxFloat32___closed__0_value;
LEAN_EXPORT const lean_object* l_instMaxFloat32 = (const lean_object*)&l_instMaxFloat32___closed__0_value;
float lean_float32_scaleb(float, lean_object*);
LEAN_EXPORT lean_object* l_Float32_scaleB___boxed(lean_object*, lean_object*);
double lean_float32_to_float(float);
LEAN_EXPORT lean_object* l_Float32_toFloat___boxed(lean_object*);
float lean_float_to_float32(double);
LEAN_EXPORT lean_object* l_Float_toFloat32___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float32_toModel___boxed(lean_object* v_self_2_){
_start:
{
float v_self_boxed_3_; uint32_t v_res_4_; lean_object* v_r_5_; 
v_self_boxed_3_ = lean_unbox_float32(v_self_2_);
lean_dec_ref(v_self_2_);
v_res_4_ = lean_float32_to_bits(v_self_boxed_3_);
v_r_5_ = lean_box_uint32(v_res_4_);
return v_r_5_;
}
}
LEAN_EXPORT lean_object* l_Float32_ofModel___boxed(lean_object* v_toModel_7_){
_start:
{
uint32_t v_toModel_boxed_8_; float v_res_9_; lean_object* v_r_10_; 
v_toModel_boxed_8_ = lean_unbox_uint32(v_toModel_7_);
lean_dec(v_toModel_7_);
v_res_9_ = lean_float32_of_bits(v_toModel_boxed_8_);
v_r_10_ = lean_box_float32(v_res_9_);
return v_r_10_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqFloat32_decEq(float v_x_11_, float v_x_12_){
_start:
{
uint32_t v_toModel_13_; uint32_t v_toModel_14_; uint8_t v___x_15_; 
v_toModel_13_ = lean_float32_to_bits(v_x_11_);
v_toModel_14_ = lean_float32_to_bits(v_x_12_);
v___x_15_ = lean_uint32_dec_eq(v_toModel_13_, v_toModel_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqFloat32_decEq___boxed(lean_object* v_x_16_, lean_object* v_x_17_){
_start:
{
float v_x_25__boxed_18_; float v_x_26__boxed_19_; uint8_t v_res_20_; lean_object* v_r_21_; 
v_x_25__boxed_18_ = lean_unbox_float32(v_x_16_);
lean_dec_ref(v_x_16_);
v_x_26__boxed_19_ = lean_unbox_float32(v_x_17_);
lean_dec_ref(v_x_17_);
v_res_20_ = l_instDecidableEqFloat32_decEq(v_x_25__boxed_18_, v_x_26__boxed_19_);
v_r_21_ = lean_box(v_res_20_);
return v_r_21_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqFloat32(float v_x_22_, float v_x_23_){
_start:
{
uint8_t v___x_24_; 
v___x_24_ = l_instDecidableEqFloat32_decEq(v_x_22_, v_x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqFloat32___boxed(lean_object* v_x_25_, lean_object* v_x_26_){
_start:
{
float v_x_5__boxed_27_; float v_x_6__boxed_28_; uint8_t v_res_29_; lean_object* v_r_30_; 
v_x_5__boxed_27_ = lean_unbox_float32(v_x_25_);
lean_dec_ref(v_x_25_);
v_x_6__boxed_28_ = lean_unbox_float32(v_x_26_);
lean_dec_ref(v_x_26_);
v_res_29_ = l_instDecidableEqFloat32(v_x_5__boxed_27_, v_x_6__boxed_28_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
static float _init_l_Float32_nan___closed__0(void){
_start:
{
uint32_t v___x_31_; float v___x_32_; 
v___x_31_ = l_Float32_Model_nan;
v___x_32_ = lean_float32_of_bits(v___x_31_);
return v___x_32_;
}
}
static float _init_l_Float32_nan(void){
_start:
{
float v___x_33_; 
v___x_33_ = lean_float32_once(&l_Float32_nan___closed__0, &l_Float32_nan___closed__0_once, _init_l_Float32_nan___closed__0);
return v___x_33_;
}
}
static float _init_l_Float32_inf___closed__0(void){
_start:
{
uint32_t v___x_34_; float v___x_35_; 
v___x_34_ = l_Float32_Model_inf;
v___x_35_ = lean_float32_of_bits(v___x_34_);
return v___x_35_;
}
}
static float _init_l_Float32_inf(void){
_start:
{
float v___x_36_; 
v___x_36_ = lean_float32_once(&l_Float32_inf___closed__0, &l_Float32_inf___closed__0_once, _init_l_Float32_inf___closed__0);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Float32_add___boxed(lean_object* v_a_00___x40___internal___hyg_39_, lean_object* v_a_00___x40___internal___hyg_40_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_41_; float v_a_00___x40___internal___hyg_2__boxed_42_; float v_res_43_; lean_object* v_r_44_; 
v_a_00___x40___internal___hyg_1__boxed_41_ = lean_unbox_float32(v_a_00___x40___internal___hyg_39_);
lean_dec_ref(v_a_00___x40___internal___hyg_39_);
v_a_00___x40___internal___hyg_2__boxed_42_ = lean_unbox_float32(v_a_00___x40___internal___hyg_40_);
lean_dec_ref(v_a_00___x40___internal___hyg_40_);
v_res_43_ = lean_float32_add(v_a_00___x40___internal___hyg_1__boxed_41_, v_a_00___x40___internal___hyg_2__boxed_42_);
v_r_44_ = lean_box_float32(v_res_43_);
return v_r_44_;
}
}
LEAN_EXPORT lean_object* l_Float32_sub___boxed(lean_object* v_a_00___x40___internal___hyg_47_, lean_object* v_a_00___x40___internal___hyg_48_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_49_; float v_a_00___x40___internal___hyg_2__boxed_50_; float v_res_51_; lean_object* v_r_52_; 
v_a_00___x40___internal___hyg_1__boxed_49_ = lean_unbox_float32(v_a_00___x40___internal___hyg_47_);
lean_dec_ref(v_a_00___x40___internal___hyg_47_);
v_a_00___x40___internal___hyg_2__boxed_50_ = lean_unbox_float32(v_a_00___x40___internal___hyg_48_);
lean_dec_ref(v_a_00___x40___internal___hyg_48_);
v_res_51_ = lean_float32_sub(v_a_00___x40___internal___hyg_1__boxed_49_, v_a_00___x40___internal___hyg_2__boxed_50_);
v_r_52_ = lean_box_float32(v_res_51_);
return v_r_52_;
}
}
LEAN_EXPORT lean_object* l_Float32_mul___boxed(lean_object* v_a_00___x40___internal___hyg_55_, lean_object* v_a_00___x40___internal___hyg_56_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_57_; float v_a_00___x40___internal___hyg_2__boxed_58_; float v_res_59_; lean_object* v_r_60_; 
v_a_00___x40___internal___hyg_1__boxed_57_ = lean_unbox_float32(v_a_00___x40___internal___hyg_55_);
lean_dec_ref(v_a_00___x40___internal___hyg_55_);
v_a_00___x40___internal___hyg_2__boxed_58_ = lean_unbox_float32(v_a_00___x40___internal___hyg_56_);
lean_dec_ref(v_a_00___x40___internal___hyg_56_);
v_res_59_ = lean_float32_mul(v_a_00___x40___internal___hyg_1__boxed_57_, v_a_00___x40___internal___hyg_2__boxed_58_);
v_r_60_ = lean_box_float32(v_res_59_);
return v_r_60_;
}
}
LEAN_EXPORT lean_object* l_Float32_div___boxed(lean_object* v_a_00___x40___internal___hyg_63_, lean_object* v_a_00___x40___internal___hyg_64_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_65_; float v_a_00___x40___internal___hyg_2__boxed_66_; float v_res_67_; lean_object* v_r_68_; 
v_a_00___x40___internal___hyg_1__boxed_65_ = lean_unbox_float32(v_a_00___x40___internal___hyg_63_);
lean_dec_ref(v_a_00___x40___internal___hyg_63_);
v_a_00___x40___internal___hyg_2__boxed_66_ = lean_unbox_float32(v_a_00___x40___internal___hyg_64_);
lean_dec_ref(v_a_00___x40___internal___hyg_64_);
v_res_67_ = lean_float32_div(v_a_00___x40___internal___hyg_1__boxed_65_, v_a_00___x40___internal___hyg_2__boxed_66_);
v_r_68_ = lean_box_float32(v_res_67_);
return v_r_68_;
}
}
LEAN_EXPORT lean_object* l_Float32_neg___boxed(lean_object* v_a_00___x40___internal___hyg_70_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_71_; float v_res_72_; lean_object* v_r_73_; 
v_a_00___x40___internal___hyg_1__boxed_71_ = lean_unbox_float32(v_a_00___x40___internal___hyg_70_);
lean_dec_ref(v_a_00___x40___internal___hyg_70_);
v_res_72_ = lean_float32_negate(v_a_00___x40___internal___hyg_1__boxed_71_);
v_r_73_ = lean_box_float32(v_res_72_);
return v_r_73_;
}
}
LEAN_EXPORT lean_object* l_Float32_lt___boxed(lean_object* v_a_00___x40___internal___hyg_76_, lean_object* v_a_00___x40___internal___hyg_77_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_78_; float v_a_00___x40___internal___hyg_2__boxed_79_; uint8_t v_res_80_; lean_object* v_r_81_; 
v_a_00___x40___internal___hyg_1__boxed_78_ = lean_unbox_float32(v_a_00___x40___internal___hyg_76_);
lean_dec_ref(v_a_00___x40___internal___hyg_76_);
v_a_00___x40___internal___hyg_2__boxed_79_ = lean_unbox_float32(v_a_00___x40___internal___hyg_77_);
lean_dec_ref(v_a_00___x40___internal___hyg_77_);
v_res_80_ = lean_float32_decLt(v_a_00___x40___internal___hyg_1__boxed_78_, v_a_00___x40___internal___hyg_2__boxed_79_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
LEAN_EXPORT lean_object* l_Float32_le___boxed(lean_object* v_a_00___x40___internal___hyg_84_, lean_object* v_a_00___x40___internal___hyg_85_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_86_; float v_a_00___x40___internal___hyg_2__boxed_87_; uint8_t v_res_88_; lean_object* v_r_89_; 
v_a_00___x40___internal___hyg_1__boxed_86_ = lean_unbox_float32(v_a_00___x40___internal___hyg_84_);
lean_dec_ref(v_a_00___x40___internal___hyg_84_);
v_a_00___x40___internal___hyg_2__boxed_87_ = lean_unbox_float32(v_a_00___x40___internal___hyg_85_);
lean_dec_ref(v_a_00___x40___internal___hyg_85_);
v_res_88_ = lean_float32_decLe(v_a_00___x40___internal___hyg_1__boxed_86_, v_a_00___x40___internal___hyg_2__boxed_87_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
LEAN_EXPORT lean_object* l_Float32_ofBits___boxed(lean_object* v_a_00___x40___internal___hyg_91_){
_start:
{
uint32_t v_a_00___x40___internal___hyg_1__boxed_92_; float v_res_93_; lean_object* v_r_94_; 
v_a_00___x40___internal___hyg_1__boxed_92_ = lean_unbox_uint32(v_a_00___x40___internal___hyg_91_);
lean_dec(v_a_00___x40___internal___hyg_91_);
v_res_93_ = lean_float32_of_bits(v_a_00___x40___internal___hyg_1__boxed_92_);
v_r_94_ = lean_box_float32(v_res_93_);
return v_r_94_;
}
}
LEAN_EXPORT lean_object* l_Float32_toBits___boxed(lean_object* v_a_00___x40___internal___hyg_96_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_97_; uint32_t v_res_98_; lean_object* v_r_99_; 
v_a_00___x40___internal___hyg_1__boxed_97_ = lean_unbox_float32(v_a_00___x40___internal___hyg_96_);
lean_dec_ref(v_a_00___x40___internal___hyg_96_);
v_res_98_ = lean_float32_to_bits(v_a_00___x40___internal___hyg_1__boxed_97_);
v_r_99_ = lean_box_uint32(v_res_98_);
return v_r_99_;
}
}
static lean_object* _init_l_instLTFloat32(void){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_box(0);
return v___x_110_;
}
}
static lean_object* _init_l_instLEFloat32(void){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = lean_box(0);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Float32_beq___boxed(lean_object* v_a_114_, lean_object* v_b_115_){
_start:
{
float v_a_boxed_116_; float v_b_boxed_117_; uint8_t v_res_118_; lean_object* v_r_119_; 
v_a_boxed_116_ = lean_unbox_float32(v_a_114_);
lean_dec_ref(v_a_114_);
v_b_boxed_117_ = lean_unbox_float32(v_b_115_);
lean_dec_ref(v_b_115_);
v_res_118_ = lean_float32_beq(v_a_boxed_116_, v_b_boxed_117_);
v_r_119_ = lean_box(v_res_118_);
return v_r_119_;
}
}
LEAN_EXPORT lean_object* l_Float32_decLt___boxed(lean_object* v_a_124_, lean_object* v_b_125_){
_start:
{
float v_a_boxed_126_; float v_b_boxed_127_; uint8_t v_res_128_; lean_object* v_r_129_; 
v_a_boxed_126_ = lean_unbox_float32(v_a_124_);
lean_dec_ref(v_a_124_);
v_b_boxed_127_ = lean_unbox_float32(v_b_125_);
lean_dec_ref(v_b_125_);
v_res_128_ = lean_float32_decLt(v_a_boxed_126_, v_b_boxed_127_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT lean_object* l_Float32_decLe___boxed(lean_object* v_a_132_, lean_object* v_b_133_){
_start:
{
float v_a_boxed_134_; float v_b_boxed_135_; uint8_t v_res_136_; lean_object* v_r_137_; 
v_a_boxed_134_ = lean_unbox_float32(v_a_132_);
lean_dec_ref(v_a_132_);
v_b_boxed_135_ = lean_unbox_float32(v_b_133_);
lean_dec_ref(v_b_133_);
v_res_136_ = lean_float32_decLe(v_a_boxed_134_, v_b_boxed_135_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT lean_object* l_Float32_toString___boxed(lean_object* v_a_00___x40___internal___hyg_139_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_140_; lean_object* v_res_141_; 
v_a_00___x40___internal___hyg_1__boxed_140_ = lean_unbox_float32(v_a_00___x40___internal___hyg_139_);
lean_dec_ref(v_a_00___x40___internal___hyg_139_);
v_res_141_ = lean_float32_to_string(v_a_00___x40___internal___hyg_1__boxed_140_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Float32_toUInt8___boxed(lean_object* v_a_00___x40___internal___hyg_143_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_144_; uint8_t v_res_145_; lean_object* v_r_146_; 
v_a_00___x40___internal___hyg_1__boxed_144_ = lean_unbox_float32(v_a_00___x40___internal___hyg_143_);
lean_dec_ref(v_a_00___x40___internal___hyg_143_);
v_res_145_ = lean_float32_to_uint8(v_a_00___x40___internal___hyg_1__boxed_144_);
v_r_146_ = lean_box(v_res_145_);
return v_r_146_;
}
}
LEAN_EXPORT lean_object* l_Float32_toUInt16___boxed(lean_object* v_a_00___x40___internal___hyg_148_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_149_; uint16_t v_res_150_; lean_object* v_r_151_; 
v_a_00___x40___internal___hyg_1__boxed_149_ = lean_unbox_float32(v_a_00___x40___internal___hyg_148_);
lean_dec_ref(v_a_00___x40___internal___hyg_148_);
v_res_150_ = lean_float32_to_uint16(v_a_00___x40___internal___hyg_1__boxed_149_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
LEAN_EXPORT lean_object* l_Float32_toUInt32___boxed(lean_object* v_a_00___x40___internal___hyg_153_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_154_; uint32_t v_res_155_; lean_object* v_r_156_; 
v_a_00___x40___internal___hyg_1__boxed_154_ = lean_unbox_float32(v_a_00___x40___internal___hyg_153_);
lean_dec_ref(v_a_00___x40___internal___hyg_153_);
v_res_155_ = lean_float32_to_uint32(v_a_00___x40___internal___hyg_1__boxed_154_);
v_r_156_ = lean_box_uint32(v_res_155_);
return v_r_156_;
}
}
LEAN_EXPORT lean_object* l_Float32_toUInt64___boxed(lean_object* v_a_00___x40___internal___hyg_158_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_159_; uint64_t v_res_160_; lean_object* v_r_161_; 
v_a_00___x40___internal___hyg_1__boxed_159_ = lean_unbox_float32(v_a_00___x40___internal___hyg_158_);
lean_dec_ref(v_a_00___x40___internal___hyg_158_);
v_res_160_ = lean_float32_to_uint64(v_a_00___x40___internal___hyg_1__boxed_159_);
v_r_161_ = lean_box_uint64(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT lean_object* l_Float32_toUSize___boxed(lean_object* v_a_00___x40___internal___hyg_163_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_164_; size_t v_res_165_; lean_object* v_r_166_; 
v_a_00___x40___internal___hyg_1__boxed_164_ = lean_unbox_float32(v_a_00___x40___internal___hyg_163_);
lean_dec_ref(v_a_00___x40___internal___hyg_163_);
v_res_165_ = lean_float32_to_usize(v_a_00___x40___internal___hyg_1__boxed_164_);
v_r_166_ = lean_box_usize(v_res_165_);
return v_r_166_;
}
}
LEAN_EXPORT lean_object* l_Float32_isNaN___boxed(lean_object* v_a_00___x40___internal___hyg_168_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_169_; uint8_t v_res_170_; lean_object* v_r_171_; 
v_a_00___x40___internal___hyg_1__boxed_169_ = lean_unbox_float32(v_a_00___x40___internal___hyg_168_);
lean_dec_ref(v_a_00___x40___internal___hyg_168_);
v_res_170_ = lean_float32_isnan(v_a_00___x40___internal___hyg_1__boxed_169_);
v_r_171_ = lean_box(v_res_170_);
return v_r_171_;
}
}
LEAN_EXPORT lean_object* l_Float32_isFinite___boxed(lean_object* v_a_00___x40___internal___hyg_173_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_174_; uint8_t v_res_175_; lean_object* v_r_176_; 
v_a_00___x40___internal___hyg_1__boxed_174_ = lean_unbox_float32(v_a_00___x40___internal___hyg_173_);
lean_dec_ref(v_a_00___x40___internal___hyg_173_);
v_res_175_ = lean_float32_isfinite(v_a_00___x40___internal___hyg_1__boxed_174_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
LEAN_EXPORT lean_object* l_Float32_isInf___boxed(lean_object* v_a_00___x40___internal___hyg_178_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_179_; uint8_t v_res_180_; lean_object* v_r_181_; 
v_a_00___x40___internal___hyg_1__boxed_179_ = lean_unbox_float32(v_a_00___x40___internal___hyg_178_);
lean_dec_ref(v_a_00___x40___internal___hyg_178_);
v_res_180_ = lean_float32_isinf(v_a_00___x40___internal___hyg_1__boxed_179_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
LEAN_EXPORT lean_object* l_Float32_frExp___boxed(lean_object* v_a_00___x40___internal___hyg_183_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_184_; lean_object* v_res_185_; 
v_a_00___x40___internal___hyg_1__boxed_184_ = lean_unbox_float32(v_a_00___x40___internal___hyg_183_);
lean_dec_ref(v_a_00___x40___internal___hyg_183_);
v_res_185_ = lean_float32_frexp(v_a_00___x40___internal___hyg_1__boxed_184_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_UInt8_toFloat32___boxed(lean_object* v_n_189_){
_start:
{
uint8_t v_n_boxed_190_; float v_res_191_; lean_object* v_r_192_; 
v_n_boxed_190_ = lean_unbox(v_n_189_);
v_res_191_ = lean_uint8_to_float32(v_n_boxed_190_);
v_r_192_ = lean_box_float32(v_res_191_);
return v_r_192_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toFloat32___boxed(lean_object* v_n_194_){
_start:
{
uint16_t v_n_boxed_195_; float v_res_196_; lean_object* v_r_197_; 
v_n_boxed_195_ = lean_unbox(v_n_194_);
v_res_196_ = lean_uint16_to_float32(v_n_boxed_195_);
v_r_197_ = lean_box_float32(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toFloat32___boxed(lean_object* v_n_199_){
_start:
{
uint32_t v_n_boxed_200_; float v_res_201_; lean_object* v_r_202_; 
v_n_boxed_200_ = lean_unbox_uint32(v_n_199_);
lean_dec(v_n_199_);
v_res_201_ = lean_uint32_to_float32(v_n_boxed_200_);
v_r_202_ = lean_box_float32(v_res_201_);
return v_r_202_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toFloat32___boxed(lean_object* v_n_204_){
_start:
{
uint64_t v_n_boxed_205_; float v_res_206_; lean_object* v_r_207_; 
v_n_boxed_205_ = lean_unbox_uint64(v_n_204_);
lean_dec_ref(v_n_204_);
v_res_206_ = lean_uint64_to_float32(v_n_boxed_205_);
v_r_207_ = lean_box_float32(v_res_206_);
return v_r_207_;
}
}
LEAN_EXPORT lean_object* l_USize_toFloat32___boxed(lean_object* v_n_209_){
_start:
{
size_t v_n_boxed_210_; float v_res_211_; lean_object* v_r_212_; 
v_n_boxed_210_ = lean_unbox_usize(v_n_209_);
lean_dec(v_n_209_);
v_res_211_ = lean_usize_to_float32(v_n_boxed_210_);
v_r_212_ = lean_box_float32(v_res_211_);
return v_r_212_;
}
}
static float _init_l_instInhabitedFloat32___closed__0(void){
_start:
{
uint64_t v___x_213_; float v___x_214_; 
v___x_213_ = 0ULL;
v___x_214_ = lean_uint64_to_float32(v___x_213_);
return v___x_214_;
}
}
static float _init_l_instInhabitedFloat32(void){
_start:
{
float v___x_215_; 
v___x_215_ = lean_float32_once(&l_instInhabitedFloat32___closed__0, &l_instInhabitedFloat32___closed__0_once, _init_l_instInhabitedFloat32___closed__0);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Float32_repr(float v_n_216_, lean_object* v_prec_217_){
_start:
{
float v___x_218_; uint8_t v___x_219_; 
v___x_218_ = lean_float32_once(&l_instInhabitedFloat32___closed__0, &l_instInhabitedFloat32___closed__0_once, _init_l_instInhabitedFloat32___closed__0);
v___x_219_ = lean_float32_decLt(v_n_216_, v___x_218_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = lean_float32_to_string(v_n_216_);
v___x_221_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
return v___x_221_;
}
else
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_222_ = lean_float32_to_string(v_n_216_);
v___x_223_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
v___x_224_ = l_Repr_addAppParen(v___x_223_, v_prec_217_);
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l_Float32_repr___boxed(lean_object* v_n_225_, lean_object* v_prec_226_){
_start:
{
float v_n_boxed_227_; lean_object* v_res_228_; 
v_n_boxed_227_ = lean_unbox_float32(v_n_225_);
lean_dec_ref(v_n_225_);
v_res_228_ = l_Float32_repr(v_n_boxed_227_, v_prec_226_);
lean_dec(v_prec_226_);
return v_res_228_;
}
}
static lean_object* _init_l_instReprAtomFloat32(void){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = lean_box(0);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Float32_sin___boxed(lean_object* v_a_00___x40___internal___hyg_233_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_234_; float v_res_235_; lean_object* v_r_236_; 
v_a_00___x40___internal___hyg_1__boxed_234_ = lean_unbox_float32(v_a_00___x40___internal___hyg_233_);
lean_dec_ref(v_a_00___x40___internal___hyg_233_);
v_res_235_ = sinf(v_a_00___x40___internal___hyg_1__boxed_234_);
v_r_236_ = lean_box_float32(v_res_235_);
return v_r_236_;
}
}
LEAN_EXPORT lean_object* l_Float32_cos___boxed(lean_object* v_a_00___x40___internal___hyg_238_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_239_; float v_res_240_; lean_object* v_r_241_; 
v_a_00___x40___internal___hyg_1__boxed_239_ = lean_unbox_float32(v_a_00___x40___internal___hyg_238_);
lean_dec_ref(v_a_00___x40___internal___hyg_238_);
v_res_240_ = cosf(v_a_00___x40___internal___hyg_1__boxed_239_);
v_r_241_ = lean_box_float32(v_res_240_);
return v_r_241_;
}
}
LEAN_EXPORT lean_object* l_Float32_tan___boxed(lean_object* v_a_00___x40___internal___hyg_243_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_244_; float v_res_245_; lean_object* v_r_246_; 
v_a_00___x40___internal___hyg_1__boxed_244_ = lean_unbox_float32(v_a_00___x40___internal___hyg_243_);
lean_dec_ref(v_a_00___x40___internal___hyg_243_);
v_res_245_ = tanf(v_a_00___x40___internal___hyg_1__boxed_244_);
v_r_246_ = lean_box_float32(v_res_245_);
return v_r_246_;
}
}
LEAN_EXPORT lean_object* l_Float32_asin___boxed(lean_object* v_a_00___x40___internal___hyg_248_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_249_; float v_res_250_; lean_object* v_r_251_; 
v_a_00___x40___internal___hyg_1__boxed_249_ = lean_unbox_float32(v_a_00___x40___internal___hyg_248_);
lean_dec_ref(v_a_00___x40___internal___hyg_248_);
v_res_250_ = asinf(v_a_00___x40___internal___hyg_1__boxed_249_);
v_r_251_ = lean_box_float32(v_res_250_);
return v_r_251_;
}
}
LEAN_EXPORT lean_object* l_Float32_acos___boxed(lean_object* v_a_00___x40___internal___hyg_253_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_254_; float v_res_255_; lean_object* v_r_256_; 
v_a_00___x40___internal___hyg_1__boxed_254_ = lean_unbox_float32(v_a_00___x40___internal___hyg_253_);
lean_dec_ref(v_a_00___x40___internal___hyg_253_);
v_res_255_ = acosf(v_a_00___x40___internal___hyg_1__boxed_254_);
v_r_256_ = lean_box_float32(v_res_255_);
return v_r_256_;
}
}
LEAN_EXPORT lean_object* l_Float32_atan___boxed(lean_object* v_a_00___x40___internal___hyg_258_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_259_; float v_res_260_; lean_object* v_r_261_; 
v_a_00___x40___internal___hyg_1__boxed_259_ = lean_unbox_float32(v_a_00___x40___internal___hyg_258_);
lean_dec_ref(v_a_00___x40___internal___hyg_258_);
v_res_260_ = atanf(v_a_00___x40___internal___hyg_1__boxed_259_);
v_r_261_ = lean_box_float32(v_res_260_);
return v_r_261_;
}
}
LEAN_EXPORT lean_object* l_Float32_atan2___boxed(lean_object* v_a_00___x40___internal___hyg_264_, lean_object* v_a_00___x40___internal___hyg_265_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_266_; float v_a_00___x40___internal___hyg_2__boxed_267_; float v_res_268_; lean_object* v_r_269_; 
v_a_00___x40___internal___hyg_1__boxed_266_ = lean_unbox_float32(v_a_00___x40___internal___hyg_264_);
lean_dec_ref(v_a_00___x40___internal___hyg_264_);
v_a_00___x40___internal___hyg_2__boxed_267_ = lean_unbox_float32(v_a_00___x40___internal___hyg_265_);
lean_dec_ref(v_a_00___x40___internal___hyg_265_);
v_res_268_ = atan2f(v_a_00___x40___internal___hyg_1__boxed_266_, v_a_00___x40___internal___hyg_2__boxed_267_);
v_r_269_ = lean_box_float32(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT lean_object* l_Float32_sinh___boxed(lean_object* v_a_00___x40___internal___hyg_271_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_272_; float v_res_273_; lean_object* v_r_274_; 
v_a_00___x40___internal___hyg_1__boxed_272_ = lean_unbox_float32(v_a_00___x40___internal___hyg_271_);
lean_dec_ref(v_a_00___x40___internal___hyg_271_);
v_res_273_ = sinhf(v_a_00___x40___internal___hyg_1__boxed_272_);
v_r_274_ = lean_box_float32(v_res_273_);
return v_r_274_;
}
}
LEAN_EXPORT lean_object* l_Float32_cosh___boxed(lean_object* v_a_00___x40___internal___hyg_276_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_277_; float v_res_278_; lean_object* v_r_279_; 
v_a_00___x40___internal___hyg_1__boxed_277_ = lean_unbox_float32(v_a_00___x40___internal___hyg_276_);
lean_dec_ref(v_a_00___x40___internal___hyg_276_);
v_res_278_ = coshf(v_a_00___x40___internal___hyg_1__boxed_277_);
v_r_279_ = lean_box_float32(v_res_278_);
return v_r_279_;
}
}
LEAN_EXPORT lean_object* l_Float32_tanh___boxed(lean_object* v_a_00___x40___internal___hyg_281_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_282_; float v_res_283_; lean_object* v_r_284_; 
v_a_00___x40___internal___hyg_1__boxed_282_ = lean_unbox_float32(v_a_00___x40___internal___hyg_281_);
lean_dec_ref(v_a_00___x40___internal___hyg_281_);
v_res_283_ = tanhf(v_a_00___x40___internal___hyg_1__boxed_282_);
v_r_284_ = lean_box_float32(v_res_283_);
return v_r_284_;
}
}
LEAN_EXPORT lean_object* l_Float32_asinh___boxed(lean_object* v_a_00___x40___internal___hyg_286_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_287_; float v_res_288_; lean_object* v_r_289_; 
v_a_00___x40___internal___hyg_1__boxed_287_ = lean_unbox_float32(v_a_00___x40___internal___hyg_286_);
lean_dec_ref(v_a_00___x40___internal___hyg_286_);
v_res_288_ = asinhf(v_a_00___x40___internal___hyg_1__boxed_287_);
v_r_289_ = lean_box_float32(v_res_288_);
return v_r_289_;
}
}
LEAN_EXPORT lean_object* l_Float32_acosh___boxed(lean_object* v_a_00___x40___internal___hyg_291_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_292_; float v_res_293_; lean_object* v_r_294_; 
v_a_00___x40___internal___hyg_1__boxed_292_ = lean_unbox_float32(v_a_00___x40___internal___hyg_291_);
lean_dec_ref(v_a_00___x40___internal___hyg_291_);
v_res_293_ = acoshf(v_a_00___x40___internal___hyg_1__boxed_292_);
v_r_294_ = lean_box_float32(v_res_293_);
return v_r_294_;
}
}
LEAN_EXPORT lean_object* l_Float32_atanh___boxed(lean_object* v_a_00___x40___internal___hyg_296_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_297_; float v_res_298_; lean_object* v_r_299_; 
v_a_00___x40___internal___hyg_1__boxed_297_ = lean_unbox_float32(v_a_00___x40___internal___hyg_296_);
lean_dec_ref(v_a_00___x40___internal___hyg_296_);
v_res_298_ = atanhf(v_a_00___x40___internal___hyg_1__boxed_297_);
v_r_299_ = lean_box_float32(v_res_298_);
return v_r_299_;
}
}
LEAN_EXPORT lean_object* l_Float32_exp___boxed(lean_object* v_a_00___x40___internal___hyg_301_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_302_; float v_res_303_; lean_object* v_r_304_; 
v_a_00___x40___internal___hyg_1__boxed_302_ = lean_unbox_float32(v_a_00___x40___internal___hyg_301_);
lean_dec_ref(v_a_00___x40___internal___hyg_301_);
v_res_303_ = expf(v_a_00___x40___internal___hyg_1__boxed_302_);
v_r_304_ = lean_box_float32(v_res_303_);
return v_r_304_;
}
}
LEAN_EXPORT lean_object* l_Float32_exp2___boxed(lean_object* v_a_00___x40___internal___hyg_306_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_307_; float v_res_308_; lean_object* v_r_309_; 
v_a_00___x40___internal___hyg_1__boxed_307_ = lean_unbox_float32(v_a_00___x40___internal___hyg_306_);
lean_dec_ref(v_a_00___x40___internal___hyg_306_);
v_res_308_ = exp2f(v_a_00___x40___internal___hyg_1__boxed_307_);
v_r_309_ = lean_box_float32(v_res_308_);
return v_r_309_;
}
}
LEAN_EXPORT lean_object* l_Float32_log___boxed(lean_object* v_a_00___x40___internal___hyg_311_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_312_; float v_res_313_; lean_object* v_r_314_; 
v_a_00___x40___internal___hyg_1__boxed_312_ = lean_unbox_float32(v_a_00___x40___internal___hyg_311_);
lean_dec_ref(v_a_00___x40___internal___hyg_311_);
v_res_313_ = logf(v_a_00___x40___internal___hyg_1__boxed_312_);
v_r_314_ = lean_box_float32(v_res_313_);
return v_r_314_;
}
}
LEAN_EXPORT lean_object* l_Float32_log2___boxed(lean_object* v_a_00___x40___internal___hyg_316_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_317_; float v_res_318_; lean_object* v_r_319_; 
v_a_00___x40___internal___hyg_1__boxed_317_ = lean_unbox_float32(v_a_00___x40___internal___hyg_316_);
lean_dec_ref(v_a_00___x40___internal___hyg_316_);
v_res_318_ = log2f(v_a_00___x40___internal___hyg_1__boxed_317_);
v_r_319_ = lean_box_float32(v_res_318_);
return v_r_319_;
}
}
LEAN_EXPORT lean_object* l_Float32_log10___boxed(lean_object* v_a_00___x40___internal___hyg_321_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_322_; float v_res_323_; lean_object* v_r_324_; 
v_a_00___x40___internal___hyg_1__boxed_322_ = lean_unbox_float32(v_a_00___x40___internal___hyg_321_);
lean_dec_ref(v_a_00___x40___internal___hyg_321_);
v_res_323_ = log10f(v_a_00___x40___internal___hyg_1__boxed_322_);
v_r_324_ = lean_box_float32(v_res_323_);
return v_r_324_;
}
}
LEAN_EXPORT lean_object* l_Float32_pow___boxed(lean_object* v_a_00___x40___internal___hyg_327_, lean_object* v_a_00___x40___internal___hyg_328_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_329_; float v_a_00___x40___internal___hyg_2__boxed_330_; float v_res_331_; lean_object* v_r_332_; 
v_a_00___x40___internal___hyg_1__boxed_329_ = lean_unbox_float32(v_a_00___x40___internal___hyg_327_);
lean_dec_ref(v_a_00___x40___internal___hyg_327_);
v_a_00___x40___internal___hyg_2__boxed_330_ = lean_unbox_float32(v_a_00___x40___internal___hyg_328_);
lean_dec_ref(v_a_00___x40___internal___hyg_328_);
v_res_331_ = powf(v_a_00___x40___internal___hyg_1__boxed_329_, v_a_00___x40___internal___hyg_2__boxed_330_);
v_r_332_ = lean_box_float32(v_res_331_);
return v_r_332_;
}
}
LEAN_EXPORT lean_object* l_Float32_sqrt___boxed(lean_object* v_a_00___x40___internal___hyg_334_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_335_; float v_res_336_; lean_object* v_r_337_; 
v_a_00___x40___internal___hyg_1__boxed_335_ = lean_unbox_float32(v_a_00___x40___internal___hyg_334_);
lean_dec_ref(v_a_00___x40___internal___hyg_334_);
v_res_336_ = sqrtf(v_a_00___x40___internal___hyg_1__boxed_335_);
v_r_337_ = lean_box_float32(v_res_336_);
return v_r_337_;
}
}
LEAN_EXPORT lean_object* l_Float32_cbrt___boxed(lean_object* v_a_00___x40___internal___hyg_339_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_340_; float v_res_341_; lean_object* v_r_342_; 
v_a_00___x40___internal___hyg_1__boxed_340_ = lean_unbox_float32(v_a_00___x40___internal___hyg_339_);
lean_dec_ref(v_a_00___x40___internal___hyg_339_);
v_res_341_ = cbrtf(v_a_00___x40___internal___hyg_1__boxed_340_);
v_r_342_ = lean_box_float32(v_res_341_);
return v_r_342_;
}
}
LEAN_EXPORT lean_object* l_Float32_ceil___boxed(lean_object* v_a_00___x40___internal___hyg_344_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_345_; float v_res_346_; lean_object* v_r_347_; 
v_a_00___x40___internal___hyg_1__boxed_345_ = lean_unbox_float32(v_a_00___x40___internal___hyg_344_);
lean_dec_ref(v_a_00___x40___internal___hyg_344_);
v_res_346_ = ceilf(v_a_00___x40___internal___hyg_1__boxed_345_);
v_r_347_ = lean_box_float32(v_res_346_);
return v_r_347_;
}
}
LEAN_EXPORT lean_object* l_Float32_floor___boxed(lean_object* v_a_00___x40___internal___hyg_349_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_350_; float v_res_351_; lean_object* v_r_352_; 
v_a_00___x40___internal___hyg_1__boxed_350_ = lean_unbox_float32(v_a_00___x40___internal___hyg_349_);
lean_dec_ref(v_a_00___x40___internal___hyg_349_);
v_res_351_ = floorf(v_a_00___x40___internal___hyg_1__boxed_350_);
v_r_352_ = lean_box_float32(v_res_351_);
return v_r_352_;
}
}
LEAN_EXPORT lean_object* l_Float32_round___boxed(lean_object* v_a_00___x40___internal___hyg_354_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_355_; float v_res_356_; lean_object* v_r_357_; 
v_a_00___x40___internal___hyg_1__boxed_355_ = lean_unbox_float32(v_a_00___x40___internal___hyg_354_);
lean_dec_ref(v_a_00___x40___internal___hyg_354_);
v_res_356_ = roundf(v_a_00___x40___internal___hyg_1__boxed_355_);
v_r_357_ = lean_box_float32(v_res_356_);
return v_r_357_;
}
}
LEAN_EXPORT lean_object* l_Float32_abs___boxed(lean_object* v_a_00___x40___internal___hyg_359_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_360_; float v_res_361_; lean_object* v_r_362_; 
v_a_00___x40___internal___hyg_1__boxed_360_ = lean_unbox_float32(v_a_00___x40___internal___hyg_359_);
lean_dec_ref(v_a_00___x40___internal___hyg_359_);
v_res_361_ = fabsf(v_a_00___x40___internal___hyg_1__boxed_360_);
v_r_362_ = lean_box_float32(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT float l_instMinFloat32___lam__0(float v_x_365_, float v_y_366_){
_start:
{
uint8_t v___x_367_; 
v___x_367_ = lean_float32_decLe(v_x_365_, v_y_366_);
if (v___x_367_ == 0)
{
return v_y_366_;
}
else
{
return v_x_365_;
}
}
}
LEAN_EXPORT lean_object* l_instMinFloat32___lam__0___boxed(lean_object* v_x_368_, lean_object* v_y_369_){
_start:
{
float v_x_boxed_370_; float v_y_boxed_371_; float v_res_372_; lean_object* v_r_373_; 
v_x_boxed_370_ = lean_unbox_float32(v_x_368_);
lean_dec_ref(v_x_368_);
v_y_boxed_371_ = lean_unbox_float32(v_y_369_);
lean_dec_ref(v_y_369_);
v_res_372_ = l_instMinFloat32___lam__0(v_x_boxed_370_, v_y_boxed_371_);
v_r_373_ = lean_box_float32(v_res_372_);
return v_r_373_;
}
}
LEAN_EXPORT float l_instMaxFloat32___lam__0(float v_x_376_, float v_y_377_){
_start:
{
uint8_t v___x_378_; 
v___x_378_ = lean_float32_decLe(v_x_376_, v_y_377_);
if (v___x_378_ == 0)
{
return v_x_376_;
}
else
{
return v_y_377_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxFloat32___lam__0___boxed(lean_object* v_x_379_, lean_object* v_y_380_){
_start:
{
float v_x_boxed_381_; float v_y_boxed_382_; float v_res_383_; lean_object* v_r_384_; 
v_x_boxed_381_ = lean_unbox_float32(v_x_379_);
lean_dec_ref(v_x_379_);
v_y_boxed_382_ = lean_unbox_float32(v_y_380_);
lean_dec_ref(v_y_380_);
v_res_383_ = l_instMaxFloat32___lam__0(v_x_boxed_381_, v_y_boxed_382_);
v_r_384_ = lean_box_float32(v_res_383_);
return v_r_384_;
}
}
LEAN_EXPORT lean_object* l_Float32_scaleB___boxed(lean_object* v_x_389_, lean_object* v_i_390_){
_start:
{
float v_x_boxed_391_; float v_res_392_; lean_object* v_r_393_; 
v_x_boxed_391_ = lean_unbox_float32(v_x_389_);
lean_dec_ref(v_x_389_);
v_res_392_ = lean_float32_scaleb(v_x_boxed_391_, v_i_390_);
lean_dec(v_i_390_);
v_r_393_ = lean_box_float32(v_res_392_);
return v_r_393_;
}
}
LEAN_EXPORT lean_object* l_Float32_toFloat___boxed(lean_object* v_a_00___x40___internal___hyg_395_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_396_; double v_res_397_; lean_object* v_r_398_; 
v_a_00___x40___internal___hyg_1__boxed_396_ = lean_unbox_float32(v_a_00___x40___internal___hyg_395_);
lean_dec_ref(v_a_00___x40___internal___hyg_395_);
v_res_397_ = lean_float32_to_float(v_a_00___x40___internal___hyg_1__boxed_396_);
v_r_398_ = lean_box_float(v_res_397_);
return v_r_398_;
}
}
LEAN_EXPORT lean_object* l_Float_toFloat32___boxed(lean_object* v_a_00___x40___internal___hyg_400_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_401_; float v_res_402_; lean_object* v_r_403_; 
v_a_00___x40___internal___hyg_1__boxed_401_ = lean_unbox_float(v_a_00___x40___internal___hyg_400_);
lean_dec_ref(v_a_00___x40___internal___hyg_400_);
v_res_402_ = lean_float_to_float32(v_a_00___x40___internal___hyg_1__boxed_401_);
v_r_403_ = lean_box_float32(v_res_402_);
return v_r_403_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Float(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Float_Model_Float32(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Float32(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Float_Float(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Model_Float32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Float32_nan = _init_l_Float32_nan();
l_Float32_inf = _init_l_Float32_inf();
l_instLTFloat32 = _init_l_instLTFloat32();
lean_mark_persistent(l_instLTFloat32);
l_instLEFloat32 = _init_l_instLEFloat32();
lean_mark_persistent(l_instLEFloat32);
l_instInhabitedFloat32 = _init_l_instInhabitedFloat32();
l_instReprAtomFloat32 = _init_l_instReprAtomFloat32();
lean_mark_persistent(l_instReprAtomFloat32);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Float_Float32(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Float_Float(uint8_t builtin);
lean_object* initialize_Init_Data_Float_Model_Float32(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Float_Float32(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float_Float(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Float_Model_Float32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Float32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Float_Float32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Float_Float32(builtin);
}
#ifdef __cplusplus
}
#endif
