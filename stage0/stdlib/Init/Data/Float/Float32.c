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
float fmaf(float, float, float);
LEAN_EXPORT lean_object* l_Float32_fma___boxed(lean_object*, lean_object*, lean_object*);
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
float lean_float32_minimum(float, float);
LEAN_EXPORT lean_object* l_Float32_minimum___boxed(lean_object*, lean_object*);
float lean_float32_minimum_number(float, float);
LEAN_EXPORT lean_object* l_Float32_minimumNumber___boxed(lean_object*, lean_object*);
float lean_float32_maximum(float, float);
LEAN_EXPORT lean_object* l_Float32_maximum___boxed(lean_object*, lean_object*);
float lean_float32_maximum_number(float, float);
LEAN_EXPORT lean_object* l_Float32_maximumNumber___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instMinFloat32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float32_minimum___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMinFloat32___closed__0 = (const lean_object*)&l_instMinFloat32___closed__0_value;
LEAN_EXPORT const lean_object* l_instMinFloat32 = (const lean_object*)&l_instMinFloat32___closed__0_value;
static const lean_closure_object l_instMaxFloat32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float32_maximum___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMaxFloat32___closed__0 = (const lean_object*)&l_instMaxFloat32___closed__0_value;
LEAN_EXPORT const lean_object* l_instMaxFloat32 = (const lean_object*)&l_instMaxFloat32___closed__0_value;
float lean_float32_scaleb(float, lean_object*);
LEAN_EXPORT lean_object* l_Float32_scaleB___boxed(lean_object*, lean_object*);
double lean_float32_to_float(float);
LEAN_EXPORT lean_object* l_Float32_toFloat___boxed(lean_object*);
float lean_float_to_float32(double);
LEAN_EXPORT lean_object* l_Float_toFloat32___boxed(lean_object*);
LEAN_EXPORT void l_Float32_toModel_0interp(lean_interpreter_value* stack)
{
float v_self_1_ = stack[0].m_float32;
uint32_t v_res_2_;
v_res_2_ = lean_float32_to_bits(v_self_1_);
stack->m_num = v_res_2_;
}
LEAN_EXPORT lean_object* l_Float32_toModel___boxed(lean_object* v_self_3_){
_start:
{
float v_self_boxed_4_; uint32_t v_res_5_; lean_object* v_r_6_; 
v_self_boxed_4_ = lean_unbox_float32(v_self_3_);
lean_dec_ref(v_self_3_);
v_res_5_ = lean_float32_to_bits(v_self_boxed_4_);
v_r_6_ = lean_box_uint32(v_res_5_);
return v_r_6_;
}
}
LEAN_EXPORT void l_Float32_ofModel_0interp(lean_interpreter_value* stack)
{
uint32_t v_toModel_7_ = stack[0].m_num;
float v_res_8_;
v_res_8_ = lean_float32_of_bits(v_toModel_7_);
stack->m_float32
 = v_res_8_;
}
LEAN_EXPORT lean_object* l_Float32_ofModel___boxed(lean_object* v_toModel_9_){
_start:
{
uint32_t v_toModel_boxed_10_; float v_res_11_; lean_object* v_r_12_; 
v_toModel_boxed_10_ = lean_unbox_uint32(v_toModel_9_);
lean_dec(v_toModel_9_);
v_res_11_ = lean_float32_of_bits(v_toModel_boxed_10_);
v_r_12_ = lean_box_float32(v_res_11_);
return v_r_12_;
}
}
uint8_t l_instDecidableEqFloat32_decEq(float v_x_13_, float v_x_14_){
_start:
{
uint32_t v_toModel_15_; uint32_t v_toModel_16_; uint8_t v___x_17_; 
v_toModel_15_ = lean_float32_to_bits(v_x_13_);
v_toModel_16_ = lean_float32_to_bits(v_x_14_);
v___x_17_ = lean_uint32_dec_eq(v_toModel_15_, v_toModel_16_);
return v___x_17_;
}
}
LEAN_EXPORT void l_instDecidableEqFloat32_decEq_0interp(lean_interpreter_value* stack)
{
float v_x_13_ = stack[0].m_float32;
float v_x_14_ = stack[1].m_float32;
uint8_t v_res_18_;
v_res_18_ = l_instDecidableEqFloat32_decEq(v_x_13_, v_x_14_);
stack->m_num = v_res_18_;
}
LEAN_EXPORT lean_object* l_instDecidableEqFloat32_decEq___boxed(lean_object* v_x_19_, lean_object* v_x_20_){
_start:
{
float v_x_31__boxed_21_; float v_x_32__boxed_22_; uint8_t v_res_23_; lean_object* v_r_24_; 
v_x_31__boxed_21_ = lean_unbox_float32(v_x_19_);
lean_dec_ref(v_x_19_);
v_x_32__boxed_22_ = lean_unbox_float32(v_x_20_);
lean_dec_ref(v_x_20_);
v_res_23_ = l_instDecidableEqFloat32_decEq(v_x_31__boxed_21_, v_x_32__boxed_22_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
uint8_t l_instDecidableEqFloat32(float v_x_25_, float v_x_26_){
_start:
{
uint8_t v___x_27_; 
v___x_27_ = l_instDecidableEqFloat32_decEq(v_x_25_, v_x_26_);
return v___x_27_;
}
}
LEAN_EXPORT void l_instDecidableEqFloat32_0interp(lean_interpreter_value* stack)
{
float v_x_25_ = stack[0].m_float32;
float v_x_26_ = stack[1].m_float32;
uint8_t v_res_28_;
v_res_28_ = l_instDecidableEqFloat32(v_x_25_, v_x_26_);
stack->m_num = v_res_28_;
}
LEAN_EXPORT lean_object* l_instDecidableEqFloat32___boxed(lean_object* v_x_29_, lean_object* v_x_30_){
_start:
{
float v_x_5__boxed_31_; float v_x_6__boxed_32_; uint8_t v_res_33_; lean_object* v_r_34_; 
v_x_5__boxed_31_ = lean_unbox_float32(v_x_29_);
lean_dec_ref(v_x_29_);
v_x_6__boxed_32_ = lean_unbox_float32(v_x_30_);
lean_dec_ref(v_x_30_);
v_res_33_ = l_instDecidableEqFloat32(v_x_5__boxed_31_, v_x_6__boxed_32_);
v_r_34_ = lean_box(v_res_33_);
return v_r_34_;
}
}
static float _init_l_Float32_nan___closed__0(void){
_start:
{
uint32_t v___x_35_; float v___x_36_; 
v___x_35_ = l_Float32_Model_nan;
v___x_36_ = lean_float32_of_bits(v___x_35_);
return v___x_36_;
}
}
static float _init_l_Float32_nan(void){
_start:
{
float v___x_37_; 
v___x_37_ = lean_float32_once(&l_Float32_nan___closed__0, &l_Float32_nan___closed__0_once, _init_l_Float32_nan___closed__0);
return v___x_37_;
}
}
static float _init_l_Float32_inf___closed__0(void){
_start:
{
uint32_t v___x_38_; float v___x_39_; 
v___x_38_ = l_Float32_Model_inf;
v___x_39_ = lean_float32_of_bits(v___x_38_);
return v___x_39_;
}
}
static float _init_l_Float32_inf(void){
_start:
{
float v___x_40_; 
v___x_40_ = lean_float32_once(&l_Float32_inf___closed__0, &l_Float32_inf___closed__0_once, _init_l_Float32_inf___closed__0);
return v___x_40_;
}
}
LEAN_EXPORT void l_Float32_add_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_41_ = stack[0].m_float32;
float v_a_00___x40___internal___hyg_42_ = stack[1].m_float32;
float v_res_43_;
v_res_43_ = lean_float32_add(v_a_00___x40___internal___hyg_41_, v_a_00___x40___internal___hyg_42_);
stack->m_float32
 = v_res_43_;
}
LEAN_EXPORT lean_object* l_Float32_add___boxed(lean_object* v_a_00___x40___internal___hyg_44_, lean_object* v_a_00___x40___internal___hyg_45_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_46_; float v_a_00___x40___internal___hyg_2__boxed_47_; float v_res_48_; lean_object* v_r_49_; 
v_a_00___x40___internal___hyg_1__boxed_46_ = lean_unbox_float32(v_a_00___x40___internal___hyg_44_);
lean_dec_ref(v_a_00___x40___internal___hyg_44_);
v_a_00___x40___internal___hyg_2__boxed_47_ = lean_unbox_float32(v_a_00___x40___internal___hyg_45_);
lean_dec_ref(v_a_00___x40___internal___hyg_45_);
v_res_48_ = lean_float32_add(v_a_00___x40___internal___hyg_1__boxed_46_, v_a_00___x40___internal___hyg_2__boxed_47_);
v_r_49_ = lean_box_float32(v_res_48_);
return v_r_49_;
}
}
LEAN_EXPORT void l_Float32_sub_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_50_ = stack[0].m_float32;
float v_a_00___x40___internal___hyg_51_ = stack[1].m_float32;
float v_res_52_;
v_res_52_ = lean_float32_sub(v_a_00___x40___internal___hyg_50_, v_a_00___x40___internal___hyg_51_);
stack->m_float32
 = v_res_52_;
}
LEAN_EXPORT lean_object* l_Float32_sub___boxed(lean_object* v_a_00___x40___internal___hyg_53_, lean_object* v_a_00___x40___internal___hyg_54_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_55_; float v_a_00___x40___internal___hyg_2__boxed_56_; float v_res_57_; lean_object* v_r_58_; 
v_a_00___x40___internal___hyg_1__boxed_55_ = lean_unbox_float32(v_a_00___x40___internal___hyg_53_);
lean_dec_ref(v_a_00___x40___internal___hyg_53_);
v_a_00___x40___internal___hyg_2__boxed_56_ = lean_unbox_float32(v_a_00___x40___internal___hyg_54_);
lean_dec_ref(v_a_00___x40___internal___hyg_54_);
v_res_57_ = lean_float32_sub(v_a_00___x40___internal___hyg_1__boxed_55_, v_a_00___x40___internal___hyg_2__boxed_56_);
v_r_58_ = lean_box_float32(v_res_57_);
return v_r_58_;
}
}
LEAN_EXPORT void l_Float32_mul_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_59_ = stack[0].m_float32;
float v_a_00___x40___internal___hyg_60_ = stack[1].m_float32;
float v_res_61_;
v_res_61_ = lean_float32_mul(v_a_00___x40___internal___hyg_59_, v_a_00___x40___internal___hyg_60_);
stack->m_float32
 = v_res_61_;
}
LEAN_EXPORT lean_object* l_Float32_mul___boxed(lean_object* v_a_00___x40___internal___hyg_62_, lean_object* v_a_00___x40___internal___hyg_63_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_64_; float v_a_00___x40___internal___hyg_2__boxed_65_; float v_res_66_; lean_object* v_r_67_; 
v_a_00___x40___internal___hyg_1__boxed_64_ = lean_unbox_float32(v_a_00___x40___internal___hyg_62_);
lean_dec_ref(v_a_00___x40___internal___hyg_62_);
v_a_00___x40___internal___hyg_2__boxed_65_ = lean_unbox_float32(v_a_00___x40___internal___hyg_63_);
lean_dec_ref(v_a_00___x40___internal___hyg_63_);
v_res_66_ = lean_float32_mul(v_a_00___x40___internal___hyg_1__boxed_64_, v_a_00___x40___internal___hyg_2__boxed_65_);
v_r_67_ = lean_box_float32(v_res_66_);
return v_r_67_;
}
}
LEAN_EXPORT void l_Float32_div_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_68_ = stack[0].m_float32;
float v_a_00___x40___internal___hyg_69_ = stack[1].m_float32;
float v_res_70_;
v_res_70_ = lean_float32_div(v_a_00___x40___internal___hyg_68_, v_a_00___x40___internal___hyg_69_);
stack->m_float32
 = v_res_70_;
}
LEAN_EXPORT lean_object* l_Float32_div___boxed(lean_object* v_a_00___x40___internal___hyg_71_, lean_object* v_a_00___x40___internal___hyg_72_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_73_; float v_a_00___x40___internal___hyg_2__boxed_74_; float v_res_75_; lean_object* v_r_76_; 
v_a_00___x40___internal___hyg_1__boxed_73_ = lean_unbox_float32(v_a_00___x40___internal___hyg_71_);
lean_dec_ref(v_a_00___x40___internal___hyg_71_);
v_a_00___x40___internal___hyg_2__boxed_74_ = lean_unbox_float32(v_a_00___x40___internal___hyg_72_);
lean_dec_ref(v_a_00___x40___internal___hyg_72_);
v_res_75_ = lean_float32_div(v_a_00___x40___internal___hyg_1__boxed_73_, v_a_00___x40___internal___hyg_2__boxed_74_);
v_r_76_ = lean_box_float32(v_res_75_);
return v_r_76_;
}
}
LEAN_EXPORT void l_Float32_neg_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_77_ = stack[0].m_float32;
float v_res_78_;
v_res_78_ = lean_float32_negate(v_a_00___x40___internal___hyg_77_);
stack->m_float32
 = v_res_78_;
}
LEAN_EXPORT lean_object* l_Float32_neg___boxed(lean_object* v_a_00___x40___internal___hyg_79_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_80_; float v_res_81_; lean_object* v_r_82_; 
v_a_00___x40___internal___hyg_1__boxed_80_ = lean_unbox_float32(v_a_00___x40___internal___hyg_79_);
lean_dec_ref(v_a_00___x40___internal___hyg_79_);
v_res_81_ = lean_float32_negate(v_a_00___x40___internal___hyg_1__boxed_80_);
v_r_82_ = lean_box_float32(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT void l_Float32_lt_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_83_ = stack[0].m_float32;
float v_a_00___x40___internal___hyg_84_ = stack[1].m_float32;
uint8_t v_res_85_;
v_res_85_ = lean_float32_decLt(v_a_00___x40___internal___hyg_83_, v_a_00___x40___internal___hyg_84_);
stack->m_num = v_res_85_;
}
LEAN_EXPORT lean_object* l_Float32_lt___boxed(lean_object* v_a_00___x40___internal___hyg_86_, lean_object* v_a_00___x40___internal___hyg_87_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_88_; float v_a_00___x40___internal___hyg_2__boxed_89_; uint8_t v_res_90_; lean_object* v_r_91_; 
v_a_00___x40___internal___hyg_1__boxed_88_ = lean_unbox_float32(v_a_00___x40___internal___hyg_86_);
lean_dec_ref(v_a_00___x40___internal___hyg_86_);
v_a_00___x40___internal___hyg_2__boxed_89_ = lean_unbox_float32(v_a_00___x40___internal___hyg_87_);
lean_dec_ref(v_a_00___x40___internal___hyg_87_);
v_res_90_ = lean_float32_decLt(v_a_00___x40___internal___hyg_1__boxed_88_, v_a_00___x40___internal___hyg_2__boxed_89_);
v_r_91_ = lean_box(v_res_90_);
return v_r_91_;
}
}
LEAN_EXPORT void l_Float32_le_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_92_ = stack[0].m_float32;
float v_a_00___x40___internal___hyg_93_ = stack[1].m_float32;
uint8_t v_res_94_;
v_res_94_ = lean_float32_decLe(v_a_00___x40___internal___hyg_92_, v_a_00___x40___internal___hyg_93_);
stack->m_num = v_res_94_;
}
LEAN_EXPORT lean_object* l_Float32_le___boxed(lean_object* v_a_00___x40___internal___hyg_95_, lean_object* v_a_00___x40___internal___hyg_96_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_97_; float v_a_00___x40___internal___hyg_2__boxed_98_; uint8_t v_res_99_; lean_object* v_r_100_; 
v_a_00___x40___internal___hyg_1__boxed_97_ = lean_unbox_float32(v_a_00___x40___internal___hyg_95_);
lean_dec_ref(v_a_00___x40___internal___hyg_95_);
v_a_00___x40___internal___hyg_2__boxed_98_ = lean_unbox_float32(v_a_00___x40___internal___hyg_96_);
lean_dec_ref(v_a_00___x40___internal___hyg_96_);
v_res_99_ = lean_float32_decLe(v_a_00___x40___internal___hyg_1__boxed_97_, v_a_00___x40___internal___hyg_2__boxed_98_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
LEAN_EXPORT void l_Float32_ofBits_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_00___x40___internal___hyg_101_ = stack[0].m_num;
float v_res_102_;
v_res_102_ = lean_float32_of_bits(v_a_00___x40___internal___hyg_101_);
stack->m_float32
 = v_res_102_;
}
LEAN_EXPORT lean_object* l_Float32_ofBits___boxed(lean_object* v_a_00___x40___internal___hyg_103_){
_start:
{
uint32_t v_a_00___x40___internal___hyg_1__boxed_104_; float v_res_105_; lean_object* v_r_106_; 
v_a_00___x40___internal___hyg_1__boxed_104_ = lean_unbox_uint32(v_a_00___x40___internal___hyg_103_);
lean_dec(v_a_00___x40___internal___hyg_103_);
v_res_105_ = lean_float32_of_bits(v_a_00___x40___internal___hyg_1__boxed_104_);
v_r_106_ = lean_box_float32(v_res_105_);
return v_r_106_;
}
}
LEAN_EXPORT void l_Float32_toBits_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_107_ = stack[0].m_float32;
uint32_t v_res_108_;
v_res_108_ = lean_float32_to_bits(v_a_00___x40___internal___hyg_107_);
stack->m_num = v_res_108_;
}
LEAN_EXPORT lean_object* l_Float32_toBits___boxed(lean_object* v_a_00___x40___internal___hyg_109_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_110_; uint32_t v_res_111_; lean_object* v_r_112_; 
v_a_00___x40___internal___hyg_1__boxed_110_ = lean_unbox_float32(v_a_00___x40___internal___hyg_109_);
lean_dec_ref(v_a_00___x40___internal___hyg_109_);
v_res_111_ = lean_float32_to_bits(v_a_00___x40___internal___hyg_1__boxed_110_);
v_r_112_ = lean_box_uint32(v_res_111_);
return v_r_112_;
}
}
static lean_object* _init_l_instLTFloat32(void){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = lean_box(0);
return v___x_123_;
}
}
static lean_object* _init_l_instLEFloat32(void){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = lean_box(0);
return v___x_124_;
}
}
LEAN_EXPORT void l_Float32_beq_0interp(lean_interpreter_value* stack)
{
float v_a_125_ = stack[0].m_float32;
float v_b_126_ = stack[1].m_float32;
uint8_t v_res_127_;
v_res_127_ = lean_float32_beq(v_a_125_, v_b_126_);
stack->m_num = v_res_127_;
}
LEAN_EXPORT lean_object* l_Float32_beq___boxed(lean_object* v_a_128_, lean_object* v_b_129_){
_start:
{
float v_a_boxed_130_; float v_b_boxed_131_; uint8_t v_res_132_; lean_object* v_r_133_; 
v_a_boxed_130_ = lean_unbox_float32(v_a_128_);
lean_dec_ref(v_a_128_);
v_b_boxed_131_ = lean_unbox_float32(v_b_129_);
lean_dec_ref(v_b_129_);
v_res_132_ = lean_float32_beq(v_a_boxed_130_, v_b_boxed_131_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT void l_Float32_decLt_0interp(lean_interpreter_value* stack)
{
float v_a_136_ = stack[0].m_float32;
float v_b_137_ = stack[1].m_float32;
uint8_t v_res_138_;
v_res_138_ = lean_float32_decLt(v_a_136_, v_b_137_);
stack->m_num = v_res_138_;
}
LEAN_EXPORT lean_object* l_Float32_decLt___boxed(lean_object* v_a_139_, lean_object* v_b_140_){
_start:
{
float v_a_boxed_141_; float v_b_boxed_142_; uint8_t v_res_143_; lean_object* v_r_144_; 
v_a_boxed_141_ = lean_unbox_float32(v_a_139_);
lean_dec_ref(v_a_139_);
v_b_boxed_142_ = lean_unbox_float32(v_b_140_);
lean_dec_ref(v_b_140_);
v_res_143_ = lean_float32_decLt(v_a_boxed_141_, v_b_boxed_142_);
v_r_144_ = lean_box(v_res_143_);
return v_r_144_;
}
}
LEAN_EXPORT void l_Float32_decLe_0interp(lean_interpreter_value* stack)
{
float v_a_145_ = stack[0].m_float32;
float v_b_146_ = stack[1].m_float32;
uint8_t v_res_147_;
v_res_147_ = lean_float32_decLe(v_a_145_, v_b_146_);
stack->m_num = v_res_147_;
}
LEAN_EXPORT lean_object* l_Float32_decLe___boxed(lean_object* v_a_148_, lean_object* v_b_149_){
_start:
{
float v_a_boxed_150_; float v_b_boxed_151_; uint8_t v_res_152_; lean_object* v_r_153_; 
v_a_boxed_150_ = lean_unbox_float32(v_a_148_);
lean_dec_ref(v_a_148_);
v_b_boxed_151_ = lean_unbox_float32(v_b_149_);
lean_dec_ref(v_b_149_);
v_res_152_ = lean_float32_decLe(v_a_boxed_150_, v_b_boxed_151_);
v_r_153_ = lean_box(v_res_152_);
return v_r_153_;
}
}
LEAN_EXPORT void l_Float32_toString_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_154_ = stack[0].m_float32;
lean_object* v_res_155_;
v_res_155_ = lean_float32_to_string(v_a_00___x40___internal___hyg_154_);
stack->m_obj
 = v_res_155_;
}
LEAN_EXPORT lean_object* l_Float32_toString___boxed(lean_object* v_a_00___x40___internal___hyg_156_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_157_; lean_object* v_res_158_; 
v_a_00___x40___internal___hyg_1__boxed_157_ = lean_unbox_float32(v_a_00___x40___internal___hyg_156_);
lean_dec_ref(v_a_00___x40___internal___hyg_156_);
v_res_158_ = lean_float32_to_string(v_a_00___x40___internal___hyg_1__boxed_157_);
return v_res_158_;
}
}
LEAN_EXPORT void l_Float32_toUInt8_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_159_ = stack[0].m_float32;
uint8_t v_res_160_;
v_res_160_ = lean_float32_to_uint8(v_a_00___x40___internal___hyg_159_);
stack->m_num = v_res_160_;
}
LEAN_EXPORT lean_object* l_Float32_toUInt8___boxed(lean_object* v_a_00___x40___internal___hyg_161_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_162_; uint8_t v_res_163_; lean_object* v_r_164_; 
v_a_00___x40___internal___hyg_1__boxed_162_ = lean_unbox_float32(v_a_00___x40___internal___hyg_161_);
lean_dec_ref(v_a_00___x40___internal___hyg_161_);
v_res_163_ = lean_float32_to_uint8(v_a_00___x40___internal___hyg_1__boxed_162_);
v_r_164_ = lean_box(v_res_163_);
return v_r_164_;
}
}
LEAN_EXPORT void l_Float32_toUInt16_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_165_ = stack[0].m_float32;
uint16_t v_res_166_;
v_res_166_ = lean_float32_to_uint16(v_a_00___x40___internal___hyg_165_);
stack->m_num = v_res_166_;
}
LEAN_EXPORT lean_object* l_Float32_toUInt16___boxed(lean_object* v_a_00___x40___internal___hyg_167_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_168_; uint16_t v_res_169_; lean_object* v_r_170_; 
v_a_00___x40___internal___hyg_1__boxed_168_ = lean_unbox_float32(v_a_00___x40___internal___hyg_167_);
lean_dec_ref(v_a_00___x40___internal___hyg_167_);
v_res_169_ = lean_float32_to_uint16(v_a_00___x40___internal___hyg_1__boxed_168_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
LEAN_EXPORT void l_Float32_toUInt32_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_171_ = stack[0].m_float32;
uint32_t v_res_172_;
v_res_172_ = lean_float32_to_uint32(v_a_00___x40___internal___hyg_171_);
stack->m_num = v_res_172_;
}
LEAN_EXPORT lean_object* l_Float32_toUInt32___boxed(lean_object* v_a_00___x40___internal___hyg_173_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_174_; uint32_t v_res_175_; lean_object* v_r_176_; 
v_a_00___x40___internal___hyg_1__boxed_174_ = lean_unbox_float32(v_a_00___x40___internal___hyg_173_);
lean_dec_ref(v_a_00___x40___internal___hyg_173_);
v_res_175_ = lean_float32_to_uint32(v_a_00___x40___internal___hyg_1__boxed_174_);
v_r_176_ = lean_box_uint32(v_res_175_);
return v_r_176_;
}
}
LEAN_EXPORT void l_Float32_toUInt64_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_177_ = stack[0].m_float32;
uint64_t v_res_178_;
v_res_178_ = lean_float32_to_uint64(v_a_00___x40___internal___hyg_177_);
stack->m_num = v_res_178_;
}
LEAN_EXPORT lean_object* l_Float32_toUInt64___boxed(lean_object* v_a_00___x40___internal___hyg_179_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_180_; uint64_t v_res_181_; lean_object* v_r_182_; 
v_a_00___x40___internal___hyg_1__boxed_180_ = lean_unbox_float32(v_a_00___x40___internal___hyg_179_);
lean_dec_ref(v_a_00___x40___internal___hyg_179_);
v_res_181_ = lean_float32_to_uint64(v_a_00___x40___internal___hyg_1__boxed_180_);
v_r_182_ = lean_box_uint64(v_res_181_);
return v_r_182_;
}
}
LEAN_EXPORT void l_Float32_toUSize_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_183_ = stack[0].m_float32;
size_t v_res_184_;
v_res_184_ = lean_float32_to_usize(v_a_00___x40___internal___hyg_183_);
stack->m_num = v_res_184_;
}
LEAN_EXPORT lean_object* l_Float32_toUSize___boxed(lean_object* v_a_00___x40___internal___hyg_185_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_186_; size_t v_res_187_; lean_object* v_r_188_; 
v_a_00___x40___internal___hyg_1__boxed_186_ = lean_unbox_float32(v_a_00___x40___internal___hyg_185_);
lean_dec_ref(v_a_00___x40___internal___hyg_185_);
v_res_187_ = lean_float32_to_usize(v_a_00___x40___internal___hyg_1__boxed_186_);
v_r_188_ = lean_box_usize(v_res_187_);
return v_r_188_;
}
}
LEAN_EXPORT void l_Float32_isNaN_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_189_ = stack[0].m_float32;
uint8_t v_res_190_;
v_res_190_ = lean_float32_isnan(v_a_00___x40___internal___hyg_189_);
stack->m_num = v_res_190_;
}
LEAN_EXPORT lean_object* l_Float32_isNaN___boxed(lean_object* v_a_00___x40___internal___hyg_191_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_192_; uint8_t v_res_193_; lean_object* v_r_194_; 
v_a_00___x40___internal___hyg_1__boxed_192_ = lean_unbox_float32(v_a_00___x40___internal___hyg_191_);
lean_dec_ref(v_a_00___x40___internal___hyg_191_);
v_res_193_ = lean_float32_isnan(v_a_00___x40___internal___hyg_1__boxed_192_);
v_r_194_ = lean_box(v_res_193_);
return v_r_194_;
}
}
LEAN_EXPORT void l_Float32_isFinite_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_195_ = stack[0].m_float32;
uint8_t v_res_196_;
v_res_196_ = lean_float32_isfinite(v_a_00___x40___internal___hyg_195_);
stack->m_num = v_res_196_;
}
LEAN_EXPORT lean_object* l_Float32_isFinite___boxed(lean_object* v_a_00___x40___internal___hyg_197_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_198_; uint8_t v_res_199_; lean_object* v_r_200_; 
v_a_00___x40___internal___hyg_1__boxed_198_ = lean_unbox_float32(v_a_00___x40___internal___hyg_197_);
lean_dec_ref(v_a_00___x40___internal___hyg_197_);
v_res_199_ = lean_float32_isfinite(v_a_00___x40___internal___hyg_1__boxed_198_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
LEAN_EXPORT void l_Float32_isInf_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_201_ = stack[0].m_float32;
uint8_t v_res_202_;
v_res_202_ = lean_float32_isinf(v_a_00___x40___internal___hyg_201_);
stack->m_num = v_res_202_;
}
LEAN_EXPORT lean_object* l_Float32_isInf___boxed(lean_object* v_a_00___x40___internal___hyg_203_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_204_; uint8_t v_res_205_; lean_object* v_r_206_; 
v_a_00___x40___internal___hyg_1__boxed_204_ = lean_unbox_float32(v_a_00___x40___internal___hyg_203_);
lean_dec_ref(v_a_00___x40___internal___hyg_203_);
v_res_205_ = lean_float32_isinf(v_a_00___x40___internal___hyg_1__boxed_204_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT void l_Float32_frExp_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_207_ = stack[0].m_float32;
lean_object* v_res_208_;
v_res_208_ = lean_float32_frexp(v_a_00___x40___internal___hyg_207_);
stack->m_obj
 = v_res_208_;
}
LEAN_EXPORT lean_object* l_Float32_frExp___boxed(lean_object* v_a_00___x40___internal___hyg_209_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_210_; lean_object* v_res_211_; 
v_a_00___x40___internal___hyg_1__boxed_210_ = lean_unbox_float32(v_a_00___x40___internal___hyg_209_);
lean_dec_ref(v_a_00___x40___internal___hyg_209_);
v_res_211_ = lean_float32_frexp(v_a_00___x40___internal___hyg_1__boxed_210_);
return v_res_211_;
}
}
LEAN_EXPORT void l_UInt8_toFloat32_0interp(lean_interpreter_value* stack)
{
uint8_t v_n_214_ = stack[0].m_num;
float v_res_215_;
v_res_215_ = lean_uint8_to_float32(v_n_214_);
stack->m_float32
 = v_res_215_;
}
LEAN_EXPORT lean_object* l_UInt8_toFloat32___boxed(lean_object* v_n_216_){
_start:
{
uint8_t v_n_boxed_217_; float v_res_218_; lean_object* v_r_219_; 
v_n_boxed_217_ = lean_unbox(v_n_216_);
v_res_218_ = lean_uint8_to_float32(v_n_boxed_217_);
v_r_219_ = lean_box_float32(v_res_218_);
return v_r_219_;
}
}
LEAN_EXPORT void l_UInt16_toFloat32_0interp(lean_interpreter_value* stack)
{
uint16_t v_n_220_ = stack[0].m_num;
float v_res_221_;
v_res_221_ = lean_uint16_to_float32(v_n_220_);
stack->m_float32
 = v_res_221_;
}
LEAN_EXPORT lean_object* l_UInt16_toFloat32___boxed(lean_object* v_n_222_){
_start:
{
uint16_t v_n_boxed_223_; float v_res_224_; lean_object* v_r_225_; 
v_n_boxed_223_ = lean_unbox(v_n_222_);
v_res_224_ = lean_uint16_to_float32(v_n_boxed_223_);
v_r_225_ = lean_box_float32(v_res_224_);
return v_r_225_;
}
}
LEAN_EXPORT void l_UInt32_toFloat32_0interp(lean_interpreter_value* stack)
{
uint32_t v_n_226_ = stack[0].m_num;
float v_res_227_;
v_res_227_ = lean_uint32_to_float32(v_n_226_);
stack->m_float32
 = v_res_227_;
}
LEAN_EXPORT lean_object* l_UInt32_toFloat32___boxed(lean_object* v_n_228_){
_start:
{
uint32_t v_n_boxed_229_; float v_res_230_; lean_object* v_r_231_; 
v_n_boxed_229_ = lean_unbox_uint32(v_n_228_);
lean_dec(v_n_228_);
v_res_230_ = lean_uint32_to_float32(v_n_boxed_229_);
v_r_231_ = lean_box_float32(v_res_230_);
return v_r_231_;
}
}
LEAN_EXPORT void l_UInt64_toFloat32_0interp(lean_interpreter_value* stack)
{
uint64_t v_n_232_ = stack[0].m_num;
float v_res_233_;
v_res_233_ = lean_uint64_to_float32(v_n_232_);
stack->m_float32
 = v_res_233_;
}
LEAN_EXPORT lean_object* l_UInt64_toFloat32___boxed(lean_object* v_n_234_){
_start:
{
uint64_t v_n_boxed_235_; float v_res_236_; lean_object* v_r_237_; 
v_n_boxed_235_ = lean_unbox_uint64(v_n_234_);
lean_dec_ref(v_n_234_);
v_res_236_ = lean_uint64_to_float32(v_n_boxed_235_);
v_r_237_ = lean_box_float32(v_res_236_);
return v_r_237_;
}
}
LEAN_EXPORT void l_USize_toFloat32_0interp(lean_interpreter_value* stack)
{
size_t v_n_238_ = stack[0].m_num;
float v_res_239_;
v_res_239_ = lean_usize_to_float32(v_n_238_);
stack->m_float32
 = v_res_239_;
}
LEAN_EXPORT lean_object* l_USize_toFloat32___boxed(lean_object* v_n_240_){
_start:
{
size_t v_n_boxed_241_; float v_res_242_; lean_object* v_r_243_; 
v_n_boxed_241_ = lean_unbox_usize(v_n_240_);
lean_dec(v_n_240_);
v_res_242_ = lean_usize_to_float32(v_n_boxed_241_);
v_r_243_ = lean_box_float32(v_res_242_);
return v_r_243_;
}
}
static float _init_l_instInhabitedFloat32___closed__0(void){
_start:
{
uint64_t v___x_244_; float v___x_245_; 
v___x_244_ = 0ULL;
v___x_245_ = lean_uint64_to_float32(v___x_244_);
return v___x_245_;
}
}
static float _init_l_instInhabitedFloat32(void){
_start:
{
float v___x_246_; 
v___x_246_ = lean_float32_once(&l_instInhabitedFloat32___closed__0, &l_instInhabitedFloat32___closed__0_once, _init_l_instInhabitedFloat32___closed__0);
return v___x_246_;
}
}
lean_object* l_Float32_repr(float v_n_247_, lean_object* v_prec_248_){
_start:
{
float v___x_249_; uint8_t v___x_250_; 
v___x_249_ = lean_float32_once(&l_instInhabitedFloat32___closed__0, &l_instInhabitedFloat32___closed__0_once, _init_l_instInhabitedFloat32___closed__0);
v___x_250_ = lean_float32_decLt(v_n_247_, v___x_249_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_float32_to_string(v_n_247_);
v___x_252_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
return v___x_252_;
}
else
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_253_ = lean_float32_to_string(v_n_247_);
v___x_254_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
v___x_255_ = l_Repr_addAppParen(v___x_254_, v_prec_248_);
return v___x_255_;
}
}
}
LEAN_EXPORT void l_Float32_repr_0interp(lean_interpreter_value* stack)
{
float v_n_247_ = stack[0].m_float32;
lean_object* v_prec_248_ = stack[1].m_obj;
lean_object* v_res_256_;
v_res_256_ = l_Float32_repr(v_n_247_, v_prec_248_);
stack->m_obj
 = v_res_256_;
}
LEAN_EXPORT lean_object* l_Float32_repr___boxed(lean_object* v_n_257_, lean_object* v_prec_258_){
_start:
{
float v_n_boxed_259_; lean_object* v_res_260_; 
v_n_boxed_259_ = lean_unbox_float32(v_n_257_);
lean_dec_ref(v_n_257_);
v_res_260_ = l_Float32_repr(v_n_boxed_259_, v_prec_258_);
lean_dec(v_prec_258_);
return v_res_260_;
}
}
static lean_object* _init_l_instReprAtomFloat32(void){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = lean_box(0);
return v___x_263_;
}
}
LEAN_EXPORT void l_Float32_sin_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_264_ = stack[0].m_float32;
float v_res_265_;
v_res_265_ = sinf(v_a_00___x40___internal___hyg_264_);
stack->m_float32
 = v_res_265_;
}
LEAN_EXPORT lean_object* l_Float32_sin___boxed(lean_object* v_a_00___x40___internal___hyg_266_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_267_; float v_res_268_; lean_object* v_r_269_; 
v_a_00___x40___internal___hyg_1__boxed_267_ = lean_unbox_float32(v_a_00___x40___internal___hyg_266_);
lean_dec_ref(v_a_00___x40___internal___hyg_266_);
v_res_268_ = sinf(v_a_00___x40___internal___hyg_1__boxed_267_);
v_r_269_ = lean_box_float32(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT void l_Float32_cos_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_270_ = stack[0].m_float32;
float v_res_271_;
v_res_271_ = cosf(v_a_00___x40___internal___hyg_270_);
stack->m_float32
 = v_res_271_;
}
LEAN_EXPORT lean_object* l_Float32_cos___boxed(lean_object* v_a_00___x40___internal___hyg_272_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_273_; float v_res_274_; lean_object* v_r_275_; 
v_a_00___x40___internal___hyg_1__boxed_273_ = lean_unbox_float32(v_a_00___x40___internal___hyg_272_);
lean_dec_ref(v_a_00___x40___internal___hyg_272_);
v_res_274_ = cosf(v_a_00___x40___internal___hyg_1__boxed_273_);
v_r_275_ = lean_box_float32(v_res_274_);
return v_r_275_;
}
}
LEAN_EXPORT void l_Float32_tan_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_276_ = stack[0].m_float32;
float v_res_277_;
v_res_277_ = tanf(v_a_00___x40___internal___hyg_276_);
stack->m_float32
 = v_res_277_;
}
LEAN_EXPORT lean_object* l_Float32_tan___boxed(lean_object* v_a_00___x40___internal___hyg_278_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_279_; float v_res_280_; lean_object* v_r_281_; 
v_a_00___x40___internal___hyg_1__boxed_279_ = lean_unbox_float32(v_a_00___x40___internal___hyg_278_);
lean_dec_ref(v_a_00___x40___internal___hyg_278_);
v_res_280_ = tanf(v_a_00___x40___internal___hyg_1__boxed_279_);
v_r_281_ = lean_box_float32(v_res_280_);
return v_r_281_;
}
}
LEAN_EXPORT void l_Float32_asin_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_282_ = stack[0].m_float32;
float v_res_283_;
v_res_283_ = asinf(v_a_00___x40___internal___hyg_282_);
stack->m_float32
 = v_res_283_;
}
LEAN_EXPORT lean_object* l_Float32_asin___boxed(lean_object* v_a_00___x40___internal___hyg_284_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_285_; float v_res_286_; lean_object* v_r_287_; 
v_a_00___x40___internal___hyg_1__boxed_285_ = lean_unbox_float32(v_a_00___x40___internal___hyg_284_);
lean_dec_ref(v_a_00___x40___internal___hyg_284_);
v_res_286_ = asinf(v_a_00___x40___internal___hyg_1__boxed_285_);
v_r_287_ = lean_box_float32(v_res_286_);
return v_r_287_;
}
}
LEAN_EXPORT void l_Float32_acos_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_288_ = stack[0].m_float32;
float v_res_289_;
v_res_289_ = acosf(v_a_00___x40___internal___hyg_288_);
stack->m_float32
 = v_res_289_;
}
LEAN_EXPORT lean_object* l_Float32_acos___boxed(lean_object* v_a_00___x40___internal___hyg_290_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_291_; float v_res_292_; lean_object* v_r_293_; 
v_a_00___x40___internal___hyg_1__boxed_291_ = lean_unbox_float32(v_a_00___x40___internal___hyg_290_);
lean_dec_ref(v_a_00___x40___internal___hyg_290_);
v_res_292_ = acosf(v_a_00___x40___internal___hyg_1__boxed_291_);
v_r_293_ = lean_box_float32(v_res_292_);
return v_r_293_;
}
}
LEAN_EXPORT void l_Float32_atan_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_294_ = stack[0].m_float32;
float v_res_295_;
v_res_295_ = atanf(v_a_00___x40___internal___hyg_294_);
stack->m_float32
 = v_res_295_;
}
LEAN_EXPORT lean_object* l_Float32_atan___boxed(lean_object* v_a_00___x40___internal___hyg_296_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_297_; float v_res_298_; lean_object* v_r_299_; 
v_a_00___x40___internal___hyg_1__boxed_297_ = lean_unbox_float32(v_a_00___x40___internal___hyg_296_);
lean_dec_ref(v_a_00___x40___internal___hyg_296_);
v_res_298_ = atanf(v_a_00___x40___internal___hyg_1__boxed_297_);
v_r_299_ = lean_box_float32(v_res_298_);
return v_r_299_;
}
}
LEAN_EXPORT void l_Float32_atan2_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_300_ = stack[0].m_float32;
float v_a_00___x40___internal___hyg_301_ = stack[1].m_float32;
float v_res_302_;
v_res_302_ = atan2f(v_a_00___x40___internal___hyg_300_, v_a_00___x40___internal___hyg_301_);
stack->m_float32
 = v_res_302_;
}
LEAN_EXPORT lean_object* l_Float32_atan2___boxed(lean_object* v_a_00___x40___internal___hyg_303_, lean_object* v_a_00___x40___internal___hyg_304_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_305_; float v_a_00___x40___internal___hyg_2__boxed_306_; float v_res_307_; lean_object* v_r_308_; 
v_a_00___x40___internal___hyg_1__boxed_305_ = lean_unbox_float32(v_a_00___x40___internal___hyg_303_);
lean_dec_ref(v_a_00___x40___internal___hyg_303_);
v_a_00___x40___internal___hyg_2__boxed_306_ = lean_unbox_float32(v_a_00___x40___internal___hyg_304_);
lean_dec_ref(v_a_00___x40___internal___hyg_304_);
v_res_307_ = atan2f(v_a_00___x40___internal___hyg_1__boxed_305_, v_a_00___x40___internal___hyg_2__boxed_306_);
v_r_308_ = lean_box_float32(v_res_307_);
return v_r_308_;
}
}
LEAN_EXPORT void l_Float32_sinh_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_309_ = stack[0].m_float32;
float v_res_310_;
v_res_310_ = sinhf(v_a_00___x40___internal___hyg_309_);
stack->m_float32
 = v_res_310_;
}
LEAN_EXPORT lean_object* l_Float32_sinh___boxed(lean_object* v_a_00___x40___internal___hyg_311_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_312_; float v_res_313_; lean_object* v_r_314_; 
v_a_00___x40___internal___hyg_1__boxed_312_ = lean_unbox_float32(v_a_00___x40___internal___hyg_311_);
lean_dec_ref(v_a_00___x40___internal___hyg_311_);
v_res_313_ = sinhf(v_a_00___x40___internal___hyg_1__boxed_312_);
v_r_314_ = lean_box_float32(v_res_313_);
return v_r_314_;
}
}
LEAN_EXPORT void l_Float32_cosh_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_315_ = stack[0].m_float32;
float v_res_316_;
v_res_316_ = coshf(v_a_00___x40___internal___hyg_315_);
stack->m_float32
 = v_res_316_;
}
LEAN_EXPORT lean_object* l_Float32_cosh___boxed(lean_object* v_a_00___x40___internal___hyg_317_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_318_; float v_res_319_; lean_object* v_r_320_; 
v_a_00___x40___internal___hyg_1__boxed_318_ = lean_unbox_float32(v_a_00___x40___internal___hyg_317_);
lean_dec_ref(v_a_00___x40___internal___hyg_317_);
v_res_319_ = coshf(v_a_00___x40___internal___hyg_1__boxed_318_);
v_r_320_ = lean_box_float32(v_res_319_);
return v_r_320_;
}
}
LEAN_EXPORT void l_Float32_tanh_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_321_ = stack[0].m_float32;
float v_res_322_;
v_res_322_ = tanhf(v_a_00___x40___internal___hyg_321_);
stack->m_float32
 = v_res_322_;
}
LEAN_EXPORT lean_object* l_Float32_tanh___boxed(lean_object* v_a_00___x40___internal___hyg_323_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_324_; float v_res_325_; lean_object* v_r_326_; 
v_a_00___x40___internal___hyg_1__boxed_324_ = lean_unbox_float32(v_a_00___x40___internal___hyg_323_);
lean_dec_ref(v_a_00___x40___internal___hyg_323_);
v_res_325_ = tanhf(v_a_00___x40___internal___hyg_1__boxed_324_);
v_r_326_ = lean_box_float32(v_res_325_);
return v_r_326_;
}
}
LEAN_EXPORT void l_Float32_asinh_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_327_ = stack[0].m_float32;
float v_res_328_;
v_res_328_ = asinhf(v_a_00___x40___internal___hyg_327_);
stack->m_float32
 = v_res_328_;
}
LEAN_EXPORT lean_object* l_Float32_asinh___boxed(lean_object* v_a_00___x40___internal___hyg_329_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_330_; float v_res_331_; lean_object* v_r_332_; 
v_a_00___x40___internal___hyg_1__boxed_330_ = lean_unbox_float32(v_a_00___x40___internal___hyg_329_);
lean_dec_ref(v_a_00___x40___internal___hyg_329_);
v_res_331_ = asinhf(v_a_00___x40___internal___hyg_1__boxed_330_);
v_r_332_ = lean_box_float32(v_res_331_);
return v_r_332_;
}
}
LEAN_EXPORT void l_Float32_acosh_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_333_ = stack[0].m_float32;
float v_res_334_;
v_res_334_ = acoshf(v_a_00___x40___internal___hyg_333_);
stack->m_float32
 = v_res_334_;
}
LEAN_EXPORT lean_object* l_Float32_acosh___boxed(lean_object* v_a_00___x40___internal___hyg_335_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_336_; float v_res_337_; lean_object* v_r_338_; 
v_a_00___x40___internal___hyg_1__boxed_336_ = lean_unbox_float32(v_a_00___x40___internal___hyg_335_);
lean_dec_ref(v_a_00___x40___internal___hyg_335_);
v_res_337_ = acoshf(v_a_00___x40___internal___hyg_1__boxed_336_);
v_r_338_ = lean_box_float32(v_res_337_);
return v_r_338_;
}
}
LEAN_EXPORT void l_Float32_atanh_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_339_ = stack[0].m_float32;
float v_res_340_;
v_res_340_ = atanhf(v_a_00___x40___internal___hyg_339_);
stack->m_float32
 = v_res_340_;
}
LEAN_EXPORT lean_object* l_Float32_atanh___boxed(lean_object* v_a_00___x40___internal___hyg_341_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_342_; float v_res_343_; lean_object* v_r_344_; 
v_a_00___x40___internal___hyg_1__boxed_342_ = lean_unbox_float32(v_a_00___x40___internal___hyg_341_);
lean_dec_ref(v_a_00___x40___internal___hyg_341_);
v_res_343_ = atanhf(v_a_00___x40___internal___hyg_1__boxed_342_);
v_r_344_ = lean_box_float32(v_res_343_);
return v_r_344_;
}
}
LEAN_EXPORT void l_Float32_exp_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_345_ = stack[0].m_float32;
float v_res_346_;
v_res_346_ = expf(v_a_00___x40___internal___hyg_345_);
stack->m_float32
 = v_res_346_;
}
LEAN_EXPORT lean_object* l_Float32_exp___boxed(lean_object* v_a_00___x40___internal___hyg_347_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_348_; float v_res_349_; lean_object* v_r_350_; 
v_a_00___x40___internal___hyg_1__boxed_348_ = lean_unbox_float32(v_a_00___x40___internal___hyg_347_);
lean_dec_ref(v_a_00___x40___internal___hyg_347_);
v_res_349_ = expf(v_a_00___x40___internal___hyg_1__boxed_348_);
v_r_350_ = lean_box_float32(v_res_349_);
return v_r_350_;
}
}
LEAN_EXPORT void l_Float32_exp2_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_351_ = stack[0].m_float32;
float v_res_352_;
v_res_352_ = exp2f(v_a_00___x40___internal___hyg_351_);
stack->m_float32
 = v_res_352_;
}
LEAN_EXPORT lean_object* l_Float32_exp2___boxed(lean_object* v_a_00___x40___internal___hyg_353_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_354_; float v_res_355_; lean_object* v_r_356_; 
v_a_00___x40___internal___hyg_1__boxed_354_ = lean_unbox_float32(v_a_00___x40___internal___hyg_353_);
lean_dec_ref(v_a_00___x40___internal___hyg_353_);
v_res_355_ = exp2f(v_a_00___x40___internal___hyg_1__boxed_354_);
v_r_356_ = lean_box_float32(v_res_355_);
return v_r_356_;
}
}
LEAN_EXPORT void l_Float32_log_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_357_ = stack[0].m_float32;
float v_res_358_;
v_res_358_ = logf(v_a_00___x40___internal___hyg_357_);
stack->m_float32
 = v_res_358_;
}
LEAN_EXPORT lean_object* l_Float32_log___boxed(lean_object* v_a_00___x40___internal___hyg_359_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_360_; float v_res_361_; lean_object* v_r_362_; 
v_a_00___x40___internal___hyg_1__boxed_360_ = lean_unbox_float32(v_a_00___x40___internal___hyg_359_);
lean_dec_ref(v_a_00___x40___internal___hyg_359_);
v_res_361_ = logf(v_a_00___x40___internal___hyg_1__boxed_360_);
v_r_362_ = lean_box_float32(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT void l_Float32_log2_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_363_ = stack[0].m_float32;
float v_res_364_;
v_res_364_ = log2f(v_a_00___x40___internal___hyg_363_);
stack->m_float32
 = v_res_364_;
}
LEAN_EXPORT lean_object* l_Float32_log2___boxed(lean_object* v_a_00___x40___internal___hyg_365_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_366_; float v_res_367_; lean_object* v_r_368_; 
v_a_00___x40___internal___hyg_1__boxed_366_ = lean_unbox_float32(v_a_00___x40___internal___hyg_365_);
lean_dec_ref(v_a_00___x40___internal___hyg_365_);
v_res_367_ = log2f(v_a_00___x40___internal___hyg_1__boxed_366_);
v_r_368_ = lean_box_float32(v_res_367_);
return v_r_368_;
}
}
LEAN_EXPORT void l_Float32_log10_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_369_ = stack[0].m_float32;
float v_res_370_;
v_res_370_ = log10f(v_a_00___x40___internal___hyg_369_);
stack->m_float32
 = v_res_370_;
}
LEAN_EXPORT lean_object* l_Float32_log10___boxed(lean_object* v_a_00___x40___internal___hyg_371_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_372_; float v_res_373_; lean_object* v_r_374_; 
v_a_00___x40___internal___hyg_1__boxed_372_ = lean_unbox_float32(v_a_00___x40___internal___hyg_371_);
lean_dec_ref(v_a_00___x40___internal___hyg_371_);
v_res_373_ = log10f(v_a_00___x40___internal___hyg_1__boxed_372_);
v_r_374_ = lean_box_float32(v_res_373_);
return v_r_374_;
}
}
LEAN_EXPORT void l_Float32_pow_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_375_ = stack[0].m_float32;
float v_a_00___x40___internal___hyg_376_ = stack[1].m_float32;
float v_res_377_;
v_res_377_ = powf(v_a_00___x40___internal___hyg_375_, v_a_00___x40___internal___hyg_376_);
stack->m_float32
 = v_res_377_;
}
LEAN_EXPORT lean_object* l_Float32_pow___boxed(lean_object* v_a_00___x40___internal___hyg_378_, lean_object* v_a_00___x40___internal___hyg_379_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_380_; float v_a_00___x40___internal___hyg_2__boxed_381_; float v_res_382_; lean_object* v_r_383_; 
v_a_00___x40___internal___hyg_1__boxed_380_ = lean_unbox_float32(v_a_00___x40___internal___hyg_378_);
lean_dec_ref(v_a_00___x40___internal___hyg_378_);
v_a_00___x40___internal___hyg_2__boxed_381_ = lean_unbox_float32(v_a_00___x40___internal___hyg_379_);
lean_dec_ref(v_a_00___x40___internal___hyg_379_);
v_res_382_ = powf(v_a_00___x40___internal___hyg_1__boxed_380_, v_a_00___x40___internal___hyg_2__boxed_381_);
v_r_383_ = lean_box_float32(v_res_382_);
return v_r_383_;
}
}
LEAN_EXPORT void l_Float32_sqrt_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_384_ = stack[0].m_float32;
float v_res_385_;
v_res_385_ = sqrtf(v_a_00___x40___internal___hyg_384_);
stack->m_float32
 = v_res_385_;
}
LEAN_EXPORT lean_object* l_Float32_sqrt___boxed(lean_object* v_a_00___x40___internal___hyg_386_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_387_; float v_res_388_; lean_object* v_r_389_; 
v_a_00___x40___internal___hyg_1__boxed_387_ = lean_unbox_float32(v_a_00___x40___internal___hyg_386_);
lean_dec_ref(v_a_00___x40___internal___hyg_386_);
v_res_388_ = sqrtf(v_a_00___x40___internal___hyg_1__boxed_387_);
v_r_389_ = lean_box_float32(v_res_388_);
return v_r_389_;
}
}
LEAN_EXPORT void l_Float32_fma_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_390_ = stack[0].m_float32;
float v_a_00___x40___internal___hyg_391_ = stack[1].m_float32;
float v_a_00___x40___internal___hyg_392_ = stack[2].m_float32;
float v_res_393_;
v_res_393_ = fmaf(v_a_00___x40___internal___hyg_390_, v_a_00___x40___internal___hyg_391_, v_a_00___x40___internal___hyg_392_);
stack->m_float32
 = v_res_393_;
}
LEAN_EXPORT lean_object* l_Float32_fma___boxed(lean_object* v_a_00___x40___internal___hyg_394_, lean_object* v_a_00___x40___internal___hyg_395_, lean_object* v_a_00___x40___internal___hyg_396_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_397_; float v_a_00___x40___internal___hyg_2__boxed_398_; float v_a_00___x40___internal___hyg_3__boxed_399_; float v_res_400_; lean_object* v_r_401_; 
v_a_00___x40___internal___hyg_1__boxed_397_ = lean_unbox_float32(v_a_00___x40___internal___hyg_394_);
lean_dec_ref(v_a_00___x40___internal___hyg_394_);
v_a_00___x40___internal___hyg_2__boxed_398_ = lean_unbox_float32(v_a_00___x40___internal___hyg_395_);
lean_dec_ref(v_a_00___x40___internal___hyg_395_);
v_a_00___x40___internal___hyg_3__boxed_399_ = lean_unbox_float32(v_a_00___x40___internal___hyg_396_);
lean_dec_ref(v_a_00___x40___internal___hyg_396_);
v_res_400_ = fmaf(v_a_00___x40___internal___hyg_1__boxed_397_, v_a_00___x40___internal___hyg_2__boxed_398_, v_a_00___x40___internal___hyg_3__boxed_399_);
v_r_401_ = lean_box_float32(v_res_400_);
return v_r_401_;
}
}
LEAN_EXPORT void l_Float32_cbrt_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_402_ = stack[0].m_float32;
float v_res_403_;
v_res_403_ = cbrtf(v_a_00___x40___internal___hyg_402_);
stack->m_float32
 = v_res_403_;
}
LEAN_EXPORT lean_object* l_Float32_cbrt___boxed(lean_object* v_a_00___x40___internal___hyg_404_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_405_; float v_res_406_; lean_object* v_r_407_; 
v_a_00___x40___internal___hyg_1__boxed_405_ = lean_unbox_float32(v_a_00___x40___internal___hyg_404_);
lean_dec_ref(v_a_00___x40___internal___hyg_404_);
v_res_406_ = cbrtf(v_a_00___x40___internal___hyg_1__boxed_405_);
v_r_407_ = lean_box_float32(v_res_406_);
return v_r_407_;
}
}
LEAN_EXPORT void l_Float32_ceil_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_408_ = stack[0].m_float32;
float v_res_409_;
v_res_409_ = ceilf(v_a_00___x40___internal___hyg_408_);
stack->m_float32
 = v_res_409_;
}
LEAN_EXPORT lean_object* l_Float32_ceil___boxed(lean_object* v_a_00___x40___internal___hyg_410_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_411_; float v_res_412_; lean_object* v_r_413_; 
v_a_00___x40___internal___hyg_1__boxed_411_ = lean_unbox_float32(v_a_00___x40___internal___hyg_410_);
lean_dec_ref(v_a_00___x40___internal___hyg_410_);
v_res_412_ = ceilf(v_a_00___x40___internal___hyg_1__boxed_411_);
v_r_413_ = lean_box_float32(v_res_412_);
return v_r_413_;
}
}
LEAN_EXPORT void l_Float32_floor_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_414_ = stack[0].m_float32;
float v_res_415_;
v_res_415_ = floorf(v_a_00___x40___internal___hyg_414_);
stack->m_float32
 = v_res_415_;
}
LEAN_EXPORT lean_object* l_Float32_floor___boxed(lean_object* v_a_00___x40___internal___hyg_416_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_417_; float v_res_418_; lean_object* v_r_419_; 
v_a_00___x40___internal___hyg_1__boxed_417_ = lean_unbox_float32(v_a_00___x40___internal___hyg_416_);
lean_dec_ref(v_a_00___x40___internal___hyg_416_);
v_res_418_ = floorf(v_a_00___x40___internal___hyg_1__boxed_417_);
v_r_419_ = lean_box_float32(v_res_418_);
return v_r_419_;
}
}
LEAN_EXPORT void l_Float32_round_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_420_ = stack[0].m_float32;
float v_res_421_;
v_res_421_ = roundf(v_a_00___x40___internal___hyg_420_);
stack->m_float32
 = v_res_421_;
}
LEAN_EXPORT lean_object* l_Float32_round___boxed(lean_object* v_a_00___x40___internal___hyg_422_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_423_; float v_res_424_; lean_object* v_r_425_; 
v_a_00___x40___internal___hyg_1__boxed_423_ = lean_unbox_float32(v_a_00___x40___internal___hyg_422_);
lean_dec_ref(v_a_00___x40___internal___hyg_422_);
v_res_424_ = roundf(v_a_00___x40___internal___hyg_1__boxed_423_);
v_r_425_ = lean_box_float32(v_res_424_);
return v_r_425_;
}
}
LEAN_EXPORT void l_Float32_abs_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_426_ = stack[0].m_float32;
float v_res_427_;
v_res_427_ = fabsf(v_a_00___x40___internal___hyg_426_);
stack->m_float32
 = v_res_427_;
}
LEAN_EXPORT lean_object* l_Float32_abs___boxed(lean_object* v_a_00___x40___internal___hyg_428_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_429_; float v_res_430_; lean_object* v_r_431_; 
v_a_00___x40___internal___hyg_1__boxed_429_ = lean_unbox_float32(v_a_00___x40___internal___hyg_428_);
lean_dec_ref(v_a_00___x40___internal___hyg_428_);
v_res_430_ = fabsf(v_a_00___x40___internal___hyg_1__boxed_429_);
v_r_431_ = lean_box_float32(v_res_430_);
return v_r_431_;
}
}
LEAN_EXPORT void l_Float32_minimum_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_434_ = stack[0].m_float32;
float v_a_00___x40___internal___hyg_435_ = stack[1].m_float32;
float v_res_436_;
v_res_436_ = lean_float32_minimum(v_a_00___x40___internal___hyg_434_, v_a_00___x40___internal___hyg_435_);
stack->m_float32
 = v_res_436_;
}
LEAN_EXPORT lean_object* l_Float32_minimum___boxed(lean_object* v_a_00___x40___internal___hyg_437_, lean_object* v_a_00___x40___internal___hyg_438_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_439_; float v_a_00___x40___internal___hyg_2__boxed_440_; float v_res_441_; lean_object* v_r_442_; 
v_a_00___x40___internal___hyg_1__boxed_439_ = lean_unbox_float32(v_a_00___x40___internal___hyg_437_);
lean_dec_ref(v_a_00___x40___internal___hyg_437_);
v_a_00___x40___internal___hyg_2__boxed_440_ = lean_unbox_float32(v_a_00___x40___internal___hyg_438_);
lean_dec_ref(v_a_00___x40___internal___hyg_438_);
v_res_441_ = lean_float32_minimum(v_a_00___x40___internal___hyg_1__boxed_439_, v_a_00___x40___internal___hyg_2__boxed_440_);
v_r_442_ = lean_box_float32(v_res_441_);
return v_r_442_;
}
}
LEAN_EXPORT void l_Float32_minimumNumber_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_443_ = stack[0].m_float32;
float v_a_00___x40___internal___hyg_444_ = stack[1].m_float32;
float v_res_445_;
v_res_445_ = lean_float32_minimum_number(v_a_00___x40___internal___hyg_443_, v_a_00___x40___internal___hyg_444_);
stack->m_float32
 = v_res_445_;
}
LEAN_EXPORT lean_object* l_Float32_minimumNumber___boxed(lean_object* v_a_00___x40___internal___hyg_446_, lean_object* v_a_00___x40___internal___hyg_447_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_448_; float v_a_00___x40___internal___hyg_2__boxed_449_; float v_res_450_; lean_object* v_r_451_; 
v_a_00___x40___internal___hyg_1__boxed_448_ = lean_unbox_float32(v_a_00___x40___internal___hyg_446_);
lean_dec_ref(v_a_00___x40___internal___hyg_446_);
v_a_00___x40___internal___hyg_2__boxed_449_ = lean_unbox_float32(v_a_00___x40___internal___hyg_447_);
lean_dec_ref(v_a_00___x40___internal___hyg_447_);
v_res_450_ = lean_float32_minimum_number(v_a_00___x40___internal___hyg_1__boxed_448_, v_a_00___x40___internal___hyg_2__boxed_449_);
v_r_451_ = lean_box_float32(v_res_450_);
return v_r_451_;
}
}
LEAN_EXPORT void l_Float32_maximum_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_452_ = stack[0].m_float32;
float v_a_00___x40___internal___hyg_453_ = stack[1].m_float32;
float v_res_454_;
v_res_454_ = lean_float32_maximum(v_a_00___x40___internal___hyg_452_, v_a_00___x40___internal___hyg_453_);
stack->m_float32
 = v_res_454_;
}
LEAN_EXPORT lean_object* l_Float32_maximum___boxed(lean_object* v_a_00___x40___internal___hyg_455_, lean_object* v_a_00___x40___internal___hyg_456_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_457_; float v_a_00___x40___internal___hyg_2__boxed_458_; float v_res_459_; lean_object* v_r_460_; 
v_a_00___x40___internal___hyg_1__boxed_457_ = lean_unbox_float32(v_a_00___x40___internal___hyg_455_);
lean_dec_ref(v_a_00___x40___internal___hyg_455_);
v_a_00___x40___internal___hyg_2__boxed_458_ = lean_unbox_float32(v_a_00___x40___internal___hyg_456_);
lean_dec_ref(v_a_00___x40___internal___hyg_456_);
v_res_459_ = lean_float32_maximum(v_a_00___x40___internal___hyg_1__boxed_457_, v_a_00___x40___internal___hyg_2__boxed_458_);
v_r_460_ = lean_box_float32(v_res_459_);
return v_r_460_;
}
}
LEAN_EXPORT void l_Float32_maximumNumber_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_461_ = stack[0].m_float32;
float v_a_00___x40___internal___hyg_462_ = stack[1].m_float32;
float v_res_463_;
v_res_463_ = lean_float32_maximum_number(v_a_00___x40___internal___hyg_461_, v_a_00___x40___internal___hyg_462_);
stack->m_float32
 = v_res_463_;
}
LEAN_EXPORT lean_object* l_Float32_maximumNumber___boxed(lean_object* v_a_00___x40___internal___hyg_464_, lean_object* v_a_00___x40___internal___hyg_465_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_466_; float v_a_00___x40___internal___hyg_2__boxed_467_; float v_res_468_; lean_object* v_r_469_; 
v_a_00___x40___internal___hyg_1__boxed_466_ = lean_unbox_float32(v_a_00___x40___internal___hyg_464_);
lean_dec_ref(v_a_00___x40___internal___hyg_464_);
v_a_00___x40___internal___hyg_2__boxed_467_ = lean_unbox_float32(v_a_00___x40___internal___hyg_465_);
lean_dec_ref(v_a_00___x40___internal___hyg_465_);
v_res_468_ = lean_float32_maximum_number(v_a_00___x40___internal___hyg_1__boxed_466_, v_a_00___x40___internal___hyg_2__boxed_467_);
v_r_469_ = lean_box_float32(v_res_468_);
return v_r_469_;
}
}
LEAN_EXPORT void l_Float32_scaleB_0interp(lean_interpreter_value* stack)
{
float v_x_474_ = stack[0].m_float32;
lean_object* v_i_475_ = stack[1].m_obj;
float v_res_476_;
v_res_476_ = lean_float32_scaleb(v_x_474_, v_i_475_);
stack->m_float32
 = v_res_476_;
}
LEAN_EXPORT lean_object* l_Float32_scaleB___boxed(lean_object* v_x_477_, lean_object* v_i_478_){
_start:
{
float v_x_boxed_479_; float v_res_480_; lean_object* v_r_481_; 
v_x_boxed_479_ = lean_unbox_float32(v_x_477_);
lean_dec_ref(v_x_477_);
v_res_480_ = lean_float32_scaleb(v_x_boxed_479_, v_i_478_);
lean_dec(v_i_478_);
v_r_481_ = lean_box_float32(v_res_480_);
return v_r_481_;
}
}
LEAN_EXPORT void l_Float32_toFloat_0interp(lean_interpreter_value* stack)
{
float v_a_00___x40___internal___hyg_482_ = stack[0].m_float32;
double v_res_483_;
v_res_483_ = lean_float32_to_float(v_a_00___x40___internal___hyg_482_);
stack->m_float
 = v_res_483_;
}
LEAN_EXPORT lean_object* l_Float32_toFloat___boxed(lean_object* v_a_00___x40___internal___hyg_484_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_485_; double v_res_486_; lean_object* v_r_487_; 
v_a_00___x40___internal___hyg_1__boxed_485_ = lean_unbox_float32(v_a_00___x40___internal___hyg_484_);
lean_dec_ref(v_a_00___x40___internal___hyg_484_);
v_res_486_ = lean_float32_to_float(v_a_00___x40___internal___hyg_1__boxed_485_);
v_r_487_ = lean_box_float(v_res_486_);
return v_r_487_;
}
}
LEAN_EXPORT void l_Float_toFloat32_0interp(lean_interpreter_value* stack)
{
double v_a_00___x40___internal___hyg_488_ = stack[0].m_float;
float v_res_489_;
v_res_489_ = lean_float_to_float32(v_a_00___x40___internal___hyg_488_);
stack->m_float32
 = v_res_489_;
}
LEAN_EXPORT lean_object* l_Float_toFloat32___boxed(lean_object* v_a_00___x40___internal___hyg_490_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_491_; float v_res_492_; lean_object* v_r_493_; 
v_a_00___x40___internal___hyg_1__boxed_491_ = lean_unbox_float(v_a_00___x40___internal___hyg_490_);
lean_dec_ref(v_a_00___x40___internal___hyg_490_);
v_res_492_ = lean_float_to_float32(v_a_00___x40___internal___hyg_1__boxed_491_);
v_r_493_ = lean_box_float32(v_res_492_);
return v_r_493_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Float(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Float_Model_Float32(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Float32(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
