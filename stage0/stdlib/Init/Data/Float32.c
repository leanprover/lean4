// Lean compiler output
// Module: Init.Data.Float32
// Imports: public import Init.Data.Float
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
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_float32Spec___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_float32Spec___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_float32Spec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_float32Spec___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_float32Spec___closed__0 = (const lean_object*)&l_float32Spec___closed__0_value;
static lean_once_cell_t l_float32Spec___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_float32Spec___closed__1;
LEAN_EXPORT lean_object* l_float32Spec;
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
LEAN_EXPORT uint8_t l_float32Spec___lam__0(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = 1;
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_float32Spec___lam__0___boxed(lean_object* v_x_4_, lean_object* v_x_5_){
_start:
{
uint8_t v_res_6_; lean_object* v_r_7_; 
v_res_6_ = l_float32Spec___lam__0(v_x_4_, v_x_5_);
v_r_7_ = lean_box(v_res_6_);
return v_r_7_;
}
}
static lean_object* _init_l_float32Spec___closed__1(void){
_start:
{
lean_object* v___f_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___f_9_ = ((lean_object*)(l_float32Spec___closed__0));
v___x_10_ = lean_box(0);
v___x_11_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
lean_ctor_set(v___x_11_, 1, v___f_9_);
lean_ctor_set(v___x_11_, 2, v___f_9_);
return v___x_11_;
}
}
static lean_object* _init_l_float32Spec(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&l_float32Spec___closed__1, &l_float32Spec___closed__1_once, _init_l_float32Spec___closed__1);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Float32_add___boxed(lean_object* v_a_00___x40___internal___hyg_15_, lean_object* v_a_00___x40___internal___hyg_16_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_17_; float v_a_00___x40___internal___hyg_2__boxed_18_; float v_res_19_; lean_object* v_r_20_; 
v_a_00___x40___internal___hyg_1__boxed_17_ = lean_unbox_float32(v_a_00___x40___internal___hyg_15_);
lean_dec_ref(v_a_00___x40___internal___hyg_15_);
v_a_00___x40___internal___hyg_2__boxed_18_ = lean_unbox_float32(v_a_00___x40___internal___hyg_16_);
lean_dec_ref(v_a_00___x40___internal___hyg_16_);
v_res_19_ = lean_float32_add(v_a_00___x40___internal___hyg_1__boxed_17_, v_a_00___x40___internal___hyg_2__boxed_18_);
v_r_20_ = lean_box_float32(v_res_19_);
return v_r_20_;
}
}
LEAN_EXPORT lean_object* l_Float32_sub___boxed(lean_object* v_a_00___x40___internal___hyg_23_, lean_object* v_a_00___x40___internal___hyg_24_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_25_; float v_a_00___x40___internal___hyg_2__boxed_26_; float v_res_27_; lean_object* v_r_28_; 
v_a_00___x40___internal___hyg_1__boxed_25_ = lean_unbox_float32(v_a_00___x40___internal___hyg_23_);
lean_dec_ref(v_a_00___x40___internal___hyg_23_);
v_a_00___x40___internal___hyg_2__boxed_26_ = lean_unbox_float32(v_a_00___x40___internal___hyg_24_);
lean_dec_ref(v_a_00___x40___internal___hyg_24_);
v_res_27_ = lean_float32_sub(v_a_00___x40___internal___hyg_1__boxed_25_, v_a_00___x40___internal___hyg_2__boxed_26_);
v_r_28_ = lean_box_float32(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT lean_object* l_Float32_mul___boxed(lean_object* v_a_00___x40___internal___hyg_31_, lean_object* v_a_00___x40___internal___hyg_32_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_33_; float v_a_00___x40___internal___hyg_2__boxed_34_; float v_res_35_; lean_object* v_r_36_; 
v_a_00___x40___internal___hyg_1__boxed_33_ = lean_unbox_float32(v_a_00___x40___internal___hyg_31_);
lean_dec_ref(v_a_00___x40___internal___hyg_31_);
v_a_00___x40___internal___hyg_2__boxed_34_ = lean_unbox_float32(v_a_00___x40___internal___hyg_32_);
lean_dec_ref(v_a_00___x40___internal___hyg_32_);
v_res_35_ = lean_float32_mul(v_a_00___x40___internal___hyg_1__boxed_33_, v_a_00___x40___internal___hyg_2__boxed_34_);
v_r_36_ = lean_box_float32(v_res_35_);
return v_r_36_;
}
}
LEAN_EXPORT lean_object* l_Float32_div___boxed(lean_object* v_a_00___x40___internal___hyg_39_, lean_object* v_a_00___x40___internal___hyg_40_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_41_; float v_a_00___x40___internal___hyg_2__boxed_42_; float v_res_43_; lean_object* v_r_44_; 
v_a_00___x40___internal___hyg_1__boxed_41_ = lean_unbox_float32(v_a_00___x40___internal___hyg_39_);
lean_dec_ref(v_a_00___x40___internal___hyg_39_);
v_a_00___x40___internal___hyg_2__boxed_42_ = lean_unbox_float32(v_a_00___x40___internal___hyg_40_);
lean_dec_ref(v_a_00___x40___internal___hyg_40_);
v_res_43_ = lean_float32_div(v_a_00___x40___internal___hyg_1__boxed_41_, v_a_00___x40___internal___hyg_2__boxed_42_);
v_r_44_ = lean_box_float32(v_res_43_);
return v_r_44_;
}
}
LEAN_EXPORT lean_object* l_Float32_neg___boxed(lean_object* v_a_00___x40___internal___hyg_46_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_47_; float v_res_48_; lean_object* v_r_49_; 
v_a_00___x40___internal___hyg_1__boxed_47_ = lean_unbox_float32(v_a_00___x40___internal___hyg_46_);
lean_dec_ref(v_a_00___x40___internal___hyg_46_);
v_res_48_ = lean_float32_negate(v_a_00___x40___internal___hyg_1__boxed_47_);
v_r_49_ = lean_box_float32(v_res_48_);
return v_r_49_;
}
}
LEAN_EXPORT lean_object* l_Float32_ofBits___boxed(lean_object* v_a_00___x40___internal___hyg_51_){
_start:
{
uint32_t v_a_00___x40___internal___hyg_1__boxed_52_; float v_res_53_; lean_object* v_r_54_; 
v_a_00___x40___internal___hyg_1__boxed_52_ = lean_unbox_uint32(v_a_00___x40___internal___hyg_51_);
lean_dec(v_a_00___x40___internal___hyg_51_);
v_res_53_ = lean_float32_of_bits(v_a_00___x40___internal___hyg_1__boxed_52_);
v_r_54_ = lean_box_float32(v_res_53_);
return v_r_54_;
}
}
LEAN_EXPORT lean_object* l_Float32_toBits___boxed(lean_object* v_a_00___x40___internal___hyg_56_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_57_; uint32_t v_res_58_; lean_object* v_r_59_; 
v_a_00___x40___internal___hyg_1__boxed_57_ = lean_unbox_float32(v_a_00___x40___internal___hyg_56_);
lean_dec_ref(v_a_00___x40___internal___hyg_56_);
v_res_58_ = lean_float32_to_bits(v_a_00___x40___internal___hyg_1__boxed_57_);
v_r_59_ = lean_box_uint32(v_res_58_);
return v_r_59_;
}
}
static lean_object* _init_l_instLTFloat32(void){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lean_box(0);
return v___x_70_;
}
}
static lean_object* _init_l_instLEFloat32(void){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lean_box(0);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Float32_beq___boxed(lean_object* v_a_74_, lean_object* v_b_75_){
_start:
{
float v_a_boxed_76_; float v_b_boxed_77_; uint8_t v_res_78_; lean_object* v_r_79_; 
v_a_boxed_76_ = lean_unbox_float32(v_a_74_);
lean_dec_ref(v_a_74_);
v_b_boxed_77_ = lean_unbox_float32(v_b_75_);
lean_dec_ref(v_b_75_);
v_res_78_ = lean_float32_beq(v_a_boxed_76_, v_b_boxed_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT lean_object* l_Float32_decLt___boxed(lean_object* v_a_84_, lean_object* v_b_85_){
_start:
{
float v_a_boxed_86_; float v_b_boxed_87_; uint8_t v_res_88_; lean_object* v_r_89_; 
v_a_boxed_86_ = lean_unbox_float32(v_a_84_);
lean_dec_ref(v_a_84_);
v_b_boxed_87_ = lean_unbox_float32(v_b_85_);
lean_dec_ref(v_b_85_);
v_res_88_ = lean_float32_decLt(v_a_boxed_86_, v_b_boxed_87_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
LEAN_EXPORT lean_object* l_Float32_decLe___boxed(lean_object* v_a_92_, lean_object* v_b_93_){
_start:
{
float v_a_boxed_94_; float v_b_boxed_95_; uint8_t v_res_96_; lean_object* v_r_97_; 
v_a_boxed_94_ = lean_unbox_float32(v_a_92_);
lean_dec_ref(v_a_92_);
v_b_boxed_95_ = lean_unbox_float32(v_b_93_);
lean_dec_ref(v_b_93_);
v_res_96_ = lean_float32_decLe(v_a_boxed_94_, v_b_boxed_95_);
v_r_97_ = lean_box(v_res_96_);
return v_r_97_;
}
}
LEAN_EXPORT lean_object* l_Float32_toString___boxed(lean_object* v_a_00___x40___internal___hyg_99_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_100_; lean_object* v_res_101_; 
v_a_00___x40___internal___hyg_1__boxed_100_ = lean_unbox_float32(v_a_00___x40___internal___hyg_99_);
lean_dec_ref(v_a_00___x40___internal___hyg_99_);
v_res_101_ = lean_float32_to_string(v_a_00___x40___internal___hyg_1__boxed_100_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Float32_toUInt8___boxed(lean_object* v_a_00___x40___internal___hyg_103_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_104_; uint8_t v_res_105_; lean_object* v_r_106_; 
v_a_00___x40___internal___hyg_1__boxed_104_ = lean_unbox_float32(v_a_00___x40___internal___hyg_103_);
lean_dec_ref(v_a_00___x40___internal___hyg_103_);
v_res_105_ = lean_float32_to_uint8(v_a_00___x40___internal___hyg_1__boxed_104_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
LEAN_EXPORT lean_object* l_Float32_toUInt16___boxed(lean_object* v_a_00___x40___internal___hyg_108_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_109_; uint16_t v_res_110_; lean_object* v_r_111_; 
v_a_00___x40___internal___hyg_1__boxed_109_ = lean_unbox_float32(v_a_00___x40___internal___hyg_108_);
lean_dec_ref(v_a_00___x40___internal___hyg_108_);
v_res_110_ = lean_float32_to_uint16(v_a_00___x40___internal___hyg_1__boxed_109_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT lean_object* l_Float32_toUInt32___boxed(lean_object* v_a_00___x40___internal___hyg_113_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_114_; uint32_t v_res_115_; lean_object* v_r_116_; 
v_a_00___x40___internal___hyg_1__boxed_114_ = lean_unbox_float32(v_a_00___x40___internal___hyg_113_);
lean_dec_ref(v_a_00___x40___internal___hyg_113_);
v_res_115_ = lean_float32_to_uint32(v_a_00___x40___internal___hyg_1__boxed_114_);
v_r_116_ = lean_box_uint32(v_res_115_);
return v_r_116_;
}
}
LEAN_EXPORT lean_object* l_Float32_toUInt64___boxed(lean_object* v_a_00___x40___internal___hyg_118_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_119_; uint64_t v_res_120_; lean_object* v_r_121_; 
v_a_00___x40___internal___hyg_1__boxed_119_ = lean_unbox_float32(v_a_00___x40___internal___hyg_118_);
lean_dec_ref(v_a_00___x40___internal___hyg_118_);
v_res_120_ = lean_float32_to_uint64(v_a_00___x40___internal___hyg_1__boxed_119_);
v_r_121_ = lean_box_uint64(v_res_120_);
return v_r_121_;
}
}
LEAN_EXPORT lean_object* l_Float32_toUSize___boxed(lean_object* v_a_00___x40___internal___hyg_123_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_124_; size_t v_res_125_; lean_object* v_r_126_; 
v_a_00___x40___internal___hyg_1__boxed_124_ = lean_unbox_float32(v_a_00___x40___internal___hyg_123_);
lean_dec_ref(v_a_00___x40___internal___hyg_123_);
v_res_125_ = lean_float32_to_usize(v_a_00___x40___internal___hyg_1__boxed_124_);
v_r_126_ = lean_box_usize(v_res_125_);
return v_r_126_;
}
}
LEAN_EXPORT lean_object* l_Float32_isNaN___boxed(lean_object* v_a_00___x40___internal___hyg_128_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_129_; uint8_t v_res_130_; lean_object* v_r_131_; 
v_a_00___x40___internal___hyg_1__boxed_129_ = lean_unbox_float32(v_a_00___x40___internal___hyg_128_);
lean_dec_ref(v_a_00___x40___internal___hyg_128_);
v_res_130_ = lean_float32_isnan(v_a_00___x40___internal___hyg_1__boxed_129_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT lean_object* l_Float32_isFinite___boxed(lean_object* v_a_00___x40___internal___hyg_133_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_134_; uint8_t v_res_135_; lean_object* v_r_136_; 
v_a_00___x40___internal___hyg_1__boxed_134_ = lean_unbox_float32(v_a_00___x40___internal___hyg_133_);
lean_dec_ref(v_a_00___x40___internal___hyg_133_);
v_res_135_ = lean_float32_isfinite(v_a_00___x40___internal___hyg_1__boxed_134_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT lean_object* l_Float32_isInf___boxed(lean_object* v_a_00___x40___internal___hyg_138_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_139_; uint8_t v_res_140_; lean_object* v_r_141_; 
v_a_00___x40___internal___hyg_1__boxed_139_ = lean_unbox_float32(v_a_00___x40___internal___hyg_138_);
lean_dec_ref(v_a_00___x40___internal___hyg_138_);
v_res_140_ = lean_float32_isinf(v_a_00___x40___internal___hyg_1__boxed_139_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
LEAN_EXPORT lean_object* l_Float32_frExp___boxed(lean_object* v_a_00___x40___internal___hyg_143_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_144_; lean_object* v_res_145_; 
v_a_00___x40___internal___hyg_1__boxed_144_ = lean_unbox_float32(v_a_00___x40___internal___hyg_143_);
lean_dec_ref(v_a_00___x40___internal___hyg_143_);
v_res_145_ = lean_float32_frexp(v_a_00___x40___internal___hyg_1__boxed_144_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_UInt8_toFloat32___boxed(lean_object* v_n_149_){
_start:
{
uint8_t v_n_boxed_150_; float v_res_151_; lean_object* v_r_152_; 
v_n_boxed_150_ = lean_unbox(v_n_149_);
v_res_151_ = lean_uint8_to_float32(v_n_boxed_150_);
v_r_152_ = lean_box_float32(v_res_151_);
return v_r_152_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toFloat32___boxed(lean_object* v_n_154_){
_start:
{
uint16_t v_n_boxed_155_; float v_res_156_; lean_object* v_r_157_; 
v_n_boxed_155_ = lean_unbox(v_n_154_);
v_res_156_ = lean_uint16_to_float32(v_n_boxed_155_);
v_r_157_ = lean_box_float32(v_res_156_);
return v_r_157_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toFloat32___boxed(lean_object* v_n_159_){
_start:
{
uint32_t v_n_boxed_160_; float v_res_161_; lean_object* v_r_162_; 
v_n_boxed_160_ = lean_unbox_uint32(v_n_159_);
lean_dec(v_n_159_);
v_res_161_ = lean_uint32_to_float32(v_n_boxed_160_);
v_r_162_ = lean_box_float32(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toFloat32___boxed(lean_object* v_n_164_){
_start:
{
uint64_t v_n_boxed_165_; float v_res_166_; lean_object* v_r_167_; 
v_n_boxed_165_ = lean_unbox_uint64(v_n_164_);
lean_dec_ref(v_n_164_);
v_res_166_ = lean_uint64_to_float32(v_n_boxed_165_);
v_r_167_ = lean_box_float32(v_res_166_);
return v_r_167_;
}
}
LEAN_EXPORT lean_object* l_USize_toFloat32___boxed(lean_object* v_n_169_){
_start:
{
size_t v_n_boxed_170_; float v_res_171_; lean_object* v_r_172_; 
v_n_boxed_170_ = lean_unbox_usize(v_n_169_);
lean_dec(v_n_169_);
v_res_171_ = lean_usize_to_float32(v_n_boxed_170_);
v_r_172_ = lean_box_float32(v_res_171_);
return v_r_172_;
}
}
static float _init_l_instInhabitedFloat32___closed__0(void){
_start:
{
uint64_t v___x_173_; float v___x_174_; 
v___x_173_ = 0ULL;
v___x_174_ = lean_uint64_to_float32(v___x_173_);
return v___x_174_;
}
}
static float _init_l_instInhabitedFloat32(void){
_start:
{
float v___x_175_; 
v___x_175_ = lean_float32_once(&l_instInhabitedFloat32___closed__0, &l_instInhabitedFloat32___closed__0_once, _init_l_instInhabitedFloat32___closed__0);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Float32_repr(float v_n_176_, lean_object* v_prec_177_){
_start:
{
float v___x_178_; uint8_t v___x_179_; 
v___x_178_ = lean_float32_once(&l_instInhabitedFloat32___closed__0, &l_instInhabitedFloat32___closed__0_once, _init_l_instInhabitedFloat32___closed__0);
v___x_179_ = lean_float32_decLt(v_n_176_, v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_float32_to_string(v_n_176_);
v___x_181_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
return v___x_181_;
}
else
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_182_ = lean_float32_to_string(v_n_176_);
v___x_183_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
v___x_184_ = l_Repr_addAppParen(v___x_183_, v_prec_177_);
return v___x_184_;
}
}
}
LEAN_EXPORT lean_object* l_Float32_repr___boxed(lean_object* v_n_185_, lean_object* v_prec_186_){
_start:
{
float v_n_boxed_187_; lean_object* v_res_188_; 
v_n_boxed_187_ = lean_unbox_float32(v_n_185_);
lean_dec_ref(v_n_185_);
v_res_188_ = l_Float32_repr(v_n_boxed_187_, v_prec_186_);
lean_dec(v_prec_186_);
return v_res_188_;
}
}
static lean_object* _init_l_instReprAtomFloat32(void){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = lean_box(0);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Float32_sin___boxed(lean_object* v_a_00___x40___internal___hyg_193_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_194_; float v_res_195_; lean_object* v_r_196_; 
v_a_00___x40___internal___hyg_1__boxed_194_ = lean_unbox_float32(v_a_00___x40___internal___hyg_193_);
lean_dec_ref(v_a_00___x40___internal___hyg_193_);
v_res_195_ = sinf(v_a_00___x40___internal___hyg_1__boxed_194_);
v_r_196_ = lean_box_float32(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT lean_object* l_Float32_cos___boxed(lean_object* v_a_00___x40___internal___hyg_198_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_199_; float v_res_200_; lean_object* v_r_201_; 
v_a_00___x40___internal___hyg_1__boxed_199_ = lean_unbox_float32(v_a_00___x40___internal___hyg_198_);
lean_dec_ref(v_a_00___x40___internal___hyg_198_);
v_res_200_ = cosf(v_a_00___x40___internal___hyg_1__boxed_199_);
v_r_201_ = lean_box_float32(v_res_200_);
return v_r_201_;
}
}
LEAN_EXPORT lean_object* l_Float32_tan___boxed(lean_object* v_a_00___x40___internal___hyg_203_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_204_; float v_res_205_; lean_object* v_r_206_; 
v_a_00___x40___internal___hyg_1__boxed_204_ = lean_unbox_float32(v_a_00___x40___internal___hyg_203_);
lean_dec_ref(v_a_00___x40___internal___hyg_203_);
v_res_205_ = tanf(v_a_00___x40___internal___hyg_1__boxed_204_);
v_r_206_ = lean_box_float32(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT lean_object* l_Float32_asin___boxed(lean_object* v_a_00___x40___internal___hyg_208_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_209_; float v_res_210_; lean_object* v_r_211_; 
v_a_00___x40___internal___hyg_1__boxed_209_ = lean_unbox_float32(v_a_00___x40___internal___hyg_208_);
lean_dec_ref(v_a_00___x40___internal___hyg_208_);
v_res_210_ = asinf(v_a_00___x40___internal___hyg_1__boxed_209_);
v_r_211_ = lean_box_float32(v_res_210_);
return v_r_211_;
}
}
LEAN_EXPORT lean_object* l_Float32_acos___boxed(lean_object* v_a_00___x40___internal___hyg_213_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_214_; float v_res_215_; lean_object* v_r_216_; 
v_a_00___x40___internal___hyg_1__boxed_214_ = lean_unbox_float32(v_a_00___x40___internal___hyg_213_);
lean_dec_ref(v_a_00___x40___internal___hyg_213_);
v_res_215_ = acosf(v_a_00___x40___internal___hyg_1__boxed_214_);
v_r_216_ = lean_box_float32(v_res_215_);
return v_r_216_;
}
}
LEAN_EXPORT lean_object* l_Float32_atan___boxed(lean_object* v_a_00___x40___internal___hyg_218_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_219_; float v_res_220_; lean_object* v_r_221_; 
v_a_00___x40___internal___hyg_1__boxed_219_ = lean_unbox_float32(v_a_00___x40___internal___hyg_218_);
lean_dec_ref(v_a_00___x40___internal___hyg_218_);
v_res_220_ = atanf(v_a_00___x40___internal___hyg_1__boxed_219_);
v_r_221_ = lean_box_float32(v_res_220_);
return v_r_221_;
}
}
LEAN_EXPORT lean_object* l_Float32_atan2___boxed(lean_object* v_a_00___x40___internal___hyg_224_, lean_object* v_a_00___x40___internal___hyg_225_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_226_; float v_a_00___x40___internal___hyg_2__boxed_227_; float v_res_228_; lean_object* v_r_229_; 
v_a_00___x40___internal___hyg_1__boxed_226_ = lean_unbox_float32(v_a_00___x40___internal___hyg_224_);
lean_dec_ref(v_a_00___x40___internal___hyg_224_);
v_a_00___x40___internal___hyg_2__boxed_227_ = lean_unbox_float32(v_a_00___x40___internal___hyg_225_);
lean_dec_ref(v_a_00___x40___internal___hyg_225_);
v_res_228_ = atan2f(v_a_00___x40___internal___hyg_1__boxed_226_, v_a_00___x40___internal___hyg_2__boxed_227_);
v_r_229_ = lean_box_float32(v_res_228_);
return v_r_229_;
}
}
LEAN_EXPORT lean_object* l_Float32_sinh___boxed(lean_object* v_a_00___x40___internal___hyg_231_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_232_; float v_res_233_; lean_object* v_r_234_; 
v_a_00___x40___internal___hyg_1__boxed_232_ = lean_unbox_float32(v_a_00___x40___internal___hyg_231_);
lean_dec_ref(v_a_00___x40___internal___hyg_231_);
v_res_233_ = sinhf(v_a_00___x40___internal___hyg_1__boxed_232_);
v_r_234_ = lean_box_float32(v_res_233_);
return v_r_234_;
}
}
LEAN_EXPORT lean_object* l_Float32_cosh___boxed(lean_object* v_a_00___x40___internal___hyg_236_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_237_; float v_res_238_; lean_object* v_r_239_; 
v_a_00___x40___internal___hyg_1__boxed_237_ = lean_unbox_float32(v_a_00___x40___internal___hyg_236_);
lean_dec_ref(v_a_00___x40___internal___hyg_236_);
v_res_238_ = coshf(v_a_00___x40___internal___hyg_1__boxed_237_);
v_r_239_ = lean_box_float32(v_res_238_);
return v_r_239_;
}
}
LEAN_EXPORT lean_object* l_Float32_tanh___boxed(lean_object* v_a_00___x40___internal___hyg_241_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_242_; float v_res_243_; lean_object* v_r_244_; 
v_a_00___x40___internal___hyg_1__boxed_242_ = lean_unbox_float32(v_a_00___x40___internal___hyg_241_);
lean_dec_ref(v_a_00___x40___internal___hyg_241_);
v_res_243_ = tanhf(v_a_00___x40___internal___hyg_1__boxed_242_);
v_r_244_ = lean_box_float32(v_res_243_);
return v_r_244_;
}
}
LEAN_EXPORT lean_object* l_Float32_asinh___boxed(lean_object* v_a_00___x40___internal___hyg_246_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_247_; float v_res_248_; lean_object* v_r_249_; 
v_a_00___x40___internal___hyg_1__boxed_247_ = lean_unbox_float32(v_a_00___x40___internal___hyg_246_);
lean_dec_ref(v_a_00___x40___internal___hyg_246_);
v_res_248_ = asinhf(v_a_00___x40___internal___hyg_1__boxed_247_);
v_r_249_ = lean_box_float32(v_res_248_);
return v_r_249_;
}
}
LEAN_EXPORT lean_object* l_Float32_acosh___boxed(lean_object* v_a_00___x40___internal___hyg_251_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_252_; float v_res_253_; lean_object* v_r_254_; 
v_a_00___x40___internal___hyg_1__boxed_252_ = lean_unbox_float32(v_a_00___x40___internal___hyg_251_);
lean_dec_ref(v_a_00___x40___internal___hyg_251_);
v_res_253_ = acoshf(v_a_00___x40___internal___hyg_1__boxed_252_);
v_r_254_ = lean_box_float32(v_res_253_);
return v_r_254_;
}
}
LEAN_EXPORT lean_object* l_Float32_atanh___boxed(lean_object* v_a_00___x40___internal___hyg_256_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_257_; float v_res_258_; lean_object* v_r_259_; 
v_a_00___x40___internal___hyg_1__boxed_257_ = lean_unbox_float32(v_a_00___x40___internal___hyg_256_);
lean_dec_ref(v_a_00___x40___internal___hyg_256_);
v_res_258_ = atanhf(v_a_00___x40___internal___hyg_1__boxed_257_);
v_r_259_ = lean_box_float32(v_res_258_);
return v_r_259_;
}
}
LEAN_EXPORT lean_object* l_Float32_exp___boxed(lean_object* v_a_00___x40___internal___hyg_261_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_262_; float v_res_263_; lean_object* v_r_264_; 
v_a_00___x40___internal___hyg_1__boxed_262_ = lean_unbox_float32(v_a_00___x40___internal___hyg_261_);
lean_dec_ref(v_a_00___x40___internal___hyg_261_);
v_res_263_ = expf(v_a_00___x40___internal___hyg_1__boxed_262_);
v_r_264_ = lean_box_float32(v_res_263_);
return v_r_264_;
}
}
LEAN_EXPORT lean_object* l_Float32_exp2___boxed(lean_object* v_a_00___x40___internal___hyg_266_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_267_; float v_res_268_; lean_object* v_r_269_; 
v_a_00___x40___internal___hyg_1__boxed_267_ = lean_unbox_float32(v_a_00___x40___internal___hyg_266_);
lean_dec_ref(v_a_00___x40___internal___hyg_266_);
v_res_268_ = exp2f(v_a_00___x40___internal___hyg_1__boxed_267_);
v_r_269_ = lean_box_float32(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT lean_object* l_Float32_log___boxed(lean_object* v_a_00___x40___internal___hyg_271_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_272_; float v_res_273_; lean_object* v_r_274_; 
v_a_00___x40___internal___hyg_1__boxed_272_ = lean_unbox_float32(v_a_00___x40___internal___hyg_271_);
lean_dec_ref(v_a_00___x40___internal___hyg_271_);
v_res_273_ = logf(v_a_00___x40___internal___hyg_1__boxed_272_);
v_r_274_ = lean_box_float32(v_res_273_);
return v_r_274_;
}
}
LEAN_EXPORT lean_object* l_Float32_log2___boxed(lean_object* v_a_00___x40___internal___hyg_276_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_277_; float v_res_278_; lean_object* v_r_279_; 
v_a_00___x40___internal___hyg_1__boxed_277_ = lean_unbox_float32(v_a_00___x40___internal___hyg_276_);
lean_dec_ref(v_a_00___x40___internal___hyg_276_);
v_res_278_ = log2f(v_a_00___x40___internal___hyg_1__boxed_277_);
v_r_279_ = lean_box_float32(v_res_278_);
return v_r_279_;
}
}
LEAN_EXPORT lean_object* l_Float32_log10___boxed(lean_object* v_a_00___x40___internal___hyg_281_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_282_; float v_res_283_; lean_object* v_r_284_; 
v_a_00___x40___internal___hyg_1__boxed_282_ = lean_unbox_float32(v_a_00___x40___internal___hyg_281_);
lean_dec_ref(v_a_00___x40___internal___hyg_281_);
v_res_283_ = log10f(v_a_00___x40___internal___hyg_1__boxed_282_);
v_r_284_ = lean_box_float32(v_res_283_);
return v_r_284_;
}
}
LEAN_EXPORT lean_object* l_Float32_pow___boxed(lean_object* v_a_00___x40___internal___hyg_287_, lean_object* v_a_00___x40___internal___hyg_288_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_289_; float v_a_00___x40___internal___hyg_2__boxed_290_; float v_res_291_; lean_object* v_r_292_; 
v_a_00___x40___internal___hyg_1__boxed_289_ = lean_unbox_float32(v_a_00___x40___internal___hyg_287_);
lean_dec_ref(v_a_00___x40___internal___hyg_287_);
v_a_00___x40___internal___hyg_2__boxed_290_ = lean_unbox_float32(v_a_00___x40___internal___hyg_288_);
lean_dec_ref(v_a_00___x40___internal___hyg_288_);
v_res_291_ = powf(v_a_00___x40___internal___hyg_1__boxed_289_, v_a_00___x40___internal___hyg_2__boxed_290_);
v_r_292_ = lean_box_float32(v_res_291_);
return v_r_292_;
}
}
LEAN_EXPORT lean_object* l_Float32_sqrt___boxed(lean_object* v_a_00___x40___internal___hyg_294_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_295_; float v_res_296_; lean_object* v_r_297_; 
v_a_00___x40___internal___hyg_1__boxed_295_ = lean_unbox_float32(v_a_00___x40___internal___hyg_294_);
lean_dec_ref(v_a_00___x40___internal___hyg_294_);
v_res_296_ = sqrtf(v_a_00___x40___internal___hyg_1__boxed_295_);
v_r_297_ = lean_box_float32(v_res_296_);
return v_r_297_;
}
}
LEAN_EXPORT lean_object* l_Float32_cbrt___boxed(lean_object* v_a_00___x40___internal___hyg_299_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_300_; float v_res_301_; lean_object* v_r_302_; 
v_a_00___x40___internal___hyg_1__boxed_300_ = lean_unbox_float32(v_a_00___x40___internal___hyg_299_);
lean_dec_ref(v_a_00___x40___internal___hyg_299_);
v_res_301_ = cbrtf(v_a_00___x40___internal___hyg_1__boxed_300_);
v_r_302_ = lean_box_float32(v_res_301_);
return v_r_302_;
}
}
LEAN_EXPORT lean_object* l_Float32_ceil___boxed(lean_object* v_a_00___x40___internal___hyg_304_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_305_; float v_res_306_; lean_object* v_r_307_; 
v_a_00___x40___internal___hyg_1__boxed_305_ = lean_unbox_float32(v_a_00___x40___internal___hyg_304_);
lean_dec_ref(v_a_00___x40___internal___hyg_304_);
v_res_306_ = ceilf(v_a_00___x40___internal___hyg_1__boxed_305_);
v_r_307_ = lean_box_float32(v_res_306_);
return v_r_307_;
}
}
LEAN_EXPORT lean_object* l_Float32_floor___boxed(lean_object* v_a_00___x40___internal___hyg_309_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_310_; float v_res_311_; lean_object* v_r_312_; 
v_a_00___x40___internal___hyg_1__boxed_310_ = lean_unbox_float32(v_a_00___x40___internal___hyg_309_);
lean_dec_ref(v_a_00___x40___internal___hyg_309_);
v_res_311_ = floorf(v_a_00___x40___internal___hyg_1__boxed_310_);
v_r_312_ = lean_box_float32(v_res_311_);
return v_r_312_;
}
}
LEAN_EXPORT lean_object* l_Float32_round___boxed(lean_object* v_a_00___x40___internal___hyg_314_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_315_; float v_res_316_; lean_object* v_r_317_; 
v_a_00___x40___internal___hyg_1__boxed_315_ = lean_unbox_float32(v_a_00___x40___internal___hyg_314_);
lean_dec_ref(v_a_00___x40___internal___hyg_314_);
v_res_316_ = roundf(v_a_00___x40___internal___hyg_1__boxed_315_);
v_r_317_ = lean_box_float32(v_res_316_);
return v_r_317_;
}
}
LEAN_EXPORT lean_object* l_Float32_abs___boxed(lean_object* v_a_00___x40___internal___hyg_319_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_320_; float v_res_321_; lean_object* v_r_322_; 
v_a_00___x40___internal___hyg_1__boxed_320_ = lean_unbox_float32(v_a_00___x40___internal___hyg_319_);
lean_dec_ref(v_a_00___x40___internal___hyg_319_);
v_res_321_ = fabsf(v_a_00___x40___internal___hyg_1__boxed_320_);
v_r_322_ = lean_box_float32(v_res_321_);
return v_r_322_;
}
}
LEAN_EXPORT float l_instMinFloat32___lam__0(float v_x_325_, float v_y_326_){
_start:
{
uint8_t v___x_327_; 
v___x_327_ = lean_float32_decLe(v_x_325_, v_y_326_);
if (v___x_327_ == 0)
{
return v_y_326_;
}
else
{
return v_x_325_;
}
}
}
LEAN_EXPORT lean_object* l_instMinFloat32___lam__0___boxed(lean_object* v_x_328_, lean_object* v_y_329_){
_start:
{
float v_x_boxed_330_; float v_y_boxed_331_; float v_res_332_; lean_object* v_r_333_; 
v_x_boxed_330_ = lean_unbox_float32(v_x_328_);
lean_dec_ref(v_x_328_);
v_y_boxed_331_ = lean_unbox_float32(v_y_329_);
lean_dec_ref(v_y_329_);
v_res_332_ = l_instMinFloat32___lam__0(v_x_boxed_330_, v_y_boxed_331_);
v_r_333_ = lean_box_float32(v_res_332_);
return v_r_333_;
}
}
LEAN_EXPORT float l_instMaxFloat32___lam__0(float v_x_336_, float v_y_337_){
_start:
{
uint8_t v___x_338_; 
v___x_338_ = lean_float32_decLe(v_x_336_, v_y_337_);
if (v___x_338_ == 0)
{
return v_x_336_;
}
else
{
return v_y_337_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxFloat32___lam__0___boxed(lean_object* v_x_339_, lean_object* v_y_340_){
_start:
{
float v_x_boxed_341_; float v_y_boxed_342_; float v_res_343_; lean_object* v_r_344_; 
v_x_boxed_341_ = lean_unbox_float32(v_x_339_);
lean_dec_ref(v_x_339_);
v_y_boxed_342_ = lean_unbox_float32(v_y_340_);
lean_dec_ref(v_y_340_);
v_res_343_ = l_instMaxFloat32___lam__0(v_x_boxed_341_, v_y_boxed_342_);
v_r_344_ = lean_box_float32(v_res_343_);
return v_r_344_;
}
}
LEAN_EXPORT lean_object* l_Float32_scaleB___boxed(lean_object* v_x_349_, lean_object* v_i_350_){
_start:
{
float v_x_boxed_351_; float v_res_352_; lean_object* v_r_353_; 
v_x_boxed_351_ = lean_unbox_float32(v_x_349_);
lean_dec_ref(v_x_349_);
v_res_352_ = lean_float32_scaleb(v_x_boxed_351_, v_i_350_);
lean_dec(v_i_350_);
v_r_353_ = lean_box_float32(v_res_352_);
return v_r_353_;
}
}
LEAN_EXPORT lean_object* l_Float32_toFloat___boxed(lean_object* v_a_00___x40___internal___hyg_355_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_356_; double v_res_357_; lean_object* v_r_358_; 
v_a_00___x40___internal___hyg_1__boxed_356_ = lean_unbox_float32(v_a_00___x40___internal___hyg_355_);
lean_dec_ref(v_a_00___x40___internal___hyg_355_);
v_res_357_ = lean_float32_to_float(v_a_00___x40___internal___hyg_1__boxed_356_);
v_r_358_ = lean_box_float(v_res_357_);
return v_r_358_;
}
}
LEAN_EXPORT lean_object* l_Float_toFloat32___boxed(lean_object* v_a_00___x40___internal___hyg_360_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_361_; float v_res_362_; lean_object* v_r_363_; 
v_a_00___x40___internal___hyg_1__boxed_361_ = lean_unbox_float(v_a_00___x40___internal___hyg_360_);
lean_dec_ref(v_a_00___x40___internal___hyg_360_);
v_res_362_ = lean_float_to_float32(v_a_00___x40___internal___hyg_1__boxed_361_);
v_r_363_ = lean_box_float32(v_res_362_);
return v_r_363_;
}
}
lean_object* runtime_initialize_Init_Data_Float(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float32(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Float(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_float32Spec = _init_l_float32Spec();
lean_mark_persistent(l_float32Spec);
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
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Float32(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Float(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Float32(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Float32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Float32(builtin);
}
#ifdef __cplusplus
}
#endif
