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
LEAN_EXPORT uint8_t l_float32Spec___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_float32Spec___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_float32Spec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_float32Spec___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
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
LEAN_EXPORT uint8_t l_float32Spec___lam__0(uint8_t v___x_1_, lean_object* v_x_2_, lean_object* v_x_3_){
_start:
{
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_float32Spec___lam__0___boxed(lean_object* v___x_4_, lean_object* v_x_5_, lean_object* v_x_6_){
_start:
{
uint8_t v___x_13__boxed_7_; uint8_t v_res_8_; lean_object* v_r_9_; 
v___x_13__boxed_7_ = lean_unbox(v___x_4_);
v_res_8_ = l_float32Spec___lam__0(v___x_13__boxed_7_, v_x_5_, v_x_6_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
static lean_object* _init_l_float32Spec___closed__1(void){
_start:
{
lean_object* v___f_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___f_13_ = ((lean_object*)(l_float32Spec___closed__0));
v___x_14_ = lean_box(0);
v___x_15_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
lean_ctor_set(v___x_15_, 1, v___f_13_);
lean_ctor_set(v___x_15_, 2, v___f_13_);
return v___x_15_;
}
}
static lean_object* _init_l_float32Spec(void){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_obj_once(&l_float32Spec___closed__1, &l_float32Spec___closed__1_once, _init_l_float32Spec___closed__1);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Float32_add___boxed(lean_object* v_a_00___x40___internal___hyg_19_, lean_object* v_a_00___x40___internal___hyg_20_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_21_; float v_a_00___x40___internal___hyg_2__boxed_22_; float v_res_23_; lean_object* v_r_24_; 
v_a_00___x40___internal___hyg_1__boxed_21_ = lean_unbox_float32(v_a_00___x40___internal___hyg_19_);
lean_dec_ref(v_a_00___x40___internal___hyg_19_);
v_a_00___x40___internal___hyg_2__boxed_22_ = lean_unbox_float32(v_a_00___x40___internal___hyg_20_);
lean_dec_ref(v_a_00___x40___internal___hyg_20_);
v_res_23_ = lean_float32_add(v_a_00___x40___internal___hyg_1__boxed_21_, v_a_00___x40___internal___hyg_2__boxed_22_);
v_r_24_ = lean_box_float32(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT lean_object* l_Float32_sub___boxed(lean_object* v_a_00___x40___internal___hyg_27_, lean_object* v_a_00___x40___internal___hyg_28_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_29_; float v_a_00___x40___internal___hyg_2__boxed_30_; float v_res_31_; lean_object* v_r_32_; 
v_a_00___x40___internal___hyg_1__boxed_29_ = lean_unbox_float32(v_a_00___x40___internal___hyg_27_);
lean_dec_ref(v_a_00___x40___internal___hyg_27_);
v_a_00___x40___internal___hyg_2__boxed_30_ = lean_unbox_float32(v_a_00___x40___internal___hyg_28_);
lean_dec_ref(v_a_00___x40___internal___hyg_28_);
v_res_31_ = lean_float32_sub(v_a_00___x40___internal___hyg_1__boxed_29_, v_a_00___x40___internal___hyg_2__boxed_30_);
v_r_32_ = lean_box_float32(v_res_31_);
return v_r_32_;
}
}
LEAN_EXPORT lean_object* l_Float32_mul___boxed(lean_object* v_a_00___x40___internal___hyg_35_, lean_object* v_a_00___x40___internal___hyg_36_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_37_; float v_a_00___x40___internal___hyg_2__boxed_38_; float v_res_39_; lean_object* v_r_40_; 
v_a_00___x40___internal___hyg_1__boxed_37_ = lean_unbox_float32(v_a_00___x40___internal___hyg_35_);
lean_dec_ref(v_a_00___x40___internal___hyg_35_);
v_a_00___x40___internal___hyg_2__boxed_38_ = lean_unbox_float32(v_a_00___x40___internal___hyg_36_);
lean_dec_ref(v_a_00___x40___internal___hyg_36_);
v_res_39_ = lean_float32_mul(v_a_00___x40___internal___hyg_1__boxed_37_, v_a_00___x40___internal___hyg_2__boxed_38_);
v_r_40_ = lean_box_float32(v_res_39_);
return v_r_40_;
}
}
LEAN_EXPORT lean_object* l_Float32_div___boxed(lean_object* v_a_00___x40___internal___hyg_43_, lean_object* v_a_00___x40___internal___hyg_44_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_45_; float v_a_00___x40___internal___hyg_2__boxed_46_; float v_res_47_; lean_object* v_r_48_; 
v_a_00___x40___internal___hyg_1__boxed_45_ = lean_unbox_float32(v_a_00___x40___internal___hyg_43_);
lean_dec_ref(v_a_00___x40___internal___hyg_43_);
v_a_00___x40___internal___hyg_2__boxed_46_ = lean_unbox_float32(v_a_00___x40___internal___hyg_44_);
lean_dec_ref(v_a_00___x40___internal___hyg_44_);
v_res_47_ = lean_float32_div(v_a_00___x40___internal___hyg_1__boxed_45_, v_a_00___x40___internal___hyg_2__boxed_46_);
v_r_48_ = lean_box_float32(v_res_47_);
return v_r_48_;
}
}
LEAN_EXPORT lean_object* l_Float32_neg___boxed(lean_object* v_a_00___x40___internal___hyg_50_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_51_; float v_res_52_; lean_object* v_r_53_; 
v_a_00___x40___internal___hyg_1__boxed_51_ = lean_unbox_float32(v_a_00___x40___internal___hyg_50_);
lean_dec_ref(v_a_00___x40___internal___hyg_50_);
v_res_52_ = lean_float32_negate(v_a_00___x40___internal___hyg_1__boxed_51_);
v_r_53_ = lean_box_float32(v_res_52_);
return v_r_53_;
}
}
LEAN_EXPORT lean_object* l_Float32_ofBits___boxed(lean_object* v_a_00___x40___internal___hyg_55_){
_start:
{
uint32_t v_a_00___x40___internal___hyg_1__boxed_56_; float v_res_57_; lean_object* v_r_58_; 
v_a_00___x40___internal___hyg_1__boxed_56_ = lean_unbox_uint32(v_a_00___x40___internal___hyg_55_);
lean_dec(v_a_00___x40___internal___hyg_55_);
v_res_57_ = lean_float32_of_bits(v_a_00___x40___internal___hyg_1__boxed_56_);
v_r_58_ = lean_box_float32(v_res_57_);
return v_r_58_;
}
}
LEAN_EXPORT lean_object* l_Float32_toBits___boxed(lean_object* v_a_00___x40___internal___hyg_60_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_61_; uint32_t v_res_62_; lean_object* v_r_63_; 
v_a_00___x40___internal___hyg_1__boxed_61_ = lean_unbox_float32(v_a_00___x40___internal___hyg_60_);
lean_dec_ref(v_a_00___x40___internal___hyg_60_);
v_res_62_ = lean_float32_to_bits(v_a_00___x40___internal___hyg_1__boxed_61_);
v_r_63_ = lean_box_uint32(v_res_62_);
return v_r_63_;
}
}
static lean_object* _init_l_instLTFloat32(void){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_box(0);
return v___x_74_;
}
}
static lean_object* _init_l_instLEFloat32(void){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_box(0);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Float32_beq___boxed(lean_object* v_a_78_, lean_object* v_b_79_){
_start:
{
float v_a_boxed_80_; float v_b_boxed_81_; uint8_t v_res_82_; lean_object* v_r_83_; 
v_a_boxed_80_ = lean_unbox_float32(v_a_78_);
lean_dec_ref(v_a_78_);
v_b_boxed_81_ = lean_unbox_float32(v_b_79_);
lean_dec_ref(v_b_79_);
v_res_82_ = lean_float32_beq(v_a_boxed_80_, v_b_boxed_81_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT lean_object* l_Float32_decLt___boxed(lean_object* v_a_88_, lean_object* v_b_89_){
_start:
{
float v_a_boxed_90_; float v_b_boxed_91_; uint8_t v_res_92_; lean_object* v_r_93_; 
v_a_boxed_90_ = lean_unbox_float32(v_a_88_);
lean_dec_ref(v_a_88_);
v_b_boxed_91_ = lean_unbox_float32(v_b_89_);
lean_dec_ref(v_b_89_);
v_res_92_ = lean_float32_decLt(v_a_boxed_90_, v_b_boxed_91_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
LEAN_EXPORT lean_object* l_Float32_decLe___boxed(lean_object* v_a_96_, lean_object* v_b_97_){
_start:
{
float v_a_boxed_98_; float v_b_boxed_99_; uint8_t v_res_100_; lean_object* v_r_101_; 
v_a_boxed_98_ = lean_unbox_float32(v_a_96_);
lean_dec_ref(v_a_96_);
v_b_boxed_99_ = lean_unbox_float32(v_b_97_);
lean_dec_ref(v_b_97_);
v_res_100_ = lean_float32_decLe(v_a_boxed_98_, v_b_boxed_99_);
v_r_101_ = lean_box(v_res_100_);
return v_r_101_;
}
}
LEAN_EXPORT lean_object* l_Float32_toString___boxed(lean_object* v_a_00___x40___internal___hyg_103_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_104_; lean_object* v_res_105_; 
v_a_00___x40___internal___hyg_1__boxed_104_ = lean_unbox_float32(v_a_00___x40___internal___hyg_103_);
lean_dec_ref(v_a_00___x40___internal___hyg_103_);
v_res_105_ = lean_float32_to_string(v_a_00___x40___internal___hyg_1__boxed_104_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Float32_toUInt8___boxed(lean_object* v_a_00___x40___internal___hyg_107_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_108_; uint8_t v_res_109_; lean_object* v_r_110_; 
v_a_00___x40___internal___hyg_1__boxed_108_ = lean_unbox_float32(v_a_00___x40___internal___hyg_107_);
lean_dec_ref(v_a_00___x40___internal___hyg_107_);
v_res_109_ = lean_float32_to_uint8(v_a_00___x40___internal___hyg_1__boxed_108_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT lean_object* l_Float32_toUInt16___boxed(lean_object* v_a_00___x40___internal___hyg_112_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_113_; uint16_t v_res_114_; lean_object* v_r_115_; 
v_a_00___x40___internal___hyg_1__boxed_113_ = lean_unbox_float32(v_a_00___x40___internal___hyg_112_);
lean_dec_ref(v_a_00___x40___internal___hyg_112_);
v_res_114_ = lean_float32_to_uint16(v_a_00___x40___internal___hyg_1__boxed_113_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT lean_object* l_Float32_toUInt32___boxed(lean_object* v_a_00___x40___internal___hyg_117_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_118_; uint32_t v_res_119_; lean_object* v_r_120_; 
v_a_00___x40___internal___hyg_1__boxed_118_ = lean_unbox_float32(v_a_00___x40___internal___hyg_117_);
lean_dec_ref(v_a_00___x40___internal___hyg_117_);
v_res_119_ = lean_float32_to_uint32(v_a_00___x40___internal___hyg_1__boxed_118_);
v_r_120_ = lean_box_uint32(v_res_119_);
return v_r_120_;
}
}
LEAN_EXPORT lean_object* l_Float32_toUInt64___boxed(lean_object* v_a_00___x40___internal___hyg_122_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_123_; uint64_t v_res_124_; lean_object* v_r_125_; 
v_a_00___x40___internal___hyg_1__boxed_123_ = lean_unbox_float32(v_a_00___x40___internal___hyg_122_);
lean_dec_ref(v_a_00___x40___internal___hyg_122_);
v_res_124_ = lean_float32_to_uint64(v_a_00___x40___internal___hyg_1__boxed_123_);
v_r_125_ = lean_box_uint64(v_res_124_);
return v_r_125_;
}
}
LEAN_EXPORT lean_object* l_Float32_toUSize___boxed(lean_object* v_a_00___x40___internal___hyg_127_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_128_; size_t v_res_129_; lean_object* v_r_130_; 
v_a_00___x40___internal___hyg_1__boxed_128_ = lean_unbox_float32(v_a_00___x40___internal___hyg_127_);
lean_dec_ref(v_a_00___x40___internal___hyg_127_);
v_res_129_ = lean_float32_to_usize(v_a_00___x40___internal___hyg_1__boxed_128_);
v_r_130_ = lean_box_usize(v_res_129_);
return v_r_130_;
}
}
LEAN_EXPORT lean_object* l_Float32_isNaN___boxed(lean_object* v_a_00___x40___internal___hyg_132_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_133_; uint8_t v_res_134_; lean_object* v_r_135_; 
v_a_00___x40___internal___hyg_1__boxed_133_ = lean_unbox_float32(v_a_00___x40___internal___hyg_132_);
lean_dec_ref(v_a_00___x40___internal___hyg_132_);
v_res_134_ = lean_float32_isnan(v_a_00___x40___internal___hyg_1__boxed_133_);
v_r_135_ = lean_box(v_res_134_);
return v_r_135_;
}
}
LEAN_EXPORT lean_object* l_Float32_isFinite___boxed(lean_object* v_a_00___x40___internal___hyg_137_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_138_; uint8_t v_res_139_; lean_object* v_r_140_; 
v_a_00___x40___internal___hyg_1__boxed_138_ = lean_unbox_float32(v_a_00___x40___internal___hyg_137_);
lean_dec_ref(v_a_00___x40___internal___hyg_137_);
v_res_139_ = lean_float32_isfinite(v_a_00___x40___internal___hyg_1__boxed_138_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT lean_object* l_Float32_isInf___boxed(lean_object* v_a_00___x40___internal___hyg_142_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_143_; uint8_t v_res_144_; lean_object* v_r_145_; 
v_a_00___x40___internal___hyg_1__boxed_143_ = lean_unbox_float32(v_a_00___x40___internal___hyg_142_);
lean_dec_ref(v_a_00___x40___internal___hyg_142_);
v_res_144_ = lean_float32_isinf(v_a_00___x40___internal___hyg_1__boxed_143_);
v_r_145_ = lean_box(v_res_144_);
return v_r_145_;
}
}
LEAN_EXPORT lean_object* l_Float32_frExp___boxed(lean_object* v_a_00___x40___internal___hyg_147_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_148_; lean_object* v_res_149_; 
v_a_00___x40___internal___hyg_1__boxed_148_ = lean_unbox_float32(v_a_00___x40___internal___hyg_147_);
lean_dec_ref(v_a_00___x40___internal___hyg_147_);
v_res_149_ = lean_float32_frexp(v_a_00___x40___internal___hyg_1__boxed_148_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_UInt8_toFloat32___boxed(lean_object* v_n_153_){
_start:
{
uint8_t v_n_boxed_154_; float v_res_155_; lean_object* v_r_156_; 
v_n_boxed_154_ = lean_unbox(v_n_153_);
v_res_155_ = lean_uint8_to_float32(v_n_boxed_154_);
v_r_156_ = lean_box_float32(v_res_155_);
return v_r_156_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toFloat32___boxed(lean_object* v_n_158_){
_start:
{
uint16_t v_n_boxed_159_; float v_res_160_; lean_object* v_r_161_; 
v_n_boxed_159_ = lean_unbox(v_n_158_);
v_res_160_ = lean_uint16_to_float32(v_n_boxed_159_);
v_r_161_ = lean_box_float32(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toFloat32___boxed(lean_object* v_n_163_){
_start:
{
uint32_t v_n_boxed_164_; float v_res_165_; lean_object* v_r_166_; 
v_n_boxed_164_ = lean_unbox_uint32(v_n_163_);
lean_dec(v_n_163_);
v_res_165_ = lean_uint32_to_float32(v_n_boxed_164_);
v_r_166_ = lean_box_float32(v_res_165_);
return v_r_166_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toFloat32___boxed(lean_object* v_n_168_){
_start:
{
uint64_t v_n_boxed_169_; float v_res_170_; lean_object* v_r_171_; 
v_n_boxed_169_ = lean_unbox_uint64(v_n_168_);
lean_dec_ref(v_n_168_);
v_res_170_ = lean_uint64_to_float32(v_n_boxed_169_);
v_r_171_ = lean_box_float32(v_res_170_);
return v_r_171_;
}
}
LEAN_EXPORT lean_object* l_USize_toFloat32___boxed(lean_object* v_n_173_){
_start:
{
size_t v_n_boxed_174_; float v_res_175_; lean_object* v_r_176_; 
v_n_boxed_174_ = lean_unbox_usize(v_n_173_);
lean_dec(v_n_173_);
v_res_175_ = lean_usize_to_float32(v_n_boxed_174_);
v_r_176_ = lean_box_float32(v_res_175_);
return v_r_176_;
}
}
static float _init_l_instInhabitedFloat32___closed__0(void){
_start:
{
uint64_t v___x_177_; float v___x_178_; 
v___x_177_ = 0ULL;
v___x_178_ = lean_uint64_to_float32(v___x_177_);
return v___x_178_;
}
}
static float _init_l_instInhabitedFloat32(void){
_start:
{
float v___x_179_; 
v___x_179_ = lean_float32_once(&l_instInhabitedFloat32___closed__0, &l_instInhabitedFloat32___closed__0_once, _init_l_instInhabitedFloat32___closed__0);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Float32_repr(float v_n_180_, lean_object* v_prec_181_){
_start:
{
float v___x_182_; uint8_t v___x_183_; 
v___x_182_ = lean_float32_once(&l_instInhabitedFloat32___closed__0, &l_instInhabitedFloat32___closed__0_once, _init_l_instInhabitedFloat32___closed__0);
v___x_183_ = lean_float32_decLt(v_n_180_, v___x_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_float32_to_string(v_n_180_);
v___x_185_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
return v___x_185_;
}
else
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_float32_to_string(v_n_180_);
v___x_187_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
v___x_188_ = l_Repr_addAppParen(v___x_187_, v_prec_181_);
return v___x_188_;
}
}
}
LEAN_EXPORT lean_object* l_Float32_repr___boxed(lean_object* v_n_189_, lean_object* v_prec_190_){
_start:
{
float v_n_boxed_191_; lean_object* v_res_192_; 
v_n_boxed_191_ = lean_unbox_float32(v_n_189_);
lean_dec_ref(v_n_189_);
v_res_192_ = l_Float32_repr(v_n_boxed_191_, v_prec_190_);
lean_dec(v_prec_190_);
return v_res_192_;
}
}
static lean_object* _init_l_instReprAtomFloat32(void){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = lean_box(0);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Float32_sin___boxed(lean_object* v_a_00___x40___internal___hyg_197_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_198_; float v_res_199_; lean_object* v_r_200_; 
v_a_00___x40___internal___hyg_1__boxed_198_ = lean_unbox_float32(v_a_00___x40___internal___hyg_197_);
lean_dec_ref(v_a_00___x40___internal___hyg_197_);
v_res_199_ = sinf(v_a_00___x40___internal___hyg_1__boxed_198_);
v_r_200_ = lean_box_float32(v_res_199_);
return v_r_200_;
}
}
LEAN_EXPORT lean_object* l_Float32_cos___boxed(lean_object* v_a_00___x40___internal___hyg_202_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_203_; float v_res_204_; lean_object* v_r_205_; 
v_a_00___x40___internal___hyg_1__boxed_203_ = lean_unbox_float32(v_a_00___x40___internal___hyg_202_);
lean_dec_ref(v_a_00___x40___internal___hyg_202_);
v_res_204_ = cosf(v_a_00___x40___internal___hyg_1__boxed_203_);
v_r_205_ = lean_box_float32(v_res_204_);
return v_r_205_;
}
}
LEAN_EXPORT lean_object* l_Float32_tan___boxed(lean_object* v_a_00___x40___internal___hyg_207_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_208_; float v_res_209_; lean_object* v_r_210_; 
v_a_00___x40___internal___hyg_1__boxed_208_ = lean_unbox_float32(v_a_00___x40___internal___hyg_207_);
lean_dec_ref(v_a_00___x40___internal___hyg_207_);
v_res_209_ = tanf(v_a_00___x40___internal___hyg_1__boxed_208_);
v_r_210_ = lean_box_float32(v_res_209_);
return v_r_210_;
}
}
LEAN_EXPORT lean_object* l_Float32_asin___boxed(lean_object* v_a_00___x40___internal___hyg_212_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_213_; float v_res_214_; lean_object* v_r_215_; 
v_a_00___x40___internal___hyg_1__boxed_213_ = lean_unbox_float32(v_a_00___x40___internal___hyg_212_);
lean_dec_ref(v_a_00___x40___internal___hyg_212_);
v_res_214_ = asinf(v_a_00___x40___internal___hyg_1__boxed_213_);
v_r_215_ = lean_box_float32(v_res_214_);
return v_r_215_;
}
}
LEAN_EXPORT lean_object* l_Float32_acos___boxed(lean_object* v_a_00___x40___internal___hyg_217_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_218_; float v_res_219_; lean_object* v_r_220_; 
v_a_00___x40___internal___hyg_1__boxed_218_ = lean_unbox_float32(v_a_00___x40___internal___hyg_217_);
lean_dec_ref(v_a_00___x40___internal___hyg_217_);
v_res_219_ = acosf(v_a_00___x40___internal___hyg_1__boxed_218_);
v_r_220_ = lean_box_float32(v_res_219_);
return v_r_220_;
}
}
LEAN_EXPORT lean_object* l_Float32_atan___boxed(lean_object* v_a_00___x40___internal___hyg_222_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_223_; float v_res_224_; lean_object* v_r_225_; 
v_a_00___x40___internal___hyg_1__boxed_223_ = lean_unbox_float32(v_a_00___x40___internal___hyg_222_);
lean_dec_ref(v_a_00___x40___internal___hyg_222_);
v_res_224_ = atanf(v_a_00___x40___internal___hyg_1__boxed_223_);
v_r_225_ = lean_box_float32(v_res_224_);
return v_r_225_;
}
}
LEAN_EXPORT lean_object* l_Float32_atan2___boxed(lean_object* v_a_00___x40___internal___hyg_228_, lean_object* v_a_00___x40___internal___hyg_229_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_230_; float v_a_00___x40___internal___hyg_2__boxed_231_; float v_res_232_; lean_object* v_r_233_; 
v_a_00___x40___internal___hyg_1__boxed_230_ = lean_unbox_float32(v_a_00___x40___internal___hyg_228_);
lean_dec_ref(v_a_00___x40___internal___hyg_228_);
v_a_00___x40___internal___hyg_2__boxed_231_ = lean_unbox_float32(v_a_00___x40___internal___hyg_229_);
lean_dec_ref(v_a_00___x40___internal___hyg_229_);
v_res_232_ = atan2f(v_a_00___x40___internal___hyg_1__boxed_230_, v_a_00___x40___internal___hyg_2__boxed_231_);
v_r_233_ = lean_box_float32(v_res_232_);
return v_r_233_;
}
}
LEAN_EXPORT lean_object* l_Float32_sinh___boxed(lean_object* v_a_00___x40___internal___hyg_235_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_236_; float v_res_237_; lean_object* v_r_238_; 
v_a_00___x40___internal___hyg_1__boxed_236_ = lean_unbox_float32(v_a_00___x40___internal___hyg_235_);
lean_dec_ref(v_a_00___x40___internal___hyg_235_);
v_res_237_ = sinhf(v_a_00___x40___internal___hyg_1__boxed_236_);
v_r_238_ = lean_box_float32(v_res_237_);
return v_r_238_;
}
}
LEAN_EXPORT lean_object* l_Float32_cosh___boxed(lean_object* v_a_00___x40___internal___hyg_240_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_241_; float v_res_242_; lean_object* v_r_243_; 
v_a_00___x40___internal___hyg_1__boxed_241_ = lean_unbox_float32(v_a_00___x40___internal___hyg_240_);
lean_dec_ref(v_a_00___x40___internal___hyg_240_);
v_res_242_ = coshf(v_a_00___x40___internal___hyg_1__boxed_241_);
v_r_243_ = lean_box_float32(v_res_242_);
return v_r_243_;
}
}
LEAN_EXPORT lean_object* l_Float32_tanh___boxed(lean_object* v_a_00___x40___internal___hyg_245_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_246_; float v_res_247_; lean_object* v_r_248_; 
v_a_00___x40___internal___hyg_1__boxed_246_ = lean_unbox_float32(v_a_00___x40___internal___hyg_245_);
lean_dec_ref(v_a_00___x40___internal___hyg_245_);
v_res_247_ = tanhf(v_a_00___x40___internal___hyg_1__boxed_246_);
v_r_248_ = lean_box_float32(v_res_247_);
return v_r_248_;
}
}
LEAN_EXPORT lean_object* l_Float32_asinh___boxed(lean_object* v_a_00___x40___internal___hyg_250_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_251_; float v_res_252_; lean_object* v_r_253_; 
v_a_00___x40___internal___hyg_1__boxed_251_ = lean_unbox_float32(v_a_00___x40___internal___hyg_250_);
lean_dec_ref(v_a_00___x40___internal___hyg_250_);
v_res_252_ = asinhf(v_a_00___x40___internal___hyg_1__boxed_251_);
v_r_253_ = lean_box_float32(v_res_252_);
return v_r_253_;
}
}
LEAN_EXPORT lean_object* l_Float32_acosh___boxed(lean_object* v_a_00___x40___internal___hyg_255_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_256_; float v_res_257_; lean_object* v_r_258_; 
v_a_00___x40___internal___hyg_1__boxed_256_ = lean_unbox_float32(v_a_00___x40___internal___hyg_255_);
lean_dec_ref(v_a_00___x40___internal___hyg_255_);
v_res_257_ = acoshf(v_a_00___x40___internal___hyg_1__boxed_256_);
v_r_258_ = lean_box_float32(v_res_257_);
return v_r_258_;
}
}
LEAN_EXPORT lean_object* l_Float32_atanh___boxed(lean_object* v_a_00___x40___internal___hyg_260_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_261_; float v_res_262_; lean_object* v_r_263_; 
v_a_00___x40___internal___hyg_1__boxed_261_ = lean_unbox_float32(v_a_00___x40___internal___hyg_260_);
lean_dec_ref(v_a_00___x40___internal___hyg_260_);
v_res_262_ = atanhf(v_a_00___x40___internal___hyg_1__boxed_261_);
v_r_263_ = lean_box_float32(v_res_262_);
return v_r_263_;
}
}
LEAN_EXPORT lean_object* l_Float32_exp___boxed(lean_object* v_a_00___x40___internal___hyg_265_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_266_; float v_res_267_; lean_object* v_r_268_; 
v_a_00___x40___internal___hyg_1__boxed_266_ = lean_unbox_float32(v_a_00___x40___internal___hyg_265_);
lean_dec_ref(v_a_00___x40___internal___hyg_265_);
v_res_267_ = expf(v_a_00___x40___internal___hyg_1__boxed_266_);
v_r_268_ = lean_box_float32(v_res_267_);
return v_r_268_;
}
}
LEAN_EXPORT lean_object* l_Float32_exp2___boxed(lean_object* v_a_00___x40___internal___hyg_270_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_271_; float v_res_272_; lean_object* v_r_273_; 
v_a_00___x40___internal___hyg_1__boxed_271_ = lean_unbox_float32(v_a_00___x40___internal___hyg_270_);
lean_dec_ref(v_a_00___x40___internal___hyg_270_);
v_res_272_ = exp2f(v_a_00___x40___internal___hyg_1__boxed_271_);
v_r_273_ = lean_box_float32(v_res_272_);
return v_r_273_;
}
}
LEAN_EXPORT lean_object* l_Float32_log___boxed(lean_object* v_a_00___x40___internal___hyg_275_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_276_; float v_res_277_; lean_object* v_r_278_; 
v_a_00___x40___internal___hyg_1__boxed_276_ = lean_unbox_float32(v_a_00___x40___internal___hyg_275_);
lean_dec_ref(v_a_00___x40___internal___hyg_275_);
v_res_277_ = logf(v_a_00___x40___internal___hyg_1__boxed_276_);
v_r_278_ = lean_box_float32(v_res_277_);
return v_r_278_;
}
}
LEAN_EXPORT lean_object* l_Float32_log2___boxed(lean_object* v_a_00___x40___internal___hyg_280_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_281_; float v_res_282_; lean_object* v_r_283_; 
v_a_00___x40___internal___hyg_1__boxed_281_ = lean_unbox_float32(v_a_00___x40___internal___hyg_280_);
lean_dec_ref(v_a_00___x40___internal___hyg_280_);
v_res_282_ = log2f(v_a_00___x40___internal___hyg_1__boxed_281_);
v_r_283_ = lean_box_float32(v_res_282_);
return v_r_283_;
}
}
LEAN_EXPORT lean_object* l_Float32_log10___boxed(lean_object* v_a_00___x40___internal___hyg_285_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_286_; float v_res_287_; lean_object* v_r_288_; 
v_a_00___x40___internal___hyg_1__boxed_286_ = lean_unbox_float32(v_a_00___x40___internal___hyg_285_);
lean_dec_ref(v_a_00___x40___internal___hyg_285_);
v_res_287_ = log10f(v_a_00___x40___internal___hyg_1__boxed_286_);
v_r_288_ = lean_box_float32(v_res_287_);
return v_r_288_;
}
}
LEAN_EXPORT lean_object* l_Float32_pow___boxed(lean_object* v_a_00___x40___internal___hyg_291_, lean_object* v_a_00___x40___internal___hyg_292_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_293_; float v_a_00___x40___internal___hyg_2__boxed_294_; float v_res_295_; lean_object* v_r_296_; 
v_a_00___x40___internal___hyg_1__boxed_293_ = lean_unbox_float32(v_a_00___x40___internal___hyg_291_);
lean_dec_ref(v_a_00___x40___internal___hyg_291_);
v_a_00___x40___internal___hyg_2__boxed_294_ = lean_unbox_float32(v_a_00___x40___internal___hyg_292_);
lean_dec_ref(v_a_00___x40___internal___hyg_292_);
v_res_295_ = powf(v_a_00___x40___internal___hyg_1__boxed_293_, v_a_00___x40___internal___hyg_2__boxed_294_);
v_r_296_ = lean_box_float32(v_res_295_);
return v_r_296_;
}
}
LEAN_EXPORT lean_object* l_Float32_sqrt___boxed(lean_object* v_a_00___x40___internal___hyg_298_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_299_; float v_res_300_; lean_object* v_r_301_; 
v_a_00___x40___internal___hyg_1__boxed_299_ = lean_unbox_float32(v_a_00___x40___internal___hyg_298_);
lean_dec_ref(v_a_00___x40___internal___hyg_298_);
v_res_300_ = sqrtf(v_a_00___x40___internal___hyg_1__boxed_299_);
v_r_301_ = lean_box_float32(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT lean_object* l_Float32_cbrt___boxed(lean_object* v_a_00___x40___internal___hyg_303_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_304_; float v_res_305_; lean_object* v_r_306_; 
v_a_00___x40___internal___hyg_1__boxed_304_ = lean_unbox_float32(v_a_00___x40___internal___hyg_303_);
lean_dec_ref(v_a_00___x40___internal___hyg_303_);
v_res_305_ = cbrtf(v_a_00___x40___internal___hyg_1__boxed_304_);
v_r_306_ = lean_box_float32(v_res_305_);
return v_r_306_;
}
}
LEAN_EXPORT lean_object* l_Float32_ceil___boxed(lean_object* v_a_00___x40___internal___hyg_308_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_309_; float v_res_310_; lean_object* v_r_311_; 
v_a_00___x40___internal___hyg_1__boxed_309_ = lean_unbox_float32(v_a_00___x40___internal___hyg_308_);
lean_dec_ref(v_a_00___x40___internal___hyg_308_);
v_res_310_ = ceilf(v_a_00___x40___internal___hyg_1__boxed_309_);
v_r_311_ = lean_box_float32(v_res_310_);
return v_r_311_;
}
}
LEAN_EXPORT lean_object* l_Float32_floor___boxed(lean_object* v_a_00___x40___internal___hyg_313_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_314_; float v_res_315_; lean_object* v_r_316_; 
v_a_00___x40___internal___hyg_1__boxed_314_ = lean_unbox_float32(v_a_00___x40___internal___hyg_313_);
lean_dec_ref(v_a_00___x40___internal___hyg_313_);
v_res_315_ = floorf(v_a_00___x40___internal___hyg_1__boxed_314_);
v_r_316_ = lean_box_float32(v_res_315_);
return v_r_316_;
}
}
LEAN_EXPORT lean_object* l_Float32_round___boxed(lean_object* v_a_00___x40___internal___hyg_318_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_319_; float v_res_320_; lean_object* v_r_321_; 
v_a_00___x40___internal___hyg_1__boxed_319_ = lean_unbox_float32(v_a_00___x40___internal___hyg_318_);
lean_dec_ref(v_a_00___x40___internal___hyg_318_);
v_res_320_ = roundf(v_a_00___x40___internal___hyg_1__boxed_319_);
v_r_321_ = lean_box_float32(v_res_320_);
return v_r_321_;
}
}
LEAN_EXPORT lean_object* l_Float32_abs___boxed(lean_object* v_a_00___x40___internal___hyg_323_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_324_; float v_res_325_; lean_object* v_r_326_; 
v_a_00___x40___internal___hyg_1__boxed_324_ = lean_unbox_float32(v_a_00___x40___internal___hyg_323_);
lean_dec_ref(v_a_00___x40___internal___hyg_323_);
v_res_325_ = fabsf(v_a_00___x40___internal___hyg_1__boxed_324_);
v_r_326_ = lean_box_float32(v_res_325_);
return v_r_326_;
}
}
LEAN_EXPORT float l_instMinFloat32___lam__0(float v_x_329_, float v_y_330_){
_start:
{
uint8_t v___x_331_; 
v___x_331_ = lean_float32_decLe(v_x_329_, v_y_330_);
if (v___x_331_ == 0)
{
return v_y_330_;
}
else
{
return v_x_329_;
}
}
}
LEAN_EXPORT lean_object* l_instMinFloat32___lam__0___boxed(lean_object* v_x_332_, lean_object* v_y_333_){
_start:
{
float v_x_boxed_334_; float v_y_boxed_335_; float v_res_336_; lean_object* v_r_337_; 
v_x_boxed_334_ = lean_unbox_float32(v_x_332_);
lean_dec_ref(v_x_332_);
v_y_boxed_335_ = lean_unbox_float32(v_y_333_);
lean_dec_ref(v_y_333_);
v_res_336_ = l_instMinFloat32___lam__0(v_x_boxed_334_, v_y_boxed_335_);
v_r_337_ = lean_box_float32(v_res_336_);
return v_r_337_;
}
}
LEAN_EXPORT float l_instMaxFloat32___lam__0(float v_x_340_, float v_y_341_){
_start:
{
uint8_t v___x_342_; 
v___x_342_ = lean_float32_decLe(v_x_340_, v_y_341_);
if (v___x_342_ == 0)
{
return v_x_340_;
}
else
{
return v_y_341_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxFloat32___lam__0___boxed(lean_object* v_x_343_, lean_object* v_y_344_){
_start:
{
float v_x_boxed_345_; float v_y_boxed_346_; float v_res_347_; lean_object* v_r_348_; 
v_x_boxed_345_ = lean_unbox_float32(v_x_343_);
lean_dec_ref(v_x_343_);
v_y_boxed_346_ = lean_unbox_float32(v_y_344_);
lean_dec_ref(v_y_344_);
v_res_347_ = l_instMaxFloat32___lam__0(v_x_boxed_345_, v_y_boxed_346_);
v_r_348_ = lean_box_float32(v_res_347_);
return v_r_348_;
}
}
LEAN_EXPORT lean_object* l_Float32_scaleB___boxed(lean_object* v_x_353_, lean_object* v_i_354_){
_start:
{
float v_x_boxed_355_; float v_res_356_; lean_object* v_r_357_; 
v_x_boxed_355_ = lean_unbox_float32(v_x_353_);
lean_dec_ref(v_x_353_);
v_res_356_ = lean_float32_scaleb(v_x_boxed_355_, v_i_354_);
lean_dec(v_i_354_);
v_r_357_ = lean_box_float32(v_res_356_);
return v_r_357_;
}
}
LEAN_EXPORT lean_object* l_Float32_toFloat___boxed(lean_object* v_a_00___x40___internal___hyg_359_){
_start:
{
float v_a_00___x40___internal___hyg_1__boxed_360_; double v_res_361_; lean_object* v_r_362_; 
v_a_00___x40___internal___hyg_1__boxed_360_ = lean_unbox_float32(v_a_00___x40___internal___hyg_359_);
lean_dec_ref(v_a_00___x40___internal___hyg_359_);
v_res_361_ = lean_float32_to_float(v_a_00___x40___internal___hyg_1__boxed_360_);
v_r_362_ = lean_box_float(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT lean_object* l_Float_toFloat32___boxed(lean_object* v_a_00___x40___internal___hyg_364_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_365_; float v_res_366_; lean_object* v_r_367_; 
v_a_00___x40___internal___hyg_1__boxed_365_ = lean_unbox_float(v_a_00___x40___internal___hyg_364_);
lean_dec_ref(v_a_00___x40___internal___hyg_364_);
v_res_366_ = lean_float_to_float32(v_a_00___x40___internal___hyg_1__boxed_365_);
v_r_367_ = lean_box_float32(v_res_366_);
return v_r_367_;
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
