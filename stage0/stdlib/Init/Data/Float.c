// Lean compiler output
// Module: Init.Data.Float
// Imports: public import Init.Data.ToString.Basic
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
LEAN_EXPORT uint8_t l_floatSpec___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_floatSpec___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_floatSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_floatSpec___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_floatSpec___closed__0 = (const lean_object*)&l_floatSpec___closed__0_value;
static lean_once_cell_t l_floatSpec___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_floatSpec___closed__1;
LEAN_EXPORT lean_object* l_floatSpec;
double lean_float_add(double, double);
LEAN_EXPORT lean_object* l_Float_add___boxed(lean_object*, lean_object*);
double lean_float_sub(double, double);
LEAN_EXPORT lean_object* l_Float_sub___boxed(lean_object*, lean_object*);
double lean_float_mul(double, double);
LEAN_EXPORT lean_object* l_Float_mul___boxed(lean_object*, lean_object*);
double lean_float_div(double, double);
LEAN_EXPORT lean_object* l_Float_div___boxed(lean_object*, lean_object*);
double lean_float_negate(double);
LEAN_EXPORT lean_object* l_Float_neg___boxed(lean_object*);
double lean_float_of_bits(uint64_t);
LEAN_EXPORT lean_object* l_Float_ofBits___boxed(lean_object*);
uint64_t lean_float_to_bits(double);
LEAN_EXPORT lean_object* l_Float_toBits___boxed(lean_object*);
static const lean_closure_object l_instAddFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instAddFloat___closed__0 = (const lean_object*)&l_instAddFloat___closed__0_value;
LEAN_EXPORT const lean_object* l_instAddFloat = (const lean_object*)&l_instAddFloat___closed__0_value;
static const lean_closure_object l_instSubFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSubFloat___closed__0 = (const lean_object*)&l_instSubFloat___closed__0_value;
LEAN_EXPORT const lean_object* l_instSubFloat = (const lean_object*)&l_instSubFloat___closed__0_value;
static const lean_closure_object l_instMulFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMulFloat___closed__0 = (const lean_object*)&l_instMulFloat___closed__0_value;
LEAN_EXPORT const lean_object* l_instMulFloat = (const lean_object*)&l_instMulFloat___closed__0_value;
static const lean_closure_object l_instDivFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_div___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instDivFloat___closed__0 = (const lean_object*)&l_instDivFloat___closed__0_value;
LEAN_EXPORT const lean_object* l_instDivFloat = (const lean_object*)&l_instDivFloat___closed__0_value;
static const lean_closure_object l_instNegFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instNegFloat___closed__0 = (const lean_object*)&l_instNegFloat___closed__0_value;
LEAN_EXPORT const lean_object* l_instNegFloat = (const lean_object*)&l_instNegFloat___closed__0_value;
LEAN_EXPORT lean_object* l_instLTFloat;
LEAN_EXPORT lean_object* l_instLEFloat;
uint8_t lean_float_beq(double, double);
LEAN_EXPORT lean_object* l_Float_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instBEqFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instBEqFloat___closed__0 = (const lean_object*)&l_instBEqFloat___closed__0_value;
LEAN_EXPORT const lean_object* l_instBEqFloat = (const lean_object*)&l_instBEqFloat___closed__0_value;
uint8_t lean_float_decLt(double, double);
LEAN_EXPORT lean_object* l_Float_decLt___boxed(lean_object*, lean_object*);
uint8_t lean_float_decLe(double, double);
LEAN_EXPORT lean_object* l_Float_decLe___boxed(lean_object*, lean_object*);
lean_object* lean_float_to_string(double);
LEAN_EXPORT lean_object* l_Float_toString___boxed(lean_object*);
uint8_t lean_float_to_uint8(double);
LEAN_EXPORT lean_object* l_Float_toUInt8___boxed(lean_object*);
uint16_t lean_float_to_uint16(double);
LEAN_EXPORT lean_object* l_Float_toUInt16___boxed(lean_object*);
uint32_t lean_float_to_uint32(double);
LEAN_EXPORT lean_object* l_Float_toUInt32___boxed(lean_object*);
uint64_t lean_float_to_uint64(double);
LEAN_EXPORT lean_object* l_Float_toUInt64___boxed(lean_object*);
size_t lean_float_to_usize(double);
LEAN_EXPORT lean_object* l_Float_toUSize___boxed(lean_object*);
uint8_t lean_float_isnan(double);
LEAN_EXPORT lean_object* l_Float_isNaN___boxed(lean_object*);
uint8_t lean_float_isfinite(double);
LEAN_EXPORT lean_object* l_Float_isFinite___boxed(lean_object*);
uint8_t lean_float_isinf(double);
LEAN_EXPORT lean_object* l_Float_isInf___boxed(lean_object*);
lean_object* lean_float_frexp(double);
LEAN_EXPORT lean_object* l_Float_frExp___boxed(lean_object*);
static const lean_closure_object l_instToStringFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringFloat___closed__0 = (const lean_object*)&l_instToStringFloat___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringFloat = (const lean_object*)&l_instToStringFloat___closed__0_value;
double lean_uint8_to_float(uint8_t);
LEAN_EXPORT lean_object* l_UInt8_toFloat___boxed(lean_object*);
double lean_uint16_to_float(uint16_t);
LEAN_EXPORT lean_object* l_UInt16_toFloat___boxed(lean_object*);
double lean_uint32_to_float(uint32_t);
LEAN_EXPORT lean_object* l_UInt32_toFloat___boxed(lean_object*);
double lean_uint64_to_float(uint64_t);
LEAN_EXPORT lean_object* l_UInt64_toFloat___boxed(lean_object*);
double lean_usize_to_float(size_t);
LEAN_EXPORT lean_object* l_USize_toFloat___boxed(lean_object*);
static lean_once_cell_t l_instInhabitedFloat___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_instInhabitedFloat___closed__0;
LEAN_EXPORT double l_instInhabitedFloat;
LEAN_EXPORT lean_object* l_Float_repr(double, lean_object*);
LEAN_EXPORT lean_object* l_Float_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprFloat___closed__0 = (const lean_object*)&l_instReprFloat___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprFloat = (const lean_object*)&l_instReprFloat___closed__0_value;
LEAN_EXPORT lean_object* l_instReprAtomFloat;
double sin(double);
LEAN_EXPORT lean_object* l_Float_sin___boxed(lean_object*);
double cos(double);
LEAN_EXPORT lean_object* l_Float_cos___boxed(lean_object*);
double tan(double);
LEAN_EXPORT lean_object* l_Float_tan___boxed(lean_object*);
double asin(double);
LEAN_EXPORT lean_object* l_Float_asin___boxed(lean_object*);
double acos(double);
LEAN_EXPORT lean_object* l_Float_acos___boxed(lean_object*);
double atan(double);
LEAN_EXPORT lean_object* l_Float_atan___boxed(lean_object*);
double atan2(double, double);
LEAN_EXPORT lean_object* l_Float_atan2___boxed(lean_object*, lean_object*);
double sinh(double);
LEAN_EXPORT lean_object* l_Float_sinh___boxed(lean_object*);
double cosh(double);
LEAN_EXPORT lean_object* l_Float_cosh___boxed(lean_object*);
double tanh(double);
LEAN_EXPORT lean_object* l_Float_tanh___boxed(lean_object*);
double asinh(double);
LEAN_EXPORT lean_object* l_Float_asinh___boxed(lean_object*);
double acosh(double);
LEAN_EXPORT lean_object* l_Float_acosh___boxed(lean_object*);
double atanh(double);
LEAN_EXPORT lean_object* l_Float_atanh___boxed(lean_object*);
double exp(double);
LEAN_EXPORT lean_object* l_Float_exp___boxed(lean_object*);
double exp2(double);
LEAN_EXPORT lean_object* l_Float_exp2___boxed(lean_object*);
double log(double);
LEAN_EXPORT lean_object* l_Float_log___boxed(lean_object*);
double log2(double);
LEAN_EXPORT lean_object* l_Float_log2___boxed(lean_object*);
double log10(double);
LEAN_EXPORT lean_object* l_Float_log10___boxed(lean_object*);
double pow(double, double);
LEAN_EXPORT lean_object* l_Float_pow___boxed(lean_object*, lean_object*);
double sqrt(double);
LEAN_EXPORT lean_object* l_Float_sqrt___boxed(lean_object*);
double cbrt(double);
LEAN_EXPORT lean_object* l_Float_cbrt___boxed(lean_object*);
double ceil(double);
LEAN_EXPORT lean_object* l_Float_ceil___boxed(lean_object*);
double floor(double);
LEAN_EXPORT lean_object* l_Float_floor___boxed(lean_object*);
double round(double);
LEAN_EXPORT lean_object* l_Float_round___boxed(lean_object*);
double fabs(double);
LEAN_EXPORT lean_object* l_Float_abs___boxed(lean_object*);
static const lean_closure_object l_instHomogeneousPowFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHomogeneousPowFloat___closed__0 = (const lean_object*)&l_instHomogeneousPowFloat___closed__0_value;
LEAN_EXPORT const lean_object* l_instHomogeneousPowFloat = (const lean_object*)&l_instHomogeneousPowFloat___closed__0_value;
LEAN_EXPORT double l_instMinFloat___lam__0(double, double);
LEAN_EXPORT lean_object* l_instMinFloat___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instMinFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMinFloat___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMinFloat___closed__0 = (const lean_object*)&l_instMinFloat___closed__0_value;
LEAN_EXPORT const lean_object* l_instMinFloat = (const lean_object*)&l_instMinFloat___closed__0_value;
LEAN_EXPORT double l_instMaxFloat___lam__0(double, double);
LEAN_EXPORT lean_object* l_instMaxFloat___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instMaxFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMaxFloat___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMaxFloat___closed__0 = (const lean_object*)&l_instMaxFloat___closed__0_value;
LEAN_EXPORT const lean_object* l_instMaxFloat = (const lean_object*)&l_instMaxFloat___closed__0_value;
double lean_float_scaleb(double, lean_object*);
LEAN_EXPORT lean_object* l_Float_scaleB___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_floatSpec___lam__0(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = 1;
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_floatSpec___lam__0___boxed(lean_object* v_x_4_, lean_object* v_x_5_){
_start:
{
uint8_t v_res_6_; lean_object* v_r_7_; 
v_res_6_ = l_floatSpec___lam__0(v_x_4_, v_x_5_);
v_r_7_ = lean_box(v_res_6_);
return v_r_7_;
}
}
static lean_object* _init_l_floatSpec___closed__1(void){
_start:
{
lean_object* v___f_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___f_9_ = ((lean_object*)(l_floatSpec___closed__0));
v___x_10_ = lean_box(0);
v___x_11_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
lean_ctor_set(v___x_11_, 1, v___f_9_);
lean_ctor_set(v___x_11_, 2, v___f_9_);
return v___x_11_;
}
}
static lean_object* _init_l_floatSpec(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&l_floatSpec___closed__1, &l_floatSpec___closed__1_once, _init_l_floatSpec___closed__1);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Float_add___boxed(lean_object* v_a_00___x40___internal___hyg_15_, lean_object* v_a_00___x40___internal___hyg_16_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_17_; double v_a_00___x40___internal___hyg_2__boxed_18_; double v_res_19_; lean_object* v_r_20_; 
v_a_00___x40___internal___hyg_1__boxed_17_ = lean_unbox_float(v_a_00___x40___internal___hyg_15_);
lean_dec_ref(v_a_00___x40___internal___hyg_15_);
v_a_00___x40___internal___hyg_2__boxed_18_ = lean_unbox_float(v_a_00___x40___internal___hyg_16_);
lean_dec_ref(v_a_00___x40___internal___hyg_16_);
v_res_19_ = lean_float_add(v_a_00___x40___internal___hyg_1__boxed_17_, v_a_00___x40___internal___hyg_2__boxed_18_);
v_r_20_ = lean_box_float(v_res_19_);
return v_r_20_;
}
}
LEAN_EXPORT lean_object* l_Float_sub___boxed(lean_object* v_a_00___x40___internal___hyg_23_, lean_object* v_a_00___x40___internal___hyg_24_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_25_; double v_a_00___x40___internal___hyg_2__boxed_26_; double v_res_27_; lean_object* v_r_28_; 
v_a_00___x40___internal___hyg_1__boxed_25_ = lean_unbox_float(v_a_00___x40___internal___hyg_23_);
lean_dec_ref(v_a_00___x40___internal___hyg_23_);
v_a_00___x40___internal___hyg_2__boxed_26_ = lean_unbox_float(v_a_00___x40___internal___hyg_24_);
lean_dec_ref(v_a_00___x40___internal___hyg_24_);
v_res_27_ = lean_float_sub(v_a_00___x40___internal___hyg_1__boxed_25_, v_a_00___x40___internal___hyg_2__boxed_26_);
v_r_28_ = lean_box_float(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT lean_object* l_Float_mul___boxed(lean_object* v_a_00___x40___internal___hyg_31_, lean_object* v_a_00___x40___internal___hyg_32_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_33_; double v_a_00___x40___internal___hyg_2__boxed_34_; double v_res_35_; lean_object* v_r_36_; 
v_a_00___x40___internal___hyg_1__boxed_33_ = lean_unbox_float(v_a_00___x40___internal___hyg_31_);
lean_dec_ref(v_a_00___x40___internal___hyg_31_);
v_a_00___x40___internal___hyg_2__boxed_34_ = lean_unbox_float(v_a_00___x40___internal___hyg_32_);
lean_dec_ref(v_a_00___x40___internal___hyg_32_);
v_res_35_ = lean_float_mul(v_a_00___x40___internal___hyg_1__boxed_33_, v_a_00___x40___internal___hyg_2__boxed_34_);
v_r_36_ = lean_box_float(v_res_35_);
return v_r_36_;
}
}
LEAN_EXPORT lean_object* l_Float_div___boxed(lean_object* v_a_00___x40___internal___hyg_39_, lean_object* v_a_00___x40___internal___hyg_40_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_41_; double v_a_00___x40___internal___hyg_2__boxed_42_; double v_res_43_; lean_object* v_r_44_; 
v_a_00___x40___internal___hyg_1__boxed_41_ = lean_unbox_float(v_a_00___x40___internal___hyg_39_);
lean_dec_ref(v_a_00___x40___internal___hyg_39_);
v_a_00___x40___internal___hyg_2__boxed_42_ = lean_unbox_float(v_a_00___x40___internal___hyg_40_);
lean_dec_ref(v_a_00___x40___internal___hyg_40_);
v_res_43_ = lean_float_div(v_a_00___x40___internal___hyg_1__boxed_41_, v_a_00___x40___internal___hyg_2__boxed_42_);
v_r_44_ = lean_box_float(v_res_43_);
return v_r_44_;
}
}
LEAN_EXPORT lean_object* l_Float_neg___boxed(lean_object* v_a_00___x40___internal___hyg_46_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_47_; double v_res_48_; lean_object* v_r_49_; 
v_a_00___x40___internal___hyg_1__boxed_47_ = lean_unbox_float(v_a_00___x40___internal___hyg_46_);
lean_dec_ref(v_a_00___x40___internal___hyg_46_);
v_res_48_ = lean_float_negate(v_a_00___x40___internal___hyg_1__boxed_47_);
v_r_49_ = lean_box_float(v_res_48_);
return v_r_49_;
}
}
LEAN_EXPORT lean_object* l_Float_ofBits___boxed(lean_object* v_a_00___x40___internal___hyg_51_){
_start:
{
uint64_t v_a_00___x40___internal___hyg_1__boxed_52_; double v_res_53_; lean_object* v_r_54_; 
v_a_00___x40___internal___hyg_1__boxed_52_ = lean_unbox_uint64(v_a_00___x40___internal___hyg_51_);
lean_dec_ref(v_a_00___x40___internal___hyg_51_);
v_res_53_ = lean_float_of_bits(v_a_00___x40___internal___hyg_1__boxed_52_);
v_r_54_ = lean_box_float(v_res_53_);
return v_r_54_;
}
}
LEAN_EXPORT lean_object* l_Float_toBits___boxed(lean_object* v_a_00___x40___internal___hyg_56_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_57_; uint64_t v_res_58_; lean_object* v_r_59_; 
v_a_00___x40___internal___hyg_1__boxed_57_ = lean_unbox_float(v_a_00___x40___internal___hyg_56_);
lean_dec_ref(v_a_00___x40___internal___hyg_56_);
v_res_58_ = lean_float_to_bits(v_a_00___x40___internal___hyg_1__boxed_57_);
v_r_59_ = lean_box_uint64(v_res_58_);
return v_r_59_;
}
}
static lean_object* _init_l_instLTFloat(void){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lean_box(0);
return v___x_70_;
}
}
static lean_object* _init_l_instLEFloat(void){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lean_box(0);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Float_beq___boxed(lean_object* v_a_74_, lean_object* v_b_75_){
_start:
{
double v_a_boxed_76_; double v_b_boxed_77_; uint8_t v_res_78_; lean_object* v_r_79_; 
v_a_boxed_76_ = lean_unbox_float(v_a_74_);
lean_dec_ref(v_a_74_);
v_b_boxed_77_ = lean_unbox_float(v_b_75_);
lean_dec_ref(v_b_75_);
v_res_78_ = lean_float_beq(v_a_boxed_76_, v_b_boxed_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT lean_object* l_Float_decLt___boxed(lean_object* v_a_84_, lean_object* v_b_85_){
_start:
{
double v_a_boxed_86_; double v_b_boxed_87_; uint8_t v_res_88_; lean_object* v_r_89_; 
v_a_boxed_86_ = lean_unbox_float(v_a_84_);
lean_dec_ref(v_a_84_);
v_b_boxed_87_ = lean_unbox_float(v_b_85_);
lean_dec_ref(v_b_85_);
v_res_88_ = lean_float_decLt(v_a_boxed_86_, v_b_boxed_87_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
LEAN_EXPORT lean_object* l_Float_decLe___boxed(lean_object* v_a_92_, lean_object* v_b_93_){
_start:
{
double v_a_boxed_94_; double v_b_boxed_95_; uint8_t v_res_96_; lean_object* v_r_97_; 
v_a_boxed_94_ = lean_unbox_float(v_a_92_);
lean_dec_ref(v_a_92_);
v_b_boxed_95_ = lean_unbox_float(v_b_93_);
lean_dec_ref(v_b_93_);
v_res_96_ = lean_float_decLe(v_a_boxed_94_, v_b_boxed_95_);
v_r_97_ = lean_box(v_res_96_);
return v_r_97_;
}
}
LEAN_EXPORT lean_object* l_Float_toString___boxed(lean_object* v_a_00___x40___internal___hyg_99_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_100_; lean_object* v_res_101_; 
v_a_00___x40___internal___hyg_1__boxed_100_ = lean_unbox_float(v_a_00___x40___internal___hyg_99_);
lean_dec_ref(v_a_00___x40___internal___hyg_99_);
v_res_101_ = lean_float_to_string(v_a_00___x40___internal___hyg_1__boxed_100_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Float_toUInt8___boxed(lean_object* v_a_00___x40___internal___hyg_103_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_104_; uint8_t v_res_105_; lean_object* v_r_106_; 
v_a_00___x40___internal___hyg_1__boxed_104_ = lean_unbox_float(v_a_00___x40___internal___hyg_103_);
lean_dec_ref(v_a_00___x40___internal___hyg_103_);
v_res_105_ = lean_float_to_uint8(v_a_00___x40___internal___hyg_1__boxed_104_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
LEAN_EXPORT lean_object* l_Float_toUInt16___boxed(lean_object* v_a_00___x40___internal___hyg_108_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_109_; uint16_t v_res_110_; lean_object* v_r_111_; 
v_a_00___x40___internal___hyg_1__boxed_109_ = lean_unbox_float(v_a_00___x40___internal___hyg_108_);
lean_dec_ref(v_a_00___x40___internal___hyg_108_);
v_res_110_ = lean_float_to_uint16(v_a_00___x40___internal___hyg_1__boxed_109_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT lean_object* l_Float_toUInt32___boxed(lean_object* v_a_00___x40___internal___hyg_113_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_114_; uint32_t v_res_115_; lean_object* v_r_116_; 
v_a_00___x40___internal___hyg_1__boxed_114_ = lean_unbox_float(v_a_00___x40___internal___hyg_113_);
lean_dec_ref(v_a_00___x40___internal___hyg_113_);
v_res_115_ = lean_float_to_uint32(v_a_00___x40___internal___hyg_1__boxed_114_);
v_r_116_ = lean_box_uint32(v_res_115_);
return v_r_116_;
}
}
LEAN_EXPORT lean_object* l_Float_toUInt64___boxed(lean_object* v_a_00___x40___internal___hyg_118_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_119_; uint64_t v_res_120_; lean_object* v_r_121_; 
v_a_00___x40___internal___hyg_1__boxed_119_ = lean_unbox_float(v_a_00___x40___internal___hyg_118_);
lean_dec_ref(v_a_00___x40___internal___hyg_118_);
v_res_120_ = lean_float_to_uint64(v_a_00___x40___internal___hyg_1__boxed_119_);
v_r_121_ = lean_box_uint64(v_res_120_);
return v_r_121_;
}
}
LEAN_EXPORT lean_object* l_Float_toUSize___boxed(lean_object* v_a_00___x40___internal___hyg_123_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_124_; size_t v_res_125_; lean_object* v_r_126_; 
v_a_00___x40___internal___hyg_1__boxed_124_ = lean_unbox_float(v_a_00___x40___internal___hyg_123_);
lean_dec_ref(v_a_00___x40___internal___hyg_123_);
v_res_125_ = lean_float_to_usize(v_a_00___x40___internal___hyg_1__boxed_124_);
v_r_126_ = lean_box_usize(v_res_125_);
return v_r_126_;
}
}
LEAN_EXPORT lean_object* l_Float_isNaN___boxed(lean_object* v_a_00___x40___internal___hyg_128_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_129_; uint8_t v_res_130_; lean_object* v_r_131_; 
v_a_00___x40___internal___hyg_1__boxed_129_ = lean_unbox_float(v_a_00___x40___internal___hyg_128_);
lean_dec_ref(v_a_00___x40___internal___hyg_128_);
v_res_130_ = lean_float_isnan(v_a_00___x40___internal___hyg_1__boxed_129_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT lean_object* l_Float_isFinite___boxed(lean_object* v_a_00___x40___internal___hyg_133_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_134_; uint8_t v_res_135_; lean_object* v_r_136_; 
v_a_00___x40___internal___hyg_1__boxed_134_ = lean_unbox_float(v_a_00___x40___internal___hyg_133_);
lean_dec_ref(v_a_00___x40___internal___hyg_133_);
v_res_135_ = lean_float_isfinite(v_a_00___x40___internal___hyg_1__boxed_134_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT lean_object* l_Float_isInf___boxed(lean_object* v_a_00___x40___internal___hyg_138_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_139_; uint8_t v_res_140_; lean_object* v_r_141_; 
v_a_00___x40___internal___hyg_1__boxed_139_ = lean_unbox_float(v_a_00___x40___internal___hyg_138_);
lean_dec_ref(v_a_00___x40___internal___hyg_138_);
v_res_140_ = lean_float_isinf(v_a_00___x40___internal___hyg_1__boxed_139_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
LEAN_EXPORT lean_object* l_Float_frExp___boxed(lean_object* v_a_00___x40___internal___hyg_143_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_144_; lean_object* v_res_145_; 
v_a_00___x40___internal___hyg_1__boxed_144_ = lean_unbox_float(v_a_00___x40___internal___hyg_143_);
lean_dec_ref(v_a_00___x40___internal___hyg_143_);
v_res_145_ = lean_float_frexp(v_a_00___x40___internal___hyg_1__boxed_144_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_UInt8_toFloat___boxed(lean_object* v_n_149_){
_start:
{
uint8_t v_n_boxed_150_; double v_res_151_; lean_object* v_r_152_; 
v_n_boxed_150_ = lean_unbox(v_n_149_);
v_res_151_ = lean_uint8_to_float(v_n_boxed_150_);
v_r_152_ = lean_box_float(v_res_151_);
return v_r_152_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toFloat___boxed(lean_object* v_n_154_){
_start:
{
uint16_t v_n_boxed_155_; double v_res_156_; lean_object* v_r_157_; 
v_n_boxed_155_ = lean_unbox(v_n_154_);
v_res_156_ = lean_uint16_to_float(v_n_boxed_155_);
v_r_157_ = lean_box_float(v_res_156_);
return v_r_157_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toFloat___boxed(lean_object* v_n_159_){
_start:
{
uint32_t v_n_boxed_160_; double v_res_161_; lean_object* v_r_162_; 
v_n_boxed_160_ = lean_unbox_uint32(v_n_159_);
lean_dec(v_n_159_);
v_res_161_ = lean_uint32_to_float(v_n_boxed_160_);
v_r_162_ = lean_box_float(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toFloat___boxed(lean_object* v_n_164_){
_start:
{
uint64_t v_n_boxed_165_; double v_res_166_; lean_object* v_r_167_; 
v_n_boxed_165_ = lean_unbox_uint64(v_n_164_);
lean_dec_ref(v_n_164_);
v_res_166_ = lean_uint64_to_float(v_n_boxed_165_);
v_r_167_ = lean_box_float(v_res_166_);
return v_r_167_;
}
}
LEAN_EXPORT lean_object* l_USize_toFloat___boxed(lean_object* v_n_169_){
_start:
{
size_t v_n_boxed_170_; double v_res_171_; lean_object* v_r_172_; 
v_n_boxed_170_ = lean_unbox_usize(v_n_169_);
lean_dec(v_n_169_);
v_res_171_ = lean_usize_to_float(v_n_boxed_170_);
v_r_172_ = lean_box_float(v_res_171_);
return v_r_172_;
}
}
static double _init_l_instInhabitedFloat___closed__0(void){
_start:
{
uint64_t v___x_173_; double v___x_174_; 
v___x_173_ = 0ULL;
v___x_174_ = lean_uint64_to_float(v___x_173_);
return v___x_174_;
}
}
static double _init_l_instInhabitedFloat(void){
_start:
{
double v___x_175_; 
v___x_175_ = lean_float_once(&l_instInhabitedFloat___closed__0, &l_instInhabitedFloat___closed__0_once, _init_l_instInhabitedFloat___closed__0);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Float_repr(double v_n_176_, lean_object* v_prec_177_){
_start:
{
double v___x_178_; uint8_t v___x_179_; 
v___x_178_ = lean_float_once(&l_instInhabitedFloat___closed__0, &l_instInhabitedFloat___closed__0_once, _init_l_instInhabitedFloat___closed__0);
v___x_179_ = lean_float_decLt(v_n_176_, v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_float_to_string(v_n_176_);
v___x_181_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
return v___x_181_;
}
else
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_182_ = lean_float_to_string(v_n_176_);
v___x_183_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
v___x_184_ = l_Repr_addAppParen(v___x_183_, v_prec_177_);
return v___x_184_;
}
}
}
LEAN_EXPORT lean_object* l_Float_repr___boxed(lean_object* v_n_185_, lean_object* v_prec_186_){
_start:
{
double v_n_boxed_187_; lean_object* v_res_188_; 
v_n_boxed_187_ = lean_unbox_float(v_n_185_);
lean_dec_ref(v_n_185_);
v_res_188_ = l_Float_repr(v_n_boxed_187_, v_prec_186_);
lean_dec(v_prec_186_);
return v_res_188_;
}
}
static lean_object* _init_l_instReprAtomFloat(void){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = lean_box(0);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Float_sin___boxed(lean_object* v_a_00___x40___internal___hyg_193_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_194_; double v_res_195_; lean_object* v_r_196_; 
v_a_00___x40___internal___hyg_1__boxed_194_ = lean_unbox_float(v_a_00___x40___internal___hyg_193_);
lean_dec_ref(v_a_00___x40___internal___hyg_193_);
v_res_195_ = sin(v_a_00___x40___internal___hyg_1__boxed_194_);
v_r_196_ = lean_box_float(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT lean_object* l_Float_cos___boxed(lean_object* v_a_00___x40___internal___hyg_198_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_199_; double v_res_200_; lean_object* v_r_201_; 
v_a_00___x40___internal___hyg_1__boxed_199_ = lean_unbox_float(v_a_00___x40___internal___hyg_198_);
lean_dec_ref(v_a_00___x40___internal___hyg_198_);
v_res_200_ = cos(v_a_00___x40___internal___hyg_1__boxed_199_);
v_r_201_ = lean_box_float(v_res_200_);
return v_r_201_;
}
}
LEAN_EXPORT lean_object* l_Float_tan___boxed(lean_object* v_a_00___x40___internal___hyg_203_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_204_; double v_res_205_; lean_object* v_r_206_; 
v_a_00___x40___internal___hyg_1__boxed_204_ = lean_unbox_float(v_a_00___x40___internal___hyg_203_);
lean_dec_ref(v_a_00___x40___internal___hyg_203_);
v_res_205_ = tan(v_a_00___x40___internal___hyg_1__boxed_204_);
v_r_206_ = lean_box_float(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT lean_object* l_Float_asin___boxed(lean_object* v_a_00___x40___internal___hyg_208_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_209_; double v_res_210_; lean_object* v_r_211_; 
v_a_00___x40___internal___hyg_1__boxed_209_ = lean_unbox_float(v_a_00___x40___internal___hyg_208_);
lean_dec_ref(v_a_00___x40___internal___hyg_208_);
v_res_210_ = asin(v_a_00___x40___internal___hyg_1__boxed_209_);
v_r_211_ = lean_box_float(v_res_210_);
return v_r_211_;
}
}
LEAN_EXPORT lean_object* l_Float_acos___boxed(lean_object* v_a_00___x40___internal___hyg_213_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_214_; double v_res_215_; lean_object* v_r_216_; 
v_a_00___x40___internal___hyg_1__boxed_214_ = lean_unbox_float(v_a_00___x40___internal___hyg_213_);
lean_dec_ref(v_a_00___x40___internal___hyg_213_);
v_res_215_ = acos(v_a_00___x40___internal___hyg_1__boxed_214_);
v_r_216_ = lean_box_float(v_res_215_);
return v_r_216_;
}
}
LEAN_EXPORT lean_object* l_Float_atan___boxed(lean_object* v_a_00___x40___internal___hyg_218_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_219_; double v_res_220_; lean_object* v_r_221_; 
v_a_00___x40___internal___hyg_1__boxed_219_ = lean_unbox_float(v_a_00___x40___internal___hyg_218_);
lean_dec_ref(v_a_00___x40___internal___hyg_218_);
v_res_220_ = atan(v_a_00___x40___internal___hyg_1__boxed_219_);
v_r_221_ = lean_box_float(v_res_220_);
return v_r_221_;
}
}
LEAN_EXPORT lean_object* l_Float_atan2___boxed(lean_object* v_y_224_, lean_object* v_x_225_){
_start:
{
double v_y_boxed_226_; double v_x_boxed_227_; double v_res_228_; lean_object* v_r_229_; 
v_y_boxed_226_ = lean_unbox_float(v_y_224_);
lean_dec_ref(v_y_224_);
v_x_boxed_227_ = lean_unbox_float(v_x_225_);
lean_dec_ref(v_x_225_);
v_res_228_ = atan2(v_y_boxed_226_, v_x_boxed_227_);
v_r_229_ = lean_box_float(v_res_228_);
return v_r_229_;
}
}
LEAN_EXPORT lean_object* l_Float_sinh___boxed(lean_object* v_a_00___x40___internal___hyg_231_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_232_; double v_res_233_; lean_object* v_r_234_; 
v_a_00___x40___internal___hyg_1__boxed_232_ = lean_unbox_float(v_a_00___x40___internal___hyg_231_);
lean_dec_ref(v_a_00___x40___internal___hyg_231_);
v_res_233_ = sinh(v_a_00___x40___internal___hyg_1__boxed_232_);
v_r_234_ = lean_box_float(v_res_233_);
return v_r_234_;
}
}
LEAN_EXPORT lean_object* l_Float_cosh___boxed(lean_object* v_a_00___x40___internal___hyg_236_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_237_; double v_res_238_; lean_object* v_r_239_; 
v_a_00___x40___internal___hyg_1__boxed_237_ = lean_unbox_float(v_a_00___x40___internal___hyg_236_);
lean_dec_ref(v_a_00___x40___internal___hyg_236_);
v_res_238_ = cosh(v_a_00___x40___internal___hyg_1__boxed_237_);
v_r_239_ = lean_box_float(v_res_238_);
return v_r_239_;
}
}
LEAN_EXPORT lean_object* l_Float_tanh___boxed(lean_object* v_a_00___x40___internal___hyg_241_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_242_; double v_res_243_; lean_object* v_r_244_; 
v_a_00___x40___internal___hyg_1__boxed_242_ = lean_unbox_float(v_a_00___x40___internal___hyg_241_);
lean_dec_ref(v_a_00___x40___internal___hyg_241_);
v_res_243_ = tanh(v_a_00___x40___internal___hyg_1__boxed_242_);
v_r_244_ = lean_box_float(v_res_243_);
return v_r_244_;
}
}
LEAN_EXPORT lean_object* l_Float_asinh___boxed(lean_object* v_a_00___x40___internal___hyg_246_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_247_; double v_res_248_; lean_object* v_r_249_; 
v_a_00___x40___internal___hyg_1__boxed_247_ = lean_unbox_float(v_a_00___x40___internal___hyg_246_);
lean_dec_ref(v_a_00___x40___internal___hyg_246_);
v_res_248_ = asinh(v_a_00___x40___internal___hyg_1__boxed_247_);
v_r_249_ = lean_box_float(v_res_248_);
return v_r_249_;
}
}
LEAN_EXPORT lean_object* l_Float_acosh___boxed(lean_object* v_a_00___x40___internal___hyg_251_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_252_; double v_res_253_; lean_object* v_r_254_; 
v_a_00___x40___internal___hyg_1__boxed_252_ = lean_unbox_float(v_a_00___x40___internal___hyg_251_);
lean_dec_ref(v_a_00___x40___internal___hyg_251_);
v_res_253_ = acosh(v_a_00___x40___internal___hyg_1__boxed_252_);
v_r_254_ = lean_box_float(v_res_253_);
return v_r_254_;
}
}
LEAN_EXPORT lean_object* l_Float_atanh___boxed(lean_object* v_a_00___x40___internal___hyg_256_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_257_; double v_res_258_; lean_object* v_r_259_; 
v_a_00___x40___internal___hyg_1__boxed_257_ = lean_unbox_float(v_a_00___x40___internal___hyg_256_);
lean_dec_ref(v_a_00___x40___internal___hyg_256_);
v_res_258_ = atanh(v_a_00___x40___internal___hyg_1__boxed_257_);
v_r_259_ = lean_box_float(v_res_258_);
return v_r_259_;
}
}
LEAN_EXPORT lean_object* l_Float_exp___boxed(lean_object* v_x_261_){
_start:
{
double v_x_boxed_262_; double v_res_263_; lean_object* v_r_264_; 
v_x_boxed_262_ = lean_unbox_float(v_x_261_);
lean_dec_ref(v_x_261_);
v_res_263_ = exp(v_x_boxed_262_);
v_r_264_ = lean_box_float(v_res_263_);
return v_r_264_;
}
}
LEAN_EXPORT lean_object* l_Float_exp2___boxed(lean_object* v_x_266_){
_start:
{
double v_x_boxed_267_; double v_res_268_; lean_object* v_r_269_; 
v_x_boxed_267_ = lean_unbox_float(v_x_266_);
lean_dec_ref(v_x_266_);
v_res_268_ = exp2(v_x_boxed_267_);
v_r_269_ = lean_box_float(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT lean_object* l_Float_log___boxed(lean_object* v_x_271_){
_start:
{
double v_x_boxed_272_; double v_res_273_; lean_object* v_r_274_; 
v_x_boxed_272_ = lean_unbox_float(v_x_271_);
lean_dec_ref(v_x_271_);
v_res_273_ = log(v_x_boxed_272_);
v_r_274_ = lean_box_float(v_res_273_);
return v_r_274_;
}
}
LEAN_EXPORT lean_object* l_Float_log2___boxed(lean_object* v_a_00___x40___internal___hyg_276_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_277_; double v_res_278_; lean_object* v_r_279_; 
v_a_00___x40___internal___hyg_1__boxed_277_ = lean_unbox_float(v_a_00___x40___internal___hyg_276_);
lean_dec_ref(v_a_00___x40___internal___hyg_276_);
v_res_278_ = log2(v_a_00___x40___internal___hyg_1__boxed_277_);
v_r_279_ = lean_box_float(v_res_278_);
return v_r_279_;
}
}
LEAN_EXPORT lean_object* l_Float_log10___boxed(lean_object* v_a_00___x40___internal___hyg_281_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_282_; double v_res_283_; lean_object* v_r_284_; 
v_a_00___x40___internal___hyg_1__boxed_282_ = lean_unbox_float(v_a_00___x40___internal___hyg_281_);
lean_dec_ref(v_a_00___x40___internal___hyg_281_);
v_res_283_ = log10(v_a_00___x40___internal___hyg_1__boxed_282_);
v_r_284_ = lean_box_float(v_res_283_);
return v_r_284_;
}
}
LEAN_EXPORT lean_object* l_Float_pow___boxed(lean_object* v_a_00___x40___internal___hyg_287_, lean_object* v_a_00___x40___internal___hyg_288_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_289_; double v_a_00___x40___internal___hyg_2__boxed_290_; double v_res_291_; lean_object* v_r_292_; 
v_a_00___x40___internal___hyg_1__boxed_289_ = lean_unbox_float(v_a_00___x40___internal___hyg_287_);
lean_dec_ref(v_a_00___x40___internal___hyg_287_);
v_a_00___x40___internal___hyg_2__boxed_290_ = lean_unbox_float(v_a_00___x40___internal___hyg_288_);
lean_dec_ref(v_a_00___x40___internal___hyg_288_);
v_res_291_ = pow(v_a_00___x40___internal___hyg_1__boxed_289_, v_a_00___x40___internal___hyg_2__boxed_290_);
v_r_292_ = lean_box_float(v_res_291_);
return v_r_292_;
}
}
LEAN_EXPORT lean_object* l_Float_sqrt___boxed(lean_object* v_a_00___x40___internal___hyg_294_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_295_; double v_res_296_; lean_object* v_r_297_; 
v_a_00___x40___internal___hyg_1__boxed_295_ = lean_unbox_float(v_a_00___x40___internal___hyg_294_);
lean_dec_ref(v_a_00___x40___internal___hyg_294_);
v_res_296_ = sqrt(v_a_00___x40___internal___hyg_1__boxed_295_);
v_r_297_ = lean_box_float(v_res_296_);
return v_r_297_;
}
}
LEAN_EXPORT lean_object* l_Float_cbrt___boxed(lean_object* v_a_00___x40___internal___hyg_299_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_300_; double v_res_301_; lean_object* v_r_302_; 
v_a_00___x40___internal___hyg_1__boxed_300_ = lean_unbox_float(v_a_00___x40___internal___hyg_299_);
lean_dec_ref(v_a_00___x40___internal___hyg_299_);
v_res_301_ = cbrt(v_a_00___x40___internal___hyg_1__boxed_300_);
v_r_302_ = lean_box_float(v_res_301_);
return v_r_302_;
}
}
LEAN_EXPORT lean_object* l_Float_ceil___boxed(lean_object* v_a_00___x40___internal___hyg_304_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_305_; double v_res_306_; lean_object* v_r_307_; 
v_a_00___x40___internal___hyg_1__boxed_305_ = lean_unbox_float(v_a_00___x40___internal___hyg_304_);
lean_dec_ref(v_a_00___x40___internal___hyg_304_);
v_res_306_ = ceil(v_a_00___x40___internal___hyg_1__boxed_305_);
v_r_307_ = lean_box_float(v_res_306_);
return v_r_307_;
}
}
LEAN_EXPORT lean_object* l_Float_floor___boxed(lean_object* v_a_00___x40___internal___hyg_309_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_310_; double v_res_311_; lean_object* v_r_312_; 
v_a_00___x40___internal___hyg_1__boxed_310_ = lean_unbox_float(v_a_00___x40___internal___hyg_309_);
lean_dec_ref(v_a_00___x40___internal___hyg_309_);
v_res_311_ = floor(v_a_00___x40___internal___hyg_1__boxed_310_);
v_r_312_ = lean_box_float(v_res_311_);
return v_r_312_;
}
}
LEAN_EXPORT lean_object* l_Float_round___boxed(lean_object* v_a_00___x40___internal___hyg_314_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_315_; double v_res_316_; lean_object* v_r_317_; 
v_a_00___x40___internal___hyg_1__boxed_315_ = lean_unbox_float(v_a_00___x40___internal___hyg_314_);
lean_dec_ref(v_a_00___x40___internal___hyg_314_);
v_res_316_ = round(v_a_00___x40___internal___hyg_1__boxed_315_);
v_r_317_ = lean_box_float(v_res_316_);
return v_r_317_;
}
}
LEAN_EXPORT lean_object* l_Float_abs___boxed(lean_object* v_a_00___x40___internal___hyg_319_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_320_; double v_res_321_; lean_object* v_r_322_; 
v_a_00___x40___internal___hyg_1__boxed_320_ = lean_unbox_float(v_a_00___x40___internal___hyg_319_);
lean_dec_ref(v_a_00___x40___internal___hyg_319_);
v_res_321_ = fabs(v_a_00___x40___internal___hyg_1__boxed_320_);
v_r_322_ = lean_box_float(v_res_321_);
return v_r_322_;
}
}
LEAN_EXPORT double l_instMinFloat___lam__0(double v_x_325_, double v_y_326_){
_start:
{
uint8_t v___x_327_; 
v___x_327_ = lean_float_decLe(v_x_325_, v_y_326_);
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
LEAN_EXPORT lean_object* l_instMinFloat___lam__0___boxed(lean_object* v_x_328_, lean_object* v_y_329_){
_start:
{
double v_x_boxed_330_; double v_y_boxed_331_; double v_res_332_; lean_object* v_r_333_; 
v_x_boxed_330_ = lean_unbox_float(v_x_328_);
lean_dec_ref(v_x_328_);
v_y_boxed_331_ = lean_unbox_float(v_y_329_);
lean_dec_ref(v_y_329_);
v_res_332_ = l_instMinFloat___lam__0(v_x_boxed_330_, v_y_boxed_331_);
v_r_333_ = lean_box_float(v_res_332_);
return v_r_333_;
}
}
LEAN_EXPORT double l_instMaxFloat___lam__0(double v_x_336_, double v_y_337_){
_start:
{
uint8_t v___x_338_; 
v___x_338_ = lean_float_decLe(v_x_336_, v_y_337_);
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
LEAN_EXPORT lean_object* l_instMaxFloat___lam__0___boxed(lean_object* v_x_339_, lean_object* v_y_340_){
_start:
{
double v_x_boxed_341_; double v_y_boxed_342_; double v_res_343_; lean_object* v_r_344_; 
v_x_boxed_341_ = lean_unbox_float(v_x_339_);
lean_dec_ref(v_x_339_);
v_y_boxed_342_ = lean_unbox_float(v_y_340_);
lean_dec_ref(v_y_340_);
v_res_343_ = l_instMaxFloat___lam__0(v_x_boxed_341_, v_y_boxed_342_);
v_r_344_ = lean_box_float(v_res_343_);
return v_r_344_;
}
}
LEAN_EXPORT lean_object* l_Float_scaleB___boxed(lean_object* v_x_349_, lean_object* v_i_350_){
_start:
{
double v_x_boxed_351_; double v_res_352_; lean_object* v_r_353_; 
v_x_boxed_351_ = lean_unbox_float(v_x_349_);
lean_dec_ref(v_x_349_);
v_res_352_ = lean_float_scaleb(v_x_boxed_351_, v_i_350_);
lean_dec(v_i_350_);
v_r_353_ = lean_box_float(v_res_352_);
return v_r_353_;
}
}
lean_object* runtime_initialize_Init_Data_ToString_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_floatSpec = _init_l_floatSpec();
lean_mark_persistent(l_floatSpec);
l_instLTFloat = _init_l_instLTFloat();
lean_mark_persistent(l_instLTFloat);
l_instLEFloat = _init_l_instLEFloat();
lean_mark_persistent(l_instLEFloat);
l_instInhabitedFloat = _init_l_instInhabitedFloat();
l_instReprAtomFloat = _init_l_instReprAtomFloat();
lean_mark_persistent(l_instReprAtomFloat);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Float(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Float(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Float(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Float(builtin);
}
#ifdef __cplusplus
}
#endif
