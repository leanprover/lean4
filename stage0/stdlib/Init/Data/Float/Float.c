// Lean compiler output
// Module: Init.Data.Float.Float
// Imports: public import Init.Data.ToString.Basic public import Init.Data.Float.Model.Float
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
uint64_t lean_float_to_bits(double);
LEAN_EXPORT lean_object* l_Float_toModel___boxed(lean_object*);
double lean_float_of_bits(uint64_t);
LEAN_EXPORT lean_object* l_Float_ofModel___boxed(lean_object*);
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
uint8_t lean_float_decLt(double, double);
LEAN_EXPORT lean_object* l_Float_lt___boxed(lean_object*, lean_object*);
uint8_t lean_float_decLe(double, double);
LEAN_EXPORT lean_object* l_Float_le___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Float_toModel___boxed(lean_object* v_self_2_){
_start:
{
double v_self_boxed_3_; uint64_t v_res_4_; lean_object* v_r_5_; 
v_self_boxed_3_ = lean_unbox_float(v_self_2_);
lean_dec_ref(v_self_2_);
v_res_4_ = lean_float_to_bits(v_self_boxed_3_);
v_r_5_ = lean_box_uint64(v_res_4_);
return v_r_5_;
}
}
LEAN_EXPORT lean_object* l_Float_ofModel___boxed(lean_object* v_toModel_7_){
_start:
{
uint64_t v_toModel_boxed_8_; double v_res_9_; lean_object* v_r_10_; 
v_toModel_boxed_8_ = lean_unbox_uint64(v_toModel_7_);
lean_dec_ref(v_toModel_7_);
v_res_9_ = lean_float_of_bits(v_toModel_boxed_8_);
v_r_10_ = lean_box_float(v_res_9_);
return v_r_10_;
}
}
LEAN_EXPORT lean_object* l_Float_add___boxed(lean_object* v_a_00___x40___internal___hyg_13_, lean_object* v_a_00___x40___internal___hyg_14_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_15_; double v_a_00___x40___internal___hyg_2__boxed_16_; double v_res_17_; lean_object* v_r_18_; 
v_a_00___x40___internal___hyg_1__boxed_15_ = lean_unbox_float(v_a_00___x40___internal___hyg_13_);
lean_dec_ref(v_a_00___x40___internal___hyg_13_);
v_a_00___x40___internal___hyg_2__boxed_16_ = lean_unbox_float(v_a_00___x40___internal___hyg_14_);
lean_dec_ref(v_a_00___x40___internal___hyg_14_);
v_res_17_ = lean_float_add(v_a_00___x40___internal___hyg_1__boxed_15_, v_a_00___x40___internal___hyg_2__boxed_16_);
v_r_18_ = lean_box_float(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT lean_object* l_Float_sub___boxed(lean_object* v_a_00___x40___internal___hyg_21_, lean_object* v_a_00___x40___internal___hyg_22_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_23_; double v_a_00___x40___internal___hyg_2__boxed_24_; double v_res_25_; lean_object* v_r_26_; 
v_a_00___x40___internal___hyg_1__boxed_23_ = lean_unbox_float(v_a_00___x40___internal___hyg_21_);
lean_dec_ref(v_a_00___x40___internal___hyg_21_);
v_a_00___x40___internal___hyg_2__boxed_24_ = lean_unbox_float(v_a_00___x40___internal___hyg_22_);
lean_dec_ref(v_a_00___x40___internal___hyg_22_);
v_res_25_ = lean_float_sub(v_a_00___x40___internal___hyg_1__boxed_23_, v_a_00___x40___internal___hyg_2__boxed_24_);
v_r_26_ = lean_box_float(v_res_25_);
return v_r_26_;
}
}
LEAN_EXPORT lean_object* l_Float_mul___boxed(lean_object* v_a_00___x40___internal___hyg_29_, lean_object* v_a_00___x40___internal___hyg_30_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_31_; double v_a_00___x40___internal___hyg_2__boxed_32_; double v_res_33_; lean_object* v_r_34_; 
v_a_00___x40___internal___hyg_1__boxed_31_ = lean_unbox_float(v_a_00___x40___internal___hyg_29_);
lean_dec_ref(v_a_00___x40___internal___hyg_29_);
v_a_00___x40___internal___hyg_2__boxed_32_ = lean_unbox_float(v_a_00___x40___internal___hyg_30_);
lean_dec_ref(v_a_00___x40___internal___hyg_30_);
v_res_33_ = lean_float_mul(v_a_00___x40___internal___hyg_1__boxed_31_, v_a_00___x40___internal___hyg_2__boxed_32_);
v_r_34_ = lean_box_float(v_res_33_);
return v_r_34_;
}
}
LEAN_EXPORT lean_object* l_Float_div___boxed(lean_object* v_a_00___x40___internal___hyg_37_, lean_object* v_a_00___x40___internal___hyg_38_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_39_; double v_a_00___x40___internal___hyg_2__boxed_40_; double v_res_41_; lean_object* v_r_42_; 
v_a_00___x40___internal___hyg_1__boxed_39_ = lean_unbox_float(v_a_00___x40___internal___hyg_37_);
lean_dec_ref(v_a_00___x40___internal___hyg_37_);
v_a_00___x40___internal___hyg_2__boxed_40_ = lean_unbox_float(v_a_00___x40___internal___hyg_38_);
lean_dec_ref(v_a_00___x40___internal___hyg_38_);
v_res_41_ = lean_float_div(v_a_00___x40___internal___hyg_1__boxed_39_, v_a_00___x40___internal___hyg_2__boxed_40_);
v_r_42_ = lean_box_float(v_res_41_);
return v_r_42_;
}
}
LEAN_EXPORT lean_object* l_Float_neg___boxed(lean_object* v_a_00___x40___internal___hyg_44_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_45_; double v_res_46_; lean_object* v_r_47_; 
v_a_00___x40___internal___hyg_1__boxed_45_ = lean_unbox_float(v_a_00___x40___internal___hyg_44_);
lean_dec_ref(v_a_00___x40___internal___hyg_44_);
v_res_46_ = lean_float_negate(v_a_00___x40___internal___hyg_1__boxed_45_);
v_r_47_ = lean_box_float(v_res_46_);
return v_r_47_;
}
}
LEAN_EXPORT lean_object* l_Float_lt___boxed(lean_object* v_a_00___x40___internal___hyg_50_, lean_object* v_a_00___x40___internal___hyg_51_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_52_; double v_a_00___x40___internal___hyg_2__boxed_53_; uint8_t v_res_54_; lean_object* v_r_55_; 
v_a_00___x40___internal___hyg_1__boxed_52_ = lean_unbox_float(v_a_00___x40___internal___hyg_50_);
lean_dec_ref(v_a_00___x40___internal___hyg_50_);
v_a_00___x40___internal___hyg_2__boxed_53_ = lean_unbox_float(v_a_00___x40___internal___hyg_51_);
lean_dec_ref(v_a_00___x40___internal___hyg_51_);
v_res_54_ = lean_float_decLt(v_a_00___x40___internal___hyg_1__boxed_52_, v_a_00___x40___internal___hyg_2__boxed_53_);
v_r_55_ = lean_box(v_res_54_);
return v_r_55_;
}
}
LEAN_EXPORT lean_object* l_Float_le___boxed(lean_object* v_a_00___x40___internal___hyg_58_, lean_object* v_a_00___x40___internal___hyg_59_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_60_; double v_a_00___x40___internal___hyg_2__boxed_61_; uint8_t v_res_62_; lean_object* v_r_63_; 
v_a_00___x40___internal___hyg_1__boxed_60_ = lean_unbox_float(v_a_00___x40___internal___hyg_58_);
lean_dec_ref(v_a_00___x40___internal___hyg_58_);
v_a_00___x40___internal___hyg_2__boxed_61_ = lean_unbox_float(v_a_00___x40___internal___hyg_59_);
lean_dec_ref(v_a_00___x40___internal___hyg_59_);
v_res_62_ = lean_float_decLe(v_a_00___x40___internal___hyg_1__boxed_60_, v_a_00___x40___internal___hyg_2__boxed_61_);
v_r_63_ = lean_box(v_res_62_);
return v_r_63_;
}
}
LEAN_EXPORT lean_object* l_Float_ofBits___boxed(lean_object* v_a_00___x40___internal___hyg_65_){
_start:
{
uint64_t v_a_00___x40___internal___hyg_1__boxed_66_; double v_res_67_; lean_object* v_r_68_; 
v_a_00___x40___internal___hyg_1__boxed_66_ = lean_unbox_uint64(v_a_00___x40___internal___hyg_65_);
lean_dec_ref(v_a_00___x40___internal___hyg_65_);
v_res_67_ = lean_float_of_bits(v_a_00___x40___internal___hyg_1__boxed_66_);
v_r_68_ = lean_box_float(v_res_67_);
return v_r_68_;
}
}
LEAN_EXPORT lean_object* l_Float_toBits___boxed(lean_object* v_a_00___x40___internal___hyg_70_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_71_; uint64_t v_res_72_; lean_object* v_r_73_; 
v_a_00___x40___internal___hyg_1__boxed_71_ = lean_unbox_float(v_a_00___x40___internal___hyg_70_);
lean_dec_ref(v_a_00___x40___internal___hyg_70_);
v_res_72_ = lean_float_to_bits(v_a_00___x40___internal___hyg_1__boxed_71_);
v_r_73_ = lean_box_uint64(v_res_72_);
return v_r_73_;
}
}
static lean_object* _init_l_instLTFloat(void){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lean_box(0);
return v___x_84_;
}
}
static lean_object* _init_l_instLEFloat(void){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = lean_box(0);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Float_beq___boxed(lean_object* v_a_88_, lean_object* v_b_89_){
_start:
{
double v_a_boxed_90_; double v_b_boxed_91_; uint8_t v_res_92_; lean_object* v_r_93_; 
v_a_boxed_90_ = lean_unbox_float(v_a_88_);
lean_dec_ref(v_a_88_);
v_b_boxed_91_ = lean_unbox_float(v_b_89_);
lean_dec_ref(v_b_89_);
v_res_92_ = lean_float_beq(v_a_boxed_90_, v_b_boxed_91_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
LEAN_EXPORT lean_object* l_Float_decLt___boxed(lean_object* v_a_98_, lean_object* v_b_99_){
_start:
{
double v_a_boxed_100_; double v_b_boxed_101_; uint8_t v_res_102_; lean_object* v_r_103_; 
v_a_boxed_100_ = lean_unbox_float(v_a_98_);
lean_dec_ref(v_a_98_);
v_b_boxed_101_ = lean_unbox_float(v_b_99_);
lean_dec_ref(v_b_99_);
v_res_102_ = lean_float_decLt(v_a_boxed_100_, v_b_boxed_101_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
LEAN_EXPORT lean_object* l_Float_decLe___boxed(lean_object* v_a_106_, lean_object* v_b_107_){
_start:
{
double v_a_boxed_108_; double v_b_boxed_109_; uint8_t v_res_110_; lean_object* v_r_111_; 
v_a_boxed_108_ = lean_unbox_float(v_a_106_);
lean_dec_ref(v_a_106_);
v_b_boxed_109_ = lean_unbox_float(v_b_107_);
lean_dec_ref(v_b_107_);
v_res_110_ = lean_float_decLe(v_a_boxed_108_, v_b_boxed_109_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT lean_object* l_Float_toString___boxed(lean_object* v_a_00___x40___internal___hyg_113_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_114_; lean_object* v_res_115_; 
v_a_00___x40___internal___hyg_1__boxed_114_ = lean_unbox_float(v_a_00___x40___internal___hyg_113_);
lean_dec_ref(v_a_00___x40___internal___hyg_113_);
v_res_115_ = lean_float_to_string(v_a_00___x40___internal___hyg_1__boxed_114_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Float_toUInt8___boxed(lean_object* v_a_00___x40___internal___hyg_117_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_118_; uint8_t v_res_119_; lean_object* v_r_120_; 
v_a_00___x40___internal___hyg_1__boxed_118_ = lean_unbox_float(v_a_00___x40___internal___hyg_117_);
lean_dec_ref(v_a_00___x40___internal___hyg_117_);
v_res_119_ = lean_float_to_uint8(v_a_00___x40___internal___hyg_1__boxed_118_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
LEAN_EXPORT lean_object* l_Float_toUInt16___boxed(lean_object* v_a_00___x40___internal___hyg_122_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_123_; uint16_t v_res_124_; lean_object* v_r_125_; 
v_a_00___x40___internal___hyg_1__boxed_123_ = lean_unbox_float(v_a_00___x40___internal___hyg_122_);
lean_dec_ref(v_a_00___x40___internal___hyg_122_);
v_res_124_ = lean_float_to_uint16(v_a_00___x40___internal___hyg_1__boxed_123_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
LEAN_EXPORT lean_object* l_Float_toUInt32___boxed(lean_object* v_a_00___x40___internal___hyg_127_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_128_; uint32_t v_res_129_; lean_object* v_r_130_; 
v_a_00___x40___internal___hyg_1__boxed_128_ = lean_unbox_float(v_a_00___x40___internal___hyg_127_);
lean_dec_ref(v_a_00___x40___internal___hyg_127_);
v_res_129_ = lean_float_to_uint32(v_a_00___x40___internal___hyg_1__boxed_128_);
v_r_130_ = lean_box_uint32(v_res_129_);
return v_r_130_;
}
}
LEAN_EXPORT lean_object* l_Float_toUInt64___boxed(lean_object* v_a_00___x40___internal___hyg_132_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_133_; uint64_t v_res_134_; lean_object* v_r_135_; 
v_a_00___x40___internal___hyg_1__boxed_133_ = lean_unbox_float(v_a_00___x40___internal___hyg_132_);
lean_dec_ref(v_a_00___x40___internal___hyg_132_);
v_res_134_ = lean_float_to_uint64(v_a_00___x40___internal___hyg_1__boxed_133_);
v_r_135_ = lean_box_uint64(v_res_134_);
return v_r_135_;
}
}
LEAN_EXPORT lean_object* l_Float_toUSize___boxed(lean_object* v_a_00___x40___internal___hyg_137_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_138_; size_t v_res_139_; lean_object* v_r_140_; 
v_a_00___x40___internal___hyg_1__boxed_138_ = lean_unbox_float(v_a_00___x40___internal___hyg_137_);
lean_dec_ref(v_a_00___x40___internal___hyg_137_);
v_res_139_ = lean_float_to_usize(v_a_00___x40___internal___hyg_1__boxed_138_);
v_r_140_ = lean_box_usize(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT lean_object* l_Float_isNaN___boxed(lean_object* v_a_00___x40___internal___hyg_142_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_143_; uint8_t v_res_144_; lean_object* v_r_145_; 
v_a_00___x40___internal___hyg_1__boxed_143_ = lean_unbox_float(v_a_00___x40___internal___hyg_142_);
lean_dec_ref(v_a_00___x40___internal___hyg_142_);
v_res_144_ = lean_float_isnan(v_a_00___x40___internal___hyg_1__boxed_143_);
v_r_145_ = lean_box(v_res_144_);
return v_r_145_;
}
}
LEAN_EXPORT lean_object* l_Float_isFinite___boxed(lean_object* v_a_00___x40___internal___hyg_147_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_148_; uint8_t v_res_149_; lean_object* v_r_150_; 
v_a_00___x40___internal___hyg_1__boxed_148_ = lean_unbox_float(v_a_00___x40___internal___hyg_147_);
lean_dec_ref(v_a_00___x40___internal___hyg_147_);
v_res_149_ = lean_float_isfinite(v_a_00___x40___internal___hyg_1__boxed_148_);
v_r_150_ = lean_box(v_res_149_);
return v_r_150_;
}
}
LEAN_EXPORT lean_object* l_Float_isInf___boxed(lean_object* v_a_00___x40___internal___hyg_152_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_153_; uint8_t v_res_154_; lean_object* v_r_155_; 
v_a_00___x40___internal___hyg_1__boxed_153_ = lean_unbox_float(v_a_00___x40___internal___hyg_152_);
lean_dec_ref(v_a_00___x40___internal___hyg_152_);
v_res_154_ = lean_float_isinf(v_a_00___x40___internal___hyg_1__boxed_153_);
v_r_155_ = lean_box(v_res_154_);
return v_r_155_;
}
}
LEAN_EXPORT lean_object* l_Float_frExp___boxed(lean_object* v_a_00___x40___internal___hyg_157_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_158_; lean_object* v_res_159_; 
v_a_00___x40___internal___hyg_1__boxed_158_ = lean_unbox_float(v_a_00___x40___internal___hyg_157_);
lean_dec_ref(v_a_00___x40___internal___hyg_157_);
v_res_159_ = lean_float_frexp(v_a_00___x40___internal___hyg_1__boxed_158_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_UInt8_toFloat___boxed(lean_object* v_n_163_){
_start:
{
uint8_t v_n_boxed_164_; double v_res_165_; lean_object* v_r_166_; 
v_n_boxed_164_ = lean_unbox(v_n_163_);
v_res_165_ = lean_uint8_to_float(v_n_boxed_164_);
v_r_166_ = lean_box_float(v_res_165_);
return v_r_166_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toFloat___boxed(lean_object* v_n_168_){
_start:
{
uint16_t v_n_boxed_169_; double v_res_170_; lean_object* v_r_171_; 
v_n_boxed_169_ = lean_unbox(v_n_168_);
v_res_170_ = lean_uint16_to_float(v_n_boxed_169_);
v_r_171_ = lean_box_float(v_res_170_);
return v_r_171_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toFloat___boxed(lean_object* v_n_173_){
_start:
{
uint32_t v_n_boxed_174_; double v_res_175_; lean_object* v_r_176_; 
v_n_boxed_174_ = lean_unbox_uint32(v_n_173_);
lean_dec(v_n_173_);
v_res_175_ = lean_uint32_to_float(v_n_boxed_174_);
v_r_176_ = lean_box_float(v_res_175_);
return v_r_176_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toFloat___boxed(lean_object* v_n_178_){
_start:
{
uint64_t v_n_boxed_179_; double v_res_180_; lean_object* v_r_181_; 
v_n_boxed_179_ = lean_unbox_uint64(v_n_178_);
lean_dec_ref(v_n_178_);
v_res_180_ = lean_uint64_to_float(v_n_boxed_179_);
v_r_181_ = lean_box_float(v_res_180_);
return v_r_181_;
}
}
LEAN_EXPORT lean_object* l_USize_toFloat___boxed(lean_object* v_n_183_){
_start:
{
size_t v_n_boxed_184_; double v_res_185_; lean_object* v_r_186_; 
v_n_boxed_184_ = lean_unbox_usize(v_n_183_);
lean_dec(v_n_183_);
v_res_185_ = lean_usize_to_float(v_n_boxed_184_);
v_r_186_ = lean_box_float(v_res_185_);
return v_r_186_;
}
}
static double _init_l_instInhabitedFloat___closed__0(void){
_start:
{
uint64_t v___x_187_; double v___x_188_; 
v___x_187_ = 0ULL;
v___x_188_ = lean_uint64_to_float(v___x_187_);
return v___x_188_;
}
}
static double _init_l_instInhabitedFloat(void){
_start:
{
double v___x_189_; 
v___x_189_ = lean_float_once(&l_instInhabitedFloat___closed__0, &l_instInhabitedFloat___closed__0_once, _init_l_instInhabitedFloat___closed__0);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Float_repr(double v_n_190_, lean_object* v_prec_191_){
_start:
{
double v___x_192_; uint8_t v___x_193_; 
v___x_192_ = lean_float_once(&l_instInhabitedFloat___closed__0, &l_instInhabitedFloat___closed__0_once, _init_l_instInhabitedFloat___closed__0);
v___x_193_ = lean_float_decLt(v_n_190_, v___x_192_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_float_to_string(v_n_190_);
v___x_195_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
return v___x_195_;
}
else
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_196_ = lean_float_to_string(v_n_190_);
v___x_197_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
v___x_198_ = l_Repr_addAppParen(v___x_197_, v_prec_191_);
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l_Float_repr___boxed(lean_object* v_n_199_, lean_object* v_prec_200_){
_start:
{
double v_n_boxed_201_; lean_object* v_res_202_; 
v_n_boxed_201_ = lean_unbox_float(v_n_199_);
lean_dec_ref(v_n_199_);
v_res_202_ = l_Float_repr(v_n_boxed_201_, v_prec_200_);
lean_dec(v_prec_200_);
return v_res_202_;
}
}
static lean_object* _init_l_instReprAtomFloat(void){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = lean_box(0);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Float_sin___boxed(lean_object* v_a_00___x40___internal___hyg_207_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_208_; double v_res_209_; lean_object* v_r_210_; 
v_a_00___x40___internal___hyg_1__boxed_208_ = lean_unbox_float(v_a_00___x40___internal___hyg_207_);
lean_dec_ref(v_a_00___x40___internal___hyg_207_);
v_res_209_ = sin(v_a_00___x40___internal___hyg_1__boxed_208_);
v_r_210_ = lean_box_float(v_res_209_);
return v_r_210_;
}
}
LEAN_EXPORT lean_object* l_Float_cos___boxed(lean_object* v_a_00___x40___internal___hyg_212_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_213_; double v_res_214_; lean_object* v_r_215_; 
v_a_00___x40___internal___hyg_1__boxed_213_ = lean_unbox_float(v_a_00___x40___internal___hyg_212_);
lean_dec_ref(v_a_00___x40___internal___hyg_212_);
v_res_214_ = cos(v_a_00___x40___internal___hyg_1__boxed_213_);
v_r_215_ = lean_box_float(v_res_214_);
return v_r_215_;
}
}
LEAN_EXPORT lean_object* l_Float_tan___boxed(lean_object* v_a_00___x40___internal___hyg_217_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_218_; double v_res_219_; lean_object* v_r_220_; 
v_a_00___x40___internal___hyg_1__boxed_218_ = lean_unbox_float(v_a_00___x40___internal___hyg_217_);
lean_dec_ref(v_a_00___x40___internal___hyg_217_);
v_res_219_ = tan(v_a_00___x40___internal___hyg_1__boxed_218_);
v_r_220_ = lean_box_float(v_res_219_);
return v_r_220_;
}
}
LEAN_EXPORT lean_object* l_Float_asin___boxed(lean_object* v_a_00___x40___internal___hyg_222_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_223_; double v_res_224_; lean_object* v_r_225_; 
v_a_00___x40___internal___hyg_1__boxed_223_ = lean_unbox_float(v_a_00___x40___internal___hyg_222_);
lean_dec_ref(v_a_00___x40___internal___hyg_222_);
v_res_224_ = asin(v_a_00___x40___internal___hyg_1__boxed_223_);
v_r_225_ = lean_box_float(v_res_224_);
return v_r_225_;
}
}
LEAN_EXPORT lean_object* l_Float_acos___boxed(lean_object* v_a_00___x40___internal___hyg_227_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_228_; double v_res_229_; lean_object* v_r_230_; 
v_a_00___x40___internal___hyg_1__boxed_228_ = lean_unbox_float(v_a_00___x40___internal___hyg_227_);
lean_dec_ref(v_a_00___x40___internal___hyg_227_);
v_res_229_ = acos(v_a_00___x40___internal___hyg_1__boxed_228_);
v_r_230_ = lean_box_float(v_res_229_);
return v_r_230_;
}
}
LEAN_EXPORT lean_object* l_Float_atan___boxed(lean_object* v_a_00___x40___internal___hyg_232_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_233_; double v_res_234_; lean_object* v_r_235_; 
v_a_00___x40___internal___hyg_1__boxed_233_ = lean_unbox_float(v_a_00___x40___internal___hyg_232_);
lean_dec_ref(v_a_00___x40___internal___hyg_232_);
v_res_234_ = atan(v_a_00___x40___internal___hyg_1__boxed_233_);
v_r_235_ = lean_box_float(v_res_234_);
return v_r_235_;
}
}
LEAN_EXPORT lean_object* l_Float_atan2___boxed(lean_object* v_y_238_, lean_object* v_x_239_){
_start:
{
double v_y_boxed_240_; double v_x_boxed_241_; double v_res_242_; lean_object* v_r_243_; 
v_y_boxed_240_ = lean_unbox_float(v_y_238_);
lean_dec_ref(v_y_238_);
v_x_boxed_241_ = lean_unbox_float(v_x_239_);
lean_dec_ref(v_x_239_);
v_res_242_ = atan2(v_y_boxed_240_, v_x_boxed_241_);
v_r_243_ = lean_box_float(v_res_242_);
return v_r_243_;
}
}
LEAN_EXPORT lean_object* l_Float_sinh___boxed(lean_object* v_a_00___x40___internal___hyg_245_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_246_; double v_res_247_; lean_object* v_r_248_; 
v_a_00___x40___internal___hyg_1__boxed_246_ = lean_unbox_float(v_a_00___x40___internal___hyg_245_);
lean_dec_ref(v_a_00___x40___internal___hyg_245_);
v_res_247_ = sinh(v_a_00___x40___internal___hyg_1__boxed_246_);
v_r_248_ = lean_box_float(v_res_247_);
return v_r_248_;
}
}
LEAN_EXPORT lean_object* l_Float_cosh___boxed(lean_object* v_a_00___x40___internal___hyg_250_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_251_; double v_res_252_; lean_object* v_r_253_; 
v_a_00___x40___internal___hyg_1__boxed_251_ = lean_unbox_float(v_a_00___x40___internal___hyg_250_);
lean_dec_ref(v_a_00___x40___internal___hyg_250_);
v_res_252_ = cosh(v_a_00___x40___internal___hyg_1__boxed_251_);
v_r_253_ = lean_box_float(v_res_252_);
return v_r_253_;
}
}
LEAN_EXPORT lean_object* l_Float_tanh___boxed(lean_object* v_a_00___x40___internal___hyg_255_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_256_; double v_res_257_; lean_object* v_r_258_; 
v_a_00___x40___internal___hyg_1__boxed_256_ = lean_unbox_float(v_a_00___x40___internal___hyg_255_);
lean_dec_ref(v_a_00___x40___internal___hyg_255_);
v_res_257_ = tanh(v_a_00___x40___internal___hyg_1__boxed_256_);
v_r_258_ = lean_box_float(v_res_257_);
return v_r_258_;
}
}
LEAN_EXPORT lean_object* l_Float_asinh___boxed(lean_object* v_a_00___x40___internal___hyg_260_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_261_; double v_res_262_; lean_object* v_r_263_; 
v_a_00___x40___internal___hyg_1__boxed_261_ = lean_unbox_float(v_a_00___x40___internal___hyg_260_);
lean_dec_ref(v_a_00___x40___internal___hyg_260_);
v_res_262_ = asinh(v_a_00___x40___internal___hyg_1__boxed_261_);
v_r_263_ = lean_box_float(v_res_262_);
return v_r_263_;
}
}
LEAN_EXPORT lean_object* l_Float_acosh___boxed(lean_object* v_a_00___x40___internal___hyg_265_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_266_; double v_res_267_; lean_object* v_r_268_; 
v_a_00___x40___internal___hyg_1__boxed_266_ = lean_unbox_float(v_a_00___x40___internal___hyg_265_);
lean_dec_ref(v_a_00___x40___internal___hyg_265_);
v_res_267_ = acosh(v_a_00___x40___internal___hyg_1__boxed_266_);
v_r_268_ = lean_box_float(v_res_267_);
return v_r_268_;
}
}
LEAN_EXPORT lean_object* l_Float_atanh___boxed(lean_object* v_a_00___x40___internal___hyg_270_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_271_; double v_res_272_; lean_object* v_r_273_; 
v_a_00___x40___internal___hyg_1__boxed_271_ = lean_unbox_float(v_a_00___x40___internal___hyg_270_);
lean_dec_ref(v_a_00___x40___internal___hyg_270_);
v_res_272_ = atanh(v_a_00___x40___internal___hyg_1__boxed_271_);
v_r_273_ = lean_box_float(v_res_272_);
return v_r_273_;
}
}
LEAN_EXPORT lean_object* l_Float_exp___boxed(lean_object* v_x_275_){
_start:
{
double v_x_boxed_276_; double v_res_277_; lean_object* v_r_278_; 
v_x_boxed_276_ = lean_unbox_float(v_x_275_);
lean_dec_ref(v_x_275_);
v_res_277_ = exp(v_x_boxed_276_);
v_r_278_ = lean_box_float(v_res_277_);
return v_r_278_;
}
}
LEAN_EXPORT lean_object* l_Float_exp2___boxed(lean_object* v_x_280_){
_start:
{
double v_x_boxed_281_; double v_res_282_; lean_object* v_r_283_; 
v_x_boxed_281_ = lean_unbox_float(v_x_280_);
lean_dec_ref(v_x_280_);
v_res_282_ = exp2(v_x_boxed_281_);
v_r_283_ = lean_box_float(v_res_282_);
return v_r_283_;
}
}
LEAN_EXPORT lean_object* l_Float_log___boxed(lean_object* v_x_285_){
_start:
{
double v_x_boxed_286_; double v_res_287_; lean_object* v_r_288_; 
v_x_boxed_286_ = lean_unbox_float(v_x_285_);
lean_dec_ref(v_x_285_);
v_res_287_ = log(v_x_boxed_286_);
v_r_288_ = lean_box_float(v_res_287_);
return v_r_288_;
}
}
LEAN_EXPORT lean_object* l_Float_log2___boxed(lean_object* v_a_00___x40___internal___hyg_290_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_291_; double v_res_292_; lean_object* v_r_293_; 
v_a_00___x40___internal___hyg_1__boxed_291_ = lean_unbox_float(v_a_00___x40___internal___hyg_290_);
lean_dec_ref(v_a_00___x40___internal___hyg_290_);
v_res_292_ = log2(v_a_00___x40___internal___hyg_1__boxed_291_);
v_r_293_ = lean_box_float(v_res_292_);
return v_r_293_;
}
}
LEAN_EXPORT lean_object* l_Float_log10___boxed(lean_object* v_a_00___x40___internal___hyg_295_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_296_; double v_res_297_; lean_object* v_r_298_; 
v_a_00___x40___internal___hyg_1__boxed_296_ = lean_unbox_float(v_a_00___x40___internal___hyg_295_);
lean_dec_ref(v_a_00___x40___internal___hyg_295_);
v_res_297_ = log10(v_a_00___x40___internal___hyg_1__boxed_296_);
v_r_298_ = lean_box_float(v_res_297_);
return v_r_298_;
}
}
LEAN_EXPORT lean_object* l_Float_pow___boxed(lean_object* v_a_00___x40___internal___hyg_301_, lean_object* v_a_00___x40___internal___hyg_302_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_303_; double v_a_00___x40___internal___hyg_2__boxed_304_; double v_res_305_; lean_object* v_r_306_; 
v_a_00___x40___internal___hyg_1__boxed_303_ = lean_unbox_float(v_a_00___x40___internal___hyg_301_);
lean_dec_ref(v_a_00___x40___internal___hyg_301_);
v_a_00___x40___internal___hyg_2__boxed_304_ = lean_unbox_float(v_a_00___x40___internal___hyg_302_);
lean_dec_ref(v_a_00___x40___internal___hyg_302_);
v_res_305_ = pow(v_a_00___x40___internal___hyg_1__boxed_303_, v_a_00___x40___internal___hyg_2__boxed_304_);
v_r_306_ = lean_box_float(v_res_305_);
return v_r_306_;
}
}
LEAN_EXPORT lean_object* l_Float_sqrt___boxed(lean_object* v_a_00___x40___internal___hyg_308_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_309_; double v_res_310_; lean_object* v_r_311_; 
v_a_00___x40___internal___hyg_1__boxed_309_ = lean_unbox_float(v_a_00___x40___internal___hyg_308_);
lean_dec_ref(v_a_00___x40___internal___hyg_308_);
v_res_310_ = sqrt(v_a_00___x40___internal___hyg_1__boxed_309_);
v_r_311_ = lean_box_float(v_res_310_);
return v_r_311_;
}
}
LEAN_EXPORT lean_object* l_Float_cbrt___boxed(lean_object* v_a_00___x40___internal___hyg_313_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_314_; double v_res_315_; lean_object* v_r_316_; 
v_a_00___x40___internal___hyg_1__boxed_314_ = lean_unbox_float(v_a_00___x40___internal___hyg_313_);
lean_dec_ref(v_a_00___x40___internal___hyg_313_);
v_res_315_ = cbrt(v_a_00___x40___internal___hyg_1__boxed_314_);
v_r_316_ = lean_box_float(v_res_315_);
return v_r_316_;
}
}
LEAN_EXPORT lean_object* l_Float_ceil___boxed(lean_object* v_a_00___x40___internal___hyg_318_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_319_; double v_res_320_; lean_object* v_r_321_; 
v_a_00___x40___internal___hyg_1__boxed_319_ = lean_unbox_float(v_a_00___x40___internal___hyg_318_);
lean_dec_ref(v_a_00___x40___internal___hyg_318_);
v_res_320_ = ceil(v_a_00___x40___internal___hyg_1__boxed_319_);
v_r_321_ = lean_box_float(v_res_320_);
return v_r_321_;
}
}
LEAN_EXPORT lean_object* l_Float_floor___boxed(lean_object* v_a_00___x40___internal___hyg_323_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_324_; double v_res_325_; lean_object* v_r_326_; 
v_a_00___x40___internal___hyg_1__boxed_324_ = lean_unbox_float(v_a_00___x40___internal___hyg_323_);
lean_dec_ref(v_a_00___x40___internal___hyg_323_);
v_res_325_ = floor(v_a_00___x40___internal___hyg_1__boxed_324_);
v_r_326_ = lean_box_float(v_res_325_);
return v_r_326_;
}
}
LEAN_EXPORT lean_object* l_Float_round___boxed(lean_object* v_a_00___x40___internal___hyg_328_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_329_; double v_res_330_; lean_object* v_r_331_; 
v_a_00___x40___internal___hyg_1__boxed_329_ = lean_unbox_float(v_a_00___x40___internal___hyg_328_);
lean_dec_ref(v_a_00___x40___internal___hyg_328_);
v_res_330_ = round(v_a_00___x40___internal___hyg_1__boxed_329_);
v_r_331_ = lean_box_float(v_res_330_);
return v_r_331_;
}
}
LEAN_EXPORT lean_object* l_Float_abs___boxed(lean_object* v_a_00___x40___internal___hyg_333_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_334_; double v_res_335_; lean_object* v_r_336_; 
v_a_00___x40___internal___hyg_1__boxed_334_ = lean_unbox_float(v_a_00___x40___internal___hyg_333_);
lean_dec_ref(v_a_00___x40___internal___hyg_333_);
v_res_335_ = fabs(v_a_00___x40___internal___hyg_1__boxed_334_);
v_r_336_ = lean_box_float(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT double l_instMinFloat___lam__0(double v_x_339_, double v_y_340_){
_start:
{
uint8_t v___x_341_; 
v___x_341_ = lean_float_decLe(v_x_339_, v_y_340_);
if (v___x_341_ == 0)
{
return v_y_340_;
}
else
{
return v_x_339_;
}
}
}
LEAN_EXPORT lean_object* l_instMinFloat___lam__0___boxed(lean_object* v_x_342_, lean_object* v_y_343_){
_start:
{
double v_x_boxed_344_; double v_y_boxed_345_; double v_res_346_; lean_object* v_r_347_; 
v_x_boxed_344_ = lean_unbox_float(v_x_342_);
lean_dec_ref(v_x_342_);
v_y_boxed_345_ = lean_unbox_float(v_y_343_);
lean_dec_ref(v_y_343_);
v_res_346_ = l_instMinFloat___lam__0(v_x_boxed_344_, v_y_boxed_345_);
v_r_347_ = lean_box_float(v_res_346_);
return v_r_347_;
}
}
LEAN_EXPORT double l_instMaxFloat___lam__0(double v_x_350_, double v_y_351_){
_start:
{
uint8_t v___x_352_; 
v___x_352_ = lean_float_decLe(v_x_350_, v_y_351_);
if (v___x_352_ == 0)
{
return v_x_350_;
}
else
{
return v_y_351_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxFloat___lam__0___boxed(lean_object* v_x_353_, lean_object* v_y_354_){
_start:
{
double v_x_boxed_355_; double v_y_boxed_356_; double v_res_357_; lean_object* v_r_358_; 
v_x_boxed_355_ = lean_unbox_float(v_x_353_);
lean_dec_ref(v_x_353_);
v_y_boxed_356_ = lean_unbox_float(v_y_354_);
lean_dec_ref(v_y_354_);
v_res_357_ = l_instMaxFloat___lam__0(v_x_boxed_355_, v_y_boxed_356_);
v_r_358_ = lean_box_float(v_res_357_);
return v_r_358_;
}
}
LEAN_EXPORT lean_object* l_Float_scaleB___boxed(lean_object* v_x_363_, lean_object* v_i_364_){
_start:
{
double v_x_boxed_365_; double v_res_366_; lean_object* v_r_367_; 
v_x_boxed_365_ = lean_unbox_float(v_x_363_);
lean_dec_ref(v_x_363_);
v_res_366_ = lean_float_scaleb(v_x_boxed_365_, v_i_364_);
lean_dec(v_i_364_);
v_r_367_ = lean_box_float(v_res_366_);
return v_r_367_;
}
}
lean_object* runtime_initialize_Init_Data_ToString_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Float_Model_Float(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Float(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Model_Float(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Float_Float(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Float_Model_Float(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Float_Float(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Float_Model_Float(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Float(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Float_Float(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Float_Float(builtin);
}
#ifdef __cplusplus
}
#endif
