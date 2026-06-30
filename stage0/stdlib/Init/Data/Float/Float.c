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
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
uint64_t lean_float_to_bits(double);
LEAN_EXPORT lean_object* l_Float_toModel___boxed(lean_object*);
double lean_float_of_bits(uint64_t);
LEAN_EXPORT lean_object* l_Float_ofModel___boxed(lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqFloat_decEq(double, double);
LEAN_EXPORT lean_object* l_instDecidableEqFloat_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqFloat(double, double);
LEAN_EXPORT lean_object* l_instDecidableEqFloat___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_instDecidableEqFloat_decEq(double v_x_11_, double v_x_12_){
_start:
{
uint64_t v_toModel_13_; uint64_t v_toModel_14_; uint8_t v___x_15_; 
v_toModel_13_ = lean_float_to_bits(v_x_11_);
v_toModel_14_ = lean_float_to_bits(v_x_12_);
v___x_15_ = lean_uint64_dec_eq(v_toModel_13_, v_toModel_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqFloat_decEq___boxed(lean_object* v_x_16_, lean_object* v_x_17_){
_start:
{
double v_x_25__boxed_18_; double v_x_26__boxed_19_; uint8_t v_res_20_; lean_object* v_r_21_; 
v_x_25__boxed_18_ = lean_unbox_float(v_x_16_);
lean_dec_ref(v_x_16_);
v_x_26__boxed_19_ = lean_unbox_float(v_x_17_);
lean_dec_ref(v_x_17_);
v_res_20_ = l_instDecidableEqFloat_decEq(v_x_25__boxed_18_, v_x_26__boxed_19_);
v_r_21_ = lean_box(v_res_20_);
return v_r_21_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqFloat(double v_x_22_, double v_x_23_){
_start:
{
uint8_t v___x_24_; 
v___x_24_ = l_instDecidableEqFloat_decEq(v_x_22_, v_x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqFloat___boxed(lean_object* v_x_25_, lean_object* v_x_26_){
_start:
{
double v_x_5__boxed_27_; double v_x_6__boxed_28_; uint8_t v_res_29_; lean_object* v_r_30_; 
v_x_5__boxed_27_ = lean_unbox_float(v_x_25_);
lean_dec_ref(v_x_25_);
v_x_6__boxed_28_ = lean_unbox_float(v_x_26_);
lean_dec_ref(v_x_26_);
v_res_29_ = l_instDecidableEqFloat(v_x_5__boxed_27_, v_x_6__boxed_28_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
LEAN_EXPORT lean_object* l_Float_add___boxed(lean_object* v_a_00___x40___internal___hyg_33_, lean_object* v_a_00___x40___internal___hyg_34_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_35_; double v_a_00___x40___internal___hyg_2__boxed_36_; double v_res_37_; lean_object* v_r_38_; 
v_a_00___x40___internal___hyg_1__boxed_35_ = lean_unbox_float(v_a_00___x40___internal___hyg_33_);
lean_dec_ref(v_a_00___x40___internal___hyg_33_);
v_a_00___x40___internal___hyg_2__boxed_36_ = lean_unbox_float(v_a_00___x40___internal___hyg_34_);
lean_dec_ref(v_a_00___x40___internal___hyg_34_);
v_res_37_ = lean_float_add(v_a_00___x40___internal___hyg_1__boxed_35_, v_a_00___x40___internal___hyg_2__boxed_36_);
v_r_38_ = lean_box_float(v_res_37_);
return v_r_38_;
}
}
LEAN_EXPORT lean_object* l_Float_sub___boxed(lean_object* v_a_00___x40___internal___hyg_41_, lean_object* v_a_00___x40___internal___hyg_42_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_43_; double v_a_00___x40___internal___hyg_2__boxed_44_; double v_res_45_; lean_object* v_r_46_; 
v_a_00___x40___internal___hyg_1__boxed_43_ = lean_unbox_float(v_a_00___x40___internal___hyg_41_);
lean_dec_ref(v_a_00___x40___internal___hyg_41_);
v_a_00___x40___internal___hyg_2__boxed_44_ = lean_unbox_float(v_a_00___x40___internal___hyg_42_);
lean_dec_ref(v_a_00___x40___internal___hyg_42_);
v_res_45_ = lean_float_sub(v_a_00___x40___internal___hyg_1__boxed_43_, v_a_00___x40___internal___hyg_2__boxed_44_);
v_r_46_ = lean_box_float(v_res_45_);
return v_r_46_;
}
}
LEAN_EXPORT lean_object* l_Float_mul___boxed(lean_object* v_a_00___x40___internal___hyg_49_, lean_object* v_a_00___x40___internal___hyg_50_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_51_; double v_a_00___x40___internal___hyg_2__boxed_52_; double v_res_53_; lean_object* v_r_54_; 
v_a_00___x40___internal___hyg_1__boxed_51_ = lean_unbox_float(v_a_00___x40___internal___hyg_49_);
lean_dec_ref(v_a_00___x40___internal___hyg_49_);
v_a_00___x40___internal___hyg_2__boxed_52_ = lean_unbox_float(v_a_00___x40___internal___hyg_50_);
lean_dec_ref(v_a_00___x40___internal___hyg_50_);
v_res_53_ = lean_float_mul(v_a_00___x40___internal___hyg_1__boxed_51_, v_a_00___x40___internal___hyg_2__boxed_52_);
v_r_54_ = lean_box_float(v_res_53_);
return v_r_54_;
}
}
LEAN_EXPORT lean_object* l_Float_div___boxed(lean_object* v_a_00___x40___internal___hyg_57_, lean_object* v_a_00___x40___internal___hyg_58_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_59_; double v_a_00___x40___internal___hyg_2__boxed_60_; double v_res_61_; lean_object* v_r_62_; 
v_a_00___x40___internal___hyg_1__boxed_59_ = lean_unbox_float(v_a_00___x40___internal___hyg_57_);
lean_dec_ref(v_a_00___x40___internal___hyg_57_);
v_a_00___x40___internal___hyg_2__boxed_60_ = lean_unbox_float(v_a_00___x40___internal___hyg_58_);
lean_dec_ref(v_a_00___x40___internal___hyg_58_);
v_res_61_ = lean_float_div(v_a_00___x40___internal___hyg_1__boxed_59_, v_a_00___x40___internal___hyg_2__boxed_60_);
v_r_62_ = lean_box_float(v_res_61_);
return v_r_62_;
}
}
LEAN_EXPORT lean_object* l_Float_neg___boxed(lean_object* v_a_00___x40___internal___hyg_64_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_65_; double v_res_66_; lean_object* v_r_67_; 
v_a_00___x40___internal___hyg_1__boxed_65_ = lean_unbox_float(v_a_00___x40___internal___hyg_64_);
lean_dec_ref(v_a_00___x40___internal___hyg_64_);
v_res_66_ = lean_float_negate(v_a_00___x40___internal___hyg_1__boxed_65_);
v_r_67_ = lean_box_float(v_res_66_);
return v_r_67_;
}
}
LEAN_EXPORT lean_object* l_Float_lt___boxed(lean_object* v_a_00___x40___internal___hyg_70_, lean_object* v_a_00___x40___internal___hyg_71_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_72_; double v_a_00___x40___internal___hyg_2__boxed_73_; uint8_t v_res_74_; lean_object* v_r_75_; 
v_a_00___x40___internal___hyg_1__boxed_72_ = lean_unbox_float(v_a_00___x40___internal___hyg_70_);
lean_dec_ref(v_a_00___x40___internal___hyg_70_);
v_a_00___x40___internal___hyg_2__boxed_73_ = lean_unbox_float(v_a_00___x40___internal___hyg_71_);
lean_dec_ref(v_a_00___x40___internal___hyg_71_);
v_res_74_ = lean_float_decLt(v_a_00___x40___internal___hyg_1__boxed_72_, v_a_00___x40___internal___hyg_2__boxed_73_);
v_r_75_ = lean_box(v_res_74_);
return v_r_75_;
}
}
LEAN_EXPORT lean_object* l_Float_le___boxed(lean_object* v_a_00___x40___internal___hyg_78_, lean_object* v_a_00___x40___internal___hyg_79_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_80_; double v_a_00___x40___internal___hyg_2__boxed_81_; uint8_t v_res_82_; lean_object* v_r_83_; 
v_a_00___x40___internal___hyg_1__boxed_80_ = lean_unbox_float(v_a_00___x40___internal___hyg_78_);
lean_dec_ref(v_a_00___x40___internal___hyg_78_);
v_a_00___x40___internal___hyg_2__boxed_81_ = lean_unbox_float(v_a_00___x40___internal___hyg_79_);
lean_dec_ref(v_a_00___x40___internal___hyg_79_);
v_res_82_ = lean_float_decLe(v_a_00___x40___internal___hyg_1__boxed_80_, v_a_00___x40___internal___hyg_2__boxed_81_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT lean_object* l_Float_ofBits___boxed(lean_object* v_a_00___x40___internal___hyg_85_){
_start:
{
uint64_t v_a_00___x40___internal___hyg_1__boxed_86_; double v_res_87_; lean_object* v_r_88_; 
v_a_00___x40___internal___hyg_1__boxed_86_ = lean_unbox_uint64(v_a_00___x40___internal___hyg_85_);
lean_dec_ref(v_a_00___x40___internal___hyg_85_);
v_res_87_ = lean_float_of_bits(v_a_00___x40___internal___hyg_1__boxed_86_);
v_r_88_ = lean_box_float(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT lean_object* l_Float_toBits___boxed(lean_object* v_a_00___x40___internal___hyg_90_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_91_; uint64_t v_res_92_; lean_object* v_r_93_; 
v_a_00___x40___internal___hyg_1__boxed_91_ = lean_unbox_float(v_a_00___x40___internal___hyg_90_);
lean_dec_ref(v_a_00___x40___internal___hyg_90_);
v_res_92_ = lean_float_to_bits(v_a_00___x40___internal___hyg_1__boxed_91_);
v_r_93_ = lean_box_uint64(v_res_92_);
return v_r_93_;
}
}
static lean_object* _init_l_instLTFloat(void){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lean_box(0);
return v___x_104_;
}
}
static lean_object* _init_l_instLEFloat(void){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = lean_box(0);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Float_beq___boxed(lean_object* v_a_108_, lean_object* v_b_109_){
_start:
{
double v_a_boxed_110_; double v_b_boxed_111_; uint8_t v_res_112_; lean_object* v_r_113_; 
v_a_boxed_110_ = lean_unbox_float(v_a_108_);
lean_dec_ref(v_a_108_);
v_b_boxed_111_ = lean_unbox_float(v_b_109_);
lean_dec_ref(v_b_109_);
v_res_112_ = lean_float_beq(v_a_boxed_110_, v_b_boxed_111_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
LEAN_EXPORT lean_object* l_Float_decLt___boxed(lean_object* v_a_118_, lean_object* v_b_119_){
_start:
{
double v_a_boxed_120_; double v_b_boxed_121_; uint8_t v_res_122_; lean_object* v_r_123_; 
v_a_boxed_120_ = lean_unbox_float(v_a_118_);
lean_dec_ref(v_a_118_);
v_b_boxed_121_ = lean_unbox_float(v_b_119_);
lean_dec_ref(v_b_119_);
v_res_122_ = lean_float_decLt(v_a_boxed_120_, v_b_boxed_121_);
v_r_123_ = lean_box(v_res_122_);
return v_r_123_;
}
}
LEAN_EXPORT lean_object* l_Float_decLe___boxed(lean_object* v_a_126_, lean_object* v_b_127_){
_start:
{
double v_a_boxed_128_; double v_b_boxed_129_; uint8_t v_res_130_; lean_object* v_r_131_; 
v_a_boxed_128_ = lean_unbox_float(v_a_126_);
lean_dec_ref(v_a_126_);
v_b_boxed_129_ = lean_unbox_float(v_b_127_);
lean_dec_ref(v_b_127_);
v_res_130_ = lean_float_decLe(v_a_boxed_128_, v_b_boxed_129_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT lean_object* l_Float_toString___boxed(lean_object* v_a_00___x40___internal___hyg_133_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_134_; lean_object* v_res_135_; 
v_a_00___x40___internal___hyg_1__boxed_134_ = lean_unbox_float(v_a_00___x40___internal___hyg_133_);
lean_dec_ref(v_a_00___x40___internal___hyg_133_);
v_res_135_ = lean_float_to_string(v_a_00___x40___internal___hyg_1__boxed_134_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Float_toUInt8___boxed(lean_object* v_a_00___x40___internal___hyg_137_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_138_; uint8_t v_res_139_; lean_object* v_r_140_; 
v_a_00___x40___internal___hyg_1__boxed_138_ = lean_unbox_float(v_a_00___x40___internal___hyg_137_);
lean_dec_ref(v_a_00___x40___internal___hyg_137_);
v_res_139_ = lean_float_to_uint8(v_a_00___x40___internal___hyg_1__boxed_138_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT lean_object* l_Float_toUInt16___boxed(lean_object* v_a_00___x40___internal___hyg_142_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_143_; uint16_t v_res_144_; lean_object* v_r_145_; 
v_a_00___x40___internal___hyg_1__boxed_143_ = lean_unbox_float(v_a_00___x40___internal___hyg_142_);
lean_dec_ref(v_a_00___x40___internal___hyg_142_);
v_res_144_ = lean_float_to_uint16(v_a_00___x40___internal___hyg_1__boxed_143_);
v_r_145_ = lean_box(v_res_144_);
return v_r_145_;
}
}
LEAN_EXPORT lean_object* l_Float_toUInt32___boxed(lean_object* v_a_00___x40___internal___hyg_147_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_148_; uint32_t v_res_149_; lean_object* v_r_150_; 
v_a_00___x40___internal___hyg_1__boxed_148_ = lean_unbox_float(v_a_00___x40___internal___hyg_147_);
lean_dec_ref(v_a_00___x40___internal___hyg_147_);
v_res_149_ = lean_float_to_uint32(v_a_00___x40___internal___hyg_1__boxed_148_);
v_r_150_ = lean_box_uint32(v_res_149_);
return v_r_150_;
}
}
LEAN_EXPORT lean_object* l_Float_toUInt64___boxed(lean_object* v_a_00___x40___internal___hyg_152_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_153_; uint64_t v_res_154_; lean_object* v_r_155_; 
v_a_00___x40___internal___hyg_1__boxed_153_ = lean_unbox_float(v_a_00___x40___internal___hyg_152_);
lean_dec_ref(v_a_00___x40___internal___hyg_152_);
v_res_154_ = lean_float_to_uint64(v_a_00___x40___internal___hyg_1__boxed_153_);
v_r_155_ = lean_box_uint64(v_res_154_);
return v_r_155_;
}
}
LEAN_EXPORT lean_object* l_Float_toUSize___boxed(lean_object* v_a_00___x40___internal___hyg_157_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_158_; size_t v_res_159_; lean_object* v_r_160_; 
v_a_00___x40___internal___hyg_1__boxed_158_ = lean_unbox_float(v_a_00___x40___internal___hyg_157_);
lean_dec_ref(v_a_00___x40___internal___hyg_157_);
v_res_159_ = lean_float_to_usize(v_a_00___x40___internal___hyg_1__boxed_158_);
v_r_160_ = lean_box_usize(v_res_159_);
return v_r_160_;
}
}
LEAN_EXPORT lean_object* l_Float_isNaN___boxed(lean_object* v_a_00___x40___internal___hyg_162_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_163_; uint8_t v_res_164_; lean_object* v_r_165_; 
v_a_00___x40___internal___hyg_1__boxed_163_ = lean_unbox_float(v_a_00___x40___internal___hyg_162_);
lean_dec_ref(v_a_00___x40___internal___hyg_162_);
v_res_164_ = lean_float_isnan(v_a_00___x40___internal___hyg_1__boxed_163_);
v_r_165_ = lean_box(v_res_164_);
return v_r_165_;
}
}
LEAN_EXPORT lean_object* l_Float_isFinite___boxed(lean_object* v_a_00___x40___internal___hyg_167_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_168_; uint8_t v_res_169_; lean_object* v_r_170_; 
v_a_00___x40___internal___hyg_1__boxed_168_ = lean_unbox_float(v_a_00___x40___internal___hyg_167_);
lean_dec_ref(v_a_00___x40___internal___hyg_167_);
v_res_169_ = lean_float_isfinite(v_a_00___x40___internal___hyg_1__boxed_168_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
LEAN_EXPORT lean_object* l_Float_isInf___boxed(lean_object* v_a_00___x40___internal___hyg_172_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_173_; uint8_t v_res_174_; lean_object* v_r_175_; 
v_a_00___x40___internal___hyg_1__boxed_173_ = lean_unbox_float(v_a_00___x40___internal___hyg_172_);
lean_dec_ref(v_a_00___x40___internal___hyg_172_);
v_res_174_ = lean_float_isinf(v_a_00___x40___internal___hyg_1__boxed_173_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
LEAN_EXPORT lean_object* l_Float_frExp___boxed(lean_object* v_a_00___x40___internal___hyg_177_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_178_; lean_object* v_res_179_; 
v_a_00___x40___internal___hyg_1__boxed_178_ = lean_unbox_float(v_a_00___x40___internal___hyg_177_);
lean_dec_ref(v_a_00___x40___internal___hyg_177_);
v_res_179_ = lean_float_frexp(v_a_00___x40___internal___hyg_1__boxed_178_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_UInt8_toFloat___boxed(lean_object* v_n_183_){
_start:
{
uint8_t v_n_boxed_184_; double v_res_185_; lean_object* v_r_186_; 
v_n_boxed_184_ = lean_unbox(v_n_183_);
v_res_185_ = lean_uint8_to_float(v_n_boxed_184_);
v_r_186_ = lean_box_float(v_res_185_);
return v_r_186_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toFloat___boxed(lean_object* v_n_188_){
_start:
{
uint16_t v_n_boxed_189_; double v_res_190_; lean_object* v_r_191_; 
v_n_boxed_189_ = lean_unbox(v_n_188_);
v_res_190_ = lean_uint16_to_float(v_n_boxed_189_);
v_r_191_ = lean_box_float(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toFloat___boxed(lean_object* v_n_193_){
_start:
{
uint32_t v_n_boxed_194_; double v_res_195_; lean_object* v_r_196_; 
v_n_boxed_194_ = lean_unbox_uint32(v_n_193_);
lean_dec(v_n_193_);
v_res_195_ = lean_uint32_to_float(v_n_boxed_194_);
v_r_196_ = lean_box_float(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toFloat___boxed(lean_object* v_n_198_){
_start:
{
uint64_t v_n_boxed_199_; double v_res_200_; lean_object* v_r_201_; 
v_n_boxed_199_ = lean_unbox_uint64(v_n_198_);
lean_dec_ref(v_n_198_);
v_res_200_ = lean_uint64_to_float(v_n_boxed_199_);
v_r_201_ = lean_box_float(v_res_200_);
return v_r_201_;
}
}
LEAN_EXPORT lean_object* l_USize_toFloat___boxed(lean_object* v_n_203_){
_start:
{
size_t v_n_boxed_204_; double v_res_205_; lean_object* v_r_206_; 
v_n_boxed_204_ = lean_unbox_usize(v_n_203_);
lean_dec(v_n_203_);
v_res_205_ = lean_usize_to_float(v_n_boxed_204_);
v_r_206_ = lean_box_float(v_res_205_);
return v_r_206_;
}
}
static double _init_l_instInhabitedFloat___closed__0(void){
_start:
{
uint64_t v___x_207_; double v___x_208_; 
v___x_207_ = 0ULL;
v___x_208_ = lean_uint64_to_float(v___x_207_);
return v___x_208_;
}
}
static double _init_l_instInhabitedFloat(void){
_start:
{
double v___x_209_; 
v___x_209_ = lean_float_once(&l_instInhabitedFloat___closed__0, &l_instInhabitedFloat___closed__0_once, _init_l_instInhabitedFloat___closed__0);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Float_repr(double v_n_210_, lean_object* v_prec_211_){
_start:
{
double v___x_212_; uint8_t v___x_213_; 
v___x_212_ = lean_float_once(&l_instInhabitedFloat___closed__0, &l_instInhabitedFloat___closed__0_once, _init_l_instInhabitedFloat___closed__0);
v___x_213_ = lean_float_decLt(v_n_210_, v___x_212_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = lean_float_to_string(v_n_210_);
v___x_215_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
return v___x_215_;
}
else
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_216_ = lean_float_to_string(v_n_210_);
v___x_217_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
v___x_218_ = l_Repr_addAppParen(v___x_217_, v_prec_211_);
return v___x_218_;
}
}
}
LEAN_EXPORT lean_object* l_Float_repr___boxed(lean_object* v_n_219_, lean_object* v_prec_220_){
_start:
{
double v_n_boxed_221_; lean_object* v_res_222_; 
v_n_boxed_221_ = lean_unbox_float(v_n_219_);
lean_dec_ref(v_n_219_);
v_res_222_ = l_Float_repr(v_n_boxed_221_, v_prec_220_);
lean_dec(v_prec_220_);
return v_res_222_;
}
}
static lean_object* _init_l_instReprAtomFloat(void){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = lean_box(0);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Float_sin___boxed(lean_object* v_a_00___x40___internal___hyg_227_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_228_; double v_res_229_; lean_object* v_r_230_; 
v_a_00___x40___internal___hyg_1__boxed_228_ = lean_unbox_float(v_a_00___x40___internal___hyg_227_);
lean_dec_ref(v_a_00___x40___internal___hyg_227_);
v_res_229_ = sin(v_a_00___x40___internal___hyg_1__boxed_228_);
v_r_230_ = lean_box_float(v_res_229_);
return v_r_230_;
}
}
LEAN_EXPORT lean_object* l_Float_cos___boxed(lean_object* v_a_00___x40___internal___hyg_232_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_233_; double v_res_234_; lean_object* v_r_235_; 
v_a_00___x40___internal___hyg_1__boxed_233_ = lean_unbox_float(v_a_00___x40___internal___hyg_232_);
lean_dec_ref(v_a_00___x40___internal___hyg_232_);
v_res_234_ = cos(v_a_00___x40___internal___hyg_1__boxed_233_);
v_r_235_ = lean_box_float(v_res_234_);
return v_r_235_;
}
}
LEAN_EXPORT lean_object* l_Float_tan___boxed(lean_object* v_a_00___x40___internal___hyg_237_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_238_; double v_res_239_; lean_object* v_r_240_; 
v_a_00___x40___internal___hyg_1__boxed_238_ = lean_unbox_float(v_a_00___x40___internal___hyg_237_);
lean_dec_ref(v_a_00___x40___internal___hyg_237_);
v_res_239_ = tan(v_a_00___x40___internal___hyg_1__boxed_238_);
v_r_240_ = lean_box_float(v_res_239_);
return v_r_240_;
}
}
LEAN_EXPORT lean_object* l_Float_asin___boxed(lean_object* v_a_00___x40___internal___hyg_242_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_243_; double v_res_244_; lean_object* v_r_245_; 
v_a_00___x40___internal___hyg_1__boxed_243_ = lean_unbox_float(v_a_00___x40___internal___hyg_242_);
lean_dec_ref(v_a_00___x40___internal___hyg_242_);
v_res_244_ = asin(v_a_00___x40___internal___hyg_1__boxed_243_);
v_r_245_ = lean_box_float(v_res_244_);
return v_r_245_;
}
}
LEAN_EXPORT lean_object* l_Float_acos___boxed(lean_object* v_a_00___x40___internal___hyg_247_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_248_; double v_res_249_; lean_object* v_r_250_; 
v_a_00___x40___internal___hyg_1__boxed_248_ = lean_unbox_float(v_a_00___x40___internal___hyg_247_);
lean_dec_ref(v_a_00___x40___internal___hyg_247_);
v_res_249_ = acos(v_a_00___x40___internal___hyg_1__boxed_248_);
v_r_250_ = lean_box_float(v_res_249_);
return v_r_250_;
}
}
LEAN_EXPORT lean_object* l_Float_atan___boxed(lean_object* v_a_00___x40___internal___hyg_252_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_253_; double v_res_254_; lean_object* v_r_255_; 
v_a_00___x40___internal___hyg_1__boxed_253_ = lean_unbox_float(v_a_00___x40___internal___hyg_252_);
lean_dec_ref(v_a_00___x40___internal___hyg_252_);
v_res_254_ = atan(v_a_00___x40___internal___hyg_1__boxed_253_);
v_r_255_ = lean_box_float(v_res_254_);
return v_r_255_;
}
}
LEAN_EXPORT lean_object* l_Float_atan2___boxed(lean_object* v_y_258_, lean_object* v_x_259_){
_start:
{
double v_y_boxed_260_; double v_x_boxed_261_; double v_res_262_; lean_object* v_r_263_; 
v_y_boxed_260_ = lean_unbox_float(v_y_258_);
lean_dec_ref(v_y_258_);
v_x_boxed_261_ = lean_unbox_float(v_x_259_);
lean_dec_ref(v_x_259_);
v_res_262_ = atan2(v_y_boxed_260_, v_x_boxed_261_);
v_r_263_ = lean_box_float(v_res_262_);
return v_r_263_;
}
}
LEAN_EXPORT lean_object* l_Float_sinh___boxed(lean_object* v_a_00___x40___internal___hyg_265_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_266_; double v_res_267_; lean_object* v_r_268_; 
v_a_00___x40___internal___hyg_1__boxed_266_ = lean_unbox_float(v_a_00___x40___internal___hyg_265_);
lean_dec_ref(v_a_00___x40___internal___hyg_265_);
v_res_267_ = sinh(v_a_00___x40___internal___hyg_1__boxed_266_);
v_r_268_ = lean_box_float(v_res_267_);
return v_r_268_;
}
}
LEAN_EXPORT lean_object* l_Float_cosh___boxed(lean_object* v_a_00___x40___internal___hyg_270_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_271_; double v_res_272_; lean_object* v_r_273_; 
v_a_00___x40___internal___hyg_1__boxed_271_ = lean_unbox_float(v_a_00___x40___internal___hyg_270_);
lean_dec_ref(v_a_00___x40___internal___hyg_270_);
v_res_272_ = cosh(v_a_00___x40___internal___hyg_1__boxed_271_);
v_r_273_ = lean_box_float(v_res_272_);
return v_r_273_;
}
}
LEAN_EXPORT lean_object* l_Float_tanh___boxed(lean_object* v_a_00___x40___internal___hyg_275_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_276_; double v_res_277_; lean_object* v_r_278_; 
v_a_00___x40___internal___hyg_1__boxed_276_ = lean_unbox_float(v_a_00___x40___internal___hyg_275_);
lean_dec_ref(v_a_00___x40___internal___hyg_275_);
v_res_277_ = tanh(v_a_00___x40___internal___hyg_1__boxed_276_);
v_r_278_ = lean_box_float(v_res_277_);
return v_r_278_;
}
}
LEAN_EXPORT lean_object* l_Float_asinh___boxed(lean_object* v_a_00___x40___internal___hyg_280_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_281_; double v_res_282_; lean_object* v_r_283_; 
v_a_00___x40___internal___hyg_1__boxed_281_ = lean_unbox_float(v_a_00___x40___internal___hyg_280_);
lean_dec_ref(v_a_00___x40___internal___hyg_280_);
v_res_282_ = asinh(v_a_00___x40___internal___hyg_1__boxed_281_);
v_r_283_ = lean_box_float(v_res_282_);
return v_r_283_;
}
}
LEAN_EXPORT lean_object* l_Float_acosh___boxed(lean_object* v_a_00___x40___internal___hyg_285_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_286_; double v_res_287_; lean_object* v_r_288_; 
v_a_00___x40___internal___hyg_1__boxed_286_ = lean_unbox_float(v_a_00___x40___internal___hyg_285_);
lean_dec_ref(v_a_00___x40___internal___hyg_285_);
v_res_287_ = acosh(v_a_00___x40___internal___hyg_1__boxed_286_);
v_r_288_ = lean_box_float(v_res_287_);
return v_r_288_;
}
}
LEAN_EXPORT lean_object* l_Float_atanh___boxed(lean_object* v_a_00___x40___internal___hyg_290_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_291_; double v_res_292_; lean_object* v_r_293_; 
v_a_00___x40___internal___hyg_1__boxed_291_ = lean_unbox_float(v_a_00___x40___internal___hyg_290_);
lean_dec_ref(v_a_00___x40___internal___hyg_290_);
v_res_292_ = atanh(v_a_00___x40___internal___hyg_1__boxed_291_);
v_r_293_ = lean_box_float(v_res_292_);
return v_r_293_;
}
}
LEAN_EXPORT lean_object* l_Float_exp___boxed(lean_object* v_x_295_){
_start:
{
double v_x_boxed_296_; double v_res_297_; lean_object* v_r_298_; 
v_x_boxed_296_ = lean_unbox_float(v_x_295_);
lean_dec_ref(v_x_295_);
v_res_297_ = exp(v_x_boxed_296_);
v_r_298_ = lean_box_float(v_res_297_);
return v_r_298_;
}
}
LEAN_EXPORT lean_object* l_Float_exp2___boxed(lean_object* v_x_300_){
_start:
{
double v_x_boxed_301_; double v_res_302_; lean_object* v_r_303_; 
v_x_boxed_301_ = lean_unbox_float(v_x_300_);
lean_dec_ref(v_x_300_);
v_res_302_ = exp2(v_x_boxed_301_);
v_r_303_ = lean_box_float(v_res_302_);
return v_r_303_;
}
}
LEAN_EXPORT lean_object* l_Float_log___boxed(lean_object* v_x_305_){
_start:
{
double v_x_boxed_306_; double v_res_307_; lean_object* v_r_308_; 
v_x_boxed_306_ = lean_unbox_float(v_x_305_);
lean_dec_ref(v_x_305_);
v_res_307_ = log(v_x_boxed_306_);
v_r_308_ = lean_box_float(v_res_307_);
return v_r_308_;
}
}
LEAN_EXPORT lean_object* l_Float_log2___boxed(lean_object* v_a_00___x40___internal___hyg_310_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_311_; double v_res_312_; lean_object* v_r_313_; 
v_a_00___x40___internal___hyg_1__boxed_311_ = lean_unbox_float(v_a_00___x40___internal___hyg_310_);
lean_dec_ref(v_a_00___x40___internal___hyg_310_);
v_res_312_ = log2(v_a_00___x40___internal___hyg_1__boxed_311_);
v_r_313_ = lean_box_float(v_res_312_);
return v_r_313_;
}
}
LEAN_EXPORT lean_object* l_Float_log10___boxed(lean_object* v_a_00___x40___internal___hyg_315_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_316_; double v_res_317_; lean_object* v_r_318_; 
v_a_00___x40___internal___hyg_1__boxed_316_ = lean_unbox_float(v_a_00___x40___internal___hyg_315_);
lean_dec_ref(v_a_00___x40___internal___hyg_315_);
v_res_317_ = log10(v_a_00___x40___internal___hyg_1__boxed_316_);
v_r_318_ = lean_box_float(v_res_317_);
return v_r_318_;
}
}
LEAN_EXPORT lean_object* l_Float_pow___boxed(lean_object* v_a_00___x40___internal___hyg_321_, lean_object* v_a_00___x40___internal___hyg_322_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_323_; double v_a_00___x40___internal___hyg_2__boxed_324_; double v_res_325_; lean_object* v_r_326_; 
v_a_00___x40___internal___hyg_1__boxed_323_ = lean_unbox_float(v_a_00___x40___internal___hyg_321_);
lean_dec_ref(v_a_00___x40___internal___hyg_321_);
v_a_00___x40___internal___hyg_2__boxed_324_ = lean_unbox_float(v_a_00___x40___internal___hyg_322_);
lean_dec_ref(v_a_00___x40___internal___hyg_322_);
v_res_325_ = pow(v_a_00___x40___internal___hyg_1__boxed_323_, v_a_00___x40___internal___hyg_2__boxed_324_);
v_r_326_ = lean_box_float(v_res_325_);
return v_r_326_;
}
}
LEAN_EXPORT lean_object* l_Float_sqrt___boxed(lean_object* v_a_00___x40___internal___hyg_328_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_329_; double v_res_330_; lean_object* v_r_331_; 
v_a_00___x40___internal___hyg_1__boxed_329_ = lean_unbox_float(v_a_00___x40___internal___hyg_328_);
lean_dec_ref(v_a_00___x40___internal___hyg_328_);
v_res_330_ = sqrt(v_a_00___x40___internal___hyg_1__boxed_329_);
v_r_331_ = lean_box_float(v_res_330_);
return v_r_331_;
}
}
LEAN_EXPORT lean_object* l_Float_cbrt___boxed(lean_object* v_a_00___x40___internal___hyg_333_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_334_; double v_res_335_; lean_object* v_r_336_; 
v_a_00___x40___internal___hyg_1__boxed_334_ = lean_unbox_float(v_a_00___x40___internal___hyg_333_);
lean_dec_ref(v_a_00___x40___internal___hyg_333_);
v_res_335_ = cbrt(v_a_00___x40___internal___hyg_1__boxed_334_);
v_r_336_ = lean_box_float(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT lean_object* l_Float_ceil___boxed(lean_object* v_a_00___x40___internal___hyg_338_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_339_; double v_res_340_; lean_object* v_r_341_; 
v_a_00___x40___internal___hyg_1__boxed_339_ = lean_unbox_float(v_a_00___x40___internal___hyg_338_);
lean_dec_ref(v_a_00___x40___internal___hyg_338_);
v_res_340_ = ceil(v_a_00___x40___internal___hyg_1__boxed_339_);
v_r_341_ = lean_box_float(v_res_340_);
return v_r_341_;
}
}
LEAN_EXPORT lean_object* l_Float_floor___boxed(lean_object* v_a_00___x40___internal___hyg_343_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_344_; double v_res_345_; lean_object* v_r_346_; 
v_a_00___x40___internal___hyg_1__boxed_344_ = lean_unbox_float(v_a_00___x40___internal___hyg_343_);
lean_dec_ref(v_a_00___x40___internal___hyg_343_);
v_res_345_ = floor(v_a_00___x40___internal___hyg_1__boxed_344_);
v_r_346_ = lean_box_float(v_res_345_);
return v_r_346_;
}
}
LEAN_EXPORT lean_object* l_Float_round___boxed(lean_object* v_a_00___x40___internal___hyg_348_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_349_; double v_res_350_; lean_object* v_r_351_; 
v_a_00___x40___internal___hyg_1__boxed_349_ = lean_unbox_float(v_a_00___x40___internal___hyg_348_);
lean_dec_ref(v_a_00___x40___internal___hyg_348_);
v_res_350_ = round(v_a_00___x40___internal___hyg_1__boxed_349_);
v_r_351_ = lean_box_float(v_res_350_);
return v_r_351_;
}
}
LEAN_EXPORT lean_object* l_Float_abs___boxed(lean_object* v_a_00___x40___internal___hyg_353_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_354_; double v_res_355_; lean_object* v_r_356_; 
v_a_00___x40___internal___hyg_1__boxed_354_ = lean_unbox_float(v_a_00___x40___internal___hyg_353_);
lean_dec_ref(v_a_00___x40___internal___hyg_353_);
v_res_355_ = fabs(v_a_00___x40___internal___hyg_1__boxed_354_);
v_r_356_ = lean_box_float(v_res_355_);
return v_r_356_;
}
}
LEAN_EXPORT double l_instMinFloat___lam__0(double v_x_359_, double v_y_360_){
_start:
{
uint8_t v___x_361_; 
v___x_361_ = lean_float_decLe(v_x_359_, v_y_360_);
if (v___x_361_ == 0)
{
return v_y_360_;
}
else
{
return v_x_359_;
}
}
}
LEAN_EXPORT lean_object* l_instMinFloat___lam__0___boxed(lean_object* v_x_362_, lean_object* v_y_363_){
_start:
{
double v_x_boxed_364_; double v_y_boxed_365_; double v_res_366_; lean_object* v_r_367_; 
v_x_boxed_364_ = lean_unbox_float(v_x_362_);
lean_dec_ref(v_x_362_);
v_y_boxed_365_ = lean_unbox_float(v_y_363_);
lean_dec_ref(v_y_363_);
v_res_366_ = l_instMinFloat___lam__0(v_x_boxed_364_, v_y_boxed_365_);
v_r_367_ = lean_box_float(v_res_366_);
return v_r_367_;
}
}
LEAN_EXPORT double l_instMaxFloat___lam__0(double v_x_370_, double v_y_371_){
_start:
{
uint8_t v___x_372_; 
v___x_372_ = lean_float_decLe(v_x_370_, v_y_371_);
if (v___x_372_ == 0)
{
return v_x_370_;
}
else
{
return v_y_371_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxFloat___lam__0___boxed(lean_object* v_x_373_, lean_object* v_y_374_){
_start:
{
double v_x_boxed_375_; double v_y_boxed_376_; double v_res_377_; lean_object* v_r_378_; 
v_x_boxed_375_ = lean_unbox_float(v_x_373_);
lean_dec_ref(v_x_373_);
v_y_boxed_376_ = lean_unbox_float(v_y_374_);
lean_dec_ref(v_y_374_);
v_res_377_ = l_instMaxFloat___lam__0(v_x_boxed_375_, v_y_boxed_376_);
v_r_378_ = lean_box_float(v_res_377_);
return v_r_378_;
}
}
LEAN_EXPORT lean_object* l_Float_scaleB___boxed(lean_object* v_x_383_, lean_object* v_i_384_){
_start:
{
double v_x_boxed_385_; double v_res_386_; lean_object* v_r_387_; 
v_x_boxed_385_ = lean_unbox_float(v_x_383_);
lean_dec_ref(v_x_383_);
v_res_386_ = lean_float_scaleb(v_x_boxed_385_, v_i_384_);
lean_dec(v_i_384_);
v_r_387_ = lean_box_float(v_res_386_);
return v_r_387_;
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
