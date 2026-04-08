// Lean compiler output
// Module: Std.Time.Internal.UnitVal
// Imports: public import Init.Data.Order.Ord public import Init.Data.Rat.Basic
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
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_nonneg(lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Int_repr___boxed(lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Int_neg___boxed(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Internal_instInhabitedUnitVal_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Internal_instInhabitedUnitVal_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Internal_instInhabitedUnitVal_default(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_instInhabitedUnitVal_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_instInhabitedUnitVal(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_instInhabitedUnitVal___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Internal_instDecidableEqUnitVal_decEq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_instDecidableEqUnitVal_decEq___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Internal_instDecidableEqUnitVal_decEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_instDecidableEqUnitVal_decEq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Internal_instDecidableEqUnitVal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_instDecidableEqUnitVal___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Internal_instDecidableEqUnitVal(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_instDecidableEqUnitVal___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_instLEUnitVal(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_instLEUnitVal___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Internal_instOrdUnitVal___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_instOrdUnitVal___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Internal_instOrdUnitVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_instOrdUnitVal___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Internal_instOrdUnitVal___closed__0 = (const lean_object*)&l_Std_Time_Internal_instOrdUnitVal___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Internal_instOrdUnitVal(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_instOrdUnitVal___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Internal_instDecidableLeUnitVal___aux__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_instDecidableLeUnitVal___aux__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Internal_instDecidableLeUnitVal___aux__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_instDecidableLeUnitVal___aux__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Internal_instDecidableLeUnitVal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_instDecidableLeUnitVal___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Internal_instDecidableLeUnitVal(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_instDecidableLeUnitVal___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_ofNat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_ofNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_ofNat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_toInt___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_toInt___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_toInt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_toInt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_mul___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_mul___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_mul(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_mul___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_ediv___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_ediv___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_ediv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_ediv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_tdiv___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_tdiv___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_tdiv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_tdiv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_div___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_div___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_div(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_div___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_add___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_add___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_add(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_add___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_sub___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_sub___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_sub(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_sub___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_abs___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_abs___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_abs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_abs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_convert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_convert___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instOfNat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instOfNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instOfNat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instRepr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instRepr___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Internal_UnitVal_instRepr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_UnitVal_instRepr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Internal_UnitVal_instRepr___closed__0 = (const lean_object*)&l_Std_Time_Internal_UnitVal_instRepr___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instRepr(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instRepr___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instLE(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instLE___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instLT(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instLT___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instAdd(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instSub(lean_object*);
static const lean_closure_object l_Std_Time_Internal_UnitVal_instNeg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Internal_UnitVal_instNeg___closed__0 = (const lean_object*)&l_Std_Time_Internal_UnitVal_instNeg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instNeg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instNeg___boxed(lean_object*);
static const lean_closure_object l_Std_Time_Internal_UnitVal_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_repr___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Internal_UnitVal_instToString___closed__0 = (const lean_object*)&l_Std_Time_Internal_UnitVal_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instToString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instToString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_cast___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_cast(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Std_Time_Internal_instInhabitedUnitVal_default___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_instInhabitedUnitVal_default(lean_object* v_a_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_obj_once(&l_Std_Time_Internal_instInhabitedUnitVal_default___closed__0, &l_Std_Time_Internal_instInhabitedUnitVal_default___closed__0_once, _init_l_Std_Time_Internal_instInhabitedUnitVal_default___closed__0);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_instInhabitedUnitVal_default___boxed(lean_object* v_a_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v_a_5_);
lean_dec_ref(v_a_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_instInhabitedUnitVal(lean_object* v_a_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v_a_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_instInhabitedUnitVal___boxed(lean_object* v_a_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Std_Time_Internal_instInhabitedUnitVal(v_a_9_);
lean_dec_ref(v_a_9_);
return v_res_10_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Internal_instDecidableEqUnitVal_decEq___redArg(lean_object* v_x_11_, lean_object* v_x_12_){
_start:
{
uint8_t v___x_13_; 
v___x_13_ = lean_int_dec_eq(v_x_11_, v_x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_instDecidableEqUnitVal_decEq___redArg___boxed(lean_object* v_x_14_, lean_object* v_x_15_){
_start:
{
uint8_t v_res_16_; lean_object* v_r_17_; 
v_res_16_ = l_Std_Time_Internal_instDecidableEqUnitVal_decEq___redArg(v_x_14_, v_x_15_);
lean_dec(v_x_15_);
lean_dec(v_x_14_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Internal_instDecidableEqUnitVal_decEq(lean_object* v_00_u03b1_18_, lean_object* v_x_19_, lean_object* v_x_20_){
_start:
{
uint8_t v___x_21_; 
v___x_21_ = lean_int_dec_eq(v_x_19_, v_x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_instDecidableEqUnitVal_decEq___boxed(lean_object* v_00_u03b1_22_, lean_object* v_x_23_, lean_object* v_x_24_){
_start:
{
uint8_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = l_Std_Time_Internal_instDecidableEqUnitVal_decEq(v_00_u03b1_22_, v_x_23_, v_x_24_);
lean_dec(v_x_24_);
lean_dec(v_x_23_);
lean_dec_ref(v_00_u03b1_22_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Internal_instDecidableEqUnitVal___redArg(lean_object* v_x_27_, lean_object* v_x_28_){
_start:
{
uint8_t v___x_29_; 
v___x_29_ = lean_int_dec_eq(v_x_27_, v_x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_instDecidableEqUnitVal___redArg___boxed(lean_object* v_x_30_, lean_object* v_x_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = l_Std_Time_Internal_instDecidableEqUnitVal___redArg(v_x_30_, v_x_31_);
lean_dec(v_x_31_);
lean_dec(v_x_30_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Internal_instDecidableEqUnitVal(lean_object* v_00_u03b1_34_, lean_object* v_x_35_, lean_object* v_x_36_){
_start:
{
uint8_t v___x_37_; 
v___x_37_ = lean_int_dec_eq(v_x_35_, v_x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_instDecidableEqUnitVal___boxed(lean_object* v_00_u03b1_38_, lean_object* v_x_39_, lean_object* v_x_40_){
_start:
{
uint8_t v_res_41_; lean_object* v_r_42_; 
v_res_41_ = l_Std_Time_Internal_instDecidableEqUnitVal(v_00_u03b1_38_, v_x_39_, v_x_40_);
lean_dec(v_x_40_);
lean_dec(v_x_39_);
lean_dec_ref(v_00_u03b1_38_);
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_instLEUnitVal(lean_object* v_x_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_box(0);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_instLEUnitVal___boxed(lean_object* v_x_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Std_Time_Internal_instLEUnitVal(v_x_45_);
lean_dec_ref(v_x_45_);
return v_res_46_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Internal_instOrdUnitVal___lam__0(lean_object* v_x_47_, lean_object* v_y_48_){
_start:
{
uint8_t v___x_49_; 
v___x_49_ = lean_int_dec_lt(v_x_47_, v_y_48_);
if (v___x_49_ == 0)
{
uint8_t v___x_50_; 
v___x_50_ = lean_int_dec_eq(v_x_47_, v_y_48_);
if (v___x_50_ == 0)
{
uint8_t v___x_51_; 
v___x_51_ = 2;
return v___x_51_;
}
else
{
uint8_t v___x_52_; 
v___x_52_ = 1;
return v___x_52_;
}
}
else
{
uint8_t v___x_53_; 
v___x_53_ = 0;
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_instOrdUnitVal___lam__0___boxed(lean_object* v_x_54_, lean_object* v_y_55_){
_start:
{
uint8_t v_res_56_; lean_object* v_r_57_; 
v_res_56_ = l_Std_Time_Internal_instOrdUnitVal___lam__0(v_x_54_, v_y_55_);
lean_dec(v_y_55_);
lean_dec(v_x_54_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_instOrdUnitVal(lean_object* v_x_59_){
_start:
{
lean_object* v___f_60_; 
v___f_60_ = ((lean_object*)(l_Std_Time_Internal_instOrdUnitVal___closed__0));
return v___f_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_instOrdUnitVal___boxed(lean_object* v_x_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Std_Time_Internal_instOrdUnitVal(v_x_61_);
lean_dec_ref(v_x_61_);
return v_res_62_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Internal_instDecidableLeUnitVal___aux__1___redArg(lean_object* v_x_63_, lean_object* v_y_64_){
_start:
{
lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_65_ = lean_int_sub(v_y_64_, v_x_63_);
v___x_66_ = lean_int_dec_nonneg(v___x_65_);
lean_dec(v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_instDecidableLeUnitVal___aux__1___redArg___boxed(lean_object* v_x_67_, lean_object* v_y_68_){
_start:
{
uint8_t v_res_69_; lean_object* v_r_70_; 
v_res_69_ = l_Std_Time_Internal_instDecidableLeUnitVal___aux__1___redArg(v_x_67_, v_y_68_);
lean_dec(v_y_68_);
lean_dec(v_x_67_);
v_r_70_ = lean_box(v_res_69_);
return v_r_70_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Internal_instDecidableLeUnitVal___aux__1(lean_object* v_z_71_, lean_object* v_x_72_, lean_object* v_y_73_){
_start:
{
uint8_t v___x_74_; 
v___x_74_ = l_Std_Time_Internal_instDecidableLeUnitVal___aux__1___redArg(v_x_72_, v_y_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_instDecidableLeUnitVal___aux__1___boxed(lean_object* v_z_75_, lean_object* v_x_76_, lean_object* v_y_77_){
_start:
{
uint8_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = l_Std_Time_Internal_instDecidableLeUnitVal___aux__1(v_z_75_, v_x_76_, v_y_77_);
lean_dec(v_y_77_);
lean_dec(v_x_76_);
lean_dec_ref(v_z_75_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Internal_instDecidableLeUnitVal___redArg(lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
uint8_t v___x_82_; 
v___x_82_ = l_Std_Time_Internal_instDecidableLeUnitVal___aux__1___redArg(v___y_80_, v___y_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_instDecidableLeUnitVal___redArg___boxed(lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
uint8_t v_res_85_; lean_object* v_r_86_; 
v_res_85_ = l_Std_Time_Internal_instDecidableLeUnitVal___redArg(v___y_83_, v___y_84_);
lean_dec(v___y_84_);
lean_dec(v___y_83_);
v_r_86_ = lean_box(v_res_85_);
return v_r_86_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Internal_instDecidableLeUnitVal(lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
uint8_t v___x_90_; 
v___x_90_ = l_Std_Time_Internal_instDecidableLeUnitVal___aux__1___redArg(v___y_88_, v___y_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_instDecidableLeUnitVal___boxed(lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
uint8_t v_res_94_; lean_object* v_r_95_; 
v_res_94_ = l_Std_Time_Internal_instDecidableLeUnitVal(v___y_91_, v___y_92_, v___y_93_);
lean_dec(v___y_93_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
v_r_95_ = lean_box(v_res_94_);
return v_r_95_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_ofNat___redArg(lean_object* v_value_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lean_nat_to_int(v_value_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_ofNat(lean_object* v_00_u03b1_98_, lean_object* v_value_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lean_nat_to_int(v_value_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_ofNat___boxed(lean_object* v_00_u03b1_101_, lean_object* v_value_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Std_Time_Internal_UnitVal_ofNat(v_00_u03b1_101_, v_value_102_);
lean_dec_ref(v_00_u03b1_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_toInt___redArg(lean_object* v_unit_104_){
_start:
{
lean_inc(v_unit_104_);
return v_unit_104_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_toInt___redArg___boxed(lean_object* v_unit_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Std_Time_Internal_UnitVal_toInt___redArg(v_unit_105_);
lean_dec(v_unit_105_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_toInt(lean_object* v_00_u03b1_107_, lean_object* v_unit_108_){
_start:
{
lean_inc(v_unit_108_);
return v_unit_108_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_toInt___boxed(lean_object* v_00_u03b1_109_, lean_object* v_unit_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Std_Time_Internal_UnitVal_toInt(v_00_u03b1_109_, v_unit_110_);
lean_dec(v_unit_110_);
lean_dec_ref(v_00_u03b1_109_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_mul___redArg(lean_object* v_unit_112_, lean_object* v_factor_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = lean_int_mul(v_unit_112_, v_factor_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_mul___redArg___boxed(lean_object* v_unit_115_, lean_object* v_factor_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Std_Time_Internal_UnitVal_mul___redArg(v_unit_115_, v_factor_116_);
lean_dec(v_factor_116_);
lean_dec(v_unit_115_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_mul(lean_object* v_a_118_, lean_object* v_unit_119_, lean_object* v_factor_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = lean_int_mul(v_unit_119_, v_factor_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_mul___boxed(lean_object* v_a_122_, lean_object* v_unit_123_, lean_object* v_factor_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Std_Time_Internal_UnitVal_mul(v_a_122_, v_unit_123_, v_factor_124_);
lean_dec(v_factor_124_);
lean_dec(v_unit_123_);
lean_dec_ref(v_a_122_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_ediv___redArg(lean_object* v_unit_126_, lean_object* v_divisor_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = lean_int_ediv(v_unit_126_, v_divisor_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_ediv___redArg___boxed(lean_object* v_unit_129_, lean_object* v_divisor_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Std_Time_Internal_UnitVal_ediv___redArg(v_unit_129_, v_divisor_130_);
lean_dec(v_divisor_130_);
lean_dec(v_unit_129_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_ediv(lean_object* v_a_132_, lean_object* v_unit_133_, lean_object* v_divisor_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = lean_int_ediv(v_unit_133_, v_divisor_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_ediv___boxed(lean_object* v_a_136_, lean_object* v_unit_137_, lean_object* v_divisor_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Std_Time_Internal_UnitVal_ediv(v_a_136_, v_unit_137_, v_divisor_138_);
lean_dec(v_divisor_138_);
lean_dec(v_unit_137_);
lean_dec_ref(v_a_136_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_tdiv___redArg(lean_object* v_unit_140_, lean_object* v_divisor_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = lean_int_div(v_unit_140_, v_divisor_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_tdiv___redArg___boxed(lean_object* v_unit_143_, lean_object* v_divisor_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Std_Time_Internal_UnitVal_tdiv___redArg(v_unit_143_, v_divisor_144_);
lean_dec(v_divisor_144_);
lean_dec(v_unit_143_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_tdiv(lean_object* v_a_146_, lean_object* v_unit_147_, lean_object* v_divisor_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = lean_int_div(v_unit_147_, v_divisor_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_tdiv___boxed(lean_object* v_a_150_, lean_object* v_unit_151_, lean_object* v_divisor_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Std_Time_Internal_UnitVal_tdiv(v_a_150_, v_unit_151_, v_divisor_152_);
lean_dec(v_divisor_152_);
lean_dec(v_unit_151_);
lean_dec_ref(v_a_150_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_div___redArg(lean_object* v_unit_154_, lean_object* v_divisor_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = lean_int_div(v_unit_154_, v_divisor_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_div___redArg___boxed(lean_object* v_unit_157_, lean_object* v_divisor_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Std_Time_Internal_UnitVal_div___redArg(v_unit_157_, v_divisor_158_);
lean_dec(v_divisor_158_);
lean_dec(v_unit_157_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_div(lean_object* v_a_160_, lean_object* v_unit_161_, lean_object* v_divisor_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = lean_int_div(v_unit_161_, v_divisor_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_div___boxed(lean_object* v_a_164_, lean_object* v_unit_165_, lean_object* v_divisor_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Std_Time_Internal_UnitVal_div(v_a_164_, v_unit_165_, v_divisor_166_);
lean_dec(v_divisor_166_);
lean_dec(v_unit_165_);
lean_dec_ref(v_a_164_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_add___redArg(lean_object* v_u1_168_, lean_object* v_u2_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = lean_int_add(v_u1_168_, v_u2_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_add___redArg___boxed(lean_object* v_u1_171_, lean_object* v_u2_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Std_Time_Internal_UnitVal_add___redArg(v_u1_171_, v_u2_172_);
lean_dec(v_u2_172_);
lean_dec(v_u1_171_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_add(lean_object* v_00_u03b1_174_, lean_object* v_u1_175_, lean_object* v_u2_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = lean_int_add(v_u1_175_, v_u2_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_add___boxed(lean_object* v_00_u03b1_178_, lean_object* v_u1_179_, lean_object* v_u2_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Std_Time_Internal_UnitVal_add(v_00_u03b1_178_, v_u1_179_, v_u2_180_);
lean_dec(v_u2_180_);
lean_dec(v_u1_179_);
lean_dec_ref(v_00_u03b1_178_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_sub___redArg(lean_object* v_u1_182_, lean_object* v_u2_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = lean_int_sub(v_u1_182_, v_u2_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_sub___redArg___boxed(lean_object* v_u1_185_, lean_object* v_u2_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Std_Time_Internal_UnitVal_sub___redArg(v_u1_185_, v_u2_186_);
lean_dec(v_u2_186_);
lean_dec(v_u1_185_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_sub(lean_object* v_00_u03b1_188_, lean_object* v_u1_189_, lean_object* v_u2_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = lean_int_sub(v_u1_189_, v_u2_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_sub___boxed(lean_object* v_00_u03b1_192_, lean_object* v_u1_193_, lean_object* v_u2_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Std_Time_Internal_UnitVal_sub(v_00_u03b1_192_, v_u1_193_, v_u2_194_);
lean_dec(v_u2_194_);
lean_dec(v_u1_193_);
lean_dec_ref(v_00_u03b1_192_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_abs___redArg(lean_object* v_u_196_){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_nat_abs(v_u_196_);
v___x_198_ = lean_nat_to_int(v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_abs___redArg___boxed(lean_object* v_u_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Std_Time_Internal_UnitVal_abs___redArg(v_u_199_);
lean_dec(v_u_199_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_abs(lean_object* v_00_u03b1_201_, lean_object* v_u_202_){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_nat_abs(v_u_202_);
v___x_204_ = lean_nat_to_int(v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_abs___boxed(lean_object* v_00_u03b1_205_, lean_object* v_u_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Std_Time_Internal_UnitVal_abs(v_00_u03b1_205_, v_u_206_);
lean_dec(v_u_206_);
lean_dec_ref(v_00_u03b1_205_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_convert(lean_object* v_a_208_, lean_object* v_b_209_, lean_object* v_val_210_){
_start:
{
lean_object* v_ratio_211_; lean_object* v_num_212_; lean_object* v_den_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v_ratio_211_ = l_Rat_div(v_a_208_, v_b_209_);
v_num_212_ = lean_ctor_get(v_ratio_211_, 0);
lean_inc(v_num_212_);
v_den_213_ = lean_ctor_get(v_ratio_211_, 1);
lean_inc(v_den_213_);
lean_dec_ref(v_ratio_211_);
v___x_214_ = lean_int_mul(v_val_210_, v_num_212_);
lean_dec(v_num_212_);
v___x_215_ = lean_nat_to_int(v_den_213_);
v___x_216_ = lean_int_ediv(v___x_214_, v___x_215_);
lean_dec(v___x_215_);
lean_dec(v___x_214_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_convert___boxed(lean_object* v_a_217_, lean_object* v_b_218_, lean_object* v_val_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Std_Time_Internal_UnitVal_convert(v_a_217_, v_b_218_, v_val_219_);
lean_dec(v_val_219_);
lean_dec_ref(v_a_217_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instOfNat___redArg(lean_object* v_n_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = lean_nat_to_int(v_n_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instOfNat(lean_object* v_00_u03b1_223_, lean_object* v_n_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = lean_nat_to_int(v_n_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instOfNat___boxed(lean_object* v_00_u03b1_226_, lean_object* v_n_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Std_Time_Internal_UnitVal_instOfNat(v_00_u03b1_226_, v_n_227_);
lean_dec_ref(v_00_u03b1_226_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instRepr___lam__0(lean_object* v_x_229_, lean_object* v_p_230_){
_start:
{
lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_231_ = lean_obj_once(&l_Std_Time_Internal_instInhabitedUnitVal_default___closed__0, &l_Std_Time_Internal_instInhabitedUnitVal_default___closed__0_once, _init_l_Std_Time_Internal_instInhabitedUnitVal_default___closed__0);
v___x_232_ = lean_int_dec_lt(v_x_229_, v___x_231_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = l_Int_repr(v_x_229_);
v___x_234_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
return v___x_234_;
}
else
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_235_ = l_Int_repr(v_x_229_);
v___x_236_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
v___x_237_ = l_Repr_addAppParen(v___x_236_, v_p_230_);
return v___x_237_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instRepr___lam__0___boxed(lean_object* v_x_238_, lean_object* v_p_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Std_Time_Internal_UnitVal_instRepr___lam__0(v_x_238_, v_p_239_);
lean_dec(v_p_239_);
lean_dec(v_x_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instRepr(lean_object* v_00_u03b1_242_){
_start:
{
lean_object* v___f_243_; 
v___f_243_ = ((lean_object*)(l_Std_Time_Internal_UnitVal_instRepr___closed__0));
return v___f_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instRepr___boxed(lean_object* v_00_u03b1_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Std_Time_Internal_UnitVal_instRepr(v_00_u03b1_244_);
lean_dec_ref(v_00_u03b1_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instLE(lean_object* v_00_u03b1_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = lean_box(0);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instLE___boxed(lean_object* v_00_u03b1_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Std_Time_Internal_UnitVal_instLE(v_00_u03b1_248_);
lean_dec_ref(v_00_u03b1_248_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instLT(lean_object* v_00_u03b1_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = lean_box(0);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instLT___boxed(lean_object* v_00_u03b1_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Std_Time_Internal_UnitVal_instLT(v_00_u03b1_252_);
lean_dec_ref(v_00_u03b1_252_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instAdd(lean_object* v_00_u03b1_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = lean_alloc_closure((void*)(l_Std_Time_Internal_UnitVal_add___boxed), 3, 1);
lean_closure_set(v___x_255_, 0, v_00_u03b1_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instSub(lean_object* v_00_u03b1_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = lean_alloc_closure((void*)(l_Std_Time_Internal_UnitVal_sub___boxed), 3, 1);
lean_closure_set(v___x_257_, 0, v_00_u03b1_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instNeg(lean_object* v_00_u03b1_259_){
_start:
{
lean_object* v___f_260_; 
v___f_260_ = ((lean_object*)(l_Std_Time_Internal_UnitVal_instNeg___closed__0));
return v___f_260_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instNeg___boxed(lean_object* v_00_u03b1_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Std_Time_Internal_UnitVal_instNeg(v_00_u03b1_261_);
lean_dec_ref(v_00_u03b1_261_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instToString(lean_object* v_n_264_){
_start:
{
lean_object* v___f_265_; 
v___f_265_ = ((lean_object*)(l_Std_Time_Internal_UnitVal_instToString___closed__0));
return v___f_265_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instToString___boxed(lean_object* v_n_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Std_Time_Internal_UnitVal_instToString(v_n_266_);
lean_dec_ref(v_n_266_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_cast___redArg(lean_object* v_x_268_){
_start:
{
lean_inc(v_x_268_);
return v_x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_cast___redArg___boxed(lean_object* v_x_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Std_Time_Internal_UnitVal_cast___redArg(v_x_269_);
lean_dec(v_x_269_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_cast(lean_object* v_a_271_, lean_object* v_b_272_, lean_object* v_x_273_, lean_object* v_x_274_){
_start:
{
lean_inc(v_x_274_);
return v_x_274_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_cast___boxed(lean_object* v_a_275_, lean_object* v_b_276_, lean_object* v_x_277_, lean_object* v_x_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Std_Time_Internal_UnitVal_cast(v_a_275_, v_b_276_, v_x_277_, v_x_278_);
lean_dec(v_x_278_);
lean_dec_ref(v_b_276_);
lean_dec_ref(v_a_275_);
return v_res_279_;
}
}
lean_object* runtime_initialize_Init_Data_Order_Ord(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Rat_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Internal_UnitVal(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Order_Ord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Rat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Internal_UnitVal(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Order_Ord(uint8_t builtin);
lean_object* initialize_Init_Data_Rat_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Internal_UnitVal(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order_Ord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Rat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Internal_UnitVal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Internal_UnitVal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Internal_UnitVal(builtin);
}
#ifdef __cplusplus
}
#endif
