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
uint8_t lean_int_dec_le(lean_object*, lean_object*);
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
lean_object* lean_int_sub(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_Internal_instInhabitedUnitVal_default(lean_object* v_00_u03b1_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_obj_once(&l_Std_Time_Internal_instInhabitedUnitVal_default___closed__0, &l_Std_Time_Internal_instInhabitedUnitVal_default___closed__0_once, _init_l_Std_Time_Internal_instInhabitedUnitVal_default___closed__0);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_instInhabitedUnitVal_default___boxed(lean_object* v_00_u03b1_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v_00_u03b1_5_);
lean_dec_ref(v_00_u03b1_5_);
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
LEAN_EXPORT uint8_t l_Std_Time_Internal_instDecidableLeUnitVal___redArg(lean_object* v_x_63_, lean_object* v_y_64_){
_start:
{
uint8_t v___x_65_; 
v___x_65_ = lean_int_dec_le(v_x_63_, v_y_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_instDecidableLeUnitVal___redArg___boxed(lean_object* v_x_66_, lean_object* v_y_67_){
_start:
{
uint8_t v_res_68_; lean_object* v_r_69_; 
v_res_68_ = l_Std_Time_Internal_instDecidableLeUnitVal___redArg(v_x_66_, v_y_67_);
lean_dec(v_y_67_);
lean_dec(v_x_66_);
v_r_69_ = lean_box(v_res_68_);
return v_r_69_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Internal_instDecidableLeUnitVal(lean_object* v_z_70_, lean_object* v_x_71_, lean_object* v_y_72_){
_start:
{
uint8_t v___x_73_; 
v___x_73_ = lean_int_dec_le(v_x_71_, v_y_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_instDecidableLeUnitVal___boxed(lean_object* v_z_74_, lean_object* v_x_75_, lean_object* v_y_76_){
_start:
{
uint8_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = l_Std_Time_Internal_instDecidableLeUnitVal(v_z_74_, v_x_75_, v_y_76_);
lean_dec(v_y_76_);
lean_dec(v_x_75_);
lean_dec_ref(v_z_74_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_ofNat___redArg(lean_object* v_value_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_nat_to_int(v_value_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_ofNat(lean_object* v_00_u03b1_81_, lean_object* v_value_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = lean_nat_to_int(v_value_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_ofNat___boxed(lean_object* v_00_u03b1_84_, lean_object* v_value_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Std_Time_Internal_UnitVal_ofNat(v_00_u03b1_84_, v_value_85_);
lean_dec_ref(v_00_u03b1_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_toInt___redArg(lean_object* v_unit_87_){
_start:
{
lean_inc(v_unit_87_);
return v_unit_87_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_toInt___redArg___boxed(lean_object* v_unit_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Std_Time_Internal_UnitVal_toInt___redArg(v_unit_88_);
lean_dec(v_unit_88_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_toInt(lean_object* v_00_u03b1_90_, lean_object* v_unit_91_){
_start:
{
lean_inc(v_unit_91_);
return v_unit_91_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_toInt___boxed(lean_object* v_00_u03b1_92_, lean_object* v_unit_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Std_Time_Internal_UnitVal_toInt(v_00_u03b1_92_, v_unit_93_);
lean_dec(v_unit_93_);
lean_dec_ref(v_00_u03b1_92_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_mul___redArg(lean_object* v_unit_95_, lean_object* v_factor_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lean_int_mul(v_unit_95_, v_factor_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_mul___redArg___boxed(lean_object* v_unit_98_, lean_object* v_factor_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Std_Time_Internal_UnitVal_mul___redArg(v_unit_98_, v_factor_99_);
lean_dec(v_factor_99_);
lean_dec(v_unit_98_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_mul(lean_object* v_a_101_, lean_object* v_unit_102_, lean_object* v_factor_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lean_int_mul(v_unit_102_, v_factor_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_mul___boxed(lean_object* v_a_105_, lean_object* v_unit_106_, lean_object* v_factor_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Std_Time_Internal_UnitVal_mul(v_a_105_, v_unit_106_, v_factor_107_);
lean_dec(v_factor_107_);
lean_dec(v_unit_106_);
lean_dec_ref(v_a_105_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_ediv___redArg(lean_object* v_unit_109_, lean_object* v_divisor_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = lean_int_ediv(v_unit_109_, v_divisor_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_ediv___redArg___boxed(lean_object* v_unit_112_, lean_object* v_divisor_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Std_Time_Internal_UnitVal_ediv___redArg(v_unit_112_, v_divisor_113_);
lean_dec(v_divisor_113_);
lean_dec(v_unit_112_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_ediv(lean_object* v_a_115_, lean_object* v_unit_116_, lean_object* v_divisor_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_int_ediv(v_unit_116_, v_divisor_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_ediv___boxed(lean_object* v_a_119_, lean_object* v_unit_120_, lean_object* v_divisor_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Std_Time_Internal_UnitVal_ediv(v_a_119_, v_unit_120_, v_divisor_121_);
lean_dec(v_divisor_121_);
lean_dec(v_unit_120_);
lean_dec_ref(v_a_119_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_tdiv___redArg(lean_object* v_unit_123_, lean_object* v_divisor_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = lean_int_div(v_unit_123_, v_divisor_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_tdiv___redArg___boxed(lean_object* v_unit_126_, lean_object* v_divisor_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Std_Time_Internal_UnitVal_tdiv___redArg(v_unit_126_, v_divisor_127_);
lean_dec(v_divisor_127_);
lean_dec(v_unit_126_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_tdiv(lean_object* v_a_129_, lean_object* v_unit_130_, lean_object* v_divisor_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = lean_int_div(v_unit_130_, v_divisor_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_tdiv___boxed(lean_object* v_a_133_, lean_object* v_unit_134_, lean_object* v_divisor_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Std_Time_Internal_UnitVal_tdiv(v_a_133_, v_unit_134_, v_divisor_135_);
lean_dec(v_divisor_135_);
lean_dec(v_unit_134_);
lean_dec_ref(v_a_133_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_div___redArg(lean_object* v_unit_137_, lean_object* v_divisor_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = lean_int_div(v_unit_137_, v_divisor_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_div___redArg___boxed(lean_object* v_unit_140_, lean_object* v_divisor_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Std_Time_Internal_UnitVal_div___redArg(v_unit_140_, v_divisor_141_);
lean_dec(v_divisor_141_);
lean_dec(v_unit_140_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_div(lean_object* v_a_143_, lean_object* v_unit_144_, lean_object* v_divisor_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = lean_int_div(v_unit_144_, v_divisor_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_div___boxed(lean_object* v_a_147_, lean_object* v_unit_148_, lean_object* v_divisor_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Std_Time_Internal_UnitVal_div(v_a_147_, v_unit_148_, v_divisor_149_);
lean_dec(v_divisor_149_);
lean_dec(v_unit_148_);
lean_dec_ref(v_a_147_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_add___redArg(lean_object* v_u1_151_, lean_object* v_u2_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = lean_int_add(v_u1_151_, v_u2_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_add___redArg___boxed(lean_object* v_u1_154_, lean_object* v_u2_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Std_Time_Internal_UnitVal_add___redArg(v_u1_154_, v_u2_155_);
lean_dec(v_u2_155_);
lean_dec(v_u1_154_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_add(lean_object* v_00_u03b1_157_, lean_object* v_u1_158_, lean_object* v_u2_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lean_int_add(v_u1_158_, v_u2_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_add___boxed(lean_object* v_00_u03b1_161_, lean_object* v_u1_162_, lean_object* v_u2_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Std_Time_Internal_UnitVal_add(v_00_u03b1_161_, v_u1_162_, v_u2_163_);
lean_dec(v_u2_163_);
lean_dec(v_u1_162_);
lean_dec_ref(v_00_u03b1_161_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_sub___redArg(lean_object* v_u1_165_, lean_object* v_u2_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_int_sub(v_u1_165_, v_u2_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_sub___redArg___boxed(lean_object* v_u1_168_, lean_object* v_u2_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Std_Time_Internal_UnitVal_sub___redArg(v_u1_168_, v_u2_169_);
lean_dec(v_u2_169_);
lean_dec(v_u1_168_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_sub(lean_object* v_00_u03b1_171_, lean_object* v_u1_172_, lean_object* v_u2_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lean_int_sub(v_u1_172_, v_u2_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_sub___boxed(lean_object* v_00_u03b1_175_, lean_object* v_u1_176_, lean_object* v_u2_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Std_Time_Internal_UnitVal_sub(v_00_u03b1_175_, v_u1_176_, v_u2_177_);
lean_dec(v_u2_177_);
lean_dec(v_u1_176_);
lean_dec_ref(v_00_u03b1_175_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_abs___redArg(lean_object* v_u_179_){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_nat_abs(v_u_179_);
v___x_181_ = lean_nat_to_int(v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_abs___redArg___boxed(lean_object* v_u_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Std_Time_Internal_UnitVal_abs___redArg(v_u_182_);
lean_dec(v_u_182_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_abs(lean_object* v_00_u03b1_184_, lean_object* v_u_185_){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = lean_nat_abs(v_u_185_);
v___x_187_ = lean_nat_to_int(v___x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_abs___boxed(lean_object* v_00_u03b1_188_, lean_object* v_u_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Std_Time_Internal_UnitVal_abs(v_00_u03b1_188_, v_u_189_);
lean_dec(v_u_189_);
lean_dec_ref(v_00_u03b1_188_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_convert(lean_object* v_a_191_, lean_object* v_b_192_, lean_object* v_val_193_){
_start:
{
lean_object* v_ratio_194_; lean_object* v_num_195_; lean_object* v_den_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v_ratio_194_ = l_Rat_div(v_a_191_, v_b_192_);
v_num_195_ = lean_ctor_get(v_ratio_194_, 0);
lean_inc(v_num_195_);
v_den_196_ = lean_ctor_get(v_ratio_194_, 1);
lean_inc(v_den_196_);
lean_dec_ref(v_ratio_194_);
v___x_197_ = lean_int_mul(v_val_193_, v_num_195_);
lean_dec(v_num_195_);
v___x_198_ = lean_nat_to_int(v_den_196_);
v___x_199_ = lean_int_ediv(v___x_197_, v___x_198_);
lean_dec(v___x_198_);
lean_dec(v___x_197_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_convert___boxed(lean_object* v_a_200_, lean_object* v_b_201_, lean_object* v_val_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Std_Time_Internal_UnitVal_convert(v_a_200_, v_b_201_, v_val_202_);
lean_dec(v_val_202_);
lean_dec_ref(v_a_200_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instOfNat___redArg(lean_object* v_n_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = lean_nat_to_int(v_n_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instOfNat(lean_object* v_00_u03b1_206_, lean_object* v_n_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = lean_nat_to_int(v_n_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instOfNat___boxed(lean_object* v_00_u03b1_209_, lean_object* v_n_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Std_Time_Internal_UnitVal_instOfNat(v_00_u03b1_209_, v_n_210_);
lean_dec_ref(v_00_u03b1_209_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instRepr___lam__0(lean_object* v_x_212_, lean_object* v_p_213_){
_start:
{
lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_214_ = lean_obj_once(&l_Std_Time_Internal_instInhabitedUnitVal_default___closed__0, &l_Std_Time_Internal_instInhabitedUnitVal_default___closed__0_once, _init_l_Std_Time_Internal_instInhabitedUnitVal_default___closed__0);
v___x_215_ = lean_int_dec_lt(v_x_212_, v___x_214_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = l_Int_repr(v_x_212_);
v___x_217_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
return v___x_217_;
}
else
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_218_ = l_Int_repr(v_x_212_);
v___x_219_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
v___x_220_ = l_Repr_addAppParen(v___x_219_, v_p_213_);
return v___x_220_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instRepr___lam__0___boxed(lean_object* v_x_221_, lean_object* v_p_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Std_Time_Internal_UnitVal_instRepr___lam__0(v_x_221_, v_p_222_);
lean_dec(v_p_222_);
lean_dec(v_x_221_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instRepr(lean_object* v_00_u03b1_225_){
_start:
{
lean_object* v___f_226_; 
v___f_226_ = ((lean_object*)(l_Std_Time_Internal_UnitVal_instRepr___closed__0));
return v___f_226_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instRepr___boxed(lean_object* v_00_u03b1_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Std_Time_Internal_UnitVal_instRepr(v_00_u03b1_227_);
lean_dec_ref(v_00_u03b1_227_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instLE(lean_object* v_00_u03b1_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = lean_box(0);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instLE___boxed(lean_object* v_00_u03b1_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Std_Time_Internal_UnitVal_instLE(v_00_u03b1_231_);
lean_dec_ref(v_00_u03b1_231_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instLT(lean_object* v_00_u03b1_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = lean_box(0);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instLT___boxed(lean_object* v_00_u03b1_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Std_Time_Internal_UnitVal_instLT(v_00_u03b1_235_);
lean_dec_ref(v_00_u03b1_235_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instAdd(lean_object* v_00_u03b1_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = lean_alloc_closure((void*)(l_Std_Time_Internal_UnitVal_add___boxed), 3, 1);
lean_closure_set(v___x_238_, 0, v_00_u03b1_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instSub(lean_object* v_00_u03b1_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = lean_alloc_closure((void*)(l_Std_Time_Internal_UnitVal_sub___boxed), 3, 1);
lean_closure_set(v___x_240_, 0, v_00_u03b1_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instNeg(lean_object* v_00_u03b1_242_){
_start:
{
lean_object* v___f_243_; 
v___f_243_ = ((lean_object*)(l_Std_Time_Internal_UnitVal_instNeg___closed__0));
return v___f_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instNeg___boxed(lean_object* v_00_u03b1_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Std_Time_Internal_UnitVal_instNeg(v_00_u03b1_244_);
lean_dec_ref(v_00_u03b1_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instToString(lean_object* v_n_247_){
_start:
{
lean_object* v___f_248_; 
v___f_248_ = ((lean_object*)(l_Std_Time_Internal_UnitVal_instToString___closed__0));
return v___f_248_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_instToString___boxed(lean_object* v_n_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Std_Time_Internal_UnitVal_instToString(v_n_249_);
lean_dec_ref(v_n_249_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_cast___redArg(lean_object* v_x_251_){
_start:
{
lean_inc(v_x_251_);
return v_x_251_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_cast___redArg___boxed(lean_object* v_x_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Std_Time_Internal_UnitVal_cast___redArg(v_x_252_);
lean_dec(v_x_252_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_cast(lean_object* v_a_254_, lean_object* v_b_255_, lean_object* v_x_256_, lean_object* v_x_257_){
_start:
{
lean_inc(v_x_257_);
return v_x_257_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Internal_UnitVal_cast___boxed(lean_object* v_a_258_, lean_object* v_b_259_, lean_object* v_x_260_, lean_object* v_x_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Std_Time_Internal_UnitVal_cast(v_a_258_, v_b_259_, v_x_260_, v_x_261_);
lean_dec(v_x_261_);
lean_dec_ref(v_b_259_);
lean_dec_ref(v_a_258_);
return v_res_262_;
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
