// Lean compiler output
// Module: Std.Time.Time.Unit.Nanosecond
// Imports: public import Std.Time.Internal
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
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Int_neg___boxed(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_instInhabitedUnitVal_default(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_Bounded_instOrd___lam__0___boxed(lean_object*);
lean_object* l_instOrdInt___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_Bounded_instRepr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_UnitVal_instRepr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_instOrdUnitVal___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_UnitVal_sub___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_UnitVal_instToString___lam__0___boxed(lean_object*);
lean_object* l_Std_Time_Internal_UnitVal_add___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Nanosecond_instReprOrdinal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_Bounded_instRepr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Nanosecond_instReprOrdinal___closed__0 = (const lean_object*)&l_Std_Time_Nanosecond_instReprOrdinal___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Nanosecond_instReprOrdinal = (const lean_object*)&l_Std_Time_Nanosecond_instReprOrdinal___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableEqOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqOrdinal___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instLEOrdinal;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instLTOrdinal;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instOfNatOrdinal(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instOfNatOrdinal___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__0;
static lean_once_cell_t l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instInhabitedOrdinal;
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLeOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeOrdinal___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLtOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtOrdinal___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Nanosecond_instOrdOrdinal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_Bounded_instOrd___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Nanosecond_instOrdOrdinal___closed__0 = (const lean_object*)&l_Std_Time_Nanosecond_instOrdOrdinal___closed__0_value;
static const lean_closure_object l_Std_Time_Nanosecond_instOrdOrdinal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdInt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Nanosecond_instOrdOrdinal___closed__1 = (const lean_object*)&l_Std_Time_Nanosecond_instOrdOrdinal___closed__1_value;
static const lean_closure_object l_Std_Time_Nanosecond_instOrdOrdinal___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_compareOn___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Nanosecond_instOrdOrdinal___closed__1_value),((lean_object*)&l_Std_Time_Nanosecond_instOrdOrdinal___closed__0_value)} };
static const lean_object* l_Std_Time_Nanosecond_instOrdOrdinal___closed__2 = (const lean_object*)&l_Std_Time_Nanosecond_instOrdOrdinal___closed__2_value;
LEAN_EXPORT const lean_object* l_Std_Time_Nanosecond_instOrdOrdinal = (const lean_object*)&l_Std_Time_Nanosecond_instOrdOrdinal___closed__2_value;
static const lean_closure_object l_Std_Time_Nanosecond_instReprOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_UnitVal_instRepr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Nanosecond_instReprOffset___closed__0 = (const lean_object*)&l_Std_Time_Nanosecond_instReprOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Nanosecond_instReprOffset = (const lean_object*)&l_Std_Time_Nanosecond_instReprOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Nanosecond_instReprOffset_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Nanosecond_instReprOffset_spec__0(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableEqOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqOffset___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Nanosecond_instInhabitedOffset___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Nanosecond_instInhabitedOffset___closed__0;
static lean_once_cell_t l_Std_Time_Nanosecond_instInhabitedOffset___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Nanosecond_instInhabitedOffset___closed__1;
static lean_once_cell_t l_Std_Time_Nanosecond_instInhabitedOffset___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Nanosecond_instInhabitedOffset___closed__2;
static lean_once_cell_t l_Std_Time_Nanosecond_instInhabitedOffset___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Nanosecond_instInhabitedOffset___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instInhabitedOffset;
static lean_once_cell_t l_Std_Time_Nanosecond_instAddOffset___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Nanosecond_instAddOffset___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instAddOffset;
static lean_once_cell_t l_Std_Time_Nanosecond_instSubOffset___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Nanosecond_instSubOffset___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instSubOffset;
static const lean_closure_object l_Std_Time_Nanosecond_instNegOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Nanosecond_instNegOffset___closed__0 = (const lean_object*)&l_Std_Time_Nanosecond_instNegOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Nanosecond_instNegOffset = (const lean_object*)&l_Std_Time_Nanosecond_instNegOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instLEOffset;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instLTOffset;
static const lean_closure_object l_Std_Time_Nanosecond_instToStringOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_UnitVal_instToString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Nanosecond_instToStringOffset___closed__0 = (const lean_object*)&l_Std_Time_Nanosecond_instToStringOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Nanosecond_instToStringOffset = (const lean_object*)&l_Std_Time_Nanosecond_instToStringOffset___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLeOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLtOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instOfNatOffset(lean_object*);
static const lean_closure_object l_Std_Time_Nanosecond_instOrdOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_instOrdUnitVal___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Nanosecond_instOrdOffset___closed__0 = (const lean_object*)&l_Std_Time_Nanosecond_instOrdOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Nanosecond_instOrdOffset = (const lean_object*)&l_Std_Time_Nanosecond_instOrdOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofInt(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofInt___boxed(lean_object*);
LEAN_EXPORT const lean_object* l_Std_Time_Nanosecond_instReprSpan = (const lean_object*)&l_Std_Time_Nanosecond_instReprOrdinal___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableEqSpan(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqSpan___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instLESpan;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instLTSpan;
static lean_once_cell_t l_Std_Time_Nanosecond_instInhabitedSpan___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Nanosecond_instInhabitedSpan___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instInhabitedSpan;
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLeSpan(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeSpan___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLtSpan(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtSpan___boxed(lean_object*, lean_object*);
LEAN_EXPORT const lean_object* l_Std_Time_Nanosecond_instOrdSpan = (const lean_object*)&l_Std_Time_Nanosecond_instOrdOrdinal___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Span_toOffset(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Span_toOffset___boxed(lean_object*);
LEAN_EXPORT const lean_object* l_Std_Time_Nanosecond_Ordinal_instReprOfDay = (const lean_object*)&l_Std_Time_Nanosecond_instReprOrdinal___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instLEOfDay;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instLTOfDay;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instInhabitedOfDay;
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay___boxed(lean_object*, lean_object*);
LEAN_EXPORT const lean_object* l_Std_Time_Nanosecond_Ordinal_instOrdOfDay = (const lean_object*)&l_Std_Time_Nanosecond_instOrdOrdinal___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofInt___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofInt___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofInt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofInt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofNat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofFin(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_toOffset(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_toOffset___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableEqOrdinal(lean_object* v_a_3_, lean_object* v_b_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_int_dec_eq(v_a_3_, v_b_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqOrdinal___boxed(lean_object* v_a_6_, lean_object* v_b_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = l_Std_Time_Nanosecond_instDecidableEqOrdinal(v_a_6_, v_b_7_);
lean_dec(v_b_7_);
lean_dec(v_a_6_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instLEOrdinal(void){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_box(0);
return v___x_10_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instLTOrdinal(void){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_box(0);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instOfNatOrdinal(lean_object* v_n_12_){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_13_ = lean_unsigned_to_nat(1000000000u);
v___x_14_ = lean_nat_mod(v_n_12_, v___x_13_);
v___x_15_ = lean_nat_to_int(v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instOfNatOrdinal___boxed(lean_object* v_n_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Std_Time_Nanosecond_instOfNatOrdinal(v_n_16_);
lean_dec(v_n_16_);
return v_res_17_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__0(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_18_ = lean_unsigned_to_nat(1000000000u);
v___x_19_ = lean_unsigned_to_nat(0u);
v___x_20_ = lean_nat_mod(v___x_19_, v___x_18_);
return v___x_20_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__1(void){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_obj_once(&l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__0, &l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__0);
v___x_22_ = lean_nat_to_int(v___x_21_);
return v___x_22_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOrdinal(void){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lean_obj_once(&l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__1, &l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__1_once, _init_l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__1);
return v___x_23_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLeOrdinal(lean_object* v_x_24_, lean_object* v_y_25_){
_start:
{
uint8_t v___x_26_; 
v___x_26_ = lean_int_dec_le(v_x_24_, v_y_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeOrdinal___boxed(lean_object* v_x_27_, lean_object* v_y_28_){
_start:
{
uint8_t v_res_29_; lean_object* v_r_30_; 
v_res_29_ = l_Std_Time_Nanosecond_instDecidableLeOrdinal(v_x_27_, v_y_28_);
lean_dec(v_y_28_);
lean_dec(v_x_27_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLtOrdinal(lean_object* v_x_31_, lean_object* v_y_32_){
_start:
{
uint8_t v___x_33_; 
v___x_33_ = lean_int_dec_lt(v_x_31_, v_y_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtOrdinal___boxed(lean_object* v_x_34_, lean_object* v_y_35_){
_start:
{
uint8_t v_res_36_; lean_object* v_r_37_; 
v_res_36_ = l_Std_Time_Nanosecond_instDecidableLtOrdinal(v_x_34_, v_y_35_);
lean_dec(v_y_35_);
lean_dec(v_x_34_);
v_r_37_ = lean_box(v_res_36_);
return v_r_37_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Nanosecond_instReprOffset_spec__0_spec__0(lean_object* v_a_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lean_nat_to_int(v_a_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Nanosecond_instReprOffset_spec__0(lean_object* v_a_48_){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_nat_to_int(v_a_48_);
v___x_50_ = l_Rat_ofInt(v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableEqOffset(lean_object* v_a_51_, lean_object* v_b_52_){
_start:
{
uint8_t v___x_53_; 
v___x_53_ = lean_int_dec_eq(v_a_51_, v_b_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqOffset___boxed(lean_object* v_a_54_, lean_object* v_b_55_){
_start:
{
uint8_t v_res_56_; lean_object* v_r_57_; 
v_res_56_ = l_Std_Time_Nanosecond_instDecidableEqOffset(v_a_54_, v_b_55_);
lean_dec(v_b_55_);
lean_dec(v_a_54_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOffset___closed__0(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_unsigned_to_nat(1u);
v___x_59_ = l_Nat_cast___at___00Std_Time_Nanosecond_instReprOffset_spec__0(v___x_58_);
return v___x_59_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOffset___closed__1(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_unsigned_to_nat(1000000000u);
v___x_61_ = l_Nat_cast___at___00Std_Time_Nanosecond_instReprOffset_spec__0(v___x_60_);
return v___x_61_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOffset___closed__2(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = lean_obj_once(&l_Std_Time_Nanosecond_instInhabitedOffset___closed__1, &l_Std_Time_Nanosecond_instInhabitedOffset___closed__1_once, _init_l_Std_Time_Nanosecond_instInhabitedOffset___closed__1);
v___x_63_ = lean_obj_once(&l_Std_Time_Nanosecond_instInhabitedOffset___closed__0, &l_Std_Time_Nanosecond_instInhabitedOffset___closed__0_once, _init_l_Std_Time_Nanosecond_instInhabitedOffset___closed__0);
v___x_64_ = l_Rat_div(v___x_63_, v___x_62_);
return v___x_64_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOffset___closed__3(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_obj_once(&l_Std_Time_Nanosecond_instInhabitedOffset___closed__2, &l_Std_Time_Nanosecond_instInhabitedOffset___closed__2_once, _init_l_Std_Time_Nanosecond_instInhabitedOffset___closed__2);
v___x_66_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_65_);
return v___x_66_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOffset(void){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lean_obj_once(&l_Std_Time_Nanosecond_instInhabitedOffset___closed__3, &l_Std_Time_Nanosecond_instInhabitedOffset___closed__3_once, _init_l_Std_Time_Nanosecond_instInhabitedOffset___closed__3);
return v___x_67_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instAddOffset___closed__0(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = lean_obj_once(&l_Std_Time_Nanosecond_instInhabitedOffset___closed__2, &l_Std_Time_Nanosecond_instInhabitedOffset___closed__2_once, _init_l_Std_Time_Nanosecond_instInhabitedOffset___closed__2);
v___x_69_ = lean_alloc_closure((void*)(l_Std_Time_Internal_UnitVal_add___boxed), 3, 1);
lean_closure_set(v___x_69_, 0, v___x_68_);
return v___x_69_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instAddOffset(void){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lean_obj_once(&l_Std_Time_Nanosecond_instAddOffset___closed__0, &l_Std_Time_Nanosecond_instAddOffset___closed__0_once, _init_l_Std_Time_Nanosecond_instAddOffset___closed__0);
return v___x_70_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instSubOffset___closed__0(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_obj_once(&l_Std_Time_Nanosecond_instInhabitedOffset___closed__2, &l_Std_Time_Nanosecond_instInhabitedOffset___closed__2_once, _init_l_Std_Time_Nanosecond_instInhabitedOffset___closed__2);
v___x_72_ = lean_alloc_closure((void*)(l_Std_Time_Internal_UnitVal_sub___boxed), 3, 1);
lean_closure_set(v___x_72_, 0, v___x_71_);
return v___x_72_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instSubOffset(void){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lean_obj_once(&l_Std_Time_Nanosecond_instSubOffset___closed__0, &l_Std_Time_Nanosecond_instSubOffset___closed__0_once, _init_l_Std_Time_Nanosecond_instSubOffset___closed__0);
return v___x_73_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instLEOffset(void){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_box(0);
return v___x_76_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instLTOffset(void){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_box(0);
return v___x_77_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLeOffset(lean_object* v_x_80_, lean_object* v_y_81_){
_start:
{
uint8_t v___x_82_; 
v___x_82_ = lean_int_dec_le(v_x_80_, v_y_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeOffset___boxed(lean_object* v_x_83_, lean_object* v_y_84_){
_start:
{
uint8_t v_res_85_; lean_object* v_r_86_; 
v_res_85_ = l_Std_Time_Nanosecond_instDecidableLeOffset(v_x_83_, v_y_84_);
lean_dec(v_y_84_);
lean_dec(v_x_83_);
v_r_86_ = lean_box(v_res_85_);
return v_r_86_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLtOffset(lean_object* v_x_87_, lean_object* v_y_88_){
_start:
{
uint8_t v___x_89_; 
v___x_89_ = lean_int_dec_lt(v_x_87_, v_y_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtOffset___boxed(lean_object* v_x_90_, lean_object* v_y_91_){
_start:
{
uint8_t v_res_92_; lean_object* v_r_93_; 
v_res_92_ = l_Std_Time_Nanosecond_instDecidableLtOffset(v_x_90_, v_y_91_);
lean_dec(v_y_91_);
lean_dec(v_x_90_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instOfNatOffset(lean_object* v_n_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lean_nat_to_int(v_n_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofNat(lean_object* v_data_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lean_nat_to_int(v_data_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofInt(lean_object* v_data_100_){
_start:
{
lean_inc(v_data_100_);
return v_data_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofInt___boxed(lean_object* v_data_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Std_Time_Nanosecond_Offset_ofInt(v_data_101_);
lean_dec(v_data_101_);
return v_res_102_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableEqSpan(lean_object* v_a_104_, lean_object* v_b_105_){
_start:
{
uint8_t v___x_106_; 
v___x_106_ = lean_int_dec_eq(v_a_104_, v_b_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqSpan___boxed(lean_object* v_a_107_, lean_object* v_b_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Std_Time_Nanosecond_instDecidableEqSpan(v_a_107_, v_b_108_);
lean_dec(v_b_108_);
lean_dec(v_a_107_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instLESpan(void){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = lean_box(0);
return v___x_111_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instLTSpan(void){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lean_box(0);
return v___x_112_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedSpan___closed__0(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_unsigned_to_nat(0u);
v___x_114_ = lean_nat_to_int(v___x_113_);
return v___x_114_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedSpan(void){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lean_obj_once(&l_Std_Time_Nanosecond_instInhabitedSpan___closed__0, &l_Std_Time_Nanosecond_instInhabitedSpan___closed__0_once, _init_l_Std_Time_Nanosecond_instInhabitedSpan___closed__0);
return v___x_115_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLeSpan(lean_object* v_x_116_, lean_object* v_y_117_){
_start:
{
uint8_t v___x_118_; 
v___x_118_ = lean_int_dec_le(v_x_116_, v_y_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeSpan___boxed(lean_object* v_x_119_, lean_object* v_y_120_){
_start:
{
uint8_t v_res_121_; lean_object* v_r_122_; 
v_res_121_ = l_Std_Time_Nanosecond_instDecidableLeSpan(v_x_119_, v_y_120_);
lean_dec(v_y_120_);
lean_dec(v_x_119_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLtSpan(lean_object* v_x_123_, lean_object* v_y_124_){
_start:
{
uint8_t v___x_125_; 
v___x_125_ = lean_int_dec_lt(v_x_123_, v_y_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtSpan___boxed(lean_object* v_x_126_, lean_object* v_y_127_){
_start:
{
uint8_t v_res_128_; lean_object* v_r_129_; 
v_res_128_ = l_Std_Time_Nanosecond_instDecidableLtSpan(v_x_126_, v_y_127_);
lean_dec(v_y_127_);
lean_dec(v_x_126_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Span_toOffset(lean_object* v_span_131_){
_start:
{
lean_inc(v_span_131_);
return v_span_131_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Span_toOffset___boxed(lean_object* v_span_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Std_Time_Nanosecond_Span_toOffset(v_span_132_);
lean_dec(v_span_132_);
return v_res_133_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay(lean_object* v_a_135_, lean_object* v_b_136_){
_start:
{
uint8_t v___x_137_; 
v___x_137_ = lean_int_dec_eq(v_a_135_, v_b_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay___boxed(lean_object* v_a_138_, lean_object* v_b_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay(v_a_138_, v_b_139_);
lean_dec(v_b_139_);
lean_dec(v_a_138_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_Ordinal_instLEOfDay(void){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = lean_box(0);
return v___x_142_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_Ordinal_instLTOfDay(void){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = lean_box(0);
return v___x_143_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_Ordinal_instInhabitedOfDay(void){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = lean_obj_once(&l_Std_Time_Nanosecond_instInhabitedSpan___closed__0, &l_Std_Time_Nanosecond_instInhabitedSpan___closed__0_once, _init_l_Std_Time_Nanosecond_instInhabitedSpan___closed__0);
return v___x_144_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay(lean_object* v_x_145_, lean_object* v_y_146_){
_start:
{
uint8_t v___x_147_; 
v___x_147_ = lean_int_dec_le(v_x_145_, v_y_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay___boxed(lean_object* v_x_148_, lean_object* v_y_149_){
_start:
{
uint8_t v_res_150_; lean_object* v_r_151_; 
v_res_150_ = l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay(v_x_148_, v_y_149_);
lean_dec(v_y_149_);
lean_dec(v_x_148_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay(lean_object* v_x_152_, lean_object* v_y_153_){
_start:
{
uint8_t v___x_154_; 
v___x_154_ = lean_int_dec_lt(v_x_152_, v_y_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay___boxed(lean_object* v_x_155_, lean_object* v_y_156_){
_start:
{
uint8_t v_res_157_; lean_object* v_r_158_; 
v_res_157_ = l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay(v_x_155_, v_y_156_);
lean_dec(v_y_156_);
lean_dec(v_x_155_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofInt___redArg(lean_object* v_data_160_){
_start:
{
lean_inc(v_data_160_);
return v_data_160_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofInt___redArg___boxed(lean_object* v_data_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Std_Time_Nanosecond_Ordinal_ofInt___redArg(v_data_161_);
lean_dec(v_data_161_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofInt(lean_object* v_data_163_, lean_object* v_h_164_){
_start:
{
lean_inc(v_data_163_);
return v_data_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofInt___boxed(lean_object* v_data_165_, lean_object* v_h_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Std_Time_Nanosecond_Ordinal_ofInt(v_data_165_, v_h_166_);
lean_dec(v_data_165_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofNat___redArg(lean_object* v_data_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = lean_nat_to_int(v_data_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofNat(lean_object* v_data_170_, lean_object* v_h_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lean_nat_to_int(v_data_170_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofFin(lean_object* v_data_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lean_nat_to_int(v_data_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_toOffset(lean_object* v_ordinal_175_){
_start:
{
lean_inc(v_ordinal_175_);
return v_ordinal_175_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_toOffset___boxed(lean_object* v_ordinal_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Std_Time_Nanosecond_Ordinal_toOffset(v_ordinal_176_);
lean_dec(v_ordinal_176_);
return v_res_177_;
}
}
lean_object* runtime_initialize_Std_Time_Internal(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Time_Unit_Nanosecond(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_Nanosecond_instLEOrdinal = _init_l_Std_Time_Nanosecond_instLEOrdinal();
lean_mark_persistent(l_Std_Time_Nanosecond_instLEOrdinal);
l_Std_Time_Nanosecond_instLTOrdinal = _init_l_Std_Time_Nanosecond_instLTOrdinal();
lean_mark_persistent(l_Std_Time_Nanosecond_instLTOrdinal);
l_Std_Time_Nanosecond_instInhabitedOrdinal = _init_l_Std_Time_Nanosecond_instInhabitedOrdinal();
lean_mark_persistent(l_Std_Time_Nanosecond_instInhabitedOrdinal);
l_Std_Time_Nanosecond_instInhabitedOffset = _init_l_Std_Time_Nanosecond_instInhabitedOffset();
lean_mark_persistent(l_Std_Time_Nanosecond_instInhabitedOffset);
l_Std_Time_Nanosecond_instAddOffset = _init_l_Std_Time_Nanosecond_instAddOffset();
lean_mark_persistent(l_Std_Time_Nanosecond_instAddOffset);
l_Std_Time_Nanosecond_instSubOffset = _init_l_Std_Time_Nanosecond_instSubOffset();
lean_mark_persistent(l_Std_Time_Nanosecond_instSubOffset);
l_Std_Time_Nanosecond_instLEOffset = _init_l_Std_Time_Nanosecond_instLEOffset();
lean_mark_persistent(l_Std_Time_Nanosecond_instLEOffset);
l_Std_Time_Nanosecond_instLTOffset = _init_l_Std_Time_Nanosecond_instLTOffset();
lean_mark_persistent(l_Std_Time_Nanosecond_instLTOffset);
l_Std_Time_Nanosecond_instLESpan = _init_l_Std_Time_Nanosecond_instLESpan();
lean_mark_persistent(l_Std_Time_Nanosecond_instLESpan);
l_Std_Time_Nanosecond_instLTSpan = _init_l_Std_Time_Nanosecond_instLTSpan();
lean_mark_persistent(l_Std_Time_Nanosecond_instLTSpan);
l_Std_Time_Nanosecond_instInhabitedSpan = _init_l_Std_Time_Nanosecond_instInhabitedSpan();
lean_mark_persistent(l_Std_Time_Nanosecond_instInhabitedSpan);
l_Std_Time_Nanosecond_Ordinal_instLEOfDay = _init_l_Std_Time_Nanosecond_Ordinal_instLEOfDay();
lean_mark_persistent(l_Std_Time_Nanosecond_Ordinal_instLEOfDay);
l_Std_Time_Nanosecond_Ordinal_instLTOfDay = _init_l_Std_Time_Nanosecond_Ordinal_instLTOfDay();
lean_mark_persistent(l_Std_Time_Nanosecond_Ordinal_instLTOfDay);
l_Std_Time_Nanosecond_Ordinal_instInhabitedOfDay = _init_l_Std_Time_Nanosecond_Ordinal_instInhabitedOfDay();
lean_mark_persistent(l_Std_Time_Nanosecond_Ordinal_instInhabitedOfDay);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Time_Unit_Nanosecond(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Internal(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Time_Unit_Nanosecond(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Time_Unit_Nanosecond(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Time_Unit_Nanosecond(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Time_Unit_Nanosecond(builtin);
}
#ifdef __cplusplus
}
#endif
