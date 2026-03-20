// Lean compiler output
// Module: Std.Time.Time.Unit.Second
// Imports: public import Std.Time.Time.Unit.Nanosecond
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
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_Bounded_instOrd___lam__0___boxed(lean_object*);
lean_object* l_instOrdInt___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Int_neg___boxed(lean_object*);
lean_object* l_Std_Time_Internal_UnitVal_sub___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_UnitVal_instRepr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Int_repr___boxed(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_instOrdUnitVal___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_instInhabitedUnitVal_default(lean_object*);
lean_object* l_Std_Time_Internal_UnitVal_add___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instLEOrdinal(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_Second_instLEOrdinal___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instLTOrdinal(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_Second_instLTOrdinal___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Second_instReprOrdinal___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Second_instReprOrdinal___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Second_instReprOrdinal___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instReprOrdinal___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Second_instReprOrdinal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Second_instReprOrdinal___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Second_instReprOrdinal___closed__0 = (const lean_object*)&l_Std_Time_Second_instReprOrdinal___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Second_instReprOrdinal(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_Second_instReprOrdinal___boxed(lean_object*);
static const lean_closure_object l_Std_Time_Second_instToStringOrdinal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_repr___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Second_instToStringOrdinal___closed__0 = (const lean_object*)&l_Std_Time_Second_instToStringOrdinal___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Second_instToStringOrdinal(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_Second_instToStringOrdinal___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Second_instOfNatOrdinal___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Second_instOfNatOrdinal___closed__0;
static lean_once_cell_t l_Std_Time_Second_instOfNatOrdinal___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Second_instOfNatOrdinal___closed__1;
static lean_once_cell_t l_Std_Time_Second_instOfNatOrdinal___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Second_instOfNatOrdinal___closed__2;
static lean_once_cell_t l_Std_Time_Second_instOfNatOrdinal___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Second_instOfNatOrdinal___closed__3;
static lean_once_cell_t l_Std_Time_Second_instOfNatOrdinal___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Second_instOfNatOrdinal___closed__4;
LEAN_EXPORT lean_object* l_Std_Time_Second_instOfNatOrdinal(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instOfNatOrdinal___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLeOrdinal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLeOrdinal___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLeOrdinal(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLeOrdinal___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLtOrdinal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLtOrdinal___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLtOrdinal(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLtOrdinal___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableEqOrdinal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableEqOrdinal___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableEqOrdinal(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableEqOrdinal___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Second_instOrdOrdinal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_Bounded_instOrd___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Second_instOrdOrdinal___closed__0 = (const lean_object*)&l_Std_Time_Second_instOrdOrdinal___closed__0_value;
static const lean_closure_object l_Std_Time_Second_instOrdOrdinal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdInt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Second_instOrdOrdinal___closed__1 = (const lean_object*)&l_Std_Time_Second_instOrdOrdinal___closed__1_value;
static const lean_closure_object l_Std_Time_Second_instOrdOrdinal___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_compareOn___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Second_instOrdOrdinal___closed__1_value),((lean_object*)&l_Std_Time_Second_instOrdOrdinal___closed__0_value)} };
static const lean_object* l_Std_Time_Second_instOrdOrdinal___closed__2 = (const lean_object*)&l_Std_Time_Second_instOrdOrdinal___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Time_Second_instOrdOrdinal(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_Second_instOrdOrdinal___boxed(lean_object*);
static const lean_closure_object l_Std_Time_Second_instReprOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_UnitVal_instRepr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Second_instReprOffset___closed__0 = (const lean_object*)&l_Std_Time_Second_instReprOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Second_instReprOffset = (const lean_object*)&l_Std_Time_Second_instReprOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Second_instReprOffset_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Second_instReprOffset_spec__0(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableEqOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableEqOffset___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Second_instInhabitedOffset___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Second_instInhabitedOffset___closed__0;
static lean_once_cell_t l_Std_Time_Second_instInhabitedOffset___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Second_instInhabitedOffset___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_Second_instInhabitedOffset;
static lean_once_cell_t l_Std_Time_Second_instAddOffset___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Second_instAddOffset___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Second_instAddOffset;
static lean_once_cell_t l_Std_Time_Second_instSubOffset___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Second_instSubOffset___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Second_instSubOffset;
static const lean_closure_object l_Std_Time_Second_instNegOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Second_instNegOffset___closed__0 = (const lean_object*)&l_Std_Time_Second_instNegOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Second_instNegOffset = (const lean_object*)&l_Std_Time_Second_instNegOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Second_instLEOffset;
LEAN_EXPORT lean_object* l_Std_Time_Second_instLTOffset;
LEAN_EXPORT const lean_object* l_Std_Time_Second_instToStringOffset = (const lean_object*)&l_Std_Time_Second_instToStringOrdinal___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLeOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLeOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLtOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLtOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instOfNatOffset(lean_object*);
static const lean_closure_object l_Std_Time_Second_instOrdOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_instOrdUnitVal___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Second_instOrdOffset___closed__0 = (const lean_object*)&l_Std_Time_Second_instOrdOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Second_instOrdOffset = (const lean_object*)&l_Std_Time_Second_instOrdOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofInt(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofInt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofInt___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofInt___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofInt(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofInt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofNat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofNat(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofNat___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofFin___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofFin(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofFin___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_toOffset___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_toOffset___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_toOffset(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_toOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instLEOrdinal(uint8_t v_leap_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instLEOrdinal___boxed(lean_object* v_leap_3_){
_start:
{
uint8_t v_leap_boxed_4_; lean_object* v_res_5_; 
v_leap_boxed_4_ = lean_unbox(v_leap_3_);
v_res_5_ = l_Std_Time_Second_instLEOrdinal(v_leap_boxed_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instLTOrdinal(uint8_t v_leap_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_box(0);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instLTOrdinal___boxed(lean_object* v_leap_8_){
_start:
{
uint8_t v_leap_boxed_9_; lean_object* v_res_10_; 
v_leap_boxed_9_ = lean_unbox(v_leap_8_);
v_res_10_ = l_Std_Time_Second_instLTOrdinal(v_leap_boxed_9_);
return v_res_10_;
}
}
static lean_object* _init_l_Std_Time_Second_instReprOrdinal___lam__0___closed__0(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_unsigned_to_nat(0u);
v___x_12_ = lean_nat_to_int(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instReprOrdinal___lam__0(lean_object* v_r_13_, lean_object* v___y_14_){
_start:
{
lean_object* v___x_15_; uint8_t v___x_16_; 
v___x_15_ = lean_obj_once(&l_Std_Time_Second_instReprOrdinal___lam__0___closed__0, &l_Std_Time_Second_instReprOrdinal___lam__0___closed__0_once, _init_l_Std_Time_Second_instReprOrdinal___lam__0___closed__0);
v___x_16_ = lean_int_dec_lt(v_r_13_, v___x_15_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = l_Int_repr(v_r_13_);
v___x_18_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
else
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_19_ = l_Int_repr(v_r_13_);
v___x_20_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_20_, 0, v___x_19_);
v___x_21_ = l_Repr_addAppParen(v___x_20_, v___y_14_);
return v___x_21_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instReprOrdinal___lam__0___boxed(lean_object* v_r_22_, lean_object* v___y_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Std_Time_Second_instReprOrdinal___lam__0(v_r_22_, v___y_23_);
lean_dec(v___y_23_);
lean_dec(v_r_22_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instReprOrdinal(uint8_t v_leap_26_){
_start:
{
lean_object* v___f_27_; 
v___f_27_ = ((lean_object*)(l_Std_Time_Second_instReprOrdinal___closed__0));
return v___f_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instReprOrdinal___boxed(lean_object* v_leap_28_){
_start:
{
uint8_t v_leap_boxed_29_; lean_object* v_res_30_; 
v_leap_boxed_29_ = lean_unbox(v_leap_28_);
v_res_30_ = l_Std_Time_Second_instReprOrdinal(v_leap_boxed_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instToStringOrdinal(uint8_t v_leap_32_){
_start:
{
lean_object* v___f_33_; 
v___f_33_ = ((lean_object*)(l_Std_Time_Second_instToStringOrdinal___closed__0));
return v___f_33_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instToStringOrdinal___boxed(lean_object* v_leap_34_){
_start:
{
uint8_t v_leap_boxed_35_; lean_object* v_res_36_; 
v_leap_boxed_35_ = lean_unbox(v_leap_34_);
v_res_36_ = l_Std_Time_Second_instToStringOrdinal(v_leap_boxed_35_);
return v_res_36_;
}
}
static lean_object* _init_l_Std_Time_Second_instOfNatOrdinal___closed__0(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_unsigned_to_nat(59u);
v___x_38_ = lean_nat_to_int(v___x_37_);
return v___x_38_;
}
}
static lean_object* _init_l_Std_Time_Second_instOfNatOrdinal___closed__1(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_39_ = lean_obj_once(&l_Std_Time_Second_instOfNatOrdinal___closed__0, &l_Std_Time_Second_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Second_instOfNatOrdinal___closed__0);
v___x_40_ = lean_obj_once(&l_Std_Time_Second_instReprOrdinal___lam__0___closed__0, &l_Std_Time_Second_instReprOrdinal___lam__0___closed__0_once, _init_l_Std_Time_Second_instReprOrdinal___lam__0___closed__0);
v___x_41_ = lean_int_add(v___x_40_, v___x_39_);
return v___x_41_;
}
}
static lean_object* _init_l_Std_Time_Second_instOfNatOrdinal___closed__2(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_42_ = lean_obj_once(&l_Std_Time_Second_instReprOrdinal___lam__0___closed__0, &l_Std_Time_Second_instReprOrdinal___lam__0___closed__0_once, _init_l_Std_Time_Second_instReprOrdinal___lam__0___closed__0);
v___x_43_ = lean_obj_once(&l_Std_Time_Second_instOfNatOrdinal___closed__1, &l_Std_Time_Second_instOfNatOrdinal___closed__1_once, _init_l_Std_Time_Second_instOfNatOrdinal___closed__1);
v___x_44_ = lean_int_sub(v___x_43_, v___x_42_);
return v___x_44_;
}
}
static lean_object* _init_l_Std_Time_Second_instOfNatOrdinal___closed__3(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_unsigned_to_nat(1u);
v___x_46_ = lean_nat_to_int(v___x_45_);
return v___x_46_;
}
}
static lean_object* _init_l_Std_Time_Second_instOfNatOrdinal___closed__4(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v_range_49_; 
v___x_47_ = lean_obj_once(&l_Std_Time_Second_instOfNatOrdinal___closed__3, &l_Std_Time_Second_instOfNatOrdinal___closed__3_once, _init_l_Std_Time_Second_instOfNatOrdinal___closed__3);
v___x_48_ = lean_obj_once(&l_Std_Time_Second_instOfNatOrdinal___closed__2, &l_Std_Time_Second_instOfNatOrdinal___closed__2_once, _init_l_Std_Time_Second_instOfNatOrdinal___closed__2);
v_range_49_ = lean_int_add(v___x_48_, v___x_47_);
return v_range_49_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instOfNatOrdinal(uint8_t v_leap_50_, lean_object* v_n_51_){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_obj_once(&l_Std_Time_Second_instReprOrdinal___lam__0___closed__0, &l_Std_Time_Second_instReprOrdinal___lam__0___closed__0_once, _init_l_Std_Time_Second_instReprOrdinal___lam__0___closed__0);
v___x_53_ = lean_unsigned_to_nat(59u);
if (v_leap_50_ == 0)
{
lean_object* v_inst_54_; 
v_inst_54_ = l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast(v___x_52_, v_n_51_, v___x_53_);
return v_inst_54_;
}
else
{
lean_object* v___x_55_; lean_object* v_range_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_55_ = lean_nat_to_int(v_n_51_);
v_range_56_ = lean_obj_once(&l_Std_Time_Second_instOfNatOrdinal___closed__4, &l_Std_Time_Second_instOfNatOrdinal___closed__4_once, _init_l_Std_Time_Second_instOfNatOrdinal___closed__4);
v___x_57_ = lean_int_sub(v___x_55_, v___x_52_);
lean_dec(v___x_55_);
v___x_58_ = lean_int_emod(v___x_57_, v_range_56_);
lean_dec(v___x_57_);
v___x_59_ = lean_int_add(v___x_58_, v_range_56_);
lean_dec(v___x_58_);
v___x_60_ = lean_int_emod(v___x_59_, v_range_56_);
lean_dec(v___x_59_);
v___x_61_ = lean_int_add(v___x_60_, v___x_52_);
lean_dec(v___x_60_);
return v___x_61_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instOfNatOrdinal___boxed(lean_object* v_leap_62_, lean_object* v_n_63_){
_start:
{
uint8_t v_leap_boxed_64_; lean_object* v_res_65_; 
v_leap_boxed_64_ = lean_unbox(v_leap_62_);
v_res_65_ = l_Std_Time_Second_instOfNatOrdinal(v_leap_boxed_64_, v_n_63_);
return v_res_65_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLeOrdinal___redArg(lean_object* v_x_66_, lean_object* v_y_67_){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = lean_int_dec_le(v_x_66_, v_y_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLeOrdinal___redArg___boxed(lean_object* v_x_69_, lean_object* v_y_70_){
_start:
{
uint8_t v_res_71_; lean_object* v_r_72_; 
v_res_71_ = l_Std_Time_Second_instDecidableLeOrdinal___redArg(v_x_69_, v_y_70_);
lean_dec(v_y_70_);
lean_dec(v_x_69_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLeOrdinal(uint8_t v_leap_73_, lean_object* v_x_74_, lean_object* v_y_75_){
_start:
{
uint8_t v___x_76_; 
v___x_76_ = lean_int_dec_le(v_x_74_, v_y_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLeOrdinal___boxed(lean_object* v_leap_77_, lean_object* v_x_78_, lean_object* v_y_79_){
_start:
{
uint8_t v_leap_boxed_80_; uint8_t v_res_81_; lean_object* v_r_82_; 
v_leap_boxed_80_ = lean_unbox(v_leap_77_);
v_res_81_ = l_Std_Time_Second_instDecidableLeOrdinal(v_leap_boxed_80_, v_x_78_, v_y_79_);
lean_dec(v_y_79_);
lean_dec(v_x_78_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLtOrdinal___redArg(lean_object* v_x_83_, lean_object* v_y_84_){
_start:
{
uint8_t v___x_85_; 
v___x_85_ = lean_int_dec_lt(v_x_83_, v_y_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLtOrdinal___redArg___boxed(lean_object* v_x_86_, lean_object* v_y_87_){
_start:
{
uint8_t v_res_88_; lean_object* v_r_89_; 
v_res_88_ = l_Std_Time_Second_instDecidableLtOrdinal___redArg(v_x_86_, v_y_87_);
lean_dec(v_y_87_);
lean_dec(v_x_86_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLtOrdinal(uint8_t v_leap_90_, lean_object* v_x_91_, lean_object* v_y_92_){
_start:
{
uint8_t v___x_93_; 
v___x_93_ = lean_int_dec_lt(v_x_91_, v_y_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLtOrdinal___boxed(lean_object* v_leap_94_, lean_object* v_x_95_, lean_object* v_y_96_){
_start:
{
uint8_t v_leap_boxed_97_; uint8_t v_res_98_; lean_object* v_r_99_; 
v_leap_boxed_97_ = lean_unbox(v_leap_94_);
v_res_98_ = l_Std_Time_Second_instDecidableLtOrdinal(v_leap_boxed_97_, v_x_95_, v_y_96_);
lean_dec(v_y_96_);
lean_dec(v_x_95_);
v_r_99_ = lean_box(v_res_98_);
return v_r_99_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableEqOrdinal___redArg(lean_object* v_a_100_, lean_object* v_b_101_){
_start:
{
uint8_t v___x_102_; 
v___x_102_ = lean_int_dec_eq(v_a_100_, v_b_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableEqOrdinal___redArg___boxed(lean_object* v_a_103_, lean_object* v_b_104_){
_start:
{
uint8_t v_res_105_; lean_object* v_r_106_; 
v_res_105_ = l_Std_Time_Second_instDecidableEqOrdinal___redArg(v_a_103_, v_b_104_);
lean_dec(v_b_104_);
lean_dec(v_a_103_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableEqOrdinal(uint8_t v_leap_107_, lean_object* v_a_108_, lean_object* v_b_109_){
_start:
{
uint8_t v___x_110_; 
v___x_110_ = lean_int_dec_eq(v_a_108_, v_b_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableEqOrdinal___boxed(lean_object* v_leap_111_, lean_object* v_a_112_, lean_object* v_b_113_){
_start:
{
uint8_t v_leap_boxed_114_; uint8_t v_res_115_; lean_object* v_r_116_; 
v_leap_boxed_114_ = lean_unbox(v_leap_111_);
v_res_115_ = l_Std_Time_Second_instDecidableEqOrdinal(v_leap_boxed_114_, v_a_112_, v_b_113_);
lean_dec(v_b_113_);
lean_dec(v_a_112_);
v_r_116_ = lean_box(v_res_115_);
return v_r_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instOrdOrdinal(uint8_t v_leap_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = ((lean_object*)(l_Std_Time_Second_instOrdOrdinal___closed__2));
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instOrdOrdinal___boxed(lean_object* v_leap_124_){
_start:
{
uint8_t v_leap_boxed_125_; lean_object* v_res_126_; 
v_leap_boxed_125_ = lean_unbox(v_leap_124_);
v_res_126_ = l_Std_Time_Second_instOrdOrdinal(v_leap_boxed_125_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Second_instReprOffset_spec__0_spec__0(lean_object* v_a_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = lean_nat_to_int(v_a_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Second_instReprOffset_spec__0(lean_object* v_a_131_){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = lean_nat_to_int(v_a_131_);
v___x_133_ = l_Rat_ofInt(v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableEqOffset(lean_object* v_a_134_, lean_object* v_b_135_){
_start:
{
uint8_t v___x_136_; 
v___x_136_ = lean_int_dec_eq(v_a_134_, v_b_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableEqOffset___boxed(lean_object* v_a_137_, lean_object* v_b_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l_Std_Time_Second_instDecidableEqOffset(v_a_137_, v_b_138_);
lean_dec(v_b_138_);
lean_dec(v_a_137_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
static lean_object* _init_l_Std_Time_Second_instInhabitedOffset___closed__0(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = lean_unsigned_to_nat(1u);
v___x_142_ = l_Nat_cast___at___00Std_Time_Second_instReprOffset_spec__0(v___x_141_);
return v___x_142_;
}
}
static lean_object* _init_l_Std_Time_Second_instInhabitedOffset___closed__1(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = lean_obj_once(&l_Std_Time_Second_instInhabitedOffset___closed__0, &l_Std_Time_Second_instInhabitedOffset___closed__0_once, _init_l_Std_Time_Second_instInhabitedOffset___closed__0);
v___x_144_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_143_);
return v___x_144_;
}
}
static lean_object* _init_l_Std_Time_Second_instInhabitedOffset(void){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = lean_obj_once(&l_Std_Time_Second_instInhabitedOffset___closed__1, &l_Std_Time_Second_instInhabitedOffset___closed__1_once, _init_l_Std_Time_Second_instInhabitedOffset___closed__1);
return v___x_145_;
}
}
static lean_object* _init_l_Std_Time_Second_instAddOffset___closed__0(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = lean_obj_once(&l_Std_Time_Second_instInhabitedOffset___closed__0, &l_Std_Time_Second_instInhabitedOffset___closed__0_once, _init_l_Std_Time_Second_instInhabitedOffset___closed__0);
v___x_147_ = lean_alloc_closure((void*)(l_Std_Time_Internal_UnitVal_add___boxed), 3, 1);
lean_closure_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
}
static lean_object* _init_l_Std_Time_Second_instAddOffset(void){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = lean_obj_once(&l_Std_Time_Second_instAddOffset___closed__0, &l_Std_Time_Second_instAddOffset___closed__0_once, _init_l_Std_Time_Second_instAddOffset___closed__0);
return v___x_148_;
}
}
static lean_object* _init_l_Std_Time_Second_instSubOffset___closed__0(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = lean_obj_once(&l_Std_Time_Second_instInhabitedOffset___closed__0, &l_Std_Time_Second_instInhabitedOffset___closed__0_once, _init_l_Std_Time_Second_instInhabitedOffset___closed__0);
v___x_150_ = lean_alloc_closure((void*)(l_Std_Time_Internal_UnitVal_sub___boxed), 3, 1);
lean_closure_set(v___x_150_, 0, v___x_149_);
return v___x_150_;
}
}
static lean_object* _init_l_Std_Time_Second_instSubOffset(void){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lean_obj_once(&l_Std_Time_Second_instSubOffset___closed__0, &l_Std_Time_Second_instSubOffset___closed__0_once, _init_l_Std_Time_Second_instSubOffset___closed__0);
return v___x_151_;
}
}
static lean_object* _init_l_Std_Time_Second_instLEOffset(void){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = lean_box(0);
return v___x_154_;
}
}
static lean_object* _init_l_Std_Time_Second_instLTOffset(void){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = lean_box(0);
return v___x_155_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLeOffset(lean_object* v_x_157_, lean_object* v_y_158_){
_start:
{
uint8_t v___x_159_; 
v___x_159_ = lean_int_dec_le(v_x_157_, v_y_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLeOffset___boxed(lean_object* v_x_160_, lean_object* v_y_161_){
_start:
{
uint8_t v_res_162_; lean_object* v_r_163_; 
v_res_162_ = l_Std_Time_Second_instDecidableLeOffset(v_x_160_, v_y_161_);
lean_dec(v_y_161_);
lean_dec(v_x_160_);
v_r_163_ = lean_box(v_res_162_);
return v_r_163_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLtOffset(lean_object* v_x_164_, lean_object* v_y_165_){
_start:
{
uint8_t v___x_166_; 
v___x_166_ = lean_int_dec_lt(v_x_164_, v_y_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLtOffset___boxed(lean_object* v_x_167_, lean_object* v_y_168_){
_start:
{
uint8_t v_res_169_; lean_object* v_r_170_; 
v_res_169_ = l_Std_Time_Second_instDecidableLtOffset(v_x_167_, v_y_168_);
lean_dec(v_y_168_);
lean_dec(v_x_167_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instOfNatOffset(lean_object* v_n_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lean_nat_to_int(v_n_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofNat(lean_object* v_data_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = lean_nat_to_int(v_data_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofInt(lean_object* v_data_177_){
_start:
{
lean_inc(v_data_177_);
return v_data_177_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofInt___boxed(lean_object* v_data_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Std_Time_Second_Offset_ofInt(v_data_178_);
lean_dec(v_data_178_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofInt___redArg(lean_object* v_data_180_){
_start:
{
lean_inc(v_data_180_);
return v_data_180_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofInt___redArg___boxed(lean_object* v_data_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Std_Time_Second_Ordinal_ofInt___redArg(v_data_181_);
lean_dec(v_data_181_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofInt(uint8_t v_leap_183_, lean_object* v_data_184_, lean_object* v_h_185_){
_start:
{
lean_inc(v_data_184_);
return v_data_184_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofInt___boxed(lean_object* v_leap_186_, lean_object* v_data_187_, lean_object* v_h_188_){
_start:
{
uint8_t v_leap_boxed_189_; lean_object* v_res_190_; 
v_leap_boxed_189_ = lean_unbox(v_leap_186_);
v_res_190_ = l_Std_Time_Second_Ordinal_ofInt(v_leap_boxed_189_, v_data_187_, v_h_188_);
lean_dec(v_data_187_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofNat___redArg(lean_object* v_data_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_nat_to_int(v_data_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofNat(uint8_t v_leap_193_, lean_object* v_data_194_, lean_object* v_h_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = lean_nat_to_int(v_data_194_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofNat___boxed(lean_object* v_leap_197_, lean_object* v_data_198_, lean_object* v_h_199_){
_start:
{
uint8_t v_leap_boxed_200_; lean_object* v_res_201_; 
v_leap_boxed_200_ = lean_unbox(v_leap_197_);
v_res_201_ = l_Std_Time_Second_Ordinal_ofNat(v_leap_boxed_200_, v_data_198_, v_h_199_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofFin___redArg(lean_object* v_data_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = lean_nat_to_int(v_data_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofFin(uint8_t v_leap_204_, lean_object* v_data_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = lean_nat_to_int(v_data_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofFin___boxed(lean_object* v_leap_207_, lean_object* v_data_208_){
_start:
{
uint8_t v_leap_boxed_209_; lean_object* v_res_210_; 
v_leap_boxed_209_ = lean_unbox(v_leap_207_);
v_res_210_ = l_Std_Time_Second_Ordinal_ofFin(v_leap_boxed_209_, v_data_208_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_toOffset___redArg(lean_object* v_ordinal_211_){
_start:
{
lean_inc(v_ordinal_211_);
return v_ordinal_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_toOffset___redArg___boxed(lean_object* v_ordinal_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Std_Time_Second_Ordinal_toOffset___redArg(v_ordinal_212_);
lean_dec(v_ordinal_212_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_toOffset(uint8_t v_leap_214_, lean_object* v_ordinal_215_){
_start:
{
lean_inc(v_ordinal_215_);
return v_ordinal_215_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_toOffset___boxed(lean_object* v_leap_216_, lean_object* v_ordinal_217_){
_start:
{
uint8_t v_leap_boxed_218_; lean_object* v_res_219_; 
v_leap_boxed_218_ = lean_unbox(v_leap_216_);
v_res_219_ = l_Std_Time_Second_Ordinal_toOffset(v_leap_boxed_218_, v_ordinal_217_);
lean_dec(v_ordinal_217_);
return v_res_219_;
}
}
lean_object* runtime_initialize_Std_Time_Time_Unit_Nanosecond(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Time_Unit_Second(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time_Time_Unit_Nanosecond(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_Second_instInhabitedOffset = _init_l_Std_Time_Second_instInhabitedOffset();
lean_mark_persistent(l_Std_Time_Second_instInhabitedOffset);
l_Std_Time_Second_instAddOffset = _init_l_Std_Time_Second_instAddOffset();
lean_mark_persistent(l_Std_Time_Second_instAddOffset);
l_Std_Time_Second_instSubOffset = _init_l_Std_Time_Second_instSubOffset();
lean_mark_persistent(l_Std_Time_Second_instSubOffset);
l_Std_Time_Second_instLEOffset = _init_l_Std_Time_Second_instLEOffset();
lean_mark_persistent(l_Std_Time_Second_instLEOffset);
l_Std_Time_Second_instLTOffset = _init_l_Std_Time_Second_instLTOffset();
lean_mark_persistent(l_Std_Time_Second_instLTOffset);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Time_Unit_Second(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Time_Unit_Nanosecond(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Time_Unit_Second(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Time_Unit_Nanosecond(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Time_Unit_Second(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Time_Unit_Second(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Time_Unit_Second(builtin);
}
#ifdef __cplusplus
}
#endif
