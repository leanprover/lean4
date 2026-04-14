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
lean_object* l_Int_neg___boxed(lean_object*);
lean_object* l_Int_sub___boxed(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Int_repr___boxed(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Rat_instNatCast___lam__0(lean_object*);
lean_object* l_Std_Time_Internal_instInhabitedUnitVal_default(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_add___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableEqOrdinal___aux__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableEqOrdinal___aux__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableEqOrdinal___aux__1(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableEqOrdinal___aux__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableEqOrdinal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableEqOrdinal___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableEqOrdinal(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableEqOrdinal___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Second_instOrdOrdinal___aux__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instOrdOrdinal___aux__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Second_instOrdOrdinal___aux__1(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instOrdOrdinal___aux__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instOrdOrdinal(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_Second_instOrdOrdinal___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instReprOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instReprOffset___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instReprOffset___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instReprOffset___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Second_instReprOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Second_instReprOffset___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Second_instReprOffset___closed__0 = (const lean_object*)&l_Std_Time_Second_instReprOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Second_instReprOffset = (const lean_object*)&l_Std_Time_Second_instReprOffset___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableEqOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableEqOffset___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableEqOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableEqOffset___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Second_instInhabitedOffset___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Second_instInhabitedOffset___aux__1___closed__0;
static lean_once_cell_t l_Std_Time_Second_instInhabitedOffset___aux__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Second_instInhabitedOffset___aux__1___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_Second_instInhabitedOffset___aux__1;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Second_instInhabitedOffset_spec__0(lean_object*);
static lean_once_cell_t l_Std_Time_Second_instInhabitedOffset___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Second_instInhabitedOffset___closed__0;
static lean_once_cell_t l_Std_Time_Second_instInhabitedOffset___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Second_instInhabitedOffset___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_Second_instInhabitedOffset;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Second_instInhabitedOffset_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instAddOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instAddOffset___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Second_instAddOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Second_instAddOffset___closed__0 = (const lean_object*)&l_Std_Time_Second_instAddOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Second_instAddOffset = (const lean_object*)&l_Std_Time_Second_instAddOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Second_instSubOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instSubOffset___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Second_instSubOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Second_instSubOffset___closed__0 = (const lean_object*)&l_Std_Time_Second_instSubOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Second_instSubOffset = (const lean_object*)&l_Std_Time_Second_instSubOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Second_instNegOffset___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instNegOffset___aux__1___boxed(lean_object*);
static const lean_closure_object l_Std_Time_Second_instNegOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Second_instNegOffset___closed__0 = (const lean_object*)&l_Std_Time_Second_instNegOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Second_instNegOffset = (const lean_object*)&l_Std_Time_Second_instNegOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Second_instLEOffset;
LEAN_EXPORT lean_object* l_Std_Time_Second_instLTOffset;
LEAN_EXPORT lean_object* l_Std_Time_Second_instToStringOffset___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instToStringOffset___aux__1___boxed(lean_object*);
LEAN_EXPORT const lean_object* l_Std_Time_Second_instToStringOffset = (const lean_object*)&l_Std_Time_Second_instToStringOrdinal___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLeOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLeOffset___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLeOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLeOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLtOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLtOffset___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLtOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLtOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instOfNatOffset(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Second_instOrdOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instOrdOffset___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Second_instOrdOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Second_instOrdOffset___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableEqOrdinal___aux__1___redArg(lean_object* v_a_100_, lean_object* v_b_101_){
_start:
{
uint8_t v___x_102_; 
v___x_102_ = lean_int_dec_eq(v_a_100_, v_b_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableEqOrdinal___aux__1___redArg___boxed(lean_object* v_a_103_, lean_object* v_b_104_){
_start:
{
uint8_t v_res_105_; lean_object* v_r_106_; 
v_res_105_ = l_Std_Time_Second_instDecidableEqOrdinal___aux__1___redArg(v_a_103_, v_b_104_);
lean_dec(v_b_104_);
lean_dec(v_a_103_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableEqOrdinal___aux__1(uint8_t v_leap_107_, lean_object* v_a_108_, lean_object* v_b_109_){
_start:
{
uint8_t v___x_110_; 
v___x_110_ = lean_int_dec_eq(v_a_108_, v_b_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableEqOrdinal___aux__1___boxed(lean_object* v_leap_111_, lean_object* v_a_112_, lean_object* v_b_113_){
_start:
{
uint8_t v_leap_boxed_114_; uint8_t v_res_115_; lean_object* v_r_116_; 
v_leap_boxed_114_ = lean_unbox(v_leap_111_);
v_res_115_ = l_Std_Time_Second_instDecidableEqOrdinal___aux__1(v_leap_boxed_114_, v_a_112_, v_b_113_);
lean_dec(v_b_113_);
lean_dec(v_a_112_);
v_r_116_ = lean_box(v_res_115_);
return v_r_116_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableEqOrdinal___redArg(lean_object* v_a_117_, lean_object* v_b_118_){
_start:
{
uint8_t v___x_119_; 
v___x_119_ = lean_int_dec_eq(v_a_117_, v_b_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableEqOrdinal___redArg___boxed(lean_object* v_a_120_, lean_object* v_b_121_){
_start:
{
uint8_t v_res_122_; lean_object* v_r_123_; 
v_res_122_ = l_Std_Time_Second_instDecidableEqOrdinal___redArg(v_a_120_, v_b_121_);
lean_dec(v_b_121_);
lean_dec(v_a_120_);
v_r_123_ = lean_box(v_res_122_);
return v_r_123_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableEqOrdinal(uint8_t v_leap_124_, lean_object* v_a_125_, lean_object* v_b_126_){
_start:
{
uint8_t v___x_127_; 
v___x_127_ = lean_int_dec_eq(v_a_125_, v_b_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableEqOrdinal___boxed(lean_object* v_leap_128_, lean_object* v_a_129_, lean_object* v_b_130_){
_start:
{
uint8_t v_leap_boxed_131_; uint8_t v_res_132_; lean_object* v_r_133_; 
v_leap_boxed_131_ = lean_unbox(v_leap_128_);
v_res_132_ = l_Std_Time_Second_instDecidableEqOrdinal(v_leap_boxed_131_, v_a_129_, v_b_130_);
lean_dec(v_b_130_);
lean_dec(v_a_129_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instOrdOrdinal___aux__1___redArg(lean_object* v_x_134_, lean_object* v_y_135_){
_start:
{
uint8_t v___x_136_; 
v___x_136_ = lean_int_dec_lt(v_x_134_, v_y_135_);
if (v___x_136_ == 0)
{
uint8_t v___x_137_; 
v___x_137_ = lean_int_dec_eq(v_x_134_, v_y_135_);
if (v___x_137_ == 0)
{
uint8_t v___x_138_; 
v___x_138_ = 2;
return v___x_138_;
}
else
{
uint8_t v___x_139_; 
v___x_139_ = 1;
return v___x_139_;
}
}
else
{
uint8_t v___x_140_; 
v___x_140_ = 0;
return v___x_140_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instOrdOrdinal___aux__1___redArg___boxed(lean_object* v_x_141_, lean_object* v_y_142_){
_start:
{
uint8_t v_res_143_; lean_object* v_r_144_; 
v_res_143_ = l_Std_Time_Second_instOrdOrdinal___aux__1___redArg(v_x_141_, v_y_142_);
lean_dec(v_y_142_);
lean_dec(v_x_141_);
v_r_144_ = lean_box(v_res_143_);
return v_r_144_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instOrdOrdinal___aux__1(uint8_t v_leap_145_, lean_object* v_x_146_, lean_object* v_y_147_){
_start:
{
uint8_t v___x_148_; 
v___x_148_ = lean_int_dec_lt(v_x_146_, v_y_147_);
if (v___x_148_ == 0)
{
uint8_t v___x_149_; 
v___x_149_ = lean_int_dec_eq(v_x_146_, v_y_147_);
if (v___x_149_ == 0)
{
uint8_t v___x_150_; 
v___x_150_ = 2;
return v___x_150_;
}
else
{
uint8_t v___x_151_; 
v___x_151_ = 1;
return v___x_151_;
}
}
else
{
uint8_t v___x_152_; 
v___x_152_ = 0;
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instOrdOrdinal___aux__1___boxed(lean_object* v_leap_153_, lean_object* v_x_154_, lean_object* v_y_155_){
_start:
{
uint8_t v_leap_boxed_156_; uint8_t v_res_157_; lean_object* v_r_158_; 
v_leap_boxed_156_ = lean_unbox(v_leap_153_);
v_res_157_ = l_Std_Time_Second_instOrdOrdinal___aux__1(v_leap_boxed_156_, v_x_154_, v_y_155_);
lean_dec(v_y_155_);
lean_dec(v_x_154_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instOrdOrdinal(uint8_t v_leap_159_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = lean_box(v_leap_159_);
v___x_161_ = lean_alloc_closure((void*)(l_Std_Time_Second_instOrdOrdinal___aux__1___boxed), 3, 1);
lean_closure_set(v___x_161_, 0, v___x_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instOrdOrdinal___boxed(lean_object* v_leap_162_){
_start:
{
uint8_t v_leap_boxed_163_; lean_object* v_res_164_; 
v_leap_boxed_163_ = lean_unbox(v_leap_162_);
v_res_164_ = l_Std_Time_Second_instOrdOrdinal(v_leap_boxed_163_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instReprOffset___aux__1(lean_object* v_x_165_, lean_object* v_p_166_){
_start:
{
lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_167_ = lean_obj_once(&l_Std_Time_Second_instReprOrdinal___lam__0___closed__0, &l_Std_Time_Second_instReprOrdinal___lam__0___closed__0_once, _init_l_Std_Time_Second_instReprOrdinal___lam__0___closed__0);
v___x_168_ = lean_int_dec_lt(v_x_165_, v___x_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = l_Int_repr(v_x_165_);
v___x_170_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
return v___x_170_;
}
else
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_171_ = l_Int_repr(v_x_165_);
v___x_172_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
v___x_173_ = l_Repr_addAppParen(v___x_172_, v_p_166_);
return v___x_173_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instReprOffset___aux__1___boxed(lean_object* v_x_174_, lean_object* v_p_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Std_Time_Second_instReprOffset___aux__1(v_x_174_, v_p_175_);
lean_dec(v_p_175_);
lean_dec(v_x_174_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instReprOffset___lam__0(lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_179_ = lean_obj_once(&l_Std_Time_Second_instReprOrdinal___lam__0___closed__0, &l_Std_Time_Second_instReprOrdinal___lam__0___closed__0_once, _init_l_Std_Time_Second_instReprOrdinal___lam__0___closed__0);
v___x_180_ = lean_int_dec_lt(v___y_177_, v___x_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = l_Int_repr(v___y_177_);
v___x_182_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
return v___x_182_;
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = l_Int_repr(v___y_177_);
v___x_184_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
v___x_185_ = l_Repr_addAppParen(v___x_184_, v___y_178_);
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instReprOffset___lam__0___boxed(lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Std_Time_Second_instReprOffset___lam__0(v___y_186_, v___y_187_);
lean_dec(v___y_187_);
lean_dec(v___y_186_);
return v_res_188_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableEqOffset___aux__1(lean_object* v_a_191_, lean_object* v_b_192_){
_start:
{
uint8_t v___x_193_; 
v___x_193_ = lean_int_dec_eq(v_a_191_, v_b_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableEqOffset___aux__1___boxed(lean_object* v_a_194_, lean_object* v_b_195_){
_start:
{
uint8_t v_res_196_; lean_object* v_r_197_; 
v_res_196_ = l_Std_Time_Second_instDecidableEqOffset___aux__1(v_a_194_, v_b_195_);
lean_dec(v_b_195_);
lean_dec(v_a_194_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableEqOffset(lean_object* v_a_198_, lean_object* v_b_199_){
_start:
{
uint8_t v___x_200_; 
v___x_200_ = lean_int_dec_eq(v_a_198_, v_b_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableEqOffset___boxed(lean_object* v_a_201_, lean_object* v_b_202_){
_start:
{
uint8_t v_res_203_; lean_object* v_r_204_; 
v_res_203_ = l_Std_Time_Second_instDecidableEqOffset(v_a_201_, v_b_202_);
lean_dec(v_b_202_);
lean_dec(v_a_201_);
v_r_204_ = lean_box(v_res_203_);
return v_r_204_;
}
}
static lean_object* _init_l_Std_Time_Second_instInhabitedOffset___aux__1___closed__0(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_unsigned_to_nat(1u);
v___x_206_ = l_Rat_instNatCast___lam__0(v___x_205_);
return v___x_206_;
}
}
static lean_object* _init_l_Std_Time_Second_instInhabitedOffset___aux__1___closed__1(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_obj_once(&l_Std_Time_Second_instInhabitedOffset___aux__1___closed__0, &l_Std_Time_Second_instInhabitedOffset___aux__1___closed__0_once, _init_l_Std_Time_Second_instInhabitedOffset___aux__1___closed__0);
v___x_208_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_207_);
return v___x_208_;
}
}
static lean_object* _init_l_Std_Time_Second_instInhabitedOffset___aux__1(void){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = lean_obj_once(&l_Std_Time_Second_instInhabitedOffset___aux__1___closed__1, &l_Std_Time_Second_instInhabitedOffset___aux__1___closed__1_once, _init_l_Std_Time_Second_instInhabitedOffset___aux__1___closed__1);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Second_instInhabitedOffset_spec__0(lean_object* v_a_210_){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_nat_to_int(v_a_210_);
v___x_212_ = l_Rat_ofInt(v___x_211_);
return v___x_212_;
}
}
static lean_object* _init_l_Std_Time_Second_instInhabitedOffset___closed__0(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_unsigned_to_nat(1u);
v___x_214_ = l_Nat_cast___at___00Std_Time_Second_instInhabitedOffset_spec__0(v___x_213_);
return v___x_214_;
}
}
static lean_object* _init_l_Std_Time_Second_instInhabitedOffset___closed__1(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_obj_once(&l_Std_Time_Second_instInhabitedOffset___closed__0, &l_Std_Time_Second_instInhabitedOffset___closed__0_once, _init_l_Std_Time_Second_instInhabitedOffset___closed__0);
v___x_216_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_215_);
return v___x_216_;
}
}
static lean_object* _init_l_Std_Time_Second_instInhabitedOffset(void){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = lean_obj_once(&l_Std_Time_Second_instInhabitedOffset___closed__1, &l_Std_Time_Second_instInhabitedOffset___closed__1_once, _init_l_Std_Time_Second_instInhabitedOffset___closed__1);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Second_instInhabitedOffset_spec__0_spec__0(lean_object* v_a_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = lean_nat_to_int(v_a_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instAddOffset___aux__1(lean_object* v_u1_220_, lean_object* v_u2_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = lean_int_add(v_u1_220_, v_u2_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instAddOffset___aux__1___boxed(lean_object* v_u1_223_, lean_object* v_u2_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Std_Time_Second_instAddOffset___aux__1(v_u1_223_, v_u2_224_);
lean_dec(v_u2_224_);
lean_dec(v_u1_223_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instSubOffset___aux__1(lean_object* v_u1_228_, lean_object* v_u2_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = lean_int_sub(v_u1_228_, v_u2_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instSubOffset___aux__1___boxed(lean_object* v_u1_231_, lean_object* v_u2_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Std_Time_Second_instSubOffset___aux__1(v_u1_231_, v_u2_232_);
lean_dec(v_u2_232_);
lean_dec(v_u1_231_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instNegOffset___aux__1(lean_object* v_x_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = lean_int_neg(v_x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instNegOffset___aux__1___boxed(lean_object* v_x_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Std_Time_Second_instNegOffset___aux__1(v_x_238_);
lean_dec(v_x_238_);
return v_res_239_;
}
}
static lean_object* _init_l_Std_Time_Second_instLEOffset(void){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = lean_box(0);
return v___x_242_;
}
}
static lean_object* _init_l_Std_Time_Second_instLTOffset(void){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = lean_box(0);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instToStringOffset___aux__1(lean_object* v_n_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Int_repr(v_n_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instToStringOffset___aux__1___boxed(lean_object* v_n_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Std_Time_Second_instToStringOffset___aux__1(v_n_246_);
lean_dec(v_n_246_);
return v_res_247_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLeOffset___aux__1(lean_object* v_x_249_, lean_object* v_y_250_){
_start:
{
uint8_t v___x_251_; 
v___x_251_ = lean_int_dec_le(v_x_249_, v_y_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLeOffset___aux__1___boxed(lean_object* v_x_252_, lean_object* v_y_253_){
_start:
{
uint8_t v_res_254_; lean_object* v_r_255_; 
v_res_254_ = l_Std_Time_Second_instDecidableLeOffset___aux__1(v_x_252_, v_y_253_);
lean_dec(v_y_253_);
lean_dec(v_x_252_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLeOffset(lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
uint8_t v___x_258_; 
v___x_258_ = lean_int_dec_le(v___y_256_, v___y_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLeOffset___boxed(lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
uint8_t v_res_261_; lean_object* v_r_262_; 
v_res_261_ = l_Std_Time_Second_instDecidableLeOffset(v___y_259_, v___y_260_);
lean_dec(v___y_260_);
lean_dec(v___y_259_);
v_r_262_ = lean_box(v_res_261_);
return v_r_262_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLtOffset___aux__1(lean_object* v_x_263_, lean_object* v_y_264_){
_start:
{
uint8_t v___x_265_; 
v___x_265_ = lean_int_dec_lt(v_x_263_, v_y_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLtOffset___aux__1___boxed(lean_object* v_x_266_, lean_object* v_y_267_){
_start:
{
uint8_t v_res_268_; lean_object* v_r_269_; 
v_res_268_ = l_Std_Time_Second_instDecidableLtOffset___aux__1(v_x_266_, v_y_267_);
lean_dec(v_y_267_);
lean_dec(v_x_266_);
v_r_269_ = lean_box(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLtOffset(lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
uint8_t v___x_272_; 
v___x_272_ = lean_int_dec_lt(v___y_270_, v___y_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLtOffset___boxed(lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
uint8_t v_res_275_; lean_object* v_r_276_; 
v_res_275_ = l_Std_Time_Second_instDecidableLtOffset(v___y_273_, v___y_274_);
lean_dec(v___y_274_);
lean_dec(v___y_273_);
v_r_276_ = lean_box(v_res_275_);
return v_r_276_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instOfNatOffset(lean_object* v_n_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = lean_nat_to_int(v_n_277_);
return v___x_278_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instOrdOffset___aux__1(lean_object* v_x_279_, lean_object* v_y_280_){
_start:
{
uint8_t v___x_281_; 
v___x_281_ = lean_int_dec_lt(v_x_279_, v_y_280_);
if (v___x_281_ == 0)
{
uint8_t v___x_282_; 
v___x_282_ = lean_int_dec_eq(v_x_279_, v_y_280_);
if (v___x_282_ == 0)
{
uint8_t v___x_283_; 
v___x_283_ = 2;
return v___x_283_;
}
else
{
uint8_t v___x_284_; 
v___x_284_ = 1;
return v___x_284_;
}
}
else
{
uint8_t v___x_285_; 
v___x_285_ = 0;
return v___x_285_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instOrdOffset___aux__1___boxed(lean_object* v_x_286_, lean_object* v_y_287_){
_start:
{
uint8_t v_res_288_; lean_object* v_r_289_; 
v_res_288_ = l_Std_Time_Second_instOrdOffset___aux__1(v_x_286_, v_y_287_);
lean_dec(v_y_287_);
lean_dec(v_x_286_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofNat(lean_object* v_data_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = lean_nat_to_int(v_data_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofInt(lean_object* v_data_294_){
_start:
{
lean_inc(v_data_294_);
return v_data_294_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofInt___boxed(lean_object* v_data_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Std_Time_Second_Offset_ofInt(v_data_295_);
lean_dec(v_data_295_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofInt___redArg(lean_object* v_data_297_){
_start:
{
lean_inc(v_data_297_);
return v_data_297_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofInt___redArg___boxed(lean_object* v_data_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Std_Time_Second_Ordinal_ofInt___redArg(v_data_298_);
lean_dec(v_data_298_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofInt(uint8_t v_leap_300_, lean_object* v_data_301_, lean_object* v_h_302_){
_start:
{
lean_inc(v_data_301_);
return v_data_301_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofInt___boxed(lean_object* v_leap_303_, lean_object* v_data_304_, lean_object* v_h_305_){
_start:
{
uint8_t v_leap_boxed_306_; lean_object* v_res_307_; 
v_leap_boxed_306_ = lean_unbox(v_leap_303_);
v_res_307_ = l_Std_Time_Second_Ordinal_ofInt(v_leap_boxed_306_, v_data_304_, v_h_305_);
lean_dec(v_data_304_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofNat___redArg(lean_object* v_data_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = lean_nat_to_int(v_data_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofNat(uint8_t v_leap_310_, lean_object* v_data_311_, lean_object* v_h_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = lean_nat_to_int(v_data_311_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofNat___boxed(lean_object* v_leap_314_, lean_object* v_data_315_, lean_object* v_h_316_){
_start:
{
uint8_t v_leap_boxed_317_; lean_object* v_res_318_; 
v_leap_boxed_317_ = lean_unbox(v_leap_314_);
v_res_318_ = l_Std_Time_Second_Ordinal_ofNat(v_leap_boxed_317_, v_data_315_, v_h_316_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofFin___redArg(lean_object* v_data_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = lean_nat_to_int(v_data_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofFin(uint8_t v_leap_321_, lean_object* v_data_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = lean_nat_to_int(v_data_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofFin___boxed(lean_object* v_leap_324_, lean_object* v_data_325_){
_start:
{
uint8_t v_leap_boxed_326_; lean_object* v_res_327_; 
v_leap_boxed_326_ = lean_unbox(v_leap_324_);
v_res_327_ = l_Std_Time_Second_Ordinal_ofFin(v_leap_boxed_326_, v_data_325_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_toOffset___redArg(lean_object* v_ordinal_328_){
_start:
{
lean_inc(v_ordinal_328_);
return v_ordinal_328_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_toOffset___redArg___boxed(lean_object* v_ordinal_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Std_Time_Second_Ordinal_toOffset___redArg(v_ordinal_329_);
lean_dec(v_ordinal_329_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_toOffset(uint8_t v_leap_331_, lean_object* v_ordinal_332_){
_start:
{
lean_inc(v_ordinal_332_);
return v_ordinal_332_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_toOffset___boxed(lean_object* v_leap_333_, lean_object* v_ordinal_334_){
_start:
{
uint8_t v_leap_boxed_335_; lean_object* v_res_336_; 
v_leap_boxed_335_ = lean_unbox(v_leap_333_);
v_res_336_ = l_Std_Time_Second_Ordinal_toOffset(v_leap_boxed_335_, v_ordinal_334_);
lean_dec(v_ordinal_334_);
return v_res_336_;
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
l_Std_Time_Second_instInhabitedOffset___aux__1 = _init_l_Std_Time_Second_instInhabitedOffset___aux__1();
lean_mark_persistent(l_Std_Time_Second_instInhabitedOffset___aux__1);
l_Std_Time_Second_instInhabitedOffset = _init_l_Std_Time_Second_instInhabitedOffset();
lean_mark_persistent(l_Std_Time_Second_instInhabitedOffset);
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
