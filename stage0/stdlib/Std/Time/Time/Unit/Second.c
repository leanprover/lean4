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
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_nonneg(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_neg___boxed(lean_object*);
lean_object* l_Int_sub___boxed(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Int_repr___boxed(lean_object*);
lean_object* l_Rat_instNatCast___lam__0(lean_object*);
lean_object* l_Std_Time_Internal_instInhabitedUnitVal_default(lean_object*);
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
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLeOrdinal___aux__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLeOrdinal___aux__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLeOrdinal___aux__1(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLeOrdinal___aux__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLeOrdinal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLeOrdinal___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLeOrdinal(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLeOrdinal___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLtOrdinal___aux__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLtOrdinal___aux__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLtOrdinal___aux__1(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLtOrdinal___aux__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLeOrdinal___aux__1___redArg(lean_object* v_x_66_, lean_object* v_y_67_){
_start:
{
lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_68_ = lean_int_sub(v_y_67_, v_x_66_);
v___x_69_ = lean_int_dec_nonneg(v___x_68_);
lean_dec(v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLeOrdinal___aux__1___redArg___boxed(lean_object* v_x_70_, lean_object* v_y_71_){
_start:
{
uint8_t v_res_72_; lean_object* v_r_73_; 
v_res_72_ = l_Std_Time_Second_instDecidableLeOrdinal___aux__1___redArg(v_x_70_, v_y_71_);
lean_dec(v_y_71_);
lean_dec(v_x_70_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLeOrdinal___aux__1(uint8_t v_leap_74_, lean_object* v_x_75_, lean_object* v_y_76_){
_start:
{
uint8_t v___x_77_; 
v___x_77_ = l_Std_Time_Second_instDecidableLeOrdinal___aux__1___redArg(v_x_75_, v_y_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLeOrdinal___aux__1___boxed(lean_object* v_leap_78_, lean_object* v_x_79_, lean_object* v_y_80_){
_start:
{
uint8_t v_leap_boxed_81_; uint8_t v_res_82_; lean_object* v_r_83_; 
v_leap_boxed_81_ = lean_unbox(v_leap_78_);
v_res_82_ = l_Std_Time_Second_instDecidableLeOrdinal___aux__1(v_leap_boxed_81_, v_x_79_, v_y_80_);
lean_dec(v_y_80_);
lean_dec(v_x_79_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLeOrdinal___redArg(lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
uint8_t v___x_86_; 
v___x_86_ = l_Std_Time_Second_instDecidableLeOrdinal___aux__1___redArg(v___y_84_, v___y_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLeOrdinal___redArg___boxed(lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_Std_Time_Second_instDecidableLeOrdinal___redArg(v___y_87_, v___y_88_);
lean_dec(v___y_88_);
lean_dec(v___y_87_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLeOrdinal(uint8_t v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
uint8_t v___x_94_; 
v___x_94_ = l_Std_Time_Second_instDecidableLeOrdinal___aux__1___redArg(v___y_92_, v___y_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLeOrdinal___boxed(lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
uint8_t v___y_19__boxed_98_; uint8_t v_res_99_; lean_object* v_r_100_; 
v___y_19__boxed_98_ = lean_unbox(v___y_95_);
v_res_99_ = l_Std_Time_Second_instDecidableLeOrdinal(v___y_19__boxed_98_, v___y_96_, v___y_97_);
lean_dec(v___y_97_);
lean_dec(v___y_96_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLtOrdinal___aux__1___redArg(lean_object* v_x_101_, lean_object* v_y_102_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_103_ = lean_obj_once(&l_Std_Time_Second_instOfNatOrdinal___closed__3, &l_Std_Time_Second_instOfNatOrdinal___closed__3_once, _init_l_Std_Time_Second_instOfNatOrdinal___closed__3);
v___x_104_ = lean_int_add(v_x_101_, v___x_103_);
v___x_105_ = lean_int_sub(v_y_102_, v___x_104_);
lean_dec(v___x_104_);
v___x_106_ = lean_int_dec_nonneg(v___x_105_);
lean_dec(v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLtOrdinal___aux__1___redArg___boxed(lean_object* v_x_107_, lean_object* v_y_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Std_Time_Second_instDecidableLtOrdinal___aux__1___redArg(v_x_107_, v_y_108_);
lean_dec(v_y_108_);
lean_dec(v_x_107_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLtOrdinal___aux__1(uint8_t v_leap_111_, lean_object* v_x_112_, lean_object* v_y_113_){
_start:
{
uint8_t v___x_114_; 
v___x_114_ = l_Std_Time_Second_instDecidableLtOrdinal___aux__1___redArg(v_x_112_, v_y_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLtOrdinal___aux__1___boxed(lean_object* v_leap_115_, lean_object* v_x_116_, lean_object* v_y_117_){
_start:
{
uint8_t v_leap_boxed_118_; uint8_t v_res_119_; lean_object* v_r_120_; 
v_leap_boxed_118_ = lean_unbox(v_leap_115_);
v_res_119_ = l_Std_Time_Second_instDecidableLtOrdinal___aux__1(v_leap_boxed_118_, v_x_116_, v_y_117_);
lean_dec(v_y_117_);
lean_dec(v_x_116_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLtOrdinal___redArg(lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
uint8_t v___x_123_; 
v___x_123_ = l_Std_Time_Second_instDecidableLtOrdinal___aux__1___redArg(v___y_121_, v___y_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLtOrdinal___redArg___boxed(lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
uint8_t v_res_126_; lean_object* v_r_127_; 
v_res_126_ = l_Std_Time_Second_instDecidableLtOrdinal___redArg(v___y_124_, v___y_125_);
lean_dec(v___y_125_);
lean_dec(v___y_124_);
v_r_127_ = lean_box(v_res_126_);
return v_r_127_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLtOrdinal(uint8_t v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
uint8_t v___x_131_; 
v___x_131_ = l_Std_Time_Second_instDecidableLtOrdinal___aux__1___redArg(v___y_129_, v___y_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLtOrdinal___boxed(lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
uint8_t v___y_19__boxed_135_; uint8_t v_res_136_; lean_object* v_r_137_; 
v___y_19__boxed_135_ = lean_unbox(v___y_132_);
v_res_136_ = l_Std_Time_Second_instDecidableLtOrdinal(v___y_19__boxed_135_, v___y_133_, v___y_134_);
lean_dec(v___y_134_);
lean_dec(v___y_133_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableEqOrdinal___aux__1___redArg(lean_object* v_x_138_, lean_object* v_x_139_){
_start:
{
uint8_t v___x_140_; 
v___x_140_ = lean_int_dec_eq(v_x_138_, v_x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableEqOrdinal___aux__1___redArg___boxed(lean_object* v_x_141_, lean_object* v_x_142_){
_start:
{
uint8_t v_res_143_; lean_object* v_r_144_; 
v_res_143_ = l_Std_Time_Second_instDecidableEqOrdinal___aux__1___redArg(v_x_141_, v_x_142_);
lean_dec(v_x_142_);
lean_dec(v_x_141_);
v_r_144_ = lean_box(v_res_143_);
return v_r_144_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableEqOrdinal___aux__1(uint8_t v_leap_145_, lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
uint8_t v___x_148_; 
v___x_148_ = lean_int_dec_eq(v_x_146_, v_x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableEqOrdinal___aux__1___boxed(lean_object* v_leap_149_, lean_object* v_x_150_, lean_object* v_x_151_){
_start:
{
uint8_t v_leap_boxed_152_; uint8_t v_res_153_; lean_object* v_r_154_; 
v_leap_boxed_152_ = lean_unbox(v_leap_149_);
v_res_153_ = l_Std_Time_Second_instDecidableEqOrdinal___aux__1(v_leap_boxed_152_, v_x_150_, v_x_151_);
lean_dec(v_x_151_);
lean_dec(v_x_150_);
v_r_154_ = lean_box(v_res_153_);
return v_r_154_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableEqOrdinal___redArg(lean_object* v_a_155_, lean_object* v_b_156_){
_start:
{
uint8_t v___x_157_; 
v___x_157_ = lean_int_dec_eq(v_a_155_, v_b_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableEqOrdinal___redArg___boxed(lean_object* v_a_158_, lean_object* v_b_159_){
_start:
{
uint8_t v_res_160_; lean_object* v_r_161_; 
v_res_160_ = l_Std_Time_Second_instDecidableEqOrdinal___redArg(v_a_158_, v_b_159_);
lean_dec(v_b_159_);
lean_dec(v_a_158_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableEqOrdinal(uint8_t v_leap_162_, lean_object* v_a_163_, lean_object* v_b_164_){
_start:
{
uint8_t v___x_165_; 
v___x_165_ = lean_int_dec_eq(v_a_163_, v_b_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableEqOrdinal___boxed(lean_object* v_leap_166_, lean_object* v_a_167_, lean_object* v_b_168_){
_start:
{
uint8_t v_leap_boxed_169_; uint8_t v_res_170_; lean_object* v_r_171_; 
v_leap_boxed_169_ = lean_unbox(v_leap_166_);
v_res_170_ = l_Std_Time_Second_instDecidableEqOrdinal(v_leap_boxed_169_, v_a_167_, v_b_168_);
lean_dec(v_b_168_);
lean_dec(v_a_167_);
v_r_171_ = lean_box(v_res_170_);
return v_r_171_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instOrdOrdinal___aux__1___redArg(lean_object* v_x_172_, lean_object* v_y_173_){
_start:
{
uint8_t v___x_174_; 
v___x_174_ = lean_int_dec_lt(v_x_172_, v_y_173_);
if (v___x_174_ == 0)
{
uint8_t v___x_175_; 
v___x_175_ = lean_int_dec_eq(v_x_172_, v_y_173_);
if (v___x_175_ == 0)
{
uint8_t v___x_176_; 
v___x_176_ = 2;
return v___x_176_;
}
else
{
uint8_t v___x_177_; 
v___x_177_ = 1;
return v___x_177_;
}
}
else
{
uint8_t v___x_178_; 
v___x_178_ = 0;
return v___x_178_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instOrdOrdinal___aux__1___redArg___boxed(lean_object* v_x_179_, lean_object* v_y_180_){
_start:
{
uint8_t v_res_181_; lean_object* v_r_182_; 
v_res_181_ = l_Std_Time_Second_instOrdOrdinal___aux__1___redArg(v_x_179_, v_y_180_);
lean_dec(v_y_180_);
lean_dec(v_x_179_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instOrdOrdinal___aux__1(uint8_t v_leap_183_, lean_object* v_x_184_, lean_object* v_y_185_){
_start:
{
uint8_t v___x_186_; 
v___x_186_ = lean_int_dec_lt(v_x_184_, v_y_185_);
if (v___x_186_ == 0)
{
uint8_t v___x_187_; 
v___x_187_ = lean_int_dec_eq(v_x_184_, v_y_185_);
if (v___x_187_ == 0)
{
uint8_t v___x_188_; 
v___x_188_ = 2;
return v___x_188_;
}
else
{
uint8_t v___x_189_; 
v___x_189_ = 1;
return v___x_189_;
}
}
else
{
uint8_t v___x_190_; 
v___x_190_ = 0;
return v___x_190_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instOrdOrdinal___aux__1___boxed(lean_object* v_leap_191_, lean_object* v_x_192_, lean_object* v_y_193_){
_start:
{
uint8_t v_leap_boxed_194_; uint8_t v_res_195_; lean_object* v_r_196_; 
v_leap_boxed_194_ = lean_unbox(v_leap_191_);
v_res_195_ = l_Std_Time_Second_instOrdOrdinal___aux__1(v_leap_boxed_194_, v_x_192_, v_y_193_);
lean_dec(v_y_193_);
lean_dec(v_x_192_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instOrdOrdinal(uint8_t v_leap_197_){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_box(v_leap_197_);
v___x_199_ = lean_alloc_closure((void*)(l_Std_Time_Second_instOrdOrdinal___aux__1___boxed), 3, 1);
lean_closure_set(v___x_199_, 0, v___x_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instOrdOrdinal___boxed(lean_object* v_leap_200_){
_start:
{
uint8_t v_leap_boxed_201_; lean_object* v_res_202_; 
v_leap_boxed_201_ = lean_unbox(v_leap_200_);
v_res_202_ = l_Std_Time_Second_instOrdOrdinal(v_leap_boxed_201_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instReprOffset___aux__1(lean_object* v_x_203_, lean_object* v_p_204_){
_start:
{
lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_205_ = lean_obj_once(&l_Std_Time_Second_instReprOrdinal___lam__0___closed__0, &l_Std_Time_Second_instReprOrdinal___lam__0___closed__0_once, _init_l_Std_Time_Second_instReprOrdinal___lam__0___closed__0);
v___x_206_ = lean_int_dec_lt(v_x_203_, v___x_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = l_Int_repr(v_x_203_);
v___x_208_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
return v___x_208_;
}
else
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_209_ = l_Int_repr(v_x_203_);
v___x_210_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
v___x_211_ = l_Repr_addAppParen(v___x_210_, v_p_204_);
return v___x_211_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instReprOffset___aux__1___boxed(lean_object* v_x_212_, lean_object* v_p_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Std_Time_Second_instReprOffset___aux__1(v_x_212_, v_p_213_);
lean_dec(v_p_213_);
lean_dec(v_x_212_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instReprOffset___lam__0(lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_217_ = lean_obj_once(&l_Std_Time_Second_instReprOrdinal___lam__0___closed__0, &l_Std_Time_Second_instReprOrdinal___lam__0___closed__0_once, _init_l_Std_Time_Second_instReprOrdinal___lam__0___closed__0);
v___x_218_ = lean_int_dec_lt(v___y_215_, v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = l_Int_repr(v___y_215_);
v___x_220_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
return v___x_220_;
}
else
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_221_ = l_Int_repr(v___y_215_);
v___x_222_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
v___x_223_ = l_Repr_addAppParen(v___x_222_, v___y_216_);
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instReprOffset___lam__0___boxed(lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Std_Time_Second_instReprOffset___lam__0(v___y_224_, v___y_225_);
lean_dec(v___y_225_);
lean_dec(v___y_224_);
return v_res_226_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableEqOffset___aux__1(lean_object* v_x_229_, lean_object* v_x_230_){
_start:
{
uint8_t v___x_231_; 
v___x_231_ = lean_int_dec_eq(v_x_229_, v_x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableEqOffset___aux__1___boxed(lean_object* v_x_232_, lean_object* v_x_233_){
_start:
{
uint8_t v_res_234_; lean_object* v_r_235_; 
v_res_234_ = l_Std_Time_Second_instDecidableEqOffset___aux__1(v_x_232_, v_x_233_);
lean_dec(v_x_233_);
lean_dec(v_x_232_);
v_r_235_ = lean_box(v_res_234_);
return v_r_235_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableEqOffset(lean_object* v_a_236_, lean_object* v_b_237_){
_start:
{
uint8_t v___x_238_; 
v___x_238_ = lean_int_dec_eq(v_a_236_, v_b_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableEqOffset___boxed(lean_object* v_a_239_, lean_object* v_b_240_){
_start:
{
uint8_t v_res_241_; lean_object* v_r_242_; 
v_res_241_ = l_Std_Time_Second_instDecidableEqOffset(v_a_239_, v_b_240_);
lean_dec(v_b_240_);
lean_dec(v_a_239_);
v_r_242_ = lean_box(v_res_241_);
return v_r_242_;
}
}
static lean_object* _init_l_Std_Time_Second_instInhabitedOffset___aux__1___closed__0(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_unsigned_to_nat(1u);
v___x_244_ = l_Rat_instNatCast___lam__0(v___x_243_);
return v___x_244_;
}
}
static lean_object* _init_l_Std_Time_Second_instInhabitedOffset___aux__1___closed__1(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_obj_once(&l_Std_Time_Second_instInhabitedOffset___aux__1___closed__0, &l_Std_Time_Second_instInhabitedOffset___aux__1___closed__0_once, _init_l_Std_Time_Second_instInhabitedOffset___aux__1___closed__0);
v___x_246_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_245_);
return v___x_246_;
}
}
static lean_object* _init_l_Std_Time_Second_instInhabitedOffset___aux__1(void){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = lean_obj_once(&l_Std_Time_Second_instInhabitedOffset___aux__1___closed__1, &l_Std_Time_Second_instInhabitedOffset___aux__1___closed__1_once, _init_l_Std_Time_Second_instInhabitedOffset___aux__1___closed__1);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Second_instInhabitedOffset_spec__0(lean_object* v_a_248_){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = lean_nat_to_int(v_a_248_);
v___x_250_ = l_Rat_ofInt(v___x_249_);
return v___x_250_;
}
}
static lean_object* _init_l_Std_Time_Second_instInhabitedOffset___closed__0(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_unsigned_to_nat(1u);
v___x_252_ = l_Nat_cast___at___00Std_Time_Second_instInhabitedOffset_spec__0(v___x_251_);
return v___x_252_;
}
}
static lean_object* _init_l_Std_Time_Second_instInhabitedOffset___closed__1(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_obj_once(&l_Std_Time_Second_instInhabitedOffset___closed__0, &l_Std_Time_Second_instInhabitedOffset___closed__0_once, _init_l_Std_Time_Second_instInhabitedOffset___closed__0);
v___x_254_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_253_);
return v___x_254_;
}
}
static lean_object* _init_l_Std_Time_Second_instInhabitedOffset(void){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = lean_obj_once(&l_Std_Time_Second_instInhabitedOffset___closed__1, &l_Std_Time_Second_instInhabitedOffset___closed__1_once, _init_l_Std_Time_Second_instInhabitedOffset___closed__1);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Second_instInhabitedOffset_spec__0_spec__0(lean_object* v_a_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = lean_nat_to_int(v_a_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instAddOffset___aux__1(lean_object* v_u1_258_, lean_object* v_u2_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = lean_int_add(v_u1_258_, v_u2_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instAddOffset___aux__1___boxed(lean_object* v_u1_261_, lean_object* v_u2_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Std_Time_Second_instAddOffset___aux__1(v_u1_261_, v_u2_262_);
lean_dec(v_u2_262_);
lean_dec(v_u1_261_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instSubOffset___aux__1(lean_object* v_u1_266_, lean_object* v_u2_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = lean_int_sub(v_u1_266_, v_u2_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instSubOffset___aux__1___boxed(lean_object* v_u1_269_, lean_object* v_u2_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Std_Time_Second_instSubOffset___aux__1(v_u1_269_, v_u2_270_);
lean_dec(v_u2_270_);
lean_dec(v_u1_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instNegOffset___aux__1(lean_object* v_x_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = lean_int_neg(v_x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instNegOffset___aux__1___boxed(lean_object* v_x_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Std_Time_Second_instNegOffset___aux__1(v_x_276_);
lean_dec(v_x_276_);
return v_res_277_;
}
}
static lean_object* _init_l_Std_Time_Second_instLEOffset(void){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = lean_box(0);
return v___x_280_;
}
}
static lean_object* _init_l_Std_Time_Second_instLTOffset(void){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = lean_box(0);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instToStringOffset___aux__1(lean_object* v_n_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Int_repr(v_n_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instToStringOffset___aux__1___boxed(lean_object* v_n_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Std_Time_Second_instToStringOffset___aux__1(v_n_284_);
lean_dec(v_n_284_);
return v_res_285_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLeOffset___aux__1(lean_object* v_x_287_, lean_object* v_y_288_){
_start:
{
lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_289_ = lean_int_sub(v_y_288_, v_x_287_);
v___x_290_ = lean_int_dec_nonneg(v___x_289_);
lean_dec(v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLeOffset___aux__1___boxed(lean_object* v_x_291_, lean_object* v_y_292_){
_start:
{
uint8_t v_res_293_; lean_object* v_r_294_; 
v_res_293_ = l_Std_Time_Second_instDecidableLeOffset___aux__1(v_x_291_, v_y_292_);
lean_dec(v_y_292_);
lean_dec(v_x_291_);
v_r_294_ = lean_box(v_res_293_);
return v_r_294_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLeOffset(lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
uint8_t v___x_297_; 
v___x_297_ = l_Std_Time_Second_instDecidableLeOffset___aux__1(v___y_295_, v___y_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLeOffset___boxed(lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
uint8_t v_res_300_; lean_object* v_r_301_; 
v_res_300_ = l_Std_Time_Second_instDecidableLeOffset(v___y_298_, v___y_299_);
lean_dec(v___y_299_);
lean_dec(v___y_298_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLtOffset___aux__1(lean_object* v_x_302_, lean_object* v_y_303_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_304_ = lean_obj_once(&l_Std_Time_Second_instOfNatOrdinal___closed__3, &l_Std_Time_Second_instOfNatOrdinal___closed__3_once, _init_l_Std_Time_Second_instOfNatOrdinal___closed__3);
v___x_305_ = lean_int_add(v_x_302_, v___x_304_);
v___x_306_ = lean_int_sub(v_y_303_, v___x_305_);
lean_dec(v___x_305_);
v___x_307_ = lean_int_dec_nonneg(v___x_306_);
lean_dec(v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLtOffset___aux__1___boxed(lean_object* v_x_308_, lean_object* v_y_309_){
_start:
{
uint8_t v_res_310_; lean_object* v_r_311_; 
v_res_310_ = l_Std_Time_Second_instDecidableLtOffset___aux__1(v_x_308_, v_y_309_);
lean_dec(v_y_309_);
lean_dec(v_x_308_);
v_r_311_ = lean_box(v_res_310_);
return v_r_311_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLtOffset(lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
uint8_t v___x_314_; 
v___x_314_ = l_Std_Time_Second_instDecidableLtOffset___aux__1(v___y_312_, v___y_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLtOffset___boxed(lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
uint8_t v_res_317_; lean_object* v_r_318_; 
v_res_317_ = l_Std_Time_Second_instDecidableLtOffset(v___y_315_, v___y_316_);
lean_dec(v___y_316_);
lean_dec(v___y_315_);
v_r_318_ = lean_box(v_res_317_);
return v_r_318_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instOfNatOffset(lean_object* v_n_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = lean_nat_to_int(v_n_319_);
return v___x_320_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instOrdOffset___aux__1(lean_object* v_x_321_, lean_object* v_y_322_){
_start:
{
uint8_t v___x_323_; 
v___x_323_ = lean_int_dec_lt(v_x_321_, v_y_322_);
if (v___x_323_ == 0)
{
uint8_t v___x_324_; 
v___x_324_ = lean_int_dec_eq(v_x_321_, v_y_322_);
if (v___x_324_ == 0)
{
uint8_t v___x_325_; 
v___x_325_ = 2;
return v___x_325_;
}
else
{
uint8_t v___x_326_; 
v___x_326_ = 1;
return v___x_326_;
}
}
else
{
uint8_t v___x_327_; 
v___x_327_ = 0;
return v___x_327_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instOrdOffset___aux__1___boxed(lean_object* v_x_328_, lean_object* v_y_329_){
_start:
{
uint8_t v_res_330_; lean_object* v_r_331_; 
v_res_330_ = l_Std_Time_Second_instOrdOffset___aux__1(v_x_328_, v_y_329_);
lean_dec(v_y_329_);
lean_dec(v_x_328_);
v_r_331_ = lean_box(v_res_330_);
return v_r_331_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofNat(lean_object* v_data_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = lean_nat_to_int(v_data_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofInt(lean_object* v_data_336_){
_start:
{
lean_inc(v_data_336_);
return v_data_336_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofInt___boxed(lean_object* v_data_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Std_Time_Second_Offset_ofInt(v_data_337_);
lean_dec(v_data_337_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofInt___redArg(lean_object* v_data_339_){
_start:
{
lean_inc(v_data_339_);
return v_data_339_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofInt___redArg___boxed(lean_object* v_data_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Std_Time_Second_Ordinal_ofInt___redArg(v_data_340_);
lean_dec(v_data_340_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofInt(uint8_t v_leap_342_, lean_object* v_data_343_, lean_object* v_h_344_){
_start:
{
lean_inc(v_data_343_);
return v_data_343_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofInt___boxed(lean_object* v_leap_345_, lean_object* v_data_346_, lean_object* v_h_347_){
_start:
{
uint8_t v_leap_boxed_348_; lean_object* v_res_349_; 
v_leap_boxed_348_ = lean_unbox(v_leap_345_);
v_res_349_ = l_Std_Time_Second_Ordinal_ofInt(v_leap_boxed_348_, v_data_346_, v_h_347_);
lean_dec(v_data_346_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofNat___redArg(lean_object* v_data_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = lean_nat_to_int(v_data_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofNat(uint8_t v_leap_352_, lean_object* v_data_353_, lean_object* v_h_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = lean_nat_to_int(v_data_353_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofNat___boxed(lean_object* v_leap_356_, lean_object* v_data_357_, lean_object* v_h_358_){
_start:
{
uint8_t v_leap_boxed_359_; lean_object* v_res_360_; 
v_leap_boxed_359_ = lean_unbox(v_leap_356_);
v_res_360_ = l_Std_Time_Second_Ordinal_ofNat(v_leap_boxed_359_, v_data_357_, v_h_358_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofFin___redArg(lean_object* v_data_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = lean_nat_to_int(v_data_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofFin(uint8_t v_leap_363_, lean_object* v_data_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = lean_nat_to_int(v_data_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofFin___boxed(lean_object* v_leap_366_, lean_object* v_data_367_){
_start:
{
uint8_t v_leap_boxed_368_; lean_object* v_res_369_; 
v_leap_boxed_368_ = lean_unbox(v_leap_366_);
v_res_369_ = l_Std_Time_Second_Ordinal_ofFin(v_leap_boxed_368_, v_data_367_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_toOffset___redArg(lean_object* v_ordinal_370_){
_start:
{
lean_inc(v_ordinal_370_);
return v_ordinal_370_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_toOffset___redArg___boxed(lean_object* v_ordinal_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Std_Time_Second_Ordinal_toOffset___redArg(v_ordinal_371_);
lean_dec(v_ordinal_371_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_toOffset(uint8_t v_leap_373_, lean_object* v_ordinal_374_){
_start:
{
lean_inc(v_ordinal_374_);
return v_ordinal_374_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_toOffset___boxed(lean_object* v_leap_375_, lean_object* v_ordinal_376_){
_start:
{
uint8_t v_leap_boxed_377_; lean_object* v_res_378_; 
v_leap_boxed_377_ = lean_unbox(v_leap_375_);
v_res_378_ = l_Std_Time_Second_Ordinal_toOffset(v_leap_boxed_377_, v_ordinal_376_);
lean_dec(v_ordinal_376_);
return v_res_378_;
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
