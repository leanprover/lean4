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
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
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
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_instOrdUnitVal___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_instInhabitedUnitVal_default(lean_object*);
lean_object* l_Std_Time_Internal_UnitVal_add___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_UnitVal_instToString___lam__0___boxed(lean_object*);
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
static const lean_string_object l_Std_Time_Second_instToStringOrdinal___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Time_Second_instToStringOrdinal___lam__0___closed__0 = (const lean_object*)&l_Std_Time_Second_instToStringOrdinal___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Second_instToStringOrdinal___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_instToStringOrdinal___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Time_Second_instToStringOrdinal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Second_instToStringOrdinal___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_closure_object l_Std_Time_Second_instToStringOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_UnitVal_instToString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Second_instToStringOffset___closed__0 = (const lean_object*)&l_Std_Time_Second_instToStringOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Second_instToStringOffset = (const lean_object*)&l_Std_Time_Second_instToStringOffset___closed__0_value;
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
LEAN_EXPORT lean_object* l_Std_Time_Second_instToStringOrdinal___lam__0(lean_object* v_r_32_){
_start:
{
lean_object* v_intZero_33_; uint8_t v_isNeg_34_; 
v_intZero_33_ = lean_obj_once(&l_Std_Time_Second_instReprOrdinal___lam__0___closed__0, &l_Std_Time_Second_instReprOrdinal___lam__0___closed__0_once, _init_l_Std_Time_Second_instReprOrdinal___lam__0___closed__0);
v_isNeg_34_ = lean_int_dec_lt(v_r_32_, v_intZero_33_);
if (v_isNeg_34_ == 0)
{
lean_object* v_a_35_; lean_object* v___x_36_; 
v_a_35_ = lean_nat_abs(v_r_32_);
v___x_36_ = l_Nat_reprFast(v_a_35_);
return v___x_36_;
}
else
{
lean_object* v_abs_37_; lean_object* v_one_38_; lean_object* v_a_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v_abs_37_ = lean_nat_abs(v_r_32_);
v_one_38_ = lean_unsigned_to_nat(1u);
v_a_39_ = lean_nat_sub(v_abs_37_, v_one_38_);
lean_dec(v_abs_37_);
v___x_40_ = ((lean_object*)(l_Std_Time_Second_instToStringOrdinal___lam__0___closed__0));
v___x_41_ = lean_nat_add(v_a_39_, v_one_38_);
lean_dec(v_a_39_);
v___x_42_ = l_Nat_reprFast(v___x_41_);
v___x_43_ = lean_string_append(v___x_40_, v___x_42_);
lean_dec_ref(v___x_42_);
return v___x_43_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instToStringOrdinal___lam__0___boxed(lean_object* v_r_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Std_Time_Second_instToStringOrdinal___lam__0(v_r_44_);
lean_dec(v_r_44_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instToStringOrdinal(uint8_t v_leap_47_){
_start:
{
lean_object* v___f_48_; 
v___f_48_ = ((lean_object*)(l_Std_Time_Second_instToStringOrdinal___closed__0));
return v___f_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instToStringOrdinal___boxed(lean_object* v_leap_49_){
_start:
{
uint8_t v_leap_boxed_50_; lean_object* v_res_51_; 
v_leap_boxed_50_ = lean_unbox(v_leap_49_);
v_res_51_ = l_Std_Time_Second_instToStringOrdinal(v_leap_boxed_50_);
return v_res_51_;
}
}
static lean_object* _init_l_Std_Time_Second_instOfNatOrdinal___closed__0(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_unsigned_to_nat(59u);
v___x_53_ = lean_nat_to_int(v___x_52_);
return v___x_53_;
}
}
static lean_object* _init_l_Std_Time_Second_instOfNatOrdinal___closed__1(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = lean_obj_once(&l_Std_Time_Second_instOfNatOrdinal___closed__0, &l_Std_Time_Second_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Second_instOfNatOrdinal___closed__0);
v___x_55_ = lean_obj_once(&l_Std_Time_Second_instReprOrdinal___lam__0___closed__0, &l_Std_Time_Second_instReprOrdinal___lam__0___closed__0_once, _init_l_Std_Time_Second_instReprOrdinal___lam__0___closed__0);
v___x_56_ = lean_int_add(v___x_55_, v___x_54_);
return v___x_56_;
}
}
static lean_object* _init_l_Std_Time_Second_instOfNatOrdinal___closed__2(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_57_ = lean_obj_once(&l_Std_Time_Second_instReprOrdinal___lam__0___closed__0, &l_Std_Time_Second_instReprOrdinal___lam__0___closed__0_once, _init_l_Std_Time_Second_instReprOrdinal___lam__0___closed__0);
v___x_58_ = lean_obj_once(&l_Std_Time_Second_instOfNatOrdinal___closed__1, &l_Std_Time_Second_instOfNatOrdinal___closed__1_once, _init_l_Std_Time_Second_instOfNatOrdinal___closed__1);
v___x_59_ = lean_int_sub(v___x_58_, v___x_57_);
return v___x_59_;
}
}
static lean_object* _init_l_Std_Time_Second_instOfNatOrdinal___closed__3(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_unsigned_to_nat(1u);
v___x_61_ = lean_nat_to_int(v___x_60_);
return v___x_61_;
}
}
static lean_object* _init_l_Std_Time_Second_instOfNatOrdinal___closed__4(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v_range_64_; 
v___x_62_ = lean_obj_once(&l_Std_Time_Second_instOfNatOrdinal___closed__3, &l_Std_Time_Second_instOfNatOrdinal___closed__3_once, _init_l_Std_Time_Second_instOfNatOrdinal___closed__3);
v___x_63_ = lean_obj_once(&l_Std_Time_Second_instOfNatOrdinal___closed__2, &l_Std_Time_Second_instOfNatOrdinal___closed__2_once, _init_l_Std_Time_Second_instOfNatOrdinal___closed__2);
v_range_64_ = lean_int_add(v___x_63_, v___x_62_);
return v_range_64_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instOfNatOrdinal(uint8_t v_leap_65_, lean_object* v_n_66_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_obj_once(&l_Std_Time_Second_instReprOrdinal___lam__0___closed__0, &l_Std_Time_Second_instReprOrdinal___lam__0___closed__0_once, _init_l_Std_Time_Second_instReprOrdinal___lam__0___closed__0);
v___x_68_ = lean_unsigned_to_nat(59u);
if (v_leap_65_ == 0)
{
lean_object* v_inst_69_; 
v_inst_69_ = l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast(v___x_67_, v_n_66_, v___x_68_);
return v_inst_69_;
}
else
{
lean_object* v___x_70_; lean_object* v_range_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_70_ = lean_nat_to_int(v_n_66_);
v_range_71_ = lean_obj_once(&l_Std_Time_Second_instOfNatOrdinal___closed__4, &l_Std_Time_Second_instOfNatOrdinal___closed__4_once, _init_l_Std_Time_Second_instOfNatOrdinal___closed__4);
v___x_72_ = lean_int_sub(v___x_70_, v___x_67_);
lean_dec(v___x_70_);
v___x_73_ = lean_int_emod(v___x_72_, v_range_71_);
lean_dec(v___x_72_);
v___x_74_ = lean_int_add(v___x_73_, v_range_71_);
lean_dec(v___x_73_);
v___x_75_ = lean_int_emod(v___x_74_, v_range_71_);
lean_dec(v___x_74_);
v___x_76_ = lean_int_add(v___x_75_, v___x_67_);
lean_dec(v___x_75_);
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instOfNatOrdinal___boxed(lean_object* v_leap_77_, lean_object* v_n_78_){
_start:
{
uint8_t v_leap_boxed_79_; lean_object* v_res_80_; 
v_leap_boxed_79_ = lean_unbox(v_leap_77_);
v_res_80_ = l_Std_Time_Second_instOfNatOrdinal(v_leap_boxed_79_, v_n_78_);
return v_res_80_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLeOrdinal___redArg(lean_object* v_x_81_, lean_object* v_y_82_){
_start:
{
uint8_t v___x_83_; 
v___x_83_ = lean_int_dec_le(v_x_81_, v_y_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLeOrdinal___redArg___boxed(lean_object* v_x_84_, lean_object* v_y_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l_Std_Time_Second_instDecidableLeOrdinal___redArg(v_x_84_, v_y_85_);
lean_dec(v_y_85_);
lean_dec(v_x_84_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLeOrdinal(uint8_t v_leap_88_, lean_object* v_x_89_, lean_object* v_y_90_){
_start:
{
uint8_t v___x_91_; 
v___x_91_ = lean_int_dec_le(v_x_89_, v_y_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLeOrdinal___boxed(lean_object* v_leap_92_, lean_object* v_x_93_, lean_object* v_y_94_){
_start:
{
uint8_t v_leap_boxed_95_; uint8_t v_res_96_; lean_object* v_r_97_; 
v_leap_boxed_95_ = lean_unbox(v_leap_92_);
v_res_96_ = l_Std_Time_Second_instDecidableLeOrdinal(v_leap_boxed_95_, v_x_93_, v_y_94_);
lean_dec(v_y_94_);
lean_dec(v_x_93_);
v_r_97_ = lean_box(v_res_96_);
return v_r_97_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLtOrdinal___redArg(lean_object* v_x_98_, lean_object* v_y_99_){
_start:
{
uint8_t v___x_100_; 
v___x_100_ = lean_int_dec_lt(v_x_98_, v_y_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLtOrdinal___redArg___boxed(lean_object* v_x_101_, lean_object* v_y_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = l_Std_Time_Second_instDecidableLtOrdinal___redArg(v_x_101_, v_y_102_);
lean_dec(v_y_102_);
lean_dec(v_x_101_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLtOrdinal(uint8_t v_leap_105_, lean_object* v_x_106_, lean_object* v_y_107_){
_start:
{
uint8_t v___x_108_; 
v___x_108_ = lean_int_dec_lt(v_x_106_, v_y_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLtOrdinal___boxed(lean_object* v_leap_109_, lean_object* v_x_110_, lean_object* v_y_111_){
_start:
{
uint8_t v_leap_boxed_112_; uint8_t v_res_113_; lean_object* v_r_114_; 
v_leap_boxed_112_ = lean_unbox(v_leap_109_);
v_res_113_ = l_Std_Time_Second_instDecidableLtOrdinal(v_leap_boxed_112_, v_x_110_, v_y_111_);
lean_dec(v_y_111_);
lean_dec(v_x_110_);
v_r_114_ = lean_box(v_res_113_);
return v_r_114_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableEqOrdinal___redArg(lean_object* v_a_115_, lean_object* v_b_116_){
_start:
{
uint8_t v___x_117_; 
v___x_117_ = lean_int_dec_eq(v_a_115_, v_b_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableEqOrdinal___redArg___boxed(lean_object* v_a_118_, lean_object* v_b_119_){
_start:
{
uint8_t v_res_120_; lean_object* v_r_121_; 
v_res_120_ = l_Std_Time_Second_instDecidableEqOrdinal___redArg(v_a_118_, v_b_119_);
lean_dec(v_b_119_);
lean_dec(v_a_118_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableEqOrdinal(uint8_t v_leap_122_, lean_object* v_a_123_, lean_object* v_b_124_){
_start:
{
uint8_t v___x_125_; 
v___x_125_ = lean_int_dec_eq(v_a_123_, v_b_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableEqOrdinal___boxed(lean_object* v_leap_126_, lean_object* v_a_127_, lean_object* v_b_128_){
_start:
{
uint8_t v_leap_boxed_129_; uint8_t v_res_130_; lean_object* v_r_131_; 
v_leap_boxed_129_ = lean_unbox(v_leap_126_);
v_res_130_ = l_Std_Time_Second_instDecidableEqOrdinal(v_leap_boxed_129_, v_a_127_, v_b_128_);
lean_dec(v_b_128_);
lean_dec(v_a_127_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instOrdOrdinal(uint8_t v_leap_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = ((lean_object*)(l_Std_Time_Second_instOrdOrdinal___closed__2));
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instOrdOrdinal___boxed(lean_object* v_leap_139_){
_start:
{
uint8_t v_leap_boxed_140_; lean_object* v_res_141_; 
v_leap_boxed_140_ = lean_unbox(v_leap_139_);
v_res_141_ = l_Std_Time_Second_instOrdOrdinal(v_leap_boxed_140_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Second_instReprOffset_spec__0_spec__0(lean_object* v_a_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = lean_nat_to_int(v_a_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Second_instReprOffset_spec__0(lean_object* v_a_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_nat_to_int(v_a_146_);
v___x_148_ = l_Rat_ofInt(v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableEqOffset(lean_object* v_a_149_, lean_object* v_b_150_){
_start:
{
uint8_t v___x_151_; 
v___x_151_ = lean_int_dec_eq(v_a_149_, v_b_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableEqOffset___boxed(lean_object* v_a_152_, lean_object* v_b_153_){
_start:
{
uint8_t v_res_154_; lean_object* v_r_155_; 
v_res_154_ = l_Std_Time_Second_instDecidableEqOffset(v_a_152_, v_b_153_);
lean_dec(v_b_153_);
lean_dec(v_a_152_);
v_r_155_ = lean_box(v_res_154_);
return v_r_155_;
}
}
static lean_object* _init_l_Std_Time_Second_instInhabitedOffset___closed__0(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_unsigned_to_nat(1u);
v___x_157_ = l_Nat_cast___at___00Std_Time_Second_instReprOffset_spec__0(v___x_156_);
return v___x_157_;
}
}
static lean_object* _init_l_Std_Time_Second_instInhabitedOffset___closed__1(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = lean_obj_once(&l_Std_Time_Second_instInhabitedOffset___closed__0, &l_Std_Time_Second_instInhabitedOffset___closed__0_once, _init_l_Std_Time_Second_instInhabitedOffset___closed__0);
v___x_159_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_158_);
return v___x_159_;
}
}
static lean_object* _init_l_Std_Time_Second_instInhabitedOffset(void){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lean_obj_once(&l_Std_Time_Second_instInhabitedOffset___closed__1, &l_Std_Time_Second_instInhabitedOffset___closed__1_once, _init_l_Std_Time_Second_instInhabitedOffset___closed__1);
return v___x_160_;
}
}
static lean_object* _init_l_Std_Time_Second_instAddOffset___closed__0(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_obj_once(&l_Std_Time_Second_instInhabitedOffset___closed__0, &l_Std_Time_Second_instInhabitedOffset___closed__0_once, _init_l_Std_Time_Second_instInhabitedOffset___closed__0);
v___x_162_ = lean_alloc_closure((void*)(l_Std_Time_Internal_UnitVal_add___boxed), 3, 1);
lean_closure_set(v___x_162_, 0, v___x_161_);
return v___x_162_;
}
}
static lean_object* _init_l_Std_Time_Second_instAddOffset(void){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = lean_obj_once(&l_Std_Time_Second_instAddOffset___closed__0, &l_Std_Time_Second_instAddOffset___closed__0_once, _init_l_Std_Time_Second_instAddOffset___closed__0);
return v___x_163_;
}
}
static lean_object* _init_l_Std_Time_Second_instSubOffset___closed__0(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_obj_once(&l_Std_Time_Second_instInhabitedOffset___closed__0, &l_Std_Time_Second_instInhabitedOffset___closed__0_once, _init_l_Std_Time_Second_instInhabitedOffset___closed__0);
v___x_165_ = lean_alloc_closure((void*)(l_Std_Time_Internal_UnitVal_sub___boxed), 3, 1);
lean_closure_set(v___x_165_, 0, v___x_164_);
return v___x_165_;
}
}
static lean_object* _init_l_Std_Time_Second_instSubOffset(void){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_obj_once(&l_Std_Time_Second_instSubOffset___closed__0, &l_Std_Time_Second_instSubOffset___closed__0_once, _init_l_Std_Time_Second_instSubOffset___closed__0);
return v___x_166_;
}
}
static lean_object* _init_l_Std_Time_Second_instLEOffset(void){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = lean_box(0);
return v___x_169_;
}
}
static lean_object* _init_l_Std_Time_Second_instLTOffset(void){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = lean_box(0);
return v___x_170_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLeOffset(lean_object* v_x_173_, lean_object* v_y_174_){
_start:
{
uint8_t v___x_175_; 
v___x_175_ = lean_int_dec_le(v_x_173_, v_y_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLeOffset___boxed(lean_object* v_x_176_, lean_object* v_y_177_){
_start:
{
uint8_t v_res_178_; lean_object* v_r_179_; 
v_res_178_ = l_Std_Time_Second_instDecidableLeOffset(v_x_176_, v_y_177_);
lean_dec(v_y_177_);
lean_dec(v_x_176_);
v_r_179_ = lean_box(v_res_178_);
return v_r_179_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Second_instDecidableLtOffset(lean_object* v_x_180_, lean_object* v_y_181_){
_start:
{
uint8_t v___x_182_; 
v___x_182_ = lean_int_dec_lt(v_x_180_, v_y_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instDecidableLtOffset___boxed(lean_object* v_x_183_, lean_object* v_y_184_){
_start:
{
uint8_t v_res_185_; lean_object* v_r_186_; 
v_res_185_ = l_Std_Time_Second_instDecidableLtOffset(v_x_183_, v_y_184_);
lean_dec(v_y_184_);
lean_dec(v_x_183_);
v_r_186_ = lean_box(v_res_185_);
return v_r_186_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_instOfNatOffset(lean_object* v_n_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = lean_nat_to_int(v_n_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofNat(lean_object* v_data_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_nat_to_int(v_data_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofInt(lean_object* v_data_193_){
_start:
{
lean_inc(v_data_193_);
return v_data_193_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofInt___boxed(lean_object* v_data_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Std_Time_Second_Offset_ofInt(v_data_194_);
lean_dec(v_data_194_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofInt___redArg(lean_object* v_data_196_){
_start:
{
lean_inc(v_data_196_);
return v_data_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofInt___redArg___boxed(lean_object* v_data_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Std_Time_Second_Ordinal_ofInt___redArg(v_data_197_);
lean_dec(v_data_197_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofInt(uint8_t v_leap_199_, lean_object* v_data_200_, lean_object* v_h_201_){
_start:
{
lean_inc(v_data_200_);
return v_data_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofInt___boxed(lean_object* v_leap_202_, lean_object* v_data_203_, lean_object* v_h_204_){
_start:
{
uint8_t v_leap_boxed_205_; lean_object* v_res_206_; 
v_leap_boxed_205_ = lean_unbox(v_leap_202_);
v_res_206_ = l_Std_Time_Second_Ordinal_ofInt(v_leap_boxed_205_, v_data_203_, v_h_204_);
lean_dec(v_data_203_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofNat___redArg(lean_object* v_data_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = lean_nat_to_int(v_data_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofNat(uint8_t v_leap_209_, lean_object* v_data_210_, lean_object* v_h_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = lean_nat_to_int(v_data_210_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofNat___boxed(lean_object* v_leap_213_, lean_object* v_data_214_, lean_object* v_h_215_){
_start:
{
uint8_t v_leap_boxed_216_; lean_object* v_res_217_; 
v_leap_boxed_216_ = lean_unbox(v_leap_213_);
v_res_217_ = l_Std_Time_Second_Ordinal_ofNat(v_leap_boxed_216_, v_data_214_, v_h_215_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofFin___redArg(lean_object* v_data_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = lean_nat_to_int(v_data_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofFin(uint8_t v_leap_220_, lean_object* v_data_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = lean_nat_to_int(v_data_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_ofFin___boxed(lean_object* v_leap_223_, lean_object* v_data_224_){
_start:
{
uint8_t v_leap_boxed_225_; lean_object* v_res_226_; 
v_leap_boxed_225_ = lean_unbox(v_leap_223_);
v_res_226_ = l_Std_Time_Second_Ordinal_ofFin(v_leap_boxed_225_, v_data_224_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_toOffset___redArg(lean_object* v_ordinal_227_){
_start:
{
lean_inc(v_ordinal_227_);
return v_ordinal_227_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_toOffset___redArg___boxed(lean_object* v_ordinal_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Std_Time_Second_Ordinal_toOffset___redArg(v_ordinal_228_);
lean_dec(v_ordinal_228_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_toOffset(uint8_t v_leap_230_, lean_object* v_ordinal_231_){
_start:
{
lean_inc(v_ordinal_231_);
return v_ordinal_231_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Ordinal_toOffset___boxed(lean_object* v_leap_232_, lean_object* v_ordinal_233_){
_start:
{
uint8_t v_leap_boxed_234_; lean_object* v_res_235_; 
v_leap_boxed_234_ = lean_unbox(v_leap_232_);
v_res_235_ = l_Std_Time_Second_Ordinal_toOffset(v_leap_boxed_234_, v_ordinal_233_);
lean_dec(v_ordinal_233_);
return v_res_235_;
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
