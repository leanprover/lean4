// Lean compiler output
// Module: Std.Time.Time.Unit.Millisecond
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
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_nonneg(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_instInhabitedUnitVal_default(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Int_neg___boxed(lean_object*);
lean_object* l_Int_sub___boxed(lean_object*, lean_object*);
lean_object* l_Rat_instNatCast___lam__0(lean_object*);
lean_object* l_Int_add___boxed(lean_object*, lean_object*);
lean_object* l_Int_repr___boxed(lean_object*);
lean_object* lean_int_neg(lean_object*);
static lean_once_cell_t l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instReprOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instReprOrdinal___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instReprOrdinal___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instReprOrdinal___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Millisecond_instReprOrdinal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Millisecond_instReprOrdinal___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Millisecond_instReprOrdinal___closed__0 = (const lean_object*)&l_Std_Time_Millisecond_instReprOrdinal___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Millisecond_instReprOrdinal = (const lean_object*)&l_Std_Time_Millisecond_instReprOrdinal___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Millisecond_instDecidableEqOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instDecidableEqOrdinal___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Millisecond_instDecidableEqOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instDecidableEqOrdinal___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instLEOrdinal;
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instLTOrdinal;
static lean_once_cell_t l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__0;
static lean_once_cell_t l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__1;
static lean_once_cell_t l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__2;
static lean_once_cell_t l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__3;
static lean_once_cell_t l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4;
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instOfNatOrdinal___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instOfNatOrdinal(lean_object*);
static lean_once_cell_t l_Std_Time_Millisecond_instInhabitedOrdinal___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Millisecond_instInhabitedOrdinal___closed__0;
static lean_once_cell_t l_Std_Time_Millisecond_instInhabitedOrdinal___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Millisecond_instInhabitedOrdinal___closed__1;
static lean_once_cell_t l_Std_Time_Millisecond_instInhabitedOrdinal___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Millisecond_instInhabitedOrdinal___closed__2;
static lean_once_cell_t l_Std_Time_Millisecond_instInhabitedOrdinal___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Millisecond_instInhabitedOrdinal___closed__3;
static lean_once_cell_t l_Std_Time_Millisecond_instInhabitedOrdinal___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Millisecond_instInhabitedOrdinal___closed__4;
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instInhabitedOrdinal;
LEAN_EXPORT uint8_t l_Std_Time_Millisecond_instDecidableLeOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instDecidableLeOrdinal___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Millisecond_instDecidableLeOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instDecidableLeOrdinal___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Millisecond_instDecidableLtOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instDecidableLtOrdinal___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Millisecond_instDecidableLtOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instDecidableLtOrdinal___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Millisecond_instOrdOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instOrdOrdinal___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Millisecond_instOrdOrdinal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Millisecond_instOrdOrdinal___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Millisecond_instOrdOrdinal___closed__0 = (const lean_object*)&l_Std_Time_Millisecond_instOrdOrdinal___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Millisecond_instOrdOrdinal = (const lean_object*)&l_Std_Time_Millisecond_instOrdOrdinal___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instReprOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instReprOffset___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT const lean_object* l_Std_Time_Millisecond_instReprOffset = (const lean_object*)&l_Std_Time_Millisecond_instReprOrdinal___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Millisecond_instDecidableEqOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instDecidableEqOffset___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Millisecond_instDecidableEqOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instDecidableEqOffset___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__0;
static lean_once_cell_t l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__1;
static lean_once_cell_t l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__2;
static lean_once_cell_t l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instInhabitedOffset___aux__1;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Millisecond_instInhabitedOffset_spec__0(lean_object*);
static lean_once_cell_t l_Std_Time_Millisecond_instInhabitedOffset___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Millisecond_instInhabitedOffset___closed__0;
static lean_once_cell_t l_Std_Time_Millisecond_instInhabitedOffset___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Millisecond_instInhabitedOffset___closed__1;
static lean_once_cell_t l_Std_Time_Millisecond_instInhabitedOffset___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Millisecond_instInhabitedOffset___closed__2;
static lean_once_cell_t l_Std_Time_Millisecond_instInhabitedOffset___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Millisecond_instInhabitedOffset___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instInhabitedOffset;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Millisecond_instInhabitedOffset_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instAddOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instAddOffset___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Millisecond_instAddOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Millisecond_instAddOffset___closed__0 = (const lean_object*)&l_Std_Time_Millisecond_instAddOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Millisecond_instAddOffset = (const lean_object*)&l_Std_Time_Millisecond_instAddOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instSubOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instSubOffset___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Millisecond_instSubOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Millisecond_instSubOffset___closed__0 = (const lean_object*)&l_Std_Time_Millisecond_instSubOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Millisecond_instSubOffset = (const lean_object*)&l_Std_Time_Millisecond_instSubOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instNegOffset___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instNegOffset___aux__1___boxed(lean_object*);
static const lean_closure_object l_Std_Time_Millisecond_instNegOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Millisecond_instNegOffset___closed__0 = (const lean_object*)&l_Std_Time_Millisecond_instNegOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Millisecond_instNegOffset = (const lean_object*)&l_Std_Time_Millisecond_instNegOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instLEOffset;
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instLTOffset;
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instToStringOffset___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instToStringOffset___aux__1___boxed(lean_object*);
static const lean_closure_object l_Std_Time_Millisecond_instToStringOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_repr___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Millisecond_instToStringOffset___closed__0 = (const lean_object*)&l_Std_Time_Millisecond_instToStringOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Millisecond_instToStringOffset = (const lean_object*)&l_Std_Time_Millisecond_instToStringOffset___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Millisecond_instDecidableLeOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instDecidableLeOffset___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Millisecond_instDecidableLeOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instDecidableLeOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Millisecond_instDecidableLtOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instDecidableLtOffset___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Millisecond_instDecidableLtOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instDecidableLtOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instOfNatOffset(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Millisecond_instOrdOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instOrdOffset___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Millisecond_instOrdOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Millisecond_instOrdOffset___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Millisecond_instOrdOffset___closed__0 = (const lean_object*)&l_Std_Time_Millisecond_instOrdOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Millisecond_instOrdOffset = (const lean_object*)&l_Std_Time_Millisecond_instOrdOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofInt(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofInt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Ordinal_ofInt___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Ordinal_ofInt___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Ordinal_ofInt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Ordinal_ofInt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Ordinal_ofNat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Ordinal_ofNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Ordinal_ofFin(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Ordinal_toOffset(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Ordinal_toOffset___boxed(lean_object*);
static lean_object* _init_l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instReprOrdinal___aux__1(lean_object* v_n_3_, lean_object* v_a_4_){
_start:
{
lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_5_ = lean_obj_once(&l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0);
v___x_6_ = lean_int_dec_lt(v_n_3_, v___x_5_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = l_Int_repr(v_n_3_);
v___x_8_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
return v___x_8_;
}
else
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_9_ = l_Int_repr(v_n_3_);
v___x_10_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
v___x_11_ = l_Repr_addAppParen(v___x_10_, v_a_4_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instReprOrdinal___aux__1___boxed(lean_object* v_n_12_, lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_Time_Millisecond_instReprOrdinal___aux__1(v_n_12_, v_a_13_);
lean_dec(v_a_13_);
lean_dec(v_n_12_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instReprOrdinal___lam__0(lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
lean_object* v___x_17_; uint8_t v___x_18_; 
v___x_17_ = lean_obj_once(&l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0);
v___x_18_ = lean_int_dec_lt(v___y_15_, v___x_17_);
if (v___x_18_ == 0)
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = l_Int_repr(v___y_15_);
v___x_20_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_20_, 0, v___x_19_);
return v___x_20_;
}
else
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_21_ = l_Int_repr(v___y_15_);
v___x_22_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_22_, 0, v___x_21_);
v___x_23_ = l_Repr_addAppParen(v___x_22_, v___y_16_);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instReprOrdinal___lam__0___boxed(lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Std_Time_Millisecond_instReprOrdinal___lam__0(v___y_24_, v___y_25_);
lean_dec(v___y_25_);
lean_dec(v___y_24_);
return v_res_26_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Millisecond_instDecidableEqOrdinal___aux__1(lean_object* v_x_29_, lean_object* v_x_30_){
_start:
{
uint8_t v___x_31_; 
v___x_31_ = lean_int_dec_eq(v_x_29_, v_x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instDecidableEqOrdinal___aux__1___boxed(lean_object* v_x_32_, lean_object* v_x_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l_Std_Time_Millisecond_instDecidableEqOrdinal___aux__1(v_x_32_, v_x_33_);
lean_dec(v_x_33_);
lean_dec(v_x_32_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Millisecond_instDecidableEqOrdinal(lean_object* v_a_36_, lean_object* v_b_37_){
_start:
{
uint8_t v___x_38_; 
v___x_38_ = lean_int_dec_eq(v_a_36_, v_b_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instDecidableEqOrdinal___boxed(lean_object* v_a_39_, lean_object* v_b_40_){
_start:
{
uint8_t v_res_41_; lean_object* v_r_42_; 
v_res_41_ = l_Std_Time_Millisecond_instDecidableEqOrdinal(v_a_39_, v_b_40_);
lean_dec(v_b_40_);
lean_dec(v_a_39_);
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_instLEOrdinal(void){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_box(0);
return v___x_43_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_instLTOrdinal(void){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_box(0);
return v___x_44_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__0(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_unsigned_to_nat(999u);
v___x_46_ = lean_nat_to_int(v___x_45_);
return v___x_46_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__1(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_47_ = lean_obj_once(&l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__0);
v___x_48_ = lean_obj_once(&l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0);
v___x_49_ = lean_int_add(v___x_48_, v___x_47_);
return v___x_49_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__2(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = lean_obj_once(&l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0);
v___x_51_ = lean_obj_once(&l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__1, &l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__1_once, _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__1);
v___x_52_ = lean_int_sub(v___x_51_, v___x_50_);
return v___x_52_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__3(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_unsigned_to_nat(1u);
v___x_54_ = lean_nat_to_int(v___x_53_);
return v___x_54_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v_range_57_; 
v___x_55_ = lean_obj_once(&l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__3);
v___x_56_ = lean_obj_once(&l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__2, &l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__2_once, _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__2);
v_range_57_ = lean_int_add(v___x_56_, v___x_55_);
return v_range_57_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instOfNatOrdinal___aux__1(lean_object* v_n_58_){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v_range_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_59_ = lean_obj_once(&l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0);
v___x_60_ = lean_nat_to_int(v_n_58_);
v_range_61_ = lean_obj_once(&l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4);
v___x_62_ = lean_int_sub(v___x_60_, v___x_59_);
lean_dec(v___x_60_);
v___x_63_ = lean_int_emod(v___x_62_, v_range_61_);
lean_dec(v___x_62_);
v___x_64_ = lean_int_add(v___x_63_, v_range_61_);
lean_dec(v___x_63_);
v___x_65_ = lean_int_emod(v___x_64_, v_range_61_);
lean_dec(v___x_64_);
v___x_66_ = lean_int_add(v___x_65_, v___x_59_);
lean_dec(v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instOfNatOrdinal(lean_object* v_n_67_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v_range_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_68_ = lean_obj_once(&l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0);
v___x_69_ = lean_nat_to_int(v_n_67_);
v_range_70_ = lean_obj_once(&l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4);
v___x_71_ = lean_int_sub(v___x_69_, v___x_68_);
lean_dec(v___x_69_);
v___x_72_ = lean_int_emod(v___x_71_, v_range_70_);
lean_dec(v___x_71_);
v___x_73_ = lean_int_add(v___x_72_, v_range_70_);
lean_dec(v___x_72_);
v___x_74_ = lean_int_emod(v___x_73_, v_range_70_);
lean_dec(v___x_73_);
v___x_75_ = lean_int_add(v___x_74_, v___x_68_);
lean_dec(v___x_74_);
return v___x_75_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_instInhabitedOrdinal___closed__0(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = lean_obj_once(&l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0);
v___x_77_ = lean_int_sub(v___x_76_, v___x_76_);
return v___x_77_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_instInhabitedOrdinal___closed__1(void){
_start:
{
lean_object* v_range_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v_range_78_ = lean_obj_once(&l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4);
v___x_79_ = lean_obj_once(&l_Std_Time_Millisecond_instInhabitedOrdinal___closed__0, &l_Std_Time_Millisecond_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Millisecond_instInhabitedOrdinal___closed__0);
v___x_80_ = lean_int_emod(v___x_79_, v_range_78_);
return v___x_80_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_instInhabitedOrdinal___closed__2(void){
_start:
{
lean_object* v_range_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v_range_81_ = lean_obj_once(&l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4);
v___x_82_ = lean_obj_once(&l_Std_Time_Millisecond_instInhabitedOrdinal___closed__1, &l_Std_Time_Millisecond_instInhabitedOrdinal___closed__1_once, _init_l_Std_Time_Millisecond_instInhabitedOrdinal___closed__1);
v___x_83_ = lean_int_add(v___x_82_, v_range_81_);
return v___x_83_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_instInhabitedOrdinal___closed__3(void){
_start:
{
lean_object* v_range_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v_range_84_ = lean_obj_once(&l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4);
v___x_85_ = lean_obj_once(&l_Std_Time_Millisecond_instInhabitedOrdinal___closed__2, &l_Std_Time_Millisecond_instInhabitedOrdinal___closed__2_once, _init_l_Std_Time_Millisecond_instInhabitedOrdinal___closed__2);
v___x_86_ = lean_int_emod(v___x_85_, v_range_84_);
return v___x_86_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_instInhabitedOrdinal___closed__4(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = lean_obj_once(&l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0);
v___x_88_ = lean_obj_once(&l_Std_Time_Millisecond_instInhabitedOrdinal___closed__3, &l_Std_Time_Millisecond_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Millisecond_instInhabitedOrdinal___closed__3);
v___x_89_ = lean_int_add(v___x_88_, v___x_87_);
return v___x_89_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_instInhabitedOrdinal(void){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = lean_obj_once(&l_Std_Time_Millisecond_instInhabitedOrdinal___closed__4, &l_Std_Time_Millisecond_instInhabitedOrdinal___closed__4_once, _init_l_Std_Time_Millisecond_instInhabitedOrdinal___closed__4);
return v___x_90_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Millisecond_instDecidableLeOrdinal___aux__1(lean_object* v_x_91_, lean_object* v_y_92_){
_start:
{
lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_93_ = lean_int_sub(v_y_92_, v_x_91_);
v___x_94_ = lean_int_dec_nonneg(v___x_93_);
lean_dec(v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instDecidableLeOrdinal___aux__1___boxed(lean_object* v_x_95_, lean_object* v_y_96_){
_start:
{
uint8_t v_res_97_; lean_object* v_r_98_; 
v_res_97_ = l_Std_Time_Millisecond_instDecidableLeOrdinal___aux__1(v_x_95_, v_y_96_);
lean_dec(v_y_96_);
lean_dec(v_x_95_);
v_r_98_ = lean_box(v_res_97_);
return v_r_98_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Millisecond_instDecidableLeOrdinal(lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
uint8_t v___x_101_; 
v___x_101_ = l_Std_Time_Millisecond_instDecidableLeOrdinal___aux__1(v___y_99_, v___y_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instDecidableLeOrdinal___boxed(lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
uint8_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = l_Std_Time_Millisecond_instDecidableLeOrdinal(v___y_102_, v___y_103_);
lean_dec(v___y_103_);
lean_dec(v___y_102_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Millisecond_instDecidableLtOrdinal___aux__1(lean_object* v_x_106_, lean_object* v_y_107_){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_108_ = lean_obj_once(&l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__3);
v___x_109_ = lean_int_add(v_x_106_, v___x_108_);
v___x_110_ = lean_int_sub(v_y_107_, v___x_109_);
lean_dec(v___x_109_);
v___x_111_ = lean_int_dec_nonneg(v___x_110_);
lean_dec(v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instDecidableLtOrdinal___aux__1___boxed(lean_object* v_x_112_, lean_object* v_y_113_){
_start:
{
uint8_t v_res_114_; lean_object* v_r_115_; 
v_res_114_ = l_Std_Time_Millisecond_instDecidableLtOrdinal___aux__1(v_x_112_, v_y_113_);
lean_dec(v_y_113_);
lean_dec(v_x_112_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Millisecond_instDecidableLtOrdinal(lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
uint8_t v___x_118_; 
v___x_118_ = l_Std_Time_Millisecond_instDecidableLtOrdinal___aux__1(v___y_116_, v___y_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instDecidableLtOrdinal___boxed(lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
uint8_t v_res_121_; lean_object* v_r_122_; 
v_res_121_ = l_Std_Time_Millisecond_instDecidableLtOrdinal(v___y_119_, v___y_120_);
lean_dec(v___y_120_);
lean_dec(v___y_119_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Millisecond_instOrdOrdinal___aux__1(lean_object* v_x_123_, lean_object* v_y_124_){
_start:
{
uint8_t v___x_125_; 
v___x_125_ = lean_int_dec_lt(v_x_123_, v_y_124_);
if (v___x_125_ == 0)
{
uint8_t v___x_126_; 
v___x_126_ = lean_int_dec_eq(v_x_123_, v_y_124_);
if (v___x_126_ == 0)
{
uint8_t v___x_127_; 
v___x_127_ = 2;
return v___x_127_;
}
else
{
uint8_t v___x_128_; 
v___x_128_ = 1;
return v___x_128_;
}
}
else
{
uint8_t v___x_129_; 
v___x_129_ = 0;
return v___x_129_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instOrdOrdinal___aux__1___boxed(lean_object* v_x_130_, lean_object* v_y_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l_Std_Time_Millisecond_instOrdOrdinal___aux__1(v_x_130_, v_y_131_);
lean_dec(v_y_131_);
lean_dec(v_x_130_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instReprOffset___aux__1(lean_object* v_x_136_, lean_object* v_p_137_){
_start:
{
lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_138_ = lean_obj_once(&l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0);
v___x_139_ = lean_int_dec_lt(v_x_136_, v___x_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = l_Int_repr(v_x_136_);
v___x_141_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
return v___x_141_;
}
else
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_142_ = l_Int_repr(v_x_136_);
v___x_143_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
v___x_144_ = l_Repr_addAppParen(v___x_143_, v_p_137_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instReprOffset___aux__1___boxed(lean_object* v_x_145_, lean_object* v_p_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Std_Time_Millisecond_instReprOffset___aux__1(v_x_145_, v_p_146_);
lean_dec(v_p_146_);
lean_dec(v_x_145_);
return v_res_147_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Millisecond_instDecidableEqOffset___aux__1(lean_object* v_x_149_, lean_object* v_x_150_){
_start:
{
uint8_t v___x_151_; 
v___x_151_ = lean_int_dec_eq(v_x_149_, v_x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instDecidableEqOffset___aux__1___boxed(lean_object* v_x_152_, lean_object* v_x_153_){
_start:
{
uint8_t v_res_154_; lean_object* v_r_155_; 
v_res_154_ = l_Std_Time_Millisecond_instDecidableEqOffset___aux__1(v_x_152_, v_x_153_);
lean_dec(v_x_153_);
lean_dec(v_x_152_);
v_r_155_ = lean_box(v_res_154_);
return v_r_155_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Millisecond_instDecidableEqOffset(lean_object* v_a_156_, lean_object* v_b_157_){
_start:
{
uint8_t v___x_158_; 
v___x_158_ = lean_int_dec_eq(v_a_156_, v_b_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instDecidableEqOffset___boxed(lean_object* v_a_159_, lean_object* v_b_160_){
_start:
{
uint8_t v_res_161_; lean_object* v_r_162_; 
v_res_161_ = l_Std_Time_Millisecond_instDecidableEqOffset(v_a_159_, v_b_160_);
lean_dec(v_b_160_);
lean_dec(v_a_159_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__0(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_unsigned_to_nat(1u);
v___x_164_ = l_Rat_instNatCast___lam__0(v___x_163_);
return v___x_164_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__1(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_unsigned_to_nat(1000u);
v___x_166_ = l_Rat_instNatCast___lam__0(v___x_165_);
return v___x_166_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__2(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = lean_obj_once(&l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__1, &l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__1_once, _init_l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__1);
v___x_168_ = lean_obj_once(&l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__0, &l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__0_once, _init_l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__0);
v___x_169_ = l_Rat_div(v___x_168_, v___x_167_);
return v___x_169_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__3(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_obj_once(&l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__2, &l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__2_once, _init_l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__2);
v___x_171_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_170_);
return v___x_171_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_instInhabitedOffset___aux__1(void){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lean_obj_once(&l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__3, &l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__3_once, _init_l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__3);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Millisecond_instInhabitedOffset_spec__0(lean_object* v_a_173_){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_nat_to_int(v_a_173_);
v___x_175_ = l_Rat_ofInt(v___x_174_);
return v___x_175_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_instInhabitedOffset___closed__0(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = lean_unsigned_to_nat(1u);
v___x_177_ = l_Nat_cast___at___00Std_Time_Millisecond_instInhabitedOffset_spec__0(v___x_176_);
return v___x_177_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_instInhabitedOffset___closed__1(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_unsigned_to_nat(1000u);
v___x_179_ = l_Nat_cast___at___00Std_Time_Millisecond_instInhabitedOffset_spec__0(v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_instInhabitedOffset___closed__2(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = lean_obj_once(&l_Std_Time_Millisecond_instInhabitedOffset___closed__1, &l_Std_Time_Millisecond_instInhabitedOffset___closed__1_once, _init_l_Std_Time_Millisecond_instInhabitedOffset___closed__1);
v___x_181_ = lean_obj_once(&l_Std_Time_Millisecond_instInhabitedOffset___closed__0, &l_Std_Time_Millisecond_instInhabitedOffset___closed__0_once, _init_l_Std_Time_Millisecond_instInhabitedOffset___closed__0);
v___x_182_ = l_Rat_div(v___x_181_, v___x_180_);
return v___x_182_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_instInhabitedOffset___closed__3(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_obj_once(&l_Std_Time_Millisecond_instInhabitedOffset___closed__2, &l_Std_Time_Millisecond_instInhabitedOffset___closed__2_once, _init_l_Std_Time_Millisecond_instInhabitedOffset___closed__2);
v___x_184_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_183_);
return v___x_184_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_instInhabitedOffset(void){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = lean_obj_once(&l_Std_Time_Millisecond_instInhabitedOffset___closed__3, &l_Std_Time_Millisecond_instInhabitedOffset___closed__3_once, _init_l_Std_Time_Millisecond_instInhabitedOffset___closed__3);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Millisecond_instInhabitedOffset_spec__0_spec__0(lean_object* v_a_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = lean_nat_to_int(v_a_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instAddOffset___aux__1(lean_object* v_u1_188_, lean_object* v_u2_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = lean_int_add(v_u1_188_, v_u2_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instAddOffset___aux__1___boxed(lean_object* v_u1_191_, lean_object* v_u2_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Std_Time_Millisecond_instAddOffset___aux__1(v_u1_191_, v_u2_192_);
lean_dec(v_u2_192_);
lean_dec(v_u1_191_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instSubOffset___aux__1(lean_object* v_u1_196_, lean_object* v_u2_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = lean_int_sub(v_u1_196_, v_u2_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instSubOffset___aux__1___boxed(lean_object* v_u1_199_, lean_object* v_u2_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Std_Time_Millisecond_instSubOffset___aux__1(v_u1_199_, v_u2_200_);
lean_dec(v_u2_200_);
lean_dec(v_u1_199_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instNegOffset___aux__1(lean_object* v_x_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = lean_int_neg(v_x_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instNegOffset___aux__1___boxed(lean_object* v_x_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Std_Time_Millisecond_instNegOffset___aux__1(v_x_206_);
lean_dec(v_x_206_);
return v_res_207_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_instLEOffset(void){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = lean_box(0);
return v___x_210_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_instLTOffset(void){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = lean_box(0);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instToStringOffset___aux__1(lean_object* v_n_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Int_repr(v_n_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instToStringOffset___aux__1___boxed(lean_object* v_n_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Std_Time_Millisecond_instToStringOffset___aux__1(v_n_214_);
lean_dec(v_n_214_);
return v_res_215_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Millisecond_instDecidableLeOffset___aux__1(lean_object* v_x_218_, lean_object* v_y_219_){
_start:
{
lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_220_ = lean_int_sub(v_y_219_, v_x_218_);
v___x_221_ = lean_int_dec_nonneg(v___x_220_);
lean_dec(v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instDecidableLeOffset___aux__1___boxed(lean_object* v_x_222_, lean_object* v_y_223_){
_start:
{
uint8_t v_res_224_; lean_object* v_r_225_; 
v_res_224_ = l_Std_Time_Millisecond_instDecidableLeOffset___aux__1(v_x_222_, v_y_223_);
lean_dec(v_y_223_);
lean_dec(v_x_222_);
v_r_225_ = lean_box(v_res_224_);
return v_r_225_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Millisecond_instDecidableLeOffset(lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
uint8_t v___x_228_; 
v___x_228_ = l_Std_Time_Millisecond_instDecidableLeOffset___aux__1(v___y_226_, v___y_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instDecidableLeOffset___boxed(lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
uint8_t v_res_231_; lean_object* v_r_232_; 
v_res_231_ = l_Std_Time_Millisecond_instDecidableLeOffset(v___y_229_, v___y_230_);
lean_dec(v___y_230_);
lean_dec(v___y_229_);
v_r_232_ = lean_box(v_res_231_);
return v_r_232_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Millisecond_instDecidableLtOffset___aux__1(lean_object* v_x_233_, lean_object* v_y_234_){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_235_ = lean_obj_once(&l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__3);
v___x_236_ = lean_int_add(v_x_233_, v___x_235_);
v___x_237_ = lean_int_sub(v_y_234_, v___x_236_);
lean_dec(v___x_236_);
v___x_238_ = lean_int_dec_nonneg(v___x_237_);
lean_dec(v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instDecidableLtOffset___aux__1___boxed(lean_object* v_x_239_, lean_object* v_y_240_){
_start:
{
uint8_t v_res_241_; lean_object* v_r_242_; 
v_res_241_ = l_Std_Time_Millisecond_instDecidableLtOffset___aux__1(v_x_239_, v_y_240_);
lean_dec(v_y_240_);
lean_dec(v_x_239_);
v_r_242_ = lean_box(v_res_241_);
return v_r_242_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Millisecond_instDecidableLtOffset(lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
uint8_t v___x_245_; 
v___x_245_ = l_Std_Time_Millisecond_instDecidableLtOffset___aux__1(v___y_243_, v___y_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instDecidableLtOffset___boxed(lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
uint8_t v_res_248_; lean_object* v_r_249_; 
v_res_248_ = l_Std_Time_Millisecond_instDecidableLtOffset(v___y_246_, v___y_247_);
lean_dec(v___y_247_);
lean_dec(v___y_246_);
v_r_249_ = lean_box(v_res_248_);
return v_r_249_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instOfNatOffset(lean_object* v_n_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = lean_nat_to_int(v_n_250_);
return v___x_251_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Millisecond_instOrdOffset___aux__1(lean_object* v_x_252_, lean_object* v_y_253_){
_start:
{
uint8_t v___x_254_; 
v___x_254_ = lean_int_dec_lt(v_x_252_, v_y_253_);
if (v___x_254_ == 0)
{
uint8_t v___x_255_; 
v___x_255_ = lean_int_dec_eq(v_x_252_, v_y_253_);
if (v___x_255_ == 0)
{
uint8_t v___x_256_; 
v___x_256_ = 2;
return v___x_256_;
}
else
{
uint8_t v___x_257_; 
v___x_257_ = 1;
return v___x_257_;
}
}
else
{
uint8_t v___x_258_; 
v___x_258_ = 0;
return v___x_258_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_instOrdOffset___aux__1___boxed(lean_object* v_x_259_, lean_object* v_y_260_){
_start:
{
uint8_t v_res_261_; lean_object* v_r_262_; 
v_res_261_ = l_Std_Time_Millisecond_instOrdOffset___aux__1(v_x_259_, v_y_260_);
lean_dec(v_y_260_);
lean_dec(v_x_259_);
v_r_262_ = lean_box(v_res_261_);
return v_r_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofNat(lean_object* v_data_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = lean_nat_to_int(v_data_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofInt(lean_object* v_data_267_){
_start:
{
lean_inc(v_data_267_);
return v_data_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofInt___boxed(lean_object* v_data_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Std_Time_Millisecond_Offset_ofInt(v_data_268_);
lean_dec(v_data_268_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Ordinal_ofInt___redArg(lean_object* v_data_270_){
_start:
{
lean_inc(v_data_270_);
return v_data_270_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Ordinal_ofInt___redArg___boxed(lean_object* v_data_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Std_Time_Millisecond_Ordinal_ofInt___redArg(v_data_271_);
lean_dec(v_data_271_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Ordinal_ofInt(lean_object* v_data_273_, lean_object* v_h_274_){
_start:
{
lean_inc(v_data_273_);
return v_data_273_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Ordinal_ofInt___boxed(lean_object* v_data_275_, lean_object* v_h_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Std_Time_Millisecond_Ordinal_ofInt(v_data_275_, v_h_276_);
lean_dec(v_data_275_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Ordinal_ofNat___redArg(lean_object* v_data_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = lean_nat_to_int(v_data_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Ordinal_ofNat(lean_object* v_data_280_, lean_object* v_h_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = lean_nat_to_int(v_data_280_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Ordinal_ofFin(lean_object* v_data_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = lean_nat_to_int(v_data_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Ordinal_toOffset(lean_object* v_ordinal_285_){
_start:
{
lean_inc(v_ordinal_285_);
return v_ordinal_285_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Ordinal_toOffset___boxed(lean_object* v_ordinal_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Std_Time_Millisecond_Ordinal_toOffset(v_ordinal_286_);
lean_dec(v_ordinal_286_);
return v_res_287_;
}
}
lean_object* runtime_initialize_Std_Time_Time_Unit_Nanosecond(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Time_Unit_Millisecond(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time_Time_Unit_Nanosecond(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_Millisecond_instLEOrdinal = _init_l_Std_Time_Millisecond_instLEOrdinal();
lean_mark_persistent(l_Std_Time_Millisecond_instLEOrdinal);
l_Std_Time_Millisecond_instLTOrdinal = _init_l_Std_Time_Millisecond_instLTOrdinal();
lean_mark_persistent(l_Std_Time_Millisecond_instLTOrdinal);
l_Std_Time_Millisecond_instInhabitedOrdinal = _init_l_Std_Time_Millisecond_instInhabitedOrdinal();
lean_mark_persistent(l_Std_Time_Millisecond_instInhabitedOrdinal);
l_Std_Time_Millisecond_instInhabitedOffset___aux__1 = _init_l_Std_Time_Millisecond_instInhabitedOffset___aux__1();
lean_mark_persistent(l_Std_Time_Millisecond_instInhabitedOffset___aux__1);
l_Std_Time_Millisecond_instInhabitedOffset = _init_l_Std_Time_Millisecond_instInhabitedOffset();
lean_mark_persistent(l_Std_Time_Millisecond_instInhabitedOffset);
l_Std_Time_Millisecond_instLEOffset = _init_l_Std_Time_Millisecond_instLEOffset();
lean_mark_persistent(l_Std_Time_Millisecond_instLEOffset);
l_Std_Time_Millisecond_instLTOffset = _init_l_Std_Time_Millisecond_instLTOffset();
lean_mark_persistent(l_Std_Time_Millisecond_instLTOffset);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Time_Unit_Millisecond(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Time_Unit_Nanosecond(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Time_Unit_Millisecond(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Time_Unit_Nanosecond(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Time_Unit_Millisecond(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Time_Unit_Millisecond(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Time_Unit_Millisecond(builtin);
}
#ifdef __cplusplus
}
#endif
