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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_instInhabitedUnitVal_default___redArg();
lean_object* l_Int_neg___boxed(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Int_sub___boxed(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Int_repr___boxed(lean_object*);
lean_object* l_Int_add___boxed(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
static lean_once_cell_t l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instReprOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instReprOrdinal___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instReprOrdinal___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instReprOrdinal___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Nanosecond_instReprOrdinal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Nanosecond_instReprOrdinal___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Nanosecond_instReprOrdinal___closed__0 = (const lean_object*)&l_Std_Time_Nanosecond_instReprOrdinal___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Nanosecond_instReprOrdinal = (const lean_object*)&l_Std_Time_Nanosecond_instReprOrdinal___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableEqOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqOrdinal___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableEqOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqOrdinal___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instLEOrdinal;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instLTOrdinal;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instOfNatOrdinal(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instOfNatOrdinal___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instInhabitedOrdinal;
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLeOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeOrdinal___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLeOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeOrdinal___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLtOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtOrdinal___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instOrdOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instOrdOrdinal___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Nanosecond_instOrdOrdinal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Nanosecond_instOrdOrdinal___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Nanosecond_instOrdOrdinal___closed__0 = (const lean_object*)&l_Std_Time_Nanosecond_instOrdOrdinal___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Nanosecond_instOrdOrdinal = (const lean_object*)&l_Std_Time_Nanosecond_instOrdOrdinal___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instReprOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instReprOffset___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT const lean_object* l_Std_Time_Nanosecond_instReprOffset = (const lean_object*)&l_Std_Time_Nanosecond_instReprOrdinal___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableEqOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqOffset___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Nanosecond_instDecidableEqOffset___aux__1_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Nanosecond_instDecidableEqOffset___aux__1_spec__0(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableEqOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqOffset___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instInhabitedOffset___aux__1;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instInhabitedOffset;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instAddOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instAddOffset___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Nanosecond_instAddOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Nanosecond_instAddOffset___closed__0 = (const lean_object*)&l_Std_Time_Nanosecond_instAddOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Nanosecond_instAddOffset = (const lean_object*)&l_Std_Time_Nanosecond_instAddOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instSubOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instSubOffset___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Nanosecond_instSubOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Nanosecond_instSubOffset___closed__0 = (const lean_object*)&l_Std_Time_Nanosecond_instSubOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Nanosecond_instSubOffset = (const lean_object*)&l_Std_Time_Nanosecond_instSubOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instNegOffset___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instNegOffset___aux__1___boxed(lean_object*);
static const lean_closure_object l_Std_Time_Nanosecond_instNegOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Nanosecond_instNegOffset___closed__0 = (const lean_object*)&l_Std_Time_Nanosecond_instNegOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Nanosecond_instNegOffset = (const lean_object*)&l_Std_Time_Nanosecond_instNegOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instLEOffset;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instLTOffset;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instToStringOffset___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instToStringOffset___aux__1___boxed(lean_object*);
static const lean_closure_object l_Std_Time_Nanosecond_instToStringOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_repr___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Nanosecond_instToStringOffset___closed__0 = (const lean_object*)&l_Std_Time_Nanosecond_instToStringOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Nanosecond_instToStringOffset = (const lean_object*)&l_Std_Time_Nanosecond_instToStringOffset___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLeOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeOffset___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLeOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLtOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtOffset___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLtOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instOfNatOffset(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instOrdOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instOrdOffset___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Nanosecond_instOrdOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Nanosecond_instOrdOffset___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Nanosecond_instOrdOffset___closed__0 = (const lean_object*)&l_Std_Time_Nanosecond_instOrdOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Nanosecond_instOrdOffset = (const lean_object*)&l_Std_Time_Nanosecond_instOrdOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofInt(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofInt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instReprSpan___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instReprSpan___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT const lean_object* l_Std_Time_Nanosecond_instReprSpan = (const lean_object*)&l_Std_Time_Nanosecond_instReprOrdinal___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableEqSpan___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqSpan___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableEqSpan(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqSpan___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instLESpan;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instLTSpan;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instInhabitedSpan;
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLeSpan___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeSpan___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLeSpan(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeSpan___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLtSpan___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtSpan___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLtSpan(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtSpan___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instOrdSpan___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instOrdSpan___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Nanosecond_instOrdSpan___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Nanosecond_instOrdSpan___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Nanosecond_instOrdSpan___closed__0 = (const lean_object*)&l_Std_Time_Nanosecond_instOrdSpan___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Nanosecond_instOrdSpan = (const lean_object*)&l_Std_Time_Nanosecond_instOrdSpan___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Span_toOffset(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Span_toOffset___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instReprOfDay___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instReprOfDay___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT const lean_object* l_Std_Time_Nanosecond_Ordinal_instReprOfDay = (const lean_object*)&l_Std_Time_Nanosecond_instReprOrdinal___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instLEOfDay;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instLTOfDay;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instInhabitedOfDay;
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instOrdOfDay___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instOrdOfDay___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Nanosecond_Ordinal_instOrdOfDay___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Nanosecond_Ordinal_instOrdOfDay___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Nanosecond_Ordinal_instOrdOfDay___closed__0 = (const lean_object*)&l_Std_Time_Nanosecond_Ordinal_instOrdOfDay___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Nanosecond_Ordinal_instOrdOfDay = (const lean_object*)&l_Std_Time_Nanosecond_Ordinal_instOrdOfDay___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofInt___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofInt___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofInt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofInt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofNat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofFin(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_toOffset(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_toOffset___boxed(lean_object*);
static lean_object* _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instReprOrdinal___aux__1(lean_object* v_n_3_, lean_object* v_a_4_){
_start:
{
lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_5_ = lean_obj_once(&l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0);
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
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instReprOrdinal___aux__1___boxed(lean_object* v_n_12_, lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_Time_Nanosecond_instReprOrdinal___aux__1(v_n_12_, v_a_13_);
lean_dec(v_a_13_);
lean_dec(v_n_12_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instReprOrdinal___lam__0(lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
lean_object* v___x_17_; uint8_t v___x_18_; 
v___x_17_ = lean_obj_once(&l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0);
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
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instReprOrdinal___lam__0___boxed(lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Std_Time_Nanosecond_instReprOrdinal___lam__0(v___y_24_, v___y_25_);
lean_dec(v___y_25_);
lean_dec(v___y_24_);
return v_res_26_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableEqOrdinal___aux__1(lean_object* v_a_29_, lean_object* v_b_30_){
_start:
{
uint8_t v___x_31_; 
v___x_31_ = lean_int_dec_eq(v_a_29_, v_b_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqOrdinal___aux__1___boxed(lean_object* v_a_32_, lean_object* v_b_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l_Std_Time_Nanosecond_instDecidableEqOrdinal___aux__1(v_a_32_, v_b_33_);
lean_dec(v_b_33_);
lean_dec(v_a_32_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableEqOrdinal(lean_object* v_a_36_, lean_object* v_b_37_){
_start:
{
uint8_t v___x_38_; 
v___x_38_ = lean_int_dec_eq(v_a_36_, v_b_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqOrdinal___boxed(lean_object* v_a_39_, lean_object* v_b_40_){
_start:
{
uint8_t v_res_41_; lean_object* v_r_42_; 
v_res_41_ = l_Std_Time_Nanosecond_instDecidableEqOrdinal(v_a_39_, v_b_40_);
lean_dec(v_b_40_);
lean_dec(v_a_39_);
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instLEOrdinal(void){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_box(0);
return v___x_43_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instLTOrdinal(void){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_box(0);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instOfNatOrdinal(lean_object* v_n_45_){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_unsigned_to_nat(1000000000u);
v___x_47_ = lean_nat_mod(v_n_45_, v___x_46_);
v___x_48_ = lean_nat_to_int(v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instOfNatOrdinal___boxed(lean_object* v_n_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Std_Time_Nanosecond_instOfNatOrdinal(v_n_49_);
lean_dec(v_n_49_);
return v_res_50_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__0(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_unsigned_to_nat(0u);
v___x_52_ = lean_nat_to_int(v___x_51_);
return v___x_52_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOrdinal(void){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lean_obj_once(&l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__0, &l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__0);
return v___x_53_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLeOrdinal___aux__1(lean_object* v_x_54_, lean_object* v_y_55_){
_start:
{
uint8_t v___x_56_; 
v___x_56_ = lean_int_dec_le(v_x_54_, v_y_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeOrdinal___aux__1___boxed(lean_object* v_x_57_, lean_object* v_y_58_){
_start:
{
uint8_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = l_Std_Time_Nanosecond_instDecidableLeOrdinal___aux__1(v_x_57_, v_y_58_);
lean_dec(v_y_58_);
lean_dec(v_x_57_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLeOrdinal(lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = lean_int_dec_le(v___y_61_, v___y_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeOrdinal___boxed(lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
uint8_t v_res_66_; lean_object* v_r_67_; 
v_res_66_ = l_Std_Time_Nanosecond_instDecidableLeOrdinal(v___y_64_, v___y_65_);
lean_dec(v___y_65_);
lean_dec(v___y_64_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1(lean_object* v_x_68_, lean_object* v_y_69_){
_start:
{
uint8_t v___x_70_; 
v___x_70_ = lean_int_dec_lt(v_x_68_, v_y_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1___boxed(lean_object* v_x_71_, lean_object* v_y_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1(v_x_71_, v_y_72_);
lean_dec(v_y_72_);
lean_dec(v_x_71_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLtOrdinal(lean_object* v___y_75_, lean_object* v___y_76_){
_start:
{
uint8_t v___x_77_; 
v___x_77_ = lean_int_dec_lt(v___y_75_, v___y_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtOrdinal___boxed(lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
uint8_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = l_Std_Time_Nanosecond_instDecidableLtOrdinal(v___y_78_, v___y_79_);
lean_dec(v___y_79_);
lean_dec(v___y_78_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instOrdOrdinal___aux__1(lean_object* v_x_82_, lean_object* v_y_83_){
_start:
{
uint8_t v___x_84_; 
v___x_84_ = lean_int_dec_lt(v_x_82_, v_y_83_);
if (v___x_84_ == 0)
{
uint8_t v___x_85_; 
v___x_85_ = lean_int_dec_eq(v_x_82_, v_y_83_);
if (v___x_85_ == 0)
{
uint8_t v___x_86_; 
v___x_86_ = 2;
return v___x_86_;
}
else
{
uint8_t v___x_87_; 
v___x_87_ = 1;
return v___x_87_;
}
}
else
{
uint8_t v___x_88_; 
v___x_88_ = 0;
return v___x_88_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instOrdOrdinal___aux__1___boxed(lean_object* v_x_89_, lean_object* v_y_90_){
_start:
{
uint8_t v_res_91_; lean_object* v_r_92_; 
v_res_91_ = l_Std_Time_Nanosecond_instOrdOrdinal___aux__1(v_x_89_, v_y_90_);
lean_dec(v_y_90_);
lean_dec(v_x_89_);
v_r_92_ = lean_box(v_res_91_);
return v_r_92_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instReprOffset___aux__1(lean_object* v_x_95_, lean_object* v_p_96_){
_start:
{
lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_97_ = lean_obj_once(&l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0);
v___x_98_ = lean_int_dec_lt(v_x_95_, v___x_97_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = l_Int_repr(v_x_95_);
v___x_100_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
return v___x_100_;
}
else
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = l_Int_repr(v_x_95_);
v___x_102_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
v___x_103_ = l_Repr_addAppParen(v___x_102_, v_p_96_);
return v___x_103_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instReprOffset___aux__1___boxed(lean_object* v_x_104_, lean_object* v_p_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Std_Time_Nanosecond_instReprOffset___aux__1(v_x_104_, v_p_105_);
lean_dec(v_p_105_);
lean_dec(v_x_104_);
return v_res_106_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableEqOffset___aux__1(lean_object* v_a_108_, lean_object* v_b_109_){
_start:
{
uint8_t v___x_110_; 
v___x_110_ = lean_int_dec_eq(v_a_108_, v_b_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqOffset___aux__1___boxed(lean_object* v_a_111_, lean_object* v_b_112_){
_start:
{
uint8_t v_res_113_; lean_object* v_r_114_; 
v_res_113_ = l_Std_Time_Nanosecond_instDecidableEqOffset___aux__1(v_a_111_, v_b_112_);
lean_dec(v_b_112_);
lean_dec(v_a_111_);
v_r_114_ = lean_box(v_res_113_);
return v_r_114_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Nanosecond_instDecidableEqOffset___aux__1_spec__0_spec__0(lean_object* v_a_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_nat_to_int(v_a_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Nanosecond_instDecidableEqOffset___aux__1_spec__0(lean_object* v_a_117_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = lean_nat_to_int(v_a_117_);
v___x_119_ = l_Rat_ofInt(v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableEqOffset(lean_object* v_a_120_, lean_object* v_b_121_){
_start:
{
uint8_t v___x_122_; 
v___x_122_ = lean_int_dec_eq(v_a_120_, v_b_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqOffset___boxed(lean_object* v_a_123_, lean_object* v_b_124_){
_start:
{
uint8_t v_res_125_; lean_object* v_r_126_; 
v_res_125_ = l_Std_Time_Nanosecond_instDecidableEqOffset(v_a_123_, v_b_124_);
lean_dec(v_b_124_);
lean_dec(v_a_123_);
v_r_126_ = lean_box(v_res_125_);
return v_r_126_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__0(void){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Std_Time_Internal_instInhabitedUnitVal_default___redArg();
return v___x_127_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOffset___aux__1(void){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = lean_obj_once(&l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__0, &l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__0);
return v___x_128_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOffset(void){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lean_obj_once(&l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__0, &l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__0);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instAddOffset___aux__1(lean_object* v_u1_130_, lean_object* v_u2_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = lean_int_add(v_u1_130_, v_u2_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instAddOffset___aux__1___boxed(lean_object* v_u1_133_, lean_object* v_u2_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Std_Time_Nanosecond_instAddOffset___aux__1(v_u1_133_, v_u2_134_);
lean_dec(v_u2_134_);
lean_dec(v_u1_133_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instSubOffset___aux__1(lean_object* v_u1_138_, lean_object* v_u2_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = lean_int_sub(v_u1_138_, v_u2_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instSubOffset___aux__1___boxed(lean_object* v_u1_141_, lean_object* v_u2_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Std_Time_Nanosecond_instSubOffset___aux__1(v_u1_141_, v_u2_142_);
lean_dec(v_u2_142_);
lean_dec(v_u1_141_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instNegOffset___aux__1(lean_object* v_x_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = lean_int_neg(v_x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instNegOffset___aux__1___boxed(lean_object* v_x_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Std_Time_Nanosecond_instNegOffset___aux__1(v_x_148_);
lean_dec(v_x_148_);
return v_res_149_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instLEOffset(void){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = lean_box(0);
return v___x_152_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instLTOffset(void){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = lean_box(0);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instToStringOffset___aux__1(lean_object* v_n_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Int_repr(v_n_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instToStringOffset___aux__1___boxed(lean_object* v_n_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Std_Time_Nanosecond_instToStringOffset___aux__1(v_n_156_);
lean_dec(v_n_156_);
return v_res_157_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLeOffset___aux__1(lean_object* v_x_160_, lean_object* v_y_161_){
_start:
{
uint8_t v___x_162_; 
v___x_162_ = lean_int_dec_le(v_x_160_, v_y_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeOffset___aux__1___boxed(lean_object* v_x_163_, lean_object* v_y_164_){
_start:
{
uint8_t v_res_165_; lean_object* v_r_166_; 
v_res_165_ = l_Std_Time_Nanosecond_instDecidableLeOffset___aux__1(v_x_163_, v_y_164_);
lean_dec(v_y_164_);
lean_dec(v_x_163_);
v_r_166_ = lean_box(v_res_165_);
return v_r_166_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLeOffset(lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
uint8_t v___x_169_; 
v___x_169_ = lean_int_dec_le(v___y_167_, v___y_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeOffset___boxed(lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
uint8_t v_res_172_; lean_object* v_r_173_; 
v_res_172_ = l_Std_Time_Nanosecond_instDecidableLeOffset(v___y_170_, v___y_171_);
lean_dec(v___y_171_);
lean_dec(v___y_170_);
v_r_173_ = lean_box(v_res_172_);
return v_r_173_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLtOffset___aux__1(lean_object* v_x_174_, lean_object* v_y_175_){
_start:
{
uint8_t v___x_176_; 
v___x_176_ = lean_int_dec_lt(v_x_174_, v_y_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtOffset___aux__1___boxed(lean_object* v_x_177_, lean_object* v_y_178_){
_start:
{
uint8_t v_res_179_; lean_object* v_r_180_; 
v_res_179_ = l_Std_Time_Nanosecond_instDecidableLtOffset___aux__1(v_x_177_, v_y_178_);
lean_dec(v_y_178_);
lean_dec(v_x_177_);
v_r_180_ = lean_box(v_res_179_);
return v_r_180_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLtOffset(lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
uint8_t v___x_183_; 
v___x_183_ = lean_int_dec_lt(v___y_181_, v___y_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtOffset___boxed(lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
uint8_t v_res_186_; lean_object* v_r_187_; 
v_res_186_ = l_Std_Time_Nanosecond_instDecidableLtOffset(v___y_184_, v___y_185_);
lean_dec(v___y_185_);
lean_dec(v___y_184_);
v_r_187_ = lean_box(v_res_186_);
return v_r_187_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instOfNatOffset(lean_object* v_n_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = lean_nat_to_int(v_n_188_);
return v___x_189_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instOrdOffset___aux__1(lean_object* v_x_190_, lean_object* v_y_191_){
_start:
{
uint8_t v___x_192_; 
v___x_192_ = lean_int_dec_lt(v_x_190_, v_y_191_);
if (v___x_192_ == 0)
{
uint8_t v___x_193_; 
v___x_193_ = lean_int_dec_eq(v_x_190_, v_y_191_);
if (v___x_193_ == 0)
{
uint8_t v___x_194_; 
v___x_194_ = 2;
return v___x_194_;
}
else
{
uint8_t v___x_195_; 
v___x_195_ = 1;
return v___x_195_;
}
}
else
{
uint8_t v___x_196_; 
v___x_196_ = 0;
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instOrdOffset___aux__1___boxed(lean_object* v_x_197_, lean_object* v_y_198_){
_start:
{
uint8_t v_res_199_; lean_object* v_r_200_; 
v_res_199_ = l_Std_Time_Nanosecond_instOrdOffset___aux__1(v_x_197_, v_y_198_);
lean_dec(v_y_198_);
lean_dec(v_x_197_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofNat(lean_object* v_data_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = lean_nat_to_int(v_data_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofInt(lean_object* v_data_205_){
_start:
{
lean_inc(v_data_205_);
return v_data_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofInt___boxed(lean_object* v_data_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Std_Time_Nanosecond_Offset_ofInt(v_data_206_);
lean_dec(v_data_206_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instReprSpan___aux__1(lean_object* v_n_208_, lean_object* v_a_209_){
_start:
{
lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_210_ = lean_obj_once(&l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0);
v___x_211_ = lean_int_dec_lt(v_n_208_, v___x_210_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = l_Int_repr(v_n_208_);
v___x_213_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
return v___x_213_;
}
else
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_214_ = l_Int_repr(v_n_208_);
v___x_215_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
v___x_216_ = l_Repr_addAppParen(v___x_215_, v_a_209_);
return v___x_216_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instReprSpan___aux__1___boxed(lean_object* v_n_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Std_Time_Nanosecond_instReprSpan___aux__1(v_n_217_, v_a_218_);
lean_dec(v_a_218_);
lean_dec(v_n_217_);
return v_res_219_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableEqSpan___aux__1(lean_object* v_a_221_, lean_object* v_b_222_){
_start:
{
uint8_t v___x_223_; 
v___x_223_ = lean_int_dec_eq(v_a_221_, v_b_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqSpan___aux__1___boxed(lean_object* v_a_224_, lean_object* v_b_225_){
_start:
{
uint8_t v_res_226_; lean_object* v_r_227_; 
v_res_226_ = l_Std_Time_Nanosecond_instDecidableEqSpan___aux__1(v_a_224_, v_b_225_);
lean_dec(v_b_225_);
lean_dec(v_a_224_);
v_r_227_ = lean_box(v_res_226_);
return v_r_227_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableEqSpan(lean_object* v_a_228_, lean_object* v_b_229_){
_start:
{
uint8_t v___x_230_; 
v___x_230_ = lean_int_dec_eq(v_a_228_, v_b_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqSpan___boxed(lean_object* v_a_231_, lean_object* v_b_232_){
_start:
{
uint8_t v_res_233_; lean_object* v_r_234_; 
v_res_233_ = l_Std_Time_Nanosecond_instDecidableEqSpan(v_a_231_, v_b_232_);
lean_dec(v_b_232_);
lean_dec(v_a_231_);
v_r_234_ = lean_box(v_res_233_);
return v_r_234_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instLESpan(void){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = lean_box(0);
return v___x_235_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instLTSpan(void){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = lean_box(0);
return v___x_236_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedSpan(void){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = lean_obj_once(&l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0);
return v___x_237_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLeSpan___aux__1(lean_object* v_x_238_, lean_object* v_y_239_){
_start:
{
uint8_t v___x_240_; 
v___x_240_ = lean_int_dec_le(v_x_238_, v_y_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeSpan___aux__1___boxed(lean_object* v_x_241_, lean_object* v_y_242_){
_start:
{
uint8_t v_res_243_; lean_object* v_r_244_; 
v_res_243_ = l_Std_Time_Nanosecond_instDecidableLeSpan___aux__1(v_x_241_, v_y_242_);
lean_dec(v_y_242_);
lean_dec(v_x_241_);
v_r_244_ = lean_box(v_res_243_);
return v_r_244_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLeSpan(lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
uint8_t v___x_247_; 
v___x_247_ = lean_int_dec_le(v___y_245_, v___y_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeSpan___boxed(lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
uint8_t v_res_250_; lean_object* v_r_251_; 
v_res_250_ = l_Std_Time_Nanosecond_instDecidableLeSpan(v___y_248_, v___y_249_);
lean_dec(v___y_249_);
lean_dec(v___y_248_);
v_r_251_ = lean_box(v_res_250_);
return v_r_251_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLtSpan___aux__1(lean_object* v_x_252_, lean_object* v_y_253_){
_start:
{
uint8_t v___x_254_; 
v___x_254_ = lean_int_dec_lt(v_x_252_, v_y_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtSpan___aux__1___boxed(lean_object* v_x_255_, lean_object* v_y_256_){
_start:
{
uint8_t v_res_257_; lean_object* v_r_258_; 
v_res_257_ = l_Std_Time_Nanosecond_instDecidableLtSpan___aux__1(v_x_255_, v_y_256_);
lean_dec(v_y_256_);
lean_dec(v_x_255_);
v_r_258_ = lean_box(v_res_257_);
return v_r_258_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLtSpan(lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
uint8_t v___x_261_; 
v___x_261_ = lean_int_dec_lt(v___y_259_, v___y_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtSpan___boxed(lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
uint8_t v_res_264_; lean_object* v_r_265_; 
v_res_264_ = l_Std_Time_Nanosecond_instDecidableLtSpan(v___y_262_, v___y_263_);
lean_dec(v___y_263_);
lean_dec(v___y_262_);
v_r_265_ = lean_box(v_res_264_);
return v_r_265_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instOrdSpan___aux__1(lean_object* v_x_266_, lean_object* v_y_267_){
_start:
{
uint8_t v___x_268_; 
v___x_268_ = lean_int_dec_lt(v_x_266_, v_y_267_);
if (v___x_268_ == 0)
{
uint8_t v___x_269_; 
v___x_269_ = lean_int_dec_eq(v_x_266_, v_y_267_);
if (v___x_269_ == 0)
{
uint8_t v___x_270_; 
v___x_270_ = 2;
return v___x_270_;
}
else
{
uint8_t v___x_271_; 
v___x_271_ = 1;
return v___x_271_;
}
}
else
{
uint8_t v___x_272_; 
v___x_272_ = 0;
return v___x_272_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instOrdSpan___aux__1___boxed(lean_object* v_x_273_, lean_object* v_y_274_){
_start:
{
uint8_t v_res_275_; lean_object* v_r_276_; 
v_res_275_ = l_Std_Time_Nanosecond_instOrdSpan___aux__1(v_x_273_, v_y_274_);
lean_dec(v_y_274_);
lean_dec(v_x_273_);
v_r_276_ = lean_box(v_res_275_);
return v_r_276_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Span_toOffset(lean_object* v_span_279_){
_start:
{
lean_inc(v_span_279_);
return v_span_279_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Span_toOffset___boxed(lean_object* v_span_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Std_Time_Nanosecond_Span_toOffset(v_span_280_);
lean_dec(v_span_280_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instReprOfDay___aux__1(lean_object* v_n_282_, lean_object* v_a_283_){
_start:
{
lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_284_ = lean_obj_once(&l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0);
v___x_285_ = lean_int_dec_lt(v_n_282_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = l_Int_repr(v_n_282_);
v___x_287_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
return v___x_287_;
}
else
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_288_ = l_Int_repr(v_n_282_);
v___x_289_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
v___x_290_ = l_Repr_addAppParen(v___x_289_, v_a_283_);
return v___x_290_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instReprOfDay___aux__1___boxed(lean_object* v_n_291_, lean_object* v_a_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Std_Time_Nanosecond_Ordinal_instReprOfDay___aux__1(v_n_291_, v_a_292_);
lean_dec(v_a_292_);
lean_dec(v_n_291_);
return v_res_293_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay___aux__1(lean_object* v_a_295_, lean_object* v_b_296_){
_start:
{
uint8_t v___x_297_; 
v___x_297_ = lean_int_dec_eq(v_a_295_, v_b_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay___aux__1___boxed(lean_object* v_a_298_, lean_object* v_b_299_){
_start:
{
uint8_t v_res_300_; lean_object* v_r_301_; 
v_res_300_ = l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay___aux__1(v_a_298_, v_b_299_);
lean_dec(v_b_299_);
lean_dec(v_a_298_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay(lean_object* v_a_302_, lean_object* v_b_303_){
_start:
{
uint8_t v___x_304_; 
v___x_304_ = lean_int_dec_eq(v_a_302_, v_b_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay___boxed(lean_object* v_a_305_, lean_object* v_b_306_){
_start:
{
uint8_t v_res_307_; lean_object* v_r_308_; 
v_res_307_ = l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay(v_a_305_, v_b_306_);
lean_dec(v_b_306_);
lean_dec(v_a_305_);
v_r_308_ = lean_box(v_res_307_);
return v_r_308_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_Ordinal_instLEOfDay(void){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = lean_box(0);
return v___x_309_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_Ordinal_instLTOfDay(void){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = lean_box(0);
return v___x_310_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_Ordinal_instInhabitedOfDay(void){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = lean_obj_once(&l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0);
return v___x_311_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay___aux__1(lean_object* v_x_312_, lean_object* v_y_313_){
_start:
{
uint8_t v___x_314_; 
v___x_314_ = lean_int_dec_le(v_x_312_, v_y_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay___aux__1___boxed(lean_object* v_x_315_, lean_object* v_y_316_){
_start:
{
uint8_t v_res_317_; lean_object* v_r_318_; 
v_res_317_ = l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay___aux__1(v_x_315_, v_y_316_);
lean_dec(v_y_316_);
lean_dec(v_x_315_);
v_r_318_ = lean_box(v_res_317_);
return v_r_318_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay(lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
uint8_t v___x_321_; 
v___x_321_ = lean_int_dec_le(v___y_319_, v___y_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay___boxed(lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
uint8_t v_res_324_; lean_object* v_r_325_; 
v_res_324_ = l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay(v___y_322_, v___y_323_);
lean_dec(v___y_323_);
lean_dec(v___y_322_);
v_r_325_ = lean_box(v_res_324_);
return v_r_325_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay___aux__1(lean_object* v_x_326_, lean_object* v_y_327_){
_start:
{
uint8_t v___x_328_; 
v___x_328_ = lean_int_dec_lt(v_x_326_, v_y_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay___aux__1___boxed(lean_object* v_x_329_, lean_object* v_y_330_){
_start:
{
uint8_t v_res_331_; lean_object* v_r_332_; 
v_res_331_ = l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay___aux__1(v_x_329_, v_y_330_);
lean_dec(v_y_330_);
lean_dec(v_x_329_);
v_r_332_ = lean_box(v_res_331_);
return v_r_332_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay(lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
uint8_t v___x_335_; 
v___x_335_ = lean_int_dec_lt(v___y_333_, v___y_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay___boxed(lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
uint8_t v_res_338_; lean_object* v_r_339_; 
v_res_338_ = l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay(v___y_336_, v___y_337_);
lean_dec(v___y_337_);
lean_dec(v___y_336_);
v_r_339_ = lean_box(v_res_338_);
return v_r_339_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instOrdOfDay___aux__1(lean_object* v_x_340_, lean_object* v_y_341_){
_start:
{
uint8_t v___x_342_; 
v___x_342_ = lean_int_dec_lt(v_x_340_, v_y_341_);
if (v___x_342_ == 0)
{
uint8_t v___x_343_; 
v___x_343_ = lean_int_dec_eq(v_x_340_, v_y_341_);
if (v___x_343_ == 0)
{
uint8_t v___x_344_; 
v___x_344_ = 2;
return v___x_344_;
}
else
{
uint8_t v___x_345_; 
v___x_345_ = 1;
return v___x_345_;
}
}
else
{
uint8_t v___x_346_; 
v___x_346_ = 0;
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instOrdOfDay___aux__1___boxed(lean_object* v_x_347_, lean_object* v_y_348_){
_start:
{
uint8_t v_res_349_; lean_object* v_r_350_; 
v_res_349_ = l_Std_Time_Nanosecond_Ordinal_instOrdOfDay___aux__1(v_x_347_, v_y_348_);
lean_dec(v_y_348_);
lean_dec(v_x_347_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofInt___redArg(lean_object* v_data_353_){
_start:
{
lean_inc(v_data_353_);
return v_data_353_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofInt___redArg___boxed(lean_object* v_data_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Std_Time_Nanosecond_Ordinal_ofInt___redArg(v_data_354_);
lean_dec(v_data_354_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofInt(lean_object* v_data_356_, lean_object* v_h_357_){
_start:
{
lean_inc(v_data_356_);
return v_data_356_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofInt___boxed(lean_object* v_data_358_, lean_object* v_h_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Std_Time_Nanosecond_Ordinal_ofInt(v_data_358_, v_h_359_);
lean_dec(v_data_358_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofNat___redArg(lean_object* v_data_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = lean_nat_to_int(v_data_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofNat(lean_object* v_data_363_, lean_object* v_h_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = lean_nat_to_int(v_data_363_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofFin(lean_object* v_data_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = lean_nat_to_int(v_data_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_toOffset(lean_object* v_ordinal_368_){
_start:
{
lean_inc(v_ordinal_368_);
return v_ordinal_368_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_toOffset___boxed(lean_object* v_ordinal_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Std_Time_Nanosecond_Ordinal_toOffset(v_ordinal_369_);
lean_dec(v_ordinal_369_);
return v_res_370_;
}
}
lean_object* runtime_initialize_Std_Time_Internal(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Time_Unit_Nanosecond(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Time_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_Nanosecond_instLEOrdinal = _init_l_Std_Time_Nanosecond_instLEOrdinal();
lean_mark_persistent(l_Std_Time_Nanosecond_instLEOrdinal);
l_Std_Time_Nanosecond_instLTOrdinal = _init_l_Std_Time_Nanosecond_instLTOrdinal();
lean_mark_persistent(l_Std_Time_Nanosecond_instLTOrdinal);
l_Std_Time_Nanosecond_instInhabitedOrdinal = _init_l_Std_Time_Nanosecond_instInhabitedOrdinal();
lean_mark_persistent(l_Std_Time_Nanosecond_instInhabitedOrdinal);
l_Std_Time_Nanosecond_instInhabitedOffset___aux__1 = _init_l_Std_Time_Nanosecond_instInhabitedOffset___aux__1();
lean_mark_persistent(l_Std_Time_Nanosecond_instInhabitedOffset___aux__1);
l_Std_Time_Nanosecond_instInhabitedOffset = _init_l_Std_Time_Nanosecond_instInhabitedOffset();
lean_mark_persistent(l_Std_Time_Nanosecond_instInhabitedOffset);
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
