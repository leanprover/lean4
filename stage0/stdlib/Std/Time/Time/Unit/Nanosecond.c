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
uint8_t l_Std_Time_Nanosecond_instDecidableEqOrdinal___aux__1(lean_object* v_a_29_, lean_object* v_b_30_){
_start:
{
uint8_t v___x_31_; 
v___x_31_ = lean_int_dec_eq(v_a_29_, v_b_30_);
return v___x_31_;
}
}
LEAN_EXPORT void l_Std_Time_Nanosecond_instDecidableEqOrdinal___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_29_ = stack[0].m_obj;
lean_object* v_b_30_ = stack[1].m_obj;
uint8_t v_res_32_;
v_res_32_ = l_Std_Time_Nanosecond_instDecidableEqOrdinal___aux__1(v_a_29_, v_b_30_);
stack->m_num = v_res_32_;
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqOrdinal___aux__1___boxed(lean_object* v_a_33_, lean_object* v_b_34_){
_start:
{
uint8_t v_res_35_; lean_object* v_r_36_; 
v_res_35_ = l_Std_Time_Nanosecond_instDecidableEqOrdinal___aux__1(v_a_33_, v_b_34_);
lean_dec(v_b_34_);
lean_dec(v_a_33_);
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
uint8_t l_Std_Time_Nanosecond_instDecidableEqOrdinal(lean_object* v_a_37_, lean_object* v_b_38_){
_start:
{
uint8_t v___x_39_; 
v___x_39_ = lean_int_dec_eq(v_a_37_, v_b_38_);
return v___x_39_;
}
}
LEAN_EXPORT void l_Std_Time_Nanosecond_instDecidableEqOrdinal_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_37_ = stack[0].m_obj;
lean_object* v_b_38_ = stack[1].m_obj;
uint8_t v_res_40_;
v_res_40_ = l_Std_Time_Nanosecond_instDecidableEqOrdinal(v_a_37_, v_b_38_);
stack->m_num = v_res_40_;
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqOrdinal___boxed(lean_object* v_a_41_, lean_object* v_b_42_){
_start:
{
uint8_t v_res_43_; lean_object* v_r_44_; 
v_res_43_ = l_Std_Time_Nanosecond_instDecidableEqOrdinal(v_a_41_, v_b_42_);
lean_dec(v_b_42_);
lean_dec(v_a_41_);
v_r_44_ = lean_box(v_res_43_);
return v_r_44_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instLEOrdinal(void){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_box(0);
return v___x_45_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instLTOrdinal(void){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_box(0);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instOfNatOrdinal(lean_object* v_n_47_){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_48_ = lean_unsigned_to_nat(1000000000u);
v___x_49_ = lean_nat_mod(v_n_47_, v___x_48_);
v___x_50_ = lean_nat_to_int(v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instOfNatOrdinal___boxed(lean_object* v_n_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Std_Time_Nanosecond_instOfNatOrdinal(v_n_51_);
lean_dec(v_n_51_);
return v_res_52_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__0(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_unsigned_to_nat(0u);
v___x_54_ = lean_nat_to_int(v___x_53_);
return v___x_54_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOrdinal(void){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lean_obj_once(&l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__0, &l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__0);
return v___x_55_;
}
}
uint8_t l_Std_Time_Nanosecond_instDecidableLeOrdinal___aux__1(lean_object* v_x_56_, lean_object* v_y_57_){
_start:
{
uint8_t v___x_58_; 
v___x_58_ = lean_int_dec_le(v_x_56_, v_y_57_);
return v___x_58_;
}
}
LEAN_EXPORT void l_Std_Time_Nanosecond_instDecidableLeOrdinal___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_56_ = stack[0].m_obj;
lean_object* v_y_57_ = stack[1].m_obj;
uint8_t v_res_59_;
v_res_59_ = l_Std_Time_Nanosecond_instDecidableLeOrdinal___aux__1(v_x_56_, v_y_57_);
stack->m_num = v_res_59_;
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeOrdinal___aux__1___boxed(lean_object* v_x_60_, lean_object* v_y_61_){
_start:
{
uint8_t v_res_62_; lean_object* v_r_63_; 
v_res_62_ = l_Std_Time_Nanosecond_instDecidableLeOrdinal___aux__1(v_x_60_, v_y_61_);
lean_dec(v_y_61_);
lean_dec(v_x_60_);
v_r_63_ = lean_box(v_res_62_);
return v_r_63_;
}
}
uint8_t l_Std_Time_Nanosecond_instDecidableLeOrdinal(lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
uint8_t v___x_66_; 
v___x_66_ = lean_int_dec_le(v___y_64_, v___y_65_);
return v___x_66_;
}
}
LEAN_EXPORT void l_Std_Time_Nanosecond_instDecidableLeOrdinal_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_64_ = stack[0].m_obj;
lean_object* v___y_65_ = stack[1].m_obj;
uint8_t v_res_67_;
v_res_67_ = l_Std_Time_Nanosecond_instDecidableLeOrdinal(v___y_64_, v___y_65_);
stack->m_num = v_res_67_;
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeOrdinal___boxed(lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
uint8_t v_res_70_; lean_object* v_r_71_; 
v_res_70_ = l_Std_Time_Nanosecond_instDecidableLeOrdinal(v___y_68_, v___y_69_);
lean_dec(v___y_69_);
lean_dec(v___y_68_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
uint8_t l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1(lean_object* v_x_72_, lean_object* v_y_73_){
_start:
{
uint8_t v___x_74_; 
v___x_74_ = lean_int_dec_lt(v_x_72_, v_y_73_);
return v___x_74_;
}
}
LEAN_EXPORT void l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_72_ = stack[0].m_obj;
lean_object* v_y_73_ = stack[1].m_obj;
uint8_t v_res_75_;
v_res_75_ = l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1(v_x_72_, v_y_73_);
stack->m_num = v_res_75_;
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1___boxed(lean_object* v_x_76_, lean_object* v_y_77_){
_start:
{
uint8_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1(v_x_76_, v_y_77_);
lean_dec(v_y_77_);
lean_dec(v_x_76_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
uint8_t l_Std_Time_Nanosecond_instDecidableLtOrdinal(lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
uint8_t v___x_82_; 
v___x_82_ = lean_int_dec_lt(v___y_80_, v___y_81_);
return v___x_82_;
}
}
LEAN_EXPORT void l_Std_Time_Nanosecond_instDecidableLtOrdinal_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_80_ = stack[0].m_obj;
lean_object* v___y_81_ = stack[1].m_obj;
uint8_t v_res_83_;
v_res_83_ = l_Std_Time_Nanosecond_instDecidableLtOrdinal(v___y_80_, v___y_81_);
stack->m_num = v_res_83_;
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtOrdinal___boxed(lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l_Std_Time_Nanosecond_instDecidableLtOrdinal(v___y_84_, v___y_85_);
lean_dec(v___y_85_);
lean_dec(v___y_84_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
uint8_t l_Std_Time_Nanosecond_instOrdOrdinal___aux__1(lean_object* v_x_88_, lean_object* v_y_89_){
_start:
{
uint8_t v___x_90_; 
v___x_90_ = lean_int_dec_lt(v_x_88_, v_y_89_);
if (v___x_90_ == 0)
{
uint8_t v___x_91_; 
v___x_91_ = lean_int_dec_eq(v_x_88_, v_y_89_);
if (v___x_91_ == 0)
{
uint8_t v___x_92_; 
v___x_92_ = 2;
return v___x_92_;
}
else
{
uint8_t v___x_93_; 
v___x_93_ = 1;
return v___x_93_;
}
}
else
{
uint8_t v___x_94_; 
v___x_94_ = 0;
return v___x_94_;
}
}
}
LEAN_EXPORT void l_Std_Time_Nanosecond_instOrdOrdinal___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_88_ = stack[0].m_obj;
lean_object* v_y_89_ = stack[1].m_obj;
uint8_t v_res_95_;
v_res_95_ = l_Std_Time_Nanosecond_instOrdOrdinal___aux__1(v_x_88_, v_y_89_);
stack->m_num = v_res_95_;
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instOrdOrdinal___aux__1___boxed(lean_object* v_x_96_, lean_object* v_y_97_){
_start:
{
uint8_t v_res_98_; lean_object* v_r_99_; 
v_res_98_ = l_Std_Time_Nanosecond_instOrdOrdinal___aux__1(v_x_96_, v_y_97_);
lean_dec(v_y_97_);
lean_dec(v_x_96_);
v_r_99_ = lean_box(v_res_98_);
return v_r_99_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instReprOffset___aux__1(lean_object* v_x_102_, lean_object* v_p_103_){
_start:
{
lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_104_ = lean_obj_once(&l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0);
v___x_105_ = lean_int_dec_lt(v_x_102_, v___x_104_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = l_Int_repr(v_x_102_);
v___x_107_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
return v___x_107_;
}
else
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_108_ = l_Int_repr(v_x_102_);
v___x_109_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
v___x_110_ = l_Repr_addAppParen(v___x_109_, v_p_103_);
return v___x_110_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instReprOffset___aux__1___boxed(lean_object* v_x_111_, lean_object* v_p_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Std_Time_Nanosecond_instReprOffset___aux__1(v_x_111_, v_p_112_);
lean_dec(v_p_112_);
lean_dec(v_x_111_);
return v_res_113_;
}
}
uint8_t l_Std_Time_Nanosecond_instDecidableEqOffset___aux__1(lean_object* v_a_115_, lean_object* v_b_116_){
_start:
{
uint8_t v___x_117_; 
v___x_117_ = lean_int_dec_eq(v_a_115_, v_b_116_);
return v___x_117_;
}
}
LEAN_EXPORT void l_Std_Time_Nanosecond_instDecidableEqOffset___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_115_ = stack[0].m_obj;
lean_object* v_b_116_ = stack[1].m_obj;
uint8_t v_res_118_;
v_res_118_ = l_Std_Time_Nanosecond_instDecidableEqOffset___aux__1(v_a_115_, v_b_116_);
stack->m_num = v_res_118_;
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqOffset___aux__1___boxed(lean_object* v_a_119_, lean_object* v_b_120_){
_start:
{
uint8_t v_res_121_; lean_object* v_r_122_; 
v_res_121_ = l_Std_Time_Nanosecond_instDecidableEqOffset___aux__1(v_a_119_, v_b_120_);
lean_dec(v_b_120_);
lean_dec(v_a_119_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Nanosecond_instDecidableEqOffset___aux__1_spec__0_spec__0(lean_object* v_a_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = lean_nat_to_int(v_a_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Nanosecond_instDecidableEqOffset___aux__1_spec__0(lean_object* v_a_125_){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_nat_to_int(v_a_125_);
v___x_127_ = l_Rat_ofInt(v___x_126_);
return v___x_127_;
}
}
uint8_t l_Std_Time_Nanosecond_instDecidableEqOffset(lean_object* v_a_128_, lean_object* v_b_129_){
_start:
{
uint8_t v___x_130_; 
v___x_130_ = lean_int_dec_eq(v_a_128_, v_b_129_);
return v___x_130_;
}
}
LEAN_EXPORT void l_Std_Time_Nanosecond_instDecidableEqOffset_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_128_ = stack[0].m_obj;
lean_object* v_b_129_ = stack[1].m_obj;
uint8_t v_res_131_;
v_res_131_ = l_Std_Time_Nanosecond_instDecidableEqOffset(v_a_128_, v_b_129_);
stack->m_num = v_res_131_;
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqOffset___boxed(lean_object* v_a_132_, lean_object* v_b_133_){
_start:
{
uint8_t v_res_134_; lean_object* v_r_135_; 
v_res_134_ = l_Std_Time_Nanosecond_instDecidableEqOffset(v_a_132_, v_b_133_);
lean_dec(v_b_133_);
lean_dec(v_a_132_);
v_r_135_ = lean_box(v_res_134_);
return v_r_135_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__0(void){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Std_Time_Internal_instInhabitedUnitVal_default___redArg();
return v___x_136_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOffset___aux__1(void){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = lean_obj_once(&l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__0, &l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__0);
return v___x_137_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOffset(void){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = lean_obj_once(&l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__0, &l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__0);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instAddOffset___aux__1(lean_object* v_u1_139_, lean_object* v_u2_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = lean_int_add(v_u1_139_, v_u2_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instAddOffset___aux__1___boxed(lean_object* v_u1_142_, lean_object* v_u2_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Std_Time_Nanosecond_instAddOffset___aux__1(v_u1_142_, v_u2_143_);
lean_dec(v_u2_143_);
lean_dec(v_u1_142_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instSubOffset___aux__1(lean_object* v_u1_147_, lean_object* v_u2_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = lean_int_sub(v_u1_147_, v_u2_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instSubOffset___aux__1___boxed(lean_object* v_u1_150_, lean_object* v_u2_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Std_Time_Nanosecond_instSubOffset___aux__1(v_u1_150_, v_u2_151_);
lean_dec(v_u2_151_);
lean_dec(v_u1_150_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instNegOffset___aux__1(lean_object* v_x_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = lean_int_neg(v_x_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instNegOffset___aux__1___boxed(lean_object* v_x_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Std_Time_Nanosecond_instNegOffset___aux__1(v_x_157_);
lean_dec(v_x_157_);
return v_res_158_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instLEOffset(void){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = lean_box(0);
return v___x_161_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instLTOffset(void){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = lean_box(0);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instToStringOffset___aux__1(lean_object* v_n_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Int_repr(v_n_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instToStringOffset___aux__1___boxed(lean_object* v_n_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Std_Time_Nanosecond_instToStringOffset___aux__1(v_n_165_);
lean_dec(v_n_165_);
return v_res_166_;
}
}
uint8_t l_Std_Time_Nanosecond_instDecidableLeOffset___aux__1(lean_object* v_x_169_, lean_object* v_y_170_){
_start:
{
uint8_t v___x_171_; 
v___x_171_ = lean_int_dec_le(v_x_169_, v_y_170_);
return v___x_171_;
}
}
LEAN_EXPORT void l_Std_Time_Nanosecond_instDecidableLeOffset___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_169_ = stack[0].m_obj;
lean_object* v_y_170_ = stack[1].m_obj;
uint8_t v_res_172_;
v_res_172_ = l_Std_Time_Nanosecond_instDecidableLeOffset___aux__1(v_x_169_, v_y_170_);
stack->m_num = v_res_172_;
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeOffset___aux__1___boxed(lean_object* v_x_173_, lean_object* v_y_174_){
_start:
{
uint8_t v_res_175_; lean_object* v_r_176_; 
v_res_175_ = l_Std_Time_Nanosecond_instDecidableLeOffset___aux__1(v_x_173_, v_y_174_);
lean_dec(v_y_174_);
lean_dec(v_x_173_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
uint8_t l_Std_Time_Nanosecond_instDecidableLeOffset(lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
uint8_t v___x_179_; 
v___x_179_ = lean_int_dec_le(v___y_177_, v___y_178_);
return v___x_179_;
}
}
LEAN_EXPORT void l_Std_Time_Nanosecond_instDecidableLeOffset_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_177_ = stack[0].m_obj;
lean_object* v___y_178_ = stack[1].m_obj;
uint8_t v_res_180_;
v_res_180_ = l_Std_Time_Nanosecond_instDecidableLeOffset(v___y_177_, v___y_178_);
stack->m_num = v_res_180_;
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeOffset___boxed(lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
uint8_t v_res_183_; lean_object* v_r_184_; 
v_res_183_ = l_Std_Time_Nanosecond_instDecidableLeOffset(v___y_181_, v___y_182_);
lean_dec(v___y_182_);
lean_dec(v___y_181_);
v_r_184_ = lean_box(v_res_183_);
return v_r_184_;
}
}
uint8_t l_Std_Time_Nanosecond_instDecidableLtOffset___aux__1(lean_object* v_x_185_, lean_object* v_y_186_){
_start:
{
uint8_t v___x_187_; 
v___x_187_ = lean_int_dec_lt(v_x_185_, v_y_186_);
return v___x_187_;
}
}
LEAN_EXPORT void l_Std_Time_Nanosecond_instDecidableLtOffset___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_185_ = stack[0].m_obj;
lean_object* v_y_186_ = stack[1].m_obj;
uint8_t v_res_188_;
v_res_188_ = l_Std_Time_Nanosecond_instDecidableLtOffset___aux__1(v_x_185_, v_y_186_);
stack->m_num = v_res_188_;
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtOffset___aux__1___boxed(lean_object* v_x_189_, lean_object* v_y_190_){
_start:
{
uint8_t v_res_191_; lean_object* v_r_192_; 
v_res_191_ = l_Std_Time_Nanosecond_instDecidableLtOffset___aux__1(v_x_189_, v_y_190_);
lean_dec(v_y_190_);
lean_dec(v_x_189_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
uint8_t l_Std_Time_Nanosecond_instDecidableLtOffset(lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
uint8_t v___x_195_; 
v___x_195_ = lean_int_dec_lt(v___y_193_, v___y_194_);
return v___x_195_;
}
}
LEAN_EXPORT void l_Std_Time_Nanosecond_instDecidableLtOffset_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_193_ = stack[0].m_obj;
lean_object* v___y_194_ = stack[1].m_obj;
uint8_t v_res_196_;
v_res_196_ = l_Std_Time_Nanosecond_instDecidableLtOffset(v___y_193_, v___y_194_);
stack->m_num = v_res_196_;
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtOffset___boxed(lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
uint8_t v_res_199_; lean_object* v_r_200_; 
v_res_199_ = l_Std_Time_Nanosecond_instDecidableLtOffset(v___y_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec(v___y_197_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instOfNatOffset(lean_object* v_n_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = lean_nat_to_int(v_n_201_);
return v___x_202_;
}
}
uint8_t l_Std_Time_Nanosecond_instOrdOffset___aux__1(lean_object* v_x_203_, lean_object* v_y_204_){
_start:
{
uint8_t v___x_205_; 
v___x_205_ = lean_int_dec_lt(v_x_203_, v_y_204_);
if (v___x_205_ == 0)
{
uint8_t v___x_206_; 
v___x_206_ = lean_int_dec_eq(v_x_203_, v_y_204_);
if (v___x_206_ == 0)
{
uint8_t v___x_207_; 
v___x_207_ = 2;
return v___x_207_;
}
else
{
uint8_t v___x_208_; 
v___x_208_ = 1;
return v___x_208_;
}
}
else
{
uint8_t v___x_209_; 
v___x_209_ = 0;
return v___x_209_;
}
}
}
LEAN_EXPORT void l_Std_Time_Nanosecond_instOrdOffset___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_203_ = stack[0].m_obj;
lean_object* v_y_204_ = stack[1].m_obj;
uint8_t v_res_210_;
v_res_210_ = l_Std_Time_Nanosecond_instOrdOffset___aux__1(v_x_203_, v_y_204_);
stack->m_num = v_res_210_;
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instOrdOffset___aux__1___boxed(lean_object* v_x_211_, lean_object* v_y_212_){
_start:
{
uint8_t v_res_213_; lean_object* v_r_214_; 
v_res_213_ = l_Std_Time_Nanosecond_instOrdOffset___aux__1(v_x_211_, v_y_212_);
lean_dec(v_y_212_);
lean_dec(v_x_211_);
v_r_214_ = lean_box(v_res_213_);
return v_r_214_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofNat(lean_object* v_data_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = lean_nat_to_int(v_data_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofInt(lean_object* v_data_219_){
_start:
{
lean_inc(v_data_219_);
return v_data_219_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofInt___boxed(lean_object* v_data_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Std_Time_Nanosecond_Offset_ofInt(v_data_220_);
lean_dec(v_data_220_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instReprSpan___aux__1(lean_object* v_n_222_, lean_object* v_a_223_){
_start:
{
lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_224_ = lean_obj_once(&l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0);
v___x_225_ = lean_int_dec_lt(v_n_222_, v___x_224_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = l_Int_repr(v_n_222_);
v___x_227_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
else
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_228_ = l_Int_repr(v_n_222_);
v___x_229_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
v___x_230_ = l_Repr_addAppParen(v___x_229_, v_a_223_);
return v___x_230_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instReprSpan___aux__1___boxed(lean_object* v_n_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Std_Time_Nanosecond_instReprSpan___aux__1(v_n_231_, v_a_232_);
lean_dec(v_a_232_);
lean_dec(v_n_231_);
return v_res_233_;
}
}
uint8_t l_Std_Time_Nanosecond_instDecidableEqSpan___aux__1(lean_object* v_a_235_, lean_object* v_b_236_){
_start:
{
uint8_t v___x_237_; 
v___x_237_ = lean_int_dec_eq(v_a_235_, v_b_236_);
return v___x_237_;
}
}
LEAN_EXPORT void l_Std_Time_Nanosecond_instDecidableEqSpan___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_235_ = stack[0].m_obj;
lean_object* v_b_236_ = stack[1].m_obj;
uint8_t v_res_238_;
v_res_238_ = l_Std_Time_Nanosecond_instDecidableEqSpan___aux__1(v_a_235_, v_b_236_);
stack->m_num = v_res_238_;
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqSpan___aux__1___boxed(lean_object* v_a_239_, lean_object* v_b_240_){
_start:
{
uint8_t v_res_241_; lean_object* v_r_242_; 
v_res_241_ = l_Std_Time_Nanosecond_instDecidableEqSpan___aux__1(v_a_239_, v_b_240_);
lean_dec(v_b_240_);
lean_dec(v_a_239_);
v_r_242_ = lean_box(v_res_241_);
return v_r_242_;
}
}
uint8_t l_Std_Time_Nanosecond_instDecidableEqSpan(lean_object* v_a_243_, lean_object* v_b_244_){
_start:
{
uint8_t v___x_245_; 
v___x_245_ = lean_int_dec_eq(v_a_243_, v_b_244_);
return v___x_245_;
}
}
LEAN_EXPORT void l_Std_Time_Nanosecond_instDecidableEqSpan_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_243_ = stack[0].m_obj;
lean_object* v_b_244_ = stack[1].m_obj;
uint8_t v_res_246_;
v_res_246_ = l_Std_Time_Nanosecond_instDecidableEqSpan(v_a_243_, v_b_244_);
stack->m_num = v_res_246_;
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqSpan___boxed(lean_object* v_a_247_, lean_object* v_b_248_){
_start:
{
uint8_t v_res_249_; lean_object* v_r_250_; 
v_res_249_ = l_Std_Time_Nanosecond_instDecidableEqSpan(v_a_247_, v_b_248_);
lean_dec(v_b_248_);
lean_dec(v_a_247_);
v_r_250_ = lean_box(v_res_249_);
return v_r_250_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instLESpan(void){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = lean_box(0);
return v___x_251_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instLTSpan(void){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = lean_box(0);
return v___x_252_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedSpan(void){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = lean_obj_once(&l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0);
return v___x_253_;
}
}
uint8_t l_Std_Time_Nanosecond_instDecidableLeSpan___aux__1(lean_object* v_x_254_, lean_object* v_y_255_){
_start:
{
uint8_t v___x_256_; 
v___x_256_ = lean_int_dec_le(v_x_254_, v_y_255_);
return v___x_256_;
}
}
LEAN_EXPORT void l_Std_Time_Nanosecond_instDecidableLeSpan___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_254_ = stack[0].m_obj;
lean_object* v_y_255_ = stack[1].m_obj;
uint8_t v_res_257_;
v_res_257_ = l_Std_Time_Nanosecond_instDecidableLeSpan___aux__1(v_x_254_, v_y_255_);
stack->m_num = v_res_257_;
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeSpan___aux__1___boxed(lean_object* v_x_258_, lean_object* v_y_259_){
_start:
{
uint8_t v_res_260_; lean_object* v_r_261_; 
v_res_260_ = l_Std_Time_Nanosecond_instDecidableLeSpan___aux__1(v_x_258_, v_y_259_);
lean_dec(v_y_259_);
lean_dec(v_x_258_);
v_r_261_ = lean_box(v_res_260_);
return v_r_261_;
}
}
uint8_t l_Std_Time_Nanosecond_instDecidableLeSpan(lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
uint8_t v___x_264_; 
v___x_264_ = lean_int_dec_le(v___y_262_, v___y_263_);
return v___x_264_;
}
}
LEAN_EXPORT void l_Std_Time_Nanosecond_instDecidableLeSpan_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_262_ = stack[0].m_obj;
lean_object* v___y_263_ = stack[1].m_obj;
uint8_t v_res_265_;
v_res_265_ = l_Std_Time_Nanosecond_instDecidableLeSpan(v___y_262_, v___y_263_);
stack->m_num = v_res_265_;
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeSpan___boxed(lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
uint8_t v_res_268_; lean_object* v_r_269_; 
v_res_268_ = l_Std_Time_Nanosecond_instDecidableLeSpan(v___y_266_, v___y_267_);
lean_dec(v___y_267_);
lean_dec(v___y_266_);
v_r_269_ = lean_box(v_res_268_);
return v_r_269_;
}
}
uint8_t l_Std_Time_Nanosecond_instDecidableLtSpan___aux__1(lean_object* v_x_270_, lean_object* v_y_271_){
_start:
{
uint8_t v___x_272_; 
v___x_272_ = lean_int_dec_lt(v_x_270_, v_y_271_);
return v___x_272_;
}
}
LEAN_EXPORT void l_Std_Time_Nanosecond_instDecidableLtSpan___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_270_ = stack[0].m_obj;
lean_object* v_y_271_ = stack[1].m_obj;
uint8_t v_res_273_;
v_res_273_ = l_Std_Time_Nanosecond_instDecidableLtSpan___aux__1(v_x_270_, v_y_271_);
stack->m_num = v_res_273_;
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtSpan___aux__1___boxed(lean_object* v_x_274_, lean_object* v_y_275_){
_start:
{
uint8_t v_res_276_; lean_object* v_r_277_; 
v_res_276_ = l_Std_Time_Nanosecond_instDecidableLtSpan___aux__1(v_x_274_, v_y_275_);
lean_dec(v_y_275_);
lean_dec(v_x_274_);
v_r_277_ = lean_box(v_res_276_);
return v_r_277_;
}
}
uint8_t l_Std_Time_Nanosecond_instDecidableLtSpan(lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
uint8_t v___x_280_; 
v___x_280_ = lean_int_dec_lt(v___y_278_, v___y_279_);
return v___x_280_;
}
}
LEAN_EXPORT void l_Std_Time_Nanosecond_instDecidableLtSpan_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_278_ = stack[0].m_obj;
lean_object* v___y_279_ = stack[1].m_obj;
uint8_t v_res_281_;
v_res_281_ = l_Std_Time_Nanosecond_instDecidableLtSpan(v___y_278_, v___y_279_);
stack->m_num = v_res_281_;
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtSpan___boxed(lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
uint8_t v_res_284_; lean_object* v_r_285_; 
v_res_284_ = l_Std_Time_Nanosecond_instDecidableLtSpan(v___y_282_, v___y_283_);
lean_dec(v___y_283_);
lean_dec(v___y_282_);
v_r_285_ = lean_box(v_res_284_);
return v_r_285_;
}
}
uint8_t l_Std_Time_Nanosecond_instOrdSpan___aux__1(lean_object* v_x_286_, lean_object* v_y_287_){
_start:
{
uint8_t v___x_288_; 
v___x_288_ = lean_int_dec_lt(v_x_286_, v_y_287_);
if (v___x_288_ == 0)
{
uint8_t v___x_289_; 
v___x_289_ = lean_int_dec_eq(v_x_286_, v_y_287_);
if (v___x_289_ == 0)
{
uint8_t v___x_290_; 
v___x_290_ = 2;
return v___x_290_;
}
else
{
uint8_t v___x_291_; 
v___x_291_ = 1;
return v___x_291_;
}
}
else
{
uint8_t v___x_292_; 
v___x_292_ = 0;
return v___x_292_;
}
}
}
LEAN_EXPORT void l_Std_Time_Nanosecond_instOrdSpan___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_286_ = stack[0].m_obj;
lean_object* v_y_287_ = stack[1].m_obj;
uint8_t v_res_293_;
v_res_293_ = l_Std_Time_Nanosecond_instOrdSpan___aux__1(v_x_286_, v_y_287_);
stack->m_num = v_res_293_;
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instOrdSpan___aux__1___boxed(lean_object* v_x_294_, lean_object* v_y_295_){
_start:
{
uint8_t v_res_296_; lean_object* v_r_297_; 
v_res_296_ = l_Std_Time_Nanosecond_instOrdSpan___aux__1(v_x_294_, v_y_295_);
lean_dec(v_y_295_);
lean_dec(v_x_294_);
v_r_297_ = lean_box(v_res_296_);
return v_r_297_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Span_toOffset(lean_object* v_span_300_){
_start:
{
lean_inc(v_span_300_);
return v_span_300_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Span_toOffset___boxed(lean_object* v_span_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Std_Time_Nanosecond_Span_toOffset(v_span_301_);
lean_dec(v_span_301_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instReprOfDay___aux__1(lean_object* v_n_303_, lean_object* v_a_304_){
_start:
{
lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_305_ = lean_obj_once(&l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0);
v___x_306_ = lean_int_dec_lt(v_n_303_, v___x_305_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = l_Int_repr(v_n_303_);
v___x_308_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
return v___x_308_;
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = l_Int_repr(v_n_303_);
v___x_310_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
v___x_311_ = l_Repr_addAppParen(v___x_310_, v_a_304_);
return v___x_311_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instReprOfDay___aux__1___boxed(lean_object* v_n_312_, lean_object* v_a_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Std_Time_Nanosecond_Ordinal_instReprOfDay___aux__1(v_n_312_, v_a_313_);
lean_dec(v_a_313_);
lean_dec(v_n_312_);
return v_res_314_;
}
}
uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay___aux__1(lean_object* v_a_316_, lean_object* v_b_317_){
_start:
{
uint8_t v___x_318_; 
v___x_318_ = lean_int_dec_eq(v_a_316_, v_b_317_);
return v___x_318_;
}
}
LEAN_EXPORT void l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_316_ = stack[0].m_obj;
lean_object* v_b_317_ = stack[1].m_obj;
uint8_t v_res_319_;
v_res_319_ = l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay___aux__1(v_a_316_, v_b_317_);
stack->m_num = v_res_319_;
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay___aux__1___boxed(lean_object* v_a_320_, lean_object* v_b_321_){
_start:
{
uint8_t v_res_322_; lean_object* v_r_323_; 
v_res_322_ = l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay___aux__1(v_a_320_, v_b_321_);
lean_dec(v_b_321_);
lean_dec(v_a_320_);
v_r_323_ = lean_box(v_res_322_);
return v_r_323_;
}
}
uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay(lean_object* v_a_324_, lean_object* v_b_325_){
_start:
{
uint8_t v___x_326_; 
v___x_326_ = lean_int_dec_eq(v_a_324_, v_b_325_);
return v___x_326_;
}
}
LEAN_EXPORT void l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_324_ = stack[0].m_obj;
lean_object* v_b_325_ = stack[1].m_obj;
uint8_t v_res_327_;
v_res_327_ = l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay(v_a_324_, v_b_325_);
stack->m_num = v_res_327_;
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay___boxed(lean_object* v_a_328_, lean_object* v_b_329_){
_start:
{
uint8_t v_res_330_; lean_object* v_r_331_; 
v_res_330_ = l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay(v_a_328_, v_b_329_);
lean_dec(v_b_329_);
lean_dec(v_a_328_);
v_r_331_ = lean_box(v_res_330_);
return v_r_331_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_Ordinal_instLEOfDay(void){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = lean_box(0);
return v___x_332_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_Ordinal_instLTOfDay(void){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = lean_box(0);
return v___x_333_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_Ordinal_instInhabitedOfDay(void){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = lean_obj_once(&l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0);
return v___x_334_;
}
}
uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay___aux__1(lean_object* v_x_335_, lean_object* v_y_336_){
_start:
{
uint8_t v___x_337_; 
v___x_337_ = lean_int_dec_le(v_x_335_, v_y_336_);
return v___x_337_;
}
}
LEAN_EXPORT void l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_335_ = stack[0].m_obj;
lean_object* v_y_336_ = stack[1].m_obj;
uint8_t v_res_338_;
v_res_338_ = l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay___aux__1(v_x_335_, v_y_336_);
stack->m_num = v_res_338_;
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay___aux__1___boxed(lean_object* v_x_339_, lean_object* v_y_340_){
_start:
{
uint8_t v_res_341_; lean_object* v_r_342_; 
v_res_341_ = l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay___aux__1(v_x_339_, v_y_340_);
lean_dec(v_y_340_);
lean_dec(v_x_339_);
v_r_342_ = lean_box(v_res_341_);
return v_r_342_;
}
}
uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay(lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
uint8_t v___x_345_; 
v___x_345_ = lean_int_dec_le(v___y_343_, v___y_344_);
return v___x_345_;
}
}
LEAN_EXPORT void l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_343_ = stack[0].m_obj;
lean_object* v___y_344_ = stack[1].m_obj;
uint8_t v_res_346_;
v_res_346_ = l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay(v___y_343_, v___y_344_);
stack->m_num = v_res_346_;
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay___boxed(lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
uint8_t v_res_349_; lean_object* v_r_350_; 
v_res_349_ = l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay(v___y_347_, v___y_348_);
lean_dec(v___y_348_);
lean_dec(v___y_347_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay___aux__1(lean_object* v_x_351_, lean_object* v_y_352_){
_start:
{
uint8_t v___x_353_; 
v___x_353_ = lean_int_dec_lt(v_x_351_, v_y_352_);
return v___x_353_;
}
}
LEAN_EXPORT void l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_351_ = stack[0].m_obj;
lean_object* v_y_352_ = stack[1].m_obj;
uint8_t v_res_354_;
v_res_354_ = l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay___aux__1(v_x_351_, v_y_352_);
stack->m_num = v_res_354_;
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay___aux__1___boxed(lean_object* v_x_355_, lean_object* v_y_356_){
_start:
{
uint8_t v_res_357_; lean_object* v_r_358_; 
v_res_357_ = l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay___aux__1(v_x_355_, v_y_356_);
lean_dec(v_y_356_);
lean_dec(v_x_355_);
v_r_358_ = lean_box(v_res_357_);
return v_r_358_;
}
}
uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay(lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
uint8_t v___x_361_; 
v___x_361_ = lean_int_dec_lt(v___y_359_, v___y_360_);
return v___x_361_;
}
}
LEAN_EXPORT void l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_359_ = stack[0].m_obj;
lean_object* v___y_360_ = stack[1].m_obj;
uint8_t v_res_362_;
v_res_362_ = l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay(v___y_359_, v___y_360_);
stack->m_num = v_res_362_;
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay___boxed(lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
uint8_t v_res_365_; lean_object* v_r_366_; 
v_res_365_ = l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay(v___y_363_, v___y_364_);
lean_dec(v___y_364_);
lean_dec(v___y_363_);
v_r_366_ = lean_box(v_res_365_);
return v_r_366_;
}
}
uint8_t l_Std_Time_Nanosecond_Ordinal_instOrdOfDay___aux__1(lean_object* v_x_367_, lean_object* v_y_368_){
_start:
{
uint8_t v___x_369_; 
v___x_369_ = lean_int_dec_lt(v_x_367_, v_y_368_);
if (v___x_369_ == 0)
{
uint8_t v___x_370_; 
v___x_370_ = lean_int_dec_eq(v_x_367_, v_y_368_);
if (v___x_370_ == 0)
{
uint8_t v___x_371_; 
v___x_371_ = 2;
return v___x_371_;
}
else
{
uint8_t v___x_372_; 
v___x_372_ = 1;
return v___x_372_;
}
}
else
{
uint8_t v___x_373_; 
v___x_373_ = 0;
return v___x_373_;
}
}
}
LEAN_EXPORT void l_Std_Time_Nanosecond_Ordinal_instOrdOfDay___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_367_ = stack[0].m_obj;
lean_object* v_y_368_ = stack[1].m_obj;
uint8_t v_res_374_;
v_res_374_ = l_Std_Time_Nanosecond_Ordinal_instOrdOfDay___aux__1(v_x_367_, v_y_368_);
stack->m_num = v_res_374_;
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instOrdOfDay___aux__1___boxed(lean_object* v_x_375_, lean_object* v_y_376_){
_start:
{
uint8_t v_res_377_; lean_object* v_r_378_; 
v_res_377_ = l_Std_Time_Nanosecond_Ordinal_instOrdOfDay___aux__1(v_x_375_, v_y_376_);
lean_dec(v_y_376_);
lean_dec(v_x_375_);
v_r_378_ = lean_box(v_res_377_);
return v_r_378_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofInt___redArg(lean_object* v_data_381_){
_start:
{
lean_inc(v_data_381_);
return v_data_381_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofInt___redArg___boxed(lean_object* v_data_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Std_Time_Nanosecond_Ordinal_ofInt___redArg(v_data_382_);
lean_dec(v_data_382_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofInt(lean_object* v_data_384_, lean_object* v_h_385_){
_start:
{
lean_inc(v_data_384_);
return v_data_384_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofInt___boxed(lean_object* v_data_386_, lean_object* v_h_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Std_Time_Nanosecond_Ordinal_ofInt(v_data_386_, v_h_387_);
lean_dec(v_data_386_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofNat___redArg(lean_object* v_data_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = lean_nat_to_int(v_data_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofNat(lean_object* v_data_391_, lean_object* v_h_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = lean_nat_to_int(v_data_391_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofFin(lean_object* v_data_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = lean_nat_to_int(v_data_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_toOffset(lean_object* v_ordinal_396_){
_start:
{
lean_inc(v_ordinal_396_);
return v_ordinal_396_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_toOffset___boxed(lean_object* v_ordinal_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Std_Time_Nanosecond_Ordinal_toOffset(v_ordinal_397_);
lean_dec(v_ordinal_397_);
return v_res_398_;
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
