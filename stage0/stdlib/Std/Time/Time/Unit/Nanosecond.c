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
lean_object* lean_int_mul(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_instInhabitedUnitVal_default___redArg();
lean_object* l_Int_neg___boxed(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instHMulIntOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instHMulIntOffset___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Nanosecond_instHMulIntOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Nanosecond_instHMulIntOffset___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Nanosecond_instHMulIntOffset___closed__0 = (const lean_object*)&l_Std_Time_Nanosecond_instHMulIntOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Nanosecond_instHMulIntOffset = (const lean_object*)&l_Std_Time_Nanosecond_instHMulIntOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instHMulOffsetInt___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instHMulOffsetInt___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Nanosecond_instHMulOffsetInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Nanosecond_instHMulOffsetInt___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Nanosecond_instHMulOffsetInt___closed__0 = (const lean_object*)&l_Std_Time_Nanosecond_instHMulOffsetInt___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Nanosecond_instHMulOffsetInt = (const lean_object*)&l_Std_Time_Nanosecond_instHMulOffsetInt___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instHMulNatOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instHMulNatOffset___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Nanosecond_instHMulNatOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Nanosecond_instHMulNatOffset___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Nanosecond_instHMulNatOffset___closed__0 = (const lean_object*)&l_Std_Time_Nanosecond_instHMulNatOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Nanosecond_instHMulNatOffset = (const lean_object*)&l_Std_Time_Nanosecond_instHMulNatOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instHMulOffsetNat___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instHMulOffsetNat___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Nanosecond_instHMulOffsetNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Nanosecond_instHMulOffsetNat___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Nanosecond_instHMulOffsetNat___closed__0 = (const lean_object*)&l_Std_Time_Nanosecond_instHMulOffsetNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Nanosecond_instHMulOffsetNat = (const lean_object*)&l_Std_Time_Nanosecond_instHMulOffsetNat___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instHDivOffsetInt___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instHDivOffsetInt___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Nanosecond_instHDivOffsetInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Nanosecond_instHDivOffsetInt___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Nanosecond_instHDivOffsetInt___closed__0 = (const lean_object*)&l_Std_Time_Nanosecond_instHDivOffsetInt___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Nanosecond_instHDivOffsetInt = (const lean_object*)&l_Std_Time_Nanosecond_instHDivOffsetInt___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instHDivOffsetNat___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instHDivOffsetNat___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Nanosecond_instHDivOffsetNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Nanosecond_instHDivOffsetNat___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Nanosecond_instHDivOffsetNat___closed__0 = (const lean_object*)&l_Std_Time_Nanosecond_instHDivOffsetNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Nanosecond_instHDivOffsetNat = (const lean_object*)&l_Std_Time_Nanosecond_instHDivOffsetNat___closed__0_value;
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
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instHMulIntOffset___aux__1(lean_object* v_n_203_, lean_object* v_x_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = lean_int_mul(v_n_203_, v_x_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instHMulIntOffset___aux__1___boxed(lean_object* v_n_206_, lean_object* v_x_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Std_Time_Nanosecond_instHMulIntOffset___aux__1(v_n_206_, v_x_207_);
lean_dec(v_x_207_);
lean_dec(v_n_206_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instHMulOffsetInt___aux__1(lean_object* v_x_211_, lean_object* v_n_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = lean_int_mul(v_x_211_, v_n_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instHMulOffsetInt___aux__1___boxed(lean_object* v_x_214_, lean_object* v_n_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Std_Time_Nanosecond_instHMulOffsetInt___aux__1(v_x_214_, v_n_215_);
lean_dec(v_n_215_);
lean_dec(v_x_214_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instHMulNatOffset___aux__1(lean_object* v_n_219_, lean_object* v_x_220_){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_nat_to_int(v_n_219_);
v___x_222_ = lean_int_mul(v___x_221_, v_x_220_);
lean_dec(v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instHMulNatOffset___aux__1___boxed(lean_object* v_n_223_, lean_object* v_x_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Std_Time_Nanosecond_instHMulNatOffset___aux__1(v_n_223_, v_x_224_);
lean_dec(v_x_224_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instHMulOffsetNat___aux__1(lean_object* v_x_228_, lean_object* v_n_229_){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lean_nat_to_int(v_n_229_);
v___x_231_ = lean_int_mul(v_x_228_, v___x_230_);
lean_dec(v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instHMulOffsetNat___aux__1___boxed(lean_object* v_x_232_, lean_object* v_n_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Std_Time_Nanosecond_instHMulOffsetNat___aux__1(v_x_232_, v_n_233_);
lean_dec(v_x_232_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instHDivOffsetInt___aux__1(lean_object* v_x_237_, lean_object* v_n_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = lean_int_div(v_x_237_, v_n_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instHDivOffsetInt___aux__1___boxed(lean_object* v_x_240_, lean_object* v_n_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Std_Time_Nanosecond_instHDivOffsetInt___aux__1(v_x_240_, v_n_241_);
lean_dec(v_n_241_);
lean_dec(v_x_240_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instHDivOffsetNat___aux__1(lean_object* v_x_245_, lean_object* v_n_246_){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_nat_to_int(v_n_246_);
v___x_248_ = lean_int_div(v_x_245_, v___x_247_);
lean_dec(v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instHDivOffsetNat___aux__1___boxed(lean_object* v_x_249_, lean_object* v_n_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Std_Time_Nanosecond_instHDivOffsetNat___aux__1(v_x_249_, v_n_250_);
lean_dec(v_x_249_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofNat(lean_object* v_data_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = lean_nat_to_int(v_data_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofInt(lean_object* v_data_256_){
_start:
{
lean_inc(v_data_256_);
return v_data_256_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofInt___boxed(lean_object* v_data_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Std_Time_Nanosecond_Offset_ofInt(v_data_257_);
lean_dec(v_data_257_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instReprSpan___aux__1(lean_object* v_n_259_, lean_object* v_a_260_){
_start:
{
lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_261_ = lean_obj_once(&l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0);
v___x_262_ = lean_int_dec_lt(v_n_259_, v___x_261_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = l_Int_repr(v_n_259_);
v___x_264_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
return v___x_264_;
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = l_Int_repr(v_n_259_);
v___x_266_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
v___x_267_ = l_Repr_addAppParen(v___x_266_, v_a_260_);
return v___x_267_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instReprSpan___aux__1___boxed(lean_object* v_n_268_, lean_object* v_a_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Std_Time_Nanosecond_instReprSpan___aux__1(v_n_268_, v_a_269_);
lean_dec(v_a_269_);
lean_dec(v_n_268_);
return v_res_270_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableEqSpan___aux__1(lean_object* v_a_272_, lean_object* v_b_273_){
_start:
{
uint8_t v___x_274_; 
v___x_274_ = lean_int_dec_eq(v_a_272_, v_b_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqSpan___aux__1___boxed(lean_object* v_a_275_, lean_object* v_b_276_){
_start:
{
uint8_t v_res_277_; lean_object* v_r_278_; 
v_res_277_ = l_Std_Time_Nanosecond_instDecidableEqSpan___aux__1(v_a_275_, v_b_276_);
lean_dec(v_b_276_);
lean_dec(v_a_275_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableEqSpan(lean_object* v_a_279_, lean_object* v_b_280_){
_start:
{
uint8_t v___x_281_; 
v___x_281_ = lean_int_dec_eq(v_a_279_, v_b_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqSpan___boxed(lean_object* v_a_282_, lean_object* v_b_283_){
_start:
{
uint8_t v_res_284_; lean_object* v_r_285_; 
v_res_284_ = l_Std_Time_Nanosecond_instDecidableEqSpan(v_a_282_, v_b_283_);
lean_dec(v_b_283_);
lean_dec(v_a_282_);
v_r_285_ = lean_box(v_res_284_);
return v_r_285_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instLESpan(void){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = lean_box(0);
return v___x_286_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instLTSpan(void){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = lean_box(0);
return v___x_287_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedSpan(void){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = lean_obj_once(&l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0);
return v___x_288_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLeSpan___aux__1(lean_object* v_x_289_, lean_object* v_y_290_){
_start:
{
uint8_t v___x_291_; 
v___x_291_ = lean_int_dec_le(v_x_289_, v_y_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeSpan___aux__1___boxed(lean_object* v_x_292_, lean_object* v_y_293_){
_start:
{
uint8_t v_res_294_; lean_object* v_r_295_; 
v_res_294_ = l_Std_Time_Nanosecond_instDecidableLeSpan___aux__1(v_x_292_, v_y_293_);
lean_dec(v_y_293_);
lean_dec(v_x_292_);
v_r_295_ = lean_box(v_res_294_);
return v_r_295_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLeSpan(lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
uint8_t v___x_298_; 
v___x_298_ = lean_int_dec_le(v___y_296_, v___y_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeSpan___boxed(lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
uint8_t v_res_301_; lean_object* v_r_302_; 
v_res_301_ = l_Std_Time_Nanosecond_instDecidableLeSpan(v___y_299_, v___y_300_);
lean_dec(v___y_300_);
lean_dec(v___y_299_);
v_r_302_ = lean_box(v_res_301_);
return v_r_302_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLtSpan___aux__1(lean_object* v_x_303_, lean_object* v_y_304_){
_start:
{
uint8_t v___x_305_; 
v___x_305_ = lean_int_dec_lt(v_x_303_, v_y_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtSpan___aux__1___boxed(lean_object* v_x_306_, lean_object* v_y_307_){
_start:
{
uint8_t v_res_308_; lean_object* v_r_309_; 
v_res_308_ = l_Std_Time_Nanosecond_instDecidableLtSpan___aux__1(v_x_306_, v_y_307_);
lean_dec(v_y_307_);
lean_dec(v_x_306_);
v_r_309_ = lean_box(v_res_308_);
return v_r_309_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLtSpan(lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
uint8_t v___x_312_; 
v___x_312_ = lean_int_dec_lt(v___y_310_, v___y_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtSpan___boxed(lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
uint8_t v_res_315_; lean_object* v_r_316_; 
v_res_315_ = l_Std_Time_Nanosecond_instDecidableLtSpan(v___y_313_, v___y_314_);
lean_dec(v___y_314_);
lean_dec(v___y_313_);
v_r_316_ = lean_box(v_res_315_);
return v_r_316_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instOrdSpan___aux__1(lean_object* v_x_317_, lean_object* v_y_318_){
_start:
{
uint8_t v___x_319_; 
v___x_319_ = lean_int_dec_lt(v_x_317_, v_y_318_);
if (v___x_319_ == 0)
{
uint8_t v___x_320_; 
v___x_320_ = lean_int_dec_eq(v_x_317_, v_y_318_);
if (v___x_320_ == 0)
{
uint8_t v___x_321_; 
v___x_321_ = 2;
return v___x_321_;
}
else
{
uint8_t v___x_322_; 
v___x_322_ = 1;
return v___x_322_;
}
}
else
{
uint8_t v___x_323_; 
v___x_323_ = 0;
return v___x_323_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instOrdSpan___aux__1___boxed(lean_object* v_x_324_, lean_object* v_y_325_){
_start:
{
uint8_t v_res_326_; lean_object* v_r_327_; 
v_res_326_ = l_Std_Time_Nanosecond_instOrdSpan___aux__1(v_x_324_, v_y_325_);
lean_dec(v_y_325_);
lean_dec(v_x_324_);
v_r_327_ = lean_box(v_res_326_);
return v_r_327_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Span_toOffset(lean_object* v_span_330_){
_start:
{
lean_inc(v_span_330_);
return v_span_330_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Span_toOffset___boxed(lean_object* v_span_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Std_Time_Nanosecond_Span_toOffset(v_span_331_);
lean_dec(v_span_331_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instReprOfDay___aux__1(lean_object* v_n_333_, lean_object* v_a_334_){
_start:
{
lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_335_ = lean_obj_once(&l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0);
v___x_336_ = lean_int_dec_lt(v_n_333_, v___x_335_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = l_Int_repr(v_n_333_);
v___x_338_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
return v___x_338_;
}
else
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_339_ = l_Int_repr(v_n_333_);
v___x_340_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
v___x_341_ = l_Repr_addAppParen(v___x_340_, v_a_334_);
return v___x_341_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instReprOfDay___aux__1___boxed(lean_object* v_n_342_, lean_object* v_a_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Std_Time_Nanosecond_Ordinal_instReprOfDay___aux__1(v_n_342_, v_a_343_);
lean_dec(v_a_343_);
lean_dec(v_n_342_);
return v_res_344_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay___aux__1(lean_object* v_a_346_, lean_object* v_b_347_){
_start:
{
uint8_t v___x_348_; 
v___x_348_ = lean_int_dec_eq(v_a_346_, v_b_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay___aux__1___boxed(lean_object* v_a_349_, lean_object* v_b_350_){
_start:
{
uint8_t v_res_351_; lean_object* v_r_352_; 
v_res_351_ = l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay___aux__1(v_a_349_, v_b_350_);
lean_dec(v_b_350_);
lean_dec(v_a_349_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay(lean_object* v_a_353_, lean_object* v_b_354_){
_start:
{
uint8_t v___x_355_; 
v___x_355_ = lean_int_dec_eq(v_a_353_, v_b_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay___boxed(lean_object* v_a_356_, lean_object* v_b_357_){
_start:
{
uint8_t v_res_358_; lean_object* v_r_359_; 
v_res_358_ = l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay(v_a_356_, v_b_357_);
lean_dec(v_b_357_);
lean_dec(v_a_356_);
v_r_359_ = lean_box(v_res_358_);
return v_r_359_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_Ordinal_instLEOfDay(void){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = lean_box(0);
return v___x_360_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_Ordinal_instLTOfDay(void){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lean_box(0);
return v___x_361_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_Ordinal_instInhabitedOfDay(void){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = lean_obj_once(&l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0);
return v___x_362_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay___aux__1(lean_object* v_x_363_, lean_object* v_y_364_){
_start:
{
uint8_t v___x_365_; 
v___x_365_ = lean_int_dec_le(v_x_363_, v_y_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay___aux__1___boxed(lean_object* v_x_366_, lean_object* v_y_367_){
_start:
{
uint8_t v_res_368_; lean_object* v_r_369_; 
v_res_368_ = l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay___aux__1(v_x_366_, v_y_367_);
lean_dec(v_y_367_);
lean_dec(v_x_366_);
v_r_369_ = lean_box(v_res_368_);
return v_r_369_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay(lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
uint8_t v___x_372_; 
v___x_372_ = lean_int_dec_le(v___y_370_, v___y_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay___boxed(lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
uint8_t v_res_375_; lean_object* v_r_376_; 
v_res_375_ = l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay(v___y_373_, v___y_374_);
lean_dec(v___y_374_);
lean_dec(v___y_373_);
v_r_376_ = lean_box(v_res_375_);
return v_r_376_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay___aux__1(lean_object* v_x_377_, lean_object* v_y_378_){
_start:
{
uint8_t v___x_379_; 
v___x_379_ = lean_int_dec_lt(v_x_377_, v_y_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay___aux__1___boxed(lean_object* v_x_380_, lean_object* v_y_381_){
_start:
{
uint8_t v_res_382_; lean_object* v_r_383_; 
v_res_382_ = l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay___aux__1(v_x_380_, v_y_381_);
lean_dec(v_y_381_);
lean_dec(v_x_380_);
v_r_383_ = lean_box(v_res_382_);
return v_r_383_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay(lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
uint8_t v___x_386_; 
v___x_386_ = lean_int_dec_lt(v___y_384_, v___y_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay___boxed(lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
uint8_t v_res_389_; lean_object* v_r_390_; 
v_res_389_ = l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay(v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec(v___y_387_);
v_r_390_ = lean_box(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instOrdOfDay___aux__1(lean_object* v_x_391_, lean_object* v_y_392_){
_start:
{
uint8_t v___x_393_; 
v___x_393_ = lean_int_dec_lt(v_x_391_, v_y_392_);
if (v___x_393_ == 0)
{
uint8_t v___x_394_; 
v___x_394_ = lean_int_dec_eq(v_x_391_, v_y_392_);
if (v___x_394_ == 0)
{
uint8_t v___x_395_; 
v___x_395_ = 2;
return v___x_395_;
}
else
{
uint8_t v___x_396_; 
v___x_396_ = 1;
return v___x_396_;
}
}
else
{
uint8_t v___x_397_; 
v___x_397_ = 0;
return v___x_397_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instOrdOfDay___aux__1___boxed(lean_object* v_x_398_, lean_object* v_y_399_){
_start:
{
uint8_t v_res_400_; lean_object* v_r_401_; 
v_res_400_ = l_Std_Time_Nanosecond_Ordinal_instOrdOfDay___aux__1(v_x_398_, v_y_399_);
lean_dec(v_y_399_);
lean_dec(v_x_398_);
v_r_401_ = lean_box(v_res_400_);
return v_r_401_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofInt___redArg(lean_object* v_data_404_){
_start:
{
lean_inc(v_data_404_);
return v_data_404_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofInt___redArg___boxed(lean_object* v_data_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Std_Time_Nanosecond_Ordinal_ofInt___redArg(v_data_405_);
lean_dec(v_data_405_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofInt(lean_object* v_data_407_, lean_object* v_h_408_){
_start:
{
lean_inc(v_data_407_);
return v_data_407_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofInt___boxed(lean_object* v_data_409_, lean_object* v_h_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Std_Time_Nanosecond_Ordinal_ofInt(v_data_409_, v_h_410_);
lean_dec(v_data_409_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofNat___redArg(lean_object* v_data_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = lean_nat_to_int(v_data_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofNat(lean_object* v_data_414_, lean_object* v_h_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = lean_nat_to_int(v_data_414_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofFin(lean_object* v_data_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = lean_nat_to_int(v_data_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_toOffset(lean_object* v_ordinal_419_){
_start:
{
lean_inc(v_ordinal_419_);
return v_ordinal_419_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_toOffset___boxed(lean_object* v_ordinal_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Std_Time_Nanosecond_Ordinal_toOffset(v_ordinal_420_);
lean_dec(v_ordinal_420_);
return v_res_421_;
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
