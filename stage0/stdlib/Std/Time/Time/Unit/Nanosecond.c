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
lean_object* l_Rat_instNatCast___lam__0(lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_instInhabitedUnitVal_default(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_nonneg(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Int_neg___boxed(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Int_sub___boxed(lean_object*, lean_object*);
lean_object* l_Int_repr___boxed(lean_object*);
lean_object* l_Int_add___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instInhabitedOrdinal;
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLeOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeOrdinal___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLeOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeOrdinal___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1___closed__0;
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
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableEqOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqOffset___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__0;
static lean_once_cell_t l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__1;
static lean_once_cell_t l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__2;
static lean_once_cell_t l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instInhabitedOffset___aux__1;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Nanosecond_instInhabitedOffset_spec__0(lean_object*);
static lean_once_cell_t l_Std_Time_Nanosecond_instInhabitedOffset___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Nanosecond_instInhabitedOffset___closed__0;
static lean_once_cell_t l_Std_Time_Nanosecond_instInhabitedOffset___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Nanosecond_instInhabitedOffset___closed__1;
static lean_once_cell_t l_Std_Time_Nanosecond_instInhabitedOffset___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Nanosecond_instInhabitedOffset___closed__2;
static lean_once_cell_t l_Std_Time_Nanosecond_instInhabitedOffset___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Nanosecond_instInhabitedOffset___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instInhabitedOffset;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Nanosecond_instInhabitedOffset_spec__0_spec__0(lean_object*);
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
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableEqOrdinal___aux__1(lean_object* v_x_29_, lean_object* v_x_30_){
_start:
{
uint8_t v___x_31_; 
v___x_31_ = lean_int_dec_eq(v_x_29_, v_x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqOrdinal___aux__1___boxed(lean_object* v_x_32_, lean_object* v_x_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l_Std_Time_Nanosecond_instDecidableEqOrdinal___aux__1(v_x_32_, v_x_33_);
lean_dec(v_x_33_);
lean_dec(v_x_32_);
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
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_unsigned_to_nat(1000000000u);
v___x_52_ = lean_unsigned_to_nat(0u);
v___x_53_ = lean_nat_mod(v___x_52_, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__1(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_obj_once(&l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__0, &l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__0);
v___x_55_ = lean_nat_to_int(v___x_54_);
return v___x_55_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOrdinal(void){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lean_obj_once(&l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__1, &l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__1_once, _init_l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__1);
return v___x_56_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLeOrdinal___aux__1(lean_object* v_x_57_, lean_object* v_y_58_){
_start:
{
lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_59_ = lean_int_sub(v_y_58_, v_x_57_);
v___x_60_ = lean_int_dec_nonneg(v___x_59_);
lean_dec(v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeOrdinal___aux__1___boxed(lean_object* v_x_61_, lean_object* v_y_62_){
_start:
{
uint8_t v_res_63_; lean_object* v_r_64_; 
v_res_63_ = l_Std_Time_Nanosecond_instDecidableLeOrdinal___aux__1(v_x_61_, v_y_62_);
lean_dec(v_y_62_);
lean_dec(v_x_61_);
v_r_64_ = lean_box(v_res_63_);
return v_r_64_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLeOrdinal(lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = l_Std_Time_Nanosecond_instDecidableLeOrdinal___aux__1(v___y_65_, v___y_66_);
return v___x_67_;
}
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
static lean_object* _init_l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1___closed__0(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_nat_to_int(v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1(lean_object* v_x_74_, lean_object* v_y_75_){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_76_ = lean_obj_once(&l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1___closed__0, &l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1___closed__0);
v___x_77_ = lean_int_add(v_x_74_, v___x_76_);
v___x_78_ = lean_int_sub(v_y_75_, v___x_77_);
lean_dec(v___x_77_);
v___x_79_ = lean_int_dec_nonneg(v___x_78_);
lean_dec(v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1___boxed(lean_object* v_x_80_, lean_object* v_y_81_){
_start:
{
uint8_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1(v_x_80_, v_y_81_);
lean_dec(v_y_81_);
lean_dec(v_x_80_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLtOrdinal(lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
uint8_t v___x_86_; 
v___x_86_ = l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1(v___y_84_, v___y_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtOrdinal___boxed(lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_Std_Time_Nanosecond_instDecidableLtOrdinal(v___y_87_, v___y_88_);
lean_dec(v___y_88_);
lean_dec(v___y_87_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instOrdOrdinal___aux__1(lean_object* v_x_91_, lean_object* v_y_92_){
_start:
{
uint8_t v___x_93_; 
v___x_93_ = lean_int_dec_lt(v_x_91_, v_y_92_);
if (v___x_93_ == 0)
{
uint8_t v___x_94_; 
v___x_94_ = lean_int_dec_eq(v_x_91_, v_y_92_);
if (v___x_94_ == 0)
{
uint8_t v___x_95_; 
v___x_95_ = 2;
return v___x_95_;
}
else
{
uint8_t v___x_96_; 
v___x_96_ = 1;
return v___x_96_;
}
}
else
{
uint8_t v___x_97_; 
v___x_97_ = 0;
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instOrdOrdinal___aux__1___boxed(lean_object* v_x_98_, lean_object* v_y_99_){
_start:
{
uint8_t v_res_100_; lean_object* v_r_101_; 
v_res_100_ = l_Std_Time_Nanosecond_instOrdOrdinal___aux__1(v_x_98_, v_y_99_);
lean_dec(v_y_99_);
lean_dec(v_x_98_);
v_r_101_ = lean_box(v_res_100_);
return v_r_101_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instReprOffset___aux__1(lean_object* v_x_104_, lean_object* v_p_105_){
_start:
{
lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_106_ = lean_obj_once(&l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0);
v___x_107_ = lean_int_dec_lt(v_x_104_, v___x_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = l_Int_repr(v_x_104_);
v___x_109_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
return v___x_109_;
}
else
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_110_ = l_Int_repr(v_x_104_);
v___x_111_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
v___x_112_ = l_Repr_addAppParen(v___x_111_, v_p_105_);
return v___x_112_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instReprOffset___aux__1___boxed(lean_object* v_x_113_, lean_object* v_p_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Std_Time_Nanosecond_instReprOffset___aux__1(v_x_113_, v_p_114_);
lean_dec(v_p_114_);
lean_dec(v_x_113_);
return v_res_115_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableEqOffset___aux__1(lean_object* v_x_117_, lean_object* v_x_118_){
_start:
{
uint8_t v___x_119_; 
v___x_119_ = lean_int_dec_eq(v_x_117_, v_x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqOffset___aux__1___boxed(lean_object* v_x_120_, lean_object* v_x_121_){
_start:
{
uint8_t v_res_122_; lean_object* v_r_123_; 
v_res_122_ = l_Std_Time_Nanosecond_instDecidableEqOffset___aux__1(v_x_120_, v_x_121_);
lean_dec(v_x_121_);
lean_dec(v_x_120_);
v_r_123_ = lean_box(v_res_122_);
return v_r_123_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableEqOffset(lean_object* v_a_124_, lean_object* v_b_125_){
_start:
{
uint8_t v___x_126_; 
v___x_126_ = lean_int_dec_eq(v_a_124_, v_b_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqOffset___boxed(lean_object* v_a_127_, lean_object* v_b_128_){
_start:
{
uint8_t v_res_129_; lean_object* v_r_130_; 
v_res_129_ = l_Std_Time_Nanosecond_instDecidableEqOffset(v_a_127_, v_b_128_);
lean_dec(v_b_128_);
lean_dec(v_a_127_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__0(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_unsigned_to_nat(1u);
v___x_132_ = l_Rat_instNatCast___lam__0(v___x_131_);
return v___x_132_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__1(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_unsigned_to_nat(1000000000u);
v___x_134_ = l_Rat_instNatCast___lam__0(v___x_133_);
return v___x_134_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__2(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_135_ = lean_obj_once(&l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__1, &l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__1_once, _init_l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__1);
v___x_136_ = lean_obj_once(&l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__0, &l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__0);
v___x_137_ = l_Rat_div(v___x_136_, v___x_135_);
return v___x_137_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__3(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_obj_once(&l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__2, &l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__2_once, _init_l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__2);
v___x_139_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_138_);
return v___x_139_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOffset___aux__1(void){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = lean_obj_once(&l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__3, &l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__3_once, _init_l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__3);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Nanosecond_instInhabitedOffset_spec__0(lean_object* v_a_141_){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_nat_to_int(v_a_141_);
v___x_143_ = l_Rat_ofInt(v___x_142_);
return v___x_143_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOffset___closed__0(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_unsigned_to_nat(1u);
v___x_145_ = l_Nat_cast___at___00Std_Time_Nanosecond_instInhabitedOffset_spec__0(v___x_144_);
return v___x_145_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOffset___closed__1(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = lean_unsigned_to_nat(1000000000u);
v___x_147_ = l_Nat_cast___at___00Std_Time_Nanosecond_instInhabitedOffset_spec__0(v___x_146_);
return v___x_147_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOffset___closed__2(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_obj_once(&l_Std_Time_Nanosecond_instInhabitedOffset___closed__1, &l_Std_Time_Nanosecond_instInhabitedOffset___closed__1_once, _init_l_Std_Time_Nanosecond_instInhabitedOffset___closed__1);
v___x_149_ = lean_obj_once(&l_Std_Time_Nanosecond_instInhabitedOffset___closed__0, &l_Std_Time_Nanosecond_instInhabitedOffset___closed__0_once, _init_l_Std_Time_Nanosecond_instInhabitedOffset___closed__0);
v___x_150_ = l_Rat_div(v___x_149_, v___x_148_);
return v___x_150_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOffset___closed__3(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = lean_obj_once(&l_Std_Time_Nanosecond_instInhabitedOffset___closed__2, &l_Std_Time_Nanosecond_instInhabitedOffset___closed__2_once, _init_l_Std_Time_Nanosecond_instInhabitedOffset___closed__2);
v___x_152_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_151_);
return v___x_152_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedOffset(void){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = lean_obj_once(&l_Std_Time_Nanosecond_instInhabitedOffset___closed__3, &l_Std_Time_Nanosecond_instInhabitedOffset___closed__3_once, _init_l_Std_Time_Nanosecond_instInhabitedOffset___closed__3);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Nanosecond_instInhabitedOffset_spec__0_spec__0(lean_object* v_a_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = lean_nat_to_int(v_a_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instAddOffset___aux__1(lean_object* v_u1_156_, lean_object* v_u2_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = lean_int_add(v_u1_156_, v_u2_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instAddOffset___aux__1___boxed(lean_object* v_u1_159_, lean_object* v_u2_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Std_Time_Nanosecond_instAddOffset___aux__1(v_u1_159_, v_u2_160_);
lean_dec(v_u2_160_);
lean_dec(v_u1_159_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instSubOffset___aux__1(lean_object* v_u1_164_, lean_object* v_u2_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_int_sub(v_u1_164_, v_u2_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instSubOffset___aux__1___boxed(lean_object* v_u1_167_, lean_object* v_u2_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Std_Time_Nanosecond_instSubOffset___aux__1(v_u1_167_, v_u2_168_);
lean_dec(v_u2_168_);
lean_dec(v_u1_167_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instNegOffset___aux__1(lean_object* v_x_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = lean_int_neg(v_x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instNegOffset___aux__1___boxed(lean_object* v_x_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Std_Time_Nanosecond_instNegOffset___aux__1(v_x_174_);
lean_dec(v_x_174_);
return v_res_175_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instLEOffset(void){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = lean_box(0);
return v___x_178_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instLTOffset(void){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = lean_box(0);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instToStringOffset___aux__1(lean_object* v_n_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Int_repr(v_n_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instToStringOffset___aux__1___boxed(lean_object* v_n_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Std_Time_Nanosecond_instToStringOffset___aux__1(v_n_182_);
lean_dec(v_n_182_);
return v_res_183_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLeOffset___aux__1(lean_object* v_x_186_, lean_object* v_y_187_){
_start:
{
lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_188_ = lean_int_sub(v_y_187_, v_x_186_);
v___x_189_ = lean_int_dec_nonneg(v___x_188_);
lean_dec(v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeOffset___aux__1___boxed(lean_object* v_x_190_, lean_object* v_y_191_){
_start:
{
uint8_t v_res_192_; lean_object* v_r_193_; 
v_res_192_ = l_Std_Time_Nanosecond_instDecidableLeOffset___aux__1(v_x_190_, v_y_191_);
lean_dec(v_y_191_);
lean_dec(v_x_190_);
v_r_193_ = lean_box(v_res_192_);
return v_r_193_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLeOffset(lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
uint8_t v___x_196_; 
v___x_196_ = l_Std_Time_Nanosecond_instDecidableLeOffset___aux__1(v___y_194_, v___y_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeOffset___boxed(lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
uint8_t v_res_199_; lean_object* v_r_200_; 
v_res_199_ = l_Std_Time_Nanosecond_instDecidableLeOffset(v___y_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec(v___y_197_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLtOffset___aux__1(lean_object* v_x_201_, lean_object* v_y_202_){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_203_ = lean_obj_once(&l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1___closed__0, &l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1___closed__0);
v___x_204_ = lean_int_add(v_x_201_, v___x_203_);
v___x_205_ = lean_int_sub(v_y_202_, v___x_204_);
lean_dec(v___x_204_);
v___x_206_ = lean_int_dec_nonneg(v___x_205_);
lean_dec(v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtOffset___aux__1___boxed(lean_object* v_x_207_, lean_object* v_y_208_){
_start:
{
uint8_t v_res_209_; lean_object* v_r_210_; 
v_res_209_ = l_Std_Time_Nanosecond_instDecidableLtOffset___aux__1(v_x_207_, v_y_208_);
lean_dec(v_y_208_);
lean_dec(v_x_207_);
v_r_210_ = lean_box(v_res_209_);
return v_r_210_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLtOffset(lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
uint8_t v___x_213_; 
v___x_213_ = l_Std_Time_Nanosecond_instDecidableLtOffset___aux__1(v___y_211_, v___y_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtOffset___boxed(lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
uint8_t v_res_216_; lean_object* v_r_217_; 
v_res_216_ = l_Std_Time_Nanosecond_instDecidableLtOffset(v___y_214_, v___y_215_);
lean_dec(v___y_215_);
lean_dec(v___y_214_);
v_r_217_ = lean_box(v_res_216_);
return v_r_217_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instOfNatOffset(lean_object* v_n_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = lean_nat_to_int(v_n_218_);
return v___x_219_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instOrdOffset___aux__1(lean_object* v_x_220_, lean_object* v_y_221_){
_start:
{
uint8_t v___x_222_; 
v___x_222_ = lean_int_dec_lt(v_x_220_, v_y_221_);
if (v___x_222_ == 0)
{
uint8_t v___x_223_; 
v___x_223_ = lean_int_dec_eq(v_x_220_, v_y_221_);
if (v___x_223_ == 0)
{
uint8_t v___x_224_; 
v___x_224_ = 2;
return v___x_224_;
}
else
{
uint8_t v___x_225_; 
v___x_225_ = 1;
return v___x_225_;
}
}
else
{
uint8_t v___x_226_; 
v___x_226_ = 0;
return v___x_226_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instOrdOffset___aux__1___boxed(lean_object* v_x_227_, lean_object* v_y_228_){
_start:
{
uint8_t v_res_229_; lean_object* v_r_230_; 
v_res_229_ = l_Std_Time_Nanosecond_instOrdOffset___aux__1(v_x_227_, v_y_228_);
lean_dec(v_y_228_);
lean_dec(v_x_227_);
v_r_230_ = lean_box(v_res_229_);
return v_r_230_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofNat(lean_object* v_data_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = lean_nat_to_int(v_data_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofInt(lean_object* v_data_235_){
_start:
{
lean_inc(v_data_235_);
return v_data_235_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofInt___boxed(lean_object* v_data_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Std_Time_Nanosecond_Offset_ofInt(v_data_236_);
lean_dec(v_data_236_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instReprSpan___aux__1(lean_object* v_n_238_, lean_object* v_a_239_){
_start:
{
lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_240_ = lean_obj_once(&l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0);
v___x_241_ = lean_int_dec_lt(v_n_238_, v___x_240_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = l_Int_repr(v_n_238_);
v___x_243_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
else
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = l_Int_repr(v_n_238_);
v___x_245_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
v___x_246_ = l_Repr_addAppParen(v___x_245_, v_a_239_);
return v___x_246_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instReprSpan___aux__1___boxed(lean_object* v_n_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Std_Time_Nanosecond_instReprSpan___aux__1(v_n_247_, v_a_248_);
lean_dec(v_a_248_);
lean_dec(v_n_247_);
return v_res_249_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableEqSpan___aux__1(lean_object* v_x_251_, lean_object* v_x_252_){
_start:
{
uint8_t v___x_253_; 
v___x_253_ = lean_int_dec_eq(v_x_251_, v_x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqSpan___aux__1___boxed(lean_object* v_x_254_, lean_object* v_x_255_){
_start:
{
uint8_t v_res_256_; lean_object* v_r_257_; 
v_res_256_ = l_Std_Time_Nanosecond_instDecidableEqSpan___aux__1(v_x_254_, v_x_255_);
lean_dec(v_x_255_);
lean_dec(v_x_254_);
v_r_257_ = lean_box(v_res_256_);
return v_r_257_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableEqSpan(lean_object* v_a_258_, lean_object* v_b_259_){
_start:
{
uint8_t v___x_260_; 
v___x_260_ = lean_int_dec_eq(v_a_258_, v_b_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableEqSpan___boxed(lean_object* v_a_261_, lean_object* v_b_262_){
_start:
{
uint8_t v_res_263_; lean_object* v_r_264_; 
v_res_263_ = l_Std_Time_Nanosecond_instDecidableEqSpan(v_a_261_, v_b_262_);
lean_dec(v_b_262_);
lean_dec(v_a_261_);
v_r_264_ = lean_box(v_res_263_);
return v_r_264_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instLESpan(void){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = lean_box(0);
return v___x_265_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instLTSpan(void){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = lean_box(0);
return v___x_266_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_instInhabitedSpan(void){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = lean_obj_once(&l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0);
return v___x_267_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLeSpan___aux__1(lean_object* v_x_268_, lean_object* v_y_269_){
_start:
{
lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_270_ = lean_int_sub(v_y_269_, v_x_268_);
v___x_271_ = lean_int_dec_nonneg(v___x_270_);
lean_dec(v___x_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeSpan___aux__1___boxed(lean_object* v_x_272_, lean_object* v_y_273_){
_start:
{
uint8_t v_res_274_; lean_object* v_r_275_; 
v_res_274_ = l_Std_Time_Nanosecond_instDecidableLeSpan___aux__1(v_x_272_, v_y_273_);
lean_dec(v_y_273_);
lean_dec(v_x_272_);
v_r_275_ = lean_box(v_res_274_);
return v_r_275_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLeSpan(lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
uint8_t v___x_278_; 
v___x_278_ = l_Std_Time_Nanosecond_instDecidableLeSpan___aux__1(v___y_276_, v___y_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLeSpan___boxed(lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
uint8_t v_res_281_; lean_object* v_r_282_; 
v_res_281_ = l_Std_Time_Nanosecond_instDecidableLeSpan(v___y_279_, v___y_280_);
lean_dec(v___y_280_);
lean_dec(v___y_279_);
v_r_282_ = lean_box(v_res_281_);
return v_r_282_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLtSpan___aux__1(lean_object* v_x_283_, lean_object* v_y_284_){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_285_ = lean_obj_once(&l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1___closed__0, &l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1___closed__0);
v___x_286_ = lean_int_add(v_x_283_, v___x_285_);
v___x_287_ = lean_int_sub(v_y_284_, v___x_286_);
lean_dec(v___x_286_);
v___x_288_ = lean_int_dec_nonneg(v___x_287_);
lean_dec(v___x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtSpan___aux__1___boxed(lean_object* v_x_289_, lean_object* v_y_290_){
_start:
{
uint8_t v_res_291_; lean_object* v_r_292_; 
v_res_291_ = l_Std_Time_Nanosecond_instDecidableLtSpan___aux__1(v_x_289_, v_y_290_);
lean_dec(v_y_290_);
lean_dec(v_x_289_);
v_r_292_ = lean_box(v_res_291_);
return v_r_292_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instDecidableLtSpan(lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
uint8_t v___x_295_; 
v___x_295_ = l_Std_Time_Nanosecond_instDecidableLtSpan___aux__1(v___y_293_, v___y_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instDecidableLtSpan___boxed(lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
uint8_t v_res_298_; lean_object* v_r_299_; 
v_res_298_ = l_Std_Time_Nanosecond_instDecidableLtSpan(v___y_296_, v___y_297_);
lean_dec(v___y_297_);
lean_dec(v___y_296_);
v_r_299_ = lean_box(v_res_298_);
return v_r_299_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_instOrdSpan___aux__1(lean_object* v_x_300_, lean_object* v_y_301_){
_start:
{
uint8_t v___x_302_; 
v___x_302_ = lean_int_dec_lt(v_x_300_, v_y_301_);
if (v___x_302_ == 0)
{
uint8_t v___x_303_; 
v___x_303_ = lean_int_dec_eq(v_x_300_, v_y_301_);
if (v___x_303_ == 0)
{
uint8_t v___x_304_; 
v___x_304_ = 2;
return v___x_304_;
}
else
{
uint8_t v___x_305_; 
v___x_305_ = 1;
return v___x_305_;
}
}
else
{
uint8_t v___x_306_; 
v___x_306_ = 0;
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_instOrdSpan___aux__1___boxed(lean_object* v_x_307_, lean_object* v_y_308_){
_start:
{
uint8_t v_res_309_; lean_object* v_r_310_; 
v_res_309_ = l_Std_Time_Nanosecond_instOrdSpan___aux__1(v_x_307_, v_y_308_);
lean_dec(v_y_308_);
lean_dec(v_x_307_);
v_r_310_ = lean_box(v_res_309_);
return v_r_310_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Span_toOffset(lean_object* v_span_313_){
_start:
{
lean_inc(v_span_313_);
return v_span_313_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Span_toOffset___boxed(lean_object* v_span_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Std_Time_Nanosecond_Span_toOffset(v_span_314_);
lean_dec(v_span_314_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instReprOfDay___aux__1(lean_object* v_n_316_, lean_object* v_a_317_){
_start:
{
lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_318_ = lean_obj_once(&l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0);
v___x_319_ = lean_int_dec_lt(v_n_316_, v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = l_Int_repr(v_n_316_);
v___x_321_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
return v___x_321_;
}
else
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_322_ = l_Int_repr(v_n_316_);
v___x_323_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
v___x_324_ = l_Repr_addAppParen(v___x_323_, v_a_317_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instReprOfDay___aux__1___boxed(lean_object* v_n_325_, lean_object* v_a_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Std_Time_Nanosecond_Ordinal_instReprOfDay___aux__1(v_n_325_, v_a_326_);
lean_dec(v_a_326_);
lean_dec(v_n_325_);
return v_res_327_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay___aux__1(lean_object* v_x_329_, lean_object* v_x_330_){
_start:
{
uint8_t v___x_331_; 
v___x_331_ = lean_int_dec_eq(v_x_329_, v_x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay___aux__1___boxed(lean_object* v_x_332_, lean_object* v_x_333_){
_start:
{
uint8_t v_res_334_; lean_object* v_r_335_; 
v_res_334_ = l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay___aux__1(v_x_332_, v_x_333_);
lean_dec(v_x_333_);
lean_dec(v_x_332_);
v_r_335_ = lean_box(v_res_334_);
return v_r_335_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay(lean_object* v_a_336_, lean_object* v_b_337_){
_start:
{
uint8_t v___x_338_; 
v___x_338_ = lean_int_dec_eq(v_a_336_, v_b_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay___boxed(lean_object* v_a_339_, lean_object* v_b_340_){
_start:
{
uint8_t v_res_341_; lean_object* v_r_342_; 
v_res_341_ = l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay(v_a_339_, v_b_340_);
lean_dec(v_b_340_);
lean_dec(v_a_339_);
v_r_342_ = lean_box(v_res_341_);
return v_r_342_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_Ordinal_instLEOfDay(void){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = lean_box(0);
return v___x_343_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_Ordinal_instLTOfDay(void){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = lean_box(0);
return v___x_344_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_Ordinal_instInhabitedOfDay(void){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = lean_obj_once(&l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0);
return v___x_345_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay___aux__1(lean_object* v_x_346_, lean_object* v_y_347_){
_start:
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = lean_int_sub(v_y_347_, v_x_346_);
v___x_349_ = lean_int_dec_nonneg(v___x_348_);
lean_dec(v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay___aux__1___boxed(lean_object* v_x_350_, lean_object* v_y_351_){
_start:
{
uint8_t v_res_352_; lean_object* v_r_353_; 
v_res_352_ = l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay___aux__1(v_x_350_, v_y_351_);
lean_dec(v_y_351_);
lean_dec(v_x_350_);
v_r_353_ = lean_box(v_res_352_);
return v_r_353_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay(lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
uint8_t v___x_356_; 
v___x_356_ = l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay___aux__1(v___y_354_, v___y_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay___boxed(lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
uint8_t v_res_359_; lean_object* v_r_360_; 
v_res_359_ = l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay(v___y_357_, v___y_358_);
lean_dec(v___y_358_);
lean_dec(v___y_357_);
v_r_360_ = lean_box(v_res_359_);
return v_r_360_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay___aux__1(lean_object* v_x_361_, lean_object* v_y_362_){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_363_ = lean_obj_once(&l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1___closed__0, &l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1___closed__0);
v___x_364_ = lean_int_add(v_x_361_, v___x_363_);
v___x_365_ = lean_int_sub(v_y_362_, v___x_364_);
lean_dec(v___x_364_);
v___x_366_ = lean_int_dec_nonneg(v___x_365_);
lean_dec(v___x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay___aux__1___boxed(lean_object* v_x_367_, lean_object* v_y_368_){
_start:
{
uint8_t v_res_369_; lean_object* v_r_370_; 
v_res_369_ = l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay___aux__1(v_x_367_, v_y_368_);
lean_dec(v_y_368_);
lean_dec(v_x_367_);
v_r_370_ = lean_box(v_res_369_);
return v_r_370_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay(lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
uint8_t v___x_373_; 
v___x_373_ = l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay___aux__1(v___y_371_, v___y_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay___boxed(lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
uint8_t v_res_376_; lean_object* v_r_377_; 
v_res_376_ = l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay(v___y_374_, v___y_375_);
lean_dec(v___y_375_);
lean_dec(v___y_374_);
v_r_377_ = lean_box(v_res_376_);
return v_r_377_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Nanosecond_Ordinal_instOrdOfDay___aux__1(lean_object* v_x_378_, lean_object* v_y_379_){
_start:
{
uint8_t v___x_380_; 
v___x_380_ = lean_int_dec_lt(v_x_378_, v_y_379_);
if (v___x_380_ == 0)
{
uint8_t v___x_381_; 
v___x_381_ = lean_int_dec_eq(v_x_378_, v_y_379_);
if (v___x_381_ == 0)
{
uint8_t v___x_382_; 
v___x_382_ = 2;
return v___x_382_;
}
else
{
uint8_t v___x_383_; 
v___x_383_ = 1;
return v___x_383_;
}
}
else
{
uint8_t v___x_384_; 
v___x_384_ = 0;
return v___x_384_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_instOrdOfDay___aux__1___boxed(lean_object* v_x_385_, lean_object* v_y_386_){
_start:
{
uint8_t v_res_387_; lean_object* v_r_388_; 
v_res_387_ = l_Std_Time_Nanosecond_Ordinal_instOrdOfDay___aux__1(v_x_385_, v_y_386_);
lean_dec(v_y_386_);
lean_dec(v_x_385_);
v_r_388_ = lean_box(v_res_387_);
return v_r_388_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofInt___redArg(lean_object* v_data_391_){
_start:
{
lean_inc(v_data_391_);
return v_data_391_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofInt___redArg___boxed(lean_object* v_data_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Std_Time_Nanosecond_Ordinal_ofInt___redArg(v_data_392_);
lean_dec(v_data_392_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofInt(lean_object* v_data_394_, lean_object* v_h_395_){
_start:
{
lean_inc(v_data_394_);
return v_data_394_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofInt___boxed(lean_object* v_data_396_, lean_object* v_h_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Std_Time_Nanosecond_Ordinal_ofInt(v_data_396_, v_h_397_);
lean_dec(v_data_396_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofNat___redArg(lean_object* v_data_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = lean_nat_to_int(v_data_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofNat(lean_object* v_data_401_, lean_object* v_h_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = lean_nat_to_int(v_data_401_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_ofFin(lean_object* v_data_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = lean_nat_to_int(v_data_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_toOffset(lean_object* v_ordinal_406_){
_start:
{
lean_inc(v_ordinal_406_);
return v_ordinal_406_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Ordinal_toOffset___boxed(lean_object* v_ordinal_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Std_Time_Nanosecond_Ordinal_toOffset(v_ordinal_407_);
lean_dec(v_ordinal_407_);
return v_res_408_;
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
