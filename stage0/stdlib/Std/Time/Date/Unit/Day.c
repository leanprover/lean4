// Lean compiler output
// Module: Std.Time.Date.Unit.Day
// Imports: public import Std.Time.Time
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
lean_object* lean_int_mul(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_instInhabitedUnitVal_default___redArg();
lean_object* l_Int_sub___boxed(lean_object*, lean_object*);
lean_object* l_Int_repr___boxed(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_neg___boxed(lean_object*);
lean_object* l_Int_add___boxed(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Day_instReprOrdinal___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_instReprOrdinal___aux__1___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Day_instReprOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instReprOrdinal___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instReprOrdinal___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instReprOrdinal___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Day_instReprOrdinal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Day_instReprOrdinal___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Day_instReprOrdinal___closed__0 = (const lean_object*)&l_Std_Time_Day_instReprOrdinal___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Day_instReprOrdinal = (const lean_object*)&l_Std_Time_Day_instReprOrdinal___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableEqOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableEqOrdinal___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableEqOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableEqOrdinal___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instLEOrdinal;
LEAN_EXPORT lean_object* l_Std_Time_Day_instLTOrdinal;
static lean_once_cell_t l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0;
static lean_once_cell_t l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__1;
static lean_once_cell_t l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__2;
static lean_once_cell_t l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__3;
static lean_once_cell_t l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4;
LEAN_EXPORT lean_object* l_Std_Time_Day_instOfNatOrdinal___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instOfNatOrdinal(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLeOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLeOrdinal___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLeOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLeOrdinal___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLtOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLtOrdinal___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLtOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLtOrdinal___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Day_instInhabitedOrdinal___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_instInhabitedOrdinal___closed__0;
static lean_once_cell_t l_Std_Time_Day_instInhabitedOrdinal___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_instInhabitedOrdinal___closed__1;
static lean_once_cell_t l_Std_Time_Day_instInhabitedOrdinal___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_instInhabitedOrdinal___closed__2;
static lean_once_cell_t l_Std_Time_Day_instInhabitedOrdinal___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_instInhabitedOrdinal___closed__3;
static lean_once_cell_t l_Std_Time_Day_instInhabitedOrdinal___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_instInhabitedOrdinal___closed__4;
LEAN_EXPORT lean_object* l_Std_Time_Day_instInhabitedOrdinal;
LEAN_EXPORT uint8_t l_Std_Time_Day_instOrdOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instOrdOrdinal___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Day_instOrdOrdinal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Day_instOrdOrdinal___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Day_instOrdOrdinal___closed__0 = (const lean_object*)&l_Std_Time_Day_instOrdOrdinal___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Day_instOrdOrdinal = (const lean_object*)&l_Std_Time_Day_instOrdOrdinal___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Day_instReprOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instReprOffset___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT const lean_object* l_Std_Time_Day_instReprOffset = (const lean_object*)&l_Std_Time_Day_instReprOrdinal___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableEqOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableEqOffset___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Day_instDecidableEqOffset___aux__1_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Day_instDecidableEqOffset___aux__1_spec__0(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableEqOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableEqOffset___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Day_instInhabitedOffset___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_instInhabitedOffset___aux__1___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Day_instInhabitedOffset___aux__1;
LEAN_EXPORT lean_object* l_Std_Time_Day_instInhabitedOffset;
LEAN_EXPORT lean_object* l_Std_Time_Day_instAddOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instAddOffset___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Day_instAddOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Day_instAddOffset___closed__0 = (const lean_object*)&l_Std_Time_Day_instAddOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Day_instAddOffset = (const lean_object*)&l_Std_Time_Day_instAddOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Day_instSubOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instSubOffset___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Day_instSubOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Day_instSubOffset___closed__0 = (const lean_object*)&l_Std_Time_Day_instSubOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Day_instSubOffset = (const lean_object*)&l_Std_Time_Day_instSubOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Day_instNegOffset___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instNegOffset___aux__1___boxed(lean_object*);
static const lean_closure_object l_Std_Time_Day_instNegOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Day_instNegOffset___closed__0 = (const lean_object*)&l_Std_Time_Day_instNegOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Day_instNegOffset = (const lean_object*)&l_Std_Time_Day_instNegOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Day_instLEOffset;
LEAN_EXPORT lean_object* l_Std_Time_Day_instLTOffset;
LEAN_EXPORT lean_object* l_Std_Time_Day_instToStringOffset___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instToStringOffset___aux__1___boxed(lean_object*);
static const lean_closure_object l_Std_Time_Day_instToStringOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_repr___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Day_instToStringOffset___closed__0 = (const lean_object*)&l_Std_Time_Day_instToStringOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Day_instToStringOffset = (const lean_object*)&l_Std_Time_Day_instToStringOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Day_instOfNatOffset(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLeOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLeOffset___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLeOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLeOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLtOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLtOffset___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLtOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLtOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Day_instOrdOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instOrdOffset___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Day_instOrdOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Day_instOrdOffset___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Day_instOrdOffset___closed__0 = (const lean_object*)&l_Std_Time_Day_instOrdOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Day_instOrdOffset = (const lean_object*)&l_Std_Time_Day_instOrdOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Day_instHMulIntOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instHMulIntOffset___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Day_instHMulIntOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Day_instHMulIntOffset___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Day_instHMulIntOffset___closed__0 = (const lean_object*)&l_Std_Time_Day_instHMulIntOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Day_instHMulIntOffset = (const lean_object*)&l_Std_Time_Day_instHMulIntOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Day_instHMulOffsetInt___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instHMulOffsetInt___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Day_instHMulOffsetInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Day_instHMulOffsetInt___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Day_instHMulOffsetInt___closed__0 = (const lean_object*)&l_Std_Time_Day_instHMulOffsetInt___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Day_instHMulOffsetInt = (const lean_object*)&l_Std_Time_Day_instHMulOffsetInt___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Day_instHMulNatOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instHMulNatOffset___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Day_instHMulNatOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Day_instHMulNatOffset___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Day_instHMulNatOffset___closed__0 = (const lean_object*)&l_Std_Time_Day_instHMulNatOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Day_instHMulNatOffset = (const lean_object*)&l_Std_Time_Day_instHMulNatOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Day_instHMulOffsetNat___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instHMulOffsetNat___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Day_instHMulOffsetNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Day_instHMulOffsetNat___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Day_instHMulOffsetNat___closed__0 = (const lean_object*)&l_Std_Time_Day_instHMulOffsetNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Day_instHMulOffsetNat = (const lean_object*)&l_Std_Time_Day_instHMulOffsetNat___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Day_instHDivOffsetInt___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instHDivOffsetInt___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Day_instHDivOffsetInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Day_instHDivOffsetInt___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Day_instHDivOffsetInt___closed__0 = (const lean_object*)&l_Std_Time_Day_instHDivOffsetInt___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Day_instHDivOffsetInt = (const lean_object*)&l_Std_Time_Day_instHDivOffsetInt___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Day_instHDivOffsetNat___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instHDivOffsetNat___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Day_instHDivOffsetNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Day_instHDivOffsetNat___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Day_instHDivOffsetNat___closed__0 = (const lean_object*)&l_Std_Time_Day_instHDivOffsetNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Day_instHDivOffsetNat = (const lean_object*)&l_Std_Time_Day_instHDivOffsetNat___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Day_Ordinal_instReprOfYear___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Day_Ordinal_instReprOfYear___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___redArg___closed__0 = (const lean_object*)&l_Std_Time_Day_Ordinal_instReprOfYear___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___redArg();
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instToStringOfYear___redArg();
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instToStringOfYear___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instToStringOfYear(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instToStringOfYear___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Day_Ordinal_instDecidableEqOfYear___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instDecidableEqOfYear___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Day_Ordinal_instDecidableEqOfYear(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instDecidableEqOfYear___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOrdOfYear(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOrdOfYear___boxed(lean_object*);
static const lean_string_object l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__0 = (const lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__0_value;
static const lean_string_object l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__1 = (const lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__1_value;
static const lean_string_object l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__2 = (const lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__2_value;
static const lean_string_object l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__3 = (const lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__3_value;
static const lean_ctor_object l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__4_value_aux_0),((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__4_value_aux_1),((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__4_value_aux_2),((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__4 = (const lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__4_value;
static const lean_array_object l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5 = (const lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5_value;
static const lean_string_object l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__6 = (const lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__6_value;
static const lean_ctor_object l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__7_value_aux_0),((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__7_value_aux_1),((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__7_value_aux_2),((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__7 = (const lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__7_value;
static const lean_string_object l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__8 = (const lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__8_value;
static const lean_ctor_object l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__9 = (const lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__9_value;
static const lean_string_object l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__10 = (const lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__10_value;
static const lean_ctor_object l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__11_value_aux_0),((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__11_value_aux_1),((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__11_value_aux_2),((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(53, 158, 1, 232, 101, 200, 191, 197)}};
static const lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__11 = (const lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__11_value;
static lean_once_cell_t l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__12;
static lean_once_cell_t l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__13;
static const lean_string_object l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__14 = (const lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__14_value;
static const lean_ctor_object l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__15_value_aux_0),((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__15_value_aux_1),((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__15_value_aux_2),((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__15 = (const lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__15_value;
static const lean_ctor_object l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__9_value),((lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5_value)}};
static const lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__16 = (const lean_object*)&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__16_value;
static lean_once_cell_t l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__17;
static lean_once_cell_t l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__18;
static lean_once_cell_t l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__19;
static lean_once_cell_t l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__20;
static lean_once_cell_t l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__21;
static lean_once_cell_t l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__22;
static lean_once_cell_t l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__23;
static lean_once_cell_t l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__24;
static lean_once_cell_t l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__25;
static lean_once_cell_t l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26;
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3;
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__0;
static lean_once_cell_t l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__1;
static lean_once_cell_t l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__2;
static lean_once_cell_t l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1(lean_object*);
static lean_once_cell_t l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__0;
static lean_once_cell_t l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__1;
static lean_once_cell_t l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__2;
static lean_once_cell_t l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instInhabitedOfYear___redArg();
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instInhabitedOfYear___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Day_Ordinal_instInhabitedOfYear___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Ordinal_instInhabitedOfYear___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instInhabitedOfYear(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instInhabitedOfYear___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofNat___auto__1;
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofNat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofNat(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Day_Ordinal_ofFin___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Ordinal_ofFin___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofFin(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_toOffset(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_toOffset___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_toOffset___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_toOffset___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_toOffset(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_toOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toOrdinal___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toOrdinal___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toOrdinal___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofInt(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofInt___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Day_Offset_toNanoseconds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Offset_toNanoseconds___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toNanoseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toNanoseconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofNanoseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofNanoseconds___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Day_Offset_toMilliseconds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Offset_toMilliseconds___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toMilliseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toMilliseconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofMilliseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofMilliseconds___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Day_Offset_toSeconds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Offset_toSeconds___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toSeconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toSeconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofSeconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofSeconds___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Day_Offset_toMinutes___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Offset_toMinutes___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toMinutes(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toMinutes___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofMinutes(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofMinutes___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Day_Offset_toHours___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Offset_toHours___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toHours(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toHours___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofHours(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofHours___boxed(lean_object*);
static lean_object* _init_l_Std_Time_Day_instReprOrdinal___aux__1___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instReprOrdinal___aux__1(lean_object* v_n_3_, lean_object* v_a_4_){
_start:
{
lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_5_ = lean_obj_once(&l_Std_Time_Day_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Day_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instReprOrdinal___aux__1___closed__0);
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
LEAN_EXPORT lean_object* l_Std_Time_Day_instReprOrdinal___aux__1___boxed(lean_object* v_n_12_, lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_Time_Day_instReprOrdinal___aux__1(v_n_12_, v_a_13_);
lean_dec(v_a_13_);
lean_dec(v_n_12_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instReprOrdinal___lam__0(lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
lean_object* v___x_17_; uint8_t v___x_18_; 
v___x_17_ = lean_obj_once(&l_Std_Time_Day_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Day_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instReprOrdinal___aux__1___closed__0);
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
LEAN_EXPORT lean_object* l_Std_Time_Day_instReprOrdinal___lam__0___boxed(lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Std_Time_Day_instReprOrdinal___lam__0(v___y_24_, v___y_25_);
lean_dec(v___y_25_);
lean_dec(v___y_24_);
return v_res_26_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableEqOrdinal___aux__1(lean_object* v_a_29_, lean_object* v_b_30_){
_start:
{
uint8_t v___x_31_; 
v___x_31_ = lean_int_dec_eq(v_a_29_, v_b_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableEqOrdinal___aux__1___boxed(lean_object* v_a_32_, lean_object* v_b_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l_Std_Time_Day_instDecidableEqOrdinal___aux__1(v_a_32_, v_b_33_);
lean_dec(v_b_33_);
lean_dec(v_a_32_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableEqOrdinal(lean_object* v_a_36_, lean_object* v_b_37_){
_start:
{
uint8_t v___x_38_; 
v___x_38_ = lean_int_dec_eq(v_a_36_, v_b_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableEqOrdinal___boxed(lean_object* v_a_39_, lean_object* v_b_40_){
_start:
{
uint8_t v_res_41_; lean_object* v_r_42_; 
v_res_41_ = l_Std_Time_Day_instDecidableEqOrdinal(v_a_39_, v_b_40_);
lean_dec(v_b_40_);
lean_dec(v_a_39_);
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
}
}
static lean_object* _init_l_Std_Time_Day_instLEOrdinal(void){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_box(0);
return v___x_43_;
}
}
static lean_object* _init_l_Std_Time_Day_instLTOrdinal(void){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_box(0);
return v___x_44_;
}
}
static lean_object* _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_unsigned_to_nat(1u);
v___x_46_ = lean_nat_to_int(v___x_45_);
return v___x_46_;
}
}
static lean_object* _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__1(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_unsigned_to_nat(30u);
v___x_48_ = lean_nat_to_int(v___x_47_);
return v___x_48_;
}
}
static lean_object* _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__2(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__1, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__1_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__1);
v___x_50_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_51_ = lean_int_add(v___x_50_, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__3(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_53_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__2, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__2_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__2);
v___x_54_ = lean_int_sub(v___x_53_, v___x_52_);
return v___x_54_;
}
}
static lean_object* _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v_range_57_; 
v___x_55_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_56_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__3);
v_range_57_ = lean_int_add(v___x_56_, v___x_55_);
return v_range_57_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instOfNatOrdinal___aux__1(lean_object* v_n_58_){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v_range_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_59_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_60_ = lean_nat_to_int(v_n_58_);
v_range_61_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4);
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
LEAN_EXPORT lean_object* l_Std_Time_Day_instOfNatOrdinal(lean_object* v_n_67_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v_range_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_68_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_69_ = lean_nat_to_int(v_n_67_);
v_range_70_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4);
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
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLeOrdinal___aux__1(lean_object* v_x_76_, lean_object* v_y_77_){
_start:
{
uint8_t v___x_78_; 
v___x_78_ = lean_int_dec_le(v_x_76_, v_y_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLeOrdinal___aux__1___boxed(lean_object* v_x_79_, lean_object* v_y_80_){
_start:
{
uint8_t v_res_81_; lean_object* v_r_82_; 
v_res_81_ = l_Std_Time_Day_instDecidableLeOrdinal___aux__1(v_x_79_, v_y_80_);
lean_dec(v_y_80_);
lean_dec(v_x_79_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLeOrdinal(lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
uint8_t v___x_85_; 
v___x_85_ = lean_int_dec_le(v___y_83_, v___y_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLeOrdinal___boxed(lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
uint8_t v_res_88_; lean_object* v_r_89_; 
v_res_88_ = l_Std_Time_Day_instDecidableLeOrdinal(v___y_86_, v___y_87_);
lean_dec(v___y_87_);
lean_dec(v___y_86_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLtOrdinal___aux__1(lean_object* v_x_90_, lean_object* v_y_91_){
_start:
{
uint8_t v___x_92_; 
v___x_92_ = lean_int_dec_lt(v_x_90_, v_y_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLtOrdinal___aux__1___boxed(lean_object* v_x_93_, lean_object* v_y_94_){
_start:
{
uint8_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = l_Std_Time_Day_instDecidableLtOrdinal___aux__1(v_x_93_, v_y_94_);
lean_dec(v_y_94_);
lean_dec(v_x_93_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLtOrdinal(lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
uint8_t v___x_99_; 
v___x_99_ = lean_int_dec_lt(v___y_97_, v___y_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLtOrdinal___boxed(lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
uint8_t v_res_102_; lean_object* v_r_103_; 
v_res_102_ = l_Std_Time_Day_instDecidableLtOrdinal(v___y_100_, v___y_101_);
lean_dec(v___y_101_);
lean_dec(v___y_100_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOrdinal___closed__0(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_105_ = lean_int_sub(v___x_104_, v___x_104_);
return v___x_105_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOrdinal___closed__1(void){
_start:
{
lean_object* v_range_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v_range_106_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4);
v___x_107_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOrdinal___closed__0, &l_Std_Time_Day_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Day_instInhabitedOrdinal___closed__0);
v___x_108_ = lean_int_emod(v___x_107_, v_range_106_);
return v___x_108_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOrdinal___closed__2(void){
_start:
{
lean_object* v_range_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v_range_109_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4);
v___x_110_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOrdinal___closed__1, &l_Std_Time_Day_instInhabitedOrdinal___closed__1_once, _init_l_Std_Time_Day_instInhabitedOrdinal___closed__1);
v___x_111_ = lean_int_add(v___x_110_, v_range_109_);
return v___x_111_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOrdinal___closed__3(void){
_start:
{
lean_object* v_range_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v_range_112_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4);
v___x_113_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOrdinal___closed__2, &l_Std_Time_Day_instInhabitedOrdinal___closed__2_once, _init_l_Std_Time_Day_instInhabitedOrdinal___closed__2);
v___x_114_ = lean_int_emod(v___x_113_, v_range_112_);
return v___x_114_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOrdinal___closed__4(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_115_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_116_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOrdinal___closed__3, &l_Std_Time_Day_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Day_instInhabitedOrdinal___closed__3);
v___x_117_ = lean_int_add(v___x_116_, v___x_115_);
return v___x_117_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOrdinal(void){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOrdinal___closed__4, &l_Std_Time_Day_instInhabitedOrdinal___closed__4_once, _init_l_Std_Time_Day_instInhabitedOrdinal___closed__4);
return v___x_118_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_instOrdOrdinal___aux__1(lean_object* v_x_119_, lean_object* v_y_120_){
_start:
{
uint8_t v___x_121_; 
v___x_121_ = lean_int_dec_lt(v_x_119_, v_y_120_);
if (v___x_121_ == 0)
{
uint8_t v___x_122_; 
v___x_122_ = lean_int_dec_eq(v_x_119_, v_y_120_);
if (v___x_122_ == 0)
{
uint8_t v___x_123_; 
v___x_123_ = 2;
return v___x_123_;
}
else
{
uint8_t v___x_124_; 
v___x_124_ = 1;
return v___x_124_;
}
}
else
{
uint8_t v___x_125_; 
v___x_125_ = 0;
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instOrdOrdinal___aux__1___boxed(lean_object* v_x_126_, lean_object* v_y_127_){
_start:
{
uint8_t v_res_128_; lean_object* v_r_129_; 
v_res_128_ = l_Std_Time_Day_instOrdOrdinal___aux__1(v_x_126_, v_y_127_);
lean_dec(v_y_127_);
lean_dec(v_x_126_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instReprOffset___aux__1(lean_object* v_x_132_, lean_object* v_p_133_){
_start:
{
lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_134_ = lean_obj_once(&l_Std_Time_Day_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Day_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instReprOrdinal___aux__1___closed__0);
v___x_135_ = lean_int_dec_lt(v_x_132_, v___x_134_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = l_Int_repr(v_x_132_);
v___x_137_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
return v___x_137_;
}
else
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_138_ = l_Int_repr(v_x_132_);
v___x_139_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
v___x_140_ = l_Repr_addAppParen(v___x_139_, v_p_133_);
return v___x_140_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instReprOffset___aux__1___boxed(lean_object* v_x_141_, lean_object* v_p_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Std_Time_Day_instReprOffset___aux__1(v_x_141_, v_p_142_);
lean_dec(v_p_142_);
lean_dec(v_x_141_);
return v_res_143_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableEqOffset___aux__1(lean_object* v_a_145_, lean_object* v_b_146_){
_start:
{
uint8_t v___x_147_; 
v___x_147_ = lean_int_dec_eq(v_a_145_, v_b_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableEqOffset___aux__1___boxed(lean_object* v_a_148_, lean_object* v_b_149_){
_start:
{
uint8_t v_res_150_; lean_object* v_r_151_; 
v_res_150_ = l_Std_Time_Day_instDecidableEqOffset___aux__1(v_a_148_, v_b_149_);
lean_dec(v_b_149_);
lean_dec(v_a_148_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Day_instDecidableEqOffset___aux__1_spec__0_spec__0(lean_object* v_a_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = lean_nat_to_int(v_a_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Day_instDecidableEqOffset___aux__1_spec__0(lean_object* v_a_154_){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_nat_to_int(v_a_154_);
v___x_156_ = l_Rat_ofInt(v___x_155_);
return v___x_156_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableEqOffset(lean_object* v_a_157_, lean_object* v_b_158_){
_start:
{
uint8_t v___x_159_; 
v___x_159_ = lean_int_dec_eq(v_a_157_, v_b_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableEqOffset___boxed(lean_object* v_a_160_, lean_object* v_b_161_){
_start:
{
uint8_t v_res_162_; lean_object* v_r_163_; 
v_res_162_ = l_Std_Time_Day_instDecidableEqOffset(v_a_160_, v_b_161_);
lean_dec(v_b_161_);
lean_dec(v_a_160_);
v_r_163_ = lean_box(v_res_162_);
return v_r_163_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOffset___aux__1___closed__0(void){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Std_Time_Internal_instInhabitedUnitVal_default___redArg();
return v___x_164_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOffset___aux__1(void){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOffset___aux__1___closed__0, &l_Std_Time_Day_instInhabitedOffset___aux__1___closed__0_once, _init_l_Std_Time_Day_instInhabitedOffset___aux__1___closed__0);
return v___x_165_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOffset(void){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOffset___aux__1___closed__0, &l_Std_Time_Day_instInhabitedOffset___aux__1___closed__0_once, _init_l_Std_Time_Day_instInhabitedOffset___aux__1___closed__0);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instAddOffset___aux__1(lean_object* v_u1_167_, lean_object* v_u2_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = lean_int_add(v_u1_167_, v_u2_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instAddOffset___aux__1___boxed(lean_object* v_u1_170_, lean_object* v_u2_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Std_Time_Day_instAddOffset___aux__1(v_u1_170_, v_u2_171_);
lean_dec(v_u2_171_);
lean_dec(v_u1_170_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instSubOffset___aux__1(lean_object* v_u1_175_, lean_object* v_u2_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = lean_int_sub(v_u1_175_, v_u2_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instSubOffset___aux__1___boxed(lean_object* v_u1_178_, lean_object* v_u2_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Std_Time_Day_instSubOffset___aux__1(v_u1_178_, v_u2_179_);
lean_dec(v_u2_179_);
lean_dec(v_u1_178_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instNegOffset___aux__1(lean_object* v_x_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = lean_int_neg(v_x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instNegOffset___aux__1___boxed(lean_object* v_x_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Std_Time_Day_instNegOffset___aux__1(v_x_185_);
lean_dec(v_x_185_);
return v_res_186_;
}
}
static lean_object* _init_l_Std_Time_Day_instLEOffset(void){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = lean_box(0);
return v___x_189_;
}
}
static lean_object* _init_l_Std_Time_Day_instLTOffset(void){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = lean_box(0);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instToStringOffset___aux__1(lean_object* v_n_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Int_repr(v_n_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instToStringOffset___aux__1___boxed(lean_object* v_n_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Std_Time_Day_instToStringOffset___aux__1(v_n_193_);
lean_dec(v_n_193_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instOfNatOffset(lean_object* v_n_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = lean_nat_to_int(v_n_197_);
return v___x_198_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLeOffset___aux__1(lean_object* v_x_199_, lean_object* v_y_200_){
_start:
{
uint8_t v___x_201_; 
v___x_201_ = lean_int_dec_le(v_x_199_, v_y_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLeOffset___aux__1___boxed(lean_object* v_x_202_, lean_object* v_y_203_){
_start:
{
uint8_t v_res_204_; lean_object* v_r_205_; 
v_res_204_ = l_Std_Time_Day_instDecidableLeOffset___aux__1(v_x_202_, v_y_203_);
lean_dec(v_y_203_);
lean_dec(v_x_202_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLeOffset(lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
uint8_t v___x_208_; 
v___x_208_ = lean_int_dec_le(v___y_206_, v___y_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLeOffset___boxed(lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
uint8_t v_res_211_; lean_object* v_r_212_; 
v_res_211_ = l_Std_Time_Day_instDecidableLeOffset(v___y_209_, v___y_210_);
lean_dec(v___y_210_);
lean_dec(v___y_209_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLtOffset___aux__1(lean_object* v_x_213_, lean_object* v_y_214_){
_start:
{
uint8_t v___x_215_; 
v___x_215_ = lean_int_dec_lt(v_x_213_, v_y_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLtOffset___aux__1___boxed(lean_object* v_x_216_, lean_object* v_y_217_){
_start:
{
uint8_t v_res_218_; lean_object* v_r_219_; 
v_res_218_ = l_Std_Time_Day_instDecidableLtOffset___aux__1(v_x_216_, v_y_217_);
lean_dec(v_y_217_);
lean_dec(v_x_216_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLtOffset(lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
uint8_t v___x_222_; 
v___x_222_ = lean_int_dec_lt(v___y_220_, v___y_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLtOffset___boxed(lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
uint8_t v_res_225_; lean_object* v_r_226_; 
v_res_225_ = l_Std_Time_Day_instDecidableLtOffset(v___y_223_, v___y_224_);
lean_dec(v___y_224_);
lean_dec(v___y_223_);
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_instOrdOffset___aux__1(lean_object* v_x_227_, lean_object* v_y_228_){
_start:
{
uint8_t v___x_229_; 
v___x_229_ = lean_int_dec_lt(v_x_227_, v_y_228_);
if (v___x_229_ == 0)
{
uint8_t v___x_230_; 
v___x_230_ = lean_int_dec_eq(v_x_227_, v_y_228_);
if (v___x_230_ == 0)
{
uint8_t v___x_231_; 
v___x_231_ = 2;
return v___x_231_;
}
else
{
uint8_t v___x_232_; 
v___x_232_ = 1;
return v___x_232_;
}
}
else
{
uint8_t v___x_233_; 
v___x_233_ = 0;
return v___x_233_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instOrdOffset___aux__1___boxed(lean_object* v_x_234_, lean_object* v_y_235_){
_start:
{
uint8_t v_res_236_; lean_object* v_r_237_; 
v_res_236_ = l_Std_Time_Day_instOrdOffset___aux__1(v_x_234_, v_y_235_);
lean_dec(v_y_235_);
lean_dec(v_x_234_);
v_r_237_ = lean_box(v_res_236_);
return v_r_237_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instHMulIntOffset___aux__1(lean_object* v_n_240_, lean_object* v_x_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = lean_int_mul(v_n_240_, v_x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instHMulIntOffset___aux__1___boxed(lean_object* v_n_243_, lean_object* v_x_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Std_Time_Day_instHMulIntOffset___aux__1(v_n_243_, v_x_244_);
lean_dec(v_x_244_);
lean_dec(v_n_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instHMulOffsetInt___aux__1(lean_object* v_x_248_, lean_object* v_n_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = lean_int_mul(v_x_248_, v_n_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instHMulOffsetInt___aux__1___boxed(lean_object* v_x_251_, lean_object* v_n_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Std_Time_Day_instHMulOffsetInt___aux__1(v_x_251_, v_n_252_);
lean_dec(v_n_252_);
lean_dec(v_x_251_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instHMulNatOffset___aux__1(lean_object* v_n_256_, lean_object* v_x_257_){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = lean_nat_to_int(v_n_256_);
v___x_259_ = lean_int_mul(v___x_258_, v_x_257_);
lean_dec(v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instHMulNatOffset___aux__1___boxed(lean_object* v_n_260_, lean_object* v_x_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Std_Time_Day_instHMulNatOffset___aux__1(v_n_260_, v_x_261_);
lean_dec(v_x_261_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instHMulOffsetNat___aux__1(lean_object* v_x_265_, lean_object* v_n_266_){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_nat_to_int(v_n_266_);
v___x_268_ = lean_int_mul(v_x_265_, v___x_267_);
lean_dec(v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instHMulOffsetNat___aux__1___boxed(lean_object* v_x_269_, lean_object* v_n_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Std_Time_Day_instHMulOffsetNat___aux__1(v_x_269_, v_n_270_);
lean_dec(v_x_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instHDivOffsetInt___aux__1(lean_object* v_x_274_, lean_object* v_n_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = lean_int_div(v_x_274_, v_n_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instHDivOffsetInt___aux__1___boxed(lean_object* v_x_277_, lean_object* v_n_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Std_Time_Day_instHDivOffsetInt___aux__1(v_x_277_, v_n_278_);
lean_dec(v_n_278_);
lean_dec(v_x_277_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instHDivOffsetNat___aux__1(lean_object* v_x_282_, lean_object* v_n_283_){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_nat_to_int(v_n_283_);
v___x_285_ = lean_int_div(v_x_282_, v___x_284_);
lean_dec(v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instHDivOffsetNat___aux__1___boxed(lean_object* v_x_286_, lean_object* v_n_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Std_Time_Day_instHDivOffsetNat___aux__1(v_x_286_, v_n_287_);
lean_dec(v_x_286_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt___redArg(lean_object* v_data_291_){
_start:
{
lean_inc(v_data_291_);
return v_data_291_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt___redArg___boxed(lean_object* v_data_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Std_Time_Day_Ordinal_ofInt___redArg(v_data_292_);
lean_dec(v_data_292_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt(lean_object* v_data_294_, lean_object* v_h_295_){
_start:
{
lean_inc(v_data_294_);
return v_data_294_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt___boxed(lean_object* v_data_296_, lean_object* v_h_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Std_Time_Day_Ordinal_ofInt(v_data_296_, v_h_297_);
lean_dec(v_data_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___redArg___lam__0(lean_object* v_r_299_, lean_object* v_p_300_){
_start:
{
lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_301_ = lean_obj_once(&l_Std_Time_Day_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Day_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instReprOrdinal___aux__1___closed__0);
v___x_302_ = lean_int_dec_lt(v_r_299_, v___x_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = l_Int_repr(v_r_299_);
v___x_304_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
return v___x_304_;
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_305_ = l_Int_repr(v_r_299_);
v___x_306_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
v___x_307_ = l_Repr_addAppParen(v___x_306_, v_p_300_);
return v___x_307_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___redArg___lam__0___boxed(lean_object* v_r_308_, lean_object* v_p_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Std_Time_Day_Ordinal_instReprOfYear___redArg___lam__0(v_r_308_, v_p_309_);
lean_dec(v_p_309_);
lean_dec(v_r_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___redArg(){
_start:
{
lean_object* v___f_313_; 
v___f_313_ = ((lean_object*)(l_Std_Time_Day_Ordinal_instReprOfYear___redArg___closed__0));
return v___f_313_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___redArg___boxed(lean_object* v___dummy_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Std_Time_Day_Ordinal_instReprOfYear___redArg();
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear(uint8_t v_leap_316_){
_start:
{
lean_object* v___f_317_; 
v___f_317_ = ((lean_object*)(l_Std_Time_Day_Ordinal_instReprOfYear___redArg___closed__0));
return v___f_317_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___boxed(lean_object* v_leap_318_){
_start:
{
uint8_t v_leap_boxed_319_; lean_object* v_res_320_; 
v_leap_boxed_319_ = lean_unbox(v_leap_318_);
v_res_320_ = l_Std_Time_Day_Ordinal_instReprOfYear(v_leap_boxed_319_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instToStringOfYear___redArg(){
_start:
{
lean_object* v___f_322_; 
v___f_322_ = ((lean_object*)(l_Std_Time_Day_instToStringOffset___closed__0));
return v___f_322_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instToStringOfYear___redArg___boxed(lean_object* v___dummy_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Std_Time_Day_Ordinal_instToStringOfYear___redArg();
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instToStringOfYear(uint8_t v_leap_325_){
_start:
{
lean_object* v___f_326_; 
v___f_326_ = ((lean_object*)(l_Std_Time_Day_instToStringOffset___closed__0));
return v___f_326_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instToStringOfYear___boxed(lean_object* v_leap_327_){
_start:
{
uint8_t v_leap_boxed_328_; lean_object* v_res_329_; 
v_leap_boxed_328_ = lean_unbox(v_leap_327_);
v_res_329_ = l_Std_Time_Day_Ordinal_instToStringOfYear(v_leap_boxed_328_);
return v_res_329_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1___redArg(lean_object* v_a_330_, lean_object* v_b_331_){
_start:
{
uint8_t v___x_332_; 
v___x_332_ = lean_int_dec_eq(v_a_330_, v_b_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1___redArg___boxed(lean_object* v_a_333_, lean_object* v_b_334_){
_start:
{
uint8_t v_res_335_; lean_object* v_r_336_; 
v_res_335_ = l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1___redArg(v_a_333_, v_b_334_);
lean_dec(v_b_334_);
lean_dec(v_a_333_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1(uint8_t v_leap_337_, lean_object* v_a_338_, lean_object* v_b_339_){
_start:
{
uint8_t v___x_340_; 
v___x_340_ = lean_int_dec_eq(v_a_338_, v_b_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1___boxed(lean_object* v_leap_341_, lean_object* v_a_342_, lean_object* v_b_343_){
_start:
{
uint8_t v_leap_boxed_344_; uint8_t v_res_345_; lean_object* v_r_346_; 
v_leap_boxed_344_ = lean_unbox(v_leap_341_);
v_res_345_ = l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1(v_leap_boxed_344_, v_a_342_, v_b_343_);
lean_dec(v_b_343_);
lean_dec(v_a_342_);
v_r_346_ = lean_box(v_res_345_);
return v_r_346_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_Ordinal_instDecidableEqOfYear___redArg(lean_object* v_a_347_, lean_object* v_b_348_){
_start:
{
uint8_t v___x_349_; 
v___x_349_ = lean_int_dec_eq(v_a_347_, v_b_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instDecidableEqOfYear___redArg___boxed(lean_object* v_a_350_, lean_object* v_b_351_){
_start:
{
uint8_t v_res_352_; lean_object* v_r_353_; 
v_res_352_ = l_Std_Time_Day_Ordinal_instDecidableEqOfYear___redArg(v_a_350_, v_b_351_);
lean_dec(v_b_351_);
lean_dec(v_a_350_);
v_r_353_ = lean_box(v_res_352_);
return v_r_353_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_Ordinal_instDecidableEqOfYear(uint8_t v_leap_354_, lean_object* v_a_355_, lean_object* v_b_356_){
_start:
{
uint8_t v___x_357_; 
v___x_357_ = lean_int_dec_eq(v_a_355_, v_b_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instDecidableEqOfYear___boxed(lean_object* v_leap_358_, lean_object* v_a_359_, lean_object* v_b_360_){
_start:
{
uint8_t v_leap_boxed_361_; uint8_t v_res_362_; lean_object* v_r_363_; 
v_leap_boxed_361_ = lean_unbox(v_leap_358_);
v_res_362_ = l_Std_Time_Day_Ordinal_instDecidableEqOfYear(v_leap_boxed_361_, v_a_359_, v_b_360_);
lean_dec(v_b_360_);
lean_dec(v_a_359_);
v_r_363_ = lean_box(v_res_362_);
return v_r_363_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___redArg(lean_object* v_x_364_, lean_object* v_y_365_){
_start:
{
uint8_t v___x_366_; 
v___x_366_ = lean_int_dec_lt(v_x_364_, v_y_365_);
if (v___x_366_ == 0)
{
uint8_t v___x_367_; 
v___x_367_ = lean_int_dec_eq(v_x_364_, v_y_365_);
if (v___x_367_ == 0)
{
uint8_t v___x_368_; 
v___x_368_ = 2;
return v___x_368_;
}
else
{
uint8_t v___x_369_; 
v___x_369_ = 1;
return v___x_369_;
}
}
else
{
uint8_t v___x_370_; 
v___x_370_ = 0;
return v___x_370_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___redArg___boxed(lean_object* v_x_371_, lean_object* v_y_372_){
_start:
{
uint8_t v_res_373_; lean_object* v_r_374_; 
v_res_373_ = l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___redArg(v_x_371_, v_y_372_);
lean_dec(v_y_372_);
lean_dec(v_x_371_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1(uint8_t v_leap_375_, lean_object* v_x_376_, lean_object* v_y_377_){
_start:
{
uint8_t v___x_378_; 
v___x_378_ = lean_int_dec_lt(v_x_376_, v_y_377_);
if (v___x_378_ == 0)
{
uint8_t v___x_379_; 
v___x_379_ = lean_int_dec_eq(v_x_376_, v_y_377_);
if (v___x_379_ == 0)
{
uint8_t v___x_380_; 
v___x_380_ = 2;
return v___x_380_;
}
else
{
uint8_t v___x_381_; 
v___x_381_ = 1;
return v___x_381_;
}
}
else
{
uint8_t v___x_382_; 
v___x_382_ = 0;
return v___x_382_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___boxed(lean_object* v_leap_383_, lean_object* v_x_384_, lean_object* v_y_385_){
_start:
{
uint8_t v_leap_boxed_386_; uint8_t v_res_387_; lean_object* v_r_388_; 
v_leap_boxed_386_ = lean_unbox(v_leap_383_);
v_res_387_ = l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1(v_leap_boxed_386_, v_x_384_, v_y_385_);
lean_dec(v_y_385_);
lean_dec(v_x_384_);
v_r_388_ = lean_box(v_res_387_);
return v_r_388_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOrdOfYear(uint8_t v_leap_389_){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = lean_box(v_leap_389_);
v___x_391_ = lean_alloc_closure((void*)(l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___boxed), 3, 1);
lean_closure_set(v___x_391_, 0, v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOrdOfYear___boxed(lean_object* v_leap_392_){
_start:
{
uint8_t v_leap_boxed_393_; lean_object* v_res_394_; 
v_leap_boxed_393_ = lean_unbox(v_leap_392_);
v_res_394_ = l_Std_Time_Day_Ordinal_instOrdOfYear(v_leap_boxed_393_);
return v_res_394_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__12(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__10));
v___x_422_ = l_Lean_mkAtom(v___x_421_);
return v___x_422_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__13(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_423_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__12, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__12_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__12);
v___x_424_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5));
v___x_425_ = lean_array_push(v___x_424_, v___x_423_);
return v___x_425_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__17(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__16));
v___x_437_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5));
v___x_438_ = lean_array_push(v___x_437_, v___x_436_);
return v___x_438_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__18(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_439_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__17, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__17_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__17);
v___x_440_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__15));
v___x_441_ = lean_box(2);
v___x_442_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
lean_ctor_set(v___x_442_, 1, v___x_440_);
lean_ctor_set(v___x_442_, 2, v___x_439_);
return v___x_442_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__19(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__18, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__18_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__18);
v___x_444_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__13, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__13_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__13);
v___x_445_ = lean_array_push(v___x_444_, v___x_443_);
return v___x_445_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__20(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_446_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__19, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__19_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__19);
v___x_447_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__11));
v___x_448_ = lean_box(2);
v___x_449_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
lean_ctor_set(v___x_449_, 1, v___x_447_);
lean_ctor_set(v___x_449_, 2, v___x_446_);
return v___x_449_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__21(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_450_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__20, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__20_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__20);
v___x_451_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5));
v___x_452_ = lean_array_push(v___x_451_, v___x_450_);
return v___x_452_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__22(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_453_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__21, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__21_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__21);
v___x_454_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__9));
v___x_455_ = lean_box(2);
v___x_456_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set(v___x_456_, 1, v___x_454_);
lean_ctor_set(v___x_456_, 2, v___x_453_);
return v___x_456_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__23(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_457_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__22, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__22_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__22);
v___x_458_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5));
v___x_459_ = lean_array_push(v___x_458_, v___x_457_);
return v___x_459_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__24(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_460_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__23, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__23_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__23);
v___x_461_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__7));
v___x_462_ = lean_box(2);
v___x_463_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
lean_ctor_set(v___x_463_, 1, v___x_461_);
lean_ctor_set(v___x_463_, 2, v___x_460_);
return v___x_463_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__25(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_464_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__24, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__24_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__24);
v___x_465_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5));
v___x_466_ = lean_array_push(v___x_465_, v___x_464_);
return v___x_466_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_467_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__25, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__25_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__25);
v___x_468_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__4));
v___x_469_ = lean_box(2);
v___x_470_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
lean_ctor_set(v___x_470_, 1, v___x_468_);
lean_ctor_set(v___x_470_, 2, v___x_467_);
return v___x_470_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3(void){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___redArg(lean_object* v_data_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = lean_nat_to_int(v_data_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat(uint8_t v_leap_474_, lean_object* v_data_475_, lean_object* v_h_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = lean_nat_to_int(v_data_475_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___boxed(lean_object* v_leap_478_, lean_object* v_data_479_, lean_object* v_h_480_){
_start:
{
uint8_t v_leap_boxed_481_; lean_object* v_res_482_; 
v_leap_boxed_481_ = lean_unbox(v_leap_478_);
v_res_482_ = l_Std_Time_Day_Ordinal_OfYear_ofNat(v_leap_boxed_481_, v_data_479_, v_h_480_);
return v_res_482_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__0(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_unsigned_to_nat(365u);
v___x_484_ = lean_nat_to_int(v___x_483_);
return v___x_484_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__1(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_485_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__0, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__0_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__0);
v___x_486_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_487_ = lean_int_add(v___x_486_, v___x_485_);
return v___x_487_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__2(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_488_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_489_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__1, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__1_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__1);
v___x_490_ = lean_int_sub(v___x_489_, v___x_488_);
return v___x_490_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v_range_493_; 
v___x_491_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_492_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__2, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__2_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__2);
v_range_493_ = lean_int_add(v___x_492_, v___x_491_);
return v_range_493_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1(lean_object* v_n_494_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v_range_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_495_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_496_ = lean_nat_to_int(v_n_494_);
v_range_497_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3);
v___x_498_ = lean_int_sub(v___x_496_, v___x_495_);
lean_dec(v___x_496_);
v___x_499_ = lean_int_emod(v___x_498_, v_range_497_);
lean_dec(v___x_498_);
v___x_500_ = lean_int_add(v___x_499_, v_range_497_);
lean_dec(v___x_499_);
v___x_501_ = lean_int_emod(v___x_500_, v_range_497_);
lean_dec(v___x_500_);
v___x_502_ = lean_int_add(v___x_501_, v___x_495_);
lean_dec(v___x_501_);
return v___x_502_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__0(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_unsigned_to_nat(364u);
v___x_504_ = lean_nat_to_int(v___x_503_);
return v___x_504_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__1(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_505_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__0, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__0_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__0);
v___x_506_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_507_ = lean_int_add(v___x_506_, v___x_505_);
return v___x_507_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__2(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_508_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_509_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__1, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__1_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__1);
v___x_510_ = lean_int_sub(v___x_509_, v___x_508_);
return v___x_510_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v_range_513_; 
v___x_511_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_512_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__2, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__2_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__2);
v_range_513_ = lean_int_add(v___x_512_, v___x_511_);
return v_range_513_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3(lean_object* v_n_514_){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v_range_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_515_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_516_ = lean_nat_to_int(v_n_514_);
v_range_517_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3);
v___x_518_ = lean_int_sub(v___x_516_, v___x_515_);
lean_dec(v___x_516_);
v___x_519_ = lean_int_emod(v___x_518_, v_range_517_);
lean_dec(v___x_518_);
v___x_520_ = lean_int_add(v___x_519_, v_range_517_);
lean_dec(v___x_519_);
v___x_521_ = lean_int_emod(v___x_520_, v_range_517_);
lean_dec(v___x_520_);
v___x_522_ = lean_int_add(v___x_521_, v___x_515_);
lean_dec(v___x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear(uint8_t v_leap_523_, lean_object* v_n_524_){
_start:
{
if (v_leap_523_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v_range_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_525_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_526_ = lean_nat_to_int(v_n_524_);
v_range_527_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3);
v___x_528_ = lean_int_sub(v___x_526_, v___x_525_);
lean_dec(v___x_526_);
v___x_529_ = lean_int_emod(v___x_528_, v_range_527_);
lean_dec(v___x_528_);
v___x_530_ = lean_int_add(v___x_529_, v_range_527_);
lean_dec(v___x_529_);
v___x_531_ = lean_int_emod(v___x_530_, v_range_527_);
lean_dec(v___x_530_);
v___x_532_ = lean_int_add(v___x_531_, v___x_525_);
lean_dec(v___x_531_);
return v___x_532_;
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v_range_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_533_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_534_ = lean_nat_to_int(v_n_524_);
v_range_535_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3);
v___x_536_ = lean_int_sub(v___x_534_, v___x_533_);
lean_dec(v___x_534_);
v___x_537_ = lean_int_emod(v___x_536_, v_range_535_);
lean_dec(v___x_536_);
v___x_538_ = lean_int_add(v___x_537_, v_range_535_);
lean_dec(v___x_537_);
v___x_539_ = lean_int_emod(v___x_538_, v_range_535_);
lean_dec(v___x_538_);
v___x_540_ = lean_int_add(v___x_539_, v___x_533_);
lean_dec(v___x_539_);
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear___boxed(lean_object* v_leap_541_, lean_object* v_n_542_){
_start:
{
uint8_t v_leap_boxed_543_; lean_object* v_res_544_; 
v_leap_boxed_543_ = lean_unbox(v_leap_541_);
v_res_544_ = l_Std_Time_Day_Ordinal_instOfNatOfYear(v_leap_boxed_543_, v_n_542_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instInhabitedOfYear___redArg(){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instInhabitedOfYear___redArg___boxed(lean_object* v___dummy_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Std_Time_Day_Ordinal_instInhabitedOfYear___redArg();
return v_res_548_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instInhabitedOfYear___closed__0(void){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Std_Time_Day_Ordinal_instInhabitedOfYear___redArg();
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instInhabitedOfYear(uint8_t v_leap_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instInhabitedOfYear___closed__0, &l_Std_Time_Day_Ordinal_instInhabitedOfYear___closed__0_once, _init_l_Std_Time_Day_Ordinal_instInhabitedOfYear___closed__0);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instInhabitedOfYear___boxed(lean_object* v_leap_552_){
_start:
{
uint8_t v_leap_boxed_553_; lean_object* v_res_554_; 
v_leap_boxed_553_ = lean_unbox(v_leap_552_);
v_res_554_ = l_Std_Time_Day_Ordinal_instInhabitedOfYear(v_leap_boxed_553_);
return v_res_554_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_ofNat___auto__1(void){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofNat___redArg(lean_object* v_data_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = lean_nat_to_int(v_data_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofNat(lean_object* v_data_558_, lean_object* v_h_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = lean_nat_to_int(v_data_558_);
return v___x_560_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_ofFin___closed__0(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = lean_unsigned_to_nat(1u);
v___x_562_ = lean_nat_to_int(v___x_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofFin(lean_object* v_data_563_){
_start:
{
lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_564_ = lean_unsigned_to_nat(1u);
v___x_565_ = lean_nat_dec_le(v___x_564_, v_data_563_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; 
lean_dec(v_data_563_);
v___x_566_ = lean_obj_once(&l_Std_Time_Day_Ordinal_ofFin___closed__0, &l_Std_Time_Day_Ordinal_ofFin___closed__0_once, _init_l_Std_Time_Day_Ordinal_ofFin___closed__0);
return v___x_566_;
}
else
{
lean_object* v___x_567_; 
v___x_567_ = lean_nat_to_int(v_data_563_);
return v___x_567_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_toOffset(lean_object* v_ordinal_568_){
_start:
{
lean_inc(v_ordinal_568_);
return v_ordinal_568_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_toOffset___boxed(lean_object* v_ordinal_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Std_Time_Day_Ordinal_toOffset(v_ordinal_569_);
lean_dec(v_ordinal_569_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_toOffset___redArg(lean_object* v_ofYear_571_){
_start:
{
lean_inc(v_ofYear_571_);
return v_ofYear_571_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_toOffset___redArg___boxed(lean_object* v_ofYear_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Std_Time_Day_Ordinal_OfYear_toOffset___redArg(v_ofYear_572_);
lean_dec(v_ofYear_572_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_toOffset(uint8_t v_leap_574_, lean_object* v_ofYear_575_){
_start:
{
lean_inc(v_ofYear_575_);
return v_ofYear_575_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_toOffset___boxed(lean_object* v_leap_576_, lean_object* v_ofYear_577_){
_start:
{
uint8_t v_leap_boxed_578_; lean_object* v_res_579_; 
v_leap_boxed_578_ = lean_unbox(v_leap_576_);
v_res_579_ = l_Std_Time_Day_Ordinal_OfYear_toOffset(v_leap_boxed_578_, v_ofYear_577_);
lean_dec(v_ofYear_577_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toOrdinal___redArg(lean_object* v_off_580_){
_start:
{
lean_inc(v_off_580_);
return v_off_580_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toOrdinal___redArg___boxed(lean_object* v_off_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Std_Time_Day_Offset_toOrdinal___redArg(v_off_581_);
lean_dec(v_off_581_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toOrdinal(lean_object* v_off_583_, lean_object* v_h_584_){
_start:
{
lean_inc(v_off_583_);
return v_off_583_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toOrdinal___boxed(lean_object* v_off_585_, lean_object* v_h_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Std_Time_Day_Offset_toOrdinal(v_off_585_, v_h_586_);
lean_dec(v_off_585_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofNat(lean_object* v_data_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = lean_nat_to_int(v_data_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofInt(lean_object* v_data_590_){
_start:
{
lean_inc(v_data_590_);
return v_data_590_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofInt___boxed(lean_object* v_data_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Std_Time_Day_Offset_ofInt(v_data_591_);
lean_dec(v_data_591_);
return v_res_592_;
}
}
static lean_object* _init_l_Std_Time_Day_Offset_toNanoseconds___closed__0(void){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_593_ = lean_cstr_to_nat("86400000000000");
v___x_594_ = lean_nat_to_int(v___x_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toNanoseconds(lean_object* v_days_595_){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_obj_once(&l_Std_Time_Day_Offset_toNanoseconds___closed__0, &l_Std_Time_Day_Offset_toNanoseconds___closed__0_once, _init_l_Std_Time_Day_Offset_toNanoseconds___closed__0);
v___x_597_ = lean_int_mul(v_days_595_, v___x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toNanoseconds___boxed(lean_object* v_days_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Std_Time_Day_Offset_toNanoseconds(v_days_598_);
lean_dec(v_days_598_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofNanoseconds(lean_object* v_ns_600_){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = lean_obj_once(&l_Std_Time_Day_Offset_toNanoseconds___closed__0, &l_Std_Time_Day_Offset_toNanoseconds___closed__0_once, _init_l_Std_Time_Day_Offset_toNanoseconds___closed__0);
v___x_602_ = lean_int_ediv(v_ns_600_, v___x_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofNanoseconds___boxed(lean_object* v_ns_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Std_Time_Day_Offset_ofNanoseconds(v_ns_603_);
lean_dec(v_ns_603_);
return v_res_604_;
}
}
static lean_object* _init_l_Std_Time_Day_Offset_toMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_unsigned_to_nat(86400000u);
v___x_606_ = lean_nat_to_int(v___x_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toMilliseconds(lean_object* v_days_607_){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_obj_once(&l_Std_Time_Day_Offset_toMilliseconds___closed__0, &l_Std_Time_Day_Offset_toMilliseconds___closed__0_once, _init_l_Std_Time_Day_Offset_toMilliseconds___closed__0);
v___x_609_ = lean_int_mul(v_days_607_, v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toMilliseconds___boxed(lean_object* v_days_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Std_Time_Day_Offset_toMilliseconds(v_days_610_);
lean_dec(v_days_610_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofMilliseconds(lean_object* v_ms_612_){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = lean_obj_once(&l_Std_Time_Day_Offset_toMilliseconds___closed__0, &l_Std_Time_Day_Offset_toMilliseconds___closed__0_once, _init_l_Std_Time_Day_Offset_toMilliseconds___closed__0);
v___x_614_ = lean_int_ediv(v_ms_612_, v___x_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofMilliseconds___boxed(lean_object* v_ms_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Std_Time_Day_Offset_ofMilliseconds(v_ms_615_);
lean_dec(v_ms_615_);
return v_res_616_;
}
}
static lean_object* _init_l_Std_Time_Day_Offset_toSeconds___closed__0(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_unsigned_to_nat(86400u);
v___x_618_ = lean_nat_to_int(v___x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toSeconds(lean_object* v_days_619_){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_obj_once(&l_Std_Time_Day_Offset_toSeconds___closed__0, &l_Std_Time_Day_Offset_toSeconds___closed__0_once, _init_l_Std_Time_Day_Offset_toSeconds___closed__0);
v___x_621_ = lean_int_mul(v_days_619_, v___x_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toSeconds___boxed(lean_object* v_days_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Std_Time_Day_Offset_toSeconds(v_days_622_);
lean_dec(v_days_622_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofSeconds(lean_object* v_secs_624_){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_obj_once(&l_Std_Time_Day_Offset_toSeconds___closed__0, &l_Std_Time_Day_Offset_toSeconds___closed__0_once, _init_l_Std_Time_Day_Offset_toSeconds___closed__0);
v___x_626_ = lean_int_ediv(v_secs_624_, v___x_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofSeconds___boxed(lean_object* v_secs_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Std_Time_Day_Offset_ofSeconds(v_secs_627_);
lean_dec(v_secs_627_);
return v_res_628_;
}
}
static lean_object* _init_l_Std_Time_Day_Offset_toMinutes___closed__0(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_unsigned_to_nat(1440u);
v___x_630_ = lean_nat_to_int(v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toMinutes(lean_object* v_days_631_){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_obj_once(&l_Std_Time_Day_Offset_toMinutes___closed__0, &l_Std_Time_Day_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Day_Offset_toMinutes___closed__0);
v___x_633_ = lean_int_mul(v_days_631_, v___x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toMinutes___boxed(lean_object* v_days_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Std_Time_Day_Offset_toMinutes(v_days_634_);
lean_dec(v_days_634_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofMinutes(lean_object* v_minutes_636_){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = lean_obj_once(&l_Std_Time_Day_Offset_toMinutes___closed__0, &l_Std_Time_Day_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Day_Offset_toMinutes___closed__0);
v___x_638_ = lean_int_ediv(v_minutes_636_, v___x_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofMinutes___boxed(lean_object* v_minutes_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Std_Time_Day_Offset_ofMinutes(v_minutes_639_);
lean_dec(v_minutes_639_);
return v_res_640_;
}
}
static lean_object* _init_l_Std_Time_Day_Offset_toHours___closed__0(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = lean_unsigned_to_nat(24u);
v___x_642_ = lean_nat_to_int(v___x_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toHours(lean_object* v_days_643_){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = lean_obj_once(&l_Std_Time_Day_Offset_toHours___closed__0, &l_Std_Time_Day_Offset_toHours___closed__0_once, _init_l_Std_Time_Day_Offset_toHours___closed__0);
v___x_645_ = lean_int_mul(v_days_643_, v___x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toHours___boxed(lean_object* v_days_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Std_Time_Day_Offset_toHours(v_days_646_);
lean_dec(v_days_646_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofHours(lean_object* v_hours_648_){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_obj_once(&l_Std_Time_Day_Offset_toHours___closed__0, &l_Std_Time_Day_Offset_toHours___closed__0_once, _init_l_Std_Time_Day_Offset_toHours___closed__0);
v___x_650_ = lean_int_ediv(v_hours_648_, v___x_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofHours___boxed(lean_object* v_hours_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Std_Time_Day_Offset_ofHours(v_hours_651_);
lean_dec(v_hours_651_);
return v_res_652_;
}
}
lean_object* runtime_initialize_Std_Time_Time(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Date_Unit_Day(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Time_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_Day_instLEOrdinal = _init_l_Std_Time_Day_instLEOrdinal();
lean_mark_persistent(l_Std_Time_Day_instLEOrdinal);
l_Std_Time_Day_instLTOrdinal = _init_l_Std_Time_Day_instLTOrdinal();
lean_mark_persistent(l_Std_Time_Day_instLTOrdinal);
l_Std_Time_Day_instInhabitedOrdinal = _init_l_Std_Time_Day_instInhabitedOrdinal();
lean_mark_persistent(l_Std_Time_Day_instInhabitedOrdinal);
l_Std_Time_Day_instInhabitedOffset___aux__1 = _init_l_Std_Time_Day_instInhabitedOffset___aux__1();
lean_mark_persistent(l_Std_Time_Day_instInhabitedOffset___aux__1);
l_Std_Time_Day_instInhabitedOffset = _init_l_Std_Time_Day_instInhabitedOffset();
lean_mark_persistent(l_Std_Time_Day_instInhabitedOffset);
l_Std_Time_Day_instLEOffset = _init_l_Std_Time_Day_instLEOffset();
lean_mark_persistent(l_Std_Time_Day_instLEOffset);
l_Std_Time_Day_instLTOffset = _init_l_Std_Time_Day_instLTOffset();
lean_mark_persistent(l_Std_Time_Day_instLTOffset);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Date_Unit_Day(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3 = _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3();
lean_mark_persistent(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3);
l_Std_Time_Day_Ordinal_ofNat___auto__1 = _init_l_Std_Time_Day_Ordinal_ofNat___auto__1();
lean_mark_persistent(l_Std_Time_Day_Ordinal_ofNat___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Time(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Date_Unit_Day(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Date_Unit_Day(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Date_Unit_Day(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Date_Unit_Day(builtin);
}
#ifdef __cplusplus
}
#endif
