// Lean compiler output
// Module: Std.Time.Date.Unit.Month
// Imports: public import Std.Time.Date.Unit.Day import Init.Data.Fin.Lemmas
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
lean_object* l_Int_ediv___boxed(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_instInhabitedUnitVal_default___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
lean_object* l_Int_repr___boxed(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Int_mul___boxed(lean_object*, lean_object*);
lean_object* l_Int_add___boxed(lean_object*, lean_object*);
lean_object* l_Rat_instNatCast___lam__0(lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Int_neg___boxed(lean_object*);
lean_object* l_Int_sub___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instReprOrdinal___aux__1___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Month_instReprOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instReprOrdinal___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instReprOrdinal___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instReprOrdinal___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Month_instReprOrdinal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Month_instReprOrdinal___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Month_instReprOrdinal___closed__0 = (const lean_object*)&l_Std_Time_Month_instReprOrdinal___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Month_instReprOrdinal = (const lean_object*)&l_Std_Time_Month_instReprOrdinal___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableEqOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableEqOrdinal___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableEqOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableEqOrdinal___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instLEOrdinal;
LEAN_EXPORT lean_object* l_Std_Time_Month_instLTOrdinal;
static lean_once_cell_t l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0;
static lean_once_cell_t l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1;
static lean_once_cell_t l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__2;
static lean_once_cell_t l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__3;
static lean_once_cell_t l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4;
LEAN_EXPORT lean_object* l_Std_Time_Month_instOfNatOrdinal___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instOfNatOrdinal(lean_object*);
static lean_once_cell_t l_Std_Time_Month_instInhabitedOrdinal___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instInhabitedOrdinal___closed__0;
static lean_once_cell_t l_Std_Time_Month_instInhabitedOrdinal___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instInhabitedOrdinal___closed__1;
static lean_once_cell_t l_Std_Time_Month_instInhabitedOrdinal___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instInhabitedOrdinal___closed__2;
static lean_once_cell_t l_Std_Time_Month_instInhabitedOrdinal___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instInhabitedOrdinal___closed__3;
static lean_once_cell_t l_Std_Time_Month_instInhabitedOrdinal___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instInhabitedOrdinal___closed__4;
LEAN_EXPORT lean_object* l_Std_Time_Month_instInhabitedOrdinal;
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableLeOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableLeOrdinal___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableLeOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableLeOrdinal___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableLtOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableLtOrdinal___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableLtOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableLtOrdinal___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Month_instOrdOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instOrdOrdinal___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Month_instOrdOrdinal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Month_instOrdOrdinal___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Month_instOrdOrdinal___closed__0 = (const lean_object*)&l_Std_Time_Month_instOrdOrdinal___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Month_instOrdOrdinal = (const lean_object*)&l_Std_Time_Month_instOrdOrdinal___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Month_instReprOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instReprOffset___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT const lean_object* l_Std_Time_Month_instReprOffset = (const lean_object*)&l_Std_Time_Month_instReprOrdinal___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableEqOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableEqOffset___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableEqOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableEqOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instInhabitedOffset___aux__1;
LEAN_EXPORT lean_object* l_Std_Time_Month_instInhabitedOffset;
LEAN_EXPORT lean_object* l_Std_Time_Month_instAddOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instAddOffset___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Month_instAddOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Month_instAddOffset___closed__0 = (const lean_object*)&l_Std_Time_Month_instAddOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Month_instAddOffset = (const lean_object*)&l_Std_Time_Month_instAddOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Month_instSubOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instSubOffset___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Month_instSubOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Month_instSubOffset___closed__0 = (const lean_object*)&l_Std_Time_Month_instSubOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Month_instSubOffset = (const lean_object*)&l_Std_Time_Month_instSubOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Month_instMulOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instMulOffset___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Month_instMulOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Month_instMulOffset___closed__0 = (const lean_object*)&l_Std_Time_Month_instMulOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Month_instMulOffset = (const lean_object*)&l_Std_Time_Month_instMulOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Month_instDivOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instDivOffset___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Month_instDivOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_ediv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Month_instDivOffset___closed__0 = (const lean_object*)&l_Std_Time_Month_instDivOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Month_instDivOffset = (const lean_object*)&l_Std_Time_Month_instDivOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Month_instNegOffset___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instNegOffset___aux__1___boxed(lean_object*);
static const lean_closure_object l_Std_Time_Month_instNegOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Month_instNegOffset___closed__0 = (const lean_object*)&l_Std_Time_Month_instNegOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Month_instNegOffset = (const lean_object*)&l_Std_Time_Month_instNegOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Month_instToStringOffset___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instToStringOffset___aux__1___boxed(lean_object*);
static const lean_closure_object l_Std_Time_Month_instToStringOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_repr___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Month_instToStringOffset___closed__0 = (const lean_object*)&l_Std_Time_Month_instToStringOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Month_instToStringOffset = (const lean_object*)&l_Std_Time_Month_instToStringOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Month_instLTOffset;
LEAN_EXPORT lean_object* l_Std_Time_Month_instLEOffset;
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableLeOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableLeOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableLtOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableLtOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instOfNatOffset(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Month_instOrdOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instOrdOffset___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Month_instOrdOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Month_instOrdOffset___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Month_instOrdOffset___closed__0 = (const lean_object*)&l_Std_Time_Month_instOrdOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Month_instOrdOffset = (const lean_object*)&l_Std_Time_Month_instOrdOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Month_instReprQuarter___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instReprQuarter___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT const lean_object* l_Std_Time_Month_instReprQuarter = (const lean_object*)&l_Std_Time_Month_instReprOrdinal___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableEqQuarter___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableEqQuarter___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableEqQuarter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableEqQuarter___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instLTQuarter;
LEAN_EXPORT lean_object* l_Std_Time_Month_instLEQuarter;
static lean_once_cell_t l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0;
static lean_once_cell_t l_Std_Time_Month_instOfNatQuarter___aux__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instOfNatQuarter___aux__1___closed__1;
static lean_once_cell_t l_Std_Time_Month_instOfNatQuarter___aux__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instOfNatQuarter___aux__1___closed__2;
static lean_once_cell_t l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_Month_instOfNatQuarter___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instOfNatQuarter(lean_object*);
static lean_once_cell_t l_Std_Time_Month_instInhabitedQuarter___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instInhabitedQuarter___closed__0;
static lean_once_cell_t l_Std_Time_Month_instInhabitedQuarter___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instInhabitedQuarter___closed__1;
static lean_once_cell_t l_Std_Time_Month_instInhabitedQuarter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instInhabitedQuarter___closed__2;
static lean_once_cell_t l_Std_Time_Month_instInhabitedQuarter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instInhabitedQuarter___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_Month_instInhabitedQuarter;
LEAN_EXPORT uint8_t l_Std_Time_Month_instOrdQuarter___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instOrdQuarter___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Month_instOrdQuarter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Month_instOrdQuarter___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Month_instOrdQuarter___closed__0 = (const lean_object*)&l_Std_Time_Month_instOrdQuarter___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Month_instOrdQuarter = (const lean_object*)&l_Std_Time_Month_instOrdQuarter___closed__0_value;
static lean_once_cell_t l_Std_Time_Month_Quarter_ofMonth___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Quarter_ofMonth___closed__0;
static lean_once_cell_t l_Std_Time_Month_Quarter_ofMonth___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Quarter_ofMonth___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_Month_Quarter_ofMonth(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_Quarter_ofMonth___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_Offset_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_Offset_ofInt(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_Offset_ofInt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_january;
static lean_once_cell_t l_Std_Time_Month_Ordinal_february___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_february___closed__0;
static lean_once_cell_t l_Std_Time_Month_Ordinal_february___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_february___closed__1;
static lean_once_cell_t l_Std_Time_Month_Ordinal_february___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_february___closed__2;
static lean_once_cell_t l_Std_Time_Month_Ordinal_february___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_february___closed__3;
static lean_once_cell_t l_Std_Time_Month_Ordinal_february___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_february___closed__4;
static lean_once_cell_t l_Std_Time_Month_Ordinal_february___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_february___closed__5;
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_february;
static lean_once_cell_t l_Std_Time_Month_Ordinal_march___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_march___closed__0;
static lean_once_cell_t l_Std_Time_Month_Ordinal_march___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_march___closed__1;
static lean_once_cell_t l_Std_Time_Month_Ordinal_march___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_march___closed__2;
static lean_once_cell_t l_Std_Time_Month_Ordinal_march___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_march___closed__3;
static lean_once_cell_t l_Std_Time_Month_Ordinal_march___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_march___closed__4;
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_march;
static lean_once_cell_t l_Std_Time_Month_Ordinal_april___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_april___closed__0;
static lean_once_cell_t l_Std_Time_Month_Ordinal_april___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_april___closed__1;
static lean_once_cell_t l_Std_Time_Month_Ordinal_april___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_april___closed__2;
static lean_once_cell_t l_Std_Time_Month_Ordinal_april___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_april___closed__3;
static lean_once_cell_t l_Std_Time_Month_Ordinal_april___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_april___closed__4;
static lean_once_cell_t l_Std_Time_Month_Ordinal_april___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_april___closed__5;
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_april;
static lean_once_cell_t l_Std_Time_Month_Ordinal_may___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_may___closed__0;
static lean_once_cell_t l_Std_Time_Month_Ordinal_may___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_may___closed__1;
static lean_once_cell_t l_Std_Time_Month_Ordinal_may___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_may___closed__2;
static lean_once_cell_t l_Std_Time_Month_Ordinal_may___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_may___closed__3;
static lean_once_cell_t l_Std_Time_Month_Ordinal_may___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_may___closed__4;
static lean_once_cell_t l_Std_Time_Month_Ordinal_may___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_may___closed__5;
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_may;
static lean_once_cell_t l_Std_Time_Month_Ordinal_june___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_june___closed__0;
static lean_once_cell_t l_Std_Time_Month_Ordinal_june___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_june___closed__1;
static lean_once_cell_t l_Std_Time_Month_Ordinal_june___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_june___closed__2;
static lean_once_cell_t l_Std_Time_Month_Ordinal_june___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_june___closed__3;
static lean_once_cell_t l_Std_Time_Month_Ordinal_june___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_june___closed__4;
static lean_once_cell_t l_Std_Time_Month_Ordinal_june___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_june___closed__5;
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_june;
static lean_once_cell_t l_Std_Time_Month_Ordinal_july___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_july___closed__0;
static lean_once_cell_t l_Std_Time_Month_Ordinal_july___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_july___closed__1;
static lean_once_cell_t l_Std_Time_Month_Ordinal_july___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_july___closed__2;
static lean_once_cell_t l_Std_Time_Month_Ordinal_july___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_july___closed__3;
static lean_once_cell_t l_Std_Time_Month_Ordinal_july___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_july___closed__4;
static lean_once_cell_t l_Std_Time_Month_Ordinal_july___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_july___closed__5;
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_july;
static lean_once_cell_t l_Std_Time_Month_Ordinal_august___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_august___closed__0;
static lean_once_cell_t l_Std_Time_Month_Ordinal_august___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_august___closed__1;
static lean_once_cell_t l_Std_Time_Month_Ordinal_august___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_august___closed__2;
static lean_once_cell_t l_Std_Time_Month_Ordinal_august___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_august___closed__3;
static lean_once_cell_t l_Std_Time_Month_Ordinal_august___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_august___closed__4;
static lean_once_cell_t l_Std_Time_Month_Ordinal_august___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_august___closed__5;
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_august;
static lean_once_cell_t l_Std_Time_Month_Ordinal_september___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_september___closed__0;
static lean_once_cell_t l_Std_Time_Month_Ordinal_september___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_september___closed__1;
static lean_once_cell_t l_Std_Time_Month_Ordinal_september___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_september___closed__2;
static lean_once_cell_t l_Std_Time_Month_Ordinal_september___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_september___closed__3;
static lean_once_cell_t l_Std_Time_Month_Ordinal_september___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_september___closed__4;
static lean_once_cell_t l_Std_Time_Month_Ordinal_september___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_september___closed__5;
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_september;
static lean_once_cell_t l_Std_Time_Month_Ordinal_october___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_october___closed__0;
static lean_once_cell_t l_Std_Time_Month_Ordinal_october___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_october___closed__1;
static lean_once_cell_t l_Std_Time_Month_Ordinal_october___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_october___closed__2;
static lean_once_cell_t l_Std_Time_Month_Ordinal_october___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_october___closed__3;
static lean_once_cell_t l_Std_Time_Month_Ordinal_october___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_october___closed__4;
static lean_once_cell_t l_Std_Time_Month_Ordinal_october___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_october___closed__5;
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_october;
static lean_once_cell_t l_Std_Time_Month_Ordinal_november___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_november___closed__0;
static lean_once_cell_t l_Std_Time_Month_Ordinal_november___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_november___closed__1;
static lean_once_cell_t l_Std_Time_Month_Ordinal_november___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_november___closed__2;
static lean_once_cell_t l_Std_Time_Month_Ordinal_november___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_november___closed__3;
static lean_once_cell_t l_Std_Time_Month_Ordinal_november___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_november___closed__4;
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_november;
static lean_once_cell_t l_Std_Time_Month_Ordinal_december___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_december___closed__0;
static lean_once_cell_t l_Std_Time_Month_Ordinal_december___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_december___closed__1;
static lean_once_cell_t l_Std_Time_Month_Ordinal_december___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_december___closed__2;
static lean_once_cell_t l_Std_Time_Month_Ordinal_december___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_december___closed__3;
static lean_once_cell_t l_Std_Time_Month_Ordinal_december___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_december___closed__4;
static lean_once_cell_t l_Std_Time_Month_Ordinal_december___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_december___closed__5;
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_december;
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toOffset(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toOffset___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_ofInt___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_ofInt___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_ofInt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_ofInt___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__0 = (const lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__0_value;
static const lean_string_object l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__1 = (const lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__1_value;
static const lean_string_object l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__2 = (const lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__2_value;
static const lean_string_object l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__3 = (const lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__3_value;
static const lean_ctor_object l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4_value_aux_0),((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4_value_aux_1),((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4_value_aux_2),((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4 = (const lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4_value;
static const lean_array_object l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5 = (const lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5_value;
static const lean_string_object l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__6 = (const lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__6_value;
static const lean_ctor_object l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7_value_aux_0),((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7_value_aux_1),((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7_value_aux_2),((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7 = (const lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7_value;
static const lean_string_object l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__8 = (const lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__8_value;
static const lean_ctor_object l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__9 = (const lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__9_value;
static const lean_string_object l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__10 = (const lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__10_value;
static const lean_ctor_object l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11_value_aux_0),((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11_value_aux_1),((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11_value_aux_2),((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(53, 158, 1, 232, 101, 200, 191, 197)}};
static const lean_object* l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11 = (const lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11_value;
static lean_once_cell_t l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__12;
static lean_once_cell_t l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__13;
static const lean_string_object l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__14 = (const lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__14_value;
static const lean_ctor_object l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15_value_aux_0),((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15_value_aux_1),((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15_value_aux_2),((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15 = (const lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15_value;
static const lean_ctor_object l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__9_value),((lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5_value)}};
static const lean_object* l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__16 = (const lean_object*)&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__16_value;
static lean_once_cell_t l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__17;
static lean_once_cell_t l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__18;
static lean_once_cell_t l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__19;
static lean_once_cell_t l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__20;
static lean_once_cell_t l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__21;
static lean_once_cell_t l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__22;
static lean_once_cell_t l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__23;
static lean_once_cell_t l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__24;
static lean_once_cell_t l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__25;
static lean_once_cell_t l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__26;
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_ofNat___auto__1;
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_ofNat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_ofNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toNat___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Month_Ordinal_ofFin___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_ofFin___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_ofFin(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Month_Ordinal_toSeconds_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00Std_Time_Month_Ordinal_toSeconds_spec__2(lean_object*);
static lean_once_cell_t l_Std_Time_Month_Ordinal_toSeconds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_toSeconds___closed__0;
static lean_once_cell_t l_Std_Time_Month_Ordinal_toSeconds___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_toSeconds___closed__1;
static lean_once_cell_t l_Std_Time_Month_Ordinal_toSeconds___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_toSeconds___closed__2;
static lean_once_cell_t l_Std_Time_Month_Ordinal_toSeconds___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_toSeconds___closed__3;
static lean_once_cell_t l_Std_Time_Month_Ordinal_toSeconds___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_toSeconds___closed__4;
static lean_once_cell_t l_Std_Time_Month_Ordinal_toSeconds___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_toSeconds___closed__5;
static lean_once_cell_t l_Std_Time_Month_Ordinal_toSeconds___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_toSeconds___closed__6;
static lean_once_cell_t l_Std_Time_Month_Ordinal_toSeconds___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_toSeconds___closed__7;
static lean_once_cell_t l_Std_Time_Month_Ordinal_toSeconds___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_toSeconds___closed__8;
static lean_once_cell_t l_Std_Time_Month_Ordinal_toSeconds___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_toSeconds___closed__9;
static lean_once_cell_t l_Std_Time_Month_Ordinal_toSeconds___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_toSeconds___closed__10;
static lean_once_cell_t l_Std_Time_Month_Ordinal_toSeconds___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_toSeconds___closed__11;
static lean_once_cell_t l_Std_Time_Month_Ordinal_toSeconds___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_toSeconds___closed__12;
static lean_once_cell_t l_Std_Time_Month_Ordinal_toSeconds___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_toSeconds___closed__13;
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toSeconds(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toSeconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Month_Ordinal_toSeconds_spec__0(lean_object*);
static lean_once_cell_t l_Std_Time_Month_Ordinal_toMinutes___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_toMinutes___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toMinutes(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toMinutes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toHours(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toHours___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Month_Ordinal_toDays___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_toDays___closed__0;
static lean_once_cell_t l_Std_Time_Month_Ordinal_toDays___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_toDays___closed__1;
static lean_once_cell_t l_Std_Time_Month_Ordinal_toDays___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_toDays___closed__2;
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toDays(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toDays___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__1;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__3;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__5;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__6;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__7;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__8;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__9;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__10;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__11;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__12;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__13;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__14;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__15;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__16;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__17;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__18;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__19;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__20;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__21;
LEAN_EXPORT lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__0;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__1;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__2;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__3;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__4;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__5;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__6;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__7;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__8;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__9;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__10;
static lean_once_cell_t l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__11;
LEAN_EXPORT lean_object* l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes;
static lean_once_cell_t l_Std_Time_Month_Ordinal_days___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_days___closed__0;
static lean_once_cell_t l_Std_Time_Month_Ordinal_days___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_days___closed__1;
static lean_once_cell_t l_Std_Time_Month_Ordinal_days___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_days___closed__2;
static lean_once_cell_t l_Std_Time_Month_Ordinal_days___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_days___closed__3;
static lean_once_cell_t l_Std_Time_Month_Ordinal_days___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_days___closed__4;
static lean_once_cell_t l_Std_Time_Month_Ordinal_days___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_days___closed__5;
static lean_once_cell_t l_Std_Time_Month_Ordinal_days___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_days___closed__6;
static lean_once_cell_t l_Std_Time_Month_Ordinal_days___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_days___closed__7;
static lean_once_cell_t l_Std_Time_Month_Ordinal_days___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_days___closed__8;
static lean_once_cell_t l_Std_Time_Month_Ordinal_days___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_days___closed__9;
static lean_once_cell_t l_Std_Time_Month_Ordinal_days___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_days___closed__10;
static lean_once_cell_t l_Std_Time_Month_Ordinal_days___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_days___closed__11;
static lean_once_cell_t l_Std_Time_Month_Ordinal_days___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_days___closed__12;
static lean_once_cell_t l_Std_Time_Month_Ordinal_days___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_days___closed__13;
static lean_once_cell_t l_Std_Time_Month_Ordinal_days___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_days___closed__14;
static lean_once_cell_t l_Std_Time_Month_Ordinal_days___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_days___closed__15;
static lean_once_cell_t l_Std_Time_Month_Ordinal_days___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_days___closed__16;
static lean_once_cell_t l_Std_Time_Month_Ordinal_days___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_days___closed__17;
static lean_once_cell_t l_Std_Time_Month_Ordinal_days___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_days___closed__18;
static lean_once_cell_t l_Std_Time_Month_Ordinal_days___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_days___closed__19;
static lean_once_cell_t l_Std_Time_Month_Ordinal_days___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_days___closed__20;
static lean_once_cell_t l_Std_Time_Month_Ordinal_days___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_days___closed__21;
static lean_once_cell_t l_Std_Time_Month_Ordinal_days___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_days___closed__22;
static lean_once_cell_t l_Std_Time_Month_Ordinal_days___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_days___closed__23;
static lean_once_cell_t l_Std_Time_Month_Ordinal_days___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_days___closed__24;
static lean_once_cell_t l_Std_Time_Month_Ordinal_days___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_days___closed__25;
static lean_once_cell_t l_Std_Time_Month_Ordinal_days___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_days___closed__26;
static lean_once_cell_t l_Std_Time_Month_Ordinal_days___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_days___closed__27;
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_days(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_days___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_cumulativeDays(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_cumulativeDays___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_clipDay(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_clipDay___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instReprOrdinal___aux__1(lean_object* v_n_3_, lean_object* v_a_4_){
_start:
{
lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_5_ = lean_obj_once(&l_Std_Time_Month_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0);
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
LEAN_EXPORT lean_object* l_Std_Time_Month_instReprOrdinal___aux__1___boxed(lean_object* v_n_12_, lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_Time_Month_instReprOrdinal___aux__1(v_n_12_, v_a_13_);
lean_dec(v_a_13_);
lean_dec(v_n_12_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instReprOrdinal___lam__0(lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
lean_object* v___x_17_; uint8_t v___x_18_; 
v___x_17_ = lean_obj_once(&l_Std_Time_Month_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0);
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
LEAN_EXPORT lean_object* l_Std_Time_Month_instReprOrdinal___lam__0___boxed(lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Std_Time_Month_instReprOrdinal___lam__0(v___y_24_, v___y_25_);
lean_dec(v___y_25_);
lean_dec(v___y_24_);
return v_res_26_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableEqOrdinal___aux__1(lean_object* v_a_29_, lean_object* v_b_30_){
_start:
{
uint8_t v___x_31_; 
v___x_31_ = lean_int_dec_eq(v_a_29_, v_b_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableEqOrdinal___aux__1___boxed(lean_object* v_a_32_, lean_object* v_b_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l_Std_Time_Month_instDecidableEqOrdinal___aux__1(v_a_32_, v_b_33_);
lean_dec(v_b_33_);
lean_dec(v_a_32_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableEqOrdinal(lean_object* v_a_36_, lean_object* v_b_37_){
_start:
{
uint8_t v___x_38_; 
v___x_38_ = lean_int_dec_eq(v_a_36_, v_b_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableEqOrdinal___boxed(lean_object* v_a_39_, lean_object* v_b_40_){
_start:
{
uint8_t v_res_41_; lean_object* v_r_42_; 
v_res_41_ = l_Std_Time_Month_instDecidableEqOrdinal(v_a_39_, v_b_40_);
lean_dec(v_b_40_);
lean_dec(v_a_39_);
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
}
}
static lean_object* _init_l_Std_Time_Month_instLEOrdinal(void){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_box(0);
return v___x_43_;
}
}
static lean_object* _init_l_Std_Time_Month_instLTOrdinal(void){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_box(0);
return v___x_44_;
}
}
static lean_object* _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_unsigned_to_nat(1u);
v___x_46_ = lean_nat_to_int(v___x_45_);
return v___x_46_;
}
}
static lean_object* _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_unsigned_to_nat(11u);
v___x_48_ = lean_nat_to_int(v___x_47_);
return v___x_48_;
}
}
static lean_object* _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__2(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1);
v___x_50_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_51_ = lean_int_add(v___x_50_, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__3(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_53_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__2, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__2_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__2);
v___x_54_ = lean_int_sub(v___x_53_, v___x_52_);
return v___x_54_;
}
}
static lean_object* _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v_range_57_; 
v___x_55_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_56_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__3);
v_range_57_ = lean_int_add(v___x_56_, v___x_55_);
return v_range_57_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instOfNatOrdinal___aux__1(lean_object* v_n_58_){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v_range_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_59_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_60_ = lean_nat_to_int(v_n_58_);
v_range_61_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
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
LEAN_EXPORT lean_object* l_Std_Time_Month_instOfNatOrdinal(lean_object* v_n_67_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v_range_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_68_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_69_ = lean_nat_to_int(v_n_67_);
v_range_70_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
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
static lean_object* _init_l_Std_Time_Month_instInhabitedOrdinal___closed__0(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_77_ = lean_int_sub(v___x_76_, v___x_76_);
return v___x_77_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedOrdinal___closed__1(void){
_start:
{
lean_object* v_range_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v_range_78_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_79_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__0, &l_Std_Time_Month_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__0);
v___x_80_ = lean_int_emod(v___x_79_, v_range_78_);
return v___x_80_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedOrdinal___closed__2(void){
_start:
{
lean_object* v_range_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v_range_81_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_82_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__1, &l_Std_Time_Month_instInhabitedOrdinal___closed__1_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__1);
v___x_83_ = lean_int_add(v___x_82_, v_range_81_);
return v___x_83_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3(void){
_start:
{
lean_object* v_range_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v_range_84_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_85_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__2, &l_Std_Time_Month_instInhabitedOrdinal___closed__2_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__2);
v___x_86_ = lean_int_emod(v___x_85_, v_range_84_);
return v___x_86_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedOrdinal___closed__4(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_88_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_89_ = lean_int_add(v___x_88_, v___x_87_);
return v___x_89_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedOrdinal(void){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__4, &l_Std_Time_Month_instInhabitedOrdinal___closed__4_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__4);
return v___x_90_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableLeOrdinal___aux__1(lean_object* v_x_91_, lean_object* v_y_92_){
_start:
{
uint8_t v___x_93_; 
v___x_93_ = lean_int_dec_le(v_x_91_, v_y_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableLeOrdinal___aux__1___boxed(lean_object* v_x_94_, lean_object* v_y_95_){
_start:
{
uint8_t v_res_96_; lean_object* v_r_97_; 
v_res_96_ = l_Std_Time_Month_instDecidableLeOrdinal___aux__1(v_x_94_, v_y_95_);
lean_dec(v_y_95_);
lean_dec(v_x_94_);
v_r_97_ = lean_box(v_res_96_);
return v_r_97_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableLeOrdinal(lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
uint8_t v___x_100_; 
v___x_100_ = lean_int_dec_le(v___y_98_, v___y_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableLeOrdinal___boxed(lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = l_Std_Time_Month_instDecidableLeOrdinal(v___y_101_, v___y_102_);
lean_dec(v___y_102_);
lean_dec(v___y_101_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableLtOrdinal___aux__1(lean_object* v_x_105_, lean_object* v_y_106_){
_start:
{
uint8_t v___x_107_; 
v___x_107_ = lean_int_dec_lt(v_x_105_, v_y_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableLtOrdinal___aux__1___boxed(lean_object* v_x_108_, lean_object* v_y_109_){
_start:
{
uint8_t v_res_110_; lean_object* v_r_111_; 
v_res_110_ = l_Std_Time_Month_instDecidableLtOrdinal___aux__1(v_x_108_, v_y_109_);
lean_dec(v_y_109_);
lean_dec(v_x_108_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableLtOrdinal(lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
uint8_t v___x_114_; 
v___x_114_ = lean_int_dec_lt(v___y_112_, v___y_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableLtOrdinal___boxed(lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
uint8_t v_res_117_; lean_object* v_r_118_; 
v_res_117_ = l_Std_Time_Month_instDecidableLtOrdinal(v___y_115_, v___y_116_);
lean_dec(v___y_116_);
lean_dec(v___y_115_);
v_r_118_ = lean_box(v_res_117_);
return v_r_118_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Month_instOrdOrdinal___aux__1(lean_object* v_x_119_, lean_object* v_y_120_){
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
LEAN_EXPORT lean_object* l_Std_Time_Month_instOrdOrdinal___aux__1___boxed(lean_object* v_x_126_, lean_object* v_y_127_){
_start:
{
uint8_t v_res_128_; lean_object* v_r_129_; 
v_res_128_ = l_Std_Time_Month_instOrdOrdinal___aux__1(v_x_126_, v_y_127_);
lean_dec(v_y_127_);
lean_dec(v_x_126_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instReprOffset___aux__1(lean_object* v_i_132_, lean_object* v_prec_133_){
_start:
{
lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_134_ = lean_obj_once(&l_Std_Time_Month_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0);
v___x_135_ = lean_int_dec_lt(v_i_132_, v___x_134_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = l_Int_repr(v_i_132_);
v___x_137_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
return v___x_137_;
}
else
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_138_ = l_Int_repr(v_i_132_);
v___x_139_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
v___x_140_ = l_Repr_addAppParen(v___x_139_, v_prec_133_);
return v___x_140_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instReprOffset___aux__1___boxed(lean_object* v_i_141_, lean_object* v_prec_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Std_Time_Month_instReprOffset___aux__1(v_i_141_, v_prec_142_);
lean_dec(v_prec_142_);
lean_dec(v_i_141_);
return v_res_143_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableEqOffset___aux__1(lean_object* v_a_145_, lean_object* v_b_146_){
_start:
{
uint8_t v___x_147_; 
v___x_147_ = lean_int_dec_eq(v_a_145_, v_b_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableEqOffset___aux__1___boxed(lean_object* v_a_148_, lean_object* v_b_149_){
_start:
{
uint8_t v_res_150_; lean_object* v_r_151_; 
v_res_150_ = l_Std_Time_Month_instDecidableEqOffset___aux__1(v_a_148_, v_b_149_);
lean_dec(v_b_149_);
lean_dec(v_a_148_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableEqOffset(lean_object* v_a_152_, lean_object* v_b_153_){
_start:
{
uint8_t v___x_154_; 
v___x_154_ = lean_int_dec_eq(v_a_152_, v_b_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableEqOffset___boxed(lean_object* v_a_155_, lean_object* v_b_156_){
_start:
{
uint8_t v_res_157_; lean_object* v_r_158_; 
v_res_157_ = l_Std_Time_Month_instDecidableEqOffset(v_a_155_, v_b_156_);
lean_dec(v_b_156_);
lean_dec(v_a_155_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedOffset___aux__1(void){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = lean_obj_once(&l_Std_Time_Month_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0);
return v___x_159_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedOffset(void){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lean_obj_once(&l_Std_Time_Month_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instAddOffset___aux__1(lean_object* v_m_161_, lean_object* v_n_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = lean_int_add(v_m_161_, v_n_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instAddOffset___aux__1___boxed(lean_object* v_m_164_, lean_object* v_n_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Std_Time_Month_instAddOffset___aux__1(v_m_164_, v_n_165_);
lean_dec(v_n_165_);
lean_dec(v_m_164_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instSubOffset___aux__1(lean_object* v_m_169_, lean_object* v_n_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = lean_int_sub(v_m_169_, v_n_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instSubOffset___aux__1___boxed(lean_object* v_m_172_, lean_object* v_n_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Std_Time_Month_instSubOffset___aux__1(v_m_172_, v_n_173_);
lean_dec(v_n_173_);
lean_dec(v_m_172_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instMulOffset___aux__1(lean_object* v_m_177_, lean_object* v_n_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = lean_int_mul(v_m_177_, v_n_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instMulOffset___aux__1___boxed(lean_object* v_m_180_, lean_object* v_n_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Std_Time_Month_instMulOffset___aux__1(v_m_180_, v_n_181_);
lean_dec(v_n_181_);
lean_dec(v_m_180_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDivOffset___aux__1(lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = lean_int_ediv(v_a_185_, v_a_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDivOffset___aux__1___boxed(lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Std_Time_Month_instDivOffset___aux__1(v_a_188_, v_a_189_);
lean_dec(v_a_189_);
lean_dec(v_a_188_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instNegOffset___aux__1(lean_object* v_n_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = lean_int_neg(v_n_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instNegOffset___aux__1___boxed(lean_object* v_n_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Std_Time_Month_instNegOffset___aux__1(v_n_195_);
lean_dec(v_n_195_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instToStringOffset___aux__1(lean_object* v_a_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Int_repr(v_a_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instToStringOffset___aux__1___boxed(lean_object* v_a_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Std_Time_Month_instToStringOffset___aux__1(v_a_201_);
lean_dec(v_a_201_);
return v_res_202_;
}
}
static lean_object* _init_l_Std_Time_Month_instLTOffset(void){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = lean_box(0);
return v___x_205_;
}
}
static lean_object* _init_l_Std_Time_Month_instLEOffset(void){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = lean_box(0);
return v___x_206_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableLeOffset(lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
uint8_t v___x_209_; 
v___x_209_ = lean_int_dec_le(v___y_207_, v___y_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableLeOffset___boxed(lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
uint8_t v_res_212_; lean_object* v_r_213_; 
v_res_212_ = l_Std_Time_Month_instDecidableLeOffset(v___y_210_, v___y_211_);
lean_dec(v___y_211_);
lean_dec(v___y_210_);
v_r_213_ = lean_box(v_res_212_);
return v_r_213_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableLtOffset(lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
uint8_t v___x_216_; 
v___x_216_ = lean_int_dec_lt(v___y_214_, v___y_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableLtOffset___boxed(lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
uint8_t v_res_219_; lean_object* v_r_220_; 
v_res_219_ = l_Std_Time_Month_instDecidableLtOffset(v___y_217_, v___y_218_);
lean_dec(v___y_218_);
lean_dec(v___y_217_);
v_r_220_ = lean_box(v_res_219_);
return v_r_220_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instOfNatOffset(lean_object* v_n_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = lean_nat_to_int(v_n_221_);
return v___x_222_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Month_instOrdOffset___aux__1(lean_object* v_x_223_, lean_object* v_y_224_){
_start:
{
uint8_t v___x_225_; 
v___x_225_ = lean_int_dec_lt(v_x_223_, v_y_224_);
if (v___x_225_ == 0)
{
uint8_t v___x_226_; 
v___x_226_ = lean_int_dec_eq(v_x_223_, v_y_224_);
if (v___x_226_ == 0)
{
uint8_t v___x_227_; 
v___x_227_ = 2;
return v___x_227_;
}
else
{
uint8_t v___x_228_; 
v___x_228_ = 1;
return v___x_228_;
}
}
else
{
uint8_t v___x_229_; 
v___x_229_ = 0;
return v___x_229_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instOrdOffset___aux__1___boxed(lean_object* v_x_230_, lean_object* v_y_231_){
_start:
{
uint8_t v_res_232_; lean_object* v_r_233_; 
v_res_232_ = l_Std_Time_Month_instOrdOffset___aux__1(v_x_230_, v_y_231_);
lean_dec(v_y_231_);
lean_dec(v_x_230_);
v_r_233_ = lean_box(v_res_232_);
return v_r_233_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instReprQuarter___aux__1(lean_object* v_n_236_, lean_object* v_a_237_){
_start:
{
lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_238_ = lean_obj_once(&l_Std_Time_Month_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0);
v___x_239_ = lean_int_dec_lt(v_n_236_, v___x_238_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = l_Int_repr(v_n_236_);
v___x_241_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_242_ = l_Int_repr(v_n_236_);
v___x_243_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
v___x_244_ = l_Repr_addAppParen(v___x_243_, v_a_237_);
return v___x_244_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instReprQuarter___aux__1___boxed(lean_object* v_n_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Std_Time_Month_instReprQuarter___aux__1(v_n_245_, v_a_246_);
lean_dec(v_a_246_);
lean_dec(v_n_245_);
return v_res_247_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableEqQuarter___aux__1(lean_object* v_a_249_, lean_object* v_b_250_){
_start:
{
uint8_t v___x_251_; 
v___x_251_ = lean_int_dec_eq(v_a_249_, v_b_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableEqQuarter___aux__1___boxed(lean_object* v_a_252_, lean_object* v_b_253_){
_start:
{
uint8_t v_res_254_; lean_object* v_r_255_; 
v_res_254_ = l_Std_Time_Month_instDecidableEqQuarter___aux__1(v_a_252_, v_b_253_);
lean_dec(v_b_253_);
lean_dec(v_a_252_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableEqQuarter(lean_object* v_a_256_, lean_object* v_b_257_){
_start:
{
uint8_t v___x_258_; 
v___x_258_ = lean_int_dec_eq(v_a_256_, v_b_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableEqQuarter___boxed(lean_object* v_a_259_, lean_object* v_b_260_){
_start:
{
uint8_t v_res_261_; lean_object* v_r_262_; 
v_res_261_ = l_Std_Time_Month_instDecidableEqQuarter(v_a_259_, v_b_260_);
lean_dec(v_b_260_);
lean_dec(v_a_259_);
v_r_262_ = lean_box(v_res_261_);
return v_r_262_;
}
}
static lean_object* _init_l_Std_Time_Month_instLTQuarter(void){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = lean_box(0);
return v___x_263_;
}
}
static lean_object* _init_l_Std_Time_Month_instLEQuarter(void){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = lean_box(0);
return v___x_264_;
}
}
static lean_object* _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_unsigned_to_nat(3u);
v___x_266_ = lean_nat_to_int(v___x_265_);
return v___x_266_;
}
}
static lean_object* _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__1(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_267_ = lean_obj_once(&l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0, &l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0);
v___x_268_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_269_ = lean_int_add(v___x_268_, v___x_267_);
return v___x_269_;
}
}
static lean_object* _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__2(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_270_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_271_ = lean_obj_once(&l_Std_Time_Month_instOfNatQuarter___aux__1___closed__1, &l_Std_Time_Month_instOfNatQuarter___aux__1___closed__1_once, _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__1);
v___x_272_ = lean_int_sub(v___x_271_, v___x_270_);
return v___x_272_;
}
}
static lean_object* _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v_range_275_; 
v___x_273_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_274_ = lean_obj_once(&l_Std_Time_Month_instOfNatQuarter___aux__1___closed__2, &l_Std_Time_Month_instOfNatQuarter___aux__1___closed__2_once, _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__2);
v_range_275_ = lean_int_add(v___x_274_, v___x_273_);
return v_range_275_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instOfNatQuarter___aux__1(lean_object* v_n_276_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v_range_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_277_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_278_ = lean_nat_to_int(v_n_276_);
v_range_279_ = lean_obj_once(&l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3, &l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3_once, _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3);
v___x_280_ = lean_int_sub(v___x_278_, v___x_277_);
lean_dec(v___x_278_);
v___x_281_ = lean_int_emod(v___x_280_, v_range_279_);
lean_dec(v___x_280_);
v___x_282_ = lean_int_add(v___x_281_, v_range_279_);
lean_dec(v___x_281_);
v___x_283_ = lean_int_emod(v___x_282_, v_range_279_);
lean_dec(v___x_282_);
v___x_284_ = lean_int_add(v___x_283_, v___x_277_);
lean_dec(v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instOfNatQuarter(lean_object* v_n_285_){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v_range_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_286_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_287_ = lean_nat_to_int(v_n_285_);
v_range_288_ = lean_obj_once(&l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3, &l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3_once, _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3);
v___x_289_ = lean_int_sub(v___x_287_, v___x_286_);
lean_dec(v___x_287_);
v___x_290_ = lean_int_emod(v___x_289_, v_range_288_);
lean_dec(v___x_289_);
v___x_291_ = lean_int_add(v___x_290_, v_range_288_);
lean_dec(v___x_290_);
v___x_292_ = lean_int_emod(v___x_291_, v_range_288_);
lean_dec(v___x_291_);
v___x_293_ = lean_int_add(v___x_292_, v___x_286_);
lean_dec(v___x_292_);
return v___x_293_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedQuarter___closed__0(void){
_start:
{
lean_object* v_range_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v_range_294_ = lean_obj_once(&l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3, &l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3_once, _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3);
v___x_295_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__0, &l_Std_Time_Month_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__0);
v___x_296_ = lean_int_emod(v___x_295_, v_range_294_);
return v___x_296_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedQuarter___closed__1(void){
_start:
{
lean_object* v_range_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v_range_297_ = lean_obj_once(&l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3, &l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3_once, _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3);
v___x_298_ = lean_obj_once(&l_Std_Time_Month_instInhabitedQuarter___closed__0, &l_Std_Time_Month_instInhabitedQuarter___closed__0_once, _init_l_Std_Time_Month_instInhabitedQuarter___closed__0);
v___x_299_ = lean_int_add(v___x_298_, v_range_297_);
return v___x_299_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedQuarter___closed__2(void){
_start:
{
lean_object* v_range_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v_range_300_ = lean_obj_once(&l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3, &l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3_once, _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3);
v___x_301_ = lean_obj_once(&l_Std_Time_Month_instInhabitedQuarter___closed__1, &l_Std_Time_Month_instInhabitedQuarter___closed__1_once, _init_l_Std_Time_Month_instInhabitedQuarter___closed__1);
v___x_302_ = lean_int_emod(v___x_301_, v_range_300_);
return v___x_302_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedQuarter___closed__3(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_303_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_304_ = lean_obj_once(&l_Std_Time_Month_instInhabitedQuarter___closed__2, &l_Std_Time_Month_instInhabitedQuarter___closed__2_once, _init_l_Std_Time_Month_instInhabitedQuarter___closed__2);
v___x_305_ = lean_int_add(v___x_304_, v___x_303_);
return v___x_305_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedQuarter(void){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = lean_obj_once(&l_Std_Time_Month_instInhabitedQuarter___closed__3, &l_Std_Time_Month_instInhabitedQuarter___closed__3_once, _init_l_Std_Time_Month_instInhabitedQuarter___closed__3);
return v___x_306_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Month_instOrdQuarter___aux__1(lean_object* v_x_307_, lean_object* v_y_308_){
_start:
{
uint8_t v___x_309_; 
v___x_309_ = lean_int_dec_lt(v_x_307_, v_y_308_);
if (v___x_309_ == 0)
{
uint8_t v___x_310_; 
v___x_310_ = lean_int_dec_eq(v_x_307_, v_y_308_);
if (v___x_310_ == 0)
{
uint8_t v___x_311_; 
v___x_311_ = 2;
return v___x_311_;
}
else
{
uint8_t v___x_312_; 
v___x_312_ = 1;
return v___x_312_;
}
}
else
{
uint8_t v___x_313_; 
v___x_313_ = 0;
return v___x_313_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instOrdQuarter___aux__1___boxed(lean_object* v_x_314_, lean_object* v_y_315_){
_start:
{
uint8_t v_res_316_; lean_object* v_r_317_; 
v_res_316_ = l_Std_Time_Month_instOrdQuarter___aux__1(v_x_314_, v_y_315_);
lean_dec(v_y_315_);
lean_dec(v_x_314_);
v_r_317_ = lean_box(v_res_316_);
return v_r_317_;
}
}
static lean_object* _init_l_Std_Time_Month_Quarter_ofMonth___closed__0(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_unsigned_to_nat(3u);
v___x_321_ = lean_nat_to_int(v___x_320_);
return v___x_321_;
}
}
static lean_object* _init_l_Std_Time_Month_Quarter_ofMonth___closed__1(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_323_ = lean_int_neg(v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Quarter_ofMonth(lean_object* v_month_324_){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_325_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_326_ = lean_obj_once(&l_Std_Time_Month_Quarter_ofMonth___closed__0, &l_Std_Time_Month_Quarter_ofMonth___closed__0_once, _init_l_Std_Time_Month_Quarter_ofMonth___closed__0);
v___x_327_ = lean_obj_once(&l_Std_Time_Month_Quarter_ofMonth___closed__1, &l_Std_Time_Month_Quarter_ofMonth___closed__1_once, _init_l_Std_Time_Month_Quarter_ofMonth___closed__1);
v___x_328_ = lean_int_add(v_month_324_, v___x_327_);
v___x_329_ = lean_int_ediv(v___x_328_, v___x_326_);
lean_dec(v___x_328_);
v___x_330_ = lean_int_add(v___x_329_, v___x_325_);
lean_dec(v___x_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Quarter_ofMonth___boxed(lean_object* v_month_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Std_Time_Month_Quarter_ofMonth(v_month_331_);
lean_dec(v_month_331_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Offset_ofNat(lean_object* v_data_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = lean_nat_to_int(v_data_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Offset_ofInt(lean_object* v_data_335_){
_start:
{
lean_inc(v_data_335_);
return v_data_335_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Offset_ofInt___boxed(lean_object* v_data_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Std_Time_Month_Offset_ofInt(v_data_336_);
lean_dec(v_data_336_);
return v_res_337_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_january(void){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__4, &l_Std_Time_Month_instInhabitedOrdinal___closed__4_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__4);
return v___x_338_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_february___closed__0(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_unsigned_to_nat(2u);
v___x_340_ = lean_nat_to_int(v___x_339_);
return v___x_340_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_february___closed__1(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_341_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_342_ = lean_obj_once(&l_Std_Time_Month_Ordinal_february___closed__0, &l_Std_Time_Month_Ordinal_february___closed__0_once, _init_l_Std_Time_Month_Ordinal_february___closed__0);
v___x_343_ = lean_int_sub(v___x_342_, v___x_341_);
return v___x_343_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_february___closed__2(void){
_start:
{
lean_object* v_range_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_range_344_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_345_ = lean_obj_once(&l_Std_Time_Month_Ordinal_february___closed__1, &l_Std_Time_Month_Ordinal_february___closed__1_once, _init_l_Std_Time_Month_Ordinal_february___closed__1);
v___x_346_ = lean_int_emod(v___x_345_, v_range_344_);
return v___x_346_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_february___closed__3(void){
_start:
{
lean_object* v_range_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_range_347_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_348_ = lean_obj_once(&l_Std_Time_Month_Ordinal_february___closed__2, &l_Std_Time_Month_Ordinal_february___closed__2_once, _init_l_Std_Time_Month_Ordinal_february___closed__2);
v___x_349_ = lean_int_add(v___x_348_, v_range_347_);
return v___x_349_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_february___closed__4(void){
_start:
{
lean_object* v_range_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_range_350_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_351_ = lean_obj_once(&l_Std_Time_Month_Ordinal_february___closed__3, &l_Std_Time_Month_Ordinal_february___closed__3_once, _init_l_Std_Time_Month_Ordinal_february___closed__3);
v___x_352_ = lean_int_emod(v___x_351_, v_range_350_);
return v___x_352_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_february___closed__5(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_353_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_354_ = lean_obj_once(&l_Std_Time_Month_Ordinal_february___closed__4, &l_Std_Time_Month_Ordinal_february___closed__4_once, _init_l_Std_Time_Month_Ordinal_february___closed__4);
v___x_355_ = lean_int_add(v___x_354_, v___x_353_);
return v___x_355_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_february(void){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = lean_obj_once(&l_Std_Time_Month_Ordinal_february___closed__5, &l_Std_Time_Month_Ordinal_february___closed__5_once, _init_l_Std_Time_Month_Ordinal_february___closed__5);
return v___x_356_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_march___closed__0(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_357_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_358_ = lean_obj_once(&l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0, &l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0);
v___x_359_ = lean_int_sub(v___x_358_, v___x_357_);
return v___x_359_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_march___closed__1(void){
_start:
{
lean_object* v_range_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v_range_360_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_361_ = lean_obj_once(&l_Std_Time_Month_Ordinal_march___closed__0, &l_Std_Time_Month_Ordinal_march___closed__0_once, _init_l_Std_Time_Month_Ordinal_march___closed__0);
v___x_362_ = lean_int_emod(v___x_361_, v_range_360_);
return v___x_362_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_march___closed__2(void){
_start:
{
lean_object* v_range_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v_range_363_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_364_ = lean_obj_once(&l_Std_Time_Month_Ordinal_march___closed__1, &l_Std_Time_Month_Ordinal_march___closed__1_once, _init_l_Std_Time_Month_Ordinal_march___closed__1);
v___x_365_ = lean_int_add(v___x_364_, v_range_363_);
return v___x_365_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_march___closed__3(void){
_start:
{
lean_object* v_range_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_range_366_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_367_ = lean_obj_once(&l_Std_Time_Month_Ordinal_march___closed__2, &l_Std_Time_Month_Ordinal_march___closed__2_once, _init_l_Std_Time_Month_Ordinal_march___closed__2);
v___x_368_ = lean_int_emod(v___x_367_, v_range_366_);
return v___x_368_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_march___closed__4(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_369_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_370_ = lean_obj_once(&l_Std_Time_Month_Ordinal_march___closed__3, &l_Std_Time_Month_Ordinal_march___closed__3_once, _init_l_Std_Time_Month_Ordinal_march___closed__3);
v___x_371_ = lean_int_add(v___x_370_, v___x_369_);
return v___x_371_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_march(void){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = lean_obj_once(&l_Std_Time_Month_Ordinal_march___closed__4, &l_Std_Time_Month_Ordinal_march___closed__4_once, _init_l_Std_Time_Month_Ordinal_march___closed__4);
return v___x_372_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_april___closed__0(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_unsigned_to_nat(4u);
v___x_374_ = lean_nat_to_int(v___x_373_);
return v___x_374_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_april___closed__1(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_375_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_376_ = lean_obj_once(&l_Std_Time_Month_Ordinal_april___closed__0, &l_Std_Time_Month_Ordinal_april___closed__0_once, _init_l_Std_Time_Month_Ordinal_april___closed__0);
v___x_377_ = lean_int_sub(v___x_376_, v___x_375_);
return v___x_377_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_april___closed__2(void){
_start:
{
lean_object* v_range_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_range_378_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_379_ = lean_obj_once(&l_Std_Time_Month_Ordinal_april___closed__1, &l_Std_Time_Month_Ordinal_april___closed__1_once, _init_l_Std_Time_Month_Ordinal_april___closed__1);
v___x_380_ = lean_int_emod(v___x_379_, v_range_378_);
return v___x_380_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_april___closed__3(void){
_start:
{
lean_object* v_range_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v_range_381_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_382_ = lean_obj_once(&l_Std_Time_Month_Ordinal_april___closed__2, &l_Std_Time_Month_Ordinal_april___closed__2_once, _init_l_Std_Time_Month_Ordinal_april___closed__2);
v___x_383_ = lean_int_add(v___x_382_, v_range_381_);
return v___x_383_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_april___closed__4(void){
_start:
{
lean_object* v_range_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v_range_384_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_385_ = lean_obj_once(&l_Std_Time_Month_Ordinal_april___closed__3, &l_Std_Time_Month_Ordinal_april___closed__3_once, _init_l_Std_Time_Month_Ordinal_april___closed__3);
v___x_386_ = lean_int_emod(v___x_385_, v_range_384_);
return v___x_386_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_april___closed__5(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_387_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_388_ = lean_obj_once(&l_Std_Time_Month_Ordinal_april___closed__4, &l_Std_Time_Month_Ordinal_april___closed__4_once, _init_l_Std_Time_Month_Ordinal_april___closed__4);
v___x_389_ = lean_int_add(v___x_388_, v___x_387_);
return v___x_389_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_april(void){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = lean_obj_once(&l_Std_Time_Month_Ordinal_april___closed__5, &l_Std_Time_Month_Ordinal_april___closed__5_once, _init_l_Std_Time_Month_Ordinal_april___closed__5);
return v___x_390_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_may___closed__0(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_unsigned_to_nat(5u);
v___x_392_ = lean_nat_to_int(v___x_391_);
return v___x_392_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_may___closed__1(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_393_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_394_ = lean_obj_once(&l_Std_Time_Month_Ordinal_may___closed__0, &l_Std_Time_Month_Ordinal_may___closed__0_once, _init_l_Std_Time_Month_Ordinal_may___closed__0);
v___x_395_ = lean_int_sub(v___x_394_, v___x_393_);
return v___x_395_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_may___closed__2(void){
_start:
{
lean_object* v_range_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_range_396_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_397_ = lean_obj_once(&l_Std_Time_Month_Ordinal_may___closed__1, &l_Std_Time_Month_Ordinal_may___closed__1_once, _init_l_Std_Time_Month_Ordinal_may___closed__1);
v___x_398_ = lean_int_emod(v___x_397_, v_range_396_);
return v___x_398_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_may___closed__3(void){
_start:
{
lean_object* v_range_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v_range_399_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_400_ = lean_obj_once(&l_Std_Time_Month_Ordinal_may___closed__2, &l_Std_Time_Month_Ordinal_may___closed__2_once, _init_l_Std_Time_Month_Ordinal_may___closed__2);
v___x_401_ = lean_int_add(v___x_400_, v_range_399_);
return v___x_401_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_may___closed__4(void){
_start:
{
lean_object* v_range_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v_range_402_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_403_ = lean_obj_once(&l_Std_Time_Month_Ordinal_may___closed__3, &l_Std_Time_Month_Ordinal_may___closed__3_once, _init_l_Std_Time_Month_Ordinal_may___closed__3);
v___x_404_ = lean_int_emod(v___x_403_, v_range_402_);
return v___x_404_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_may___closed__5(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_406_ = lean_obj_once(&l_Std_Time_Month_Ordinal_may___closed__4, &l_Std_Time_Month_Ordinal_may___closed__4_once, _init_l_Std_Time_Month_Ordinal_may___closed__4);
v___x_407_ = lean_int_add(v___x_406_, v___x_405_);
return v___x_407_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_may(void){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = lean_obj_once(&l_Std_Time_Month_Ordinal_may___closed__5, &l_Std_Time_Month_Ordinal_may___closed__5_once, _init_l_Std_Time_Month_Ordinal_may___closed__5);
return v___x_408_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_june___closed__0(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = lean_unsigned_to_nat(6u);
v___x_410_ = lean_nat_to_int(v___x_409_);
return v___x_410_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_june___closed__1(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_411_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_412_ = lean_obj_once(&l_Std_Time_Month_Ordinal_june___closed__0, &l_Std_Time_Month_Ordinal_june___closed__0_once, _init_l_Std_Time_Month_Ordinal_june___closed__0);
v___x_413_ = lean_int_sub(v___x_412_, v___x_411_);
return v___x_413_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_june___closed__2(void){
_start:
{
lean_object* v_range_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v_range_414_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_415_ = lean_obj_once(&l_Std_Time_Month_Ordinal_june___closed__1, &l_Std_Time_Month_Ordinal_june___closed__1_once, _init_l_Std_Time_Month_Ordinal_june___closed__1);
v___x_416_ = lean_int_emod(v___x_415_, v_range_414_);
return v___x_416_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_june___closed__3(void){
_start:
{
lean_object* v_range_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v_range_417_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_418_ = lean_obj_once(&l_Std_Time_Month_Ordinal_june___closed__2, &l_Std_Time_Month_Ordinal_june___closed__2_once, _init_l_Std_Time_Month_Ordinal_june___closed__2);
v___x_419_ = lean_int_add(v___x_418_, v_range_417_);
return v___x_419_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_june___closed__4(void){
_start:
{
lean_object* v_range_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v_range_420_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_421_ = lean_obj_once(&l_Std_Time_Month_Ordinal_june___closed__3, &l_Std_Time_Month_Ordinal_june___closed__3_once, _init_l_Std_Time_Month_Ordinal_june___closed__3);
v___x_422_ = lean_int_emod(v___x_421_, v_range_420_);
return v___x_422_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_june___closed__5(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_423_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_424_ = lean_obj_once(&l_Std_Time_Month_Ordinal_june___closed__4, &l_Std_Time_Month_Ordinal_june___closed__4_once, _init_l_Std_Time_Month_Ordinal_june___closed__4);
v___x_425_ = lean_int_add(v___x_424_, v___x_423_);
return v___x_425_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_june(void){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = lean_obj_once(&l_Std_Time_Month_Ordinal_june___closed__5, &l_Std_Time_Month_Ordinal_june___closed__5_once, _init_l_Std_Time_Month_Ordinal_june___closed__5);
return v___x_426_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_july___closed__0(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_unsigned_to_nat(7u);
v___x_428_ = lean_nat_to_int(v___x_427_);
return v___x_428_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_july___closed__1(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_429_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_430_ = lean_obj_once(&l_Std_Time_Month_Ordinal_july___closed__0, &l_Std_Time_Month_Ordinal_july___closed__0_once, _init_l_Std_Time_Month_Ordinal_july___closed__0);
v___x_431_ = lean_int_sub(v___x_430_, v___x_429_);
return v___x_431_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_july___closed__2(void){
_start:
{
lean_object* v_range_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v_range_432_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_433_ = lean_obj_once(&l_Std_Time_Month_Ordinal_july___closed__1, &l_Std_Time_Month_Ordinal_july___closed__1_once, _init_l_Std_Time_Month_Ordinal_july___closed__1);
v___x_434_ = lean_int_emod(v___x_433_, v_range_432_);
return v___x_434_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_july___closed__3(void){
_start:
{
lean_object* v_range_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v_range_435_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_436_ = lean_obj_once(&l_Std_Time_Month_Ordinal_july___closed__2, &l_Std_Time_Month_Ordinal_july___closed__2_once, _init_l_Std_Time_Month_Ordinal_july___closed__2);
v___x_437_ = lean_int_add(v___x_436_, v_range_435_);
return v___x_437_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_july___closed__4(void){
_start:
{
lean_object* v_range_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v_range_438_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_439_ = lean_obj_once(&l_Std_Time_Month_Ordinal_july___closed__3, &l_Std_Time_Month_Ordinal_july___closed__3_once, _init_l_Std_Time_Month_Ordinal_july___closed__3);
v___x_440_ = lean_int_emod(v___x_439_, v_range_438_);
return v___x_440_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_july___closed__5(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_441_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_442_ = lean_obj_once(&l_Std_Time_Month_Ordinal_july___closed__4, &l_Std_Time_Month_Ordinal_july___closed__4_once, _init_l_Std_Time_Month_Ordinal_july___closed__4);
v___x_443_ = lean_int_add(v___x_442_, v___x_441_);
return v___x_443_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_july(void){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = lean_obj_once(&l_Std_Time_Month_Ordinal_july___closed__5, &l_Std_Time_Month_Ordinal_july___closed__5_once, _init_l_Std_Time_Month_Ordinal_july___closed__5);
return v___x_444_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_august___closed__0(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_unsigned_to_nat(8u);
v___x_446_ = lean_nat_to_int(v___x_445_);
return v___x_446_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_august___closed__1(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_447_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_448_ = lean_obj_once(&l_Std_Time_Month_Ordinal_august___closed__0, &l_Std_Time_Month_Ordinal_august___closed__0_once, _init_l_Std_Time_Month_Ordinal_august___closed__0);
v___x_449_ = lean_int_sub(v___x_448_, v___x_447_);
return v___x_449_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_august___closed__2(void){
_start:
{
lean_object* v_range_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v_range_450_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_451_ = lean_obj_once(&l_Std_Time_Month_Ordinal_august___closed__1, &l_Std_Time_Month_Ordinal_august___closed__1_once, _init_l_Std_Time_Month_Ordinal_august___closed__1);
v___x_452_ = lean_int_emod(v___x_451_, v_range_450_);
return v___x_452_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_august___closed__3(void){
_start:
{
lean_object* v_range_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v_range_453_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_454_ = lean_obj_once(&l_Std_Time_Month_Ordinal_august___closed__2, &l_Std_Time_Month_Ordinal_august___closed__2_once, _init_l_Std_Time_Month_Ordinal_august___closed__2);
v___x_455_ = lean_int_add(v___x_454_, v_range_453_);
return v___x_455_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_august___closed__4(void){
_start:
{
lean_object* v_range_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v_range_456_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_457_ = lean_obj_once(&l_Std_Time_Month_Ordinal_august___closed__3, &l_Std_Time_Month_Ordinal_august___closed__3_once, _init_l_Std_Time_Month_Ordinal_august___closed__3);
v___x_458_ = lean_int_emod(v___x_457_, v_range_456_);
return v___x_458_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_august___closed__5(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_459_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_460_ = lean_obj_once(&l_Std_Time_Month_Ordinal_august___closed__4, &l_Std_Time_Month_Ordinal_august___closed__4_once, _init_l_Std_Time_Month_Ordinal_august___closed__4);
v___x_461_ = lean_int_add(v___x_460_, v___x_459_);
return v___x_461_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_august(void){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = lean_obj_once(&l_Std_Time_Month_Ordinal_august___closed__5, &l_Std_Time_Month_Ordinal_august___closed__5_once, _init_l_Std_Time_Month_Ordinal_august___closed__5);
return v___x_462_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_september___closed__0(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_unsigned_to_nat(9u);
v___x_464_ = lean_nat_to_int(v___x_463_);
return v___x_464_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_september___closed__1(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_466_ = lean_obj_once(&l_Std_Time_Month_Ordinal_september___closed__0, &l_Std_Time_Month_Ordinal_september___closed__0_once, _init_l_Std_Time_Month_Ordinal_september___closed__0);
v___x_467_ = lean_int_sub(v___x_466_, v___x_465_);
return v___x_467_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_september___closed__2(void){
_start:
{
lean_object* v_range_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v_range_468_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_469_ = lean_obj_once(&l_Std_Time_Month_Ordinal_september___closed__1, &l_Std_Time_Month_Ordinal_september___closed__1_once, _init_l_Std_Time_Month_Ordinal_september___closed__1);
v___x_470_ = lean_int_emod(v___x_469_, v_range_468_);
return v___x_470_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_september___closed__3(void){
_start:
{
lean_object* v_range_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v_range_471_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_472_ = lean_obj_once(&l_Std_Time_Month_Ordinal_september___closed__2, &l_Std_Time_Month_Ordinal_september___closed__2_once, _init_l_Std_Time_Month_Ordinal_september___closed__2);
v___x_473_ = lean_int_add(v___x_472_, v_range_471_);
return v___x_473_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_september___closed__4(void){
_start:
{
lean_object* v_range_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v_range_474_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_475_ = lean_obj_once(&l_Std_Time_Month_Ordinal_september___closed__3, &l_Std_Time_Month_Ordinal_september___closed__3_once, _init_l_Std_Time_Month_Ordinal_september___closed__3);
v___x_476_ = lean_int_emod(v___x_475_, v_range_474_);
return v___x_476_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_september___closed__5(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_477_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_478_ = lean_obj_once(&l_Std_Time_Month_Ordinal_september___closed__4, &l_Std_Time_Month_Ordinal_september___closed__4_once, _init_l_Std_Time_Month_Ordinal_september___closed__4);
v___x_479_ = lean_int_add(v___x_478_, v___x_477_);
return v___x_479_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_september(void){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = lean_obj_once(&l_Std_Time_Month_Ordinal_september___closed__5, &l_Std_Time_Month_Ordinal_september___closed__5_once, _init_l_Std_Time_Month_Ordinal_september___closed__5);
return v___x_480_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_october___closed__0(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_unsigned_to_nat(10u);
v___x_482_ = lean_nat_to_int(v___x_481_);
return v___x_482_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_october___closed__1(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_483_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_484_ = lean_obj_once(&l_Std_Time_Month_Ordinal_october___closed__0, &l_Std_Time_Month_Ordinal_october___closed__0_once, _init_l_Std_Time_Month_Ordinal_october___closed__0);
v___x_485_ = lean_int_sub(v___x_484_, v___x_483_);
return v___x_485_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_october___closed__2(void){
_start:
{
lean_object* v_range_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v_range_486_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_487_ = lean_obj_once(&l_Std_Time_Month_Ordinal_october___closed__1, &l_Std_Time_Month_Ordinal_october___closed__1_once, _init_l_Std_Time_Month_Ordinal_october___closed__1);
v___x_488_ = lean_int_emod(v___x_487_, v_range_486_);
return v___x_488_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_october___closed__3(void){
_start:
{
lean_object* v_range_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v_range_489_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_490_ = lean_obj_once(&l_Std_Time_Month_Ordinal_october___closed__2, &l_Std_Time_Month_Ordinal_october___closed__2_once, _init_l_Std_Time_Month_Ordinal_october___closed__2);
v___x_491_ = lean_int_add(v___x_490_, v_range_489_);
return v___x_491_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_october___closed__4(void){
_start:
{
lean_object* v_range_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v_range_492_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_493_ = lean_obj_once(&l_Std_Time_Month_Ordinal_october___closed__3, &l_Std_Time_Month_Ordinal_october___closed__3_once, _init_l_Std_Time_Month_Ordinal_october___closed__3);
v___x_494_ = lean_int_emod(v___x_493_, v_range_492_);
return v___x_494_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_october___closed__5(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_496_ = lean_obj_once(&l_Std_Time_Month_Ordinal_october___closed__4, &l_Std_Time_Month_Ordinal_october___closed__4_once, _init_l_Std_Time_Month_Ordinal_october___closed__4);
v___x_497_ = lean_int_add(v___x_496_, v___x_495_);
return v___x_497_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_october(void){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = lean_obj_once(&l_Std_Time_Month_Ordinal_october___closed__5, &l_Std_Time_Month_Ordinal_october___closed__5_once, _init_l_Std_Time_Month_Ordinal_october___closed__5);
return v___x_498_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_november___closed__0(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_499_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_500_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1);
v___x_501_ = lean_int_sub(v___x_500_, v___x_499_);
return v___x_501_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_november___closed__1(void){
_start:
{
lean_object* v_range_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v_range_502_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_503_ = lean_obj_once(&l_Std_Time_Month_Ordinal_november___closed__0, &l_Std_Time_Month_Ordinal_november___closed__0_once, _init_l_Std_Time_Month_Ordinal_november___closed__0);
v___x_504_ = lean_int_emod(v___x_503_, v_range_502_);
return v___x_504_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_november___closed__2(void){
_start:
{
lean_object* v_range_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v_range_505_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_506_ = lean_obj_once(&l_Std_Time_Month_Ordinal_november___closed__1, &l_Std_Time_Month_Ordinal_november___closed__1_once, _init_l_Std_Time_Month_Ordinal_november___closed__1);
v___x_507_ = lean_int_add(v___x_506_, v_range_505_);
return v___x_507_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_november___closed__3(void){
_start:
{
lean_object* v_range_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v_range_508_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_509_ = lean_obj_once(&l_Std_Time_Month_Ordinal_november___closed__2, &l_Std_Time_Month_Ordinal_november___closed__2_once, _init_l_Std_Time_Month_Ordinal_november___closed__2);
v___x_510_ = lean_int_emod(v___x_509_, v_range_508_);
return v___x_510_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_november___closed__4(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_511_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_512_ = lean_obj_once(&l_Std_Time_Month_Ordinal_november___closed__3, &l_Std_Time_Month_Ordinal_november___closed__3_once, _init_l_Std_Time_Month_Ordinal_november___closed__3);
v___x_513_ = lean_int_add(v___x_512_, v___x_511_);
return v___x_513_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_november(void){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = lean_obj_once(&l_Std_Time_Month_Ordinal_november___closed__4, &l_Std_Time_Month_Ordinal_november___closed__4_once, _init_l_Std_Time_Month_Ordinal_november___closed__4);
return v___x_514_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_december___closed__0(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_unsigned_to_nat(12u);
v___x_516_ = lean_nat_to_int(v___x_515_);
return v___x_516_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_december___closed__1(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_517_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_518_ = lean_obj_once(&l_Std_Time_Month_Ordinal_december___closed__0, &l_Std_Time_Month_Ordinal_december___closed__0_once, _init_l_Std_Time_Month_Ordinal_december___closed__0);
v___x_519_ = lean_int_sub(v___x_518_, v___x_517_);
return v___x_519_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_december___closed__2(void){
_start:
{
lean_object* v_range_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v_range_520_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_521_ = lean_obj_once(&l_Std_Time_Month_Ordinal_december___closed__1, &l_Std_Time_Month_Ordinal_december___closed__1_once, _init_l_Std_Time_Month_Ordinal_december___closed__1);
v___x_522_ = lean_int_emod(v___x_521_, v_range_520_);
return v___x_522_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_december___closed__3(void){
_start:
{
lean_object* v_range_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v_range_523_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_524_ = lean_obj_once(&l_Std_Time_Month_Ordinal_december___closed__2, &l_Std_Time_Month_Ordinal_december___closed__2_once, _init_l_Std_Time_Month_Ordinal_december___closed__2);
v___x_525_ = lean_int_add(v___x_524_, v_range_523_);
return v___x_525_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_december___closed__4(void){
_start:
{
lean_object* v_range_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v_range_526_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_527_ = lean_obj_once(&l_Std_Time_Month_Ordinal_december___closed__3, &l_Std_Time_Month_Ordinal_december___closed__3_once, _init_l_Std_Time_Month_Ordinal_december___closed__3);
v___x_528_ = lean_int_emod(v___x_527_, v_range_526_);
return v___x_528_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_december___closed__5(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_529_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_530_ = lean_obj_once(&l_Std_Time_Month_Ordinal_december___closed__4, &l_Std_Time_Month_Ordinal_december___closed__4_once, _init_l_Std_Time_Month_Ordinal_december___closed__4);
v___x_531_ = lean_int_add(v___x_530_, v___x_529_);
return v___x_531_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_december(void){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = lean_obj_once(&l_Std_Time_Month_Ordinal_december___closed__5, &l_Std_Time_Month_Ordinal_december___closed__5_once, _init_l_Std_Time_Month_Ordinal_december___closed__5);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toOffset(lean_object* v_month_533_){
_start:
{
lean_inc(v_month_533_);
return v_month_533_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toOffset___boxed(lean_object* v_month_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Std_Time_Month_Ordinal_toOffset(v_month_534_);
lean_dec(v_month_534_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_ofInt___redArg(lean_object* v_data_536_){
_start:
{
lean_inc(v_data_536_);
return v_data_536_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_ofInt___redArg___boxed(lean_object* v_data_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Std_Time_Month_Ordinal_ofInt___redArg(v_data_537_);
lean_dec(v_data_537_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_ofInt(lean_object* v_data_539_, lean_object* v_h_540_){
_start:
{
lean_inc(v_data_539_);
return v_data_539_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_ofInt___boxed(lean_object* v_data_541_, lean_object* v_h_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Std_Time_Month_Ordinal_ofInt(v_data_541_, v_h_542_);
lean_dec(v_data_541_);
return v_res_543_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__12(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__10));
v___x_571_ = l_Lean_mkAtom(v___x_570_);
return v___x_571_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__13(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_572_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__12, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__12_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__12);
v___x_573_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5));
v___x_574_ = lean_array_push(v___x_573_, v___x_572_);
return v___x_574_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__17(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_585_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__16));
v___x_586_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5));
v___x_587_ = lean_array_push(v___x_586_, v___x_585_);
return v___x_587_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__18(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_588_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__17, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__17_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__17);
v___x_589_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15));
v___x_590_ = lean_box(2);
v___x_591_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
lean_ctor_set(v___x_591_, 1, v___x_589_);
lean_ctor_set(v___x_591_, 2, v___x_588_);
return v___x_591_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__19(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_592_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__18, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__18_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__18);
v___x_593_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__13, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__13_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__13);
v___x_594_ = lean_array_push(v___x_593_, v___x_592_);
return v___x_594_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__20(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_595_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__19, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__19_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__19);
v___x_596_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11));
v___x_597_ = lean_box(2);
v___x_598_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
lean_ctor_set(v___x_598_, 1, v___x_596_);
lean_ctor_set(v___x_598_, 2, v___x_595_);
return v___x_598_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__21(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_599_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__20, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__20_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__20);
v___x_600_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5));
v___x_601_ = lean_array_push(v___x_600_, v___x_599_);
return v___x_601_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__22(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_602_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__21, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__21_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__21);
v___x_603_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__9));
v___x_604_ = lean_box(2);
v___x_605_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v___x_603_);
lean_ctor_set(v___x_605_, 2, v___x_602_);
return v___x_605_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__23(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_606_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__22, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__22_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__22);
v___x_607_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5));
v___x_608_ = lean_array_push(v___x_607_, v___x_606_);
return v___x_608_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__24(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_609_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__23, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__23_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__23);
v___x_610_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7));
v___x_611_ = lean_box(2);
v___x_612_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v___x_610_);
lean_ctor_set(v___x_612_, 2, v___x_609_);
return v___x_612_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__25(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_613_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__24, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__24_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__24);
v___x_614_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5));
v___x_615_ = lean_array_push(v___x_614_, v___x_613_);
return v___x_615_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__26(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_616_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__25, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__25_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__25);
v___x_617_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4));
v___x_618_ = lean_box(2);
v___x_619_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
lean_ctor_set(v___x_619_, 1, v___x_617_);
lean_ctor_set(v___x_619_, 2, v___x_616_);
return v___x_619_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1(void){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__26, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__26_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__26);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_ofNat___redArg(lean_object* v_data_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = lean_nat_to_int(v_data_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_ofNat(lean_object* v_data_623_, lean_object* v_h_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = lean_nat_to_int(v_data_623_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toNat(lean_object* v_month_626_){
_start:
{
lean_object* v_intZero_627_; uint8_t v_isNeg_628_; lean_object* v_a_629_; 
v_intZero_627_ = lean_obj_once(&l_Std_Time_Month_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0);
v_isNeg_628_ = lean_int_dec_lt(v_month_626_, v_intZero_627_);
v_a_629_ = lean_nat_abs(v_month_626_);
return v_a_629_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toNat___boxed(lean_object* v_month_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Std_Time_Month_Ordinal_toNat(v_month_630_);
lean_dec(v_month_630_);
return v_res_631_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofFin___closed__0(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_unsigned_to_nat(1u);
v___x_633_ = lean_nat_to_int(v___x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_ofFin(lean_object* v_data_634_){
_start:
{
lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_635_ = lean_unsigned_to_nat(1u);
v___x_636_ = lean_nat_dec_le(v___x_635_, v_data_634_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; 
lean_dec(v_data_634_);
v___x_637_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofFin___closed__0, &l_Std_Time_Month_Ordinal_ofFin___closed__0_once, _init_l_Std_Time_Month_Ordinal_ofFin___closed__0);
return v___x_637_;
}
else
{
lean_object* v___x_638_; 
v___x_638_ = lean_nat_to_int(v_data_634_);
return v___x_638_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Month_Ordinal_toSeconds_spec__1(lean_object* v_a_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = lean_nat_to_int(v_a_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Std_Time_Month_Ordinal_toSeconds_spec__2(lean_object* v_a_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Rat_ofInt(v_a_641_);
return v___x_642_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__0(void){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Std_Time_Internal_instInhabitedUnitVal_default___redArg();
return v___x_643_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__1(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = lean_unsigned_to_nat(31u);
v___x_645_ = lean_nat_to_int(v___x_644_);
return v___x_645_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__2(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_unsigned_to_nat(59u);
v___x_647_ = lean_nat_to_int(v___x_646_);
return v___x_647_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__3(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_unsigned_to_nat(90u);
v___x_649_ = lean_nat_to_int(v___x_648_);
return v___x_649_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__4(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_unsigned_to_nat(120u);
v___x_651_ = lean_nat_to_int(v___x_650_);
return v___x_651_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__5(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = lean_unsigned_to_nat(151u);
v___x_653_ = lean_nat_to_int(v___x_652_);
return v___x_653_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__6(void){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_unsigned_to_nat(181u);
v___x_655_ = lean_nat_to_int(v___x_654_);
return v___x_655_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__7(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = lean_unsigned_to_nat(212u);
v___x_657_ = lean_nat_to_int(v___x_656_);
return v___x_657_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__8(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_unsigned_to_nat(243u);
v___x_659_ = lean_nat_to_int(v___x_658_);
return v___x_659_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__9(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = lean_unsigned_to_nat(273u);
v___x_661_ = lean_nat_to_int(v___x_660_);
return v___x_661_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__10(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = lean_unsigned_to_nat(304u);
v___x_663_ = lean_nat_to_int(v___x_662_);
return v___x_663_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__11(void){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = lean_unsigned_to_nat(334u);
v___x_665_ = lean_nat_to_int(v___x_664_);
return v___x_665_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__12(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v_intZero_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v_daysAcc_691_; 
v___x_666_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__11, &l_Std_Time_Month_Ordinal_toSeconds___closed__11_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__11);
v___x_667_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__10, &l_Std_Time_Month_Ordinal_toSeconds___closed__10_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__10);
v___x_668_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__9, &l_Std_Time_Month_Ordinal_toSeconds___closed__9_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__9);
v___x_669_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__8, &l_Std_Time_Month_Ordinal_toSeconds___closed__8_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__8);
v___x_670_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__7, &l_Std_Time_Month_Ordinal_toSeconds___closed__7_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__7);
v___x_671_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__6, &l_Std_Time_Month_Ordinal_toSeconds___closed__6_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__6);
v___x_672_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__5, &l_Std_Time_Month_Ordinal_toSeconds___closed__5_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__5);
v___x_673_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__4, &l_Std_Time_Month_Ordinal_toSeconds___closed__4_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__4);
v___x_674_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__3, &l_Std_Time_Month_Ordinal_toSeconds___closed__3_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__3);
v___x_675_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__2, &l_Std_Time_Month_Ordinal_toSeconds___closed__2_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__2);
v___x_676_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__1, &l_Std_Time_Month_Ordinal_toSeconds___closed__1_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__1);
v_intZero_677_ = lean_obj_once(&l_Std_Time_Month_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0);
v___x_678_ = lean_unsigned_to_nat(12u);
v___x_679_ = lean_mk_empty_array_with_capacity(v___x_678_);
v___x_680_ = lean_array_push(v___x_679_, v_intZero_677_);
v___x_681_ = lean_array_push(v___x_680_, v___x_676_);
v___x_682_ = lean_array_push(v___x_681_, v___x_675_);
v___x_683_ = lean_array_push(v___x_682_, v___x_674_);
v___x_684_ = lean_array_push(v___x_683_, v___x_673_);
v___x_685_ = lean_array_push(v___x_684_, v___x_672_);
v___x_686_ = lean_array_push(v___x_685_, v___x_671_);
v___x_687_ = lean_array_push(v___x_686_, v___x_670_);
v___x_688_ = lean_array_push(v___x_687_, v___x_669_);
v___x_689_ = lean_array_push(v___x_688_, v___x_668_);
v___x_690_ = lean_array_push(v___x_689_, v___x_667_);
v_daysAcc_691_ = lean_array_push(v___x_690_, v___x_666_);
return v_daysAcc_691_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__13(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_unsigned_to_nat(86400u);
v___x_693_ = lean_nat_to_int(v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toSeconds(uint8_t v_leap_694_, lean_object* v_month_695_){
_start:
{
lean_object* v_intZero_696_; uint8_t v_isNeg_697_; lean_object* v___x_698_; lean_object* v_a_699_; lean_object* v_daysAcc_700_; lean_object* v_days_701_; lean_object* v___x_702_; lean_object* v_time_703_; 
v_intZero_696_ = lean_obj_once(&l_Std_Time_Month_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0);
v_isNeg_697_ = lean_int_dec_lt(v_month_695_, v_intZero_696_);
v___x_698_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__0, &l_Std_Time_Month_Ordinal_toSeconds___closed__0_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__0);
v_a_699_ = lean_nat_abs(v_month_695_);
v_daysAcc_700_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__12, &l_Std_Time_Month_Ordinal_toSeconds___closed__12_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__12);
v_days_701_ = lean_array_get_borrowed(v___x_698_, v_daysAcc_700_, v_a_699_);
v___x_702_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__13, &l_Std_Time_Month_Ordinal_toSeconds___closed__13_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__13);
v_time_703_ = lean_int_mul(v_days_701_, v___x_702_);
if (v_leap_694_ == 0)
{
lean_dec(v_a_699_);
return v_time_703_;
}
else
{
lean_object* v___x_704_; uint8_t v___x_705_; 
v___x_704_ = lean_unsigned_to_nat(2u);
v___x_705_ = lean_nat_dec_le(v___x_704_, v_a_699_);
lean_dec(v_a_699_);
if (v___x_705_ == 0)
{
return v_time_703_;
}
else
{
lean_object* v___x_706_; 
v___x_706_ = lean_int_add(v_time_703_, v___x_702_);
lean_dec(v_time_703_);
return v___x_706_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toSeconds___boxed(lean_object* v_leap_707_, lean_object* v_month_708_){
_start:
{
uint8_t v_leap_boxed_709_; lean_object* v_res_710_; 
v_leap_boxed_709_ = lean_unbox(v_leap_707_);
v_res_710_ = l_Std_Time_Month_Ordinal_toSeconds(v_leap_boxed_709_, v_month_708_);
lean_dec(v_month_708_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Month_Ordinal_toSeconds_spec__0(lean_object* v_a_711_){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = lean_nat_to_int(v_a_711_);
v___x_713_ = l_Rat_ofInt(v___x_712_);
return v___x_713_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toMinutes___closed__0(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_unsigned_to_nat(60u);
v___x_715_ = lean_nat_to_int(v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toMinutes(uint8_t v_leap_716_, lean_object* v_month_717_){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_718_ = l_Std_Time_Month_Ordinal_toSeconds(v_leap_716_, v_month_717_);
v___x_719_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toMinutes___closed__0, &l_Std_Time_Month_Ordinal_toMinutes___closed__0_once, _init_l_Std_Time_Month_Ordinal_toMinutes___closed__0);
v___x_720_ = lean_int_div(v___x_718_, v___x_719_);
lean_dec(v___x_718_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toMinutes___boxed(lean_object* v_leap_721_, lean_object* v_month_722_){
_start:
{
uint8_t v_leap_boxed_723_; lean_object* v_res_724_; 
v_leap_boxed_723_ = lean_unbox(v_leap_721_);
v_res_724_ = l_Std_Time_Month_Ordinal_toMinutes(v_leap_boxed_723_, v_month_722_);
lean_dec(v_month_722_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toHours(uint8_t v_leap_725_, lean_object* v_month_726_){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_727_ = l_Std_Time_Month_Ordinal_toSeconds(v_leap_725_, v_month_726_);
v___x_728_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toMinutes___closed__0, &l_Std_Time_Month_Ordinal_toMinutes___closed__0_once, _init_l_Std_Time_Month_Ordinal_toMinutes___closed__0);
v___x_729_ = lean_int_div(v___x_727_, v___x_728_);
lean_dec(v___x_727_);
v___x_730_ = lean_int_div(v___x_729_, v___x_728_);
lean_dec(v___x_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toHours___boxed(lean_object* v_leap_731_, lean_object* v_month_732_){
_start:
{
uint8_t v_leap_boxed_733_; lean_object* v_res_734_; 
v_leap_boxed_733_ = lean_unbox(v_leap_731_);
v_res_734_ = l_Std_Time_Month_Ordinal_toHours(v_leap_boxed_733_, v_month_732_);
lean_dec(v_month_732_);
return v_res_734_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toDays___closed__0(void){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_unsigned_to_nat(1u);
v___x_736_ = l_Rat_instNatCast___lam__0(v___x_735_);
return v___x_736_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toDays___closed__1(void){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = lean_unsigned_to_nat(86400u);
v___x_738_ = l_Rat_instNatCast___lam__0(v___x_737_);
return v___x_738_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toDays___closed__2(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v_ratio_741_; 
v___x_739_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toDays___closed__1, &l_Std_Time_Month_Ordinal_toDays___closed__1_once, _init_l_Std_Time_Month_Ordinal_toDays___closed__1);
v___x_740_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toDays___closed__0, &l_Std_Time_Month_Ordinal_toDays___closed__0_once, _init_l_Std_Time_Month_Ordinal_toDays___closed__0);
v_ratio_741_ = l_Rat_div(v___x_740_, v___x_739_);
return v_ratio_741_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toDays(uint8_t v_leap_742_, lean_object* v_month_743_){
_start:
{
lean_object* v_ratio_744_; lean_object* v_num_745_; lean_object* v_den_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v_ratio_744_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toDays___closed__2, &l_Std_Time_Month_Ordinal_toDays___closed__2_once, _init_l_Std_Time_Month_Ordinal_toDays___closed__2);
v_num_745_ = lean_ctor_get(v_ratio_744_, 0);
v_den_746_ = lean_ctor_get(v_ratio_744_, 1);
v___x_747_ = l_Std_Time_Month_Ordinal_toSeconds(v_leap_742_, v_month_743_);
v___x_748_ = lean_int_mul(v___x_747_, v_num_745_);
lean_dec(v___x_747_);
lean_inc(v_den_746_);
v___x_749_ = lean_nat_to_int(v_den_746_);
v___x_750_ = lean_int_ediv(v___x_748_, v___x_749_);
lean_dec(v___x_749_);
lean_dec(v___x_748_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toDays___boxed(lean_object* v_leap_751_, lean_object* v_month_752_){
_start:
{
uint8_t v_leap_boxed_753_; lean_object* v_res_754_; 
v_leap_boxed_753_ = lean_unbox(v_leap_751_);
v_res_754_ = l_Std_Time_Month_Ordinal_toDays(v_leap_boxed_753_, v_month_752_);
lean_dec(v_month_752_);
return v_res_754_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_unsigned_to_nat(30u);
v___x_756_ = lean_nat_to_int(v___x_755_);
return v___x_756_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__1(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_757_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0);
v___x_758_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_759_ = lean_int_add(v___x_758_, v___x_757_);
return v___x_759_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_unsigned_to_nat(31u);
v___x_761_ = lean_nat_to_int(v___x_760_);
return v___x_761_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__3(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_762_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_763_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__1, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__1_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__1);
v___x_764_ = lean_int_sub(v___x_763_, v___x_762_);
return v___x_764_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v_range_767_; 
v___x_765_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_766_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__3, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__3_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__3);
v_range_767_ = lean_int_add(v___x_766_, v___x_765_);
return v_range_767_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__5(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_769_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2);
v___x_770_ = lean_int_sub(v___x_769_, v___x_768_);
return v___x_770_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__6(void){
_start:
{
lean_object* v_range_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v_range_771_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
v___x_772_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__5, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__5_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__5);
v___x_773_ = lean_int_emod(v___x_772_, v_range_771_);
return v___x_773_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__7(void){
_start:
{
lean_object* v_range_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v_range_774_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
v___x_775_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__6, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__6_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__6);
v___x_776_ = lean_int_add(v___x_775_, v_range_774_);
return v___x_776_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__8(void){
_start:
{
lean_object* v_range_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v_range_777_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
v___x_778_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__7, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__7_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__7);
v___x_779_ = lean_int_emod(v___x_778_, v_range_777_);
return v___x_779_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__9(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_780_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_781_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__8, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__8_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__8);
v___x_782_ = lean_int_add(v___x_781_, v___x_780_);
return v___x_782_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__10(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = lean_unsigned_to_nat(28u);
v___x_784_ = lean_nat_to_int(v___x_783_);
return v___x_784_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__11(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_785_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_786_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__10, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__10_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__10);
v___x_787_ = lean_int_sub(v___x_786_, v___x_785_);
return v___x_787_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__12(void){
_start:
{
lean_object* v_range_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v_range_788_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
v___x_789_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__11, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__11_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__11);
v___x_790_ = lean_int_emod(v___x_789_, v_range_788_);
return v___x_790_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__13(void){
_start:
{
lean_object* v_range_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v_range_791_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
v___x_792_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__12, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__12_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__12);
v___x_793_ = lean_int_add(v___x_792_, v_range_791_);
return v___x_793_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__14(void){
_start:
{
lean_object* v_range_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v_range_794_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
v___x_795_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__13, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__13_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__13);
v___x_796_ = lean_int_emod(v___x_795_, v_range_794_);
return v___x_796_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__15(void){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_797_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_798_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__14, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__14_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__14);
v___x_799_ = lean_int_add(v___x_798_, v___x_797_);
return v___x_799_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__16(void){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_800_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_801_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0);
v___x_802_ = lean_int_sub(v___x_801_, v___x_800_);
return v___x_802_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__17(void){
_start:
{
lean_object* v_range_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v_range_803_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
v___x_804_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__16, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__16_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__16);
v___x_805_ = lean_int_emod(v___x_804_, v_range_803_);
return v___x_805_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__18(void){
_start:
{
lean_object* v_range_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v_range_806_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
v___x_807_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__17, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__17_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__17);
v___x_808_ = lean_int_add(v___x_807_, v_range_806_);
return v___x_808_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__19(void){
_start:
{
lean_object* v_range_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v_range_809_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
v___x_810_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__18, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__18_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__18);
v___x_811_ = lean_int_emod(v___x_810_, v_range_809_);
return v___x_811_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__20(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_812_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_813_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__19, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__19_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__19);
v___x_814_ = lean_int_add(v___x_813_, v___x_812_);
return v___x_814_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__21(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_815_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__20, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__20_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__20);
v___x_816_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__15, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__15_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__15);
v___x_817_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__9, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__9_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__9);
v___x_818_ = lean_unsigned_to_nat(12u);
v___x_819_ = lean_mk_empty_array_with_capacity(v___x_818_);
v___x_820_ = lean_array_push(v___x_819_, v___x_817_);
v___x_821_ = lean_array_push(v___x_820_, v___x_816_);
v___x_822_ = lean_array_push(v___x_821_, v___x_817_);
v___x_823_ = lean_array_push(v___x_822_, v___x_815_);
v___x_824_ = lean_array_push(v___x_823_, v___x_817_);
v___x_825_ = lean_array_push(v___x_824_, v___x_815_);
v___x_826_ = lean_array_push(v___x_825_, v___x_817_);
v___x_827_ = lean_array_push(v___x_826_, v___x_817_);
v___x_828_ = lean_array_push(v___x_827_, v___x_815_);
v___x_829_ = lean_array_push(v___x_828_, v___x_817_);
v___x_830_ = lean_array_push(v___x_829_, v___x_815_);
v___x_831_ = lean_array_push(v___x_830_, v___x_817_);
return v___x_831_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap(void){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__21, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__21_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__21);
return v___x_832_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__0(void){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = lean_unsigned_to_nat(0u);
v___x_834_ = lean_nat_to_int(v___x_833_);
return v___x_834_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__1(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = lean_unsigned_to_nat(59u);
v___x_836_ = lean_nat_to_int(v___x_835_);
return v___x_836_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__2(void){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = lean_unsigned_to_nat(90u);
v___x_838_ = lean_nat_to_int(v___x_837_);
return v___x_838_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__3(void){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = lean_unsigned_to_nat(120u);
v___x_840_ = lean_nat_to_int(v___x_839_);
return v___x_840_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__4(void){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = lean_unsigned_to_nat(151u);
v___x_842_ = lean_nat_to_int(v___x_841_);
return v___x_842_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__5(void){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = lean_unsigned_to_nat(181u);
v___x_844_ = lean_nat_to_int(v___x_843_);
return v___x_844_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__6(void){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = lean_unsigned_to_nat(212u);
v___x_846_ = lean_nat_to_int(v___x_845_);
return v___x_846_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__7(void){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_unsigned_to_nat(243u);
v___x_848_ = lean_nat_to_int(v___x_847_);
return v___x_848_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__8(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = lean_unsigned_to_nat(273u);
v___x_850_ = lean_nat_to_int(v___x_849_);
return v___x_850_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__9(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = lean_unsigned_to_nat(304u);
v___x_852_ = lean_nat_to_int(v___x_851_);
return v___x_852_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__10(void){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_853_ = lean_unsigned_to_nat(334u);
v___x_854_ = lean_nat_to_int(v___x_853_);
return v___x_854_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__11(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_855_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__10, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__10_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__10);
v___x_856_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__9, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__9_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__9);
v___x_857_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__8, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__8_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__8);
v___x_858_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__7, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__7_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__7);
v___x_859_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__6, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__6_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__6);
v___x_860_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__5, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__5_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__5);
v___x_861_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__4);
v___x_862_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__3, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__3_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__3);
v___x_863_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__2, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__2_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__2);
v___x_864_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__1, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__1_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__1);
v___x_865_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2);
v___x_866_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__0, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__0_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__0);
v___x_867_ = lean_unsigned_to_nat(12u);
v___x_868_ = lean_mk_empty_array_with_capacity(v___x_867_);
v___x_869_ = lean_array_push(v___x_868_, v___x_866_);
v___x_870_ = lean_array_push(v___x_869_, v___x_865_);
v___x_871_ = lean_array_push(v___x_870_, v___x_864_);
v___x_872_ = lean_array_push(v___x_871_, v___x_863_);
v___x_873_ = lean_array_push(v___x_872_, v___x_862_);
v___x_874_ = lean_array_push(v___x_873_, v___x_861_);
v___x_875_ = lean_array_push(v___x_874_, v___x_860_);
v___x_876_ = lean_array_push(v___x_875_, v___x_859_);
v___x_877_ = lean_array_push(v___x_876_, v___x_858_);
v___x_878_ = lean_array_push(v___x_877_, v___x_857_);
v___x_879_ = lean_array_push(v___x_878_, v___x_856_);
v___x_880_ = lean_array_push(v___x_879_, v___x_855_);
return v___x_880_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes(void){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__11, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__11_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__11);
return v___x_881_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__0(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = lean_unsigned_to_nat(2u);
v___x_883_ = lean_nat_to_int(v___x_882_);
return v___x_883_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__1(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = lean_unsigned_to_nat(30u);
v___x_885_ = lean_nat_to_int(v___x_884_);
return v___x_885_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__2(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_886_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__1, &l_Std_Time_Month_Ordinal_days___closed__1_once, _init_l_Std_Time_Month_Ordinal_days___closed__1);
v___x_887_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_888_ = lean_int_add(v___x_887_, v___x_886_);
return v___x_888_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__3(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_889_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_890_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__2, &l_Std_Time_Month_Ordinal_days___closed__2_once, _init_l_Std_Time_Month_Ordinal_days___closed__2);
v___x_891_ = lean_int_sub(v___x_890_, v___x_889_);
return v___x_891_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__4(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v_range_894_; 
v___x_892_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_893_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__3, &l_Std_Time_Month_Ordinal_days___closed__3_once, _init_l_Std_Time_Month_Ordinal_days___closed__3);
v_range_894_ = lean_int_add(v___x_893_, v___x_892_);
return v_range_894_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__5(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_895_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_896_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__1, &l_Std_Time_Month_Ordinal_toSeconds___closed__1_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__1);
v___x_897_ = lean_int_sub(v___x_896_, v___x_895_);
return v___x_897_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__6(void){
_start:
{
lean_object* v_range_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v_range_898_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_899_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__5, &l_Std_Time_Month_Ordinal_days___closed__5_once, _init_l_Std_Time_Month_Ordinal_days___closed__5);
v___x_900_ = lean_int_emod(v___x_899_, v_range_898_);
return v___x_900_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__7(void){
_start:
{
lean_object* v_range_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v_range_901_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_902_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__6, &l_Std_Time_Month_Ordinal_days___closed__6_once, _init_l_Std_Time_Month_Ordinal_days___closed__6);
v___x_903_ = lean_int_add(v___x_902_, v_range_901_);
return v___x_903_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__8(void){
_start:
{
lean_object* v_range_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v_range_904_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_905_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__7, &l_Std_Time_Month_Ordinal_days___closed__7_once, _init_l_Std_Time_Month_Ordinal_days___closed__7);
v___x_906_ = lean_int_emod(v___x_905_, v_range_904_);
return v___x_906_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__9(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_907_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_908_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__8, &l_Std_Time_Month_Ordinal_days___closed__8_once, _init_l_Std_Time_Month_Ordinal_days___closed__8);
v___x_909_ = lean_int_add(v___x_908_, v___x_907_);
return v___x_909_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__10(void){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = lean_unsigned_to_nat(28u);
v___x_911_ = lean_nat_to_int(v___x_910_);
return v___x_911_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__11(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_912_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_913_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__10, &l_Std_Time_Month_Ordinal_days___closed__10_once, _init_l_Std_Time_Month_Ordinal_days___closed__10);
v___x_914_ = lean_int_sub(v___x_913_, v___x_912_);
return v___x_914_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__12(void){
_start:
{
lean_object* v_range_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v_range_915_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_916_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__11, &l_Std_Time_Month_Ordinal_days___closed__11_once, _init_l_Std_Time_Month_Ordinal_days___closed__11);
v___x_917_ = lean_int_emod(v___x_916_, v_range_915_);
return v___x_917_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__13(void){
_start:
{
lean_object* v_range_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v_range_918_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_919_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__12, &l_Std_Time_Month_Ordinal_days___closed__12_once, _init_l_Std_Time_Month_Ordinal_days___closed__12);
v___x_920_ = lean_int_add(v___x_919_, v_range_918_);
return v___x_920_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__14(void){
_start:
{
lean_object* v_range_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v_range_921_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_922_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__13, &l_Std_Time_Month_Ordinal_days___closed__13_once, _init_l_Std_Time_Month_Ordinal_days___closed__13);
v___x_923_ = lean_int_emod(v___x_922_, v_range_921_);
return v___x_923_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__15(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_924_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_925_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__14, &l_Std_Time_Month_Ordinal_days___closed__14_once, _init_l_Std_Time_Month_Ordinal_days___closed__14);
v___x_926_ = lean_int_add(v___x_925_, v___x_924_);
return v___x_926_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__16(void){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_927_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_928_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__1, &l_Std_Time_Month_Ordinal_days___closed__1_once, _init_l_Std_Time_Month_Ordinal_days___closed__1);
v___x_929_ = lean_int_sub(v___x_928_, v___x_927_);
return v___x_929_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__17(void){
_start:
{
lean_object* v_range_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v_range_930_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_931_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__16, &l_Std_Time_Month_Ordinal_days___closed__16_once, _init_l_Std_Time_Month_Ordinal_days___closed__16);
v___x_932_ = lean_int_emod(v___x_931_, v_range_930_);
return v___x_932_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__18(void){
_start:
{
lean_object* v_range_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v_range_933_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_934_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__17, &l_Std_Time_Month_Ordinal_days___closed__17_once, _init_l_Std_Time_Month_Ordinal_days___closed__17);
v___x_935_ = lean_int_add(v___x_934_, v_range_933_);
return v___x_935_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__19(void){
_start:
{
lean_object* v_range_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v_range_936_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_937_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__18, &l_Std_Time_Month_Ordinal_days___closed__18_once, _init_l_Std_Time_Month_Ordinal_days___closed__18);
v___x_938_ = lean_int_emod(v___x_937_, v_range_936_);
return v___x_938_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__20(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_939_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_940_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__19, &l_Std_Time_Month_Ordinal_days___closed__19_once, _init_l_Std_Time_Month_Ordinal_days___closed__19);
v___x_941_ = lean_int_add(v___x_940_, v___x_939_);
return v___x_941_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__21(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_942_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__20, &l_Std_Time_Month_Ordinal_days___closed__20_once, _init_l_Std_Time_Month_Ordinal_days___closed__20);
v___x_943_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__15, &l_Std_Time_Month_Ordinal_days___closed__15_once, _init_l_Std_Time_Month_Ordinal_days___closed__15);
v___x_944_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__9, &l_Std_Time_Month_Ordinal_days___closed__9_once, _init_l_Std_Time_Month_Ordinal_days___closed__9);
v___x_945_ = lean_unsigned_to_nat(12u);
v___x_946_ = lean_mk_empty_array_with_capacity(v___x_945_);
v___x_947_ = lean_array_push(v___x_946_, v___x_944_);
v___x_948_ = lean_array_push(v___x_947_, v___x_943_);
v___x_949_ = lean_array_push(v___x_948_, v___x_944_);
v___x_950_ = lean_array_push(v___x_949_, v___x_942_);
v___x_951_ = lean_array_push(v___x_950_, v___x_944_);
v___x_952_ = lean_array_push(v___x_951_, v___x_942_);
v___x_953_ = lean_array_push(v___x_952_, v___x_944_);
v___x_954_ = lean_array_push(v___x_953_, v___x_944_);
v___x_955_ = lean_array_push(v___x_954_, v___x_942_);
v___x_956_ = lean_array_push(v___x_955_, v___x_944_);
v___x_957_ = lean_array_push(v___x_956_, v___x_942_);
v___x_958_ = lean_array_push(v___x_957_, v___x_944_);
return v___x_958_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__22(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = lean_unsigned_to_nat(29u);
v___x_960_ = lean_nat_to_int(v___x_959_);
return v___x_960_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__23(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_961_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_962_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__22, &l_Std_Time_Month_Ordinal_days___closed__22_once, _init_l_Std_Time_Month_Ordinal_days___closed__22);
v___x_963_ = lean_int_sub(v___x_962_, v___x_961_);
return v___x_963_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__24(void){
_start:
{
lean_object* v_range_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v_range_964_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_965_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__23, &l_Std_Time_Month_Ordinal_days___closed__23_once, _init_l_Std_Time_Month_Ordinal_days___closed__23);
v___x_966_ = lean_int_emod(v___x_965_, v_range_964_);
return v___x_966_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__25(void){
_start:
{
lean_object* v_range_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v_range_967_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_968_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__24, &l_Std_Time_Month_Ordinal_days___closed__24_once, _init_l_Std_Time_Month_Ordinal_days___closed__24);
v___x_969_ = lean_int_add(v___x_968_, v_range_967_);
return v___x_969_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__26(void){
_start:
{
lean_object* v_range_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v_range_970_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_971_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__25, &l_Std_Time_Month_Ordinal_days___closed__25_once, _init_l_Std_Time_Month_Ordinal_days___closed__25);
v___x_972_ = lean_int_emod(v___x_971_, v_range_970_);
return v___x_972_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__27(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_973_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_974_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__26, &l_Std_Time_Month_Ordinal_days___closed__26_once, _init_l_Std_Time_Month_Ordinal_days___closed__26);
v___x_975_ = lean_int_add(v___x_974_, v___x_973_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_days(uint8_t v_leap_976_, lean_object* v_month_977_){
_start:
{
lean_object* v___x_978_; uint8_t v___x_979_; 
v___x_978_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__0, &l_Std_Time_Month_Ordinal_days___closed__0_once, _init_l_Std_Time_Month_Ordinal_days___closed__0);
v___x_979_ = lean_int_dec_eq(v_month_977_, v___x_978_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_980_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__21, &l_Std_Time_Month_Ordinal_days___closed__21_once, _init_l_Std_Time_Month_Ordinal_days___closed__21);
v___x_981_ = lean_obj_once(&l_Std_Time_Month_Quarter_ofMonth___closed__1, &l_Std_Time_Month_Quarter_ofMonth___closed__1_once, _init_l_Std_Time_Month_Quarter_ofMonth___closed__1);
v___x_982_ = lean_int_add(v_month_977_, v___x_981_);
v___x_983_ = l_Int_toNat(v___x_982_);
lean_dec(v___x_982_);
v___x_984_ = lean_array_fget_borrowed(v___x_980_, v___x_983_);
lean_dec(v___x_983_);
lean_inc(v___x_984_);
return v___x_984_;
}
else
{
if (v_leap_976_ == 0)
{
lean_object* v___x_985_; 
v___x_985_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__15, &l_Std_Time_Month_Ordinal_days___closed__15_once, _init_l_Std_Time_Month_Ordinal_days___closed__15);
return v___x_985_;
}
else
{
lean_object* v___x_986_; 
v___x_986_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__27, &l_Std_Time_Month_Ordinal_days___closed__27_once, _init_l_Std_Time_Month_Ordinal_days___closed__27);
return v___x_986_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_days___boxed(lean_object* v_leap_987_, lean_object* v_month_988_){
_start:
{
uint8_t v_leap_boxed_989_; lean_object* v_res_990_; 
v_leap_boxed_989_ = lean_unbox(v_leap_987_);
v_res_990_ = l_Std_Time_Month_Ordinal_days(v_leap_boxed_989_, v_month_988_);
lean_dec(v_month_988_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_cumulativeDays(uint8_t v_leap_991_, lean_object* v_month_992_){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v_res_1001_; 
v___x_993_ = lean_obj_once(&l_Std_Time_Month_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0);
v___x_994_ = lean_unsigned_to_nat(12u);
v___x_995_ = lean_mk_empty_array_with_capacity(v___x_994_);
lean_dec_ref(v___x_995_);
v___x_996_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__12, &l_Std_Time_Month_Ordinal_toSeconds___closed__12_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__12);
v___x_997_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_998_ = lean_obj_once(&l_Std_Time_Month_Quarter_ofMonth___closed__1, &l_Std_Time_Month_Quarter_ofMonth___closed__1_once, _init_l_Std_Time_Month_Quarter_ofMonth___closed__1);
v___x_999_ = lean_int_add(v_month_992_, v___x_998_);
v___x_1000_ = l_Int_toNat(v___x_999_);
lean_dec(v___x_999_);
v_res_1001_ = lean_array_fget_borrowed(v___x_996_, v___x_1000_);
lean_dec(v___x_1000_);
if (v_leap_991_ == 0)
{
lean_object* v___x_1002_; 
v___x_1002_ = lean_int_add(v_res_1001_, v___x_993_);
return v___x_1002_;
}
else
{
lean_object* v___x_1003_; uint8_t v___x_1004_; 
v___x_1003_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__0, &l_Std_Time_Month_Ordinal_days___closed__0_once, _init_l_Std_Time_Month_Ordinal_days___closed__0);
v___x_1004_ = lean_int_dec_lt(v___x_1003_, v_month_992_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_int_add(v_res_1001_, v___x_993_);
return v___x_1005_;
}
else
{
lean_object* v___x_1006_; 
v___x_1006_ = lean_int_add(v_res_1001_, v___x_997_);
return v___x_1006_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_cumulativeDays___boxed(lean_object* v_leap_1007_, lean_object* v_month_1008_){
_start:
{
uint8_t v_leap_boxed_1009_; lean_object* v_res_1010_; 
v_leap_boxed_1009_ = lean_unbox(v_leap_1007_);
v_res_1010_ = l_Std_Time_Month_Ordinal_cumulativeDays(v_leap_boxed_1009_, v_month_1008_);
lean_dec(v_month_1008_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_clipDay(uint8_t v_leap_1011_, lean_object* v_month_1012_, lean_object* v_day_1013_){
_start:
{
lean_object* v_max_1014_; uint8_t v___x_1015_; 
v_max_1014_ = l_Std_Time_Month_Ordinal_days(v_leap_1011_, v_month_1012_);
v___x_1015_ = lean_int_dec_lt(v_max_1014_, v_day_1013_);
if (v___x_1015_ == 0)
{
lean_dec(v_max_1014_);
lean_inc(v_day_1013_);
return v_day_1013_;
}
else
{
return v_max_1014_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_clipDay___boxed(lean_object* v_leap_1016_, lean_object* v_month_1017_, lean_object* v_day_1018_){
_start:
{
uint8_t v_leap_boxed_1019_; lean_object* v_res_1020_; 
v_leap_boxed_1019_ = lean_unbox(v_leap_1016_);
v_res_1020_ = l_Std_Time_Month_Ordinal_clipDay(v_leap_boxed_1019_, v_month_1017_, v_day_1018_);
lean_dec(v_day_1018_);
lean_dec(v_month_1017_);
return v_res_1020_;
}
}
lean_object* runtime_initialize_Std_Time_Date_Unit_Day(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Date_Unit_Month(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Time_Date_Unit_Day(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_Month_instLEOrdinal = _init_l_Std_Time_Month_instLEOrdinal();
lean_mark_persistent(l_Std_Time_Month_instLEOrdinal);
l_Std_Time_Month_instLTOrdinal = _init_l_Std_Time_Month_instLTOrdinal();
lean_mark_persistent(l_Std_Time_Month_instLTOrdinal);
l_Std_Time_Month_instInhabitedOrdinal = _init_l_Std_Time_Month_instInhabitedOrdinal();
lean_mark_persistent(l_Std_Time_Month_instInhabitedOrdinal);
l_Std_Time_Month_instInhabitedOffset___aux__1 = _init_l_Std_Time_Month_instInhabitedOffset___aux__1();
lean_mark_persistent(l_Std_Time_Month_instInhabitedOffset___aux__1);
l_Std_Time_Month_instInhabitedOffset = _init_l_Std_Time_Month_instInhabitedOffset();
lean_mark_persistent(l_Std_Time_Month_instInhabitedOffset);
l_Std_Time_Month_instLTOffset = _init_l_Std_Time_Month_instLTOffset();
lean_mark_persistent(l_Std_Time_Month_instLTOffset);
l_Std_Time_Month_instLEOffset = _init_l_Std_Time_Month_instLEOffset();
lean_mark_persistent(l_Std_Time_Month_instLEOffset);
l_Std_Time_Month_instLTQuarter = _init_l_Std_Time_Month_instLTQuarter();
lean_mark_persistent(l_Std_Time_Month_instLTQuarter);
l_Std_Time_Month_instLEQuarter = _init_l_Std_Time_Month_instLEQuarter();
lean_mark_persistent(l_Std_Time_Month_instLEQuarter);
l_Std_Time_Month_instInhabitedQuarter = _init_l_Std_Time_Month_instInhabitedQuarter();
lean_mark_persistent(l_Std_Time_Month_instInhabitedQuarter);
l_Std_Time_Month_Ordinal_january = _init_l_Std_Time_Month_Ordinal_january();
lean_mark_persistent(l_Std_Time_Month_Ordinal_january);
l_Std_Time_Month_Ordinal_february = _init_l_Std_Time_Month_Ordinal_february();
lean_mark_persistent(l_Std_Time_Month_Ordinal_february);
l_Std_Time_Month_Ordinal_march = _init_l_Std_Time_Month_Ordinal_march();
lean_mark_persistent(l_Std_Time_Month_Ordinal_march);
l_Std_Time_Month_Ordinal_april = _init_l_Std_Time_Month_Ordinal_april();
lean_mark_persistent(l_Std_Time_Month_Ordinal_april);
l_Std_Time_Month_Ordinal_may = _init_l_Std_Time_Month_Ordinal_may();
lean_mark_persistent(l_Std_Time_Month_Ordinal_may);
l_Std_Time_Month_Ordinal_june = _init_l_Std_Time_Month_Ordinal_june();
lean_mark_persistent(l_Std_Time_Month_Ordinal_june);
l_Std_Time_Month_Ordinal_july = _init_l_Std_Time_Month_Ordinal_july();
lean_mark_persistent(l_Std_Time_Month_Ordinal_july);
l_Std_Time_Month_Ordinal_august = _init_l_Std_Time_Month_Ordinal_august();
lean_mark_persistent(l_Std_Time_Month_Ordinal_august);
l_Std_Time_Month_Ordinal_september = _init_l_Std_Time_Month_Ordinal_september();
lean_mark_persistent(l_Std_Time_Month_Ordinal_september);
l_Std_Time_Month_Ordinal_october = _init_l_Std_Time_Month_Ordinal_october();
lean_mark_persistent(l_Std_Time_Month_Ordinal_october);
l_Std_Time_Month_Ordinal_november = _init_l_Std_Time_Month_Ordinal_november();
lean_mark_persistent(l_Std_Time_Month_Ordinal_november);
l_Std_Time_Month_Ordinal_december = _init_l_Std_Time_Month_Ordinal_december();
lean_mark_persistent(l_Std_Time_Month_Ordinal_december);
l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap = _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap();
lean_mark_persistent(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap);
l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes = _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes();
lean_mark_persistent(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Date_Unit_Month(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Std_Time_Month_Ordinal_ofNat___auto__1 = _init_l_Std_Time_Month_Ordinal_ofNat___auto__1();
lean_mark_persistent(l_Std_Time_Month_Ordinal_ofNat___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Date_Unit_Day(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Date_Unit_Month(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Date_Unit_Day(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Date_Unit_Month(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Date_Unit_Month(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Date_Unit_Month(builtin);
}
#ifdef __cplusplus
}
#endif
