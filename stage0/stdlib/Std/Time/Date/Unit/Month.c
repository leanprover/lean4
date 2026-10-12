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
uint8_t l_Std_Time_Month_instDecidableEqOrdinal___aux__1(lean_object* v_a_29_, lean_object* v_b_30_){
_start:
{
uint8_t v___x_31_; 
v___x_31_ = lean_int_dec_eq(v_a_29_, v_b_30_);
return v___x_31_;
}
}
LEAN_EXPORT void l_Std_Time_Month_instDecidableEqOrdinal___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_29_ = stack[0].m_obj;
lean_object* v_b_30_ = stack[1].m_obj;
uint8_t v_res_32_;
v_res_32_ = l_Std_Time_Month_instDecidableEqOrdinal___aux__1(v_a_29_, v_b_30_);
stack->m_num = v_res_32_;
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableEqOrdinal___aux__1___boxed(lean_object* v_a_33_, lean_object* v_b_34_){
_start:
{
uint8_t v_res_35_; lean_object* v_r_36_; 
v_res_35_ = l_Std_Time_Month_instDecidableEqOrdinal___aux__1(v_a_33_, v_b_34_);
lean_dec(v_b_34_);
lean_dec(v_a_33_);
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
uint8_t l_Std_Time_Month_instDecidableEqOrdinal(lean_object* v_a_37_, lean_object* v_b_38_){
_start:
{
uint8_t v___x_39_; 
v___x_39_ = lean_int_dec_eq(v_a_37_, v_b_38_);
return v___x_39_;
}
}
LEAN_EXPORT void l_Std_Time_Month_instDecidableEqOrdinal_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_37_ = stack[0].m_obj;
lean_object* v_b_38_ = stack[1].m_obj;
uint8_t v_res_40_;
v_res_40_ = l_Std_Time_Month_instDecidableEqOrdinal(v_a_37_, v_b_38_);
stack->m_num = v_res_40_;
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableEqOrdinal___boxed(lean_object* v_a_41_, lean_object* v_b_42_){
_start:
{
uint8_t v_res_43_; lean_object* v_r_44_; 
v_res_43_ = l_Std_Time_Month_instDecidableEqOrdinal(v_a_41_, v_b_42_);
lean_dec(v_b_42_);
lean_dec(v_a_41_);
v_r_44_ = lean_box(v_res_43_);
return v_r_44_;
}
}
static lean_object* _init_l_Std_Time_Month_instLEOrdinal(void){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_box(0);
return v___x_45_;
}
}
static lean_object* _init_l_Std_Time_Month_instLTOrdinal(void){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_box(0);
return v___x_46_;
}
}
static lean_object* _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_unsigned_to_nat(1u);
v___x_48_ = lean_nat_to_int(v___x_47_);
return v___x_48_;
}
}
static lean_object* _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_unsigned_to_nat(11u);
v___x_50_ = lean_nat_to_int(v___x_49_);
return v___x_50_;
}
}
static lean_object* _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__2(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1);
v___x_52_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_53_ = lean_int_add(v___x_52_, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__3(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_55_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__2, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__2_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__2);
v___x_56_ = lean_int_sub(v___x_55_, v___x_54_);
return v___x_56_;
}
}
static lean_object* _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v_range_59_; 
v___x_57_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_58_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__3);
v_range_59_ = lean_int_add(v___x_58_, v___x_57_);
return v_range_59_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instOfNatOrdinal___aux__1(lean_object* v_n_60_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v_range_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_61_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_62_ = lean_nat_to_int(v_n_60_);
v_range_63_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_64_ = lean_int_sub(v___x_62_, v___x_61_);
lean_dec(v___x_62_);
v___x_65_ = lean_int_emod(v___x_64_, v_range_63_);
lean_dec(v___x_64_);
v___x_66_ = lean_int_add(v___x_65_, v_range_63_);
lean_dec(v___x_65_);
v___x_67_ = lean_int_emod(v___x_66_, v_range_63_);
lean_dec(v___x_66_);
v___x_68_ = lean_int_add(v___x_67_, v___x_61_);
lean_dec(v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instOfNatOrdinal(lean_object* v_n_69_){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v_range_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_70_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_71_ = lean_nat_to_int(v_n_69_);
v_range_72_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_73_ = lean_int_sub(v___x_71_, v___x_70_);
lean_dec(v___x_71_);
v___x_74_ = lean_int_emod(v___x_73_, v_range_72_);
lean_dec(v___x_73_);
v___x_75_ = lean_int_add(v___x_74_, v_range_72_);
lean_dec(v___x_74_);
v___x_76_ = lean_int_emod(v___x_75_, v_range_72_);
lean_dec(v___x_75_);
v___x_77_ = lean_int_add(v___x_76_, v___x_70_);
lean_dec(v___x_76_);
return v___x_77_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedOrdinal___closed__0(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_79_ = lean_int_sub(v___x_78_, v___x_78_);
return v___x_79_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedOrdinal___closed__1(void){
_start:
{
lean_object* v_range_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v_range_80_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_81_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__0, &l_Std_Time_Month_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__0);
v___x_82_ = lean_int_emod(v___x_81_, v_range_80_);
return v___x_82_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedOrdinal___closed__2(void){
_start:
{
lean_object* v_range_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v_range_83_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_84_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__1, &l_Std_Time_Month_instInhabitedOrdinal___closed__1_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__1);
v___x_85_ = lean_int_add(v___x_84_, v_range_83_);
return v___x_85_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3(void){
_start:
{
lean_object* v_range_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v_range_86_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_87_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__2, &l_Std_Time_Month_instInhabitedOrdinal___closed__2_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__2);
v___x_88_ = lean_int_emod(v___x_87_, v_range_86_);
return v___x_88_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedOrdinal___closed__4(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_89_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_90_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_91_ = lean_int_add(v___x_90_, v___x_89_);
return v___x_91_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedOrdinal(void){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__4, &l_Std_Time_Month_instInhabitedOrdinal___closed__4_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__4);
return v___x_92_;
}
}
uint8_t l_Std_Time_Month_instDecidableLeOrdinal___aux__1(lean_object* v_x_93_, lean_object* v_y_94_){
_start:
{
uint8_t v___x_95_; 
v___x_95_ = lean_int_dec_le(v_x_93_, v_y_94_);
return v___x_95_;
}
}
LEAN_EXPORT void l_Std_Time_Month_instDecidableLeOrdinal___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_93_ = stack[0].m_obj;
lean_object* v_y_94_ = stack[1].m_obj;
uint8_t v_res_96_;
v_res_96_ = l_Std_Time_Month_instDecidableLeOrdinal___aux__1(v_x_93_, v_y_94_);
stack->m_num = v_res_96_;
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableLeOrdinal___aux__1___boxed(lean_object* v_x_97_, lean_object* v_y_98_){
_start:
{
uint8_t v_res_99_; lean_object* v_r_100_; 
v_res_99_ = l_Std_Time_Month_instDecidableLeOrdinal___aux__1(v_x_97_, v_y_98_);
lean_dec(v_y_98_);
lean_dec(v_x_97_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
uint8_t l_Std_Time_Month_instDecidableLeOrdinal(lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
uint8_t v___x_103_; 
v___x_103_ = lean_int_dec_le(v___y_101_, v___y_102_);
return v___x_103_;
}
}
LEAN_EXPORT void l_Std_Time_Month_instDecidableLeOrdinal_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_101_ = stack[0].m_obj;
lean_object* v___y_102_ = stack[1].m_obj;
uint8_t v_res_104_;
v_res_104_ = l_Std_Time_Month_instDecidableLeOrdinal(v___y_101_, v___y_102_);
stack->m_num = v_res_104_;
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableLeOrdinal___boxed(lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
uint8_t v_res_107_; lean_object* v_r_108_; 
v_res_107_ = l_Std_Time_Month_instDecidableLeOrdinal(v___y_105_, v___y_106_);
lean_dec(v___y_106_);
lean_dec(v___y_105_);
v_r_108_ = lean_box(v_res_107_);
return v_r_108_;
}
}
uint8_t l_Std_Time_Month_instDecidableLtOrdinal___aux__1(lean_object* v_x_109_, lean_object* v_y_110_){
_start:
{
uint8_t v___x_111_; 
v___x_111_ = lean_int_dec_lt(v_x_109_, v_y_110_);
return v___x_111_;
}
}
LEAN_EXPORT void l_Std_Time_Month_instDecidableLtOrdinal___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_109_ = stack[0].m_obj;
lean_object* v_y_110_ = stack[1].m_obj;
uint8_t v_res_112_;
v_res_112_ = l_Std_Time_Month_instDecidableLtOrdinal___aux__1(v_x_109_, v_y_110_);
stack->m_num = v_res_112_;
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableLtOrdinal___aux__1___boxed(lean_object* v_x_113_, lean_object* v_y_114_){
_start:
{
uint8_t v_res_115_; lean_object* v_r_116_; 
v_res_115_ = l_Std_Time_Month_instDecidableLtOrdinal___aux__1(v_x_113_, v_y_114_);
lean_dec(v_y_114_);
lean_dec(v_x_113_);
v_r_116_ = lean_box(v_res_115_);
return v_r_116_;
}
}
uint8_t l_Std_Time_Month_instDecidableLtOrdinal(lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
uint8_t v___x_119_; 
v___x_119_ = lean_int_dec_lt(v___y_117_, v___y_118_);
return v___x_119_;
}
}
LEAN_EXPORT void l_Std_Time_Month_instDecidableLtOrdinal_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_117_ = stack[0].m_obj;
lean_object* v___y_118_ = stack[1].m_obj;
uint8_t v_res_120_;
v_res_120_ = l_Std_Time_Month_instDecidableLtOrdinal(v___y_117_, v___y_118_);
stack->m_num = v_res_120_;
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableLtOrdinal___boxed(lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
uint8_t v_res_123_; lean_object* v_r_124_; 
v_res_123_ = l_Std_Time_Month_instDecidableLtOrdinal(v___y_121_, v___y_122_);
lean_dec(v___y_122_);
lean_dec(v___y_121_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
uint8_t l_Std_Time_Month_instOrdOrdinal___aux__1(lean_object* v_x_125_, lean_object* v_y_126_){
_start:
{
uint8_t v___x_127_; 
v___x_127_ = lean_int_dec_lt(v_x_125_, v_y_126_);
if (v___x_127_ == 0)
{
uint8_t v___x_128_; 
v___x_128_ = lean_int_dec_eq(v_x_125_, v_y_126_);
if (v___x_128_ == 0)
{
uint8_t v___x_129_; 
v___x_129_ = 2;
return v___x_129_;
}
else
{
uint8_t v___x_130_; 
v___x_130_ = 1;
return v___x_130_;
}
}
else
{
uint8_t v___x_131_; 
v___x_131_ = 0;
return v___x_131_;
}
}
}
LEAN_EXPORT void l_Std_Time_Month_instOrdOrdinal___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_125_ = stack[0].m_obj;
lean_object* v_y_126_ = stack[1].m_obj;
uint8_t v_res_132_;
v_res_132_ = l_Std_Time_Month_instOrdOrdinal___aux__1(v_x_125_, v_y_126_);
stack->m_num = v_res_132_;
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instOrdOrdinal___aux__1___boxed(lean_object* v_x_133_, lean_object* v_y_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = l_Std_Time_Month_instOrdOrdinal___aux__1(v_x_133_, v_y_134_);
lean_dec(v_y_134_);
lean_dec(v_x_133_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instReprOffset___aux__1(lean_object* v_i_139_, lean_object* v_prec_140_){
_start:
{
lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_141_ = lean_obj_once(&l_Std_Time_Month_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0);
v___x_142_ = lean_int_dec_lt(v_i_139_, v___x_141_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = l_Int_repr(v_i_139_);
v___x_144_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
return v___x_144_;
}
else
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_145_ = l_Int_repr(v_i_139_);
v___x_146_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
v___x_147_ = l_Repr_addAppParen(v___x_146_, v_prec_140_);
return v___x_147_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instReprOffset___aux__1___boxed(lean_object* v_i_148_, lean_object* v_prec_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Std_Time_Month_instReprOffset___aux__1(v_i_148_, v_prec_149_);
lean_dec(v_prec_149_);
lean_dec(v_i_148_);
return v_res_150_;
}
}
uint8_t l_Std_Time_Month_instDecidableEqOffset___aux__1(lean_object* v_a_152_, lean_object* v_b_153_){
_start:
{
uint8_t v___x_154_; 
v___x_154_ = lean_int_dec_eq(v_a_152_, v_b_153_);
return v___x_154_;
}
}
LEAN_EXPORT void l_Std_Time_Month_instDecidableEqOffset___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_152_ = stack[0].m_obj;
lean_object* v_b_153_ = stack[1].m_obj;
uint8_t v_res_155_;
v_res_155_ = l_Std_Time_Month_instDecidableEqOffset___aux__1(v_a_152_, v_b_153_);
stack->m_num = v_res_155_;
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableEqOffset___aux__1___boxed(lean_object* v_a_156_, lean_object* v_b_157_){
_start:
{
uint8_t v_res_158_; lean_object* v_r_159_; 
v_res_158_ = l_Std_Time_Month_instDecidableEqOffset___aux__1(v_a_156_, v_b_157_);
lean_dec(v_b_157_);
lean_dec(v_a_156_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
uint8_t l_Std_Time_Month_instDecidableEqOffset(lean_object* v_a_160_, lean_object* v_b_161_){
_start:
{
uint8_t v___x_162_; 
v___x_162_ = lean_int_dec_eq(v_a_160_, v_b_161_);
return v___x_162_;
}
}
LEAN_EXPORT void l_Std_Time_Month_instDecidableEqOffset_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_160_ = stack[0].m_obj;
lean_object* v_b_161_ = stack[1].m_obj;
uint8_t v_res_163_;
v_res_163_ = l_Std_Time_Month_instDecidableEqOffset(v_a_160_, v_b_161_);
stack->m_num = v_res_163_;
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableEqOffset___boxed(lean_object* v_a_164_, lean_object* v_b_165_){
_start:
{
uint8_t v_res_166_; lean_object* v_r_167_; 
v_res_166_ = l_Std_Time_Month_instDecidableEqOffset(v_a_164_, v_b_165_);
lean_dec(v_b_165_);
lean_dec(v_a_164_);
v_r_167_ = lean_box(v_res_166_);
return v_r_167_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedOffset___aux__1(void){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = lean_obj_once(&l_Std_Time_Month_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0);
return v___x_168_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedOffset(void){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = lean_obj_once(&l_Std_Time_Month_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instAddOffset___aux__1(lean_object* v_m_170_, lean_object* v_n_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lean_int_add(v_m_170_, v_n_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instAddOffset___aux__1___boxed(lean_object* v_m_173_, lean_object* v_n_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Std_Time_Month_instAddOffset___aux__1(v_m_173_, v_n_174_);
lean_dec(v_n_174_);
lean_dec(v_m_173_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instSubOffset___aux__1(lean_object* v_m_178_, lean_object* v_n_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = lean_int_sub(v_m_178_, v_n_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instSubOffset___aux__1___boxed(lean_object* v_m_181_, lean_object* v_n_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Std_Time_Month_instSubOffset___aux__1(v_m_181_, v_n_182_);
lean_dec(v_n_182_);
lean_dec(v_m_181_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instMulOffset___aux__1(lean_object* v_m_186_, lean_object* v_n_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = lean_int_mul(v_m_186_, v_n_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instMulOffset___aux__1___boxed(lean_object* v_m_189_, lean_object* v_n_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Std_Time_Month_instMulOffset___aux__1(v_m_189_, v_n_190_);
lean_dec(v_n_190_);
lean_dec(v_m_189_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDivOffset___aux__1(lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = lean_int_ediv(v_a_194_, v_a_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDivOffset___aux__1___boxed(lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Std_Time_Month_instDivOffset___aux__1(v_a_197_, v_a_198_);
lean_dec(v_a_198_);
lean_dec(v_a_197_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instNegOffset___aux__1(lean_object* v_n_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = lean_int_neg(v_n_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instNegOffset___aux__1___boxed(lean_object* v_n_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Std_Time_Month_instNegOffset___aux__1(v_n_204_);
lean_dec(v_n_204_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instToStringOffset___aux__1(lean_object* v_a_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Int_repr(v_a_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instToStringOffset___aux__1___boxed(lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Std_Time_Month_instToStringOffset___aux__1(v_a_210_);
lean_dec(v_a_210_);
return v_res_211_;
}
}
static lean_object* _init_l_Std_Time_Month_instLTOffset(void){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = lean_box(0);
return v___x_214_;
}
}
static lean_object* _init_l_Std_Time_Month_instLEOffset(void){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = lean_box(0);
return v___x_215_;
}
}
uint8_t l_Std_Time_Month_instDecidableLeOffset(lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
uint8_t v___x_218_; 
v___x_218_ = lean_int_dec_le(v___y_216_, v___y_217_);
return v___x_218_;
}
}
LEAN_EXPORT void l_Std_Time_Month_instDecidableLeOffset_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_216_ = stack[0].m_obj;
lean_object* v___y_217_ = stack[1].m_obj;
uint8_t v_res_219_;
v_res_219_ = l_Std_Time_Month_instDecidableLeOffset(v___y_216_, v___y_217_);
stack->m_num = v_res_219_;
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableLeOffset___boxed(lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
uint8_t v_res_222_; lean_object* v_r_223_; 
v_res_222_ = l_Std_Time_Month_instDecidableLeOffset(v___y_220_, v___y_221_);
lean_dec(v___y_221_);
lean_dec(v___y_220_);
v_r_223_ = lean_box(v_res_222_);
return v_r_223_;
}
}
uint8_t l_Std_Time_Month_instDecidableLtOffset(lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
uint8_t v___x_226_; 
v___x_226_ = lean_int_dec_lt(v___y_224_, v___y_225_);
return v___x_226_;
}
}
LEAN_EXPORT void l_Std_Time_Month_instDecidableLtOffset_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_224_ = stack[0].m_obj;
lean_object* v___y_225_ = stack[1].m_obj;
uint8_t v_res_227_;
v_res_227_ = l_Std_Time_Month_instDecidableLtOffset(v___y_224_, v___y_225_);
stack->m_num = v_res_227_;
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableLtOffset___boxed(lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
uint8_t v_res_230_; lean_object* v_r_231_; 
v_res_230_ = l_Std_Time_Month_instDecidableLtOffset(v___y_228_, v___y_229_);
lean_dec(v___y_229_);
lean_dec(v___y_228_);
v_r_231_ = lean_box(v_res_230_);
return v_r_231_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instOfNatOffset(lean_object* v_n_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = lean_nat_to_int(v_n_232_);
return v___x_233_;
}
}
uint8_t l_Std_Time_Month_instOrdOffset___aux__1(lean_object* v_x_234_, lean_object* v_y_235_){
_start:
{
uint8_t v___x_236_; 
v___x_236_ = lean_int_dec_lt(v_x_234_, v_y_235_);
if (v___x_236_ == 0)
{
uint8_t v___x_237_; 
v___x_237_ = lean_int_dec_eq(v_x_234_, v_y_235_);
if (v___x_237_ == 0)
{
uint8_t v___x_238_; 
v___x_238_ = 2;
return v___x_238_;
}
else
{
uint8_t v___x_239_; 
v___x_239_ = 1;
return v___x_239_;
}
}
else
{
uint8_t v___x_240_; 
v___x_240_ = 0;
return v___x_240_;
}
}
}
LEAN_EXPORT void l_Std_Time_Month_instOrdOffset___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_234_ = stack[0].m_obj;
lean_object* v_y_235_ = stack[1].m_obj;
uint8_t v_res_241_;
v_res_241_ = l_Std_Time_Month_instOrdOffset___aux__1(v_x_234_, v_y_235_);
stack->m_num = v_res_241_;
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instOrdOffset___aux__1___boxed(lean_object* v_x_242_, lean_object* v_y_243_){
_start:
{
uint8_t v_res_244_; lean_object* v_r_245_; 
v_res_244_ = l_Std_Time_Month_instOrdOffset___aux__1(v_x_242_, v_y_243_);
lean_dec(v_y_243_);
lean_dec(v_x_242_);
v_r_245_ = lean_box(v_res_244_);
return v_r_245_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instReprQuarter___aux__1(lean_object* v_n_248_, lean_object* v_a_249_){
_start:
{
lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_250_ = lean_obj_once(&l_Std_Time_Month_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0);
v___x_251_ = lean_int_dec_lt(v_n_248_, v___x_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = l_Int_repr(v_n_248_);
v___x_253_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
return v___x_253_;
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = l_Int_repr(v_n_248_);
v___x_255_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
v___x_256_ = l_Repr_addAppParen(v___x_255_, v_a_249_);
return v___x_256_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instReprQuarter___aux__1___boxed(lean_object* v_n_257_, lean_object* v_a_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Std_Time_Month_instReprQuarter___aux__1(v_n_257_, v_a_258_);
lean_dec(v_a_258_);
lean_dec(v_n_257_);
return v_res_259_;
}
}
uint8_t l_Std_Time_Month_instDecidableEqQuarter___aux__1(lean_object* v_a_261_, lean_object* v_b_262_){
_start:
{
uint8_t v___x_263_; 
v___x_263_ = lean_int_dec_eq(v_a_261_, v_b_262_);
return v___x_263_;
}
}
LEAN_EXPORT void l_Std_Time_Month_instDecidableEqQuarter___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_261_ = stack[0].m_obj;
lean_object* v_b_262_ = stack[1].m_obj;
uint8_t v_res_264_;
v_res_264_ = l_Std_Time_Month_instDecidableEqQuarter___aux__1(v_a_261_, v_b_262_);
stack->m_num = v_res_264_;
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableEqQuarter___aux__1___boxed(lean_object* v_a_265_, lean_object* v_b_266_){
_start:
{
uint8_t v_res_267_; lean_object* v_r_268_; 
v_res_267_ = l_Std_Time_Month_instDecidableEqQuarter___aux__1(v_a_265_, v_b_266_);
lean_dec(v_b_266_);
lean_dec(v_a_265_);
v_r_268_ = lean_box(v_res_267_);
return v_r_268_;
}
}
uint8_t l_Std_Time_Month_instDecidableEqQuarter(lean_object* v_a_269_, lean_object* v_b_270_){
_start:
{
uint8_t v___x_271_; 
v___x_271_ = lean_int_dec_eq(v_a_269_, v_b_270_);
return v___x_271_;
}
}
LEAN_EXPORT void l_Std_Time_Month_instDecidableEqQuarter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_269_ = stack[0].m_obj;
lean_object* v_b_270_ = stack[1].m_obj;
uint8_t v_res_272_;
v_res_272_ = l_Std_Time_Month_instDecidableEqQuarter(v_a_269_, v_b_270_);
stack->m_num = v_res_272_;
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableEqQuarter___boxed(lean_object* v_a_273_, lean_object* v_b_274_){
_start:
{
uint8_t v_res_275_; lean_object* v_r_276_; 
v_res_275_ = l_Std_Time_Month_instDecidableEqQuarter(v_a_273_, v_b_274_);
lean_dec(v_b_274_);
lean_dec(v_a_273_);
v_r_276_ = lean_box(v_res_275_);
return v_r_276_;
}
}
static lean_object* _init_l_Std_Time_Month_instLTQuarter(void){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = lean_box(0);
return v___x_277_;
}
}
static lean_object* _init_l_Std_Time_Month_instLEQuarter(void){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = lean_box(0);
return v___x_278_;
}
}
static lean_object* _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_unsigned_to_nat(3u);
v___x_280_ = lean_nat_to_int(v___x_279_);
return v___x_280_;
}
}
static lean_object* _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__1(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_281_ = lean_obj_once(&l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0, &l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0);
v___x_282_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_283_ = lean_int_add(v___x_282_, v___x_281_);
return v___x_283_;
}
}
static lean_object* _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__2(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_284_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_285_ = lean_obj_once(&l_Std_Time_Month_instOfNatQuarter___aux__1___closed__1, &l_Std_Time_Month_instOfNatQuarter___aux__1___closed__1_once, _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__1);
v___x_286_ = lean_int_sub(v___x_285_, v___x_284_);
return v___x_286_;
}
}
static lean_object* _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v_range_289_; 
v___x_287_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_288_ = lean_obj_once(&l_Std_Time_Month_instOfNatQuarter___aux__1___closed__2, &l_Std_Time_Month_instOfNatQuarter___aux__1___closed__2_once, _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__2);
v_range_289_ = lean_int_add(v___x_288_, v___x_287_);
return v_range_289_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instOfNatQuarter___aux__1(lean_object* v_n_290_){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v_range_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_291_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_292_ = lean_nat_to_int(v_n_290_);
v_range_293_ = lean_obj_once(&l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3, &l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3_once, _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3);
v___x_294_ = lean_int_sub(v___x_292_, v___x_291_);
lean_dec(v___x_292_);
v___x_295_ = lean_int_emod(v___x_294_, v_range_293_);
lean_dec(v___x_294_);
v___x_296_ = lean_int_add(v___x_295_, v_range_293_);
lean_dec(v___x_295_);
v___x_297_ = lean_int_emod(v___x_296_, v_range_293_);
lean_dec(v___x_296_);
v___x_298_ = lean_int_add(v___x_297_, v___x_291_);
lean_dec(v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instOfNatQuarter(lean_object* v_n_299_){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v_range_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_300_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_301_ = lean_nat_to_int(v_n_299_);
v_range_302_ = lean_obj_once(&l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3, &l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3_once, _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3);
v___x_303_ = lean_int_sub(v___x_301_, v___x_300_);
lean_dec(v___x_301_);
v___x_304_ = lean_int_emod(v___x_303_, v_range_302_);
lean_dec(v___x_303_);
v___x_305_ = lean_int_add(v___x_304_, v_range_302_);
lean_dec(v___x_304_);
v___x_306_ = lean_int_emod(v___x_305_, v_range_302_);
lean_dec(v___x_305_);
v___x_307_ = lean_int_add(v___x_306_, v___x_300_);
lean_dec(v___x_306_);
return v___x_307_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedQuarter___closed__0(void){
_start:
{
lean_object* v_range_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v_range_308_ = lean_obj_once(&l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3, &l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3_once, _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3);
v___x_309_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__0, &l_Std_Time_Month_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__0);
v___x_310_ = lean_int_emod(v___x_309_, v_range_308_);
return v___x_310_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedQuarter___closed__1(void){
_start:
{
lean_object* v_range_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v_range_311_ = lean_obj_once(&l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3, &l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3_once, _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3);
v___x_312_ = lean_obj_once(&l_Std_Time_Month_instInhabitedQuarter___closed__0, &l_Std_Time_Month_instInhabitedQuarter___closed__0_once, _init_l_Std_Time_Month_instInhabitedQuarter___closed__0);
v___x_313_ = lean_int_add(v___x_312_, v_range_311_);
return v___x_313_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedQuarter___closed__2(void){
_start:
{
lean_object* v_range_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v_range_314_ = lean_obj_once(&l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3, &l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3_once, _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3);
v___x_315_ = lean_obj_once(&l_Std_Time_Month_instInhabitedQuarter___closed__1, &l_Std_Time_Month_instInhabitedQuarter___closed__1_once, _init_l_Std_Time_Month_instInhabitedQuarter___closed__1);
v___x_316_ = lean_int_emod(v___x_315_, v_range_314_);
return v___x_316_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedQuarter___closed__3(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_318_ = lean_obj_once(&l_Std_Time_Month_instInhabitedQuarter___closed__2, &l_Std_Time_Month_instInhabitedQuarter___closed__2_once, _init_l_Std_Time_Month_instInhabitedQuarter___closed__2);
v___x_319_ = lean_int_add(v___x_318_, v___x_317_);
return v___x_319_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedQuarter(void){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = lean_obj_once(&l_Std_Time_Month_instInhabitedQuarter___closed__3, &l_Std_Time_Month_instInhabitedQuarter___closed__3_once, _init_l_Std_Time_Month_instInhabitedQuarter___closed__3);
return v___x_320_;
}
}
uint8_t l_Std_Time_Month_instOrdQuarter___aux__1(lean_object* v_x_321_, lean_object* v_y_322_){
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
LEAN_EXPORT void l_Std_Time_Month_instOrdQuarter___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_321_ = stack[0].m_obj;
lean_object* v_y_322_ = stack[1].m_obj;
uint8_t v_res_328_;
v_res_328_ = l_Std_Time_Month_instOrdQuarter___aux__1(v_x_321_, v_y_322_);
stack->m_num = v_res_328_;
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instOrdQuarter___aux__1___boxed(lean_object* v_x_329_, lean_object* v_y_330_){
_start:
{
uint8_t v_res_331_; lean_object* v_r_332_; 
v_res_331_ = l_Std_Time_Month_instOrdQuarter___aux__1(v_x_329_, v_y_330_);
lean_dec(v_y_330_);
lean_dec(v_x_329_);
v_r_332_ = lean_box(v_res_331_);
return v_r_332_;
}
}
static lean_object* _init_l_Std_Time_Month_Quarter_ofMonth___closed__0(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_unsigned_to_nat(3u);
v___x_336_ = lean_nat_to_int(v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l_Std_Time_Month_Quarter_ofMonth___closed__1(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_338_ = lean_int_neg(v___x_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Quarter_ofMonth(lean_object* v_month_339_){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_340_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_341_ = lean_obj_once(&l_Std_Time_Month_Quarter_ofMonth___closed__0, &l_Std_Time_Month_Quarter_ofMonth___closed__0_once, _init_l_Std_Time_Month_Quarter_ofMonth___closed__0);
v___x_342_ = lean_obj_once(&l_Std_Time_Month_Quarter_ofMonth___closed__1, &l_Std_Time_Month_Quarter_ofMonth___closed__1_once, _init_l_Std_Time_Month_Quarter_ofMonth___closed__1);
v___x_343_ = lean_int_add(v_month_339_, v___x_342_);
v___x_344_ = lean_int_ediv(v___x_343_, v___x_341_);
lean_dec(v___x_343_);
v___x_345_ = lean_int_add(v___x_344_, v___x_340_);
lean_dec(v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Quarter_ofMonth___boxed(lean_object* v_month_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Std_Time_Month_Quarter_ofMonth(v_month_346_);
lean_dec(v_month_346_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Offset_ofNat(lean_object* v_data_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = lean_nat_to_int(v_data_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Offset_ofInt(lean_object* v_data_350_){
_start:
{
lean_inc(v_data_350_);
return v_data_350_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Offset_ofInt___boxed(lean_object* v_data_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Std_Time_Month_Offset_ofInt(v_data_351_);
lean_dec(v_data_351_);
return v_res_352_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_january(void){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__4, &l_Std_Time_Month_instInhabitedOrdinal___closed__4_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__4);
return v___x_353_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_february___closed__0(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_unsigned_to_nat(2u);
v___x_355_ = lean_nat_to_int(v___x_354_);
return v___x_355_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_february___closed__1(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_356_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_357_ = lean_obj_once(&l_Std_Time_Month_Ordinal_february___closed__0, &l_Std_Time_Month_Ordinal_february___closed__0_once, _init_l_Std_Time_Month_Ordinal_february___closed__0);
v___x_358_ = lean_int_sub(v___x_357_, v___x_356_);
return v___x_358_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_february___closed__2(void){
_start:
{
lean_object* v_range_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_range_359_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_360_ = lean_obj_once(&l_Std_Time_Month_Ordinal_february___closed__1, &l_Std_Time_Month_Ordinal_february___closed__1_once, _init_l_Std_Time_Month_Ordinal_february___closed__1);
v___x_361_ = lean_int_emod(v___x_360_, v_range_359_);
return v___x_361_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_february___closed__3(void){
_start:
{
lean_object* v_range_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v_range_362_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_363_ = lean_obj_once(&l_Std_Time_Month_Ordinal_february___closed__2, &l_Std_Time_Month_Ordinal_february___closed__2_once, _init_l_Std_Time_Month_Ordinal_february___closed__2);
v___x_364_ = lean_int_add(v___x_363_, v_range_362_);
return v___x_364_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_february___closed__4(void){
_start:
{
lean_object* v_range_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v_range_365_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_366_ = lean_obj_once(&l_Std_Time_Month_Ordinal_february___closed__3, &l_Std_Time_Month_Ordinal_february___closed__3_once, _init_l_Std_Time_Month_Ordinal_february___closed__3);
v___x_367_ = lean_int_emod(v___x_366_, v_range_365_);
return v___x_367_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_february___closed__5(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_368_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_369_ = lean_obj_once(&l_Std_Time_Month_Ordinal_february___closed__4, &l_Std_Time_Month_Ordinal_february___closed__4_once, _init_l_Std_Time_Month_Ordinal_february___closed__4);
v___x_370_ = lean_int_add(v___x_369_, v___x_368_);
return v___x_370_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_february(void){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = lean_obj_once(&l_Std_Time_Month_Ordinal_february___closed__5, &l_Std_Time_Month_Ordinal_february___closed__5_once, _init_l_Std_Time_Month_Ordinal_february___closed__5);
return v___x_371_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_march___closed__0(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_372_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_373_ = lean_obj_once(&l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0, &l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0);
v___x_374_ = lean_int_sub(v___x_373_, v___x_372_);
return v___x_374_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_march___closed__1(void){
_start:
{
lean_object* v_range_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v_range_375_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_376_ = lean_obj_once(&l_Std_Time_Month_Ordinal_march___closed__0, &l_Std_Time_Month_Ordinal_march___closed__0_once, _init_l_Std_Time_Month_Ordinal_march___closed__0);
v___x_377_ = lean_int_emod(v___x_376_, v_range_375_);
return v___x_377_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_march___closed__2(void){
_start:
{
lean_object* v_range_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_range_378_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_379_ = lean_obj_once(&l_Std_Time_Month_Ordinal_march___closed__1, &l_Std_Time_Month_Ordinal_march___closed__1_once, _init_l_Std_Time_Month_Ordinal_march___closed__1);
v___x_380_ = lean_int_add(v___x_379_, v_range_378_);
return v___x_380_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_march___closed__3(void){
_start:
{
lean_object* v_range_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v_range_381_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_382_ = lean_obj_once(&l_Std_Time_Month_Ordinal_march___closed__2, &l_Std_Time_Month_Ordinal_march___closed__2_once, _init_l_Std_Time_Month_Ordinal_march___closed__2);
v___x_383_ = lean_int_emod(v___x_382_, v_range_381_);
return v___x_383_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_march___closed__4(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_384_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_385_ = lean_obj_once(&l_Std_Time_Month_Ordinal_march___closed__3, &l_Std_Time_Month_Ordinal_march___closed__3_once, _init_l_Std_Time_Month_Ordinal_march___closed__3);
v___x_386_ = lean_int_add(v___x_385_, v___x_384_);
return v___x_386_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_march(void){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = lean_obj_once(&l_Std_Time_Month_Ordinal_march___closed__4, &l_Std_Time_Month_Ordinal_march___closed__4_once, _init_l_Std_Time_Month_Ordinal_march___closed__4);
return v___x_387_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_april___closed__0(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = lean_unsigned_to_nat(4u);
v___x_389_ = lean_nat_to_int(v___x_388_);
return v___x_389_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_april___closed__1(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_390_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_391_ = lean_obj_once(&l_Std_Time_Month_Ordinal_april___closed__0, &l_Std_Time_Month_Ordinal_april___closed__0_once, _init_l_Std_Time_Month_Ordinal_april___closed__0);
v___x_392_ = lean_int_sub(v___x_391_, v___x_390_);
return v___x_392_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_april___closed__2(void){
_start:
{
lean_object* v_range_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v_range_393_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_394_ = lean_obj_once(&l_Std_Time_Month_Ordinal_april___closed__1, &l_Std_Time_Month_Ordinal_april___closed__1_once, _init_l_Std_Time_Month_Ordinal_april___closed__1);
v___x_395_ = lean_int_emod(v___x_394_, v_range_393_);
return v___x_395_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_april___closed__3(void){
_start:
{
lean_object* v_range_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_range_396_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_397_ = lean_obj_once(&l_Std_Time_Month_Ordinal_april___closed__2, &l_Std_Time_Month_Ordinal_april___closed__2_once, _init_l_Std_Time_Month_Ordinal_april___closed__2);
v___x_398_ = lean_int_add(v___x_397_, v_range_396_);
return v___x_398_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_april___closed__4(void){
_start:
{
lean_object* v_range_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v_range_399_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_400_ = lean_obj_once(&l_Std_Time_Month_Ordinal_april___closed__3, &l_Std_Time_Month_Ordinal_april___closed__3_once, _init_l_Std_Time_Month_Ordinal_april___closed__3);
v___x_401_ = lean_int_emod(v___x_400_, v_range_399_);
return v___x_401_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_april___closed__5(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_402_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_403_ = lean_obj_once(&l_Std_Time_Month_Ordinal_april___closed__4, &l_Std_Time_Month_Ordinal_april___closed__4_once, _init_l_Std_Time_Month_Ordinal_april___closed__4);
v___x_404_ = lean_int_add(v___x_403_, v___x_402_);
return v___x_404_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_april(void){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = lean_obj_once(&l_Std_Time_Month_Ordinal_april___closed__5, &l_Std_Time_Month_Ordinal_april___closed__5_once, _init_l_Std_Time_Month_Ordinal_april___closed__5);
return v___x_405_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_may___closed__0(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_unsigned_to_nat(5u);
v___x_407_ = lean_nat_to_int(v___x_406_);
return v___x_407_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_may___closed__1(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_408_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_409_ = lean_obj_once(&l_Std_Time_Month_Ordinal_may___closed__0, &l_Std_Time_Month_Ordinal_may___closed__0_once, _init_l_Std_Time_Month_Ordinal_may___closed__0);
v___x_410_ = lean_int_sub(v___x_409_, v___x_408_);
return v___x_410_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_may___closed__2(void){
_start:
{
lean_object* v_range_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v_range_411_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_412_ = lean_obj_once(&l_Std_Time_Month_Ordinal_may___closed__1, &l_Std_Time_Month_Ordinal_may___closed__1_once, _init_l_Std_Time_Month_Ordinal_may___closed__1);
v___x_413_ = lean_int_emod(v___x_412_, v_range_411_);
return v___x_413_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_may___closed__3(void){
_start:
{
lean_object* v_range_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v_range_414_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_415_ = lean_obj_once(&l_Std_Time_Month_Ordinal_may___closed__2, &l_Std_Time_Month_Ordinal_may___closed__2_once, _init_l_Std_Time_Month_Ordinal_may___closed__2);
v___x_416_ = lean_int_add(v___x_415_, v_range_414_);
return v___x_416_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_may___closed__4(void){
_start:
{
lean_object* v_range_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v_range_417_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_418_ = lean_obj_once(&l_Std_Time_Month_Ordinal_may___closed__3, &l_Std_Time_Month_Ordinal_may___closed__3_once, _init_l_Std_Time_Month_Ordinal_may___closed__3);
v___x_419_ = lean_int_emod(v___x_418_, v_range_417_);
return v___x_419_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_may___closed__5(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_421_ = lean_obj_once(&l_Std_Time_Month_Ordinal_may___closed__4, &l_Std_Time_Month_Ordinal_may___closed__4_once, _init_l_Std_Time_Month_Ordinal_may___closed__4);
v___x_422_ = lean_int_add(v___x_421_, v___x_420_);
return v___x_422_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_may(void){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = lean_obj_once(&l_Std_Time_Month_Ordinal_may___closed__5, &l_Std_Time_Month_Ordinal_may___closed__5_once, _init_l_Std_Time_Month_Ordinal_may___closed__5);
return v___x_423_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_june___closed__0(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_unsigned_to_nat(6u);
v___x_425_ = lean_nat_to_int(v___x_424_);
return v___x_425_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_june___closed__1(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_426_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_427_ = lean_obj_once(&l_Std_Time_Month_Ordinal_june___closed__0, &l_Std_Time_Month_Ordinal_june___closed__0_once, _init_l_Std_Time_Month_Ordinal_june___closed__0);
v___x_428_ = lean_int_sub(v___x_427_, v___x_426_);
return v___x_428_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_june___closed__2(void){
_start:
{
lean_object* v_range_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v_range_429_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_430_ = lean_obj_once(&l_Std_Time_Month_Ordinal_june___closed__1, &l_Std_Time_Month_Ordinal_june___closed__1_once, _init_l_Std_Time_Month_Ordinal_june___closed__1);
v___x_431_ = lean_int_emod(v___x_430_, v_range_429_);
return v___x_431_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_june___closed__3(void){
_start:
{
lean_object* v_range_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v_range_432_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_433_ = lean_obj_once(&l_Std_Time_Month_Ordinal_june___closed__2, &l_Std_Time_Month_Ordinal_june___closed__2_once, _init_l_Std_Time_Month_Ordinal_june___closed__2);
v___x_434_ = lean_int_add(v___x_433_, v_range_432_);
return v___x_434_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_june___closed__4(void){
_start:
{
lean_object* v_range_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v_range_435_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_436_ = lean_obj_once(&l_Std_Time_Month_Ordinal_june___closed__3, &l_Std_Time_Month_Ordinal_june___closed__3_once, _init_l_Std_Time_Month_Ordinal_june___closed__3);
v___x_437_ = lean_int_emod(v___x_436_, v_range_435_);
return v___x_437_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_june___closed__5(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_438_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_439_ = lean_obj_once(&l_Std_Time_Month_Ordinal_june___closed__4, &l_Std_Time_Month_Ordinal_june___closed__4_once, _init_l_Std_Time_Month_Ordinal_june___closed__4);
v___x_440_ = lean_int_add(v___x_439_, v___x_438_);
return v___x_440_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_june(void){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = lean_obj_once(&l_Std_Time_Month_Ordinal_june___closed__5, &l_Std_Time_Month_Ordinal_june___closed__5_once, _init_l_Std_Time_Month_Ordinal_june___closed__5);
return v___x_441_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_july___closed__0(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_unsigned_to_nat(7u);
v___x_443_ = lean_nat_to_int(v___x_442_);
return v___x_443_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_july___closed__1(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_444_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_445_ = lean_obj_once(&l_Std_Time_Month_Ordinal_july___closed__0, &l_Std_Time_Month_Ordinal_july___closed__0_once, _init_l_Std_Time_Month_Ordinal_july___closed__0);
v___x_446_ = lean_int_sub(v___x_445_, v___x_444_);
return v___x_446_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_july___closed__2(void){
_start:
{
lean_object* v_range_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v_range_447_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_448_ = lean_obj_once(&l_Std_Time_Month_Ordinal_july___closed__1, &l_Std_Time_Month_Ordinal_july___closed__1_once, _init_l_Std_Time_Month_Ordinal_july___closed__1);
v___x_449_ = lean_int_emod(v___x_448_, v_range_447_);
return v___x_449_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_july___closed__3(void){
_start:
{
lean_object* v_range_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v_range_450_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_451_ = lean_obj_once(&l_Std_Time_Month_Ordinal_july___closed__2, &l_Std_Time_Month_Ordinal_july___closed__2_once, _init_l_Std_Time_Month_Ordinal_july___closed__2);
v___x_452_ = lean_int_add(v___x_451_, v_range_450_);
return v___x_452_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_july___closed__4(void){
_start:
{
lean_object* v_range_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v_range_453_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_454_ = lean_obj_once(&l_Std_Time_Month_Ordinal_july___closed__3, &l_Std_Time_Month_Ordinal_july___closed__3_once, _init_l_Std_Time_Month_Ordinal_july___closed__3);
v___x_455_ = lean_int_emod(v___x_454_, v_range_453_);
return v___x_455_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_july___closed__5(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_456_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_457_ = lean_obj_once(&l_Std_Time_Month_Ordinal_july___closed__4, &l_Std_Time_Month_Ordinal_july___closed__4_once, _init_l_Std_Time_Month_Ordinal_july___closed__4);
v___x_458_ = lean_int_add(v___x_457_, v___x_456_);
return v___x_458_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_july(void){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = lean_obj_once(&l_Std_Time_Month_Ordinal_july___closed__5, &l_Std_Time_Month_Ordinal_july___closed__5_once, _init_l_Std_Time_Month_Ordinal_july___closed__5);
return v___x_459_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_august___closed__0(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = lean_unsigned_to_nat(8u);
v___x_461_ = lean_nat_to_int(v___x_460_);
return v___x_461_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_august___closed__1(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_462_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_463_ = lean_obj_once(&l_Std_Time_Month_Ordinal_august___closed__0, &l_Std_Time_Month_Ordinal_august___closed__0_once, _init_l_Std_Time_Month_Ordinal_august___closed__0);
v___x_464_ = lean_int_sub(v___x_463_, v___x_462_);
return v___x_464_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_august___closed__2(void){
_start:
{
lean_object* v_range_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v_range_465_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_466_ = lean_obj_once(&l_Std_Time_Month_Ordinal_august___closed__1, &l_Std_Time_Month_Ordinal_august___closed__1_once, _init_l_Std_Time_Month_Ordinal_august___closed__1);
v___x_467_ = lean_int_emod(v___x_466_, v_range_465_);
return v___x_467_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_august___closed__3(void){
_start:
{
lean_object* v_range_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v_range_468_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_469_ = lean_obj_once(&l_Std_Time_Month_Ordinal_august___closed__2, &l_Std_Time_Month_Ordinal_august___closed__2_once, _init_l_Std_Time_Month_Ordinal_august___closed__2);
v___x_470_ = lean_int_add(v___x_469_, v_range_468_);
return v___x_470_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_august___closed__4(void){
_start:
{
lean_object* v_range_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v_range_471_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_472_ = lean_obj_once(&l_Std_Time_Month_Ordinal_august___closed__3, &l_Std_Time_Month_Ordinal_august___closed__3_once, _init_l_Std_Time_Month_Ordinal_august___closed__3);
v___x_473_ = lean_int_emod(v___x_472_, v_range_471_);
return v___x_473_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_august___closed__5(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_474_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_475_ = lean_obj_once(&l_Std_Time_Month_Ordinal_august___closed__4, &l_Std_Time_Month_Ordinal_august___closed__4_once, _init_l_Std_Time_Month_Ordinal_august___closed__4);
v___x_476_ = lean_int_add(v___x_475_, v___x_474_);
return v___x_476_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_august(void){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = lean_obj_once(&l_Std_Time_Month_Ordinal_august___closed__5, &l_Std_Time_Month_Ordinal_august___closed__5_once, _init_l_Std_Time_Month_Ordinal_august___closed__5);
return v___x_477_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_september___closed__0(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = lean_unsigned_to_nat(9u);
v___x_479_ = lean_nat_to_int(v___x_478_);
return v___x_479_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_september___closed__1(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_480_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_481_ = lean_obj_once(&l_Std_Time_Month_Ordinal_september___closed__0, &l_Std_Time_Month_Ordinal_september___closed__0_once, _init_l_Std_Time_Month_Ordinal_september___closed__0);
v___x_482_ = lean_int_sub(v___x_481_, v___x_480_);
return v___x_482_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_september___closed__2(void){
_start:
{
lean_object* v_range_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v_range_483_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_484_ = lean_obj_once(&l_Std_Time_Month_Ordinal_september___closed__1, &l_Std_Time_Month_Ordinal_september___closed__1_once, _init_l_Std_Time_Month_Ordinal_september___closed__1);
v___x_485_ = lean_int_emod(v___x_484_, v_range_483_);
return v___x_485_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_september___closed__3(void){
_start:
{
lean_object* v_range_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v_range_486_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_487_ = lean_obj_once(&l_Std_Time_Month_Ordinal_september___closed__2, &l_Std_Time_Month_Ordinal_september___closed__2_once, _init_l_Std_Time_Month_Ordinal_september___closed__2);
v___x_488_ = lean_int_add(v___x_487_, v_range_486_);
return v___x_488_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_september___closed__4(void){
_start:
{
lean_object* v_range_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v_range_489_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_490_ = lean_obj_once(&l_Std_Time_Month_Ordinal_september___closed__3, &l_Std_Time_Month_Ordinal_september___closed__3_once, _init_l_Std_Time_Month_Ordinal_september___closed__3);
v___x_491_ = lean_int_emod(v___x_490_, v_range_489_);
return v___x_491_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_september___closed__5(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_492_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_493_ = lean_obj_once(&l_Std_Time_Month_Ordinal_september___closed__4, &l_Std_Time_Month_Ordinal_september___closed__4_once, _init_l_Std_Time_Month_Ordinal_september___closed__4);
v___x_494_ = lean_int_add(v___x_493_, v___x_492_);
return v___x_494_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_september(void){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = lean_obj_once(&l_Std_Time_Month_Ordinal_september___closed__5, &l_Std_Time_Month_Ordinal_september___closed__5_once, _init_l_Std_Time_Month_Ordinal_september___closed__5);
return v___x_495_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_october___closed__0(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_unsigned_to_nat(10u);
v___x_497_ = lean_nat_to_int(v___x_496_);
return v___x_497_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_october___closed__1(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_498_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_499_ = lean_obj_once(&l_Std_Time_Month_Ordinal_october___closed__0, &l_Std_Time_Month_Ordinal_october___closed__0_once, _init_l_Std_Time_Month_Ordinal_october___closed__0);
v___x_500_ = lean_int_sub(v___x_499_, v___x_498_);
return v___x_500_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_october___closed__2(void){
_start:
{
lean_object* v_range_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v_range_501_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_502_ = lean_obj_once(&l_Std_Time_Month_Ordinal_october___closed__1, &l_Std_Time_Month_Ordinal_october___closed__1_once, _init_l_Std_Time_Month_Ordinal_october___closed__1);
v___x_503_ = lean_int_emod(v___x_502_, v_range_501_);
return v___x_503_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_october___closed__3(void){
_start:
{
lean_object* v_range_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v_range_504_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_505_ = lean_obj_once(&l_Std_Time_Month_Ordinal_october___closed__2, &l_Std_Time_Month_Ordinal_october___closed__2_once, _init_l_Std_Time_Month_Ordinal_october___closed__2);
v___x_506_ = lean_int_add(v___x_505_, v_range_504_);
return v___x_506_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_october___closed__4(void){
_start:
{
lean_object* v_range_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v_range_507_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_508_ = lean_obj_once(&l_Std_Time_Month_Ordinal_october___closed__3, &l_Std_Time_Month_Ordinal_october___closed__3_once, _init_l_Std_Time_Month_Ordinal_october___closed__3);
v___x_509_ = lean_int_emod(v___x_508_, v_range_507_);
return v___x_509_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_october___closed__5(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_510_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_511_ = lean_obj_once(&l_Std_Time_Month_Ordinal_october___closed__4, &l_Std_Time_Month_Ordinal_october___closed__4_once, _init_l_Std_Time_Month_Ordinal_october___closed__4);
v___x_512_ = lean_int_add(v___x_511_, v___x_510_);
return v___x_512_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_october(void){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = lean_obj_once(&l_Std_Time_Month_Ordinal_october___closed__5, &l_Std_Time_Month_Ordinal_october___closed__5_once, _init_l_Std_Time_Month_Ordinal_october___closed__5);
return v___x_513_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_november___closed__0(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_514_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_515_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1);
v___x_516_ = lean_int_sub(v___x_515_, v___x_514_);
return v___x_516_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_november___closed__1(void){
_start:
{
lean_object* v_range_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v_range_517_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_518_ = lean_obj_once(&l_Std_Time_Month_Ordinal_november___closed__0, &l_Std_Time_Month_Ordinal_november___closed__0_once, _init_l_Std_Time_Month_Ordinal_november___closed__0);
v___x_519_ = lean_int_emod(v___x_518_, v_range_517_);
return v___x_519_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_november___closed__2(void){
_start:
{
lean_object* v_range_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v_range_520_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_521_ = lean_obj_once(&l_Std_Time_Month_Ordinal_november___closed__1, &l_Std_Time_Month_Ordinal_november___closed__1_once, _init_l_Std_Time_Month_Ordinal_november___closed__1);
v___x_522_ = lean_int_add(v___x_521_, v_range_520_);
return v___x_522_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_november___closed__3(void){
_start:
{
lean_object* v_range_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v_range_523_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_524_ = lean_obj_once(&l_Std_Time_Month_Ordinal_november___closed__2, &l_Std_Time_Month_Ordinal_november___closed__2_once, _init_l_Std_Time_Month_Ordinal_november___closed__2);
v___x_525_ = lean_int_emod(v___x_524_, v_range_523_);
return v___x_525_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_november___closed__4(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_526_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_527_ = lean_obj_once(&l_Std_Time_Month_Ordinal_november___closed__3, &l_Std_Time_Month_Ordinal_november___closed__3_once, _init_l_Std_Time_Month_Ordinal_november___closed__3);
v___x_528_ = lean_int_add(v___x_527_, v___x_526_);
return v___x_528_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_november(void){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = lean_obj_once(&l_Std_Time_Month_Ordinal_november___closed__4, &l_Std_Time_Month_Ordinal_november___closed__4_once, _init_l_Std_Time_Month_Ordinal_november___closed__4);
return v___x_529_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_december___closed__0(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_unsigned_to_nat(12u);
v___x_531_ = lean_nat_to_int(v___x_530_);
return v___x_531_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_december___closed__1(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_532_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_533_ = lean_obj_once(&l_Std_Time_Month_Ordinal_december___closed__0, &l_Std_Time_Month_Ordinal_december___closed__0_once, _init_l_Std_Time_Month_Ordinal_december___closed__0);
v___x_534_ = lean_int_sub(v___x_533_, v___x_532_);
return v___x_534_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_december___closed__2(void){
_start:
{
lean_object* v_range_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v_range_535_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_536_ = lean_obj_once(&l_Std_Time_Month_Ordinal_december___closed__1, &l_Std_Time_Month_Ordinal_december___closed__1_once, _init_l_Std_Time_Month_Ordinal_december___closed__1);
v___x_537_ = lean_int_emod(v___x_536_, v_range_535_);
return v___x_537_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_december___closed__3(void){
_start:
{
lean_object* v_range_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v_range_538_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_539_ = lean_obj_once(&l_Std_Time_Month_Ordinal_december___closed__2, &l_Std_Time_Month_Ordinal_december___closed__2_once, _init_l_Std_Time_Month_Ordinal_december___closed__2);
v___x_540_ = lean_int_add(v___x_539_, v_range_538_);
return v___x_540_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_december___closed__4(void){
_start:
{
lean_object* v_range_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v_range_541_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4);
v___x_542_ = lean_obj_once(&l_Std_Time_Month_Ordinal_december___closed__3, &l_Std_Time_Month_Ordinal_december___closed__3_once, _init_l_Std_Time_Month_Ordinal_december___closed__3);
v___x_543_ = lean_int_emod(v___x_542_, v_range_541_);
return v___x_543_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_december___closed__5(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_544_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_545_ = lean_obj_once(&l_Std_Time_Month_Ordinal_december___closed__4, &l_Std_Time_Month_Ordinal_december___closed__4_once, _init_l_Std_Time_Month_Ordinal_december___closed__4);
v___x_546_ = lean_int_add(v___x_545_, v___x_544_);
return v___x_546_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_december(void){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = lean_obj_once(&l_Std_Time_Month_Ordinal_december___closed__5, &l_Std_Time_Month_Ordinal_december___closed__5_once, _init_l_Std_Time_Month_Ordinal_december___closed__5);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toOffset(lean_object* v_month_548_){
_start:
{
lean_inc(v_month_548_);
return v_month_548_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toOffset___boxed(lean_object* v_month_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Std_Time_Month_Ordinal_toOffset(v_month_549_);
lean_dec(v_month_549_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_ofInt___redArg(lean_object* v_data_551_){
_start:
{
lean_inc(v_data_551_);
return v_data_551_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_ofInt___redArg___boxed(lean_object* v_data_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Std_Time_Month_Ordinal_ofInt___redArg(v_data_552_);
lean_dec(v_data_552_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_ofInt(lean_object* v_data_554_, lean_object* v_h_555_){
_start:
{
lean_inc(v_data_554_);
return v_data_554_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_ofInt___boxed(lean_object* v_data_556_, lean_object* v_h_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Std_Time_Month_Ordinal_ofInt(v_data_556_, v_h_557_);
lean_dec(v_data_556_);
return v_res_558_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__12(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__10));
v___x_586_ = l_Lean_mkAtom(v___x_585_);
return v___x_586_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__13(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_587_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__12, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__12_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__12);
v___x_588_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5));
v___x_589_ = lean_array_push(v___x_588_, v___x_587_);
return v___x_589_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__17(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_600_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__16));
v___x_601_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5));
v___x_602_ = lean_array_push(v___x_601_, v___x_600_);
return v___x_602_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__18(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_603_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__17, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__17_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__17);
v___x_604_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15));
v___x_605_ = lean_box(2);
v___x_606_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
lean_ctor_set(v___x_606_, 1, v___x_604_);
lean_ctor_set(v___x_606_, 2, v___x_603_);
return v___x_606_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__19(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_607_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__18, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__18_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__18);
v___x_608_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__13, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__13_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__13);
v___x_609_ = lean_array_push(v___x_608_, v___x_607_);
return v___x_609_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__20(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_610_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__19, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__19_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__19);
v___x_611_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11));
v___x_612_ = lean_box(2);
v___x_613_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
lean_ctor_set(v___x_613_, 1, v___x_611_);
lean_ctor_set(v___x_613_, 2, v___x_610_);
return v___x_613_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__21(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_614_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__20, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__20_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__20);
v___x_615_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5));
v___x_616_ = lean_array_push(v___x_615_, v___x_614_);
return v___x_616_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__22(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_617_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__21, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__21_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__21);
v___x_618_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__9));
v___x_619_ = lean_box(2);
v___x_620_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
lean_ctor_set(v___x_620_, 1, v___x_618_);
lean_ctor_set(v___x_620_, 2, v___x_617_);
return v___x_620_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__23(void){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_621_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__22, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__22_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__22);
v___x_622_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5));
v___x_623_ = lean_array_push(v___x_622_, v___x_621_);
return v___x_623_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__24(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_624_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__23, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__23_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__23);
v___x_625_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7));
v___x_626_ = lean_box(2);
v___x_627_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v___x_625_);
lean_ctor_set(v___x_627_, 2, v___x_624_);
return v___x_627_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__25(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_628_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__24, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__24_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__24);
v___x_629_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5));
v___x_630_ = lean_array_push(v___x_629_, v___x_628_);
return v___x_630_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__26(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_631_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__25, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__25_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__25);
v___x_632_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4));
v___x_633_ = lean_box(2);
v___x_634_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
lean_ctor_set(v___x_634_, 1, v___x_632_);
lean_ctor_set(v___x_634_, 2, v___x_631_);
return v___x_634_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1(void){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__26, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__26_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__26);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_ofNat___redArg(lean_object* v_data_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = lean_nat_to_int(v_data_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_ofNat(lean_object* v_data_638_, lean_object* v_h_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = lean_nat_to_int(v_data_638_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toNat(lean_object* v_month_641_){
_start:
{
lean_object* v_intZero_642_; uint8_t v_isNeg_643_; lean_object* v_a_644_; 
v_intZero_642_ = lean_obj_once(&l_Std_Time_Month_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0);
v_isNeg_643_ = lean_int_dec_lt(v_month_641_, v_intZero_642_);
v_a_644_ = lean_nat_abs(v_month_641_);
return v_a_644_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toNat___boxed(lean_object* v_month_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Std_Time_Month_Ordinal_toNat(v_month_645_);
lean_dec(v_month_645_);
return v_res_646_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofFin___closed__0(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_unsigned_to_nat(1u);
v___x_648_ = lean_nat_to_int(v___x_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_ofFin(lean_object* v_data_649_){
_start:
{
lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_650_ = lean_unsigned_to_nat(1u);
v___x_651_ = lean_nat_dec_le(v___x_650_, v_data_649_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; 
lean_dec(v_data_649_);
v___x_652_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofFin___closed__0, &l_Std_Time_Month_Ordinal_ofFin___closed__0_once, _init_l_Std_Time_Month_Ordinal_ofFin___closed__0);
return v___x_652_;
}
else
{
lean_object* v___x_653_; 
v___x_653_ = lean_nat_to_int(v_data_649_);
return v___x_653_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Month_Ordinal_toSeconds_spec__1(lean_object* v_a_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = lean_nat_to_int(v_a_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Std_Time_Month_Ordinal_toSeconds_spec__2(lean_object* v_a_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Rat_ofInt(v_a_656_);
return v___x_657_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__0(void){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Std_Time_Internal_instInhabitedUnitVal_default___redArg();
return v___x_658_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__1(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_unsigned_to_nat(31u);
v___x_660_ = lean_nat_to_int(v___x_659_);
return v___x_660_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__2(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = lean_unsigned_to_nat(59u);
v___x_662_ = lean_nat_to_int(v___x_661_);
return v___x_662_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__3(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = lean_unsigned_to_nat(90u);
v___x_664_ = lean_nat_to_int(v___x_663_);
return v___x_664_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__4(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_unsigned_to_nat(120u);
v___x_666_ = lean_nat_to_int(v___x_665_);
return v___x_666_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__5(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_unsigned_to_nat(151u);
v___x_668_ = lean_nat_to_int(v___x_667_);
return v___x_668_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__6(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = lean_unsigned_to_nat(181u);
v___x_670_ = lean_nat_to_int(v___x_669_);
return v___x_670_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__7(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_unsigned_to_nat(212u);
v___x_672_ = lean_nat_to_int(v___x_671_);
return v___x_672_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__8(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_unsigned_to_nat(243u);
v___x_674_ = lean_nat_to_int(v___x_673_);
return v___x_674_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__9(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = lean_unsigned_to_nat(273u);
v___x_676_ = lean_nat_to_int(v___x_675_);
return v___x_676_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__10(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = lean_unsigned_to_nat(304u);
v___x_678_ = lean_nat_to_int(v___x_677_);
return v___x_678_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__11(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = lean_unsigned_to_nat(334u);
v___x_680_ = lean_nat_to_int(v___x_679_);
return v___x_680_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__12(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v_intZero_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v_daysAcc_706_; 
v___x_681_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__11, &l_Std_Time_Month_Ordinal_toSeconds___closed__11_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__11);
v___x_682_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__10, &l_Std_Time_Month_Ordinal_toSeconds___closed__10_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__10);
v___x_683_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__9, &l_Std_Time_Month_Ordinal_toSeconds___closed__9_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__9);
v___x_684_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__8, &l_Std_Time_Month_Ordinal_toSeconds___closed__8_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__8);
v___x_685_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__7, &l_Std_Time_Month_Ordinal_toSeconds___closed__7_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__7);
v___x_686_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__6, &l_Std_Time_Month_Ordinal_toSeconds___closed__6_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__6);
v___x_687_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__5, &l_Std_Time_Month_Ordinal_toSeconds___closed__5_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__5);
v___x_688_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__4, &l_Std_Time_Month_Ordinal_toSeconds___closed__4_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__4);
v___x_689_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__3, &l_Std_Time_Month_Ordinal_toSeconds___closed__3_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__3);
v___x_690_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__2, &l_Std_Time_Month_Ordinal_toSeconds___closed__2_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__2);
v___x_691_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__1, &l_Std_Time_Month_Ordinal_toSeconds___closed__1_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__1);
v_intZero_692_ = lean_obj_once(&l_Std_Time_Month_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0);
v___x_693_ = lean_unsigned_to_nat(12u);
v___x_694_ = lean_mk_empty_array_with_capacity(v___x_693_);
v___x_695_ = lean_array_push(v___x_694_, v_intZero_692_);
v___x_696_ = lean_array_push(v___x_695_, v___x_691_);
v___x_697_ = lean_array_push(v___x_696_, v___x_690_);
v___x_698_ = lean_array_push(v___x_697_, v___x_689_);
v___x_699_ = lean_array_push(v___x_698_, v___x_688_);
v___x_700_ = lean_array_push(v___x_699_, v___x_687_);
v___x_701_ = lean_array_push(v___x_700_, v___x_686_);
v___x_702_ = lean_array_push(v___x_701_, v___x_685_);
v___x_703_ = lean_array_push(v___x_702_, v___x_684_);
v___x_704_ = lean_array_push(v___x_703_, v___x_683_);
v___x_705_ = lean_array_push(v___x_704_, v___x_682_);
v_daysAcc_706_ = lean_array_push(v___x_705_, v___x_681_);
return v_daysAcc_706_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__13(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_unsigned_to_nat(86400u);
v___x_708_ = lean_nat_to_int(v___x_707_);
return v___x_708_;
}
}
lean_object* l_Std_Time_Month_Ordinal_toSeconds(uint8_t v_leap_709_, lean_object* v_month_710_){
_start:
{
lean_object* v_intZero_711_; uint8_t v_isNeg_712_; lean_object* v___x_713_; lean_object* v_a_714_; lean_object* v_daysAcc_715_; lean_object* v_days_716_; lean_object* v___x_717_; lean_object* v_time_718_; 
v_intZero_711_ = lean_obj_once(&l_Std_Time_Month_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0);
v_isNeg_712_ = lean_int_dec_lt(v_month_710_, v_intZero_711_);
v___x_713_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__0, &l_Std_Time_Month_Ordinal_toSeconds___closed__0_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__0);
v_a_714_ = lean_nat_abs(v_month_710_);
v_daysAcc_715_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__12, &l_Std_Time_Month_Ordinal_toSeconds___closed__12_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__12);
v_days_716_ = lean_array_get_borrowed(v___x_713_, v_daysAcc_715_, v_a_714_);
v___x_717_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__13, &l_Std_Time_Month_Ordinal_toSeconds___closed__13_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__13);
v_time_718_ = lean_int_mul(v_days_716_, v___x_717_);
if (v_leap_709_ == 0)
{
lean_dec(v_a_714_);
return v_time_718_;
}
else
{
lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_719_ = lean_unsigned_to_nat(2u);
v___x_720_ = lean_nat_dec_le(v___x_719_, v_a_714_);
lean_dec(v_a_714_);
if (v___x_720_ == 0)
{
return v_time_718_;
}
else
{
lean_object* v___x_721_; 
v___x_721_ = lean_int_add(v_time_718_, v___x_717_);
lean_dec(v_time_718_);
return v___x_721_;
}
}
}
}
LEAN_EXPORT void l_Std_Time_Month_Ordinal_toSeconds_0interp(lean_interpreter_value* stack)
{
uint8_t v_leap_709_ = stack[0].m_num;
lean_object* v_month_710_ = stack[1].m_obj;
lean_object* v_res_722_;
v_res_722_ = l_Std_Time_Month_Ordinal_toSeconds(v_leap_709_, v_month_710_);
stack->m_obj
 = v_res_722_;
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toSeconds___boxed(lean_object* v_leap_723_, lean_object* v_month_724_){
_start:
{
uint8_t v_leap_boxed_725_; lean_object* v_res_726_; 
v_leap_boxed_725_ = lean_unbox(v_leap_723_);
v_res_726_ = l_Std_Time_Month_Ordinal_toSeconds(v_leap_boxed_725_, v_month_724_);
lean_dec(v_month_724_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Month_Ordinal_toSeconds_spec__0(lean_object* v_a_727_){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = lean_nat_to_int(v_a_727_);
v___x_729_ = l_Rat_ofInt(v___x_728_);
return v___x_729_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toMinutes___closed__0(void){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = lean_unsigned_to_nat(60u);
v___x_731_ = lean_nat_to_int(v___x_730_);
return v___x_731_;
}
}
lean_object* l_Std_Time_Month_Ordinal_toMinutes(uint8_t v_leap_732_, lean_object* v_month_733_){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_734_ = l_Std_Time_Month_Ordinal_toSeconds(v_leap_732_, v_month_733_);
v___x_735_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toMinutes___closed__0, &l_Std_Time_Month_Ordinal_toMinutes___closed__0_once, _init_l_Std_Time_Month_Ordinal_toMinutes___closed__0);
v___x_736_ = lean_int_div(v___x_734_, v___x_735_);
lean_dec(v___x_734_);
return v___x_736_;
}
}
LEAN_EXPORT void l_Std_Time_Month_Ordinal_toMinutes_0interp(lean_interpreter_value* stack)
{
uint8_t v_leap_732_ = stack[0].m_num;
lean_object* v_month_733_ = stack[1].m_obj;
lean_object* v_res_737_;
v_res_737_ = l_Std_Time_Month_Ordinal_toMinutes(v_leap_732_, v_month_733_);
stack->m_obj
 = v_res_737_;
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toMinutes___boxed(lean_object* v_leap_738_, lean_object* v_month_739_){
_start:
{
uint8_t v_leap_boxed_740_; lean_object* v_res_741_; 
v_leap_boxed_740_ = lean_unbox(v_leap_738_);
v_res_741_ = l_Std_Time_Month_Ordinal_toMinutes(v_leap_boxed_740_, v_month_739_);
lean_dec(v_month_739_);
return v_res_741_;
}
}
lean_object* l_Std_Time_Month_Ordinal_toHours(uint8_t v_leap_742_, lean_object* v_month_743_){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_744_ = l_Std_Time_Month_Ordinal_toSeconds(v_leap_742_, v_month_743_);
v___x_745_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toMinutes___closed__0, &l_Std_Time_Month_Ordinal_toMinutes___closed__0_once, _init_l_Std_Time_Month_Ordinal_toMinutes___closed__0);
v___x_746_ = lean_int_div(v___x_744_, v___x_745_);
lean_dec(v___x_744_);
v___x_747_ = lean_int_div(v___x_746_, v___x_745_);
lean_dec(v___x_746_);
return v___x_747_;
}
}
LEAN_EXPORT void l_Std_Time_Month_Ordinal_toHours_0interp(lean_interpreter_value* stack)
{
uint8_t v_leap_742_ = stack[0].m_num;
lean_object* v_month_743_ = stack[1].m_obj;
lean_object* v_res_748_;
v_res_748_ = l_Std_Time_Month_Ordinal_toHours(v_leap_742_, v_month_743_);
stack->m_obj
 = v_res_748_;
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toHours___boxed(lean_object* v_leap_749_, lean_object* v_month_750_){
_start:
{
uint8_t v_leap_boxed_751_; lean_object* v_res_752_; 
v_leap_boxed_751_ = lean_unbox(v_leap_749_);
v_res_752_ = l_Std_Time_Month_Ordinal_toHours(v_leap_boxed_751_, v_month_750_);
lean_dec(v_month_750_);
return v_res_752_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toDays___closed__0(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = lean_unsigned_to_nat(1u);
v___x_754_ = l_Rat_instNatCast___lam__0(v___x_753_);
return v___x_754_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toDays___closed__1(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_unsigned_to_nat(86400u);
v___x_756_ = l_Rat_instNatCast___lam__0(v___x_755_);
return v___x_756_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toDays___closed__2(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v_ratio_759_; 
v___x_757_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toDays___closed__1, &l_Std_Time_Month_Ordinal_toDays___closed__1_once, _init_l_Std_Time_Month_Ordinal_toDays___closed__1);
v___x_758_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toDays___closed__0, &l_Std_Time_Month_Ordinal_toDays___closed__0_once, _init_l_Std_Time_Month_Ordinal_toDays___closed__0);
v_ratio_759_ = l_Rat_div(v___x_758_, v___x_757_);
return v_ratio_759_;
}
}
lean_object* l_Std_Time_Month_Ordinal_toDays(uint8_t v_leap_760_, lean_object* v_month_761_){
_start:
{
lean_object* v_ratio_762_; lean_object* v_num_763_; lean_object* v_den_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v_ratio_762_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toDays___closed__2, &l_Std_Time_Month_Ordinal_toDays___closed__2_once, _init_l_Std_Time_Month_Ordinal_toDays___closed__2);
v_num_763_ = lean_ctor_get(v_ratio_762_, 0);
v_den_764_ = lean_ctor_get(v_ratio_762_, 1);
v___x_765_ = l_Std_Time_Month_Ordinal_toSeconds(v_leap_760_, v_month_761_);
v___x_766_ = lean_int_mul(v___x_765_, v_num_763_);
lean_dec(v___x_765_);
lean_inc(v_den_764_);
v___x_767_ = lean_nat_to_int(v_den_764_);
v___x_768_ = lean_int_ediv(v___x_766_, v___x_767_);
lean_dec(v___x_767_);
lean_dec(v___x_766_);
return v___x_768_;
}
}
LEAN_EXPORT void l_Std_Time_Month_Ordinal_toDays_0interp(lean_interpreter_value* stack)
{
uint8_t v_leap_760_ = stack[0].m_num;
lean_object* v_month_761_ = stack[1].m_obj;
lean_object* v_res_769_;
v_res_769_ = l_Std_Time_Month_Ordinal_toDays(v_leap_760_, v_month_761_);
stack->m_obj
 = v_res_769_;
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toDays___boxed(lean_object* v_leap_770_, lean_object* v_month_771_){
_start:
{
uint8_t v_leap_boxed_772_; lean_object* v_res_773_; 
v_leap_boxed_772_ = lean_unbox(v_leap_770_);
v_res_773_ = l_Std_Time_Month_Ordinal_toDays(v_leap_boxed_772_, v_month_771_);
lean_dec(v_month_771_);
return v_res_773_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = lean_unsigned_to_nat(30u);
v___x_775_ = lean_nat_to_int(v___x_774_);
return v___x_775_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__1(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_776_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0);
v___x_777_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_778_ = lean_int_add(v___x_777_, v___x_776_);
return v___x_778_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = lean_unsigned_to_nat(31u);
v___x_780_ = lean_nat_to_int(v___x_779_);
return v___x_780_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__3(void){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_781_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_782_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__1, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__1_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__1);
v___x_783_ = lean_int_sub(v___x_782_, v___x_781_);
return v___x_783_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4(void){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v_range_786_; 
v___x_784_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_785_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__3, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__3_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__3);
v_range_786_ = lean_int_add(v___x_785_, v___x_784_);
return v_range_786_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__5(void){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_787_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_788_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2);
v___x_789_ = lean_int_sub(v___x_788_, v___x_787_);
return v___x_789_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__6(void){
_start:
{
lean_object* v_range_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_range_790_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
v___x_791_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__5, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__5_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__5);
v___x_792_ = lean_int_emod(v___x_791_, v_range_790_);
return v___x_792_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__7(void){
_start:
{
lean_object* v_range_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v_range_793_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
v___x_794_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__6, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__6_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__6);
v___x_795_ = lean_int_add(v___x_794_, v_range_793_);
return v___x_795_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__8(void){
_start:
{
lean_object* v_range_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_range_796_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
v___x_797_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__7, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__7_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__7);
v___x_798_ = lean_int_emod(v___x_797_, v_range_796_);
return v___x_798_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__9(void){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_799_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_800_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__8, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__8_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__8);
v___x_801_ = lean_int_add(v___x_800_, v___x_799_);
return v___x_801_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__10(void){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = lean_unsigned_to_nat(28u);
v___x_803_ = lean_nat_to_int(v___x_802_);
return v___x_803_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__11(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_804_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_805_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__10, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__10_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__10);
v___x_806_ = lean_int_sub(v___x_805_, v___x_804_);
return v___x_806_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__12(void){
_start:
{
lean_object* v_range_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v_range_807_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
v___x_808_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__11, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__11_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__11);
v___x_809_ = lean_int_emod(v___x_808_, v_range_807_);
return v___x_809_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__13(void){
_start:
{
lean_object* v_range_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v_range_810_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
v___x_811_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__12, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__12_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__12);
v___x_812_ = lean_int_add(v___x_811_, v_range_810_);
return v___x_812_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__14(void){
_start:
{
lean_object* v_range_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v_range_813_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
v___x_814_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__13, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__13_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__13);
v___x_815_ = lean_int_emod(v___x_814_, v_range_813_);
return v___x_815_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__15(void){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_816_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_817_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__14, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__14_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__14);
v___x_818_ = lean_int_add(v___x_817_, v___x_816_);
return v___x_818_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__16(void){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_819_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_820_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0);
v___x_821_ = lean_int_sub(v___x_820_, v___x_819_);
return v___x_821_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__17(void){
_start:
{
lean_object* v_range_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v_range_822_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
v___x_823_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__16, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__16_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__16);
v___x_824_ = lean_int_emod(v___x_823_, v_range_822_);
return v___x_824_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__18(void){
_start:
{
lean_object* v_range_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v_range_825_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
v___x_826_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__17, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__17_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__17);
v___x_827_ = lean_int_add(v___x_826_, v_range_825_);
return v___x_827_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__19(void){
_start:
{
lean_object* v_range_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v_range_828_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
v___x_829_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__18, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__18_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__18);
v___x_830_ = lean_int_emod(v___x_829_, v_range_828_);
return v___x_830_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__20(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_831_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_832_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__19, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__19_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__19);
v___x_833_ = lean_int_add(v___x_832_, v___x_831_);
return v___x_833_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__21(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_834_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__20, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__20_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__20);
v___x_835_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__15, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__15_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__15);
v___x_836_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__9, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__9_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__9);
v___x_837_ = lean_unsigned_to_nat(12u);
v___x_838_ = lean_mk_empty_array_with_capacity(v___x_837_);
v___x_839_ = lean_array_push(v___x_838_, v___x_836_);
v___x_840_ = lean_array_push(v___x_839_, v___x_835_);
v___x_841_ = lean_array_push(v___x_840_, v___x_836_);
v___x_842_ = lean_array_push(v___x_841_, v___x_834_);
v___x_843_ = lean_array_push(v___x_842_, v___x_836_);
v___x_844_ = lean_array_push(v___x_843_, v___x_834_);
v___x_845_ = lean_array_push(v___x_844_, v___x_836_);
v___x_846_ = lean_array_push(v___x_845_, v___x_836_);
v___x_847_ = lean_array_push(v___x_846_, v___x_834_);
v___x_848_ = lean_array_push(v___x_847_, v___x_836_);
v___x_849_ = lean_array_push(v___x_848_, v___x_834_);
v___x_850_ = lean_array_push(v___x_849_, v___x_836_);
return v___x_850_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap(void){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__21, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__21_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__21);
return v___x_851_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__0(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = lean_unsigned_to_nat(0u);
v___x_853_ = lean_nat_to_int(v___x_852_);
return v___x_853_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__1(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = lean_unsigned_to_nat(59u);
v___x_855_ = lean_nat_to_int(v___x_854_);
return v___x_855_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__2(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = lean_unsigned_to_nat(90u);
v___x_857_ = lean_nat_to_int(v___x_856_);
return v___x_857_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__3(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = lean_unsigned_to_nat(120u);
v___x_859_ = lean_nat_to_int(v___x_858_);
return v___x_859_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__4(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = lean_unsigned_to_nat(151u);
v___x_861_ = lean_nat_to_int(v___x_860_);
return v___x_861_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__5(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_unsigned_to_nat(181u);
v___x_863_ = lean_nat_to_int(v___x_862_);
return v___x_863_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__6(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_unsigned_to_nat(212u);
v___x_865_ = lean_nat_to_int(v___x_864_);
return v___x_865_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__7(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = lean_unsigned_to_nat(243u);
v___x_867_ = lean_nat_to_int(v___x_866_);
return v___x_867_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__8(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = lean_unsigned_to_nat(273u);
v___x_869_ = lean_nat_to_int(v___x_868_);
return v___x_869_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__9(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = lean_unsigned_to_nat(304u);
v___x_871_ = lean_nat_to_int(v___x_870_);
return v___x_871_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__10(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = lean_unsigned_to_nat(334u);
v___x_873_ = lean_nat_to_int(v___x_872_);
return v___x_873_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__11(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_874_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__10, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__10_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__10);
v___x_875_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__9, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__9_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__9);
v___x_876_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__8, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__8_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__8);
v___x_877_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__7, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__7_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__7);
v___x_878_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__6, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__6_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__6);
v___x_879_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__5, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__5_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__5);
v___x_880_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__4);
v___x_881_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__3, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__3_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__3);
v___x_882_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__2, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__2_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__2);
v___x_883_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__1, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__1_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__1);
v___x_884_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2);
v___x_885_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__0, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__0_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__0);
v___x_886_ = lean_unsigned_to_nat(12u);
v___x_887_ = lean_mk_empty_array_with_capacity(v___x_886_);
v___x_888_ = lean_array_push(v___x_887_, v___x_885_);
v___x_889_ = lean_array_push(v___x_888_, v___x_884_);
v___x_890_ = lean_array_push(v___x_889_, v___x_883_);
v___x_891_ = lean_array_push(v___x_890_, v___x_882_);
v___x_892_ = lean_array_push(v___x_891_, v___x_881_);
v___x_893_ = lean_array_push(v___x_892_, v___x_880_);
v___x_894_ = lean_array_push(v___x_893_, v___x_879_);
v___x_895_ = lean_array_push(v___x_894_, v___x_878_);
v___x_896_ = lean_array_push(v___x_895_, v___x_877_);
v___x_897_ = lean_array_push(v___x_896_, v___x_876_);
v___x_898_ = lean_array_push(v___x_897_, v___x_875_);
v___x_899_ = lean_array_push(v___x_898_, v___x_874_);
return v___x_899_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes(void){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__11, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__11_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__11);
return v___x_900_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__0(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = lean_unsigned_to_nat(2u);
v___x_902_ = lean_nat_to_int(v___x_901_);
return v___x_902_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__1(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = lean_unsigned_to_nat(30u);
v___x_904_ = lean_nat_to_int(v___x_903_);
return v___x_904_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__2(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_905_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__1, &l_Std_Time_Month_Ordinal_days___closed__1_once, _init_l_Std_Time_Month_Ordinal_days___closed__1);
v___x_906_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_907_ = lean_int_add(v___x_906_, v___x_905_);
return v___x_907_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__3(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_908_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_909_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__2, &l_Std_Time_Month_Ordinal_days___closed__2_once, _init_l_Std_Time_Month_Ordinal_days___closed__2);
v___x_910_ = lean_int_sub(v___x_909_, v___x_908_);
return v___x_910_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__4(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v_range_913_; 
v___x_911_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_912_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__3, &l_Std_Time_Month_Ordinal_days___closed__3_once, _init_l_Std_Time_Month_Ordinal_days___closed__3);
v_range_913_ = lean_int_add(v___x_912_, v___x_911_);
return v_range_913_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__5(void){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_914_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_915_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__1, &l_Std_Time_Month_Ordinal_toSeconds___closed__1_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__1);
v___x_916_ = lean_int_sub(v___x_915_, v___x_914_);
return v___x_916_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__6(void){
_start:
{
lean_object* v_range_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v_range_917_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_918_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__5, &l_Std_Time_Month_Ordinal_days___closed__5_once, _init_l_Std_Time_Month_Ordinal_days___closed__5);
v___x_919_ = lean_int_emod(v___x_918_, v_range_917_);
return v___x_919_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__7(void){
_start:
{
lean_object* v_range_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v_range_920_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_921_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__6, &l_Std_Time_Month_Ordinal_days___closed__6_once, _init_l_Std_Time_Month_Ordinal_days___closed__6);
v___x_922_ = lean_int_add(v___x_921_, v_range_920_);
return v___x_922_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__8(void){
_start:
{
lean_object* v_range_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v_range_923_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_924_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__7, &l_Std_Time_Month_Ordinal_days___closed__7_once, _init_l_Std_Time_Month_Ordinal_days___closed__7);
v___x_925_ = lean_int_emod(v___x_924_, v_range_923_);
return v___x_925_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__9(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_926_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_927_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__8, &l_Std_Time_Month_Ordinal_days___closed__8_once, _init_l_Std_Time_Month_Ordinal_days___closed__8);
v___x_928_ = lean_int_add(v___x_927_, v___x_926_);
return v___x_928_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__10(void){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = lean_unsigned_to_nat(28u);
v___x_930_ = lean_nat_to_int(v___x_929_);
return v___x_930_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__11(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_931_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_932_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__10, &l_Std_Time_Month_Ordinal_days___closed__10_once, _init_l_Std_Time_Month_Ordinal_days___closed__10);
v___x_933_ = lean_int_sub(v___x_932_, v___x_931_);
return v___x_933_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__12(void){
_start:
{
lean_object* v_range_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v_range_934_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_935_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__11, &l_Std_Time_Month_Ordinal_days___closed__11_once, _init_l_Std_Time_Month_Ordinal_days___closed__11);
v___x_936_ = lean_int_emod(v___x_935_, v_range_934_);
return v___x_936_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__13(void){
_start:
{
lean_object* v_range_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v_range_937_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_938_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__12, &l_Std_Time_Month_Ordinal_days___closed__12_once, _init_l_Std_Time_Month_Ordinal_days___closed__12);
v___x_939_ = lean_int_add(v___x_938_, v_range_937_);
return v___x_939_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__14(void){
_start:
{
lean_object* v_range_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v_range_940_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_941_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__13, &l_Std_Time_Month_Ordinal_days___closed__13_once, _init_l_Std_Time_Month_Ordinal_days___closed__13);
v___x_942_ = lean_int_emod(v___x_941_, v_range_940_);
return v___x_942_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__15(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_943_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_944_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__14, &l_Std_Time_Month_Ordinal_days___closed__14_once, _init_l_Std_Time_Month_Ordinal_days___closed__14);
v___x_945_ = lean_int_add(v___x_944_, v___x_943_);
return v___x_945_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__16(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_946_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_947_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__1, &l_Std_Time_Month_Ordinal_days___closed__1_once, _init_l_Std_Time_Month_Ordinal_days___closed__1);
v___x_948_ = lean_int_sub(v___x_947_, v___x_946_);
return v___x_948_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__17(void){
_start:
{
lean_object* v_range_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v_range_949_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_950_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__16, &l_Std_Time_Month_Ordinal_days___closed__16_once, _init_l_Std_Time_Month_Ordinal_days___closed__16);
v___x_951_ = lean_int_emod(v___x_950_, v_range_949_);
return v___x_951_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__18(void){
_start:
{
lean_object* v_range_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v_range_952_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_953_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__17, &l_Std_Time_Month_Ordinal_days___closed__17_once, _init_l_Std_Time_Month_Ordinal_days___closed__17);
v___x_954_ = lean_int_add(v___x_953_, v_range_952_);
return v___x_954_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__19(void){
_start:
{
lean_object* v_range_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v_range_955_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_956_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__18, &l_Std_Time_Month_Ordinal_days___closed__18_once, _init_l_Std_Time_Month_Ordinal_days___closed__18);
v___x_957_ = lean_int_emod(v___x_956_, v_range_955_);
return v___x_957_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__20(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_958_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_959_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__19, &l_Std_Time_Month_Ordinal_days___closed__19_once, _init_l_Std_Time_Month_Ordinal_days___closed__19);
v___x_960_ = lean_int_add(v___x_959_, v___x_958_);
return v___x_960_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__21(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_961_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__20, &l_Std_Time_Month_Ordinal_days___closed__20_once, _init_l_Std_Time_Month_Ordinal_days___closed__20);
v___x_962_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__15, &l_Std_Time_Month_Ordinal_days___closed__15_once, _init_l_Std_Time_Month_Ordinal_days___closed__15);
v___x_963_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__9, &l_Std_Time_Month_Ordinal_days___closed__9_once, _init_l_Std_Time_Month_Ordinal_days___closed__9);
v___x_964_ = lean_unsigned_to_nat(12u);
v___x_965_ = lean_mk_empty_array_with_capacity(v___x_964_);
v___x_966_ = lean_array_push(v___x_965_, v___x_963_);
v___x_967_ = lean_array_push(v___x_966_, v___x_962_);
v___x_968_ = lean_array_push(v___x_967_, v___x_963_);
v___x_969_ = lean_array_push(v___x_968_, v___x_961_);
v___x_970_ = lean_array_push(v___x_969_, v___x_963_);
v___x_971_ = lean_array_push(v___x_970_, v___x_961_);
v___x_972_ = lean_array_push(v___x_971_, v___x_963_);
v___x_973_ = lean_array_push(v___x_972_, v___x_963_);
v___x_974_ = lean_array_push(v___x_973_, v___x_961_);
v___x_975_ = lean_array_push(v___x_974_, v___x_963_);
v___x_976_ = lean_array_push(v___x_975_, v___x_961_);
v___x_977_ = lean_array_push(v___x_976_, v___x_963_);
return v___x_977_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__22(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = lean_unsigned_to_nat(29u);
v___x_979_ = lean_nat_to_int(v___x_978_);
return v___x_979_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__23(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_980_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_981_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__22, &l_Std_Time_Month_Ordinal_days___closed__22_once, _init_l_Std_Time_Month_Ordinal_days___closed__22);
v___x_982_ = lean_int_sub(v___x_981_, v___x_980_);
return v___x_982_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__24(void){
_start:
{
lean_object* v_range_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v_range_983_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_984_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__23, &l_Std_Time_Month_Ordinal_days___closed__23_once, _init_l_Std_Time_Month_Ordinal_days___closed__23);
v___x_985_ = lean_int_emod(v___x_984_, v_range_983_);
return v___x_985_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__25(void){
_start:
{
lean_object* v_range_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v_range_986_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_987_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__24, &l_Std_Time_Month_Ordinal_days___closed__24_once, _init_l_Std_Time_Month_Ordinal_days___closed__24);
v___x_988_ = lean_int_add(v___x_987_, v_range_986_);
return v___x_988_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__26(void){
_start:
{
lean_object* v_range_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v_range_989_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_990_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__25, &l_Std_Time_Month_Ordinal_days___closed__25_once, _init_l_Std_Time_Month_Ordinal_days___closed__25);
v___x_991_ = lean_int_emod(v___x_990_, v_range_989_);
return v___x_991_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__27(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_992_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_993_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__26, &l_Std_Time_Month_Ordinal_days___closed__26_once, _init_l_Std_Time_Month_Ordinal_days___closed__26);
v___x_994_ = lean_int_add(v___x_993_, v___x_992_);
return v___x_994_;
}
}
lean_object* l_Std_Time_Month_Ordinal_days(uint8_t v_leap_995_, lean_object* v_month_996_){
_start:
{
lean_object* v___x_997_; uint8_t v___x_998_; 
v___x_997_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__0, &l_Std_Time_Month_Ordinal_days___closed__0_once, _init_l_Std_Time_Month_Ordinal_days___closed__0);
v___x_998_ = lean_int_dec_eq(v_month_996_, v___x_997_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_999_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__21, &l_Std_Time_Month_Ordinal_days___closed__21_once, _init_l_Std_Time_Month_Ordinal_days___closed__21);
v___x_1000_ = lean_obj_once(&l_Std_Time_Month_Quarter_ofMonth___closed__1, &l_Std_Time_Month_Quarter_ofMonth___closed__1_once, _init_l_Std_Time_Month_Quarter_ofMonth___closed__1);
v___x_1001_ = lean_int_add(v_month_996_, v___x_1000_);
v___x_1002_ = l_Int_toNat(v___x_1001_);
lean_dec(v___x_1001_);
v___x_1003_ = lean_array_fget_borrowed(v___x_999_, v___x_1002_);
lean_dec(v___x_1002_);
lean_inc(v___x_1003_);
return v___x_1003_;
}
else
{
if (v_leap_995_ == 0)
{
lean_object* v___x_1004_; 
v___x_1004_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__15, &l_Std_Time_Month_Ordinal_days___closed__15_once, _init_l_Std_Time_Month_Ordinal_days___closed__15);
return v___x_1004_;
}
else
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__27, &l_Std_Time_Month_Ordinal_days___closed__27_once, _init_l_Std_Time_Month_Ordinal_days___closed__27);
return v___x_1005_;
}
}
}
}
LEAN_EXPORT void l_Std_Time_Month_Ordinal_days_0interp(lean_interpreter_value* stack)
{
uint8_t v_leap_995_ = stack[0].m_num;
lean_object* v_month_996_ = stack[1].m_obj;
lean_object* v_res_1006_;
v_res_1006_ = l_Std_Time_Month_Ordinal_days(v_leap_995_, v_month_996_);
stack->m_obj
 = v_res_1006_;
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_days___boxed(lean_object* v_leap_1007_, lean_object* v_month_1008_){
_start:
{
uint8_t v_leap_boxed_1009_; lean_object* v_res_1010_; 
v_leap_boxed_1009_ = lean_unbox(v_leap_1007_);
v_res_1010_ = l_Std_Time_Month_Ordinal_days(v_leap_boxed_1009_, v_month_1008_);
lean_dec(v_month_1008_);
return v_res_1010_;
}
}
lean_object* l_Std_Time_Month_Ordinal_cumulativeDays(uint8_t v_leap_1011_, lean_object* v_month_1012_){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v_res_1021_; 
v___x_1013_ = lean_obj_once(&l_Std_Time_Month_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0);
v___x_1014_ = lean_unsigned_to_nat(12u);
v___x_1015_ = lean_mk_empty_array_with_capacity(v___x_1014_);
lean_dec_ref(v___x_1015_);
v___x_1016_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__12, &l_Std_Time_Month_Ordinal_toSeconds___closed__12_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__12);
v___x_1017_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0);
v___x_1018_ = lean_obj_once(&l_Std_Time_Month_Quarter_ofMonth___closed__1, &l_Std_Time_Month_Quarter_ofMonth___closed__1_once, _init_l_Std_Time_Month_Quarter_ofMonth___closed__1);
v___x_1019_ = lean_int_add(v_month_1012_, v___x_1018_);
v___x_1020_ = l_Int_toNat(v___x_1019_);
lean_dec(v___x_1019_);
v_res_1021_ = lean_array_fget_borrowed(v___x_1016_, v___x_1020_);
lean_dec(v___x_1020_);
if (v_leap_1011_ == 0)
{
lean_object* v___x_1022_; 
v___x_1022_ = lean_int_add(v_res_1021_, v___x_1013_);
return v___x_1022_;
}
else
{
lean_object* v___x_1023_; uint8_t v___x_1024_; 
v___x_1023_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__0, &l_Std_Time_Month_Ordinal_days___closed__0_once, _init_l_Std_Time_Month_Ordinal_days___closed__0);
v___x_1024_ = lean_int_dec_lt(v___x_1023_, v_month_1012_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; 
v___x_1025_ = lean_int_add(v_res_1021_, v___x_1013_);
return v___x_1025_;
}
else
{
lean_object* v___x_1026_; 
v___x_1026_ = lean_int_add(v_res_1021_, v___x_1017_);
return v___x_1026_;
}
}
}
}
LEAN_EXPORT void l_Std_Time_Month_Ordinal_cumulativeDays_0interp(lean_interpreter_value* stack)
{
uint8_t v_leap_1011_ = stack[0].m_num;
lean_object* v_month_1012_ = stack[1].m_obj;
lean_object* v_res_1027_;
v_res_1027_ = l_Std_Time_Month_Ordinal_cumulativeDays(v_leap_1011_, v_month_1012_);
stack->m_obj
 = v_res_1027_;
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_cumulativeDays___boxed(lean_object* v_leap_1028_, lean_object* v_month_1029_){
_start:
{
uint8_t v_leap_boxed_1030_; lean_object* v_res_1031_; 
v_leap_boxed_1030_ = lean_unbox(v_leap_1028_);
v_res_1031_ = l_Std_Time_Month_Ordinal_cumulativeDays(v_leap_boxed_1030_, v_month_1029_);
lean_dec(v_month_1029_);
return v_res_1031_;
}
}
lean_object* l_Std_Time_Month_Ordinal_clipDay(uint8_t v_leap_1032_, lean_object* v_month_1033_, lean_object* v_day_1034_){
_start:
{
lean_object* v_max_1035_; uint8_t v___x_1036_; 
v_max_1035_ = l_Std_Time_Month_Ordinal_days(v_leap_1032_, v_month_1033_);
v___x_1036_ = lean_int_dec_lt(v_max_1035_, v_day_1034_);
if (v___x_1036_ == 0)
{
lean_dec(v_max_1035_);
lean_inc(v_day_1034_);
return v_day_1034_;
}
else
{
return v_max_1035_;
}
}
}
LEAN_EXPORT void l_Std_Time_Month_Ordinal_clipDay_0interp(lean_interpreter_value* stack)
{
uint8_t v_leap_1032_ = stack[0].m_num;
lean_object* v_month_1033_ = stack[1].m_obj;
lean_object* v_day_1034_ = stack[2].m_obj;
lean_object* v_res_1037_;
v_res_1037_ = l_Std_Time_Month_Ordinal_clipDay(v_leap_1032_, v_month_1033_, v_day_1034_);
stack->m_obj
 = v_res_1037_;
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_clipDay___boxed(lean_object* v_leap_1038_, lean_object* v_month_1039_, lean_object* v_day_1040_){
_start:
{
uint8_t v_leap_boxed_1041_; lean_object* v_res_1042_; 
v_leap_boxed_1041_ = lean_unbox(v_leap_1038_);
v_res_1042_ = l_Std_Time_Month_Ordinal_clipDay(v_leap_boxed_1041_, v_month_1039_, v_day_1040_);
lean_dec(v_day_1040_);
lean_dec(v_month_1039_);
return v_res_1042_;
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
