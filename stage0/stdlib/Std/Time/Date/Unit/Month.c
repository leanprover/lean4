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
lean_object* l_Int_ediv___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Time_Day_instInhabitedOffset;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Std_Time_Second_instAddOffset;
lean_object* lean_int_div(lean_object*, lean_object*);
lean_object* l_instToStringInt___lam__0___boxed(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
extern lean_object* l_Int_instInhabited;
lean_object* l_Std_Time_Internal_Bounded_instRepr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Int_mul___boxed(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_Bounded_instOrd___lam__0___boxed(lean_object*);
lean_object* l_instOrdInt___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_add___boxed(lean_object*, lean_object*);
lean_object* l_Rat_instNatCast___lam__0(lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
extern lean_object* l_Std_Time_Day_instAddOffset;
lean_object* l_Int_neg___boxed(lean_object*);
lean_object* l_instReprInt___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_sub___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Month_instReprOrdinal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_Bounded_instRepr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Month_instReprOrdinal___closed__0 = (const lean_object*)&l_Std_Time_Month_instReprOrdinal___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Month_instReprOrdinal = (const lean_object*)&l_Std_Time_Month_instReprOrdinal___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableEqOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableEqOrdinal___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instLEOrdinal;
LEAN_EXPORT lean_object* l_Std_Time_Month_instLTOrdinal;
static lean_once_cell_t l_Std_Time_Month_instOfNatOrdinal___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instOfNatOrdinal___closed__0;
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
static lean_once_cell_t l_Std_Time_Month_instInhabitedOrdinal___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instInhabitedOrdinal___closed__5;
static lean_once_cell_t l_Std_Time_Month_instInhabitedOrdinal___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instInhabitedOrdinal___closed__6;
static lean_once_cell_t l_Std_Time_Month_instInhabitedOrdinal___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instInhabitedOrdinal___closed__7;
static lean_once_cell_t l_Std_Time_Month_instInhabitedOrdinal___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instInhabitedOrdinal___closed__8;
LEAN_EXPORT lean_object* l_Std_Time_Month_instInhabitedOrdinal;
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableLeOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableLeOrdinal___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableLtOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableLtOrdinal___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Month_instOrdOrdinal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_Bounded_instOrd___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Month_instOrdOrdinal___closed__0 = (const lean_object*)&l_Std_Time_Month_instOrdOrdinal___closed__0_value;
static const lean_closure_object l_Std_Time_Month_instOrdOrdinal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdInt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Month_instOrdOrdinal___closed__1 = (const lean_object*)&l_Std_Time_Month_instOrdOrdinal___closed__1_value;
static const lean_closure_object l_Std_Time_Month_instOrdOrdinal___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_compareOn___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Month_instOrdOrdinal___closed__1_value),((lean_object*)&l_Std_Time_Month_instOrdOrdinal___closed__0_value)} };
static const lean_object* l_Std_Time_Month_instOrdOrdinal___closed__2 = (const lean_object*)&l_Std_Time_Month_instOrdOrdinal___closed__2_value;
LEAN_EXPORT const lean_object* l_Std_Time_Month_instOrdOrdinal = (const lean_object*)&l_Std_Time_Month_instOrdOrdinal___closed__2_value;
static const lean_closure_object l_Std_Time_Month_instReprOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprInt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Month_instReprOffset___closed__0 = (const lean_object*)&l_Std_Time_Month_instReprOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Month_instReprOffset = (const lean_object*)&l_Std_Time_Month_instReprOffset___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableEqOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableEqOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instInhabitedOffset;
static const lean_closure_object l_Std_Time_Month_instAddOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Month_instAddOffset___closed__0 = (const lean_object*)&l_Std_Time_Month_instAddOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Month_instAddOffset = (const lean_object*)&l_Std_Time_Month_instAddOffset___closed__0_value;
static const lean_closure_object l_Std_Time_Month_instSubOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Month_instSubOffset___closed__0 = (const lean_object*)&l_Std_Time_Month_instSubOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Month_instSubOffset = (const lean_object*)&l_Std_Time_Month_instSubOffset___closed__0_value;
static const lean_closure_object l_Std_Time_Month_instMulOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Month_instMulOffset___closed__0 = (const lean_object*)&l_Std_Time_Month_instMulOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Month_instMulOffset = (const lean_object*)&l_Std_Time_Month_instMulOffset___closed__0_value;
static const lean_closure_object l_Std_Time_Month_instDivOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_ediv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Month_instDivOffset___closed__0 = (const lean_object*)&l_Std_Time_Month_instDivOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Month_instDivOffset = (const lean_object*)&l_Std_Time_Month_instDivOffset___closed__0_value;
static const lean_closure_object l_Std_Time_Month_instNegOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Month_instNegOffset___closed__0 = (const lean_object*)&l_Std_Time_Month_instNegOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Month_instNegOffset = (const lean_object*)&l_Std_Time_Month_instNegOffset___closed__0_value;
static const lean_closure_object l_Std_Time_Month_instToStringOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringInt___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Month_instToStringOffset___closed__0 = (const lean_object*)&l_Std_Time_Month_instToStringOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Month_instToStringOffset = (const lean_object*)&l_Std_Time_Month_instToStringOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Month_instLTOffset;
LEAN_EXPORT lean_object* l_Std_Time_Month_instLEOffset;
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableLeOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableLeOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableLtOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableLtOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instOfNatOffset(lean_object*);
LEAN_EXPORT const lean_object* l_Std_Time_Month_instOrdOffset = (const lean_object*)&l_Std_Time_Month_instOrdOrdinal___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Time_Month_instReprQuarter = (const lean_object*)&l_Std_Time_Month_instReprOrdinal___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableEqQuarter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableEqQuarter___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Month_instLTQuarter;
LEAN_EXPORT lean_object* l_Std_Time_Month_instLEQuarter;
LEAN_EXPORT lean_object* l_Std_Time_Month_instOfNatQuarter(lean_object*);
static lean_once_cell_t l_Std_Time_Month_instInhabitedQuarter___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instInhabitedQuarter___closed__0;
static lean_once_cell_t l_Std_Time_Month_instInhabitedQuarter___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instInhabitedQuarter___closed__1;
static lean_once_cell_t l_Std_Time_Month_instInhabitedQuarter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instInhabitedQuarter___closed__2;
static lean_once_cell_t l_Std_Time_Month_instInhabitedQuarter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instInhabitedQuarter___closed__3;
static lean_once_cell_t l_Std_Time_Month_instInhabitedQuarter___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instInhabitedQuarter___closed__4;
static lean_once_cell_t l_Std_Time_Month_instInhabitedQuarter___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instInhabitedQuarter___closed__5;
static lean_once_cell_t l_Std_Time_Month_instInhabitedQuarter___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instInhabitedQuarter___closed__6;
static lean_once_cell_t l_Std_Time_Month_instInhabitedQuarter___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_instInhabitedQuarter___closed__7;
LEAN_EXPORT lean_object* l_Std_Time_Month_instInhabitedQuarter;
LEAN_EXPORT const lean_object* l_Std_Time_Month_instOrdQuarter = (const lean_object*)&l_Std_Time_Month_instOrdOrdinal___closed__2_value;
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
static lean_once_cell_t l_Std_Time_Month_Ordinal_toNat___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Month_Ordinal_toNat___closed__0;
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
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableEqOrdinal(lean_object* v_a_3_, lean_object* v_b_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_int_dec_eq(v_a_3_, v_b_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableEqOrdinal___boxed(lean_object* v_a_6_, lean_object* v_b_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = l_Std_Time_Month_instDecidableEqOrdinal(v_a_6_, v_b_7_);
lean_dec(v_b_7_);
lean_dec(v_a_6_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
static lean_object* _init_l_Std_Time_Month_instLEOrdinal(void){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_box(0);
return v___x_10_;
}
}
static lean_object* _init_l_Std_Time_Month_instLTOrdinal(void){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_box(0);
return v___x_11_;
}
}
static lean_object* _init_l_Std_Time_Month_instOfNatOrdinal___closed__0(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_unsigned_to_nat(1u);
v___x_13_ = lean_nat_to_int(v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instOfNatOrdinal(lean_object* v_n_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_15_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_16_ = lean_unsigned_to_nat(11u);
v___x_17_ = l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast(v___x_15_, v_n_14_, v___x_16_);
return v___x_17_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedOrdinal___closed__0(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_unsigned_to_nat(11u);
v___x_19_ = lean_nat_to_int(v___x_18_);
return v___x_19_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedOrdinal___closed__1(void){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_20_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__0, &l_Std_Time_Month_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__0);
v___x_21_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_22_ = lean_int_add(v___x_21_, v___x_20_);
return v___x_22_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedOrdinal___closed__2(void){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_23_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_24_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__1, &l_Std_Time_Month_instInhabitedOrdinal___closed__1_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__1);
v___x_25_ = lean_int_sub(v___x_24_, v___x_23_);
return v___x_25_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v_range_28_; 
v___x_26_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_27_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__2, &l_Std_Time_Month_instInhabitedOrdinal___closed__2_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__2);
v_range_28_ = lean_int_add(v___x_27_, v___x_26_);
return v_range_28_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedOrdinal___closed__4(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_30_ = lean_int_sub(v___x_29_, v___x_29_);
return v___x_30_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedOrdinal___closed__5(void){
_start:
{
lean_object* v_range_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v_range_31_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_32_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__4, &l_Std_Time_Month_instInhabitedOrdinal___closed__4_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__4);
v___x_33_ = lean_int_emod(v___x_32_, v_range_31_);
return v___x_33_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedOrdinal___closed__6(void){
_start:
{
lean_object* v_range_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v_range_34_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_35_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__5, &l_Std_Time_Month_instInhabitedOrdinal___closed__5_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__5);
v___x_36_ = lean_int_add(v___x_35_, v_range_34_);
return v___x_36_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedOrdinal___closed__7(void){
_start:
{
lean_object* v_range_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v_range_37_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_38_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__6, &l_Std_Time_Month_instInhabitedOrdinal___closed__6_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__6);
v___x_39_ = lean_int_emod(v___x_38_, v_range_37_);
return v___x_39_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedOrdinal___closed__8(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_40_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_41_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__7, &l_Std_Time_Month_instInhabitedOrdinal___closed__7_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__7);
v___x_42_ = lean_int_add(v___x_41_, v___x_40_);
return v___x_42_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedOrdinal(void){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__8, &l_Std_Time_Month_instInhabitedOrdinal___closed__8_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__8);
return v___x_43_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableLeOrdinal(lean_object* v_x_44_, lean_object* v_y_45_){
_start:
{
uint8_t v___x_46_; 
v___x_46_ = lean_int_dec_le(v_x_44_, v_y_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableLeOrdinal___boxed(lean_object* v_x_47_, lean_object* v_y_48_){
_start:
{
uint8_t v_res_49_; lean_object* v_r_50_; 
v_res_49_ = l_Std_Time_Month_instDecidableLeOrdinal(v_x_47_, v_y_48_);
lean_dec(v_y_48_);
lean_dec(v_x_47_);
v_r_50_ = lean_box(v_res_49_);
return v_r_50_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableLtOrdinal(lean_object* v_x_51_, lean_object* v_y_52_){
_start:
{
uint8_t v___x_53_; 
v___x_53_ = lean_int_dec_lt(v_x_51_, v_y_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableLtOrdinal___boxed(lean_object* v_x_54_, lean_object* v_y_55_){
_start:
{
uint8_t v_res_56_; lean_object* v_r_57_; 
v_res_56_ = l_Std_Time_Month_instDecidableLtOrdinal(v_x_54_, v_y_55_);
lean_dec(v_y_55_);
lean_dec(v_x_54_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableEqOffset(lean_object* v_a_66_, lean_object* v_b_67_){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = lean_int_dec_eq(v_a_66_, v_b_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableEqOffset___boxed(lean_object* v_a_69_, lean_object* v_b_70_){
_start:
{
uint8_t v_res_71_; lean_object* v_r_72_; 
v_res_71_ = l_Std_Time_Month_instDecidableEqOffset(v_a_69_, v_b_70_);
lean_dec(v_b_70_);
lean_dec(v_a_69_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedOffset(void){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Int_instInhabited;
return v___x_73_;
}
}
static lean_object* _init_l_Std_Time_Month_instLTOffset(void){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lean_box(0);
return v___x_86_;
}
}
static lean_object* _init_l_Std_Time_Month_instLEOffset(void){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lean_box(0);
return v___x_87_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableLeOffset(lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
uint8_t v___x_90_; 
v___x_90_ = lean_int_dec_le(v___y_88_, v___y_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableLeOffset___boxed(lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
uint8_t v_res_93_; lean_object* v_r_94_; 
v_res_93_ = l_Std_Time_Month_instDecidableLeOffset(v___y_91_, v___y_92_);
lean_dec(v___y_92_);
lean_dec(v___y_91_);
v_r_94_ = lean_box(v_res_93_);
return v_r_94_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableLtOffset(lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
uint8_t v___x_97_; 
v___x_97_ = lean_int_dec_lt(v___y_95_, v___y_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableLtOffset___boxed(lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
uint8_t v_res_100_; lean_object* v_r_101_; 
v_res_100_ = l_Std_Time_Month_instDecidableLtOffset(v___y_98_, v___y_99_);
lean_dec(v___y_99_);
lean_dec(v___y_98_);
v_r_101_ = lean_box(v_res_100_);
return v_r_101_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instOfNatOffset(lean_object* v_n_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = lean_nat_to_int(v_n_102_);
return v___x_103_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Month_instDecidableEqQuarter(lean_object* v_a_106_, lean_object* v_b_107_){
_start:
{
uint8_t v___x_108_; 
v___x_108_ = lean_int_dec_eq(v_a_106_, v_b_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instDecidableEqQuarter___boxed(lean_object* v_a_109_, lean_object* v_b_110_){
_start:
{
uint8_t v_res_111_; lean_object* v_r_112_; 
v_res_111_ = l_Std_Time_Month_instDecidableEqQuarter(v_a_109_, v_b_110_);
lean_dec(v_b_110_);
lean_dec(v_a_109_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
static lean_object* _init_l_Std_Time_Month_instLTQuarter(void){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lean_box(0);
return v___x_113_;
}
}
static lean_object* _init_l_Std_Time_Month_instLEQuarter(void){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = lean_box(0);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_instOfNatQuarter(lean_object* v_n_115_){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_116_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_117_ = lean_unsigned_to_nat(3u);
v___x_118_ = l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast(v___x_116_, v_n_115_, v___x_117_);
return v___x_118_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedQuarter___closed__0(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_unsigned_to_nat(3u);
v___x_120_ = lean_nat_to_int(v___x_119_);
return v___x_120_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedQuarter___closed__1(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_121_ = lean_obj_once(&l_Std_Time_Month_instInhabitedQuarter___closed__0, &l_Std_Time_Month_instInhabitedQuarter___closed__0_once, _init_l_Std_Time_Month_instInhabitedQuarter___closed__0);
v___x_122_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_123_ = lean_int_add(v___x_122_, v___x_121_);
return v___x_123_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedQuarter___closed__2(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_125_ = lean_obj_once(&l_Std_Time_Month_instInhabitedQuarter___closed__1, &l_Std_Time_Month_instInhabitedQuarter___closed__1_once, _init_l_Std_Time_Month_instInhabitedQuarter___closed__1);
v___x_126_ = lean_int_sub(v___x_125_, v___x_124_);
return v___x_126_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedQuarter___closed__3(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v_range_129_; 
v___x_127_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_128_ = lean_obj_once(&l_Std_Time_Month_instInhabitedQuarter___closed__2, &l_Std_Time_Month_instInhabitedQuarter___closed__2_once, _init_l_Std_Time_Month_instInhabitedQuarter___closed__2);
v_range_129_ = lean_int_add(v___x_128_, v___x_127_);
return v_range_129_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedQuarter___closed__4(void){
_start:
{
lean_object* v_range_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v_range_130_ = lean_obj_once(&l_Std_Time_Month_instInhabitedQuarter___closed__3, &l_Std_Time_Month_instInhabitedQuarter___closed__3_once, _init_l_Std_Time_Month_instInhabitedQuarter___closed__3);
v___x_131_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__4, &l_Std_Time_Month_instInhabitedOrdinal___closed__4_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__4);
v___x_132_ = lean_int_emod(v___x_131_, v_range_130_);
return v___x_132_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedQuarter___closed__5(void){
_start:
{
lean_object* v_range_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v_range_133_ = lean_obj_once(&l_Std_Time_Month_instInhabitedQuarter___closed__3, &l_Std_Time_Month_instInhabitedQuarter___closed__3_once, _init_l_Std_Time_Month_instInhabitedQuarter___closed__3);
v___x_134_ = lean_obj_once(&l_Std_Time_Month_instInhabitedQuarter___closed__4, &l_Std_Time_Month_instInhabitedQuarter___closed__4_once, _init_l_Std_Time_Month_instInhabitedQuarter___closed__4);
v___x_135_ = lean_int_add(v___x_134_, v_range_133_);
return v___x_135_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedQuarter___closed__6(void){
_start:
{
lean_object* v_range_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_range_136_ = lean_obj_once(&l_Std_Time_Month_instInhabitedQuarter___closed__3, &l_Std_Time_Month_instInhabitedQuarter___closed__3_once, _init_l_Std_Time_Month_instInhabitedQuarter___closed__3);
v___x_137_ = lean_obj_once(&l_Std_Time_Month_instInhabitedQuarter___closed__5, &l_Std_Time_Month_instInhabitedQuarter___closed__5_once, _init_l_Std_Time_Month_instInhabitedQuarter___closed__5);
v___x_138_ = lean_int_emod(v___x_137_, v_range_136_);
return v___x_138_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedQuarter___closed__7(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_140_ = lean_obj_once(&l_Std_Time_Month_instInhabitedQuarter___closed__6, &l_Std_Time_Month_instInhabitedQuarter___closed__6_once, _init_l_Std_Time_Month_instInhabitedQuarter___closed__6);
v___x_141_ = lean_int_add(v___x_140_, v___x_139_);
return v___x_141_;
}
}
static lean_object* _init_l_Std_Time_Month_instInhabitedQuarter(void){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = lean_obj_once(&l_Std_Time_Month_instInhabitedQuarter___closed__7, &l_Std_Time_Month_instInhabitedQuarter___closed__7_once, _init_l_Std_Time_Month_instInhabitedQuarter___closed__7);
return v___x_142_;
}
}
static lean_object* _init_l_Std_Time_Month_Quarter_ofMonth___closed__0(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_unsigned_to_nat(3u);
v___x_145_ = lean_nat_to_int(v___x_144_);
return v___x_145_;
}
}
static lean_object* _init_l_Std_Time_Month_Quarter_ofMonth___closed__1(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_147_ = lean_int_neg(v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Quarter_ofMonth(lean_object* v_month_148_){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_149_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_150_ = lean_obj_once(&l_Std_Time_Month_Quarter_ofMonth___closed__0, &l_Std_Time_Month_Quarter_ofMonth___closed__0_once, _init_l_Std_Time_Month_Quarter_ofMonth___closed__0);
v___x_151_ = lean_obj_once(&l_Std_Time_Month_Quarter_ofMonth___closed__1, &l_Std_Time_Month_Quarter_ofMonth___closed__1_once, _init_l_Std_Time_Month_Quarter_ofMonth___closed__1);
v___x_152_ = lean_int_add(v_month_148_, v___x_151_);
v___x_153_ = lean_int_ediv(v___x_152_, v___x_150_);
lean_dec(v___x_152_);
v___x_154_ = lean_int_add(v___x_153_, v___x_149_);
lean_dec(v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Quarter_ofMonth___boxed(lean_object* v_month_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Std_Time_Month_Quarter_ofMonth(v_month_155_);
lean_dec(v_month_155_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Offset_ofNat(lean_object* v_data_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = lean_nat_to_int(v_data_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Offset_ofInt(lean_object* v_data_159_){
_start:
{
lean_inc(v_data_159_);
return v_data_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Offset_ofInt___boxed(lean_object* v_data_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Std_Time_Month_Offset_ofInt(v_data_160_);
lean_dec(v_data_160_);
return v_res_161_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_january(void){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__8, &l_Std_Time_Month_instInhabitedOrdinal___closed__8_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__8);
return v___x_162_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_february___closed__0(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_unsigned_to_nat(2u);
v___x_164_ = lean_nat_to_int(v___x_163_);
return v___x_164_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_february___closed__1(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_166_ = lean_obj_once(&l_Std_Time_Month_Ordinal_february___closed__0, &l_Std_Time_Month_Ordinal_february___closed__0_once, _init_l_Std_Time_Month_Ordinal_february___closed__0);
v___x_167_ = lean_int_sub(v___x_166_, v___x_165_);
return v___x_167_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_february___closed__2(void){
_start:
{
lean_object* v_range_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v_range_168_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_169_ = lean_obj_once(&l_Std_Time_Month_Ordinal_february___closed__1, &l_Std_Time_Month_Ordinal_february___closed__1_once, _init_l_Std_Time_Month_Ordinal_february___closed__1);
v___x_170_ = lean_int_emod(v___x_169_, v_range_168_);
return v___x_170_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_february___closed__3(void){
_start:
{
lean_object* v_range_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v_range_171_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_172_ = lean_obj_once(&l_Std_Time_Month_Ordinal_february___closed__2, &l_Std_Time_Month_Ordinal_february___closed__2_once, _init_l_Std_Time_Month_Ordinal_february___closed__2);
v___x_173_ = lean_int_add(v___x_172_, v_range_171_);
return v___x_173_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_february___closed__4(void){
_start:
{
lean_object* v_range_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v_range_174_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_175_ = lean_obj_once(&l_Std_Time_Month_Ordinal_february___closed__3, &l_Std_Time_Month_Ordinal_february___closed__3_once, _init_l_Std_Time_Month_Ordinal_february___closed__3);
v___x_176_ = lean_int_emod(v___x_175_, v_range_174_);
return v___x_176_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_february___closed__5(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_178_ = lean_obj_once(&l_Std_Time_Month_Ordinal_february___closed__4, &l_Std_Time_Month_Ordinal_february___closed__4_once, _init_l_Std_Time_Month_Ordinal_february___closed__4);
v___x_179_ = lean_int_add(v___x_178_, v___x_177_);
return v___x_179_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_february(void){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = lean_obj_once(&l_Std_Time_Month_Ordinal_february___closed__5, &l_Std_Time_Month_Ordinal_february___closed__5_once, _init_l_Std_Time_Month_Ordinal_february___closed__5);
return v___x_180_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_march___closed__0(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_181_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_182_ = lean_obj_once(&l_Std_Time_Month_instInhabitedQuarter___closed__0, &l_Std_Time_Month_instInhabitedQuarter___closed__0_once, _init_l_Std_Time_Month_instInhabitedQuarter___closed__0);
v___x_183_ = lean_int_sub(v___x_182_, v___x_181_);
return v___x_183_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_march___closed__1(void){
_start:
{
lean_object* v_range_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v_range_184_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_185_ = lean_obj_once(&l_Std_Time_Month_Ordinal_march___closed__0, &l_Std_Time_Month_Ordinal_march___closed__0_once, _init_l_Std_Time_Month_Ordinal_march___closed__0);
v___x_186_ = lean_int_emod(v___x_185_, v_range_184_);
return v___x_186_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_march___closed__2(void){
_start:
{
lean_object* v_range_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v_range_187_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_188_ = lean_obj_once(&l_Std_Time_Month_Ordinal_march___closed__1, &l_Std_Time_Month_Ordinal_march___closed__1_once, _init_l_Std_Time_Month_Ordinal_march___closed__1);
v___x_189_ = lean_int_add(v___x_188_, v_range_187_);
return v___x_189_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_march___closed__3(void){
_start:
{
lean_object* v_range_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v_range_190_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_191_ = lean_obj_once(&l_Std_Time_Month_Ordinal_march___closed__2, &l_Std_Time_Month_Ordinal_march___closed__2_once, _init_l_Std_Time_Month_Ordinal_march___closed__2);
v___x_192_ = lean_int_emod(v___x_191_, v_range_190_);
return v___x_192_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_march___closed__4(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_193_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_194_ = lean_obj_once(&l_Std_Time_Month_Ordinal_march___closed__3, &l_Std_Time_Month_Ordinal_march___closed__3_once, _init_l_Std_Time_Month_Ordinal_march___closed__3);
v___x_195_ = lean_int_add(v___x_194_, v___x_193_);
return v___x_195_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_march(void){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = lean_obj_once(&l_Std_Time_Month_Ordinal_march___closed__4, &l_Std_Time_Month_Ordinal_march___closed__4_once, _init_l_Std_Time_Month_Ordinal_march___closed__4);
return v___x_196_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_april___closed__0(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_unsigned_to_nat(4u);
v___x_198_ = lean_nat_to_int(v___x_197_);
return v___x_198_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_april___closed__1(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_199_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_200_ = lean_obj_once(&l_Std_Time_Month_Ordinal_april___closed__0, &l_Std_Time_Month_Ordinal_april___closed__0_once, _init_l_Std_Time_Month_Ordinal_april___closed__0);
v___x_201_ = lean_int_sub(v___x_200_, v___x_199_);
return v___x_201_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_april___closed__2(void){
_start:
{
lean_object* v_range_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v_range_202_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_203_ = lean_obj_once(&l_Std_Time_Month_Ordinal_april___closed__1, &l_Std_Time_Month_Ordinal_april___closed__1_once, _init_l_Std_Time_Month_Ordinal_april___closed__1);
v___x_204_ = lean_int_emod(v___x_203_, v_range_202_);
return v___x_204_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_april___closed__3(void){
_start:
{
lean_object* v_range_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v_range_205_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_206_ = lean_obj_once(&l_Std_Time_Month_Ordinal_april___closed__2, &l_Std_Time_Month_Ordinal_april___closed__2_once, _init_l_Std_Time_Month_Ordinal_april___closed__2);
v___x_207_ = lean_int_add(v___x_206_, v_range_205_);
return v___x_207_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_april___closed__4(void){
_start:
{
lean_object* v_range_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_range_208_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_209_ = lean_obj_once(&l_Std_Time_Month_Ordinal_april___closed__3, &l_Std_Time_Month_Ordinal_april___closed__3_once, _init_l_Std_Time_Month_Ordinal_april___closed__3);
v___x_210_ = lean_int_emod(v___x_209_, v_range_208_);
return v___x_210_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_april___closed__5(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_211_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_212_ = lean_obj_once(&l_Std_Time_Month_Ordinal_april___closed__4, &l_Std_Time_Month_Ordinal_april___closed__4_once, _init_l_Std_Time_Month_Ordinal_april___closed__4);
v___x_213_ = lean_int_add(v___x_212_, v___x_211_);
return v___x_213_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_april(void){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = lean_obj_once(&l_Std_Time_Month_Ordinal_april___closed__5, &l_Std_Time_Month_Ordinal_april___closed__5_once, _init_l_Std_Time_Month_Ordinal_april___closed__5);
return v___x_214_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_may___closed__0(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_unsigned_to_nat(5u);
v___x_216_ = lean_nat_to_int(v___x_215_);
return v___x_216_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_may___closed__1(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_217_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_218_ = lean_obj_once(&l_Std_Time_Month_Ordinal_may___closed__0, &l_Std_Time_Month_Ordinal_may___closed__0_once, _init_l_Std_Time_Month_Ordinal_may___closed__0);
v___x_219_ = lean_int_sub(v___x_218_, v___x_217_);
return v___x_219_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_may___closed__2(void){
_start:
{
lean_object* v_range_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v_range_220_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_221_ = lean_obj_once(&l_Std_Time_Month_Ordinal_may___closed__1, &l_Std_Time_Month_Ordinal_may___closed__1_once, _init_l_Std_Time_Month_Ordinal_may___closed__1);
v___x_222_ = lean_int_emod(v___x_221_, v_range_220_);
return v___x_222_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_may___closed__3(void){
_start:
{
lean_object* v_range_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v_range_223_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_224_ = lean_obj_once(&l_Std_Time_Month_Ordinal_may___closed__2, &l_Std_Time_Month_Ordinal_may___closed__2_once, _init_l_Std_Time_Month_Ordinal_may___closed__2);
v___x_225_ = lean_int_add(v___x_224_, v_range_223_);
return v___x_225_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_may___closed__4(void){
_start:
{
lean_object* v_range_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v_range_226_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_227_ = lean_obj_once(&l_Std_Time_Month_Ordinal_may___closed__3, &l_Std_Time_Month_Ordinal_may___closed__3_once, _init_l_Std_Time_Month_Ordinal_may___closed__3);
v___x_228_ = lean_int_emod(v___x_227_, v_range_226_);
return v___x_228_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_may___closed__5(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_230_ = lean_obj_once(&l_Std_Time_Month_Ordinal_may___closed__4, &l_Std_Time_Month_Ordinal_may___closed__4_once, _init_l_Std_Time_Month_Ordinal_may___closed__4);
v___x_231_ = lean_int_add(v___x_230_, v___x_229_);
return v___x_231_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_may(void){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = lean_obj_once(&l_Std_Time_Month_Ordinal_may___closed__5, &l_Std_Time_Month_Ordinal_may___closed__5_once, _init_l_Std_Time_Month_Ordinal_may___closed__5);
return v___x_232_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_june___closed__0(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_unsigned_to_nat(6u);
v___x_234_ = lean_nat_to_int(v___x_233_);
return v___x_234_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_june___closed__1(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_235_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_236_ = lean_obj_once(&l_Std_Time_Month_Ordinal_june___closed__0, &l_Std_Time_Month_Ordinal_june___closed__0_once, _init_l_Std_Time_Month_Ordinal_june___closed__0);
v___x_237_ = lean_int_sub(v___x_236_, v___x_235_);
return v___x_237_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_june___closed__2(void){
_start:
{
lean_object* v_range_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_range_238_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_239_ = lean_obj_once(&l_Std_Time_Month_Ordinal_june___closed__1, &l_Std_Time_Month_Ordinal_june___closed__1_once, _init_l_Std_Time_Month_Ordinal_june___closed__1);
v___x_240_ = lean_int_emod(v___x_239_, v_range_238_);
return v___x_240_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_june___closed__3(void){
_start:
{
lean_object* v_range_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v_range_241_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_242_ = lean_obj_once(&l_Std_Time_Month_Ordinal_june___closed__2, &l_Std_Time_Month_Ordinal_june___closed__2_once, _init_l_Std_Time_Month_Ordinal_june___closed__2);
v___x_243_ = lean_int_add(v___x_242_, v_range_241_);
return v___x_243_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_june___closed__4(void){
_start:
{
lean_object* v_range_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v_range_244_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_245_ = lean_obj_once(&l_Std_Time_Month_Ordinal_june___closed__3, &l_Std_Time_Month_Ordinal_june___closed__3_once, _init_l_Std_Time_Month_Ordinal_june___closed__3);
v___x_246_ = lean_int_emod(v___x_245_, v_range_244_);
return v___x_246_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_june___closed__5(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_247_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_248_ = lean_obj_once(&l_Std_Time_Month_Ordinal_june___closed__4, &l_Std_Time_Month_Ordinal_june___closed__4_once, _init_l_Std_Time_Month_Ordinal_june___closed__4);
v___x_249_ = lean_int_add(v___x_248_, v___x_247_);
return v___x_249_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_june(void){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = lean_obj_once(&l_Std_Time_Month_Ordinal_june___closed__5, &l_Std_Time_Month_Ordinal_june___closed__5_once, _init_l_Std_Time_Month_Ordinal_june___closed__5);
return v___x_250_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_july___closed__0(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_unsigned_to_nat(7u);
v___x_252_ = lean_nat_to_int(v___x_251_);
return v___x_252_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_july___closed__1(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_253_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_254_ = lean_obj_once(&l_Std_Time_Month_Ordinal_july___closed__0, &l_Std_Time_Month_Ordinal_july___closed__0_once, _init_l_Std_Time_Month_Ordinal_july___closed__0);
v___x_255_ = lean_int_sub(v___x_254_, v___x_253_);
return v___x_255_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_july___closed__2(void){
_start:
{
lean_object* v_range_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_range_256_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_257_ = lean_obj_once(&l_Std_Time_Month_Ordinal_july___closed__1, &l_Std_Time_Month_Ordinal_july___closed__1_once, _init_l_Std_Time_Month_Ordinal_july___closed__1);
v___x_258_ = lean_int_emod(v___x_257_, v_range_256_);
return v___x_258_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_july___closed__3(void){
_start:
{
lean_object* v_range_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v_range_259_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_260_ = lean_obj_once(&l_Std_Time_Month_Ordinal_july___closed__2, &l_Std_Time_Month_Ordinal_july___closed__2_once, _init_l_Std_Time_Month_Ordinal_july___closed__2);
v___x_261_ = lean_int_add(v___x_260_, v_range_259_);
return v___x_261_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_july___closed__4(void){
_start:
{
lean_object* v_range_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v_range_262_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_263_ = lean_obj_once(&l_Std_Time_Month_Ordinal_july___closed__3, &l_Std_Time_Month_Ordinal_july___closed__3_once, _init_l_Std_Time_Month_Ordinal_july___closed__3);
v___x_264_ = lean_int_emod(v___x_263_, v_range_262_);
return v___x_264_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_july___closed__5(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_266_ = lean_obj_once(&l_Std_Time_Month_Ordinal_july___closed__4, &l_Std_Time_Month_Ordinal_july___closed__4_once, _init_l_Std_Time_Month_Ordinal_july___closed__4);
v___x_267_ = lean_int_add(v___x_266_, v___x_265_);
return v___x_267_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_july(void){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = lean_obj_once(&l_Std_Time_Month_Ordinal_july___closed__5, &l_Std_Time_Month_Ordinal_july___closed__5_once, _init_l_Std_Time_Month_Ordinal_july___closed__5);
return v___x_268_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_august___closed__0(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = lean_unsigned_to_nat(8u);
v___x_270_ = lean_nat_to_int(v___x_269_);
return v___x_270_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_august___closed__1(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_272_ = lean_obj_once(&l_Std_Time_Month_Ordinal_august___closed__0, &l_Std_Time_Month_Ordinal_august___closed__0_once, _init_l_Std_Time_Month_Ordinal_august___closed__0);
v___x_273_ = lean_int_sub(v___x_272_, v___x_271_);
return v___x_273_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_august___closed__2(void){
_start:
{
lean_object* v_range_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v_range_274_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_275_ = lean_obj_once(&l_Std_Time_Month_Ordinal_august___closed__1, &l_Std_Time_Month_Ordinal_august___closed__1_once, _init_l_Std_Time_Month_Ordinal_august___closed__1);
v___x_276_ = lean_int_emod(v___x_275_, v_range_274_);
return v___x_276_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_august___closed__3(void){
_start:
{
lean_object* v_range_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v_range_277_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_278_ = lean_obj_once(&l_Std_Time_Month_Ordinal_august___closed__2, &l_Std_Time_Month_Ordinal_august___closed__2_once, _init_l_Std_Time_Month_Ordinal_august___closed__2);
v___x_279_ = lean_int_add(v___x_278_, v_range_277_);
return v___x_279_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_august___closed__4(void){
_start:
{
lean_object* v_range_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v_range_280_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_281_ = lean_obj_once(&l_Std_Time_Month_Ordinal_august___closed__3, &l_Std_Time_Month_Ordinal_august___closed__3_once, _init_l_Std_Time_Month_Ordinal_august___closed__3);
v___x_282_ = lean_int_emod(v___x_281_, v_range_280_);
return v___x_282_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_august___closed__5(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_283_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_284_ = lean_obj_once(&l_Std_Time_Month_Ordinal_august___closed__4, &l_Std_Time_Month_Ordinal_august___closed__4_once, _init_l_Std_Time_Month_Ordinal_august___closed__4);
v___x_285_ = lean_int_add(v___x_284_, v___x_283_);
return v___x_285_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_august(void){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = lean_obj_once(&l_Std_Time_Month_Ordinal_august___closed__5, &l_Std_Time_Month_Ordinal_august___closed__5_once, _init_l_Std_Time_Month_Ordinal_august___closed__5);
return v___x_286_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_september___closed__0(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_unsigned_to_nat(9u);
v___x_288_ = lean_nat_to_int(v___x_287_);
return v___x_288_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_september___closed__1(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_289_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_290_ = lean_obj_once(&l_Std_Time_Month_Ordinal_september___closed__0, &l_Std_Time_Month_Ordinal_september___closed__0_once, _init_l_Std_Time_Month_Ordinal_september___closed__0);
v___x_291_ = lean_int_sub(v___x_290_, v___x_289_);
return v___x_291_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_september___closed__2(void){
_start:
{
lean_object* v_range_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v_range_292_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_293_ = lean_obj_once(&l_Std_Time_Month_Ordinal_september___closed__1, &l_Std_Time_Month_Ordinal_september___closed__1_once, _init_l_Std_Time_Month_Ordinal_september___closed__1);
v___x_294_ = lean_int_emod(v___x_293_, v_range_292_);
return v___x_294_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_september___closed__3(void){
_start:
{
lean_object* v_range_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v_range_295_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_296_ = lean_obj_once(&l_Std_Time_Month_Ordinal_september___closed__2, &l_Std_Time_Month_Ordinal_september___closed__2_once, _init_l_Std_Time_Month_Ordinal_september___closed__2);
v___x_297_ = lean_int_add(v___x_296_, v_range_295_);
return v___x_297_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_september___closed__4(void){
_start:
{
lean_object* v_range_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v_range_298_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_299_ = lean_obj_once(&l_Std_Time_Month_Ordinal_september___closed__3, &l_Std_Time_Month_Ordinal_september___closed__3_once, _init_l_Std_Time_Month_Ordinal_september___closed__3);
v___x_300_ = lean_int_emod(v___x_299_, v_range_298_);
return v___x_300_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_september___closed__5(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_301_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_302_ = lean_obj_once(&l_Std_Time_Month_Ordinal_september___closed__4, &l_Std_Time_Month_Ordinal_september___closed__4_once, _init_l_Std_Time_Month_Ordinal_september___closed__4);
v___x_303_ = lean_int_add(v___x_302_, v___x_301_);
return v___x_303_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_september(void){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = lean_obj_once(&l_Std_Time_Month_Ordinal_september___closed__5, &l_Std_Time_Month_Ordinal_september___closed__5_once, _init_l_Std_Time_Month_Ordinal_september___closed__5);
return v___x_304_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_october___closed__0(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = lean_unsigned_to_nat(10u);
v___x_306_ = lean_nat_to_int(v___x_305_);
return v___x_306_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_october___closed__1(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_307_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_308_ = lean_obj_once(&l_Std_Time_Month_Ordinal_october___closed__0, &l_Std_Time_Month_Ordinal_october___closed__0_once, _init_l_Std_Time_Month_Ordinal_october___closed__0);
v___x_309_ = lean_int_sub(v___x_308_, v___x_307_);
return v___x_309_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_october___closed__2(void){
_start:
{
lean_object* v_range_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v_range_310_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_311_ = lean_obj_once(&l_Std_Time_Month_Ordinal_october___closed__1, &l_Std_Time_Month_Ordinal_october___closed__1_once, _init_l_Std_Time_Month_Ordinal_october___closed__1);
v___x_312_ = lean_int_emod(v___x_311_, v_range_310_);
return v___x_312_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_october___closed__3(void){
_start:
{
lean_object* v_range_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v_range_313_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_314_ = lean_obj_once(&l_Std_Time_Month_Ordinal_october___closed__2, &l_Std_Time_Month_Ordinal_october___closed__2_once, _init_l_Std_Time_Month_Ordinal_october___closed__2);
v___x_315_ = lean_int_add(v___x_314_, v_range_313_);
return v___x_315_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_october___closed__4(void){
_start:
{
lean_object* v_range_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v_range_316_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_317_ = lean_obj_once(&l_Std_Time_Month_Ordinal_october___closed__3, &l_Std_Time_Month_Ordinal_october___closed__3_once, _init_l_Std_Time_Month_Ordinal_october___closed__3);
v___x_318_ = lean_int_emod(v___x_317_, v_range_316_);
return v___x_318_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_october___closed__5(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_320_ = lean_obj_once(&l_Std_Time_Month_Ordinal_october___closed__4, &l_Std_Time_Month_Ordinal_october___closed__4_once, _init_l_Std_Time_Month_Ordinal_october___closed__4);
v___x_321_ = lean_int_add(v___x_320_, v___x_319_);
return v___x_321_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_october(void){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = lean_obj_once(&l_Std_Time_Month_Ordinal_october___closed__5, &l_Std_Time_Month_Ordinal_october___closed__5_once, _init_l_Std_Time_Month_Ordinal_october___closed__5);
return v___x_322_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_november___closed__0(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_323_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_324_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__0, &l_Std_Time_Month_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__0);
v___x_325_ = lean_int_sub(v___x_324_, v___x_323_);
return v___x_325_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_november___closed__1(void){
_start:
{
lean_object* v_range_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v_range_326_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_327_ = lean_obj_once(&l_Std_Time_Month_Ordinal_november___closed__0, &l_Std_Time_Month_Ordinal_november___closed__0_once, _init_l_Std_Time_Month_Ordinal_november___closed__0);
v___x_328_ = lean_int_emod(v___x_327_, v_range_326_);
return v___x_328_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_november___closed__2(void){
_start:
{
lean_object* v_range_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_range_329_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_330_ = lean_obj_once(&l_Std_Time_Month_Ordinal_november___closed__1, &l_Std_Time_Month_Ordinal_november___closed__1_once, _init_l_Std_Time_Month_Ordinal_november___closed__1);
v___x_331_ = lean_int_add(v___x_330_, v_range_329_);
return v___x_331_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_november___closed__3(void){
_start:
{
lean_object* v_range_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v_range_332_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_333_ = lean_obj_once(&l_Std_Time_Month_Ordinal_november___closed__2, &l_Std_Time_Month_Ordinal_november___closed__2_once, _init_l_Std_Time_Month_Ordinal_november___closed__2);
v___x_334_ = lean_int_emod(v___x_333_, v_range_332_);
return v___x_334_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_november___closed__4(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_335_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_336_ = lean_obj_once(&l_Std_Time_Month_Ordinal_november___closed__3, &l_Std_Time_Month_Ordinal_november___closed__3_once, _init_l_Std_Time_Month_Ordinal_november___closed__3);
v___x_337_ = lean_int_add(v___x_336_, v___x_335_);
return v___x_337_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_november(void){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = lean_obj_once(&l_Std_Time_Month_Ordinal_november___closed__4, &l_Std_Time_Month_Ordinal_november___closed__4_once, _init_l_Std_Time_Month_Ordinal_november___closed__4);
return v___x_338_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_december___closed__0(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_unsigned_to_nat(12u);
v___x_340_ = lean_nat_to_int(v___x_339_);
return v___x_340_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_december___closed__1(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_341_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_342_ = lean_obj_once(&l_Std_Time_Month_Ordinal_december___closed__0, &l_Std_Time_Month_Ordinal_december___closed__0_once, _init_l_Std_Time_Month_Ordinal_december___closed__0);
v___x_343_ = lean_int_sub(v___x_342_, v___x_341_);
return v___x_343_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_december___closed__2(void){
_start:
{
lean_object* v_range_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_range_344_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_345_ = lean_obj_once(&l_Std_Time_Month_Ordinal_december___closed__1, &l_Std_Time_Month_Ordinal_december___closed__1_once, _init_l_Std_Time_Month_Ordinal_december___closed__1);
v___x_346_ = lean_int_emod(v___x_345_, v_range_344_);
return v___x_346_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_december___closed__3(void){
_start:
{
lean_object* v_range_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_range_347_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_348_ = lean_obj_once(&l_Std_Time_Month_Ordinal_december___closed__2, &l_Std_Time_Month_Ordinal_december___closed__2_once, _init_l_Std_Time_Month_Ordinal_december___closed__2);
v___x_349_ = lean_int_add(v___x_348_, v_range_347_);
return v___x_349_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_december___closed__4(void){
_start:
{
lean_object* v_range_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_range_350_ = lean_obj_once(&l_Std_Time_Month_instInhabitedOrdinal___closed__3, &l_Std_Time_Month_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3);
v___x_351_ = lean_obj_once(&l_Std_Time_Month_Ordinal_december___closed__3, &l_Std_Time_Month_Ordinal_december___closed__3_once, _init_l_Std_Time_Month_Ordinal_december___closed__3);
v___x_352_ = lean_int_emod(v___x_351_, v_range_350_);
return v___x_352_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_december___closed__5(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_353_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_354_ = lean_obj_once(&l_Std_Time_Month_Ordinal_december___closed__4, &l_Std_Time_Month_Ordinal_december___closed__4_once, _init_l_Std_Time_Month_Ordinal_december___closed__4);
v___x_355_ = lean_int_add(v___x_354_, v___x_353_);
return v___x_355_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_december(void){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = lean_obj_once(&l_Std_Time_Month_Ordinal_december___closed__5, &l_Std_Time_Month_Ordinal_december___closed__5_once, _init_l_Std_Time_Month_Ordinal_december___closed__5);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toOffset(lean_object* v_month_357_){
_start:
{
lean_inc(v_month_357_);
return v_month_357_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toOffset___boxed(lean_object* v_month_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Std_Time_Month_Ordinal_toOffset(v_month_358_);
lean_dec(v_month_358_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_ofInt___redArg(lean_object* v_data_360_){
_start:
{
lean_inc(v_data_360_);
return v_data_360_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_ofInt___redArg___boxed(lean_object* v_data_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Std_Time_Month_Ordinal_ofInt___redArg(v_data_361_);
lean_dec(v_data_361_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_ofInt(lean_object* v_data_363_, lean_object* v_h_364_){
_start:
{
lean_inc(v_data_363_);
return v_data_363_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_ofInt___boxed(lean_object* v_data_365_, lean_object* v_h_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Std_Time_Month_Ordinal_ofInt(v_data_365_, v_h_366_);
lean_dec(v_data_365_);
return v_res_367_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__12(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__10));
v___x_395_ = l_Lean_mkAtom(v___x_394_);
return v___x_395_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__13(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_396_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__12, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__12_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__12);
v___x_397_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5));
v___x_398_ = lean_array_push(v___x_397_, v___x_396_);
return v___x_398_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__17(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_409_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__16));
v___x_410_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5));
v___x_411_ = lean_array_push(v___x_410_, v___x_409_);
return v___x_411_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__18(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_412_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__17, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__17_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__17);
v___x_413_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15));
v___x_414_ = lean_box(2);
v___x_415_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
lean_ctor_set(v___x_415_, 1, v___x_413_);
lean_ctor_set(v___x_415_, 2, v___x_412_);
return v___x_415_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__19(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_416_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__18, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__18_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__18);
v___x_417_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__13, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__13_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__13);
v___x_418_ = lean_array_push(v___x_417_, v___x_416_);
return v___x_418_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__20(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_419_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__19, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__19_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__19);
v___x_420_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11));
v___x_421_ = lean_box(2);
v___x_422_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v___x_420_);
lean_ctor_set(v___x_422_, 2, v___x_419_);
return v___x_422_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__21(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_423_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__20, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__20_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__20);
v___x_424_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5));
v___x_425_ = lean_array_push(v___x_424_, v___x_423_);
return v___x_425_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__22(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_426_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__21, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__21_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__21);
v___x_427_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__9));
v___x_428_ = lean_box(2);
v___x_429_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v___x_427_);
lean_ctor_set(v___x_429_, 2, v___x_426_);
return v___x_429_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__23(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_430_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__22, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__22_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__22);
v___x_431_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5));
v___x_432_ = lean_array_push(v___x_431_, v___x_430_);
return v___x_432_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__24(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_433_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__23, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__23_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__23);
v___x_434_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7));
v___x_435_ = lean_box(2);
v___x_436_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
lean_ctor_set(v___x_436_, 1, v___x_434_);
lean_ctor_set(v___x_436_, 2, v___x_433_);
return v___x_436_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__25(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_437_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__24, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__24_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__24);
v___x_438_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5));
v___x_439_ = lean_array_push(v___x_438_, v___x_437_);
return v___x_439_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__26(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_440_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__25, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__25_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__25);
v___x_441_ = ((lean_object*)(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4));
v___x_442_ = lean_box(2);
v___x_443_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
lean_ctor_set(v___x_443_, 1, v___x_441_);
lean_ctor_set(v___x_443_, 2, v___x_440_);
return v___x_443_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofNat___auto__1(void){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__26, &l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__26_once, _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__26);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_ofNat___redArg(lean_object* v_data_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = lean_nat_to_int(v_data_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_ofNat(lean_object* v_data_447_, lean_object* v_h_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = lean_nat_to_int(v_data_447_);
return v___x_449_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toNat___closed__0(void){
_start:
{
lean_object* v_natZero_450_; lean_object* v_intZero_451_; 
v_natZero_450_ = lean_unsigned_to_nat(0u);
v_intZero_451_ = lean_nat_to_int(v_natZero_450_);
return v_intZero_451_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toNat(lean_object* v_month_452_){
_start:
{
lean_object* v_intZero_453_; uint8_t v_isNeg_454_; lean_object* v_a_455_; 
v_intZero_453_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toNat___closed__0, &l_Std_Time_Month_Ordinal_toNat___closed__0_once, _init_l_Std_Time_Month_Ordinal_toNat___closed__0);
v_isNeg_454_ = lean_int_dec_lt(v_month_452_, v_intZero_453_);
v_a_455_ = lean_nat_abs(v_month_452_);
return v_a_455_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toNat___boxed(lean_object* v_month_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Std_Time_Month_Ordinal_toNat(v_month_456_);
lean_dec(v_month_456_);
return v_res_457_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_ofFin___closed__0(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = lean_unsigned_to_nat(1u);
v___x_459_ = lean_nat_to_int(v___x_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_ofFin(lean_object* v_data_460_){
_start:
{
lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_461_ = lean_unsigned_to_nat(1u);
v___x_462_ = lean_nat_dec_le(v___x_461_, v_data_460_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; 
lean_dec(v_data_460_);
v___x_463_ = lean_obj_once(&l_Std_Time_Month_Ordinal_ofFin___closed__0, &l_Std_Time_Month_Ordinal_ofFin___closed__0_once, _init_l_Std_Time_Month_Ordinal_ofFin___closed__0);
return v___x_463_;
}
else
{
lean_object* v___x_464_; 
v___x_464_ = lean_nat_to_int(v_data_460_);
return v___x_464_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Month_Ordinal_toSeconds_spec__1(lean_object* v_a_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = lean_nat_to_int(v_a_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Std_Time_Month_Ordinal_toSeconds_spec__2(lean_object* v_a_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Rat_ofInt(v_a_467_);
return v___x_468_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__0(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = lean_unsigned_to_nat(31u);
v___x_470_ = lean_nat_to_int(v___x_469_);
return v___x_470_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__1(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = lean_unsigned_to_nat(59u);
v___x_472_ = lean_nat_to_int(v___x_471_);
return v___x_472_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__2(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_unsigned_to_nat(90u);
v___x_474_ = lean_nat_to_int(v___x_473_);
return v___x_474_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__3(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = lean_unsigned_to_nat(120u);
v___x_476_ = lean_nat_to_int(v___x_475_);
return v___x_476_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__4(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_unsigned_to_nat(151u);
v___x_478_ = lean_nat_to_int(v___x_477_);
return v___x_478_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__5(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_unsigned_to_nat(181u);
v___x_480_ = lean_nat_to_int(v___x_479_);
return v___x_480_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__6(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_unsigned_to_nat(212u);
v___x_482_ = lean_nat_to_int(v___x_481_);
return v___x_482_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__7(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_unsigned_to_nat(243u);
v___x_484_ = lean_nat_to_int(v___x_483_);
return v___x_484_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__8(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_unsigned_to_nat(273u);
v___x_486_ = lean_nat_to_int(v___x_485_);
return v___x_486_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__9(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = lean_unsigned_to_nat(304u);
v___x_488_ = lean_nat_to_int(v___x_487_);
return v___x_488_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__10(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_unsigned_to_nat(334u);
v___x_490_ = lean_nat_to_int(v___x_489_);
return v___x_490_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__11(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v_intZero_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v_daysAcc_516_; 
v___x_491_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__10, &l_Std_Time_Month_Ordinal_toSeconds___closed__10_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__10);
v___x_492_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__9, &l_Std_Time_Month_Ordinal_toSeconds___closed__9_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__9);
v___x_493_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__8, &l_Std_Time_Month_Ordinal_toSeconds___closed__8_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__8);
v___x_494_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__7, &l_Std_Time_Month_Ordinal_toSeconds___closed__7_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__7);
v___x_495_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__6, &l_Std_Time_Month_Ordinal_toSeconds___closed__6_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__6);
v___x_496_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__5, &l_Std_Time_Month_Ordinal_toSeconds___closed__5_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__5);
v___x_497_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__4, &l_Std_Time_Month_Ordinal_toSeconds___closed__4_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__4);
v___x_498_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__3, &l_Std_Time_Month_Ordinal_toSeconds___closed__3_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__3);
v___x_499_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__2, &l_Std_Time_Month_Ordinal_toSeconds___closed__2_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__2);
v___x_500_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__1, &l_Std_Time_Month_Ordinal_toSeconds___closed__1_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__1);
v___x_501_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__0, &l_Std_Time_Month_Ordinal_toSeconds___closed__0_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__0);
v_intZero_502_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toNat___closed__0, &l_Std_Time_Month_Ordinal_toNat___closed__0_once, _init_l_Std_Time_Month_Ordinal_toNat___closed__0);
v___x_503_ = lean_unsigned_to_nat(12u);
v___x_504_ = lean_mk_empty_array_with_capacity(v___x_503_);
v___x_505_ = lean_array_push(v___x_504_, v_intZero_502_);
v___x_506_ = lean_array_push(v___x_505_, v___x_501_);
v___x_507_ = lean_array_push(v___x_506_, v___x_500_);
v___x_508_ = lean_array_push(v___x_507_, v___x_499_);
v___x_509_ = lean_array_push(v___x_508_, v___x_498_);
v___x_510_ = lean_array_push(v___x_509_, v___x_497_);
v___x_511_ = lean_array_push(v___x_510_, v___x_496_);
v___x_512_ = lean_array_push(v___x_511_, v___x_495_);
v___x_513_ = lean_array_push(v___x_512_, v___x_494_);
v___x_514_ = lean_array_push(v___x_513_, v___x_493_);
v___x_515_ = lean_array_push(v___x_514_, v___x_492_);
v_daysAcc_516_ = lean_array_push(v___x_515_, v___x_491_);
return v_daysAcc_516_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toSeconds___closed__12(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_unsigned_to_nat(86400u);
v___x_518_ = lean_nat_to_int(v___x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toSeconds(uint8_t v_leap_519_, lean_object* v_month_520_){
_start:
{
lean_object* v_intZero_521_; uint8_t v_isNeg_522_; lean_object* v___x_523_; lean_object* v_a_524_; lean_object* v_daysAcc_525_; lean_object* v_days_526_; lean_object* v___x_527_; lean_object* v_time_528_; 
v_intZero_521_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toNat___closed__0, &l_Std_Time_Month_Ordinal_toNat___closed__0_once, _init_l_Std_Time_Month_Ordinal_toNat___closed__0);
v_isNeg_522_ = lean_int_dec_lt(v_month_520_, v_intZero_521_);
v___x_523_ = l_Std_Time_Day_instInhabitedOffset;
v_a_524_ = lean_nat_abs(v_month_520_);
v_daysAcc_525_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__11, &l_Std_Time_Month_Ordinal_toSeconds___closed__11_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__11);
v_days_526_ = lean_array_get(v___x_523_, v_daysAcc_525_, v_a_524_);
v___x_527_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__12, &l_Std_Time_Month_Ordinal_toSeconds___closed__12_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__12);
v_time_528_ = lean_int_mul(v_days_526_, v___x_527_);
lean_dec(v_days_526_);
if (v_leap_519_ == 0)
{
lean_dec(v_a_524_);
return v_time_528_;
}
else
{
lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_529_ = lean_unsigned_to_nat(2u);
v___x_530_ = lean_nat_dec_le(v___x_529_, v_a_524_);
lean_dec(v_a_524_);
if (v___x_530_ == 0)
{
return v_time_528_;
}
else
{
lean_object* v___x_323__overap_531_; lean_object* v___x_532_; 
v___x_323__overap_531_ = l_Std_Time_Second_instAddOffset;
v___x_532_ = lean_apply_2(v___x_323__overap_531_, v_time_528_, v___x_527_);
return v___x_532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toSeconds___boxed(lean_object* v_leap_533_, lean_object* v_month_534_){
_start:
{
uint8_t v_leap_boxed_535_; lean_object* v_res_536_; 
v_leap_boxed_535_ = lean_unbox(v_leap_533_);
v_res_536_ = l_Std_Time_Month_Ordinal_toSeconds(v_leap_boxed_535_, v_month_534_);
lean_dec(v_month_534_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Month_Ordinal_toSeconds_spec__0(lean_object* v_a_537_){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = lean_nat_to_int(v_a_537_);
v___x_539_ = l_Rat_ofInt(v___x_538_);
return v___x_539_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toMinutes___closed__0(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = lean_unsigned_to_nat(60u);
v___x_541_ = lean_nat_to_int(v___x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toMinutes(uint8_t v_leap_542_, lean_object* v_month_543_){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_544_ = l_Std_Time_Month_Ordinal_toSeconds(v_leap_542_, v_month_543_);
v___x_545_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toMinutes___closed__0, &l_Std_Time_Month_Ordinal_toMinutes___closed__0_once, _init_l_Std_Time_Month_Ordinal_toMinutes___closed__0);
v___x_546_ = lean_int_div(v___x_544_, v___x_545_);
lean_dec(v___x_544_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toMinutes___boxed(lean_object* v_leap_547_, lean_object* v_month_548_){
_start:
{
uint8_t v_leap_boxed_549_; lean_object* v_res_550_; 
v_leap_boxed_549_ = lean_unbox(v_leap_547_);
v_res_550_ = l_Std_Time_Month_Ordinal_toMinutes(v_leap_boxed_549_, v_month_548_);
lean_dec(v_month_548_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toHours(uint8_t v_leap_551_, lean_object* v_month_552_){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_553_ = l_Std_Time_Month_Ordinal_toSeconds(v_leap_551_, v_month_552_);
v___x_554_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toMinutes___closed__0, &l_Std_Time_Month_Ordinal_toMinutes___closed__0_once, _init_l_Std_Time_Month_Ordinal_toMinutes___closed__0);
v___x_555_ = lean_int_div(v___x_553_, v___x_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_int_div(v___x_555_, v___x_554_);
lean_dec(v___x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toHours___boxed(lean_object* v_leap_557_, lean_object* v_month_558_){
_start:
{
uint8_t v_leap_boxed_559_; lean_object* v_res_560_; 
v_leap_boxed_559_ = lean_unbox(v_leap_557_);
v_res_560_ = l_Std_Time_Month_Ordinal_toHours(v_leap_boxed_559_, v_month_558_);
lean_dec(v_month_558_);
return v_res_560_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toDays___closed__0(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = lean_unsigned_to_nat(1u);
v___x_562_ = l_Rat_instNatCast___lam__0(v___x_561_);
return v___x_562_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toDays___closed__1(void){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = lean_unsigned_to_nat(86400u);
v___x_564_ = l_Rat_instNatCast___lam__0(v___x_563_);
return v___x_564_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_toDays___closed__2(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v_ratio_567_; 
v___x_565_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toDays___closed__1, &l_Std_Time_Month_Ordinal_toDays___closed__1_once, _init_l_Std_Time_Month_Ordinal_toDays___closed__1);
v___x_566_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toDays___closed__0, &l_Std_Time_Month_Ordinal_toDays___closed__0_once, _init_l_Std_Time_Month_Ordinal_toDays___closed__0);
v_ratio_567_ = l_Rat_div(v___x_566_, v___x_565_);
return v_ratio_567_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toDays(uint8_t v_leap_568_, lean_object* v_month_569_){
_start:
{
lean_object* v_ratio_570_; lean_object* v_num_571_; lean_object* v_den_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v_ratio_570_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toDays___closed__2, &l_Std_Time_Month_Ordinal_toDays___closed__2_once, _init_l_Std_Time_Month_Ordinal_toDays___closed__2);
v_num_571_ = lean_ctor_get(v_ratio_570_, 0);
lean_inc(v_num_571_);
v_den_572_ = lean_ctor_get(v_ratio_570_, 1);
lean_inc(v_den_572_);
v___x_573_ = l_Std_Time_Month_Ordinal_toSeconds(v_leap_568_, v_month_569_);
v___x_574_ = lean_int_mul(v___x_573_, v_num_571_);
lean_dec(v_num_571_);
lean_dec(v___x_573_);
v___x_575_ = lean_nat_to_int(v_den_572_);
v___x_576_ = lean_int_ediv(v___x_574_, v___x_575_);
lean_dec(v___x_575_);
lean_dec(v___x_574_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_toDays___boxed(lean_object* v_leap_577_, lean_object* v_month_578_){
_start:
{
uint8_t v_leap_boxed_579_; lean_object* v_res_580_; 
v_leap_boxed_579_ = lean_unbox(v_leap_577_);
v_res_580_ = l_Std_Time_Month_Ordinal_toDays(v_leap_boxed_579_, v_month_578_);
lean_dec(v_month_578_);
return v_res_580_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = lean_unsigned_to_nat(30u);
v___x_582_ = lean_nat_to_int(v___x_581_);
return v___x_582_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__1(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_583_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0);
v___x_584_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_585_ = lean_int_add(v___x_584_, v___x_583_);
return v___x_585_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(31u);
v___x_587_ = lean_nat_to_int(v___x_586_);
return v___x_587_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__3(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_588_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_589_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__1, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__1_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__1);
v___x_590_ = lean_int_sub(v___x_589_, v___x_588_);
return v___x_590_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v_range_593_; 
v___x_591_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_592_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__3, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__3_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__3);
v_range_593_ = lean_int_add(v___x_592_, v___x_591_);
return v_range_593_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__5(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_594_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_595_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2);
v___x_596_ = lean_int_sub(v___x_595_, v___x_594_);
return v___x_596_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__6(void){
_start:
{
lean_object* v_range_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v_range_597_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
v___x_598_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__5, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__5_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__5);
v___x_599_ = lean_int_emod(v___x_598_, v_range_597_);
return v___x_599_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__7(void){
_start:
{
lean_object* v_range_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v_range_600_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
v___x_601_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__6, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__6_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__6);
v___x_602_ = lean_int_add(v___x_601_, v_range_600_);
return v___x_602_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__8(void){
_start:
{
lean_object* v_range_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v_range_603_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
v___x_604_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__7, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__7_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__7);
v___x_605_ = lean_int_emod(v___x_604_, v_range_603_);
return v___x_605_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__9(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_606_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_607_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__8, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__8_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__8);
v___x_608_ = lean_int_add(v___x_607_, v___x_606_);
return v___x_608_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__10(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_unsigned_to_nat(28u);
v___x_610_ = lean_nat_to_int(v___x_609_);
return v___x_610_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__11(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_611_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_612_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__10, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__10_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__10);
v___x_613_ = lean_int_sub(v___x_612_, v___x_611_);
return v___x_613_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__12(void){
_start:
{
lean_object* v_range_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v_range_614_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
v___x_615_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__11, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__11_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__11);
v___x_616_ = lean_int_emod(v___x_615_, v_range_614_);
return v___x_616_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__13(void){
_start:
{
lean_object* v_range_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v_range_617_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
v___x_618_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__12, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__12_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__12);
v___x_619_ = lean_int_add(v___x_618_, v_range_617_);
return v___x_619_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__14(void){
_start:
{
lean_object* v_range_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v_range_620_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
v___x_621_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__13, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__13_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__13);
v___x_622_ = lean_int_emod(v___x_621_, v_range_620_);
return v___x_622_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__15(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_623_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_624_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__14, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__14_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__14);
v___x_625_ = lean_int_add(v___x_624_, v___x_623_);
return v___x_625_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__16(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_626_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_627_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0);
v___x_628_ = lean_int_sub(v___x_627_, v___x_626_);
return v___x_628_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__17(void){
_start:
{
lean_object* v_range_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v_range_629_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
v___x_630_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__16, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__16_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__16);
v___x_631_ = lean_int_emod(v___x_630_, v_range_629_);
return v___x_631_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__18(void){
_start:
{
lean_object* v_range_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v_range_632_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
v___x_633_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__17, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__17_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__17);
v___x_634_ = lean_int_add(v___x_633_, v_range_632_);
return v___x_634_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__19(void){
_start:
{
lean_object* v_range_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v_range_635_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
v___x_636_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__18, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__18_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__18);
v___x_637_ = lean_int_emod(v___x_636_, v_range_635_);
return v___x_637_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__20(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_638_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_639_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__19, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__19_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__19);
v___x_640_ = lean_int_add(v___x_639_, v___x_638_);
return v___x_640_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__21(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_641_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__20, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__20_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__20);
v___x_642_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__15, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__15_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__15);
v___x_643_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__9, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__9_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__9);
v___x_644_ = lean_unsigned_to_nat(12u);
v___x_645_ = lean_mk_empty_array_with_capacity(v___x_644_);
v___x_646_ = lean_array_push(v___x_645_, v___x_643_);
v___x_647_ = lean_array_push(v___x_646_, v___x_642_);
v___x_648_ = lean_array_push(v___x_647_, v___x_643_);
v___x_649_ = lean_array_push(v___x_648_, v___x_641_);
v___x_650_ = lean_array_push(v___x_649_, v___x_643_);
v___x_651_ = lean_array_push(v___x_650_, v___x_641_);
v___x_652_ = lean_array_push(v___x_651_, v___x_643_);
v___x_653_ = lean_array_push(v___x_652_, v___x_643_);
v___x_654_ = lean_array_push(v___x_653_, v___x_641_);
v___x_655_ = lean_array_push(v___x_654_, v___x_643_);
v___x_656_ = lean_array_push(v___x_655_, v___x_641_);
v___x_657_ = lean_array_push(v___x_656_, v___x_643_);
return v___x_657_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap(void){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__21, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__21_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__21);
return v___x_658_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__0(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_unsigned_to_nat(0u);
v___x_660_ = lean_nat_to_int(v___x_659_);
return v___x_660_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__1(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = lean_unsigned_to_nat(59u);
v___x_662_ = lean_nat_to_int(v___x_661_);
return v___x_662_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__2(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = lean_unsigned_to_nat(90u);
v___x_664_ = lean_nat_to_int(v___x_663_);
return v___x_664_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__3(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_unsigned_to_nat(120u);
v___x_666_ = lean_nat_to_int(v___x_665_);
return v___x_666_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__4(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_unsigned_to_nat(151u);
v___x_668_ = lean_nat_to_int(v___x_667_);
return v___x_668_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__5(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = lean_unsigned_to_nat(181u);
v___x_670_ = lean_nat_to_int(v___x_669_);
return v___x_670_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__6(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_unsigned_to_nat(212u);
v___x_672_ = lean_nat_to_int(v___x_671_);
return v___x_672_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__7(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_unsigned_to_nat(243u);
v___x_674_ = lean_nat_to_int(v___x_673_);
return v___x_674_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__8(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = lean_unsigned_to_nat(273u);
v___x_676_ = lean_nat_to_int(v___x_675_);
return v___x_676_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__9(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = lean_unsigned_to_nat(304u);
v___x_678_ = lean_nat_to_int(v___x_677_);
return v___x_678_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__10(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = lean_unsigned_to_nat(334u);
v___x_680_ = lean_nat_to_int(v___x_679_);
return v___x_680_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__11(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_681_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__10, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__10_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__10);
v___x_682_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__9, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__9_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__9);
v___x_683_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__8, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__8_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__8);
v___x_684_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__7, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__7_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__7);
v___x_685_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__6, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__6_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__6);
v___x_686_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__5, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__5_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__5);
v___x_687_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__4, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__4_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__4);
v___x_688_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__3, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__3_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__3);
v___x_689_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__2, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__2_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__2);
v___x_690_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__1, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__1_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__1);
v___x_691_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2);
v___x_692_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__0, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__0_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__0);
v___x_693_ = lean_unsigned_to_nat(12u);
v___x_694_ = lean_mk_empty_array_with_capacity(v___x_693_);
v___x_695_ = lean_array_push(v___x_694_, v___x_692_);
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
v___x_706_ = lean_array_push(v___x_705_, v___x_681_);
return v___x_706_;
}
}
static lean_object* _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes(void){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = lean_obj_once(&l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__11, &l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__11_once, _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__11);
return v___x_707_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__0(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = lean_unsigned_to_nat(2u);
v___x_709_ = lean_nat_to_int(v___x_708_);
return v___x_709_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__1(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_unsigned_to_nat(30u);
v___x_711_ = lean_nat_to_int(v___x_710_);
return v___x_711_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__2(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_712_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__1, &l_Std_Time_Month_Ordinal_days___closed__1_once, _init_l_Std_Time_Month_Ordinal_days___closed__1);
v___x_713_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_714_ = lean_int_add(v___x_713_, v___x_712_);
return v___x_714_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__3(void){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_715_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_716_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__2, &l_Std_Time_Month_Ordinal_days___closed__2_once, _init_l_Std_Time_Month_Ordinal_days___closed__2);
v___x_717_ = lean_int_sub(v___x_716_, v___x_715_);
return v___x_717_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__4(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v_range_720_; 
v___x_718_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_719_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__3, &l_Std_Time_Month_Ordinal_days___closed__3_once, _init_l_Std_Time_Month_Ordinal_days___closed__3);
v_range_720_ = lean_int_add(v___x_719_, v___x_718_);
return v_range_720_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__5(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_721_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_722_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__0, &l_Std_Time_Month_Ordinal_toSeconds___closed__0_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__0);
v___x_723_ = lean_int_sub(v___x_722_, v___x_721_);
return v___x_723_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__6(void){
_start:
{
lean_object* v_range_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v_range_724_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_725_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__5, &l_Std_Time_Month_Ordinal_days___closed__5_once, _init_l_Std_Time_Month_Ordinal_days___closed__5);
v___x_726_ = lean_int_emod(v___x_725_, v_range_724_);
return v___x_726_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__7(void){
_start:
{
lean_object* v_range_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v_range_727_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_728_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__6, &l_Std_Time_Month_Ordinal_days___closed__6_once, _init_l_Std_Time_Month_Ordinal_days___closed__6);
v___x_729_ = lean_int_add(v___x_728_, v_range_727_);
return v___x_729_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__8(void){
_start:
{
lean_object* v_range_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v_range_730_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_731_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__7, &l_Std_Time_Month_Ordinal_days___closed__7_once, _init_l_Std_Time_Month_Ordinal_days___closed__7);
v___x_732_ = lean_int_emod(v___x_731_, v_range_730_);
return v___x_732_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__9(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_733_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_734_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__8, &l_Std_Time_Month_Ordinal_days___closed__8_once, _init_l_Std_Time_Month_Ordinal_days___closed__8);
v___x_735_ = lean_int_add(v___x_734_, v___x_733_);
return v___x_735_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__10(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = lean_unsigned_to_nat(28u);
v___x_737_ = lean_nat_to_int(v___x_736_);
return v___x_737_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__11(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_738_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_739_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__10, &l_Std_Time_Month_Ordinal_days___closed__10_once, _init_l_Std_Time_Month_Ordinal_days___closed__10);
v___x_740_ = lean_int_sub(v___x_739_, v___x_738_);
return v___x_740_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__12(void){
_start:
{
lean_object* v_range_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_range_741_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_742_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__11, &l_Std_Time_Month_Ordinal_days___closed__11_once, _init_l_Std_Time_Month_Ordinal_days___closed__11);
v___x_743_ = lean_int_emod(v___x_742_, v_range_741_);
return v___x_743_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__13(void){
_start:
{
lean_object* v_range_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v_range_744_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_745_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__12, &l_Std_Time_Month_Ordinal_days___closed__12_once, _init_l_Std_Time_Month_Ordinal_days___closed__12);
v___x_746_ = lean_int_add(v___x_745_, v_range_744_);
return v___x_746_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__14(void){
_start:
{
lean_object* v_range_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v_range_747_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_748_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__13, &l_Std_Time_Month_Ordinal_days___closed__13_once, _init_l_Std_Time_Month_Ordinal_days___closed__13);
v___x_749_ = lean_int_emod(v___x_748_, v_range_747_);
return v___x_749_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__15(void){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_750_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_751_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__14, &l_Std_Time_Month_Ordinal_days___closed__14_once, _init_l_Std_Time_Month_Ordinal_days___closed__14);
v___x_752_ = lean_int_add(v___x_751_, v___x_750_);
return v___x_752_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__16(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_753_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_754_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__1, &l_Std_Time_Month_Ordinal_days___closed__1_once, _init_l_Std_Time_Month_Ordinal_days___closed__1);
v___x_755_ = lean_int_sub(v___x_754_, v___x_753_);
return v___x_755_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__17(void){
_start:
{
lean_object* v_range_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v_range_756_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_757_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__16, &l_Std_Time_Month_Ordinal_days___closed__16_once, _init_l_Std_Time_Month_Ordinal_days___closed__16);
v___x_758_ = lean_int_emod(v___x_757_, v_range_756_);
return v___x_758_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__18(void){
_start:
{
lean_object* v_range_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v_range_759_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_760_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__17, &l_Std_Time_Month_Ordinal_days___closed__17_once, _init_l_Std_Time_Month_Ordinal_days___closed__17);
v___x_761_ = lean_int_add(v___x_760_, v_range_759_);
return v___x_761_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__19(void){
_start:
{
lean_object* v_range_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v_range_762_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_763_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__18, &l_Std_Time_Month_Ordinal_days___closed__18_once, _init_l_Std_Time_Month_Ordinal_days___closed__18);
v___x_764_ = lean_int_emod(v___x_763_, v_range_762_);
return v___x_764_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__20(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_765_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_766_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__19, &l_Std_Time_Month_Ordinal_days___closed__19_once, _init_l_Std_Time_Month_Ordinal_days___closed__19);
v___x_767_ = lean_int_add(v___x_766_, v___x_765_);
return v___x_767_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__21(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_768_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__20, &l_Std_Time_Month_Ordinal_days___closed__20_once, _init_l_Std_Time_Month_Ordinal_days___closed__20);
v___x_769_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__15, &l_Std_Time_Month_Ordinal_days___closed__15_once, _init_l_Std_Time_Month_Ordinal_days___closed__15);
v___x_770_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__9, &l_Std_Time_Month_Ordinal_days___closed__9_once, _init_l_Std_Time_Month_Ordinal_days___closed__9);
v___x_771_ = lean_unsigned_to_nat(12u);
v___x_772_ = lean_mk_empty_array_with_capacity(v___x_771_);
v___x_773_ = lean_array_push(v___x_772_, v___x_770_);
v___x_774_ = lean_array_push(v___x_773_, v___x_769_);
v___x_775_ = lean_array_push(v___x_774_, v___x_770_);
v___x_776_ = lean_array_push(v___x_775_, v___x_768_);
v___x_777_ = lean_array_push(v___x_776_, v___x_770_);
v___x_778_ = lean_array_push(v___x_777_, v___x_768_);
v___x_779_ = lean_array_push(v___x_778_, v___x_770_);
v___x_780_ = lean_array_push(v___x_779_, v___x_770_);
v___x_781_ = lean_array_push(v___x_780_, v___x_768_);
v___x_782_ = lean_array_push(v___x_781_, v___x_770_);
v___x_783_ = lean_array_push(v___x_782_, v___x_768_);
v___x_784_ = lean_array_push(v___x_783_, v___x_770_);
return v___x_784_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__22(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_unsigned_to_nat(29u);
v___x_786_ = lean_nat_to_int(v___x_785_);
return v___x_786_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__23(void){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_787_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_788_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__22, &l_Std_Time_Month_Ordinal_days___closed__22_once, _init_l_Std_Time_Month_Ordinal_days___closed__22);
v___x_789_ = lean_int_sub(v___x_788_, v___x_787_);
return v___x_789_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__24(void){
_start:
{
lean_object* v_range_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_range_790_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_791_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__23, &l_Std_Time_Month_Ordinal_days___closed__23_once, _init_l_Std_Time_Month_Ordinal_days___closed__23);
v___x_792_ = lean_int_emod(v___x_791_, v_range_790_);
return v___x_792_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__25(void){
_start:
{
lean_object* v_range_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v_range_793_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_794_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__24, &l_Std_Time_Month_Ordinal_days___closed__24_once, _init_l_Std_Time_Month_Ordinal_days___closed__24);
v___x_795_ = lean_int_add(v___x_794_, v_range_793_);
return v___x_795_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__26(void){
_start:
{
lean_object* v_range_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_range_796_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__4, &l_Std_Time_Month_Ordinal_days___closed__4_once, _init_l_Std_Time_Month_Ordinal_days___closed__4);
v___x_797_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__25, &l_Std_Time_Month_Ordinal_days___closed__25_once, _init_l_Std_Time_Month_Ordinal_days___closed__25);
v___x_798_ = lean_int_emod(v___x_797_, v_range_796_);
return v___x_798_;
}
}
static lean_object* _init_l_Std_Time_Month_Ordinal_days___closed__27(void){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_799_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_800_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__26, &l_Std_Time_Month_Ordinal_days___closed__26_once, _init_l_Std_Time_Month_Ordinal_days___closed__26);
v___x_801_ = lean_int_add(v___x_800_, v___x_799_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_days(uint8_t v_leap_802_, lean_object* v_month_803_){
_start:
{
lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_804_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__0, &l_Std_Time_Month_Ordinal_days___closed__0_once, _init_l_Std_Time_Month_Ordinal_days___closed__0);
v___x_805_ = lean_int_dec_eq(v_month_803_, v___x_804_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_806_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__21, &l_Std_Time_Month_Ordinal_days___closed__21_once, _init_l_Std_Time_Month_Ordinal_days___closed__21);
v___x_807_ = lean_obj_once(&l_Std_Time_Month_Quarter_ofMonth___closed__1, &l_Std_Time_Month_Quarter_ofMonth___closed__1_once, _init_l_Std_Time_Month_Quarter_ofMonth___closed__1);
v___x_808_ = lean_int_add(v_month_803_, v___x_807_);
v___x_809_ = l_Int_toNat(v___x_808_);
lean_dec(v___x_808_);
v___x_810_ = lean_array_fget(v___x_806_, v___x_809_);
lean_dec(v___x_809_);
return v___x_810_;
}
else
{
if (v_leap_802_ == 0)
{
lean_object* v___x_811_; 
v___x_811_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__15, &l_Std_Time_Month_Ordinal_days___closed__15_once, _init_l_Std_Time_Month_Ordinal_days___closed__15);
return v___x_811_;
}
else
{
lean_object* v___x_812_; 
v___x_812_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__27, &l_Std_Time_Month_Ordinal_days___closed__27_once, _init_l_Std_Time_Month_Ordinal_days___closed__27);
return v___x_812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_days___boxed(lean_object* v_leap_813_, lean_object* v_month_814_){
_start:
{
uint8_t v_leap_boxed_815_; lean_object* v_res_816_; 
v_leap_boxed_815_ = lean_unbox(v_leap_813_);
v_res_816_ = l_Std_Time_Month_Ordinal_days(v_leap_boxed_815_, v_month_814_);
lean_dec(v_month_814_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_cumulativeDays(uint8_t v_leap_817_, lean_object* v_month_818_){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v_res_827_; 
v___x_819_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toNat___closed__0, &l_Std_Time_Month_Ordinal_toNat___closed__0_once, _init_l_Std_Time_Month_Ordinal_toNat___closed__0);
v___x_820_ = lean_unsigned_to_nat(12u);
v___x_821_ = lean_mk_empty_array_with_capacity(v___x_820_);
lean_dec_ref(v___x_821_);
v___x_822_ = lean_obj_once(&l_Std_Time_Month_Ordinal_toSeconds___closed__11, &l_Std_Time_Month_Ordinal_toSeconds___closed__11_once, _init_l_Std_Time_Month_Ordinal_toSeconds___closed__11);
v___x_823_ = lean_obj_once(&l_Std_Time_Month_instOfNatOrdinal___closed__0, &l_Std_Time_Month_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Month_instOfNatOrdinal___closed__0);
v___x_824_ = lean_obj_once(&l_Std_Time_Month_Quarter_ofMonth___closed__1, &l_Std_Time_Month_Quarter_ofMonth___closed__1_once, _init_l_Std_Time_Month_Quarter_ofMonth___closed__1);
v___x_825_ = lean_int_add(v_month_818_, v___x_824_);
v___x_826_ = l_Int_toNat(v___x_825_);
lean_dec(v___x_825_);
v_res_827_ = lean_array_fget(v___x_822_, v___x_826_);
lean_dec(v___x_826_);
if (v_leap_817_ == 0)
{
lean_object* v___x_322__overap_828_; lean_object* v___x_829_; 
v___x_322__overap_828_ = l_Std_Time_Day_instAddOffset;
v___x_829_ = lean_apply_2(v___x_322__overap_828_, v_res_827_, v___x_819_);
return v___x_829_;
}
else
{
lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_830_ = lean_obj_once(&l_Std_Time_Month_Ordinal_days___closed__0, &l_Std_Time_Month_Ordinal_days___closed__0_once, _init_l_Std_Time_Month_Ordinal_days___closed__0);
v___x_831_ = lean_int_dec_lt(v___x_830_, v_month_818_);
if (v___x_831_ == 0)
{
lean_object* v___x_323__overap_832_; lean_object* v___x_833_; 
v___x_323__overap_832_ = l_Std_Time_Day_instAddOffset;
v___x_833_ = lean_apply_2(v___x_323__overap_832_, v_res_827_, v___x_819_);
return v___x_833_;
}
else
{
lean_object* v___x_324__overap_834_; lean_object* v___x_835_; 
v___x_324__overap_834_ = l_Std_Time_Day_instAddOffset;
v___x_835_ = lean_apply_2(v___x_324__overap_834_, v_res_827_, v___x_823_);
return v___x_835_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_cumulativeDays___boxed(lean_object* v_leap_836_, lean_object* v_month_837_){
_start:
{
uint8_t v_leap_boxed_838_; lean_object* v_res_839_; 
v_leap_boxed_838_ = lean_unbox(v_leap_836_);
v_res_839_ = l_Std_Time_Month_Ordinal_cumulativeDays(v_leap_boxed_838_, v_month_837_);
lean_dec(v_month_837_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_clipDay(uint8_t v_leap_840_, lean_object* v_month_841_, lean_object* v_day_842_){
_start:
{
lean_object* v_max_843_; uint8_t v___x_844_; 
v_max_843_ = l_Std_Time_Month_Ordinal_days(v_leap_840_, v_month_841_);
v___x_844_ = lean_int_dec_lt(v_max_843_, v_day_842_);
if (v___x_844_ == 0)
{
lean_dec(v_max_843_);
lean_inc(v_day_842_);
return v_day_842_;
}
else
{
return v_max_843_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Month_Ordinal_clipDay___boxed(lean_object* v_leap_845_, lean_object* v_month_846_, lean_object* v_day_847_){
_start:
{
uint8_t v_leap_boxed_848_; lean_object* v_res_849_; 
v_leap_boxed_848_ = lean_unbox(v_leap_845_);
v_res_849_ = l_Std_Time_Month_Ordinal_clipDay(v_leap_boxed_848_, v_month_846_, v_day_847_);
lean_dec(v_day_847_);
lean_dec(v_month_846_);
return v_res_849_;
}
}
lean_object* runtime_initialize_Std_Time_Date_Unit_Day(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Date_Unit_Month(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
