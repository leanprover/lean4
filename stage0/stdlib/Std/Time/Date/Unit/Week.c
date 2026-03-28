// Lean compiler output
// Module: Std.Time.Date.Unit.Week
// Imports: public import Std.Time.Date.Unit.Day
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
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Int_add___boxed(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Int_sub___boxed(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
uint8_t lean_int_dec_nonneg(lean_object*);
lean_object* l_Int_repr___boxed(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Rat_instNatCast___lam__0(lean_object*);
lean_object* l_Rat_mul(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_instInhabitedUnitVal_default(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Int_neg___boxed(lean_object*);
lean_object* lean_int_neg(lean_object*);
static lean_once_cell_t l_Std_Time_Week_instReprOrdinal___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instReprOrdinal___aux__1___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Week_instReprOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instReprOrdinal___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instReprOrdinal___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instReprOrdinal___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Week_instReprOrdinal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Week_instReprOrdinal___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Week_instReprOrdinal___closed__0 = (const lean_object*)&l_Std_Time_Week_instReprOrdinal___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Week_instReprOrdinal = (const lean_object*)&l_Std_Time_Week_instReprOrdinal___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableEqOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableEqOrdinal___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableEqOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableEqOrdinal___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instLEOrdinal;
LEAN_EXPORT lean_object* l_Std_Time_Week_instLTOrdinal;
static lean_once_cell_t l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0;
static lean_once_cell_t l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__1;
static lean_once_cell_t l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__2;
static lean_once_cell_t l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3;
static lean_once_cell_t l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4;
LEAN_EXPORT lean_object* l_Std_Time_Week_instOfNatOrdinal___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instOfNatOrdinal(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLeOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLeOrdinal___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLeOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLeOrdinal___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLtOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLtOrdinal___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLtOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLtOrdinal___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Week_instInhabitedOrdinal___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instInhabitedOrdinal___closed__0;
static lean_once_cell_t l_Std_Time_Week_instInhabitedOrdinal___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instInhabitedOrdinal___closed__1;
static lean_once_cell_t l_Std_Time_Week_instInhabitedOrdinal___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instInhabitedOrdinal___closed__2;
static lean_once_cell_t l_Std_Time_Week_instInhabitedOrdinal___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instInhabitedOrdinal___closed__3;
static lean_once_cell_t l_Std_Time_Week_instInhabitedOrdinal___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instInhabitedOrdinal___closed__4;
LEAN_EXPORT lean_object* l_Std_Time_Week_instInhabitedOrdinal;
LEAN_EXPORT uint8_t l_Std_Time_Week_instOrdOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instOrdOrdinal___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Week_instOrdOrdinal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Week_instOrdOrdinal___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Week_instOrdOrdinal___closed__0 = (const lean_object*)&l_Std_Time_Week_instOrdOrdinal___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Week_instOrdOrdinal = (const lean_object*)&l_Std_Time_Week_instOrdOrdinal___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Week_instReprOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instReprOffset___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT const lean_object* l_Std_Time_Week_instReprOffset = (const lean_object*)&l_Std_Time_Week_instReprOrdinal___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableEqOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableEqOffset___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableEqOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableEqOffset___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0;
static lean_once_cell_t l_Std_Time_Week_instInhabitedOffset___aux__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instInhabitedOffset___aux__1___closed__1;
static lean_once_cell_t l_Std_Time_Week_instInhabitedOffset___aux__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instInhabitedOffset___aux__1___closed__2;
static lean_once_cell_t l_Std_Time_Week_instInhabitedOffset___aux__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instInhabitedOffset___aux__1___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_Week_instInhabitedOffset___aux__1;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Week_instInhabitedOffset_spec__0(lean_object*);
static lean_once_cell_t l_Std_Time_Week_instInhabitedOffset___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instInhabitedOffset___closed__0;
static lean_once_cell_t l_Std_Time_Week_instInhabitedOffset___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instInhabitedOffset___closed__1;
static lean_once_cell_t l_Std_Time_Week_instInhabitedOffset___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instInhabitedOffset___closed__2;
static lean_once_cell_t l_Std_Time_Week_instInhabitedOffset___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instInhabitedOffset___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_Week_instInhabitedOffset;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Week_instInhabitedOffset_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instAddOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instAddOffset___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Week_instAddOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Week_instAddOffset___closed__0 = (const lean_object*)&l_Std_Time_Week_instAddOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Week_instAddOffset = (const lean_object*)&l_Std_Time_Week_instAddOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Week_instSubOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instSubOffset___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Week_instSubOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Week_instSubOffset___closed__0 = (const lean_object*)&l_Std_Time_Week_instSubOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Week_instSubOffset = (const lean_object*)&l_Std_Time_Week_instSubOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Week_instNegOffset___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instNegOffset___aux__1___boxed(lean_object*);
static const lean_closure_object l_Std_Time_Week_instNegOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Week_instNegOffset___closed__0 = (const lean_object*)&l_Std_Time_Week_instNegOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Week_instNegOffset = (const lean_object*)&l_Std_Time_Week_instNegOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Week_instLEOffset;
LEAN_EXPORT lean_object* l_Std_Time_Week_instLTOffset;
LEAN_EXPORT lean_object* l_Std_Time_Week_instToStringOffset___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instToStringOffset___aux__1___boxed(lean_object*);
static const lean_closure_object l_Std_Time_Week_instToStringOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_repr___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Week_instToStringOffset___closed__0 = (const lean_object*)&l_Std_Time_Week_instToStringOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Week_instToStringOffset = (const lean_object*)&l_Std_Time_Week_instToStringOffset___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLeOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLeOffset___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLeOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLeOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLtOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLtOffset___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLtOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLtOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instOfNatOffset(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Week_instOrdOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instOrdOffset___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Week_instOrdOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Week_instOrdOffset___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Week_instOrdOffset___closed__0 = (const lean_object*)&l_Std_Time_Week_instOrdOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Week_instOrdOffset = (const lean_object*)&l_Std_Time_Week_instOrdOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofInt___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofInt___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofInt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofInt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_instReprOfMonth___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_instReprOfMonth___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT const lean_object* l_Std_Time_Week_Ordinal_instReprOfMonth = (const lean_object*)&l_Std_Time_Week_instReprOrdinal___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Week_Ordinal_instDecidableEqOfMonth___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_instDecidableEqOfMonth___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Week_Ordinal_instDecidableEqOfMonth(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_instDecidableEqOfMonth___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__0;
static lean_once_cell_t l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__1;
static lean_once_cell_t l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__2;
static lean_once_cell_t l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_instOfNatOfMonth(lean_object*);
static lean_once_cell_t l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__0;
static lean_once_cell_t l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__1;
static lean_once_cell_t l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__2;
static lean_once_cell_t l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_instInhabitedOfMonth;
LEAN_EXPORT uint8_t l_Std_Time_Week_Ordinal_instOrdOfMonth___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_instOrdOfMonth___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Week_Ordinal_instOrdOfMonth___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Week_Ordinal_instOrdOfMonth___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Week_Ordinal_instOrdOfMonth___closed__0 = (const lean_object*)&l_Std_Time_Week_Ordinal_instOrdOfMonth___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Week_Ordinal_instOrdOfMonth = (const lean_object*)&l_Std_Time_Week_Ordinal_instOrdOfMonth___closed__0_value;
static const lean_string_object l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__0 = (const lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__0_value;
static const lean_string_object l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__1 = (const lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__1_value;
static const lean_string_object l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__2 = (const lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__2_value;
static const lean_string_object l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__3 = (const lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__3_value;
static const lean_ctor_object l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4_value_aux_0),((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4_value_aux_1),((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4_value_aux_2),((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4 = (const lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4_value;
static const lean_array_object l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5 = (const lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5_value;
static const lean_string_object l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__6 = (const lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__6_value;
static const lean_ctor_object l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7_value_aux_0),((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7_value_aux_1),((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7_value_aux_2),((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7 = (const lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7_value;
static const lean_string_object l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__8 = (const lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__8_value;
static const lean_ctor_object l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__9 = (const lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__9_value;
static const lean_string_object l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__10 = (const lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__10_value;
static const lean_ctor_object l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11_value_aux_0),((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11_value_aux_1),((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11_value_aux_2),((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(53, 158, 1, 232, 101, 200, 191, 197)}};
static const lean_object* l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11 = (const lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11_value;
static lean_once_cell_t l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__12;
static lean_once_cell_t l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__13;
static const lean_string_object l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__14 = (const lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__14_value;
static const lean_ctor_object l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15_value_aux_0),((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15_value_aux_1),((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15_value_aux_2),((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15 = (const lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15_value;
static const lean_ctor_object l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__9_value),((lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5_value)}};
static const lean_object* l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__16 = (const lean_object*)&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__16_value;
static lean_once_cell_t l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__17;
static lean_once_cell_t l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__18;
static lean_once_cell_t l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__19;
static lean_once_cell_t l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__20;
static lean_once_cell_t l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__21;
static lean_once_cell_t l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__22;
static lean_once_cell_t l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__23;
static lean_once_cell_t l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__24;
static lean_once_cell_t l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__25;
static lean_once_cell_t l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__26;
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofNat___auto__1;
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofNat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofNat(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Week_Ordinal_ofFin___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Ordinal_ofFin___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofFin(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_toOffset(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_toOffset___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofInt(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofInt___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Week_Offset_toMilliseconds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Offset_toMilliseconds___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toMilliseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toMilliseconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofMilliseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofMilliseconds___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Week_Offset_toNanoseconds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Offset_toNanoseconds___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toNanoseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toNanoseconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofNanoseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofNanoseconds___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Week_Offset_toSeconds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Offset_toSeconds___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toSeconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toSeconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofSeconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofSeconds___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Week_Offset_toMinutes___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Offset_toMinutes___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toMinutes(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toMinutes___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofMinutes(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofMinutes___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Week_Offset_toHours___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Offset_toHours___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toHours(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toHours___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofHours(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofHours___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Week_Offset_toDays___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Offset_toDays___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toDays(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toDays___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofDays(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofDays___boxed(lean_object*);
static lean_object* _init_l_Std_Time_Week_instReprOrdinal___aux__1___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instReprOrdinal___aux__1(lean_object* v_n_3_, lean_object* v_a_4_){
_start:
{
lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_5_ = lean_obj_once(&l_Std_Time_Week_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Week_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instReprOrdinal___aux__1___closed__0);
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
LEAN_EXPORT lean_object* l_Std_Time_Week_instReprOrdinal___aux__1___boxed(lean_object* v_n_12_, lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_Time_Week_instReprOrdinal___aux__1(v_n_12_, v_a_13_);
lean_dec(v_a_13_);
lean_dec(v_n_12_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instReprOrdinal___lam__0(lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
lean_object* v___x_17_; uint8_t v___x_18_; 
v___x_17_ = lean_obj_once(&l_Std_Time_Week_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Week_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instReprOrdinal___aux__1___closed__0);
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
LEAN_EXPORT lean_object* l_Std_Time_Week_instReprOrdinal___lam__0___boxed(lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Std_Time_Week_instReprOrdinal___lam__0(v___y_24_, v___y_25_);
lean_dec(v___y_25_);
lean_dec(v___y_24_);
return v_res_26_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableEqOrdinal___aux__1(lean_object* v_x_29_, lean_object* v_x_30_){
_start:
{
uint8_t v___x_31_; 
v___x_31_ = lean_int_dec_eq(v_x_29_, v_x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableEqOrdinal___aux__1___boxed(lean_object* v_x_32_, lean_object* v_x_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l_Std_Time_Week_instDecidableEqOrdinal___aux__1(v_x_32_, v_x_33_);
lean_dec(v_x_33_);
lean_dec(v_x_32_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableEqOrdinal(lean_object* v_a_36_, lean_object* v_b_37_){
_start:
{
uint8_t v___x_38_; 
v___x_38_ = lean_int_dec_eq(v_a_36_, v_b_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableEqOrdinal___boxed(lean_object* v_a_39_, lean_object* v_b_40_){
_start:
{
uint8_t v_res_41_; lean_object* v_r_42_; 
v_res_41_ = l_Std_Time_Week_instDecidableEqOrdinal(v_a_39_, v_b_40_);
lean_dec(v_b_40_);
lean_dec(v_a_39_);
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
}
}
static lean_object* _init_l_Std_Time_Week_instLEOrdinal(void){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_box(0);
return v___x_43_;
}
}
static lean_object* _init_l_Std_Time_Week_instLTOrdinal(void){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_box(0);
return v___x_44_;
}
}
static lean_object* _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_unsigned_to_nat(1u);
v___x_46_ = lean_nat_to_int(v___x_45_);
return v___x_46_;
}
}
static lean_object* _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__1(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_unsigned_to_nat(52u);
v___x_48_ = lean_nat_to_int(v___x_47_);
return v___x_48_;
}
}
static lean_object* _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__2(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__1, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__1_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__1);
v___x_50_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0);
v___x_51_ = lean_int_add(v___x_50_, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0);
v___x_53_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__2, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__2_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__2);
v___x_54_ = lean_int_sub(v___x_53_, v___x_52_);
return v___x_54_;
}
}
static lean_object* _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v_range_57_; 
v___x_55_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0);
v___x_56_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3);
v_range_57_ = lean_int_add(v___x_56_, v___x_55_);
return v_range_57_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instOfNatOrdinal___aux__1(lean_object* v_n_58_){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v_range_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_59_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0);
v___x_60_ = lean_nat_to_int(v_n_58_);
v_range_61_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4);
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
LEAN_EXPORT lean_object* l_Std_Time_Week_instOfNatOrdinal(lean_object* v_n_67_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v_range_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_68_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0);
v___x_69_ = lean_nat_to_int(v_n_67_);
v_range_70_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4);
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
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLeOrdinal___aux__1(lean_object* v_x_76_, lean_object* v_y_77_){
_start:
{
lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_78_ = lean_int_sub(v_y_77_, v_x_76_);
v___x_79_ = lean_int_dec_nonneg(v___x_78_);
lean_dec(v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLeOrdinal___aux__1___boxed(lean_object* v_x_80_, lean_object* v_y_81_){
_start:
{
uint8_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = l_Std_Time_Week_instDecidableLeOrdinal___aux__1(v_x_80_, v_y_81_);
lean_dec(v_y_81_);
lean_dec(v_x_80_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLeOrdinal(lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
uint8_t v___x_86_; 
v___x_86_ = l_Std_Time_Week_instDecidableLeOrdinal___aux__1(v___y_84_, v___y_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLeOrdinal___boxed(lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_Std_Time_Week_instDecidableLeOrdinal(v___y_87_, v___y_88_);
lean_dec(v___y_88_);
lean_dec(v___y_87_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLtOrdinal___aux__1(lean_object* v_x_91_, lean_object* v_y_92_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_93_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0);
v___x_94_ = lean_int_add(v_x_91_, v___x_93_);
v___x_95_ = lean_int_sub(v_y_92_, v___x_94_);
lean_dec(v___x_94_);
v___x_96_ = lean_int_dec_nonneg(v___x_95_);
lean_dec(v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLtOrdinal___aux__1___boxed(lean_object* v_x_97_, lean_object* v_y_98_){
_start:
{
uint8_t v_res_99_; lean_object* v_r_100_; 
v_res_99_ = l_Std_Time_Week_instDecidableLtOrdinal___aux__1(v_x_97_, v_y_98_);
lean_dec(v_y_98_);
lean_dec(v_x_97_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLtOrdinal(lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
uint8_t v___x_103_; 
v___x_103_ = l_Std_Time_Week_instDecidableLtOrdinal___aux__1(v___y_101_, v___y_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLtOrdinal___boxed(lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
uint8_t v_res_106_; lean_object* v_r_107_; 
v_res_106_ = l_Std_Time_Week_instDecidableLtOrdinal(v___y_104_, v___y_105_);
lean_dec(v___y_105_);
lean_dec(v___y_104_);
v_r_107_ = lean_box(v_res_106_);
return v_r_107_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal___closed__0(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0);
v___x_109_ = lean_int_sub(v___x_108_, v___x_108_);
return v___x_109_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal___closed__1(void){
_start:
{
lean_object* v_range_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v_range_110_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4);
v___x_111_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__0, &l_Std_Time_Week_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__0);
v___x_112_ = lean_int_emod(v___x_111_, v_range_110_);
return v___x_112_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal___closed__2(void){
_start:
{
lean_object* v_range_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v_range_113_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4);
v___x_114_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__1, &l_Std_Time_Week_instInhabitedOrdinal___closed__1_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__1);
v___x_115_ = lean_int_add(v___x_114_, v_range_113_);
return v___x_115_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal___closed__3(void){
_start:
{
lean_object* v_range_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v_range_116_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4);
v___x_117_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__2, &l_Std_Time_Week_instInhabitedOrdinal___closed__2_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__2);
v___x_118_ = lean_int_emod(v___x_117_, v_range_116_);
return v___x_118_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal___closed__4(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_119_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0);
v___x_120_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__3, &l_Std_Time_Week_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__3);
v___x_121_ = lean_int_add(v___x_120_, v___x_119_);
return v___x_121_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal(void){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__4, &l_Std_Time_Week_instInhabitedOrdinal___closed__4_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__4);
return v___x_122_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instOrdOrdinal___aux__1(lean_object* v_x_123_, lean_object* v_y_124_){
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
LEAN_EXPORT lean_object* l_Std_Time_Week_instOrdOrdinal___aux__1___boxed(lean_object* v_x_130_, lean_object* v_y_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l_Std_Time_Week_instOrdOrdinal___aux__1(v_x_130_, v_y_131_);
lean_dec(v_y_131_);
lean_dec(v_x_130_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instReprOffset___aux__1(lean_object* v_x_136_, lean_object* v_p_137_){
_start:
{
lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_138_ = lean_obj_once(&l_Std_Time_Week_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Week_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instReprOrdinal___aux__1___closed__0);
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
LEAN_EXPORT lean_object* l_Std_Time_Week_instReprOffset___aux__1___boxed(lean_object* v_x_145_, lean_object* v_p_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Std_Time_Week_instReprOffset___aux__1(v_x_145_, v_p_146_);
lean_dec(v_p_146_);
lean_dec(v_x_145_);
return v_res_147_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableEqOffset___aux__1(lean_object* v_x_149_, lean_object* v_x_150_){
_start:
{
uint8_t v___x_151_; 
v___x_151_ = lean_int_dec_eq(v_x_149_, v_x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableEqOffset___aux__1___boxed(lean_object* v_x_152_, lean_object* v_x_153_){
_start:
{
uint8_t v_res_154_; lean_object* v_r_155_; 
v_res_154_ = l_Std_Time_Week_instDecidableEqOffset___aux__1(v_x_152_, v_x_153_);
lean_dec(v_x_153_);
lean_dec(v_x_152_);
v_r_155_ = lean_box(v_res_154_);
return v_r_155_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableEqOffset(lean_object* v_a_156_, lean_object* v_b_157_){
_start:
{
uint8_t v___x_158_; 
v___x_158_ = lean_int_dec_eq(v_a_156_, v_b_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableEqOffset___boxed(lean_object* v_a_159_, lean_object* v_b_160_){
_start:
{
uint8_t v_res_161_; lean_object* v_r_162_; 
v_res_161_ = l_Std_Time_Week_instDecidableEqOffset(v_a_159_, v_b_160_);
lean_dec(v_b_160_);
lean_dec(v_a_159_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_unsigned_to_nat(86400u);
v___x_164_ = l_Rat_instNatCast___lam__0(v___x_163_);
return v___x_164_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__1(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_unsigned_to_nat(7u);
v___x_166_ = l_Rat_instNatCast___lam__0(v___x_165_);
return v___x_166_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__2(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOffset___aux__1___closed__1, &l_Std_Time_Week_instInhabitedOffset___aux__1___closed__1_once, _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__1);
v___x_168_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0, &l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0_once, _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0);
v___x_169_ = l_Rat_mul(v___x_168_, v___x_167_);
return v___x_169_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__3(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOffset___aux__1___closed__2, &l_Std_Time_Week_instInhabitedOffset___aux__1___closed__2_once, _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__2);
v___x_171_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_170_);
return v___x_171_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset___aux__1(void){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOffset___aux__1___closed__3, &l_Std_Time_Week_instInhabitedOffset___aux__1___closed__3_once, _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__3);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Week_instInhabitedOffset_spec__0(lean_object* v_a_173_){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_nat_to_int(v_a_173_);
v___x_175_ = l_Rat_ofInt(v___x_174_);
return v___x_175_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset___closed__0(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = lean_unsigned_to_nat(86400u);
v___x_177_ = l_Nat_cast___at___00Std_Time_Week_instInhabitedOffset_spec__0(v___x_176_);
return v___x_177_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset___closed__1(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_unsigned_to_nat(7u);
v___x_179_ = l_Nat_cast___at___00Std_Time_Week_instInhabitedOffset_spec__0(v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset___closed__2(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOffset___closed__1, &l_Std_Time_Week_instInhabitedOffset___closed__1_once, _init_l_Std_Time_Week_instInhabitedOffset___closed__1);
v___x_181_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOffset___closed__0, &l_Std_Time_Week_instInhabitedOffset___closed__0_once, _init_l_Std_Time_Week_instInhabitedOffset___closed__0);
v___x_182_ = l_Rat_mul(v___x_181_, v___x_180_);
return v___x_182_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset___closed__3(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOffset___closed__2, &l_Std_Time_Week_instInhabitedOffset___closed__2_once, _init_l_Std_Time_Week_instInhabitedOffset___closed__2);
v___x_184_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_183_);
return v___x_184_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset(void){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOffset___closed__3, &l_Std_Time_Week_instInhabitedOffset___closed__3_once, _init_l_Std_Time_Week_instInhabitedOffset___closed__3);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Week_instInhabitedOffset_spec__0_spec__0(lean_object* v_a_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = lean_nat_to_int(v_a_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instAddOffset___aux__1(lean_object* v_u1_188_, lean_object* v_u2_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = lean_int_add(v_u1_188_, v_u2_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instAddOffset___aux__1___boxed(lean_object* v_u1_191_, lean_object* v_u2_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Std_Time_Week_instAddOffset___aux__1(v_u1_191_, v_u2_192_);
lean_dec(v_u2_192_);
lean_dec(v_u1_191_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instSubOffset___aux__1(lean_object* v_u1_196_, lean_object* v_u2_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = lean_int_sub(v_u1_196_, v_u2_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instSubOffset___aux__1___boxed(lean_object* v_u1_199_, lean_object* v_u2_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Std_Time_Week_instSubOffset___aux__1(v_u1_199_, v_u2_200_);
lean_dec(v_u2_200_);
lean_dec(v_u1_199_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instNegOffset___aux__1(lean_object* v_x_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = lean_int_neg(v_x_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instNegOffset___aux__1___boxed(lean_object* v_x_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Std_Time_Week_instNegOffset___aux__1(v_x_206_);
lean_dec(v_x_206_);
return v_res_207_;
}
}
static lean_object* _init_l_Std_Time_Week_instLEOffset(void){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = lean_box(0);
return v___x_210_;
}
}
static lean_object* _init_l_Std_Time_Week_instLTOffset(void){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = lean_box(0);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instToStringOffset___aux__1(lean_object* v_n_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Int_repr(v_n_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instToStringOffset___aux__1___boxed(lean_object* v_n_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Std_Time_Week_instToStringOffset___aux__1(v_n_214_);
lean_dec(v_n_214_);
return v_res_215_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLeOffset___aux__1(lean_object* v_x_218_, lean_object* v_y_219_){
_start:
{
lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_220_ = lean_int_sub(v_y_219_, v_x_218_);
v___x_221_ = lean_int_dec_nonneg(v___x_220_);
lean_dec(v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLeOffset___aux__1___boxed(lean_object* v_x_222_, lean_object* v_y_223_){
_start:
{
uint8_t v_res_224_; lean_object* v_r_225_; 
v_res_224_ = l_Std_Time_Week_instDecidableLeOffset___aux__1(v_x_222_, v_y_223_);
lean_dec(v_y_223_);
lean_dec(v_x_222_);
v_r_225_ = lean_box(v_res_224_);
return v_r_225_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLeOffset(lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
uint8_t v___x_228_; 
v___x_228_ = l_Std_Time_Week_instDecidableLeOffset___aux__1(v___y_226_, v___y_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLeOffset___boxed(lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
uint8_t v_res_231_; lean_object* v_r_232_; 
v_res_231_ = l_Std_Time_Week_instDecidableLeOffset(v___y_229_, v___y_230_);
lean_dec(v___y_230_);
lean_dec(v___y_229_);
v_r_232_ = lean_box(v_res_231_);
return v_r_232_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLtOffset___aux__1(lean_object* v_x_233_, lean_object* v_y_234_){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_235_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0);
v___x_236_ = lean_int_add(v_x_233_, v___x_235_);
v___x_237_ = lean_int_sub(v_y_234_, v___x_236_);
lean_dec(v___x_236_);
v___x_238_ = lean_int_dec_nonneg(v___x_237_);
lean_dec(v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLtOffset___aux__1___boxed(lean_object* v_x_239_, lean_object* v_y_240_){
_start:
{
uint8_t v_res_241_; lean_object* v_r_242_; 
v_res_241_ = l_Std_Time_Week_instDecidableLtOffset___aux__1(v_x_239_, v_y_240_);
lean_dec(v_y_240_);
lean_dec(v_x_239_);
v_r_242_ = lean_box(v_res_241_);
return v_r_242_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLtOffset(lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
uint8_t v___x_245_; 
v___x_245_ = l_Std_Time_Week_instDecidableLtOffset___aux__1(v___y_243_, v___y_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLtOffset___boxed(lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
uint8_t v_res_248_; lean_object* v_r_249_; 
v_res_248_ = l_Std_Time_Week_instDecidableLtOffset(v___y_246_, v___y_247_);
lean_dec(v___y_247_);
lean_dec(v___y_246_);
v_r_249_ = lean_box(v_res_248_);
return v_r_249_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instOfNatOffset(lean_object* v_n_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = lean_nat_to_int(v_n_250_);
return v___x_251_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instOrdOffset___aux__1(lean_object* v_x_252_, lean_object* v_y_253_){
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
LEAN_EXPORT lean_object* l_Std_Time_Week_instOrdOffset___aux__1___boxed(lean_object* v_x_259_, lean_object* v_y_260_){
_start:
{
uint8_t v_res_261_; lean_object* v_r_262_; 
v_res_261_ = l_Std_Time_Week_instOrdOffset___aux__1(v_x_259_, v_y_260_);
lean_dec(v_y_260_);
lean_dec(v_x_259_);
v_r_262_ = lean_box(v_res_261_);
return v_r_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofInt___redArg(lean_object* v_data_265_){
_start:
{
lean_inc(v_data_265_);
return v_data_265_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofInt___redArg___boxed(lean_object* v_data_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Std_Time_Week_Ordinal_ofInt___redArg(v_data_266_);
lean_dec(v_data_266_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofInt(lean_object* v_data_268_, lean_object* v_h_269_){
_start:
{
lean_inc(v_data_268_);
return v_data_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofInt___boxed(lean_object* v_data_270_, lean_object* v_h_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Std_Time_Week_Ordinal_ofInt(v_data_270_, v_h_271_);
lean_dec(v_data_270_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_instReprOfMonth___aux__1(lean_object* v_n_273_, lean_object* v_a_274_){
_start:
{
lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_275_ = lean_obj_once(&l_Std_Time_Week_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Week_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instReprOrdinal___aux__1___closed__0);
v___x_276_ = lean_int_dec_lt(v_n_273_, v___x_275_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = l_Int_repr(v_n_273_);
v___x_278_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
return v___x_278_;
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_279_ = l_Int_repr(v_n_273_);
v___x_280_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
v___x_281_ = l_Repr_addAppParen(v___x_280_, v_a_274_);
return v___x_281_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_instReprOfMonth___aux__1___boxed(lean_object* v_n_282_, lean_object* v_a_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Std_Time_Week_Ordinal_instReprOfMonth___aux__1(v_n_282_, v_a_283_);
lean_dec(v_a_283_);
lean_dec(v_n_282_);
return v_res_284_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_Ordinal_instDecidableEqOfMonth___aux__1(lean_object* v_x_286_, lean_object* v_x_287_){
_start:
{
uint8_t v___x_288_; 
v___x_288_ = lean_int_dec_eq(v_x_286_, v_x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_instDecidableEqOfMonth___aux__1___boxed(lean_object* v_x_289_, lean_object* v_x_290_){
_start:
{
uint8_t v_res_291_; lean_object* v_r_292_; 
v_res_291_ = l_Std_Time_Week_Ordinal_instDecidableEqOfMonth___aux__1(v_x_289_, v_x_290_);
lean_dec(v_x_290_);
lean_dec(v_x_289_);
v_r_292_ = lean_box(v_res_291_);
return v_r_292_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_Ordinal_instDecidableEqOfMonth(lean_object* v_a_293_, lean_object* v_b_294_){
_start:
{
uint8_t v___x_295_; 
v___x_295_ = lean_int_dec_eq(v_a_293_, v_b_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_instDecidableEqOfMonth___boxed(lean_object* v_a_296_, lean_object* v_b_297_){
_start:
{
uint8_t v_res_298_; lean_object* v_r_299_; 
v_res_298_ = l_Std_Time_Week_Ordinal_instDecidableEqOfMonth(v_a_296_, v_b_297_);
lean_dec(v_b_297_);
lean_dec(v_a_296_);
v_r_299_ = lean_box(v_res_298_);
return v_r_299_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__0(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = lean_unsigned_to_nat(5u);
v___x_301_ = lean_nat_to_int(v___x_300_);
return v___x_301_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__1(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_302_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__0, &l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__0_once, _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__0);
v___x_303_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0);
v___x_304_ = lean_int_add(v___x_303_, v___x_302_);
return v___x_304_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__2(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_305_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0);
v___x_306_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__1, &l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__1_once, _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__1);
v___x_307_ = lean_int_sub(v___x_306_, v___x_305_);
return v___x_307_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v_range_310_; 
v___x_308_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0);
v___x_309_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__2, &l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__2_once, _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__2);
v_range_310_ = lean_int_add(v___x_309_, v___x_308_);
return v_range_310_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1(lean_object* v_n_311_){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v_range_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_312_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0);
v___x_313_ = lean_nat_to_int(v_n_311_);
v_range_314_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3, &l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3_once, _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3);
v___x_315_ = lean_int_sub(v___x_313_, v___x_312_);
lean_dec(v___x_313_);
v___x_316_ = lean_int_emod(v___x_315_, v_range_314_);
lean_dec(v___x_315_);
v___x_317_ = lean_int_add(v___x_316_, v_range_314_);
lean_dec(v___x_316_);
v___x_318_ = lean_int_emod(v___x_317_, v_range_314_);
lean_dec(v___x_317_);
v___x_319_ = lean_int_add(v___x_318_, v___x_312_);
lean_dec(v___x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_instOfNatOfMonth(lean_object* v_n_320_){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v_range_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_321_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0);
v___x_322_ = lean_nat_to_int(v_n_320_);
v_range_323_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3, &l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3_once, _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3);
v___x_324_ = lean_int_sub(v___x_322_, v___x_321_);
lean_dec(v___x_322_);
v___x_325_ = lean_int_emod(v___x_324_, v_range_323_);
lean_dec(v___x_324_);
v___x_326_ = lean_int_add(v___x_325_, v_range_323_);
lean_dec(v___x_325_);
v___x_327_ = lean_int_emod(v___x_326_, v_range_323_);
lean_dec(v___x_326_);
v___x_328_ = lean_int_add(v___x_327_, v___x_321_);
lean_dec(v___x_327_);
return v___x_328_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__0(void){
_start:
{
lean_object* v_range_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_range_329_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3, &l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3_once, _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3);
v___x_330_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__0, &l_Std_Time_Week_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__0);
v___x_331_ = lean_int_emod(v___x_330_, v_range_329_);
return v___x_331_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__1(void){
_start:
{
lean_object* v_range_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v_range_332_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3, &l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3_once, _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3);
v___x_333_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__0, &l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__0_once, _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__0);
v___x_334_ = lean_int_add(v___x_333_, v_range_332_);
return v___x_334_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__2(void){
_start:
{
lean_object* v_range_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_range_335_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3, &l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3_once, _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3);
v___x_336_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__1, &l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__1_once, _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__1);
v___x_337_ = lean_int_emod(v___x_336_, v_range_335_);
return v___x_337_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_338_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0);
v___x_339_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__2, &l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__2_once, _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__2);
v___x_340_ = lean_int_add(v___x_339_, v___x_338_);
return v___x_340_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth(void){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3, &l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3_once, _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3);
return v___x_341_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_Ordinal_instOrdOfMonth___aux__1(lean_object* v_x_342_, lean_object* v_y_343_){
_start:
{
uint8_t v___x_344_; 
v___x_344_ = lean_int_dec_lt(v_x_342_, v_y_343_);
if (v___x_344_ == 0)
{
uint8_t v___x_345_; 
v___x_345_ = lean_int_dec_eq(v_x_342_, v_y_343_);
if (v___x_345_ == 0)
{
uint8_t v___x_346_; 
v___x_346_ = 2;
return v___x_346_;
}
else
{
uint8_t v___x_347_; 
v___x_347_ = 1;
return v___x_347_;
}
}
else
{
uint8_t v___x_348_; 
v___x_348_ = 0;
return v___x_348_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_instOrdOfMonth___aux__1___boxed(lean_object* v_x_349_, lean_object* v_y_350_){
_start:
{
uint8_t v_res_351_; lean_object* v_r_352_; 
v_res_351_ = l_Std_Time_Week_Ordinal_instOrdOfMonth___aux__1(v_x_349_, v_y_350_);
lean_dec(v_y_350_);
lean_dec(v_x_349_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__12(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__10));
v___x_382_ = l_Lean_mkAtom(v___x_381_);
return v___x_382_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__13(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_383_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__12, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__12_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__12);
v___x_384_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5));
v___x_385_ = lean_array_push(v___x_384_, v___x_383_);
return v___x_385_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__17(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_396_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__16));
v___x_397_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5));
v___x_398_ = lean_array_push(v___x_397_, v___x_396_);
return v___x_398_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__18(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_399_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__17, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__17_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__17);
v___x_400_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15));
v___x_401_ = lean_box(2);
v___x_402_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
lean_ctor_set(v___x_402_, 1, v___x_400_);
lean_ctor_set(v___x_402_, 2, v___x_399_);
return v___x_402_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__19(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_403_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__18, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__18_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__18);
v___x_404_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__13, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__13_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__13);
v___x_405_ = lean_array_push(v___x_404_, v___x_403_);
return v___x_405_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__20(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_406_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__19, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__19_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__19);
v___x_407_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11));
v___x_408_ = lean_box(2);
v___x_409_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v___x_407_);
lean_ctor_set(v___x_409_, 2, v___x_406_);
return v___x_409_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__21(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_410_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__20, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__20_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__20);
v___x_411_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5));
v___x_412_ = lean_array_push(v___x_411_, v___x_410_);
return v___x_412_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__22(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_413_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__21, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__21_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__21);
v___x_414_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__9));
v___x_415_ = lean_box(2);
v___x_416_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
lean_ctor_set(v___x_416_, 1, v___x_414_);
lean_ctor_set(v___x_416_, 2, v___x_413_);
return v___x_416_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__23(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_417_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__22, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__22_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__22);
v___x_418_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5));
v___x_419_ = lean_array_push(v___x_418_, v___x_417_);
return v___x_419_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__24(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_420_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__23, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__23_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__23);
v___x_421_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7));
v___x_422_ = lean_box(2);
v___x_423_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v___x_421_);
lean_ctor_set(v___x_423_, 2, v___x_420_);
return v___x_423_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__25(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_424_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__24, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__24_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__24);
v___x_425_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5));
v___x_426_ = lean_array_push(v___x_425_, v___x_424_);
return v___x_426_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__26(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_427_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__25, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__25_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__25);
v___x_428_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4));
v___x_429_ = lean_box(2);
v___x_430_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v___x_428_);
lean_ctor_set(v___x_430_, 2, v___x_427_);
return v___x_430_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1(void){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__26, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__26_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__26);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofNat___redArg(lean_object* v_data_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = lean_nat_to_int(v_data_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofNat(lean_object* v_data_434_, lean_object* v_h_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = lean_nat_to_int(v_data_434_);
return v___x_436_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofFin___closed__0(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_unsigned_to_nat(1u);
v___x_438_ = lean_nat_to_int(v___x_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofFin(lean_object* v_data_439_){
_start:
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = lean_unsigned_to_nat(1u);
v___x_441_ = lean_nat_dec_le(v___x_440_, v_data_439_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; 
lean_dec(v_data_439_);
v___x_442_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofFin___closed__0, &l_Std_Time_Week_Ordinal_ofFin___closed__0_once, _init_l_Std_Time_Week_Ordinal_ofFin___closed__0);
return v___x_442_;
}
else
{
lean_object* v___x_443_; 
v___x_443_ = lean_nat_to_int(v_data_439_);
return v___x_443_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_toOffset(lean_object* v_ordinal_444_){
_start:
{
lean_inc(v_ordinal_444_);
return v_ordinal_444_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_toOffset___boxed(lean_object* v_ordinal_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Std_Time_Week_Ordinal_toOffset(v_ordinal_445_);
lean_dec(v_ordinal_445_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofNat(lean_object* v_data_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = lean_nat_to_int(v_data_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofInt(lean_object* v_data_449_){
_start:
{
lean_inc(v_data_449_);
return v_data_449_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofInt___boxed(lean_object* v_data_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Std_Time_Week_Offset_ofInt(v_data_450_);
lean_dec(v_data_450_);
return v_res_451_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = lean_unsigned_to_nat(604800000u);
v___x_453_ = lean_nat_to_int(v___x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toMilliseconds(lean_object* v_weeks_454_){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_obj_once(&l_Std_Time_Week_Offset_toMilliseconds___closed__0, &l_Std_Time_Week_Offset_toMilliseconds___closed__0_once, _init_l_Std_Time_Week_Offset_toMilliseconds___closed__0);
v___x_456_ = lean_int_mul(v_weeks_454_, v___x_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toMilliseconds___boxed(lean_object* v_weeks_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Std_Time_Week_Offset_toMilliseconds(v_weeks_457_);
lean_dec(v_weeks_457_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofMilliseconds(lean_object* v_millis_459_){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = lean_obj_once(&l_Std_Time_Week_Offset_toMilliseconds___closed__0, &l_Std_Time_Week_Offset_toMilliseconds___closed__0_once, _init_l_Std_Time_Week_Offset_toMilliseconds___closed__0);
v___x_461_ = lean_int_ediv(v_millis_459_, v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofMilliseconds___boxed(lean_object* v_millis_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Std_Time_Week_Offset_ofMilliseconds(v_millis_462_);
lean_dec(v_millis_462_);
return v_res_463_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toNanoseconds___closed__0(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_cstr_to_nat("604800000000000");
v___x_465_ = lean_nat_to_int(v___x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toNanoseconds(lean_object* v_weeks_466_){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = lean_obj_once(&l_Std_Time_Week_Offset_toNanoseconds___closed__0, &l_Std_Time_Week_Offset_toNanoseconds___closed__0_once, _init_l_Std_Time_Week_Offset_toNanoseconds___closed__0);
v___x_468_ = lean_int_mul(v_weeks_466_, v___x_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toNanoseconds___boxed(lean_object* v_weeks_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Std_Time_Week_Offset_toNanoseconds(v_weeks_469_);
lean_dec(v_weeks_469_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofNanoseconds(lean_object* v_nanos_471_){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_obj_once(&l_Std_Time_Week_Offset_toNanoseconds___closed__0, &l_Std_Time_Week_Offset_toNanoseconds___closed__0_once, _init_l_Std_Time_Week_Offset_toNanoseconds___closed__0);
v___x_473_ = lean_int_ediv(v_nanos_471_, v___x_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofNanoseconds___boxed(lean_object* v_nanos_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Std_Time_Week_Offset_ofNanoseconds(v_nanos_474_);
lean_dec(v_nanos_474_);
return v_res_475_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toSeconds___closed__0(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = lean_unsigned_to_nat(604800u);
v___x_477_ = lean_nat_to_int(v___x_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toSeconds(lean_object* v_weeks_478_){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_obj_once(&l_Std_Time_Week_Offset_toSeconds___closed__0, &l_Std_Time_Week_Offset_toSeconds___closed__0_once, _init_l_Std_Time_Week_Offset_toSeconds___closed__0);
v___x_480_ = lean_int_mul(v_weeks_478_, v___x_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toSeconds___boxed(lean_object* v_weeks_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_Time_Week_Offset_toSeconds(v_weeks_481_);
lean_dec(v_weeks_481_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofSeconds(lean_object* v_secs_483_){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_obj_once(&l_Std_Time_Week_Offset_toSeconds___closed__0, &l_Std_Time_Week_Offset_toSeconds___closed__0_once, _init_l_Std_Time_Week_Offset_toSeconds___closed__0);
v___x_485_ = lean_int_ediv(v_secs_483_, v___x_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofSeconds___boxed(lean_object* v_secs_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Std_Time_Week_Offset_ofSeconds(v_secs_486_);
lean_dec(v_secs_486_);
return v_res_487_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toMinutes___closed__0(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_unsigned_to_nat(10080u);
v___x_489_ = lean_nat_to_int(v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toMinutes(lean_object* v_weeks_490_){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = lean_obj_once(&l_Std_Time_Week_Offset_toMinutes___closed__0, &l_Std_Time_Week_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Week_Offset_toMinutes___closed__0);
v___x_492_ = lean_int_mul(v_weeks_490_, v___x_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toMinutes___boxed(lean_object* v_weeks_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Std_Time_Week_Offset_toMinutes(v_weeks_493_);
lean_dec(v_weeks_493_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofMinutes(lean_object* v_minutes_495_){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_obj_once(&l_Std_Time_Week_Offset_toMinutes___closed__0, &l_Std_Time_Week_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Week_Offset_toMinutes___closed__0);
v___x_497_ = lean_int_ediv(v_minutes_495_, v___x_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofMinutes___boxed(lean_object* v_minutes_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Std_Time_Week_Offset_ofMinutes(v_minutes_498_);
lean_dec(v_minutes_498_);
return v_res_499_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toHours___closed__0(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_unsigned_to_nat(168u);
v___x_501_ = lean_nat_to_int(v___x_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toHours(lean_object* v_weeks_502_){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_obj_once(&l_Std_Time_Week_Offset_toHours___closed__0, &l_Std_Time_Week_Offset_toHours___closed__0_once, _init_l_Std_Time_Week_Offset_toHours___closed__0);
v___x_504_ = lean_int_mul(v_weeks_502_, v___x_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toHours___boxed(lean_object* v_weeks_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Std_Time_Week_Offset_toHours(v_weeks_505_);
lean_dec(v_weeks_505_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofHours(lean_object* v_hours_507_){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = lean_obj_once(&l_Std_Time_Week_Offset_toHours___closed__0, &l_Std_Time_Week_Offset_toHours___closed__0_once, _init_l_Std_Time_Week_Offset_toHours___closed__0);
v___x_509_ = lean_int_ediv(v_hours_507_, v___x_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofHours___boxed(lean_object* v_hours_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Std_Time_Week_Offset_ofHours(v_hours_510_);
lean_dec(v_hours_510_);
return v_res_511_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toDays___closed__0(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_unsigned_to_nat(7u);
v___x_513_ = lean_nat_to_int(v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toDays(lean_object* v_weeks_514_){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_obj_once(&l_Std_Time_Week_Offset_toDays___closed__0, &l_Std_Time_Week_Offset_toDays___closed__0_once, _init_l_Std_Time_Week_Offset_toDays___closed__0);
v___x_516_ = lean_int_mul(v_weeks_514_, v___x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toDays___boxed(lean_object* v_weeks_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Std_Time_Week_Offset_toDays(v_weeks_517_);
lean_dec(v_weeks_517_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofDays(lean_object* v_days_519_){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_obj_once(&l_Std_Time_Week_Offset_toDays___closed__0, &l_Std_Time_Week_Offset_toDays___closed__0_once, _init_l_Std_Time_Week_Offset_toDays___closed__0);
v___x_521_ = lean_int_ediv(v_days_519_, v___x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofDays___boxed(lean_object* v_days_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Std_Time_Week_Offset_ofDays(v_days_522_);
lean_dec(v_days_522_);
return v_res_523_;
}
}
lean_object* runtime_initialize_Std_Time_Date_Unit_Day(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Date_Unit_Week(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time_Date_Unit_Day(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_Week_instLEOrdinal = _init_l_Std_Time_Week_instLEOrdinal();
lean_mark_persistent(l_Std_Time_Week_instLEOrdinal);
l_Std_Time_Week_instLTOrdinal = _init_l_Std_Time_Week_instLTOrdinal();
lean_mark_persistent(l_Std_Time_Week_instLTOrdinal);
l_Std_Time_Week_instInhabitedOrdinal = _init_l_Std_Time_Week_instInhabitedOrdinal();
lean_mark_persistent(l_Std_Time_Week_instInhabitedOrdinal);
l_Std_Time_Week_instInhabitedOffset___aux__1 = _init_l_Std_Time_Week_instInhabitedOffset___aux__1();
lean_mark_persistent(l_Std_Time_Week_instInhabitedOffset___aux__1);
l_Std_Time_Week_instInhabitedOffset = _init_l_Std_Time_Week_instInhabitedOffset();
lean_mark_persistent(l_Std_Time_Week_instInhabitedOffset);
l_Std_Time_Week_instLEOffset = _init_l_Std_Time_Week_instLEOffset();
lean_mark_persistent(l_Std_Time_Week_instLEOffset);
l_Std_Time_Week_instLTOffset = _init_l_Std_Time_Week_instLTOffset();
lean_mark_persistent(l_Std_Time_Week_instLTOffset);
l_Std_Time_Week_Ordinal_instInhabitedOfMonth = _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth();
lean_mark_persistent(l_Std_Time_Week_Ordinal_instInhabitedOfMonth);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Date_Unit_Week(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Std_Time_Week_Ordinal_ofNat___auto__1 = _init_l_Std_Time_Week_Ordinal_ofNat___auto__1();
lean_mark_persistent(l_Std_Time_Week_Ordinal_ofNat___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Date_Unit_Day(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Date_Unit_Week(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Date_Unit_Day(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Date_Unit_Week(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Date_Unit_Week(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Date_Unit_Week(builtin);
}
#ifdef __cplusplus
}
#endif
