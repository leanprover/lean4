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
lean_object* l_Int_repr___boxed(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableEqOrdinal___aux__1(lean_object* v_a_29_, lean_object* v_b_30_){
_start:
{
uint8_t v___x_31_; 
v___x_31_ = lean_int_dec_eq(v_a_29_, v_b_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableEqOrdinal___aux__1___boxed(lean_object* v_a_32_, lean_object* v_b_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l_Std_Time_Week_instDecidableEqOrdinal___aux__1(v_a_32_, v_b_33_);
lean_dec(v_b_33_);
lean_dec(v_a_32_);
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
uint8_t v___x_78_; 
v___x_78_ = lean_int_dec_le(v_x_76_, v_y_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLeOrdinal___aux__1___boxed(lean_object* v_x_79_, lean_object* v_y_80_){
_start:
{
uint8_t v_res_81_; lean_object* v_r_82_; 
v_res_81_ = l_Std_Time_Week_instDecidableLeOrdinal___aux__1(v_x_79_, v_y_80_);
lean_dec(v_y_80_);
lean_dec(v_x_79_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLeOrdinal(lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
uint8_t v___x_85_; 
v___x_85_ = lean_int_dec_le(v___y_83_, v___y_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLeOrdinal___boxed(lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
uint8_t v_res_88_; lean_object* v_r_89_; 
v_res_88_ = l_Std_Time_Week_instDecidableLeOrdinal(v___y_86_, v___y_87_);
lean_dec(v___y_87_);
lean_dec(v___y_86_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLtOrdinal___aux__1(lean_object* v_x_90_, lean_object* v_y_91_){
_start:
{
uint8_t v___x_92_; 
v___x_92_ = lean_int_dec_lt(v_x_90_, v_y_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLtOrdinal___aux__1___boxed(lean_object* v_x_93_, lean_object* v_y_94_){
_start:
{
uint8_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = l_Std_Time_Week_instDecidableLtOrdinal___aux__1(v_x_93_, v_y_94_);
lean_dec(v_y_94_);
lean_dec(v_x_93_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLtOrdinal(lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
uint8_t v___x_99_; 
v___x_99_ = lean_int_dec_lt(v___y_97_, v___y_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLtOrdinal___boxed(lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
uint8_t v_res_102_; lean_object* v_r_103_; 
v_res_102_ = l_Std_Time_Week_instDecidableLtOrdinal(v___y_100_, v___y_101_);
lean_dec(v___y_101_);
lean_dec(v___y_100_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal___closed__0(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0);
v___x_105_ = lean_int_sub(v___x_104_, v___x_104_);
return v___x_105_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal___closed__1(void){
_start:
{
lean_object* v_range_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v_range_106_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4);
v___x_107_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__0, &l_Std_Time_Week_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__0);
v___x_108_ = lean_int_emod(v___x_107_, v_range_106_);
return v___x_108_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal___closed__2(void){
_start:
{
lean_object* v_range_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v_range_109_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4);
v___x_110_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__1, &l_Std_Time_Week_instInhabitedOrdinal___closed__1_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__1);
v___x_111_ = lean_int_add(v___x_110_, v_range_109_);
return v___x_111_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal___closed__3(void){
_start:
{
lean_object* v_range_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v_range_112_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4);
v___x_113_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__2, &l_Std_Time_Week_instInhabitedOrdinal___closed__2_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__2);
v___x_114_ = lean_int_emod(v___x_113_, v_range_112_);
return v___x_114_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal___closed__4(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_115_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0);
v___x_116_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__3, &l_Std_Time_Week_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__3);
v___x_117_ = lean_int_add(v___x_116_, v___x_115_);
return v___x_117_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal(void){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__4, &l_Std_Time_Week_instInhabitedOrdinal___closed__4_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__4);
return v___x_118_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instOrdOrdinal___aux__1(lean_object* v_x_119_, lean_object* v_y_120_){
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
LEAN_EXPORT lean_object* l_Std_Time_Week_instOrdOrdinal___aux__1___boxed(lean_object* v_x_126_, lean_object* v_y_127_){
_start:
{
uint8_t v_res_128_; lean_object* v_r_129_; 
v_res_128_ = l_Std_Time_Week_instOrdOrdinal___aux__1(v_x_126_, v_y_127_);
lean_dec(v_y_127_);
lean_dec(v_x_126_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instReprOffset___aux__1(lean_object* v_x_132_, lean_object* v_p_133_){
_start:
{
lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_134_ = lean_obj_once(&l_Std_Time_Week_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Week_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instReprOrdinal___aux__1___closed__0);
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
LEAN_EXPORT lean_object* l_Std_Time_Week_instReprOffset___aux__1___boxed(lean_object* v_x_141_, lean_object* v_p_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Std_Time_Week_instReprOffset___aux__1(v_x_141_, v_p_142_);
lean_dec(v_p_142_);
lean_dec(v_x_141_);
return v_res_143_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableEqOffset___aux__1(lean_object* v_a_145_, lean_object* v_b_146_){
_start:
{
uint8_t v___x_147_; 
v___x_147_ = lean_int_dec_eq(v_a_145_, v_b_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableEqOffset___aux__1___boxed(lean_object* v_a_148_, lean_object* v_b_149_){
_start:
{
uint8_t v_res_150_; lean_object* v_r_151_; 
v_res_150_ = l_Std_Time_Week_instDecidableEqOffset___aux__1(v_a_148_, v_b_149_);
lean_dec(v_b_149_);
lean_dec(v_a_148_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableEqOffset(lean_object* v_a_152_, lean_object* v_b_153_){
_start:
{
uint8_t v___x_154_; 
v___x_154_ = lean_int_dec_eq(v_a_152_, v_b_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableEqOffset___boxed(lean_object* v_a_155_, lean_object* v_b_156_){
_start:
{
uint8_t v_res_157_; lean_object* v_r_158_; 
v_res_157_ = l_Std_Time_Week_instDecidableEqOffset(v_a_155_, v_b_156_);
lean_dec(v_b_156_);
lean_dec(v_a_155_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_unsigned_to_nat(86400u);
v___x_160_ = l_Rat_instNatCast___lam__0(v___x_159_);
return v___x_160_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__1(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_unsigned_to_nat(7u);
v___x_162_ = l_Rat_instNatCast___lam__0(v___x_161_);
return v___x_162_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__2(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_163_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOffset___aux__1___closed__1, &l_Std_Time_Week_instInhabitedOffset___aux__1___closed__1_once, _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__1);
v___x_164_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0, &l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0_once, _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0);
v___x_165_ = l_Rat_mul(v___x_164_, v___x_163_);
return v___x_165_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__3(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOffset___aux__1___closed__2, &l_Std_Time_Week_instInhabitedOffset___aux__1___closed__2_once, _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__2);
v___x_167_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_166_);
return v___x_167_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset___aux__1(void){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOffset___aux__1___closed__3, &l_Std_Time_Week_instInhabitedOffset___aux__1___closed__3_once, _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__3);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Week_instInhabitedOffset_spec__0(lean_object* v_a_169_){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_nat_to_int(v_a_169_);
v___x_171_ = l_Rat_ofInt(v___x_170_);
return v___x_171_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset___closed__0(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = lean_unsigned_to_nat(86400u);
v___x_173_ = l_Nat_cast___at___00Std_Time_Week_instInhabitedOffset_spec__0(v___x_172_);
return v___x_173_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset___closed__1(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_unsigned_to_nat(7u);
v___x_175_ = l_Nat_cast___at___00Std_Time_Week_instInhabitedOffset_spec__0(v___x_174_);
return v___x_175_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset___closed__2(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_176_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOffset___closed__1, &l_Std_Time_Week_instInhabitedOffset___closed__1_once, _init_l_Std_Time_Week_instInhabitedOffset___closed__1);
v___x_177_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOffset___closed__0, &l_Std_Time_Week_instInhabitedOffset___closed__0_once, _init_l_Std_Time_Week_instInhabitedOffset___closed__0);
v___x_178_ = l_Rat_mul(v___x_177_, v___x_176_);
return v___x_178_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset___closed__3(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOffset___closed__2, &l_Std_Time_Week_instInhabitedOffset___closed__2_once, _init_l_Std_Time_Week_instInhabitedOffset___closed__2);
v___x_180_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_179_);
return v___x_180_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset(void){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOffset___closed__3, &l_Std_Time_Week_instInhabitedOffset___closed__3_once, _init_l_Std_Time_Week_instInhabitedOffset___closed__3);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Week_instInhabitedOffset_spec__0_spec__0(lean_object* v_a_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = lean_nat_to_int(v_a_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instAddOffset___aux__1(lean_object* v_u1_184_, lean_object* v_u2_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = lean_int_add(v_u1_184_, v_u2_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instAddOffset___aux__1___boxed(lean_object* v_u1_187_, lean_object* v_u2_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Std_Time_Week_instAddOffset___aux__1(v_u1_187_, v_u2_188_);
lean_dec(v_u2_188_);
lean_dec(v_u1_187_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instSubOffset___aux__1(lean_object* v_u1_192_, lean_object* v_u2_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = lean_int_sub(v_u1_192_, v_u2_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instSubOffset___aux__1___boxed(lean_object* v_u1_195_, lean_object* v_u2_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Std_Time_Week_instSubOffset___aux__1(v_u1_195_, v_u2_196_);
lean_dec(v_u2_196_);
lean_dec(v_u1_195_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instNegOffset___aux__1(lean_object* v_x_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = lean_int_neg(v_x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instNegOffset___aux__1___boxed(lean_object* v_x_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Std_Time_Week_instNegOffset___aux__1(v_x_202_);
lean_dec(v_x_202_);
return v_res_203_;
}
}
static lean_object* _init_l_Std_Time_Week_instLEOffset(void){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = lean_box(0);
return v___x_206_;
}
}
static lean_object* _init_l_Std_Time_Week_instLTOffset(void){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = lean_box(0);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instToStringOffset___aux__1(lean_object* v_n_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Int_repr(v_n_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instToStringOffset___aux__1___boxed(lean_object* v_n_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Std_Time_Week_instToStringOffset___aux__1(v_n_210_);
lean_dec(v_n_210_);
return v_res_211_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLeOffset___aux__1(lean_object* v_x_214_, lean_object* v_y_215_){
_start:
{
uint8_t v___x_216_; 
v___x_216_ = lean_int_dec_le(v_x_214_, v_y_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLeOffset___aux__1___boxed(lean_object* v_x_217_, lean_object* v_y_218_){
_start:
{
uint8_t v_res_219_; lean_object* v_r_220_; 
v_res_219_ = l_Std_Time_Week_instDecidableLeOffset___aux__1(v_x_217_, v_y_218_);
lean_dec(v_y_218_);
lean_dec(v_x_217_);
v_r_220_ = lean_box(v_res_219_);
return v_r_220_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLeOffset(lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
uint8_t v___x_223_; 
v___x_223_ = lean_int_dec_le(v___y_221_, v___y_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLeOffset___boxed(lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
uint8_t v_res_226_; lean_object* v_r_227_; 
v_res_226_ = l_Std_Time_Week_instDecidableLeOffset(v___y_224_, v___y_225_);
lean_dec(v___y_225_);
lean_dec(v___y_224_);
v_r_227_ = lean_box(v_res_226_);
return v_r_227_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLtOffset___aux__1(lean_object* v_x_228_, lean_object* v_y_229_){
_start:
{
uint8_t v___x_230_; 
v___x_230_ = lean_int_dec_lt(v_x_228_, v_y_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLtOffset___aux__1___boxed(lean_object* v_x_231_, lean_object* v_y_232_){
_start:
{
uint8_t v_res_233_; lean_object* v_r_234_; 
v_res_233_ = l_Std_Time_Week_instDecidableLtOffset___aux__1(v_x_231_, v_y_232_);
lean_dec(v_y_232_);
lean_dec(v_x_231_);
v_r_234_ = lean_box(v_res_233_);
return v_r_234_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLtOffset(lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
uint8_t v___x_237_; 
v___x_237_ = lean_int_dec_lt(v___y_235_, v___y_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLtOffset___boxed(lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
uint8_t v_res_240_; lean_object* v_r_241_; 
v_res_240_ = l_Std_Time_Week_instDecidableLtOffset(v___y_238_, v___y_239_);
lean_dec(v___y_239_);
lean_dec(v___y_238_);
v_r_241_ = lean_box(v_res_240_);
return v_r_241_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instOfNatOffset(lean_object* v_n_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = lean_nat_to_int(v_n_242_);
return v___x_243_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instOrdOffset___aux__1(lean_object* v_x_244_, lean_object* v_y_245_){
_start:
{
uint8_t v___x_246_; 
v___x_246_ = lean_int_dec_lt(v_x_244_, v_y_245_);
if (v___x_246_ == 0)
{
uint8_t v___x_247_; 
v___x_247_ = lean_int_dec_eq(v_x_244_, v_y_245_);
if (v___x_247_ == 0)
{
uint8_t v___x_248_; 
v___x_248_ = 2;
return v___x_248_;
}
else
{
uint8_t v___x_249_; 
v___x_249_ = 1;
return v___x_249_;
}
}
else
{
uint8_t v___x_250_; 
v___x_250_ = 0;
return v___x_250_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instOrdOffset___aux__1___boxed(lean_object* v_x_251_, lean_object* v_y_252_){
_start:
{
uint8_t v_res_253_; lean_object* v_r_254_; 
v_res_253_ = l_Std_Time_Week_instOrdOffset___aux__1(v_x_251_, v_y_252_);
lean_dec(v_y_252_);
lean_dec(v_x_251_);
v_r_254_ = lean_box(v_res_253_);
return v_r_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofInt___redArg(lean_object* v_data_257_){
_start:
{
lean_inc(v_data_257_);
return v_data_257_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofInt___redArg___boxed(lean_object* v_data_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Std_Time_Week_Ordinal_ofInt___redArg(v_data_258_);
lean_dec(v_data_258_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofInt(lean_object* v_data_260_, lean_object* v_h_261_){
_start:
{
lean_inc(v_data_260_);
return v_data_260_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofInt___boxed(lean_object* v_data_262_, lean_object* v_h_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Std_Time_Week_Ordinal_ofInt(v_data_262_, v_h_263_);
lean_dec(v_data_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_instReprOfMonth___aux__1(lean_object* v_n_265_, lean_object* v_a_266_){
_start:
{
lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_267_ = lean_obj_once(&l_Std_Time_Week_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Week_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instReprOrdinal___aux__1___closed__0);
v___x_268_ = lean_int_dec_lt(v_n_265_, v___x_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = l_Int_repr(v_n_265_);
v___x_270_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
return v___x_270_;
}
else
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = l_Int_repr(v_n_265_);
v___x_272_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
v___x_273_ = l_Repr_addAppParen(v___x_272_, v_a_266_);
return v___x_273_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_instReprOfMonth___aux__1___boxed(lean_object* v_n_274_, lean_object* v_a_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Std_Time_Week_Ordinal_instReprOfMonth___aux__1(v_n_274_, v_a_275_);
lean_dec(v_a_275_);
lean_dec(v_n_274_);
return v_res_276_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_Ordinal_instDecidableEqOfMonth___aux__1(lean_object* v_a_278_, lean_object* v_b_279_){
_start:
{
uint8_t v___x_280_; 
v___x_280_ = lean_int_dec_eq(v_a_278_, v_b_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_instDecidableEqOfMonth___aux__1___boxed(lean_object* v_a_281_, lean_object* v_b_282_){
_start:
{
uint8_t v_res_283_; lean_object* v_r_284_; 
v_res_283_ = l_Std_Time_Week_Ordinal_instDecidableEqOfMonth___aux__1(v_a_281_, v_b_282_);
lean_dec(v_b_282_);
lean_dec(v_a_281_);
v_r_284_ = lean_box(v_res_283_);
return v_r_284_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_Ordinal_instDecidableEqOfMonth(lean_object* v_a_285_, lean_object* v_b_286_){
_start:
{
uint8_t v___x_287_; 
v___x_287_ = lean_int_dec_eq(v_a_285_, v_b_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_instDecidableEqOfMonth___boxed(lean_object* v_a_288_, lean_object* v_b_289_){
_start:
{
uint8_t v_res_290_; lean_object* v_r_291_; 
v_res_290_ = l_Std_Time_Week_Ordinal_instDecidableEqOfMonth(v_a_288_, v_b_289_);
lean_dec(v_b_289_);
lean_dec(v_a_288_);
v_r_291_ = lean_box(v_res_290_);
return v_r_291_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__0(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = lean_unsigned_to_nat(5u);
v___x_293_ = lean_nat_to_int(v___x_292_);
return v___x_293_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__1(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_294_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__0, &l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__0_once, _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__0);
v___x_295_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0);
v___x_296_ = lean_int_add(v___x_295_, v___x_294_);
return v___x_296_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__2(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_297_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0);
v___x_298_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__1, &l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__1_once, _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__1);
v___x_299_ = lean_int_sub(v___x_298_, v___x_297_);
return v___x_299_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v_range_302_; 
v___x_300_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0);
v___x_301_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__2, &l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__2_once, _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__2);
v_range_302_ = lean_int_add(v___x_301_, v___x_300_);
return v_range_302_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1(lean_object* v_n_303_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v_range_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_304_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0);
v___x_305_ = lean_nat_to_int(v_n_303_);
v_range_306_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3, &l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3_once, _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3);
v___x_307_ = lean_int_sub(v___x_305_, v___x_304_);
lean_dec(v___x_305_);
v___x_308_ = lean_int_emod(v___x_307_, v_range_306_);
lean_dec(v___x_307_);
v___x_309_ = lean_int_add(v___x_308_, v_range_306_);
lean_dec(v___x_308_);
v___x_310_ = lean_int_emod(v___x_309_, v_range_306_);
lean_dec(v___x_309_);
v___x_311_ = lean_int_add(v___x_310_, v___x_304_);
lean_dec(v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_instOfNatOfMonth(lean_object* v_n_312_){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v_range_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_313_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0);
v___x_314_ = lean_nat_to_int(v_n_312_);
v_range_315_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3, &l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3_once, _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3);
v___x_316_ = lean_int_sub(v___x_314_, v___x_313_);
lean_dec(v___x_314_);
v___x_317_ = lean_int_emod(v___x_316_, v_range_315_);
lean_dec(v___x_316_);
v___x_318_ = lean_int_add(v___x_317_, v_range_315_);
lean_dec(v___x_317_);
v___x_319_ = lean_int_emod(v___x_318_, v_range_315_);
lean_dec(v___x_318_);
v___x_320_ = lean_int_add(v___x_319_, v___x_313_);
lean_dec(v___x_319_);
return v___x_320_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__0(void){
_start:
{
lean_object* v_range_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v_range_321_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3, &l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3_once, _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3);
v___x_322_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__0, &l_Std_Time_Week_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__0);
v___x_323_ = lean_int_emod(v___x_322_, v_range_321_);
return v___x_323_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__1(void){
_start:
{
lean_object* v_range_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v_range_324_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3, &l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3_once, _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3);
v___x_325_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__0, &l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__0_once, _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__0);
v___x_326_ = lean_int_add(v___x_325_, v_range_324_);
return v___x_326_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__2(void){
_start:
{
lean_object* v_range_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v_range_327_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3, &l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3_once, _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3);
v___x_328_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__1, &l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__1_once, _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__1);
v___x_329_ = lean_int_emod(v___x_328_, v_range_327_);
return v___x_329_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_330_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0);
v___x_331_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__2, &l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__2_once, _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__2);
v___x_332_ = lean_int_add(v___x_331_, v___x_330_);
return v___x_332_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth(void){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3, &l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3_once, _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3);
return v___x_333_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_Ordinal_instOrdOfMonth___aux__1(lean_object* v_x_334_, lean_object* v_y_335_){
_start:
{
uint8_t v___x_336_; 
v___x_336_ = lean_int_dec_lt(v_x_334_, v_y_335_);
if (v___x_336_ == 0)
{
uint8_t v___x_337_; 
v___x_337_ = lean_int_dec_eq(v_x_334_, v_y_335_);
if (v___x_337_ == 0)
{
uint8_t v___x_338_; 
v___x_338_ = 2;
return v___x_338_;
}
else
{
uint8_t v___x_339_; 
v___x_339_ = 1;
return v___x_339_;
}
}
else
{
uint8_t v___x_340_; 
v___x_340_ = 0;
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_instOrdOfMonth___aux__1___boxed(lean_object* v_x_341_, lean_object* v_y_342_){
_start:
{
uint8_t v_res_343_; lean_object* v_r_344_; 
v_res_343_ = l_Std_Time_Week_Ordinal_instOrdOfMonth___aux__1(v_x_341_, v_y_342_);
lean_dec(v_y_342_);
lean_dec(v_x_341_);
v_r_344_ = lean_box(v_res_343_);
return v_r_344_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__12(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__10));
v___x_374_ = l_Lean_mkAtom(v___x_373_);
return v___x_374_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__13(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_375_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__12, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__12_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__12);
v___x_376_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5));
v___x_377_ = lean_array_push(v___x_376_, v___x_375_);
return v___x_377_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__17(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_388_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__16));
v___x_389_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5));
v___x_390_ = lean_array_push(v___x_389_, v___x_388_);
return v___x_390_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__18(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_391_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__17, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__17_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__17);
v___x_392_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15));
v___x_393_ = lean_box(2);
v___x_394_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v___x_392_);
lean_ctor_set(v___x_394_, 2, v___x_391_);
return v___x_394_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__19(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_395_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__18, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__18_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__18);
v___x_396_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__13, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__13_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__13);
v___x_397_ = lean_array_push(v___x_396_, v___x_395_);
return v___x_397_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__20(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_398_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__19, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__19_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__19);
v___x_399_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11));
v___x_400_ = lean_box(2);
v___x_401_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
lean_ctor_set(v___x_401_, 1, v___x_399_);
lean_ctor_set(v___x_401_, 2, v___x_398_);
return v___x_401_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__21(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_402_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__20, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__20_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__20);
v___x_403_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5));
v___x_404_ = lean_array_push(v___x_403_, v___x_402_);
return v___x_404_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__22(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_405_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__21, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__21_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__21);
v___x_406_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__9));
v___x_407_ = lean_box(2);
v___x_408_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set(v___x_408_, 1, v___x_406_);
lean_ctor_set(v___x_408_, 2, v___x_405_);
return v___x_408_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__23(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_409_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__22, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__22_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__22);
v___x_410_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5));
v___x_411_ = lean_array_push(v___x_410_, v___x_409_);
return v___x_411_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__24(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_412_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__23, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__23_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__23);
v___x_413_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7));
v___x_414_ = lean_box(2);
v___x_415_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
lean_ctor_set(v___x_415_, 1, v___x_413_);
lean_ctor_set(v___x_415_, 2, v___x_412_);
return v___x_415_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__25(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_416_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__24, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__24_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__24);
v___x_417_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5));
v___x_418_ = lean_array_push(v___x_417_, v___x_416_);
return v___x_418_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__26(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_419_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__25, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__25_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__25);
v___x_420_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4));
v___x_421_ = lean_box(2);
v___x_422_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v___x_420_);
lean_ctor_set(v___x_422_, 2, v___x_419_);
return v___x_422_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1(void){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__26, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__26_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__26);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofNat___redArg(lean_object* v_data_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = lean_nat_to_int(v_data_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofNat(lean_object* v_data_426_, lean_object* v_h_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = lean_nat_to_int(v_data_426_);
return v___x_428_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofFin___closed__0(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_unsigned_to_nat(1u);
v___x_430_ = lean_nat_to_int(v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofFin(lean_object* v_data_431_){
_start:
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = lean_unsigned_to_nat(1u);
v___x_433_ = lean_nat_dec_le(v___x_432_, v_data_431_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; 
lean_dec(v_data_431_);
v___x_434_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofFin___closed__0, &l_Std_Time_Week_Ordinal_ofFin___closed__0_once, _init_l_Std_Time_Week_Ordinal_ofFin___closed__0);
return v___x_434_;
}
else
{
lean_object* v___x_435_; 
v___x_435_ = lean_nat_to_int(v_data_431_);
return v___x_435_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_toOffset(lean_object* v_ordinal_436_){
_start:
{
lean_inc(v_ordinal_436_);
return v_ordinal_436_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_toOffset___boxed(lean_object* v_ordinal_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Std_Time_Week_Ordinal_toOffset(v_ordinal_437_);
lean_dec(v_ordinal_437_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofNat(lean_object* v_data_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = lean_nat_to_int(v_data_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofInt(lean_object* v_data_441_){
_start:
{
lean_inc(v_data_441_);
return v_data_441_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofInt___boxed(lean_object* v_data_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Std_Time_Week_Offset_ofInt(v_data_442_);
lean_dec(v_data_442_);
return v_res_443_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_unsigned_to_nat(604800000u);
v___x_445_ = lean_nat_to_int(v___x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toMilliseconds(lean_object* v_weeks_446_){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = lean_obj_once(&l_Std_Time_Week_Offset_toMilliseconds___closed__0, &l_Std_Time_Week_Offset_toMilliseconds___closed__0_once, _init_l_Std_Time_Week_Offset_toMilliseconds___closed__0);
v___x_448_ = lean_int_mul(v_weeks_446_, v___x_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toMilliseconds___boxed(lean_object* v_weeks_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Std_Time_Week_Offset_toMilliseconds(v_weeks_449_);
lean_dec(v_weeks_449_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofMilliseconds(lean_object* v_millis_451_){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = lean_obj_once(&l_Std_Time_Week_Offset_toMilliseconds___closed__0, &l_Std_Time_Week_Offset_toMilliseconds___closed__0_once, _init_l_Std_Time_Week_Offset_toMilliseconds___closed__0);
v___x_453_ = lean_int_ediv(v_millis_451_, v___x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofMilliseconds___boxed(lean_object* v_millis_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Std_Time_Week_Offset_ofMilliseconds(v_millis_454_);
lean_dec(v_millis_454_);
return v_res_455_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toNanoseconds___closed__0(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_cstr_to_nat("604800000000000");
v___x_457_ = lean_nat_to_int(v___x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toNanoseconds(lean_object* v_weeks_458_){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = lean_obj_once(&l_Std_Time_Week_Offset_toNanoseconds___closed__0, &l_Std_Time_Week_Offset_toNanoseconds___closed__0_once, _init_l_Std_Time_Week_Offset_toNanoseconds___closed__0);
v___x_460_ = lean_int_mul(v_weeks_458_, v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toNanoseconds___boxed(lean_object* v_weeks_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Std_Time_Week_Offset_toNanoseconds(v_weeks_461_);
lean_dec(v_weeks_461_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofNanoseconds(lean_object* v_nanos_463_){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_obj_once(&l_Std_Time_Week_Offset_toNanoseconds___closed__0, &l_Std_Time_Week_Offset_toNanoseconds___closed__0_once, _init_l_Std_Time_Week_Offset_toNanoseconds___closed__0);
v___x_465_ = lean_int_ediv(v_nanos_463_, v___x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofNanoseconds___boxed(lean_object* v_nanos_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Std_Time_Week_Offset_ofNanoseconds(v_nanos_466_);
lean_dec(v_nanos_466_);
return v_res_467_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toSeconds___closed__0(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_unsigned_to_nat(604800u);
v___x_469_ = lean_nat_to_int(v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toSeconds(lean_object* v_weeks_470_){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = lean_obj_once(&l_Std_Time_Week_Offset_toSeconds___closed__0, &l_Std_Time_Week_Offset_toSeconds___closed__0_once, _init_l_Std_Time_Week_Offset_toSeconds___closed__0);
v___x_472_ = lean_int_mul(v_weeks_470_, v___x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toSeconds___boxed(lean_object* v_weeks_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Std_Time_Week_Offset_toSeconds(v_weeks_473_);
lean_dec(v_weeks_473_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofSeconds(lean_object* v_secs_475_){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = lean_obj_once(&l_Std_Time_Week_Offset_toSeconds___closed__0, &l_Std_Time_Week_Offset_toSeconds___closed__0_once, _init_l_Std_Time_Week_Offset_toSeconds___closed__0);
v___x_477_ = lean_int_ediv(v_secs_475_, v___x_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofSeconds___boxed(lean_object* v_secs_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Std_Time_Week_Offset_ofSeconds(v_secs_478_);
lean_dec(v_secs_478_);
return v_res_479_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toMinutes___closed__0(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = lean_unsigned_to_nat(10080u);
v___x_481_ = lean_nat_to_int(v___x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toMinutes(lean_object* v_weeks_482_){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_obj_once(&l_Std_Time_Week_Offset_toMinutes___closed__0, &l_Std_Time_Week_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Week_Offset_toMinutes___closed__0);
v___x_484_ = lean_int_mul(v_weeks_482_, v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toMinutes___boxed(lean_object* v_weeks_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Std_Time_Week_Offset_toMinutes(v_weeks_485_);
lean_dec(v_weeks_485_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofMinutes(lean_object* v_minutes_487_){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_obj_once(&l_Std_Time_Week_Offset_toMinutes___closed__0, &l_Std_Time_Week_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Week_Offset_toMinutes___closed__0);
v___x_489_ = lean_int_ediv(v_minutes_487_, v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofMinutes___boxed(lean_object* v_minutes_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Std_Time_Week_Offset_ofMinutes(v_minutes_490_);
lean_dec(v_minutes_490_);
return v_res_491_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toHours___closed__0(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_unsigned_to_nat(168u);
v___x_493_ = lean_nat_to_int(v___x_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toHours(lean_object* v_weeks_494_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_obj_once(&l_Std_Time_Week_Offset_toHours___closed__0, &l_Std_Time_Week_Offset_toHours___closed__0_once, _init_l_Std_Time_Week_Offset_toHours___closed__0);
v___x_496_ = lean_int_mul(v_weeks_494_, v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toHours___boxed(lean_object* v_weeks_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Std_Time_Week_Offset_toHours(v_weeks_497_);
lean_dec(v_weeks_497_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofHours(lean_object* v_hours_499_){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_obj_once(&l_Std_Time_Week_Offset_toHours___closed__0, &l_Std_Time_Week_Offset_toHours___closed__0_once, _init_l_Std_Time_Week_Offset_toHours___closed__0);
v___x_501_ = lean_int_ediv(v_hours_499_, v___x_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofHours___boxed(lean_object* v_hours_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Std_Time_Week_Offset_ofHours(v_hours_502_);
lean_dec(v_hours_502_);
return v_res_503_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toDays___closed__0(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_unsigned_to_nat(7u);
v___x_505_ = lean_nat_to_int(v___x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toDays(lean_object* v_weeks_506_){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_obj_once(&l_Std_Time_Week_Offset_toDays___closed__0, &l_Std_Time_Week_Offset_toDays___closed__0_once, _init_l_Std_Time_Week_Offset_toDays___closed__0);
v___x_508_ = lean_int_mul(v_weeks_506_, v___x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toDays___boxed(lean_object* v_weeks_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Std_Time_Week_Offset_toDays(v_weeks_509_);
lean_dec(v_weeks_509_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofDays(lean_object* v_days_511_){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_obj_once(&l_Std_Time_Week_Offset_toDays___closed__0, &l_Std_Time_Week_Offset_toDays___closed__0_once, _init_l_Std_Time_Week_Offset_toDays___closed__0);
v___x_513_ = lean_int_ediv(v_days_511_, v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofDays___boxed(lean_object* v_days_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Std_Time_Week_Offset_ofDays(v_days_514_);
lean_dec(v_days_514_);
return v_res_515_;
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
