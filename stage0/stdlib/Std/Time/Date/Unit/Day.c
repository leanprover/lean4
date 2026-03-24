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
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_nonneg(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Std_Time_Internal_instInhabitedUnitVal_default(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_instNatCast___lam__0(lean_object*);
lean_object* l_Int_sub___boxed(lean_object*, lean_object*);
lean_object* l_Int_repr___boxed(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_neg___boxed(lean_object*);
lean_object* l_Int_add___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableEqOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableEqOffset___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Day_instInhabitedOffset___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_instInhabitedOffset___aux__1___closed__0;
static lean_once_cell_t l_Std_Time_Day_instInhabitedOffset___aux__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_instInhabitedOffset___aux__1___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_Day_instInhabitedOffset___aux__1;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Day_instInhabitedOffset_spec__0(lean_object*);
static lean_once_cell_t l_Std_Time_Day_instInhabitedOffset___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_instInhabitedOffset___closed__0;
static lean_once_cell_t l_Std_Time_Day_instInhabitedOffset___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_instInhabitedOffset___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_Day_instInhabitedOffset;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Day_instInhabitedOffset_spec__0_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Day_Ordinal_instReprOfYear___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Day_Ordinal_instReprOfYear___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___closed__0 = (const lean_object*)&l_Std_Time_Day_Ordinal_instReprOfYear___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableEqOrdinal___aux__1(lean_object* v_x_29_, lean_object* v_x_30_){
_start:
{
uint8_t v___x_31_; 
v___x_31_ = lean_int_dec_eq(v_x_29_, v_x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableEqOrdinal___aux__1___boxed(lean_object* v_x_32_, lean_object* v_x_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l_Std_Time_Day_instDecidableEqOrdinal___aux__1(v_x_32_, v_x_33_);
lean_dec(v_x_33_);
lean_dec(v_x_32_);
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
lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_78_ = lean_int_sub(v_y_77_, v_x_76_);
v___x_79_ = lean_int_dec_nonneg(v___x_78_);
lean_dec(v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLeOrdinal___aux__1___boxed(lean_object* v_x_80_, lean_object* v_y_81_){
_start:
{
uint8_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = l_Std_Time_Day_instDecidableLeOrdinal___aux__1(v_x_80_, v_y_81_);
lean_dec(v_y_81_);
lean_dec(v_x_80_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLeOrdinal(lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
uint8_t v___x_86_; 
v___x_86_ = l_Std_Time_Day_instDecidableLeOrdinal___aux__1(v___y_84_, v___y_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLeOrdinal___boxed(lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_Std_Time_Day_instDecidableLeOrdinal(v___y_87_, v___y_88_);
lean_dec(v___y_88_);
lean_dec(v___y_87_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLtOrdinal___aux__1(lean_object* v_x_91_, lean_object* v_y_92_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_93_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_94_ = lean_int_add(v_x_91_, v___x_93_);
v___x_95_ = lean_int_sub(v_y_92_, v___x_94_);
lean_dec(v___x_94_);
v___x_96_ = lean_int_dec_nonneg(v___x_95_);
lean_dec(v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLtOrdinal___aux__1___boxed(lean_object* v_x_97_, lean_object* v_y_98_){
_start:
{
uint8_t v_res_99_; lean_object* v_r_100_; 
v_res_99_ = l_Std_Time_Day_instDecidableLtOrdinal___aux__1(v_x_97_, v_y_98_);
lean_dec(v_y_98_);
lean_dec(v_x_97_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLtOrdinal(lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
uint8_t v___x_103_; 
v___x_103_ = l_Std_Time_Day_instDecidableLtOrdinal___aux__1(v___y_101_, v___y_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLtOrdinal___boxed(lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
uint8_t v_res_106_; lean_object* v_r_107_; 
v_res_106_ = l_Std_Time_Day_instDecidableLtOrdinal(v___y_104_, v___y_105_);
lean_dec(v___y_105_);
lean_dec(v___y_104_);
v_r_107_ = lean_box(v_res_106_);
return v_r_107_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOrdinal___closed__0(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_109_ = lean_int_sub(v___x_108_, v___x_108_);
return v___x_109_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOrdinal___closed__1(void){
_start:
{
lean_object* v_range_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v_range_110_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4);
v___x_111_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOrdinal___closed__0, &l_Std_Time_Day_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Day_instInhabitedOrdinal___closed__0);
v___x_112_ = lean_int_emod(v___x_111_, v_range_110_);
return v___x_112_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOrdinal___closed__2(void){
_start:
{
lean_object* v_range_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v_range_113_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4);
v___x_114_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOrdinal___closed__1, &l_Std_Time_Day_instInhabitedOrdinal___closed__1_once, _init_l_Std_Time_Day_instInhabitedOrdinal___closed__1);
v___x_115_ = lean_int_add(v___x_114_, v_range_113_);
return v___x_115_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOrdinal___closed__3(void){
_start:
{
lean_object* v_range_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v_range_116_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4);
v___x_117_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOrdinal___closed__2, &l_Std_Time_Day_instInhabitedOrdinal___closed__2_once, _init_l_Std_Time_Day_instInhabitedOrdinal___closed__2);
v___x_118_ = lean_int_emod(v___x_117_, v_range_116_);
return v___x_118_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOrdinal___closed__4(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_119_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_120_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOrdinal___closed__3, &l_Std_Time_Day_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Day_instInhabitedOrdinal___closed__3);
v___x_121_ = lean_int_add(v___x_120_, v___x_119_);
return v___x_121_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOrdinal(void){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOrdinal___closed__4, &l_Std_Time_Day_instInhabitedOrdinal___closed__4_once, _init_l_Std_Time_Day_instInhabitedOrdinal___closed__4);
return v___x_122_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_instOrdOrdinal___aux__1(lean_object* v_x_123_, lean_object* v_y_124_){
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
LEAN_EXPORT lean_object* l_Std_Time_Day_instOrdOrdinal___aux__1___boxed(lean_object* v_x_130_, lean_object* v_y_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l_Std_Time_Day_instOrdOrdinal___aux__1(v_x_130_, v_y_131_);
lean_dec(v_y_131_);
lean_dec(v_x_130_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instReprOffset___aux__1(lean_object* v_x_136_, lean_object* v_p_137_){
_start:
{
lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_138_ = lean_obj_once(&l_Std_Time_Day_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Day_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instReprOrdinal___aux__1___closed__0);
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
LEAN_EXPORT lean_object* l_Std_Time_Day_instReprOffset___aux__1___boxed(lean_object* v_x_145_, lean_object* v_p_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Std_Time_Day_instReprOffset___aux__1(v_x_145_, v_p_146_);
lean_dec(v_p_146_);
lean_dec(v_x_145_);
return v_res_147_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableEqOffset___aux__1(lean_object* v_x_149_, lean_object* v_x_150_){
_start:
{
uint8_t v___x_151_; 
v___x_151_ = lean_int_dec_eq(v_x_149_, v_x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableEqOffset___aux__1___boxed(lean_object* v_x_152_, lean_object* v_x_153_){
_start:
{
uint8_t v_res_154_; lean_object* v_r_155_; 
v_res_154_ = l_Std_Time_Day_instDecidableEqOffset___aux__1(v_x_152_, v_x_153_);
lean_dec(v_x_153_);
lean_dec(v_x_152_);
v_r_155_ = lean_box(v_res_154_);
return v_r_155_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableEqOffset(lean_object* v_a_156_, lean_object* v_b_157_){
_start:
{
uint8_t v___x_158_; 
v___x_158_ = lean_int_dec_eq(v_a_156_, v_b_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableEqOffset___boxed(lean_object* v_a_159_, lean_object* v_b_160_){
_start:
{
uint8_t v_res_161_; lean_object* v_r_162_; 
v_res_161_ = l_Std_Time_Day_instDecidableEqOffset(v_a_159_, v_b_160_);
lean_dec(v_b_160_);
lean_dec(v_a_159_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOffset___aux__1___closed__0(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_unsigned_to_nat(86400u);
v___x_164_ = l_Rat_instNatCast___lam__0(v___x_163_);
return v___x_164_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOffset___aux__1___closed__1(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOffset___aux__1___closed__0, &l_Std_Time_Day_instInhabitedOffset___aux__1___closed__0_once, _init_l_Std_Time_Day_instInhabitedOffset___aux__1___closed__0);
v___x_166_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_165_);
return v___x_166_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOffset___aux__1(void){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOffset___aux__1___closed__1, &l_Std_Time_Day_instInhabitedOffset___aux__1___closed__1_once, _init_l_Std_Time_Day_instInhabitedOffset___aux__1___closed__1);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Day_instInhabitedOffset_spec__0(lean_object* v_a_168_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = lean_nat_to_int(v_a_168_);
v___x_170_ = l_Rat_ofInt(v___x_169_);
return v___x_170_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOffset___closed__0(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = lean_unsigned_to_nat(86400u);
v___x_172_ = l_Nat_cast___at___00Std_Time_Day_instInhabitedOffset_spec__0(v___x_171_);
return v___x_172_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOffset___closed__1(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOffset___closed__0, &l_Std_Time_Day_instInhabitedOffset___closed__0_once, _init_l_Std_Time_Day_instInhabitedOffset___closed__0);
v___x_174_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_173_);
return v___x_174_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOffset(void){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOffset___closed__1, &l_Std_Time_Day_instInhabitedOffset___closed__1_once, _init_l_Std_Time_Day_instInhabitedOffset___closed__1);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Day_instInhabitedOffset_spec__0_spec__0(lean_object* v_a_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = lean_nat_to_int(v_a_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instAddOffset___aux__1(lean_object* v_u1_178_, lean_object* v_u2_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = lean_int_add(v_u1_178_, v_u2_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instAddOffset___aux__1___boxed(lean_object* v_u1_181_, lean_object* v_u2_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Std_Time_Day_instAddOffset___aux__1(v_u1_181_, v_u2_182_);
lean_dec(v_u2_182_);
lean_dec(v_u1_181_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instSubOffset___aux__1(lean_object* v_u1_186_, lean_object* v_u2_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = lean_int_sub(v_u1_186_, v_u2_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instSubOffset___aux__1___boxed(lean_object* v_u1_189_, lean_object* v_u2_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Std_Time_Day_instSubOffset___aux__1(v_u1_189_, v_u2_190_);
lean_dec(v_u2_190_);
lean_dec(v_u1_189_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instNegOffset___aux__1(lean_object* v_x_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = lean_int_neg(v_x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instNegOffset___aux__1___boxed(lean_object* v_x_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Std_Time_Day_instNegOffset___aux__1(v_x_196_);
lean_dec(v_x_196_);
return v_res_197_;
}
}
static lean_object* _init_l_Std_Time_Day_instLEOffset(void){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_box(0);
return v___x_200_;
}
}
static lean_object* _init_l_Std_Time_Day_instLTOffset(void){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = lean_box(0);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instToStringOffset___aux__1(lean_object* v_n_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Int_repr(v_n_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instToStringOffset___aux__1___boxed(lean_object* v_n_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Std_Time_Day_instToStringOffset___aux__1(v_n_204_);
lean_dec(v_n_204_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instOfNatOffset(lean_object* v_n_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = lean_nat_to_int(v_n_208_);
return v___x_209_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLeOffset___aux__1(lean_object* v_x_210_, lean_object* v_y_211_){
_start:
{
lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_212_ = lean_int_sub(v_y_211_, v_x_210_);
v___x_213_ = lean_int_dec_nonneg(v___x_212_);
lean_dec(v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLeOffset___aux__1___boxed(lean_object* v_x_214_, lean_object* v_y_215_){
_start:
{
uint8_t v_res_216_; lean_object* v_r_217_; 
v_res_216_ = l_Std_Time_Day_instDecidableLeOffset___aux__1(v_x_214_, v_y_215_);
lean_dec(v_y_215_);
lean_dec(v_x_214_);
v_r_217_ = lean_box(v_res_216_);
return v_r_217_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLeOffset(lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
uint8_t v___x_220_; 
v___x_220_ = l_Std_Time_Day_instDecidableLeOffset___aux__1(v___y_218_, v___y_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLeOffset___boxed(lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
uint8_t v_res_223_; lean_object* v_r_224_; 
v_res_223_ = l_Std_Time_Day_instDecidableLeOffset(v___y_221_, v___y_222_);
lean_dec(v___y_222_);
lean_dec(v___y_221_);
v_r_224_ = lean_box(v_res_223_);
return v_r_224_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLtOffset___aux__1(lean_object* v_x_225_, lean_object* v_y_226_){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; 
v___x_227_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_228_ = lean_int_add(v_x_225_, v___x_227_);
v___x_229_ = lean_int_sub(v_y_226_, v___x_228_);
lean_dec(v___x_228_);
v___x_230_ = lean_int_dec_nonneg(v___x_229_);
lean_dec(v___x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLtOffset___aux__1___boxed(lean_object* v_x_231_, lean_object* v_y_232_){
_start:
{
uint8_t v_res_233_; lean_object* v_r_234_; 
v_res_233_ = l_Std_Time_Day_instDecidableLtOffset___aux__1(v_x_231_, v_y_232_);
lean_dec(v_y_232_);
lean_dec(v_x_231_);
v_r_234_ = lean_box(v_res_233_);
return v_r_234_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLtOffset(lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
uint8_t v___x_237_; 
v___x_237_ = l_Std_Time_Day_instDecidableLtOffset___aux__1(v___y_235_, v___y_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLtOffset___boxed(lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
uint8_t v_res_240_; lean_object* v_r_241_; 
v_res_240_ = l_Std_Time_Day_instDecidableLtOffset(v___y_238_, v___y_239_);
lean_dec(v___y_239_);
lean_dec(v___y_238_);
v_r_241_ = lean_box(v_res_240_);
return v_r_241_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_instOrdOffset___aux__1(lean_object* v_x_242_, lean_object* v_y_243_){
_start:
{
uint8_t v___x_244_; 
v___x_244_ = lean_int_dec_lt(v_x_242_, v_y_243_);
if (v___x_244_ == 0)
{
uint8_t v___x_245_; 
v___x_245_ = lean_int_dec_eq(v_x_242_, v_y_243_);
if (v___x_245_ == 0)
{
uint8_t v___x_246_; 
v___x_246_ = 2;
return v___x_246_;
}
else
{
uint8_t v___x_247_; 
v___x_247_ = 1;
return v___x_247_;
}
}
else
{
uint8_t v___x_248_; 
v___x_248_ = 0;
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instOrdOffset___aux__1___boxed(lean_object* v_x_249_, lean_object* v_y_250_){
_start:
{
uint8_t v_res_251_; lean_object* v_r_252_; 
v_res_251_ = l_Std_Time_Day_instOrdOffset___aux__1(v_x_249_, v_y_250_);
lean_dec(v_y_250_);
lean_dec(v_x_249_);
v_r_252_ = lean_box(v_res_251_);
return v_r_252_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt___redArg(lean_object* v_data_255_){
_start:
{
lean_inc(v_data_255_);
return v_data_255_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt___redArg___boxed(lean_object* v_data_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Std_Time_Day_Ordinal_ofInt___redArg(v_data_256_);
lean_dec(v_data_256_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt(lean_object* v_data_258_, lean_object* v_h_259_){
_start:
{
lean_inc(v_data_258_);
return v_data_258_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt___boxed(lean_object* v_data_260_, lean_object* v_h_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Std_Time_Day_Ordinal_ofInt(v_data_260_, v_h_261_);
lean_dec(v_data_260_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___lam__0(lean_object* v_r_263_, lean_object* v_p_264_){
_start:
{
lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_265_ = lean_obj_once(&l_Std_Time_Day_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Day_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instReprOrdinal___aux__1___closed__0);
v___x_266_ = lean_int_dec_lt(v_r_263_, v___x_265_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = l_Int_repr(v_r_263_);
v___x_268_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
return v___x_268_;
}
else
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_269_ = l_Int_repr(v_r_263_);
v___x_270_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
v___x_271_ = l_Repr_addAppParen(v___x_270_, v_p_264_);
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___lam__0___boxed(lean_object* v_r_272_, lean_object* v_p_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Std_Time_Day_Ordinal_instReprOfYear___lam__0(v_r_272_, v_p_273_);
lean_dec(v_p_273_);
lean_dec(v_r_272_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear(uint8_t v_leap_276_){
_start:
{
lean_object* v___f_277_; 
v___f_277_ = ((lean_object*)(l_Std_Time_Day_Ordinal_instReprOfYear___closed__0));
return v___f_277_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___boxed(lean_object* v_leap_278_){
_start:
{
uint8_t v_leap_boxed_279_; lean_object* v_res_280_; 
v_leap_boxed_279_ = lean_unbox(v_leap_278_);
v_res_280_ = l_Std_Time_Day_Ordinal_instReprOfYear(v_leap_boxed_279_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instToStringOfYear(uint8_t v_leap_281_){
_start:
{
lean_object* v___f_282_; 
v___f_282_ = ((lean_object*)(l_Std_Time_Day_instToStringOffset___closed__0));
return v___f_282_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instToStringOfYear___boxed(lean_object* v_leap_283_){
_start:
{
uint8_t v_leap_boxed_284_; lean_object* v_res_285_; 
v_leap_boxed_284_ = lean_unbox(v_leap_283_);
v_res_285_ = l_Std_Time_Day_Ordinal_instToStringOfYear(v_leap_boxed_284_);
return v_res_285_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1___redArg(lean_object* v_x_286_, lean_object* v_x_287_){
_start:
{
uint8_t v___x_288_; 
v___x_288_ = lean_int_dec_eq(v_x_286_, v_x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1___redArg___boxed(lean_object* v_x_289_, lean_object* v_x_290_){
_start:
{
uint8_t v_res_291_; lean_object* v_r_292_; 
v_res_291_ = l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1___redArg(v_x_289_, v_x_290_);
lean_dec(v_x_290_);
lean_dec(v_x_289_);
v_r_292_ = lean_box(v_res_291_);
return v_r_292_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1(uint8_t v_leap_293_, lean_object* v_x_294_, lean_object* v_x_295_){
_start:
{
uint8_t v___x_296_; 
v___x_296_ = lean_int_dec_eq(v_x_294_, v_x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1___boxed(lean_object* v_leap_297_, lean_object* v_x_298_, lean_object* v_x_299_){
_start:
{
uint8_t v_leap_boxed_300_; uint8_t v_res_301_; lean_object* v_r_302_; 
v_leap_boxed_300_ = lean_unbox(v_leap_297_);
v_res_301_ = l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1(v_leap_boxed_300_, v_x_298_, v_x_299_);
lean_dec(v_x_299_);
lean_dec(v_x_298_);
v_r_302_ = lean_box(v_res_301_);
return v_r_302_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_Ordinal_instDecidableEqOfYear___redArg(lean_object* v_a_303_, lean_object* v_b_304_){
_start:
{
uint8_t v___x_305_; 
v___x_305_ = lean_int_dec_eq(v_a_303_, v_b_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instDecidableEqOfYear___redArg___boxed(lean_object* v_a_306_, lean_object* v_b_307_){
_start:
{
uint8_t v_res_308_; lean_object* v_r_309_; 
v_res_308_ = l_Std_Time_Day_Ordinal_instDecidableEqOfYear___redArg(v_a_306_, v_b_307_);
lean_dec(v_b_307_);
lean_dec(v_a_306_);
v_r_309_ = lean_box(v_res_308_);
return v_r_309_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_Ordinal_instDecidableEqOfYear(uint8_t v_leap_310_, lean_object* v_a_311_, lean_object* v_b_312_){
_start:
{
uint8_t v___x_313_; 
v___x_313_ = lean_int_dec_eq(v_a_311_, v_b_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instDecidableEqOfYear___boxed(lean_object* v_leap_314_, lean_object* v_a_315_, lean_object* v_b_316_){
_start:
{
uint8_t v_leap_boxed_317_; uint8_t v_res_318_; lean_object* v_r_319_; 
v_leap_boxed_317_ = lean_unbox(v_leap_314_);
v_res_318_ = l_Std_Time_Day_Ordinal_instDecidableEqOfYear(v_leap_boxed_317_, v_a_315_, v_b_316_);
lean_dec(v_b_316_);
lean_dec(v_a_315_);
v_r_319_ = lean_box(v_res_318_);
return v_r_319_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___redArg(lean_object* v_x_320_, lean_object* v_y_321_){
_start:
{
uint8_t v___x_322_; 
v___x_322_ = lean_int_dec_lt(v_x_320_, v_y_321_);
if (v___x_322_ == 0)
{
uint8_t v___x_323_; 
v___x_323_ = lean_int_dec_eq(v_x_320_, v_y_321_);
if (v___x_323_ == 0)
{
uint8_t v___x_324_; 
v___x_324_ = 2;
return v___x_324_;
}
else
{
uint8_t v___x_325_; 
v___x_325_ = 1;
return v___x_325_;
}
}
else
{
uint8_t v___x_326_; 
v___x_326_ = 0;
return v___x_326_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___redArg___boxed(lean_object* v_x_327_, lean_object* v_y_328_){
_start:
{
uint8_t v_res_329_; lean_object* v_r_330_; 
v_res_329_ = l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___redArg(v_x_327_, v_y_328_);
lean_dec(v_y_328_);
lean_dec(v_x_327_);
v_r_330_ = lean_box(v_res_329_);
return v_r_330_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1(uint8_t v_leap_331_, lean_object* v_x_332_, lean_object* v_y_333_){
_start:
{
uint8_t v___x_334_; 
v___x_334_ = lean_int_dec_lt(v_x_332_, v_y_333_);
if (v___x_334_ == 0)
{
uint8_t v___x_335_; 
v___x_335_ = lean_int_dec_eq(v_x_332_, v_y_333_);
if (v___x_335_ == 0)
{
uint8_t v___x_336_; 
v___x_336_ = 2;
return v___x_336_;
}
else
{
uint8_t v___x_337_; 
v___x_337_ = 1;
return v___x_337_;
}
}
else
{
uint8_t v___x_338_; 
v___x_338_ = 0;
return v___x_338_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___boxed(lean_object* v_leap_339_, lean_object* v_x_340_, lean_object* v_y_341_){
_start:
{
uint8_t v_leap_boxed_342_; uint8_t v_res_343_; lean_object* v_r_344_; 
v_leap_boxed_342_ = lean_unbox(v_leap_339_);
v_res_343_ = l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1(v_leap_boxed_342_, v_x_340_, v_y_341_);
lean_dec(v_y_341_);
lean_dec(v_x_340_);
v_r_344_ = lean_box(v_res_343_);
return v_r_344_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOrdOfYear(uint8_t v_leap_345_){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_box(v_leap_345_);
v___x_347_ = lean_alloc_closure((void*)(l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___boxed), 3, 1);
lean_closure_set(v___x_347_, 0, v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOrdOfYear___boxed(lean_object* v_leap_348_){
_start:
{
uint8_t v_leap_boxed_349_; lean_object* v_res_350_; 
v_leap_boxed_349_ = lean_unbox(v_leap_348_);
v_res_350_ = l_Std_Time_Day_Ordinal_instOrdOfYear(v_leap_boxed_349_);
return v_res_350_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__12(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__10));
v___x_378_ = l_Lean_mkAtom(v___x_377_);
return v___x_378_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__13(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__12, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__12_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__12);
v___x_380_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5));
v___x_381_ = lean_array_push(v___x_380_, v___x_379_);
return v___x_381_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__17(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_392_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__16));
v___x_393_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5));
v___x_394_ = lean_array_push(v___x_393_, v___x_392_);
return v___x_394_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__18(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_395_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__17, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__17_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__17);
v___x_396_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__15));
v___x_397_ = lean_box(2);
v___x_398_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v___x_396_);
lean_ctor_set(v___x_398_, 2, v___x_395_);
return v___x_398_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__19(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_399_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__18, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__18_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__18);
v___x_400_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__13, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__13_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__13);
v___x_401_ = lean_array_push(v___x_400_, v___x_399_);
return v___x_401_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__20(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_402_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__19, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__19_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__19);
v___x_403_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__11));
v___x_404_ = lean_box(2);
v___x_405_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v___x_403_);
lean_ctor_set(v___x_405_, 2, v___x_402_);
return v___x_405_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__21(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_406_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__20, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__20_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__20);
v___x_407_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5));
v___x_408_ = lean_array_push(v___x_407_, v___x_406_);
return v___x_408_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__22(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_409_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__21, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__21_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__21);
v___x_410_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__9));
v___x_411_ = lean_box(2);
v___x_412_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v___x_410_);
lean_ctor_set(v___x_412_, 2, v___x_409_);
return v___x_412_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__23(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_413_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__22, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__22_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__22);
v___x_414_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5));
v___x_415_ = lean_array_push(v___x_414_, v___x_413_);
return v___x_415_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__24(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_416_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__23, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__23_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__23);
v___x_417_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__7));
v___x_418_ = lean_box(2);
v___x_419_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
lean_ctor_set(v___x_419_, 1, v___x_417_);
lean_ctor_set(v___x_419_, 2, v___x_416_);
return v___x_419_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__25(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__24, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__24_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__24);
v___x_421_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5));
v___x_422_ = lean_array_push(v___x_421_, v___x_420_);
return v___x_422_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_423_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__25, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__25_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__25);
v___x_424_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__4));
v___x_425_ = lean_box(2);
v___x_426_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
lean_ctor_set(v___x_426_, 1, v___x_424_);
lean_ctor_set(v___x_426_, 2, v___x_423_);
return v___x_426_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3(void){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___redArg(lean_object* v_data_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = lean_nat_to_int(v_data_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat(uint8_t v_leap_430_, lean_object* v_data_431_, lean_object* v_h_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = lean_nat_to_int(v_data_431_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___boxed(lean_object* v_leap_434_, lean_object* v_data_435_, lean_object* v_h_436_){
_start:
{
uint8_t v_leap_boxed_437_; lean_object* v_res_438_; 
v_leap_boxed_437_ = lean_unbox(v_leap_434_);
v_res_438_ = l_Std_Time_Day_Ordinal_OfYear_ofNat(v_leap_boxed_437_, v_data_435_, v_h_436_);
return v_res_438_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__0(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = lean_unsigned_to_nat(365u);
v___x_440_ = lean_nat_to_int(v___x_439_);
return v___x_440_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__1(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_441_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__0, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__0_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__0);
v___x_442_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_443_ = lean_int_add(v___x_442_, v___x_441_);
return v___x_443_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__2(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_444_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_445_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__1, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__1_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__1);
v___x_446_ = lean_int_sub(v___x_445_, v___x_444_);
return v___x_446_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v_range_449_; 
v___x_447_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_448_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__2, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__2_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__2);
v_range_449_ = lean_int_add(v___x_448_, v___x_447_);
return v_range_449_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1(lean_object* v_n_450_){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v_range_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_451_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_452_ = lean_nat_to_int(v_n_450_);
v_range_453_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3);
v___x_454_ = lean_int_sub(v___x_452_, v___x_451_);
lean_dec(v___x_452_);
v___x_455_ = lean_int_emod(v___x_454_, v_range_453_);
lean_dec(v___x_454_);
v___x_456_ = lean_int_add(v___x_455_, v_range_453_);
lean_dec(v___x_455_);
v___x_457_ = lean_int_emod(v___x_456_, v_range_453_);
lean_dec(v___x_456_);
v___x_458_ = lean_int_add(v___x_457_, v___x_451_);
lean_dec(v___x_457_);
return v___x_458_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__0(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = lean_unsigned_to_nat(364u);
v___x_460_ = lean_nat_to_int(v___x_459_);
return v___x_460_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__1(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_461_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__0, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__0_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__0);
v___x_462_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_463_ = lean_int_add(v___x_462_, v___x_461_);
return v___x_463_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__2(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_464_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_465_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__1, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__1_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__1);
v___x_466_ = lean_int_sub(v___x_465_, v___x_464_);
return v___x_466_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v_range_469_; 
v___x_467_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_468_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__2, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__2_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__2);
v_range_469_ = lean_int_add(v___x_468_, v___x_467_);
return v_range_469_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3(lean_object* v_n_470_){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v_range_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_471_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_472_ = lean_nat_to_int(v_n_470_);
v_range_473_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3);
v___x_474_ = lean_int_sub(v___x_472_, v___x_471_);
lean_dec(v___x_472_);
v___x_475_ = lean_int_emod(v___x_474_, v_range_473_);
lean_dec(v___x_474_);
v___x_476_ = lean_int_add(v___x_475_, v_range_473_);
lean_dec(v___x_475_);
v___x_477_ = lean_int_emod(v___x_476_, v_range_473_);
lean_dec(v___x_476_);
v___x_478_ = lean_int_add(v___x_477_, v___x_471_);
lean_dec(v___x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear(uint8_t v_leap_479_, lean_object* v_n_480_){
_start:
{
if (v_leap_479_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v_range_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_481_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_482_ = lean_nat_to_int(v_n_480_);
v_range_483_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3);
v___x_484_ = lean_int_sub(v___x_482_, v___x_481_);
lean_dec(v___x_482_);
v___x_485_ = lean_int_emod(v___x_484_, v_range_483_);
lean_dec(v___x_484_);
v___x_486_ = lean_int_add(v___x_485_, v_range_483_);
lean_dec(v___x_485_);
v___x_487_ = lean_int_emod(v___x_486_, v_range_483_);
lean_dec(v___x_486_);
v___x_488_ = lean_int_add(v___x_487_, v___x_481_);
lean_dec(v___x_487_);
return v___x_488_;
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v_range_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_489_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_490_ = lean_nat_to_int(v_n_480_);
v_range_491_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3);
v___x_492_ = lean_int_sub(v___x_490_, v___x_489_);
lean_dec(v___x_490_);
v___x_493_ = lean_int_emod(v___x_492_, v_range_491_);
lean_dec(v___x_492_);
v___x_494_ = lean_int_add(v___x_493_, v_range_491_);
lean_dec(v___x_493_);
v___x_495_ = lean_int_emod(v___x_494_, v_range_491_);
lean_dec(v___x_494_);
v___x_496_ = lean_int_add(v___x_495_, v___x_489_);
lean_dec(v___x_495_);
return v___x_496_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear___boxed(lean_object* v_leap_497_, lean_object* v_n_498_){
_start:
{
uint8_t v_leap_boxed_499_; lean_object* v_res_500_; 
v_leap_boxed_499_ = lean_unbox(v_leap_497_);
v_res_500_ = l_Std_Time_Day_Ordinal_instOfNatOfYear(v_leap_boxed_499_, v_n_498_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instInhabitedOfYear(uint8_t v_leap_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instInhabitedOfYear___boxed(lean_object* v_leap_503_){
_start:
{
uint8_t v_leap_boxed_504_; lean_object* v_res_505_; 
v_leap_boxed_504_ = lean_unbox(v_leap_503_);
v_res_505_ = l_Std_Time_Day_Ordinal_instInhabitedOfYear(v_leap_boxed_504_);
return v_res_505_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_ofNat___auto__1(void){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofNat___redArg(lean_object* v_data_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = lean_nat_to_int(v_data_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofNat(lean_object* v_data_509_, lean_object* v_h_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = lean_nat_to_int(v_data_509_);
return v___x_511_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_ofFin___closed__0(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_unsigned_to_nat(1u);
v___x_513_ = lean_nat_to_int(v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofFin(lean_object* v_data_514_){
_start:
{
lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_515_ = lean_unsigned_to_nat(1u);
v___x_516_ = lean_nat_dec_le(v___x_515_, v_data_514_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; 
lean_dec(v_data_514_);
v___x_517_ = lean_obj_once(&l_Std_Time_Day_Ordinal_ofFin___closed__0, &l_Std_Time_Day_Ordinal_ofFin___closed__0_once, _init_l_Std_Time_Day_Ordinal_ofFin___closed__0);
return v___x_517_;
}
else
{
lean_object* v___x_518_; 
v___x_518_ = lean_nat_to_int(v_data_514_);
return v___x_518_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_toOffset(lean_object* v_ordinal_519_){
_start:
{
lean_inc(v_ordinal_519_);
return v_ordinal_519_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_toOffset___boxed(lean_object* v_ordinal_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Std_Time_Day_Ordinal_toOffset(v_ordinal_520_);
lean_dec(v_ordinal_520_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_toOffset___redArg(lean_object* v_ofYear_522_){
_start:
{
lean_inc(v_ofYear_522_);
return v_ofYear_522_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_toOffset___redArg___boxed(lean_object* v_ofYear_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Std_Time_Day_Ordinal_OfYear_toOffset___redArg(v_ofYear_523_);
lean_dec(v_ofYear_523_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_toOffset(uint8_t v_leap_525_, lean_object* v_ofYear_526_){
_start:
{
lean_inc(v_ofYear_526_);
return v_ofYear_526_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_toOffset___boxed(lean_object* v_leap_527_, lean_object* v_ofYear_528_){
_start:
{
uint8_t v_leap_boxed_529_; lean_object* v_res_530_; 
v_leap_boxed_529_ = lean_unbox(v_leap_527_);
v_res_530_ = l_Std_Time_Day_Ordinal_OfYear_toOffset(v_leap_boxed_529_, v_ofYear_528_);
lean_dec(v_ofYear_528_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toOrdinal___redArg(lean_object* v_off_531_){
_start:
{
lean_inc(v_off_531_);
return v_off_531_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toOrdinal___redArg___boxed(lean_object* v_off_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Std_Time_Day_Offset_toOrdinal___redArg(v_off_532_);
lean_dec(v_off_532_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toOrdinal(lean_object* v_off_534_, lean_object* v_h_535_){
_start:
{
lean_inc(v_off_534_);
return v_off_534_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toOrdinal___boxed(lean_object* v_off_536_, lean_object* v_h_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Std_Time_Day_Offset_toOrdinal(v_off_536_, v_h_537_);
lean_dec(v_off_536_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofNat(lean_object* v_data_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = lean_nat_to_int(v_data_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofInt(lean_object* v_data_541_){
_start:
{
lean_inc(v_data_541_);
return v_data_541_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofInt___boxed(lean_object* v_data_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Std_Time_Day_Offset_ofInt(v_data_542_);
lean_dec(v_data_542_);
return v_res_543_;
}
}
static lean_object* _init_l_Std_Time_Day_Offset_toNanoseconds___closed__0(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = lean_cstr_to_nat("86400000000000");
v___x_545_ = lean_nat_to_int(v___x_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toNanoseconds(lean_object* v_days_546_){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_obj_once(&l_Std_Time_Day_Offset_toNanoseconds___closed__0, &l_Std_Time_Day_Offset_toNanoseconds___closed__0_once, _init_l_Std_Time_Day_Offset_toNanoseconds___closed__0);
v___x_548_ = lean_int_mul(v_days_546_, v___x_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toNanoseconds___boxed(lean_object* v_days_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Std_Time_Day_Offset_toNanoseconds(v_days_549_);
lean_dec(v_days_549_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofNanoseconds(lean_object* v_ns_551_){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = lean_obj_once(&l_Std_Time_Day_Offset_toNanoseconds___closed__0, &l_Std_Time_Day_Offset_toNanoseconds___closed__0_once, _init_l_Std_Time_Day_Offset_toNanoseconds___closed__0);
v___x_553_ = lean_int_ediv(v_ns_551_, v___x_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofNanoseconds___boxed(lean_object* v_ns_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Std_Time_Day_Offset_ofNanoseconds(v_ns_554_);
lean_dec(v_ns_554_);
return v_res_555_;
}
}
static lean_object* _init_l_Std_Time_Day_Offset_toMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = lean_unsigned_to_nat(86400000u);
v___x_557_ = lean_nat_to_int(v___x_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toMilliseconds(lean_object* v_days_558_){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = lean_obj_once(&l_Std_Time_Day_Offset_toMilliseconds___closed__0, &l_Std_Time_Day_Offset_toMilliseconds___closed__0_once, _init_l_Std_Time_Day_Offset_toMilliseconds___closed__0);
v___x_560_ = lean_int_mul(v_days_558_, v___x_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toMilliseconds___boxed(lean_object* v_days_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Std_Time_Day_Offset_toMilliseconds(v_days_561_);
lean_dec(v_days_561_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofMilliseconds(lean_object* v_ms_563_){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_obj_once(&l_Std_Time_Day_Offset_toMilliseconds___closed__0, &l_Std_Time_Day_Offset_toMilliseconds___closed__0_once, _init_l_Std_Time_Day_Offset_toMilliseconds___closed__0);
v___x_565_ = lean_int_ediv(v_ms_563_, v___x_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofMilliseconds___boxed(lean_object* v_ms_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Std_Time_Day_Offset_ofMilliseconds(v_ms_566_);
lean_dec(v_ms_566_);
return v_res_567_;
}
}
static lean_object* _init_l_Std_Time_Day_Offset_toSeconds___closed__0(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_unsigned_to_nat(86400u);
v___x_569_ = lean_nat_to_int(v___x_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toSeconds(lean_object* v_days_570_){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_obj_once(&l_Std_Time_Day_Offset_toSeconds___closed__0, &l_Std_Time_Day_Offset_toSeconds___closed__0_once, _init_l_Std_Time_Day_Offset_toSeconds___closed__0);
v___x_572_ = lean_int_mul(v_days_570_, v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toSeconds___boxed(lean_object* v_days_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Std_Time_Day_Offset_toSeconds(v_days_573_);
lean_dec(v_days_573_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofSeconds(lean_object* v_secs_575_){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_obj_once(&l_Std_Time_Day_Offset_toSeconds___closed__0, &l_Std_Time_Day_Offset_toSeconds___closed__0_once, _init_l_Std_Time_Day_Offset_toSeconds___closed__0);
v___x_577_ = lean_int_ediv(v_secs_575_, v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofSeconds___boxed(lean_object* v_secs_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Std_Time_Day_Offset_ofSeconds(v_secs_578_);
lean_dec(v_secs_578_);
return v_res_579_;
}
}
static lean_object* _init_l_Std_Time_Day_Offset_toMinutes___closed__0(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_unsigned_to_nat(1440u);
v___x_581_ = lean_nat_to_int(v___x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toMinutes(lean_object* v_days_582_){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = lean_obj_once(&l_Std_Time_Day_Offset_toMinutes___closed__0, &l_Std_Time_Day_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Day_Offset_toMinutes___closed__0);
v___x_584_ = lean_int_mul(v_days_582_, v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toMinutes___boxed(lean_object* v_days_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Std_Time_Day_Offset_toMinutes(v_days_585_);
lean_dec(v_days_585_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofMinutes(lean_object* v_minutes_587_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = lean_obj_once(&l_Std_Time_Day_Offset_toMinutes___closed__0, &l_Std_Time_Day_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Day_Offset_toMinutes___closed__0);
v___x_589_ = lean_int_ediv(v_minutes_587_, v___x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofMinutes___boxed(lean_object* v_minutes_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Std_Time_Day_Offset_ofMinutes(v_minutes_590_);
lean_dec(v_minutes_590_);
return v_res_591_;
}
}
static lean_object* _init_l_Std_Time_Day_Offset_toHours___closed__0(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_unsigned_to_nat(24u);
v___x_593_ = lean_nat_to_int(v___x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toHours(lean_object* v_days_594_){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_obj_once(&l_Std_Time_Day_Offset_toHours___closed__0, &l_Std_Time_Day_Offset_toHours___closed__0_once, _init_l_Std_Time_Day_Offset_toHours___closed__0);
v___x_596_ = lean_int_mul(v_days_594_, v___x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toHours___boxed(lean_object* v_days_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Std_Time_Day_Offset_toHours(v_days_597_);
lean_dec(v_days_597_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofHours(lean_object* v_hours_599_){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = lean_obj_once(&l_Std_Time_Day_Offset_toHours___closed__0, &l_Std_Time_Day_Offset_toHours___closed__0_once, _init_l_Std_Time_Day_Offset_toHours___closed__0);
v___x_601_ = lean_int_ediv(v_hours_599_, v___x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofHours___boxed(lean_object* v_hours_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Std_Time_Day_Offset_ofHours(v_hours_602_);
lean_dec(v_hours_602_);
return v_res_603_;
}
}
lean_object* runtime_initialize_Std_Time_Time(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Date_Unit_Day(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
