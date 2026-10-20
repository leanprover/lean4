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
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt___redArg(lean_object* v_data_240_){
_start:
{
lean_inc(v_data_240_);
return v_data_240_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt___redArg___boxed(lean_object* v_data_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Std_Time_Day_Ordinal_ofInt___redArg(v_data_241_);
lean_dec(v_data_241_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt(lean_object* v_data_243_, lean_object* v_h_244_){
_start:
{
lean_inc(v_data_243_);
return v_data_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt___boxed(lean_object* v_data_245_, lean_object* v_h_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Std_Time_Day_Ordinal_ofInt(v_data_245_, v_h_246_);
lean_dec(v_data_245_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___redArg___lam__0(lean_object* v_r_248_, lean_object* v_p_249_){
_start:
{
lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_250_ = lean_obj_once(&l_Std_Time_Day_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Day_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instReprOrdinal___aux__1___closed__0);
v___x_251_ = lean_int_dec_lt(v_r_248_, v___x_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = l_Int_repr(v_r_248_);
v___x_253_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
return v___x_253_;
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = l_Int_repr(v_r_248_);
v___x_255_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
v___x_256_ = l_Repr_addAppParen(v___x_255_, v_p_249_);
return v___x_256_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___redArg___lam__0___boxed(lean_object* v_r_257_, lean_object* v_p_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Std_Time_Day_Ordinal_instReprOfYear___redArg___lam__0(v_r_257_, v_p_258_);
lean_dec(v_p_258_);
lean_dec(v_r_257_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___redArg(){
_start:
{
lean_object* v___f_262_; 
v___f_262_ = ((lean_object*)(l_Std_Time_Day_Ordinal_instReprOfYear___redArg___closed__0));
return v___f_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___redArg___boxed(lean_object* v___dummy_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Std_Time_Day_Ordinal_instReprOfYear___redArg();
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear(uint8_t v_leap_265_){
_start:
{
lean_object* v___f_266_; 
v___f_266_ = ((lean_object*)(l_Std_Time_Day_Ordinal_instReprOfYear___redArg___closed__0));
return v___f_266_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___boxed(lean_object* v_leap_267_){
_start:
{
uint8_t v_leap_boxed_268_; lean_object* v_res_269_; 
v_leap_boxed_268_ = lean_unbox(v_leap_267_);
v_res_269_ = l_Std_Time_Day_Ordinal_instReprOfYear(v_leap_boxed_268_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instToStringOfYear___redArg(){
_start:
{
lean_object* v___f_271_; 
v___f_271_ = ((lean_object*)(l_Std_Time_Day_instToStringOffset___closed__0));
return v___f_271_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instToStringOfYear___redArg___boxed(lean_object* v___dummy_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Std_Time_Day_Ordinal_instToStringOfYear___redArg();
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instToStringOfYear(uint8_t v_leap_274_){
_start:
{
lean_object* v___f_275_; 
v___f_275_ = ((lean_object*)(l_Std_Time_Day_instToStringOffset___closed__0));
return v___f_275_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instToStringOfYear___boxed(lean_object* v_leap_276_){
_start:
{
uint8_t v_leap_boxed_277_; lean_object* v_res_278_; 
v_leap_boxed_277_ = lean_unbox(v_leap_276_);
v_res_278_ = l_Std_Time_Day_Ordinal_instToStringOfYear(v_leap_boxed_277_);
return v_res_278_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1___redArg(lean_object* v_a_279_, lean_object* v_b_280_){
_start:
{
uint8_t v___x_281_; 
v___x_281_ = lean_int_dec_eq(v_a_279_, v_b_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1___redArg___boxed(lean_object* v_a_282_, lean_object* v_b_283_){
_start:
{
uint8_t v_res_284_; lean_object* v_r_285_; 
v_res_284_ = l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1___redArg(v_a_282_, v_b_283_);
lean_dec(v_b_283_);
lean_dec(v_a_282_);
v_r_285_ = lean_box(v_res_284_);
return v_r_285_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1(uint8_t v_leap_286_, lean_object* v_a_287_, lean_object* v_b_288_){
_start:
{
uint8_t v___x_289_; 
v___x_289_ = lean_int_dec_eq(v_a_287_, v_b_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1___boxed(lean_object* v_leap_290_, lean_object* v_a_291_, lean_object* v_b_292_){
_start:
{
uint8_t v_leap_boxed_293_; uint8_t v_res_294_; lean_object* v_r_295_; 
v_leap_boxed_293_ = lean_unbox(v_leap_290_);
v_res_294_ = l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1(v_leap_boxed_293_, v_a_291_, v_b_292_);
lean_dec(v_b_292_);
lean_dec(v_a_291_);
v_r_295_ = lean_box(v_res_294_);
return v_r_295_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_Ordinal_instDecidableEqOfYear___redArg(lean_object* v_a_296_, lean_object* v_b_297_){
_start:
{
uint8_t v___x_298_; 
v___x_298_ = lean_int_dec_eq(v_a_296_, v_b_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instDecidableEqOfYear___redArg___boxed(lean_object* v_a_299_, lean_object* v_b_300_){
_start:
{
uint8_t v_res_301_; lean_object* v_r_302_; 
v_res_301_ = l_Std_Time_Day_Ordinal_instDecidableEqOfYear___redArg(v_a_299_, v_b_300_);
lean_dec(v_b_300_);
lean_dec(v_a_299_);
v_r_302_ = lean_box(v_res_301_);
return v_r_302_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_Ordinal_instDecidableEqOfYear(uint8_t v_leap_303_, lean_object* v_a_304_, lean_object* v_b_305_){
_start:
{
uint8_t v___x_306_; 
v___x_306_ = lean_int_dec_eq(v_a_304_, v_b_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instDecidableEqOfYear___boxed(lean_object* v_leap_307_, lean_object* v_a_308_, lean_object* v_b_309_){
_start:
{
uint8_t v_leap_boxed_310_; uint8_t v_res_311_; lean_object* v_r_312_; 
v_leap_boxed_310_ = lean_unbox(v_leap_307_);
v_res_311_ = l_Std_Time_Day_Ordinal_instDecidableEqOfYear(v_leap_boxed_310_, v_a_308_, v_b_309_);
lean_dec(v_b_309_);
lean_dec(v_a_308_);
v_r_312_ = lean_box(v_res_311_);
return v_r_312_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___redArg(lean_object* v_x_313_, lean_object* v_y_314_){
_start:
{
uint8_t v___x_315_; 
v___x_315_ = lean_int_dec_lt(v_x_313_, v_y_314_);
if (v___x_315_ == 0)
{
uint8_t v___x_316_; 
v___x_316_ = lean_int_dec_eq(v_x_313_, v_y_314_);
if (v___x_316_ == 0)
{
uint8_t v___x_317_; 
v___x_317_ = 2;
return v___x_317_;
}
else
{
uint8_t v___x_318_; 
v___x_318_ = 1;
return v___x_318_;
}
}
else
{
uint8_t v___x_319_; 
v___x_319_ = 0;
return v___x_319_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___redArg___boxed(lean_object* v_x_320_, lean_object* v_y_321_){
_start:
{
uint8_t v_res_322_; lean_object* v_r_323_; 
v_res_322_ = l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___redArg(v_x_320_, v_y_321_);
lean_dec(v_y_321_);
lean_dec(v_x_320_);
v_r_323_ = lean_box(v_res_322_);
return v_r_323_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1(uint8_t v_leap_324_, lean_object* v_x_325_, lean_object* v_y_326_){
_start:
{
uint8_t v___x_327_; 
v___x_327_ = lean_int_dec_lt(v_x_325_, v_y_326_);
if (v___x_327_ == 0)
{
uint8_t v___x_328_; 
v___x_328_ = lean_int_dec_eq(v_x_325_, v_y_326_);
if (v___x_328_ == 0)
{
uint8_t v___x_329_; 
v___x_329_ = 2;
return v___x_329_;
}
else
{
uint8_t v___x_330_; 
v___x_330_ = 1;
return v___x_330_;
}
}
else
{
uint8_t v___x_331_; 
v___x_331_ = 0;
return v___x_331_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___boxed(lean_object* v_leap_332_, lean_object* v_x_333_, lean_object* v_y_334_){
_start:
{
uint8_t v_leap_boxed_335_; uint8_t v_res_336_; lean_object* v_r_337_; 
v_leap_boxed_335_ = lean_unbox(v_leap_332_);
v_res_336_ = l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1(v_leap_boxed_335_, v_x_333_, v_y_334_);
lean_dec(v_y_334_);
lean_dec(v_x_333_);
v_r_337_ = lean_box(v_res_336_);
return v_r_337_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOrdOfYear(uint8_t v_leap_338_){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_box(v_leap_338_);
v___x_340_ = lean_alloc_closure((void*)(l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___boxed), 3, 1);
lean_closure_set(v___x_340_, 0, v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOrdOfYear___boxed(lean_object* v_leap_341_){
_start:
{
uint8_t v_leap_boxed_342_; lean_object* v_res_343_; 
v_leap_boxed_342_ = lean_unbox(v_leap_341_);
v_res_343_ = l_Std_Time_Day_Ordinal_instOrdOfYear(v_leap_boxed_342_);
return v_res_343_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__12(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__10));
v___x_371_ = l_Lean_mkAtom(v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__13(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_372_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__12, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__12_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__12);
v___x_373_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5));
v___x_374_ = lean_array_push(v___x_373_, v___x_372_);
return v___x_374_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__17(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_385_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__16));
v___x_386_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5));
v___x_387_ = lean_array_push(v___x_386_, v___x_385_);
return v___x_387_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__18(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_388_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__17, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__17_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__17);
v___x_389_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__15));
v___x_390_ = lean_box(2);
v___x_391_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
lean_ctor_set(v___x_391_, 1, v___x_389_);
lean_ctor_set(v___x_391_, 2, v___x_388_);
return v___x_391_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__19(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_392_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__18, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__18_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__18);
v___x_393_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__13, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__13_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__13);
v___x_394_ = lean_array_push(v___x_393_, v___x_392_);
return v___x_394_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__20(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_395_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__19, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__19_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__19);
v___x_396_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__11));
v___x_397_ = lean_box(2);
v___x_398_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v___x_396_);
lean_ctor_set(v___x_398_, 2, v___x_395_);
return v___x_398_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__21(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_399_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__20, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__20_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__20);
v___x_400_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5));
v___x_401_ = lean_array_push(v___x_400_, v___x_399_);
return v___x_401_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__22(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_402_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__21, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__21_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__21);
v___x_403_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__9));
v___x_404_ = lean_box(2);
v___x_405_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v___x_403_);
lean_ctor_set(v___x_405_, 2, v___x_402_);
return v___x_405_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__23(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_406_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__22, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__22_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__22);
v___x_407_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5));
v___x_408_ = lean_array_push(v___x_407_, v___x_406_);
return v___x_408_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__24(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_409_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__23, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__23_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__23);
v___x_410_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__7));
v___x_411_ = lean_box(2);
v___x_412_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v___x_410_);
lean_ctor_set(v___x_412_, 2, v___x_409_);
return v___x_412_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__25(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_413_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__24, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__24_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__24);
v___x_414_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5));
v___x_415_ = lean_array_push(v___x_414_, v___x_413_);
return v___x_415_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_416_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__25, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__25_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__25);
v___x_417_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__4));
v___x_418_ = lean_box(2);
v___x_419_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
lean_ctor_set(v___x_419_, 1, v___x_417_);
lean_ctor_set(v___x_419_, 2, v___x_416_);
return v___x_419_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3(void){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___redArg(lean_object* v_data_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = lean_nat_to_int(v_data_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat(uint8_t v_leap_423_, lean_object* v_data_424_, lean_object* v_h_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = lean_nat_to_int(v_data_424_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___boxed(lean_object* v_leap_427_, lean_object* v_data_428_, lean_object* v_h_429_){
_start:
{
uint8_t v_leap_boxed_430_; lean_object* v_res_431_; 
v_leap_boxed_430_ = lean_unbox(v_leap_427_);
v_res_431_ = l_Std_Time_Day_Ordinal_OfYear_ofNat(v_leap_boxed_430_, v_data_428_, v_h_429_);
return v_res_431_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__0(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_unsigned_to_nat(365u);
v___x_433_ = lean_nat_to_int(v___x_432_);
return v___x_433_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__1(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_434_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__0, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__0_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__0);
v___x_435_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_436_ = lean_int_add(v___x_435_, v___x_434_);
return v___x_436_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__2(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_437_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_438_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__1, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__1_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__1);
v___x_439_ = lean_int_sub(v___x_438_, v___x_437_);
return v___x_439_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v_range_442_; 
v___x_440_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_441_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__2, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__2_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__2);
v_range_442_ = lean_int_add(v___x_441_, v___x_440_);
return v_range_442_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1(lean_object* v_n_443_){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v_range_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_444_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_445_ = lean_nat_to_int(v_n_443_);
v_range_446_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3);
v___x_447_ = lean_int_sub(v___x_445_, v___x_444_);
lean_dec(v___x_445_);
v___x_448_ = lean_int_emod(v___x_447_, v_range_446_);
lean_dec(v___x_447_);
v___x_449_ = lean_int_add(v___x_448_, v_range_446_);
lean_dec(v___x_448_);
v___x_450_ = lean_int_emod(v___x_449_, v_range_446_);
lean_dec(v___x_449_);
v___x_451_ = lean_int_add(v___x_450_, v___x_444_);
lean_dec(v___x_450_);
return v___x_451_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__0(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = lean_unsigned_to_nat(364u);
v___x_453_ = lean_nat_to_int(v___x_452_);
return v___x_453_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__1(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_454_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__0, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__0_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__0);
v___x_455_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_456_ = lean_int_add(v___x_455_, v___x_454_);
return v___x_456_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__2(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_457_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_458_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__1, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__1_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__1);
v___x_459_ = lean_int_sub(v___x_458_, v___x_457_);
return v___x_459_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v_range_462_; 
v___x_460_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_461_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__2, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__2_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__2);
v_range_462_ = lean_int_add(v___x_461_, v___x_460_);
return v_range_462_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3(lean_object* v_n_463_){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v_range_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_464_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_465_ = lean_nat_to_int(v_n_463_);
v_range_466_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3);
v___x_467_ = lean_int_sub(v___x_465_, v___x_464_);
lean_dec(v___x_465_);
v___x_468_ = lean_int_emod(v___x_467_, v_range_466_);
lean_dec(v___x_467_);
v___x_469_ = lean_int_add(v___x_468_, v_range_466_);
lean_dec(v___x_468_);
v___x_470_ = lean_int_emod(v___x_469_, v_range_466_);
lean_dec(v___x_469_);
v___x_471_ = lean_int_add(v___x_470_, v___x_464_);
lean_dec(v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear(uint8_t v_leap_472_, lean_object* v_n_473_){
_start:
{
if (v_leap_472_ == 0)
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v_range_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_474_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_475_ = lean_nat_to_int(v_n_473_);
v_range_476_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3);
v___x_477_ = lean_int_sub(v___x_475_, v___x_474_);
lean_dec(v___x_475_);
v___x_478_ = lean_int_emod(v___x_477_, v_range_476_);
lean_dec(v___x_477_);
v___x_479_ = lean_int_add(v___x_478_, v_range_476_);
lean_dec(v___x_478_);
v___x_480_ = lean_int_emod(v___x_479_, v_range_476_);
lean_dec(v___x_479_);
v___x_481_ = lean_int_add(v___x_480_, v___x_474_);
lean_dec(v___x_480_);
return v___x_481_;
}
else
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v_range_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_482_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_483_ = lean_nat_to_int(v_n_473_);
v_range_484_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3);
v___x_485_ = lean_int_sub(v___x_483_, v___x_482_);
lean_dec(v___x_483_);
v___x_486_ = lean_int_emod(v___x_485_, v_range_484_);
lean_dec(v___x_485_);
v___x_487_ = lean_int_add(v___x_486_, v_range_484_);
lean_dec(v___x_486_);
v___x_488_ = lean_int_emod(v___x_487_, v_range_484_);
lean_dec(v___x_487_);
v___x_489_ = lean_int_add(v___x_488_, v___x_482_);
lean_dec(v___x_488_);
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear___boxed(lean_object* v_leap_490_, lean_object* v_n_491_){
_start:
{
uint8_t v_leap_boxed_492_; lean_object* v_res_493_; 
v_leap_boxed_492_ = lean_unbox(v_leap_490_);
v_res_493_ = l_Std_Time_Day_Ordinal_instOfNatOfYear(v_leap_boxed_492_, v_n_491_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instInhabitedOfYear___redArg(){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instInhabitedOfYear___redArg___boxed(lean_object* v___dummy_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Std_Time_Day_Ordinal_instInhabitedOfYear___redArg();
return v_res_497_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instInhabitedOfYear___closed__0(void){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Std_Time_Day_Ordinal_instInhabitedOfYear___redArg();
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instInhabitedOfYear(uint8_t v_leap_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instInhabitedOfYear___closed__0, &l_Std_Time_Day_Ordinal_instInhabitedOfYear___closed__0_once, _init_l_Std_Time_Day_Ordinal_instInhabitedOfYear___closed__0);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instInhabitedOfYear___boxed(lean_object* v_leap_501_){
_start:
{
uint8_t v_leap_boxed_502_; lean_object* v_res_503_; 
v_leap_boxed_502_ = lean_unbox(v_leap_501_);
v_res_503_ = l_Std_Time_Day_Ordinal_instInhabitedOfYear(v_leap_boxed_502_);
return v_res_503_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_ofNat___auto__1(void){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofNat___redArg(lean_object* v_data_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = lean_nat_to_int(v_data_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofNat(lean_object* v_data_507_, lean_object* v_h_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = lean_nat_to_int(v_data_507_);
return v___x_509_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_ofFin___closed__0(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = lean_unsigned_to_nat(1u);
v___x_511_ = lean_nat_to_int(v___x_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofFin(lean_object* v_data_512_){
_start:
{
lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_513_ = lean_unsigned_to_nat(1u);
v___x_514_ = lean_nat_dec_le(v___x_513_, v_data_512_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; 
lean_dec(v_data_512_);
v___x_515_ = lean_obj_once(&l_Std_Time_Day_Ordinal_ofFin___closed__0, &l_Std_Time_Day_Ordinal_ofFin___closed__0_once, _init_l_Std_Time_Day_Ordinal_ofFin___closed__0);
return v___x_515_;
}
else
{
lean_object* v___x_516_; 
v___x_516_ = lean_nat_to_int(v_data_512_);
return v___x_516_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_toOffset(lean_object* v_ordinal_517_){
_start:
{
lean_inc(v_ordinal_517_);
return v_ordinal_517_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_toOffset___boxed(lean_object* v_ordinal_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Std_Time_Day_Ordinal_toOffset(v_ordinal_518_);
lean_dec(v_ordinal_518_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_toOffset___redArg(lean_object* v_ofYear_520_){
_start:
{
lean_inc(v_ofYear_520_);
return v_ofYear_520_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_toOffset___redArg___boxed(lean_object* v_ofYear_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Std_Time_Day_Ordinal_OfYear_toOffset___redArg(v_ofYear_521_);
lean_dec(v_ofYear_521_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_toOffset(uint8_t v_leap_523_, lean_object* v_ofYear_524_){
_start:
{
lean_inc(v_ofYear_524_);
return v_ofYear_524_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_toOffset___boxed(lean_object* v_leap_525_, lean_object* v_ofYear_526_){
_start:
{
uint8_t v_leap_boxed_527_; lean_object* v_res_528_; 
v_leap_boxed_527_ = lean_unbox(v_leap_525_);
v_res_528_ = l_Std_Time_Day_Ordinal_OfYear_toOffset(v_leap_boxed_527_, v_ofYear_526_);
lean_dec(v_ofYear_526_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toOrdinal___redArg(lean_object* v_off_529_){
_start:
{
lean_inc(v_off_529_);
return v_off_529_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toOrdinal___redArg___boxed(lean_object* v_off_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Std_Time_Day_Offset_toOrdinal___redArg(v_off_530_);
lean_dec(v_off_530_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toOrdinal(lean_object* v_off_532_, lean_object* v_h_533_){
_start:
{
lean_inc(v_off_532_);
return v_off_532_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toOrdinal___boxed(lean_object* v_off_534_, lean_object* v_h_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Std_Time_Day_Offset_toOrdinal(v_off_534_, v_h_535_);
lean_dec(v_off_534_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofNat(lean_object* v_data_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = lean_nat_to_int(v_data_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofInt(lean_object* v_data_539_){
_start:
{
lean_inc(v_data_539_);
return v_data_539_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofInt___boxed(lean_object* v_data_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Std_Time_Day_Offset_ofInt(v_data_540_);
lean_dec(v_data_540_);
return v_res_541_;
}
}
static lean_object* _init_l_Std_Time_Day_Offset_toNanoseconds___closed__0(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_cstr_to_nat("86400000000000");
v___x_543_ = lean_nat_to_int(v___x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toNanoseconds(lean_object* v_days_544_){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = lean_obj_once(&l_Std_Time_Day_Offset_toNanoseconds___closed__0, &l_Std_Time_Day_Offset_toNanoseconds___closed__0_once, _init_l_Std_Time_Day_Offset_toNanoseconds___closed__0);
v___x_546_ = lean_int_mul(v_days_544_, v___x_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toNanoseconds___boxed(lean_object* v_days_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Std_Time_Day_Offset_toNanoseconds(v_days_547_);
lean_dec(v_days_547_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofNanoseconds(lean_object* v_ns_549_){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = lean_obj_once(&l_Std_Time_Day_Offset_toNanoseconds___closed__0, &l_Std_Time_Day_Offset_toNanoseconds___closed__0_once, _init_l_Std_Time_Day_Offset_toNanoseconds___closed__0);
v___x_551_ = lean_int_ediv(v_ns_549_, v___x_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofNanoseconds___boxed(lean_object* v_ns_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Std_Time_Day_Offset_ofNanoseconds(v_ns_552_);
lean_dec(v_ns_552_);
return v_res_553_;
}
}
static lean_object* _init_l_Std_Time_Day_Offset_toMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = lean_unsigned_to_nat(86400000u);
v___x_555_ = lean_nat_to_int(v___x_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toMilliseconds(lean_object* v_days_556_){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_obj_once(&l_Std_Time_Day_Offset_toMilliseconds___closed__0, &l_Std_Time_Day_Offset_toMilliseconds___closed__0_once, _init_l_Std_Time_Day_Offset_toMilliseconds___closed__0);
v___x_558_ = lean_int_mul(v_days_556_, v___x_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toMilliseconds___boxed(lean_object* v_days_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Std_Time_Day_Offset_toMilliseconds(v_days_559_);
lean_dec(v_days_559_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofMilliseconds(lean_object* v_ms_561_){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_obj_once(&l_Std_Time_Day_Offset_toMilliseconds___closed__0, &l_Std_Time_Day_Offset_toMilliseconds___closed__0_once, _init_l_Std_Time_Day_Offset_toMilliseconds___closed__0);
v___x_563_ = lean_int_ediv(v_ms_561_, v___x_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofMilliseconds___boxed(lean_object* v_ms_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Std_Time_Day_Offset_ofMilliseconds(v_ms_564_);
lean_dec(v_ms_564_);
return v_res_565_;
}
}
static lean_object* _init_l_Std_Time_Day_Offset_toSeconds___closed__0(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_unsigned_to_nat(86400u);
v___x_567_ = lean_nat_to_int(v___x_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toSeconds(lean_object* v_days_568_){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = lean_obj_once(&l_Std_Time_Day_Offset_toSeconds___closed__0, &l_Std_Time_Day_Offset_toSeconds___closed__0_once, _init_l_Std_Time_Day_Offset_toSeconds___closed__0);
v___x_570_ = lean_int_mul(v_days_568_, v___x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toSeconds___boxed(lean_object* v_days_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Std_Time_Day_Offset_toSeconds(v_days_571_);
lean_dec(v_days_571_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofSeconds(lean_object* v_secs_573_){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_obj_once(&l_Std_Time_Day_Offset_toSeconds___closed__0, &l_Std_Time_Day_Offset_toSeconds___closed__0_once, _init_l_Std_Time_Day_Offset_toSeconds___closed__0);
v___x_575_ = lean_int_ediv(v_secs_573_, v___x_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofSeconds___boxed(lean_object* v_secs_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Std_Time_Day_Offset_ofSeconds(v_secs_576_);
lean_dec(v_secs_576_);
return v_res_577_;
}
}
static lean_object* _init_l_Std_Time_Day_Offset_toMinutes___closed__0(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_unsigned_to_nat(1440u);
v___x_579_ = lean_nat_to_int(v___x_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toMinutes(lean_object* v_days_580_){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = lean_obj_once(&l_Std_Time_Day_Offset_toMinutes___closed__0, &l_Std_Time_Day_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Day_Offset_toMinutes___closed__0);
v___x_582_ = lean_int_mul(v_days_580_, v___x_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toMinutes___boxed(lean_object* v_days_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Std_Time_Day_Offset_toMinutes(v_days_583_);
lean_dec(v_days_583_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofMinutes(lean_object* v_minutes_585_){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_obj_once(&l_Std_Time_Day_Offset_toMinutes___closed__0, &l_Std_Time_Day_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Day_Offset_toMinutes___closed__0);
v___x_587_ = lean_int_ediv(v_minutes_585_, v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofMinutes___boxed(lean_object* v_minutes_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Std_Time_Day_Offset_ofMinutes(v_minutes_588_);
lean_dec(v_minutes_588_);
return v_res_589_;
}
}
static lean_object* _init_l_Std_Time_Day_Offset_toHours___closed__0(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = lean_unsigned_to_nat(24u);
v___x_591_ = lean_nat_to_int(v___x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toHours(lean_object* v_days_592_){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_593_ = lean_obj_once(&l_Std_Time_Day_Offset_toHours___closed__0, &l_Std_Time_Day_Offset_toHours___closed__0_once, _init_l_Std_Time_Day_Offset_toHours___closed__0);
v___x_594_ = lean_int_mul(v_days_592_, v___x_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toHours___boxed(lean_object* v_days_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Std_Time_Day_Offset_toHours(v_days_595_);
lean_dec(v_days_595_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofHours(lean_object* v_hours_597_){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_obj_once(&l_Std_Time_Day_Offset_toHours___closed__0, &l_Std_Time_Day_Offset_toHours___closed__0_once, _init_l_Std_Time_Day_Offset_toHours___closed__0);
v___x_599_ = lean_int_ediv(v_hours_597_, v___x_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofHours___boxed(lean_object* v_hours_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Std_Time_Day_Offset_ofHours(v_hours_600_);
lean_dec(v_hours_600_);
return v_res_601_;
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
