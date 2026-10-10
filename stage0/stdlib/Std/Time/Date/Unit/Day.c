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
uint8_t l_Std_Time_Day_instDecidableEqOrdinal___aux__1(lean_object* v_a_29_, lean_object* v_b_30_){
_start:
{
uint8_t v___x_31_; 
v___x_31_ = lean_int_dec_eq(v_a_29_, v_b_30_);
return v___x_31_;
}
}
LEAN_EXPORT void l_Std_Time_Day_instDecidableEqOrdinal___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_29_ = stack[0].m_obj;
lean_object* v_b_30_ = stack[1].m_obj;
uint8_t v_res_32_;
v_res_32_ = l_Std_Time_Day_instDecidableEqOrdinal___aux__1(v_a_29_, v_b_30_);
stack->m_num = v_res_32_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableEqOrdinal___aux__1___boxed(lean_object* v_a_33_, lean_object* v_b_34_){
_start:
{
uint8_t v_res_35_; lean_object* v_r_36_; 
v_res_35_ = l_Std_Time_Day_instDecidableEqOrdinal___aux__1(v_a_33_, v_b_34_);
lean_dec(v_b_34_);
lean_dec(v_a_33_);
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
uint8_t l_Std_Time_Day_instDecidableEqOrdinal(lean_object* v_a_37_, lean_object* v_b_38_){
_start:
{
uint8_t v___x_39_; 
v___x_39_ = lean_int_dec_eq(v_a_37_, v_b_38_);
return v___x_39_;
}
}
LEAN_EXPORT void l_Std_Time_Day_instDecidableEqOrdinal_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_37_ = stack[0].m_obj;
lean_object* v_b_38_ = stack[1].m_obj;
uint8_t v_res_40_;
v_res_40_ = l_Std_Time_Day_instDecidableEqOrdinal(v_a_37_, v_b_38_);
stack->m_num = v_res_40_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableEqOrdinal___boxed(lean_object* v_a_41_, lean_object* v_b_42_){
_start:
{
uint8_t v_res_43_; lean_object* v_r_44_; 
v_res_43_ = l_Std_Time_Day_instDecidableEqOrdinal(v_a_41_, v_b_42_);
lean_dec(v_b_42_);
lean_dec(v_a_41_);
v_r_44_ = lean_box(v_res_43_);
return v_r_44_;
}
}
static lean_object* _init_l_Std_Time_Day_instLEOrdinal(void){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_box(0);
return v___x_45_;
}
}
static lean_object* _init_l_Std_Time_Day_instLTOrdinal(void){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_box(0);
return v___x_46_;
}
}
static lean_object* _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_unsigned_to_nat(1u);
v___x_48_ = lean_nat_to_int(v___x_47_);
return v___x_48_;
}
}
static lean_object* _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__1(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_unsigned_to_nat(30u);
v___x_50_ = lean_nat_to_int(v___x_49_);
return v___x_50_;
}
}
static lean_object* _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__2(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__1, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__1_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__1);
v___x_52_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_53_ = lean_int_add(v___x_52_, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__3(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_55_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__2, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__2_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__2);
v___x_56_ = lean_int_sub(v___x_55_, v___x_54_);
return v___x_56_;
}
}
static lean_object* _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v_range_59_; 
v___x_57_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_58_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__3);
v_range_59_ = lean_int_add(v___x_58_, v___x_57_);
return v_range_59_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instOfNatOrdinal___aux__1(lean_object* v_n_60_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v_range_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_61_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_62_ = lean_nat_to_int(v_n_60_);
v_range_63_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4);
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
LEAN_EXPORT lean_object* l_Std_Time_Day_instOfNatOrdinal(lean_object* v_n_69_){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v_range_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_70_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_71_ = lean_nat_to_int(v_n_69_);
v_range_72_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4);
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
uint8_t l_Std_Time_Day_instDecidableLeOrdinal___aux__1(lean_object* v_x_78_, lean_object* v_y_79_){
_start:
{
uint8_t v___x_80_; 
v___x_80_ = lean_int_dec_le(v_x_78_, v_y_79_);
return v___x_80_;
}
}
LEAN_EXPORT void l_Std_Time_Day_instDecidableLeOrdinal___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_78_ = stack[0].m_obj;
lean_object* v_y_79_ = stack[1].m_obj;
uint8_t v_res_81_;
v_res_81_ = l_Std_Time_Day_instDecidableLeOrdinal___aux__1(v_x_78_, v_y_79_);
stack->m_num = v_res_81_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLeOrdinal___aux__1___boxed(lean_object* v_x_82_, lean_object* v_y_83_){
_start:
{
uint8_t v_res_84_; lean_object* v_r_85_; 
v_res_84_ = l_Std_Time_Day_instDecidableLeOrdinal___aux__1(v_x_82_, v_y_83_);
lean_dec(v_y_83_);
lean_dec(v_x_82_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
uint8_t l_Std_Time_Day_instDecidableLeOrdinal(lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
uint8_t v___x_88_; 
v___x_88_ = lean_int_dec_le(v___y_86_, v___y_87_);
return v___x_88_;
}
}
LEAN_EXPORT void l_Std_Time_Day_instDecidableLeOrdinal_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_86_ = stack[0].m_obj;
lean_object* v___y_87_ = stack[1].m_obj;
uint8_t v_res_89_;
v_res_89_ = l_Std_Time_Day_instDecidableLeOrdinal(v___y_86_, v___y_87_);
stack->m_num = v_res_89_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLeOrdinal___boxed(lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
uint8_t v_res_92_; lean_object* v_r_93_; 
v_res_92_ = l_Std_Time_Day_instDecidableLeOrdinal(v___y_90_, v___y_91_);
lean_dec(v___y_91_);
lean_dec(v___y_90_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
uint8_t l_Std_Time_Day_instDecidableLtOrdinal___aux__1(lean_object* v_x_94_, lean_object* v_y_95_){
_start:
{
uint8_t v___x_96_; 
v___x_96_ = lean_int_dec_lt(v_x_94_, v_y_95_);
return v___x_96_;
}
}
LEAN_EXPORT void l_Std_Time_Day_instDecidableLtOrdinal___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_94_ = stack[0].m_obj;
lean_object* v_y_95_ = stack[1].m_obj;
uint8_t v_res_97_;
v_res_97_ = l_Std_Time_Day_instDecidableLtOrdinal___aux__1(v_x_94_, v_y_95_);
stack->m_num = v_res_97_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLtOrdinal___aux__1___boxed(lean_object* v_x_98_, lean_object* v_y_99_){
_start:
{
uint8_t v_res_100_; lean_object* v_r_101_; 
v_res_100_ = l_Std_Time_Day_instDecidableLtOrdinal___aux__1(v_x_98_, v_y_99_);
lean_dec(v_y_99_);
lean_dec(v_x_98_);
v_r_101_ = lean_box(v_res_100_);
return v_r_101_;
}
}
uint8_t l_Std_Time_Day_instDecidableLtOrdinal(lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
uint8_t v___x_104_; 
v___x_104_ = lean_int_dec_lt(v___y_102_, v___y_103_);
return v___x_104_;
}
}
LEAN_EXPORT void l_Std_Time_Day_instDecidableLtOrdinal_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_102_ = stack[0].m_obj;
lean_object* v___y_103_ = stack[1].m_obj;
uint8_t v_res_105_;
v_res_105_ = l_Std_Time_Day_instDecidableLtOrdinal(v___y_102_, v___y_103_);
stack->m_num = v_res_105_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLtOrdinal___boxed(lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
uint8_t v_res_108_; lean_object* v_r_109_; 
v_res_108_ = l_Std_Time_Day_instDecidableLtOrdinal(v___y_106_, v___y_107_);
lean_dec(v___y_107_);
lean_dec(v___y_106_);
v_r_109_ = lean_box(v_res_108_);
return v_r_109_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOrdinal___closed__0(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_111_ = lean_int_sub(v___x_110_, v___x_110_);
return v___x_111_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOrdinal___closed__1(void){
_start:
{
lean_object* v_range_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v_range_112_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4);
v___x_113_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOrdinal___closed__0, &l_Std_Time_Day_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Day_instInhabitedOrdinal___closed__0);
v___x_114_ = lean_int_emod(v___x_113_, v_range_112_);
return v___x_114_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOrdinal___closed__2(void){
_start:
{
lean_object* v_range_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v_range_115_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4);
v___x_116_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOrdinal___closed__1, &l_Std_Time_Day_instInhabitedOrdinal___closed__1_once, _init_l_Std_Time_Day_instInhabitedOrdinal___closed__1);
v___x_117_ = lean_int_add(v___x_116_, v_range_115_);
return v___x_117_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOrdinal___closed__3(void){
_start:
{
lean_object* v_range_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v_range_118_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4);
v___x_119_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOrdinal___closed__2, &l_Std_Time_Day_instInhabitedOrdinal___closed__2_once, _init_l_Std_Time_Day_instInhabitedOrdinal___closed__2);
v___x_120_ = lean_int_emod(v___x_119_, v_range_118_);
return v___x_120_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOrdinal___closed__4(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_121_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_122_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOrdinal___closed__3, &l_Std_Time_Day_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Day_instInhabitedOrdinal___closed__3);
v___x_123_ = lean_int_add(v___x_122_, v___x_121_);
return v___x_123_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOrdinal(void){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOrdinal___closed__4, &l_Std_Time_Day_instInhabitedOrdinal___closed__4_once, _init_l_Std_Time_Day_instInhabitedOrdinal___closed__4);
return v___x_124_;
}
}
uint8_t l_Std_Time_Day_instOrdOrdinal___aux__1(lean_object* v_x_125_, lean_object* v_y_126_){
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
LEAN_EXPORT void l_Std_Time_Day_instOrdOrdinal___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_125_ = stack[0].m_obj;
lean_object* v_y_126_ = stack[1].m_obj;
uint8_t v_res_132_;
v_res_132_ = l_Std_Time_Day_instOrdOrdinal___aux__1(v_x_125_, v_y_126_);
stack->m_num = v_res_132_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instOrdOrdinal___aux__1___boxed(lean_object* v_x_133_, lean_object* v_y_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = l_Std_Time_Day_instOrdOrdinal___aux__1(v_x_133_, v_y_134_);
lean_dec(v_y_134_);
lean_dec(v_x_133_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instReprOffset___aux__1(lean_object* v_x_139_, lean_object* v_p_140_){
_start:
{
lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_141_ = lean_obj_once(&l_Std_Time_Day_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Day_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instReprOrdinal___aux__1___closed__0);
v___x_142_ = lean_int_dec_lt(v_x_139_, v___x_141_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = l_Int_repr(v_x_139_);
v___x_144_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
return v___x_144_;
}
else
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_145_ = l_Int_repr(v_x_139_);
v___x_146_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
v___x_147_ = l_Repr_addAppParen(v___x_146_, v_p_140_);
return v___x_147_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instReprOffset___aux__1___boxed(lean_object* v_x_148_, lean_object* v_p_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Std_Time_Day_instReprOffset___aux__1(v_x_148_, v_p_149_);
lean_dec(v_p_149_);
lean_dec(v_x_148_);
return v_res_150_;
}
}
uint8_t l_Std_Time_Day_instDecidableEqOffset___aux__1(lean_object* v_a_152_, lean_object* v_b_153_){
_start:
{
uint8_t v___x_154_; 
v___x_154_ = lean_int_dec_eq(v_a_152_, v_b_153_);
return v___x_154_;
}
}
LEAN_EXPORT void l_Std_Time_Day_instDecidableEqOffset___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_152_ = stack[0].m_obj;
lean_object* v_b_153_ = stack[1].m_obj;
uint8_t v_res_155_;
v_res_155_ = l_Std_Time_Day_instDecidableEqOffset___aux__1(v_a_152_, v_b_153_);
stack->m_num = v_res_155_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableEqOffset___aux__1___boxed(lean_object* v_a_156_, lean_object* v_b_157_){
_start:
{
uint8_t v_res_158_; lean_object* v_r_159_; 
v_res_158_ = l_Std_Time_Day_instDecidableEqOffset___aux__1(v_a_156_, v_b_157_);
lean_dec(v_b_157_);
lean_dec(v_a_156_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Day_instDecidableEqOffset___aux__1_spec__0_spec__0(lean_object* v_a_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = lean_nat_to_int(v_a_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Day_instDecidableEqOffset___aux__1_spec__0(lean_object* v_a_162_){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_nat_to_int(v_a_162_);
v___x_164_ = l_Rat_ofInt(v___x_163_);
return v___x_164_;
}
}
uint8_t l_Std_Time_Day_instDecidableEqOffset(lean_object* v_a_165_, lean_object* v_b_166_){
_start:
{
uint8_t v___x_167_; 
v___x_167_ = lean_int_dec_eq(v_a_165_, v_b_166_);
return v___x_167_;
}
}
LEAN_EXPORT void l_Std_Time_Day_instDecidableEqOffset_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_165_ = stack[0].m_obj;
lean_object* v_b_166_ = stack[1].m_obj;
uint8_t v_res_168_;
v_res_168_ = l_Std_Time_Day_instDecidableEqOffset(v_a_165_, v_b_166_);
stack->m_num = v_res_168_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableEqOffset___boxed(lean_object* v_a_169_, lean_object* v_b_170_){
_start:
{
uint8_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l_Std_Time_Day_instDecidableEqOffset(v_a_169_, v_b_170_);
lean_dec(v_b_170_);
lean_dec(v_a_169_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOffset___aux__1___closed__0(void){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Std_Time_Internal_instInhabitedUnitVal_default___redArg();
return v___x_173_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOffset___aux__1(void){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOffset___aux__1___closed__0, &l_Std_Time_Day_instInhabitedOffset___aux__1___closed__0_once, _init_l_Std_Time_Day_instInhabitedOffset___aux__1___closed__0);
return v___x_174_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOffset(void){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOffset___aux__1___closed__0, &l_Std_Time_Day_instInhabitedOffset___aux__1___closed__0_once, _init_l_Std_Time_Day_instInhabitedOffset___aux__1___closed__0);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instAddOffset___aux__1(lean_object* v_u1_176_, lean_object* v_u2_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = lean_int_add(v_u1_176_, v_u2_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instAddOffset___aux__1___boxed(lean_object* v_u1_179_, lean_object* v_u2_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Std_Time_Day_instAddOffset___aux__1(v_u1_179_, v_u2_180_);
lean_dec(v_u2_180_);
lean_dec(v_u1_179_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instSubOffset___aux__1(lean_object* v_u1_184_, lean_object* v_u2_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = lean_int_sub(v_u1_184_, v_u2_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instSubOffset___aux__1___boxed(lean_object* v_u1_187_, lean_object* v_u2_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Std_Time_Day_instSubOffset___aux__1(v_u1_187_, v_u2_188_);
lean_dec(v_u2_188_);
lean_dec(v_u1_187_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instNegOffset___aux__1(lean_object* v_x_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = lean_int_neg(v_x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instNegOffset___aux__1___boxed(lean_object* v_x_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Std_Time_Day_instNegOffset___aux__1(v_x_194_);
lean_dec(v_x_194_);
return v_res_195_;
}
}
static lean_object* _init_l_Std_Time_Day_instLEOffset(void){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = lean_box(0);
return v___x_198_;
}
}
static lean_object* _init_l_Std_Time_Day_instLTOffset(void){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = lean_box(0);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instToStringOffset___aux__1(lean_object* v_n_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Int_repr(v_n_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instToStringOffset___aux__1___boxed(lean_object* v_n_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Std_Time_Day_instToStringOffset___aux__1(v_n_202_);
lean_dec(v_n_202_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instOfNatOffset(lean_object* v_n_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = lean_nat_to_int(v_n_206_);
return v___x_207_;
}
}
uint8_t l_Std_Time_Day_instDecidableLeOffset___aux__1(lean_object* v_x_208_, lean_object* v_y_209_){
_start:
{
uint8_t v___x_210_; 
v___x_210_ = lean_int_dec_le(v_x_208_, v_y_209_);
return v___x_210_;
}
}
LEAN_EXPORT void l_Std_Time_Day_instDecidableLeOffset___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_208_ = stack[0].m_obj;
lean_object* v_y_209_ = stack[1].m_obj;
uint8_t v_res_211_;
v_res_211_ = l_Std_Time_Day_instDecidableLeOffset___aux__1(v_x_208_, v_y_209_);
stack->m_num = v_res_211_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLeOffset___aux__1___boxed(lean_object* v_x_212_, lean_object* v_y_213_){
_start:
{
uint8_t v_res_214_; lean_object* v_r_215_; 
v_res_214_ = l_Std_Time_Day_instDecidableLeOffset___aux__1(v_x_212_, v_y_213_);
lean_dec(v_y_213_);
lean_dec(v_x_212_);
v_r_215_ = lean_box(v_res_214_);
return v_r_215_;
}
}
uint8_t l_Std_Time_Day_instDecidableLeOffset(lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
uint8_t v___x_218_; 
v___x_218_ = lean_int_dec_le(v___y_216_, v___y_217_);
return v___x_218_;
}
}
LEAN_EXPORT void l_Std_Time_Day_instDecidableLeOffset_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_216_ = stack[0].m_obj;
lean_object* v___y_217_ = stack[1].m_obj;
uint8_t v_res_219_;
v_res_219_ = l_Std_Time_Day_instDecidableLeOffset(v___y_216_, v___y_217_);
stack->m_num = v_res_219_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLeOffset___boxed(lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
uint8_t v_res_222_; lean_object* v_r_223_; 
v_res_222_ = l_Std_Time_Day_instDecidableLeOffset(v___y_220_, v___y_221_);
lean_dec(v___y_221_);
lean_dec(v___y_220_);
v_r_223_ = lean_box(v_res_222_);
return v_r_223_;
}
}
uint8_t l_Std_Time_Day_instDecidableLtOffset___aux__1(lean_object* v_x_224_, lean_object* v_y_225_){
_start:
{
uint8_t v___x_226_; 
v___x_226_ = lean_int_dec_lt(v_x_224_, v_y_225_);
return v___x_226_;
}
}
LEAN_EXPORT void l_Std_Time_Day_instDecidableLtOffset___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_224_ = stack[0].m_obj;
lean_object* v_y_225_ = stack[1].m_obj;
uint8_t v_res_227_;
v_res_227_ = l_Std_Time_Day_instDecidableLtOffset___aux__1(v_x_224_, v_y_225_);
stack->m_num = v_res_227_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLtOffset___aux__1___boxed(lean_object* v_x_228_, lean_object* v_y_229_){
_start:
{
uint8_t v_res_230_; lean_object* v_r_231_; 
v_res_230_ = l_Std_Time_Day_instDecidableLtOffset___aux__1(v_x_228_, v_y_229_);
lean_dec(v_y_229_);
lean_dec(v_x_228_);
v_r_231_ = lean_box(v_res_230_);
return v_r_231_;
}
}
uint8_t l_Std_Time_Day_instDecidableLtOffset(lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
uint8_t v___x_234_; 
v___x_234_ = lean_int_dec_lt(v___y_232_, v___y_233_);
return v___x_234_;
}
}
LEAN_EXPORT void l_Std_Time_Day_instDecidableLtOffset_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_232_ = stack[0].m_obj;
lean_object* v___y_233_ = stack[1].m_obj;
uint8_t v_res_235_;
v_res_235_ = l_Std_Time_Day_instDecidableLtOffset(v___y_232_, v___y_233_);
stack->m_num = v_res_235_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLtOffset___boxed(lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
uint8_t v_res_238_; lean_object* v_r_239_; 
v_res_238_ = l_Std_Time_Day_instDecidableLtOffset(v___y_236_, v___y_237_);
lean_dec(v___y_237_);
lean_dec(v___y_236_);
v_r_239_ = lean_box(v_res_238_);
return v_r_239_;
}
}
uint8_t l_Std_Time_Day_instOrdOffset___aux__1(lean_object* v_x_240_, lean_object* v_y_241_){
_start:
{
uint8_t v___x_242_; 
v___x_242_ = lean_int_dec_lt(v_x_240_, v_y_241_);
if (v___x_242_ == 0)
{
uint8_t v___x_243_; 
v___x_243_ = lean_int_dec_eq(v_x_240_, v_y_241_);
if (v___x_243_ == 0)
{
uint8_t v___x_244_; 
v___x_244_ = 2;
return v___x_244_;
}
else
{
uint8_t v___x_245_; 
v___x_245_ = 1;
return v___x_245_;
}
}
else
{
uint8_t v___x_246_; 
v___x_246_ = 0;
return v___x_246_;
}
}
}
LEAN_EXPORT void l_Std_Time_Day_instOrdOffset___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_240_ = stack[0].m_obj;
lean_object* v_y_241_ = stack[1].m_obj;
uint8_t v_res_247_;
v_res_247_ = l_Std_Time_Day_instOrdOffset___aux__1(v_x_240_, v_y_241_);
stack->m_num = v_res_247_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instOrdOffset___aux__1___boxed(lean_object* v_x_248_, lean_object* v_y_249_){
_start:
{
uint8_t v_res_250_; lean_object* v_r_251_; 
v_res_250_ = l_Std_Time_Day_instOrdOffset___aux__1(v_x_248_, v_y_249_);
lean_dec(v_y_249_);
lean_dec(v_x_248_);
v_r_251_ = lean_box(v_res_250_);
return v_r_251_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt___redArg(lean_object* v_data_254_){
_start:
{
lean_inc(v_data_254_);
return v_data_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt___redArg___boxed(lean_object* v_data_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Std_Time_Day_Ordinal_ofInt___redArg(v_data_255_);
lean_dec(v_data_255_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt(lean_object* v_data_257_, lean_object* v_h_258_){
_start:
{
lean_inc(v_data_257_);
return v_data_257_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt___boxed(lean_object* v_data_259_, lean_object* v_h_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Std_Time_Day_Ordinal_ofInt(v_data_259_, v_h_260_);
lean_dec(v_data_259_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___redArg___lam__0(lean_object* v_r_262_, lean_object* v_p_263_){
_start:
{
lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_264_ = lean_obj_once(&l_Std_Time_Day_instReprOrdinal___aux__1___closed__0, &l_Std_Time_Day_instReprOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instReprOrdinal___aux__1___closed__0);
v___x_265_ = lean_int_dec_lt(v_r_262_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = l_Int_repr(v_r_262_);
v___x_267_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
return v___x_267_;
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = l_Int_repr(v_r_262_);
v___x_269_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
v___x_270_ = l_Repr_addAppParen(v___x_269_, v_p_263_);
return v___x_270_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___redArg___lam__0___boxed(lean_object* v_r_271_, lean_object* v_p_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Std_Time_Day_Ordinal_instReprOfYear___redArg___lam__0(v_r_271_, v_p_272_);
lean_dec(v_p_272_);
lean_dec(v_r_271_);
return v_res_273_;
}
}
lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___redArg(){
_start:
{
lean_object* v___f_276_; 
v___f_276_ = ((lean_object*)(l_Std_Time_Day_Ordinal_instReprOfYear___redArg___closed__0));
return v___f_276_;
}
}
LEAN_EXPORT void l_Std_Time_Day_Ordinal_instReprOfYear___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_277_;
v_res_277_ = l_Std_Time_Day_Ordinal_instReprOfYear___redArg();
stack->m_obj
 = v_res_277_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___redArg___boxed(lean_object* v___dummy_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Std_Time_Day_Ordinal_instReprOfYear___redArg();
return v_res_279_;
}
}
lean_object* l_Std_Time_Day_Ordinal_instReprOfYear(uint8_t v_leap_280_){
_start:
{
lean_object* v___f_281_; 
v___f_281_ = ((lean_object*)(l_Std_Time_Day_Ordinal_instReprOfYear___redArg___closed__0));
return v___f_281_;
}
}
LEAN_EXPORT void l_Std_Time_Day_Ordinal_instReprOfYear_0interp(lean_interpreter_value* stack)
{
uint8_t v_leap_280_ = stack[0].m_num;
lean_object* v_res_282_;
v_res_282_ = l_Std_Time_Day_Ordinal_instReprOfYear(v_leap_280_);
stack->m_obj
 = v_res_282_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___boxed(lean_object* v_leap_283_){
_start:
{
uint8_t v_leap_boxed_284_; lean_object* v_res_285_; 
v_leap_boxed_284_ = lean_unbox(v_leap_283_);
v_res_285_ = l_Std_Time_Day_Ordinal_instReprOfYear(v_leap_boxed_284_);
return v_res_285_;
}
}
lean_object* l_Std_Time_Day_Ordinal_instToStringOfYear___redArg(){
_start:
{
lean_object* v___f_287_; 
v___f_287_ = ((lean_object*)(l_Std_Time_Day_instToStringOffset___closed__0));
return v___f_287_;
}
}
LEAN_EXPORT void l_Std_Time_Day_Ordinal_instToStringOfYear___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_288_;
v_res_288_ = l_Std_Time_Day_Ordinal_instToStringOfYear___redArg();
stack->m_obj
 = v_res_288_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instToStringOfYear___redArg___boxed(lean_object* v___dummy_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Std_Time_Day_Ordinal_instToStringOfYear___redArg();
return v_res_290_;
}
}
lean_object* l_Std_Time_Day_Ordinal_instToStringOfYear(uint8_t v_leap_291_){
_start:
{
lean_object* v___f_292_; 
v___f_292_ = ((lean_object*)(l_Std_Time_Day_instToStringOffset___closed__0));
return v___f_292_;
}
}
LEAN_EXPORT void l_Std_Time_Day_Ordinal_instToStringOfYear_0interp(lean_interpreter_value* stack)
{
uint8_t v_leap_291_ = stack[0].m_num;
lean_object* v_res_293_;
v_res_293_ = l_Std_Time_Day_Ordinal_instToStringOfYear(v_leap_291_);
stack->m_obj
 = v_res_293_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instToStringOfYear___boxed(lean_object* v_leap_294_){
_start:
{
uint8_t v_leap_boxed_295_; lean_object* v_res_296_; 
v_leap_boxed_295_ = lean_unbox(v_leap_294_);
v_res_296_ = l_Std_Time_Day_Ordinal_instToStringOfYear(v_leap_boxed_295_);
return v_res_296_;
}
}
uint8_t l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1___redArg(lean_object* v_a_297_, lean_object* v_b_298_){
_start:
{
uint8_t v___x_299_; 
v___x_299_ = lean_int_dec_eq(v_a_297_, v_b_298_);
return v___x_299_;
}
}
LEAN_EXPORT void l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_297_ = stack[0].m_obj;
lean_object* v_b_298_ = stack[1].m_obj;
uint8_t v_res_300_;
v_res_300_ = l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1___redArg(v_a_297_, v_b_298_);
stack->m_num = v_res_300_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1___redArg___boxed(lean_object* v_a_301_, lean_object* v_b_302_){
_start:
{
uint8_t v_res_303_; lean_object* v_r_304_; 
v_res_303_ = l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1___redArg(v_a_301_, v_b_302_);
lean_dec(v_b_302_);
lean_dec(v_a_301_);
v_r_304_ = lean_box(v_res_303_);
return v_r_304_;
}
}
uint8_t l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1(uint8_t v_leap_305_, lean_object* v_a_306_, lean_object* v_b_307_){
_start:
{
uint8_t v___x_308_; 
v___x_308_ = lean_int_dec_eq(v_a_306_, v_b_307_);
return v___x_308_;
}
}
LEAN_EXPORT void l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_leap_305_ = stack[0].m_num;
lean_object* v_a_306_ = stack[1].m_obj;
lean_object* v_b_307_ = stack[2].m_obj;
uint8_t v_res_309_;
v_res_309_ = l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1(v_leap_305_, v_a_306_, v_b_307_);
stack->m_num = v_res_309_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1___boxed(lean_object* v_leap_310_, lean_object* v_a_311_, lean_object* v_b_312_){
_start:
{
uint8_t v_leap_boxed_313_; uint8_t v_res_314_; lean_object* v_r_315_; 
v_leap_boxed_313_ = lean_unbox(v_leap_310_);
v_res_314_ = l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1(v_leap_boxed_313_, v_a_311_, v_b_312_);
lean_dec(v_b_312_);
lean_dec(v_a_311_);
v_r_315_ = lean_box(v_res_314_);
return v_r_315_;
}
}
uint8_t l_Std_Time_Day_Ordinal_instDecidableEqOfYear___redArg(lean_object* v_a_316_, lean_object* v_b_317_){
_start:
{
uint8_t v___x_318_; 
v___x_318_ = lean_int_dec_eq(v_a_316_, v_b_317_);
return v___x_318_;
}
}
LEAN_EXPORT void l_Std_Time_Day_Ordinal_instDecidableEqOfYear___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_316_ = stack[0].m_obj;
lean_object* v_b_317_ = stack[1].m_obj;
uint8_t v_res_319_;
v_res_319_ = l_Std_Time_Day_Ordinal_instDecidableEqOfYear___redArg(v_a_316_, v_b_317_);
stack->m_num = v_res_319_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instDecidableEqOfYear___redArg___boxed(lean_object* v_a_320_, lean_object* v_b_321_){
_start:
{
uint8_t v_res_322_; lean_object* v_r_323_; 
v_res_322_ = l_Std_Time_Day_Ordinal_instDecidableEqOfYear___redArg(v_a_320_, v_b_321_);
lean_dec(v_b_321_);
lean_dec(v_a_320_);
v_r_323_ = lean_box(v_res_322_);
return v_r_323_;
}
}
uint8_t l_Std_Time_Day_Ordinal_instDecidableEqOfYear(uint8_t v_leap_324_, lean_object* v_a_325_, lean_object* v_b_326_){
_start:
{
uint8_t v___x_327_; 
v___x_327_ = lean_int_dec_eq(v_a_325_, v_b_326_);
return v___x_327_;
}
}
LEAN_EXPORT void l_Std_Time_Day_Ordinal_instDecidableEqOfYear_0interp(lean_interpreter_value* stack)
{
uint8_t v_leap_324_ = stack[0].m_num;
lean_object* v_a_325_ = stack[1].m_obj;
lean_object* v_b_326_ = stack[2].m_obj;
uint8_t v_res_328_;
v_res_328_ = l_Std_Time_Day_Ordinal_instDecidableEqOfYear(v_leap_324_, v_a_325_, v_b_326_);
stack->m_num = v_res_328_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instDecidableEqOfYear___boxed(lean_object* v_leap_329_, lean_object* v_a_330_, lean_object* v_b_331_){
_start:
{
uint8_t v_leap_boxed_332_; uint8_t v_res_333_; lean_object* v_r_334_; 
v_leap_boxed_332_ = lean_unbox(v_leap_329_);
v_res_333_ = l_Std_Time_Day_Ordinal_instDecidableEqOfYear(v_leap_boxed_332_, v_a_330_, v_b_331_);
lean_dec(v_b_331_);
lean_dec(v_a_330_);
v_r_334_ = lean_box(v_res_333_);
return v_r_334_;
}
}
uint8_t l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___redArg(lean_object* v_x_335_, lean_object* v_y_336_){
_start:
{
uint8_t v___x_337_; 
v___x_337_ = lean_int_dec_lt(v_x_335_, v_y_336_);
if (v___x_337_ == 0)
{
uint8_t v___x_338_; 
v___x_338_ = lean_int_dec_eq(v_x_335_, v_y_336_);
if (v___x_338_ == 0)
{
uint8_t v___x_339_; 
v___x_339_ = 2;
return v___x_339_;
}
else
{
uint8_t v___x_340_; 
v___x_340_ = 1;
return v___x_340_;
}
}
else
{
uint8_t v___x_341_; 
v___x_341_ = 0;
return v___x_341_;
}
}
}
LEAN_EXPORT void l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_335_ = stack[0].m_obj;
lean_object* v_y_336_ = stack[1].m_obj;
uint8_t v_res_342_;
v_res_342_ = l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___redArg(v_x_335_, v_y_336_);
stack->m_num = v_res_342_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___redArg___boxed(lean_object* v_x_343_, lean_object* v_y_344_){
_start:
{
uint8_t v_res_345_; lean_object* v_r_346_; 
v_res_345_ = l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___redArg(v_x_343_, v_y_344_);
lean_dec(v_y_344_);
lean_dec(v_x_343_);
v_r_346_ = lean_box(v_res_345_);
return v_r_346_;
}
}
uint8_t l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1(uint8_t v_leap_347_, lean_object* v_x_348_, lean_object* v_y_349_){
_start:
{
uint8_t v___x_350_; 
v___x_350_ = lean_int_dec_lt(v_x_348_, v_y_349_);
if (v___x_350_ == 0)
{
uint8_t v___x_351_; 
v___x_351_ = lean_int_dec_eq(v_x_348_, v_y_349_);
if (v___x_351_ == 0)
{
uint8_t v___x_352_; 
v___x_352_ = 2;
return v___x_352_;
}
else
{
uint8_t v___x_353_; 
v___x_353_ = 1;
return v___x_353_;
}
}
else
{
uint8_t v___x_354_; 
v___x_354_ = 0;
return v___x_354_;
}
}
}
LEAN_EXPORT void l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_leap_347_ = stack[0].m_num;
lean_object* v_x_348_ = stack[1].m_obj;
lean_object* v_y_349_ = stack[2].m_obj;
uint8_t v_res_355_;
v_res_355_ = l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1(v_leap_347_, v_x_348_, v_y_349_);
stack->m_num = v_res_355_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___boxed(lean_object* v_leap_356_, lean_object* v_x_357_, lean_object* v_y_358_){
_start:
{
uint8_t v_leap_boxed_359_; uint8_t v_res_360_; lean_object* v_r_361_; 
v_leap_boxed_359_ = lean_unbox(v_leap_356_);
v_res_360_ = l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1(v_leap_boxed_359_, v_x_357_, v_y_358_);
lean_dec(v_y_358_);
lean_dec(v_x_357_);
v_r_361_ = lean_box(v_res_360_);
return v_r_361_;
}
}
lean_object* l_Std_Time_Day_Ordinal_instOrdOfYear(uint8_t v_leap_362_){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = lean_box(v_leap_362_);
v___x_364_ = lean_alloc_closure((void*)(l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___boxed), 3, 1);
lean_closure_set(v___x_364_, 0, v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT void l_Std_Time_Day_Ordinal_instOrdOfYear_0interp(lean_interpreter_value* stack)
{
uint8_t v_leap_362_ = stack[0].m_num;
lean_object* v_res_365_;
v_res_365_ = l_Std_Time_Day_Ordinal_instOrdOfYear(v_leap_362_);
stack->m_obj
 = v_res_365_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOrdOfYear___boxed(lean_object* v_leap_366_){
_start:
{
uint8_t v_leap_boxed_367_; lean_object* v_res_368_; 
v_leap_boxed_367_ = lean_unbox(v_leap_366_);
v_res_368_ = l_Std_Time_Day_Ordinal_instOrdOfYear(v_leap_boxed_367_);
return v_res_368_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__12(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__10));
v___x_396_ = l_Lean_mkAtom(v___x_395_);
return v___x_396_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__13(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_397_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__12, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__12_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__12);
v___x_398_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5));
v___x_399_ = lean_array_push(v___x_398_, v___x_397_);
return v___x_399_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__17(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_410_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__16));
v___x_411_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5));
v___x_412_ = lean_array_push(v___x_411_, v___x_410_);
return v___x_412_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__18(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_413_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__17, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__17_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__17);
v___x_414_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__15));
v___x_415_ = lean_box(2);
v___x_416_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
lean_ctor_set(v___x_416_, 1, v___x_414_);
lean_ctor_set(v___x_416_, 2, v___x_413_);
return v___x_416_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__19(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_417_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__18, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__18_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__18);
v___x_418_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__13, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__13_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__13);
v___x_419_ = lean_array_push(v___x_418_, v___x_417_);
return v___x_419_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__20(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_420_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__19, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__19_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__19);
v___x_421_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__11));
v___x_422_ = lean_box(2);
v___x_423_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v___x_421_);
lean_ctor_set(v___x_423_, 2, v___x_420_);
return v___x_423_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__21(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_424_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__20, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__20_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__20);
v___x_425_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5));
v___x_426_ = lean_array_push(v___x_425_, v___x_424_);
return v___x_426_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__22(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_427_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__21, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__21_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__21);
v___x_428_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__9));
v___x_429_ = lean_box(2);
v___x_430_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v___x_428_);
lean_ctor_set(v___x_430_, 2, v___x_427_);
return v___x_430_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__23(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_431_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__22, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__22_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__22);
v___x_432_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5));
v___x_433_ = lean_array_push(v___x_432_, v___x_431_);
return v___x_433_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__24(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_434_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__23, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__23_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__23);
v___x_435_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__7));
v___x_436_ = lean_box(2);
v___x_437_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
lean_ctor_set(v___x_437_, 1, v___x_435_);
lean_ctor_set(v___x_437_, 2, v___x_434_);
return v___x_437_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__25(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_438_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__24, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__24_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__24);
v___x_439_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5));
v___x_440_ = lean_array_push(v___x_439_, v___x_438_);
return v___x_440_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_441_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__25, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__25_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__25);
v___x_442_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__4));
v___x_443_ = lean_box(2);
v___x_444_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v___x_442_);
lean_ctor_set(v___x_444_, 2, v___x_441_);
return v___x_444_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3(void){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___redArg(lean_object* v_data_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = lean_nat_to_int(v_data_446_);
return v___x_447_;
}
}
lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat(uint8_t v_leap_448_, lean_object* v_data_449_, lean_object* v_h_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = lean_nat_to_int(v_data_449_);
return v___x_451_;
}
}
LEAN_EXPORT void l_Std_Time_Day_Ordinal_OfYear_ofNat_0interp(lean_interpreter_value* stack)
{
uint8_t v_leap_448_ = stack[0].m_num;
lean_object* v_data_449_ = stack[1].m_obj;
lean_object* v_res_452_;
v_res_452_ = l_Std_Time_Day_Ordinal_OfYear_ofNat(v_leap_448_, v_data_449_, lean_box(0));
stack->m_obj
 = v_res_452_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___boxed(lean_object* v_leap_453_, lean_object* v_data_454_, lean_object* v_h_455_){
_start:
{
uint8_t v_leap_boxed_456_; lean_object* v_res_457_; 
v_leap_boxed_456_ = lean_unbox(v_leap_453_);
v_res_457_ = l_Std_Time_Day_Ordinal_OfYear_ofNat(v_leap_boxed_456_, v_data_454_, v_h_455_);
return v_res_457_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__0(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = lean_unsigned_to_nat(365u);
v___x_459_ = lean_nat_to_int(v___x_458_);
return v___x_459_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__1(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_460_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__0, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__0_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__0);
v___x_461_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_462_ = lean_int_add(v___x_461_, v___x_460_);
return v___x_462_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__2(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_463_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_464_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__1, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__1_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__1);
v___x_465_ = lean_int_sub(v___x_464_, v___x_463_);
return v___x_465_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v_range_468_; 
v___x_466_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_467_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__2, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__2_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__2);
v_range_468_ = lean_int_add(v___x_467_, v___x_466_);
return v_range_468_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1(lean_object* v_n_469_){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v_range_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_470_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_471_ = lean_nat_to_int(v_n_469_);
v_range_472_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3);
v___x_473_ = lean_int_sub(v___x_471_, v___x_470_);
lean_dec(v___x_471_);
v___x_474_ = lean_int_emod(v___x_473_, v_range_472_);
lean_dec(v___x_473_);
v___x_475_ = lean_int_add(v___x_474_, v_range_472_);
lean_dec(v___x_474_);
v___x_476_ = lean_int_emod(v___x_475_, v_range_472_);
lean_dec(v___x_475_);
v___x_477_ = lean_int_add(v___x_476_, v___x_470_);
lean_dec(v___x_476_);
return v___x_477_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__0(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = lean_unsigned_to_nat(364u);
v___x_479_ = lean_nat_to_int(v___x_478_);
return v___x_479_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__1(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_480_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__0, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__0_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__0);
v___x_481_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_482_ = lean_int_add(v___x_481_, v___x_480_);
return v___x_482_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__2(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_483_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_484_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__1, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__1_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__1);
v___x_485_ = lean_int_sub(v___x_484_, v___x_483_);
return v___x_485_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v_range_488_; 
v___x_486_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_487_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__2, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__2_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__2);
v_range_488_ = lean_int_add(v___x_487_, v___x_486_);
return v_range_488_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3(lean_object* v_n_489_){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v_range_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_490_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_491_ = lean_nat_to_int(v_n_489_);
v_range_492_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3);
v___x_493_ = lean_int_sub(v___x_491_, v___x_490_);
lean_dec(v___x_491_);
v___x_494_ = lean_int_emod(v___x_493_, v_range_492_);
lean_dec(v___x_493_);
v___x_495_ = lean_int_add(v___x_494_, v_range_492_);
lean_dec(v___x_494_);
v___x_496_ = lean_int_emod(v___x_495_, v_range_492_);
lean_dec(v___x_495_);
v___x_497_ = lean_int_add(v___x_496_, v___x_490_);
lean_dec(v___x_496_);
return v___x_497_;
}
}
lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear(uint8_t v_leap_498_, lean_object* v_n_499_){
_start:
{
if (v_leap_498_ == 0)
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v_range_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_500_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_501_ = lean_nat_to_int(v_n_499_);
v_range_502_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3);
v___x_503_ = lean_int_sub(v___x_501_, v___x_500_);
lean_dec(v___x_501_);
v___x_504_ = lean_int_emod(v___x_503_, v_range_502_);
lean_dec(v___x_503_);
v___x_505_ = lean_int_add(v___x_504_, v_range_502_);
lean_dec(v___x_504_);
v___x_506_ = lean_int_emod(v___x_505_, v_range_502_);
lean_dec(v___x_505_);
v___x_507_ = lean_int_add(v___x_506_, v___x_500_);
lean_dec(v___x_506_);
return v___x_507_;
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v_range_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_508_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
v___x_509_ = lean_nat_to_int(v_n_499_);
v_range_510_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3, &l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3_once, _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3);
v___x_511_ = lean_int_sub(v___x_509_, v___x_508_);
lean_dec(v___x_509_);
v___x_512_ = lean_int_emod(v___x_511_, v_range_510_);
lean_dec(v___x_511_);
v___x_513_ = lean_int_add(v___x_512_, v_range_510_);
lean_dec(v___x_512_);
v___x_514_ = lean_int_emod(v___x_513_, v_range_510_);
lean_dec(v___x_513_);
v___x_515_ = lean_int_add(v___x_514_, v___x_508_);
lean_dec(v___x_514_);
return v___x_515_;
}
}
}
LEAN_EXPORT void l_Std_Time_Day_Ordinal_instOfNatOfYear_0interp(lean_interpreter_value* stack)
{
uint8_t v_leap_498_ = stack[0].m_num;
lean_object* v_n_499_ = stack[1].m_obj;
lean_object* v_res_516_;
v_res_516_ = l_Std_Time_Day_Ordinal_instOfNatOfYear(v_leap_498_, v_n_499_);
stack->m_obj
 = v_res_516_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear___boxed(lean_object* v_leap_517_, lean_object* v_n_518_){
_start:
{
uint8_t v_leap_boxed_519_; lean_object* v_res_520_; 
v_leap_boxed_519_ = lean_unbox(v_leap_517_);
v_res_520_ = l_Std_Time_Day_Ordinal_instOfNatOfYear(v_leap_boxed_519_, v_n_518_);
return v_res_520_;
}
}
lean_object* l_Std_Time_Day_Ordinal_instInhabitedOfYear___redArg(){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0);
return v___x_522_;
}
}
LEAN_EXPORT void l_Std_Time_Day_Ordinal_instInhabitedOfYear___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_523_;
v_res_523_ = l_Std_Time_Day_Ordinal_instInhabitedOfYear___redArg();
stack->m_obj
 = v_res_523_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instInhabitedOfYear___redArg___boxed(lean_object* v___dummy_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Std_Time_Day_Ordinal_instInhabitedOfYear___redArg();
return v_res_525_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instInhabitedOfYear___closed__0(void){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Std_Time_Day_Ordinal_instInhabitedOfYear___redArg();
return v___x_526_;
}
}
lean_object* l_Std_Time_Day_Ordinal_instInhabitedOfYear(uint8_t v_leap_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instInhabitedOfYear___closed__0, &l_Std_Time_Day_Ordinal_instInhabitedOfYear___closed__0_once, _init_l_Std_Time_Day_Ordinal_instInhabitedOfYear___closed__0);
return v___x_528_;
}
}
LEAN_EXPORT void l_Std_Time_Day_Ordinal_instInhabitedOfYear_0interp(lean_interpreter_value* stack)
{
uint8_t v_leap_527_ = stack[0].m_num;
lean_object* v_res_529_;
v_res_529_ = l_Std_Time_Day_Ordinal_instInhabitedOfYear(v_leap_527_);
stack->m_obj
 = v_res_529_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instInhabitedOfYear___boxed(lean_object* v_leap_530_){
_start:
{
uint8_t v_leap_boxed_531_; lean_object* v_res_532_; 
v_leap_boxed_531_ = lean_unbox(v_leap_530_);
v_res_532_ = l_Std_Time_Day_Ordinal_instInhabitedOfYear(v_leap_boxed_531_);
return v_res_532_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_ofNat___auto__1(void){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofNat___redArg(lean_object* v_data_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = lean_nat_to_int(v_data_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofNat(lean_object* v_data_536_, lean_object* v_h_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = lean_nat_to_int(v_data_536_);
return v___x_538_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_ofFin___closed__0(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = lean_unsigned_to_nat(1u);
v___x_540_ = lean_nat_to_int(v___x_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofFin(lean_object* v_data_541_){
_start:
{
lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_542_ = lean_unsigned_to_nat(1u);
v___x_543_ = lean_nat_dec_le(v___x_542_, v_data_541_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; 
lean_dec(v_data_541_);
v___x_544_ = lean_obj_once(&l_Std_Time_Day_Ordinal_ofFin___closed__0, &l_Std_Time_Day_Ordinal_ofFin___closed__0_once, _init_l_Std_Time_Day_Ordinal_ofFin___closed__0);
return v___x_544_;
}
else
{
lean_object* v___x_545_; 
v___x_545_ = lean_nat_to_int(v_data_541_);
return v___x_545_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_toOffset(lean_object* v_ordinal_546_){
_start:
{
lean_inc(v_ordinal_546_);
return v_ordinal_546_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_toOffset___boxed(lean_object* v_ordinal_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Std_Time_Day_Ordinal_toOffset(v_ordinal_547_);
lean_dec(v_ordinal_547_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_toOffset___redArg(lean_object* v_ofYear_549_){
_start:
{
lean_inc(v_ofYear_549_);
return v_ofYear_549_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_toOffset___redArg___boxed(lean_object* v_ofYear_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Std_Time_Day_Ordinal_OfYear_toOffset___redArg(v_ofYear_550_);
lean_dec(v_ofYear_550_);
return v_res_551_;
}
}
lean_object* l_Std_Time_Day_Ordinal_OfYear_toOffset(uint8_t v_leap_552_, lean_object* v_ofYear_553_){
_start:
{
lean_inc(v_ofYear_553_);
return v_ofYear_553_;
}
}
LEAN_EXPORT void l_Std_Time_Day_Ordinal_OfYear_toOffset_0interp(lean_interpreter_value* stack)
{
uint8_t v_leap_552_ = stack[0].m_num;
lean_object* v_ofYear_553_ = stack[1].m_obj;
lean_object* v_res_554_;
v_res_554_ = l_Std_Time_Day_Ordinal_OfYear_toOffset(v_leap_552_, v_ofYear_553_);
stack->m_obj
 = v_res_554_;
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_toOffset___boxed(lean_object* v_leap_555_, lean_object* v_ofYear_556_){
_start:
{
uint8_t v_leap_boxed_557_; lean_object* v_res_558_; 
v_leap_boxed_557_ = lean_unbox(v_leap_555_);
v_res_558_ = l_Std_Time_Day_Ordinal_OfYear_toOffset(v_leap_boxed_557_, v_ofYear_556_);
lean_dec(v_ofYear_556_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toOrdinal___redArg(lean_object* v_off_559_){
_start:
{
lean_inc(v_off_559_);
return v_off_559_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toOrdinal___redArg___boxed(lean_object* v_off_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Std_Time_Day_Offset_toOrdinal___redArg(v_off_560_);
lean_dec(v_off_560_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toOrdinal(lean_object* v_off_562_, lean_object* v_h_563_){
_start:
{
lean_inc(v_off_562_);
return v_off_562_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toOrdinal___boxed(lean_object* v_off_564_, lean_object* v_h_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Std_Time_Day_Offset_toOrdinal(v_off_564_, v_h_565_);
lean_dec(v_off_564_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofNat(lean_object* v_data_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = lean_nat_to_int(v_data_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofInt(lean_object* v_data_569_){
_start:
{
lean_inc(v_data_569_);
return v_data_569_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofInt___boxed(lean_object* v_data_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Std_Time_Day_Offset_ofInt(v_data_570_);
lean_dec(v_data_570_);
return v_res_571_;
}
}
static lean_object* _init_l_Std_Time_Day_Offset_toNanoseconds___closed__0(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = lean_cstr_to_nat("86400000000000");
v___x_573_ = lean_nat_to_int(v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toNanoseconds(lean_object* v_days_574_){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_obj_once(&l_Std_Time_Day_Offset_toNanoseconds___closed__0, &l_Std_Time_Day_Offset_toNanoseconds___closed__0_once, _init_l_Std_Time_Day_Offset_toNanoseconds___closed__0);
v___x_576_ = lean_int_mul(v_days_574_, v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toNanoseconds___boxed(lean_object* v_days_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Std_Time_Day_Offset_toNanoseconds(v_days_577_);
lean_dec(v_days_577_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofNanoseconds(lean_object* v_ns_579_){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_obj_once(&l_Std_Time_Day_Offset_toNanoseconds___closed__0, &l_Std_Time_Day_Offset_toNanoseconds___closed__0_once, _init_l_Std_Time_Day_Offset_toNanoseconds___closed__0);
v___x_581_ = lean_int_ediv(v_ns_579_, v___x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofNanoseconds___boxed(lean_object* v_ns_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Std_Time_Day_Offset_ofNanoseconds(v_ns_582_);
lean_dec(v_ns_582_);
return v_res_583_;
}
}
static lean_object* _init_l_Std_Time_Day_Offset_toMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = lean_unsigned_to_nat(86400000u);
v___x_585_ = lean_nat_to_int(v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toMilliseconds(lean_object* v_days_586_){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = lean_obj_once(&l_Std_Time_Day_Offset_toMilliseconds___closed__0, &l_Std_Time_Day_Offset_toMilliseconds___closed__0_once, _init_l_Std_Time_Day_Offset_toMilliseconds___closed__0);
v___x_588_ = lean_int_mul(v_days_586_, v___x_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toMilliseconds___boxed(lean_object* v_days_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Std_Time_Day_Offset_toMilliseconds(v_days_589_);
lean_dec(v_days_589_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofMilliseconds(lean_object* v_ms_591_){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_obj_once(&l_Std_Time_Day_Offset_toMilliseconds___closed__0, &l_Std_Time_Day_Offset_toMilliseconds___closed__0_once, _init_l_Std_Time_Day_Offset_toMilliseconds___closed__0);
v___x_593_ = lean_int_ediv(v_ms_591_, v___x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofMilliseconds___boxed(lean_object* v_ms_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Std_Time_Day_Offset_ofMilliseconds(v_ms_594_);
lean_dec(v_ms_594_);
return v_res_595_;
}
}
static lean_object* _init_l_Std_Time_Day_Offset_toSeconds___closed__0(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_unsigned_to_nat(86400u);
v___x_597_ = lean_nat_to_int(v___x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toSeconds(lean_object* v_days_598_){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_obj_once(&l_Std_Time_Day_Offset_toSeconds___closed__0, &l_Std_Time_Day_Offset_toSeconds___closed__0_once, _init_l_Std_Time_Day_Offset_toSeconds___closed__0);
v___x_600_ = lean_int_mul(v_days_598_, v___x_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toSeconds___boxed(lean_object* v_days_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Std_Time_Day_Offset_toSeconds(v_days_601_);
lean_dec(v_days_601_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofSeconds(lean_object* v_secs_603_){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_obj_once(&l_Std_Time_Day_Offset_toSeconds___closed__0, &l_Std_Time_Day_Offset_toSeconds___closed__0_once, _init_l_Std_Time_Day_Offset_toSeconds___closed__0);
v___x_605_ = lean_int_ediv(v_secs_603_, v___x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofSeconds___boxed(lean_object* v_secs_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Std_Time_Day_Offset_ofSeconds(v_secs_606_);
lean_dec(v_secs_606_);
return v_res_607_;
}
}
static lean_object* _init_l_Std_Time_Day_Offset_toMinutes___closed__0(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_unsigned_to_nat(1440u);
v___x_609_ = lean_nat_to_int(v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toMinutes(lean_object* v_days_610_){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_obj_once(&l_Std_Time_Day_Offset_toMinutes___closed__0, &l_Std_Time_Day_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Day_Offset_toMinutes___closed__0);
v___x_612_ = lean_int_mul(v_days_610_, v___x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toMinutes___boxed(lean_object* v_days_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Std_Time_Day_Offset_toMinutes(v_days_613_);
lean_dec(v_days_613_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofMinutes(lean_object* v_minutes_615_){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_obj_once(&l_Std_Time_Day_Offset_toMinutes___closed__0, &l_Std_Time_Day_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Day_Offset_toMinutes___closed__0);
v___x_617_ = lean_int_ediv(v_minutes_615_, v___x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofMinutes___boxed(lean_object* v_minutes_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Std_Time_Day_Offset_ofMinutes(v_minutes_618_);
lean_dec(v_minutes_618_);
return v_res_619_;
}
}
static lean_object* _init_l_Std_Time_Day_Offset_toHours___closed__0(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_unsigned_to_nat(24u);
v___x_621_ = lean_nat_to_int(v___x_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toHours(lean_object* v_days_622_){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_obj_once(&l_Std_Time_Day_Offset_toHours___closed__0, &l_Std_Time_Day_Offset_toHours___closed__0_once, _init_l_Std_Time_Day_Offset_toHours___closed__0);
v___x_624_ = lean_int_mul(v_days_622_, v___x_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toHours___boxed(lean_object* v_days_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Std_Time_Day_Offset_toHours(v_days_625_);
lean_dec(v_days_625_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofHours(lean_object* v_hours_627_){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = lean_obj_once(&l_Std_Time_Day_Offset_toHours___closed__0, &l_Std_Time_Day_Offset_toHours___closed__0_once, _init_l_Std_Time_Day_Offset_toHours___closed__0);
v___x_629_ = lean_int_ediv(v_hours_627_, v___x_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofHours___boxed(lean_object* v_hours_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Std_Time_Day_Offset_ofHours(v_hours_630_);
lean_dec(v_hours_630_);
return v_res_631_;
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
