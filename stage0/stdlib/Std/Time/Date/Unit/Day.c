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
lean_object* l_Std_Time_Internal_Bounded_instOrd___lam__0___boxed(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_instOrdInt___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Std_Time_Internal_instInhabitedUnitVal_default(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_instOrdUnitVal___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_Bounded_instRepr___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_UnitVal_sub___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_repr___boxed(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_UnitVal_instRepr___lam__0___boxed(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_neg___boxed(lean_object*);
lean_object* l_Std_Time_Internal_UnitVal_add___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Day_instReprOrdinal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_Bounded_instRepr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Day_instReprOrdinal___closed__0 = (const lean_object*)&l_Std_Time_Day_instReprOrdinal___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Day_instReprOrdinal = (const lean_object*)&l_Std_Time_Day_instReprOrdinal___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableEqOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableEqOrdinal___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instLEOrdinal;
LEAN_EXPORT lean_object* l_Std_Time_Day_instLTOrdinal;
static lean_once_cell_t l_Std_Time_Day_instOfNatOrdinal___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_instOfNatOrdinal___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Day_instOfNatOrdinal(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLeOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLeOrdinal___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_Time_Day_instInhabitedOrdinal___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_instInhabitedOrdinal___closed__5;
static lean_once_cell_t l_Std_Time_Day_instInhabitedOrdinal___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_instInhabitedOrdinal___closed__6;
static lean_once_cell_t l_Std_Time_Day_instInhabitedOrdinal___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_instInhabitedOrdinal___closed__7;
static lean_once_cell_t l_Std_Time_Day_instInhabitedOrdinal___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_instInhabitedOrdinal___closed__8;
LEAN_EXPORT lean_object* l_Std_Time_Day_instInhabitedOrdinal;
static const lean_closure_object l_Std_Time_Day_instOrdOrdinal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_Bounded_instOrd___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Day_instOrdOrdinal___closed__0 = (const lean_object*)&l_Std_Time_Day_instOrdOrdinal___closed__0_value;
static const lean_closure_object l_Std_Time_Day_instOrdOrdinal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdInt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Day_instOrdOrdinal___closed__1 = (const lean_object*)&l_Std_Time_Day_instOrdOrdinal___closed__1_value;
static const lean_closure_object l_Std_Time_Day_instOrdOrdinal___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_compareOn___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Day_instOrdOrdinal___closed__1_value),((lean_object*)&l_Std_Time_Day_instOrdOrdinal___closed__0_value)} };
static const lean_object* l_Std_Time_Day_instOrdOrdinal___closed__2 = (const lean_object*)&l_Std_Time_Day_instOrdOrdinal___closed__2_value;
LEAN_EXPORT const lean_object* l_Std_Time_Day_instOrdOrdinal = (const lean_object*)&l_Std_Time_Day_instOrdOrdinal___closed__2_value;
static const lean_closure_object l_Std_Time_Day_instReprOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_UnitVal_instRepr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Day_instReprOffset___closed__0 = (const lean_object*)&l_Std_Time_Day_instReprOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Day_instReprOffset = (const lean_object*)&l_Std_Time_Day_instReprOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Day_instReprOffset_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Day_instReprOffset_spec__0(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableEqOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableEqOffset___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Day_instInhabitedOffset___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_instInhabitedOffset___closed__0;
static lean_once_cell_t l_Std_Time_Day_instInhabitedOffset___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_instInhabitedOffset___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_Day_instInhabitedOffset;
static lean_once_cell_t l_Std_Time_Day_instAddOffset___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_instAddOffset___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Day_instAddOffset;
static lean_once_cell_t l_Std_Time_Day_instSubOffset___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_instSubOffset___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Day_instSubOffset;
static const lean_closure_object l_Std_Time_Day_instNegOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Day_instNegOffset___closed__0 = (const lean_object*)&l_Std_Time_Day_instNegOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Day_instNegOffset = (const lean_object*)&l_Std_Time_Day_instNegOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Day_instLEOffset;
LEAN_EXPORT lean_object* l_Std_Time_Day_instLTOffset;
static const lean_closure_object l_Std_Time_Day_instToStringOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_repr___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Day_instToStringOffset___closed__0 = (const lean_object*)&l_Std_Time_Day_instToStringOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Day_instToStringOffset = (const lean_object*)&l_Std_Time_Day_instToStringOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Day_instOfNatOffset(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLeOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLeOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLtOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLtOffset___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Day_instOrdOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_instOrdUnitVal___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Day_instOrdOffset___closed__0 = (const lean_object*)&l_Std_Time_Day_instOrdOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Day_instOrdOffset = (const lean_object*)&l_Std_Time_Day_instOrdOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Day_Ordinal_instReprOfYear___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Day_Ordinal_instReprOfYear___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Day_Ordinal_instReprOfYear___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___closed__0 = (const lean_object*)&l_Std_Time_Day_Ordinal_instReprOfYear___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instToStringOfYear(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instToStringOfYear___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Day_Ordinal_instDecidableEqOfYear___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instDecidableEqOfYear___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Day_Ordinal_instDecidableEqOfYear(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instDecidableEqOfYear___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableEqOrdinal(lean_object* v_a_3_, lean_object* v_b_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_int_dec_eq(v_a_3_, v_b_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableEqOrdinal___boxed(lean_object* v_a_6_, lean_object* v_b_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = l_Std_Time_Day_instDecidableEqOrdinal(v_a_6_, v_b_7_);
lean_dec(v_b_7_);
lean_dec(v_a_6_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
static lean_object* _init_l_Std_Time_Day_instLEOrdinal(void){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_box(0);
return v___x_10_;
}
}
static lean_object* _init_l_Std_Time_Day_instLTOrdinal(void){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_box(0);
return v___x_11_;
}
}
static lean_object* _init_l_Std_Time_Day_instOfNatOrdinal___closed__0(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_unsigned_to_nat(1u);
v___x_13_ = lean_nat_to_int(v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instOfNatOrdinal(lean_object* v_n_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_15_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___closed__0, &l_Std_Time_Day_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___closed__0);
v___x_16_ = lean_unsigned_to_nat(30u);
v___x_17_ = l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast(v___x_15_, v_n_14_, v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLeOrdinal(lean_object* v_x_18_, lean_object* v_y_19_){
_start:
{
uint8_t v___x_20_; 
v___x_20_ = lean_int_dec_le(v_x_18_, v_y_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLeOrdinal___boxed(lean_object* v_x_21_, lean_object* v_y_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l_Std_Time_Day_instDecidableLeOrdinal(v_x_21_, v_y_22_);
lean_dec(v_y_22_);
lean_dec(v_x_21_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLtOrdinal(lean_object* v_x_25_, lean_object* v_y_26_){
_start:
{
uint8_t v___x_27_; 
v___x_27_ = lean_int_dec_lt(v_x_25_, v_y_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLtOrdinal___boxed(lean_object* v_x_28_, lean_object* v_y_29_){
_start:
{
uint8_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = l_Std_Time_Day_instDecidableLtOrdinal(v_x_28_, v_y_29_);
lean_dec(v_y_29_);
lean_dec(v_x_28_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOrdinal___closed__0(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = lean_unsigned_to_nat(30u);
v___x_33_ = lean_nat_to_int(v___x_32_);
return v___x_33_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOrdinal___closed__1(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_34_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOrdinal___closed__0, &l_Std_Time_Day_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Day_instInhabitedOrdinal___closed__0);
v___x_35_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___closed__0, &l_Std_Time_Day_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___closed__0);
v___x_36_ = lean_int_add(v___x_35_, v___x_34_);
return v___x_36_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOrdinal___closed__2(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_37_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___closed__0, &l_Std_Time_Day_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___closed__0);
v___x_38_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOrdinal___closed__1, &l_Std_Time_Day_instInhabitedOrdinal___closed__1_once, _init_l_Std_Time_Day_instInhabitedOrdinal___closed__1);
v___x_39_ = lean_int_sub(v___x_38_, v___x_37_);
return v___x_39_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOrdinal___closed__3(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v_range_42_; 
v___x_40_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___closed__0, &l_Std_Time_Day_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___closed__0);
v___x_41_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOrdinal___closed__2, &l_Std_Time_Day_instInhabitedOrdinal___closed__2_once, _init_l_Std_Time_Day_instInhabitedOrdinal___closed__2);
v_range_42_ = lean_int_add(v___x_41_, v___x_40_);
return v_range_42_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOrdinal___closed__4(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___closed__0, &l_Std_Time_Day_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___closed__0);
v___x_44_ = lean_int_sub(v___x_43_, v___x_43_);
return v___x_44_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOrdinal___closed__5(void){
_start:
{
lean_object* v_range_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v_range_45_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOrdinal___closed__3, &l_Std_Time_Day_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Day_instInhabitedOrdinal___closed__3);
v___x_46_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOrdinal___closed__4, &l_Std_Time_Day_instInhabitedOrdinal___closed__4_once, _init_l_Std_Time_Day_instInhabitedOrdinal___closed__4);
v___x_47_ = lean_int_emod(v___x_46_, v_range_45_);
return v___x_47_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOrdinal___closed__6(void){
_start:
{
lean_object* v_range_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_range_48_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOrdinal___closed__3, &l_Std_Time_Day_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Day_instInhabitedOrdinal___closed__3);
v___x_49_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOrdinal___closed__5, &l_Std_Time_Day_instInhabitedOrdinal___closed__5_once, _init_l_Std_Time_Day_instInhabitedOrdinal___closed__5);
v___x_50_ = lean_int_add(v___x_49_, v_range_48_);
return v___x_50_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOrdinal___closed__7(void){
_start:
{
lean_object* v_range_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v_range_51_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOrdinal___closed__3, &l_Std_Time_Day_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Day_instInhabitedOrdinal___closed__3);
v___x_52_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOrdinal___closed__6, &l_Std_Time_Day_instInhabitedOrdinal___closed__6_once, _init_l_Std_Time_Day_instInhabitedOrdinal___closed__6);
v___x_53_ = lean_int_emod(v___x_52_, v_range_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOrdinal___closed__8(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___closed__0, &l_Std_Time_Day_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___closed__0);
v___x_55_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOrdinal___closed__7, &l_Std_Time_Day_instInhabitedOrdinal___closed__7_once, _init_l_Std_Time_Day_instInhabitedOrdinal___closed__7);
v___x_56_ = lean_int_add(v___x_55_, v___x_54_);
return v___x_56_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOrdinal(void){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOrdinal___closed__8, &l_Std_Time_Day_instInhabitedOrdinal___closed__8_once, _init_l_Std_Time_Day_instInhabitedOrdinal___closed__8);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Day_instReprOffset_spec__0_spec__0(lean_object* v_a_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lean_nat_to_int(v_a_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Day_instReprOffset_spec__0(lean_object* v_a_68_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_nat_to_int(v_a_68_);
v___x_70_ = l_Rat_ofInt(v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableEqOffset(lean_object* v_a_71_, lean_object* v_b_72_){
_start:
{
uint8_t v___x_73_; 
v___x_73_ = lean_int_dec_eq(v_a_71_, v_b_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableEqOffset___boxed(lean_object* v_a_74_, lean_object* v_b_75_){
_start:
{
uint8_t v_res_76_; lean_object* v_r_77_; 
v_res_76_ = l_Std_Time_Day_instDecidableEqOffset(v_a_74_, v_b_75_);
lean_dec(v_b_75_);
lean_dec(v_a_74_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOffset___closed__0(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(86400u);
v___x_79_ = l_Nat_cast___at___00Std_Time_Day_instReprOffset_spec__0(v___x_78_);
return v___x_79_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOffset___closed__1(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOffset___closed__0, &l_Std_Time_Day_instInhabitedOffset___closed__0_once, _init_l_Std_Time_Day_instInhabitedOffset___closed__0);
v___x_81_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_80_);
return v___x_81_;
}
}
static lean_object* _init_l_Std_Time_Day_instInhabitedOffset(void){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOffset___closed__1, &l_Std_Time_Day_instInhabitedOffset___closed__1_once, _init_l_Std_Time_Day_instInhabitedOffset___closed__1);
return v___x_82_;
}
}
static lean_object* _init_l_Std_Time_Day_instAddOffset___closed__0(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOffset___closed__0, &l_Std_Time_Day_instInhabitedOffset___closed__0_once, _init_l_Std_Time_Day_instInhabitedOffset___closed__0);
v___x_84_ = lean_alloc_closure((void*)(l_Std_Time_Internal_UnitVal_add___boxed), 3, 1);
lean_closure_set(v___x_84_, 0, v___x_83_);
return v___x_84_;
}
}
static lean_object* _init_l_Std_Time_Day_instAddOffset(void){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = lean_obj_once(&l_Std_Time_Day_instAddOffset___closed__0, &l_Std_Time_Day_instAddOffset___closed__0_once, _init_l_Std_Time_Day_instAddOffset___closed__0);
return v___x_85_;
}
}
static lean_object* _init_l_Std_Time_Day_instSubOffset___closed__0(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_obj_once(&l_Std_Time_Day_instInhabitedOffset___closed__0, &l_Std_Time_Day_instInhabitedOffset___closed__0_once, _init_l_Std_Time_Day_instInhabitedOffset___closed__0);
v___x_87_ = lean_alloc_closure((void*)(l_Std_Time_Internal_UnitVal_sub___boxed), 3, 1);
lean_closure_set(v___x_87_, 0, v___x_86_);
return v___x_87_;
}
}
static lean_object* _init_l_Std_Time_Day_instSubOffset(void){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lean_obj_once(&l_Std_Time_Day_instSubOffset___closed__0, &l_Std_Time_Day_instSubOffset___closed__0_once, _init_l_Std_Time_Day_instSubOffset___closed__0);
return v___x_88_;
}
}
static lean_object* _init_l_Std_Time_Day_instLEOffset(void){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_box(0);
return v___x_91_;
}
}
static lean_object* _init_l_Std_Time_Day_instLTOffset(void){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lean_box(0);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instOfNatOffset(lean_object* v_n_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_nat_to_int(v_n_95_);
return v___x_96_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLeOffset(lean_object* v_x_97_, lean_object* v_y_98_){
_start:
{
uint8_t v___x_99_; 
v___x_99_ = lean_int_dec_le(v_x_97_, v_y_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLeOffset___boxed(lean_object* v_x_100_, lean_object* v_y_101_){
_start:
{
uint8_t v_res_102_; lean_object* v_r_103_; 
v_res_102_ = l_Std_Time_Day_instDecidableLeOffset(v_x_100_, v_y_101_);
lean_dec(v_y_101_);
lean_dec(v_x_100_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_instDecidableLtOffset(lean_object* v_x_104_, lean_object* v_y_105_){
_start:
{
uint8_t v___x_106_; 
v___x_106_ = lean_int_dec_lt(v_x_104_, v_y_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_instDecidableLtOffset___boxed(lean_object* v_x_107_, lean_object* v_y_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Std_Time_Day_instDecidableLtOffset(v_x_107_, v_y_108_);
lean_dec(v_y_108_);
lean_dec(v_x_107_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt___redArg(lean_object* v_data_113_){
_start:
{
lean_inc(v_data_113_);
return v_data_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt___redArg___boxed(lean_object* v_data_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Std_Time_Day_Ordinal_ofInt___redArg(v_data_114_);
lean_dec(v_data_114_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt(lean_object* v_data_116_, lean_object* v_h_117_){
_start:
{
lean_inc(v_data_116_);
return v_data_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofInt___boxed(lean_object* v_data_118_, lean_object* v_h_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Std_Time_Day_Ordinal_ofInt(v_data_118_, v_h_119_);
lean_dec(v_data_118_);
return v_res_120_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_instReprOfYear___lam__0___closed__0(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_nat_to_int(v___x_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___lam__0(lean_object* v_r_123_, lean_object* v_p_124_){
_start:
{
lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_125_ = lean_obj_once(&l_Std_Time_Day_Ordinal_instReprOfYear___lam__0___closed__0, &l_Std_Time_Day_Ordinal_instReprOfYear___lam__0___closed__0_once, _init_l_Std_Time_Day_Ordinal_instReprOfYear___lam__0___closed__0);
v___x_126_ = lean_int_dec_lt(v_r_123_, v___x_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = l_Int_repr(v_r_123_);
v___x_128_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
return v___x_128_;
}
else
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = l_Int_repr(v_r_123_);
v___x_130_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
v___x_131_ = l_Repr_addAppParen(v___x_130_, v_p_124_);
return v___x_131_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___lam__0___boxed(lean_object* v_r_132_, lean_object* v_p_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Std_Time_Day_Ordinal_instReprOfYear___lam__0(v_r_132_, v_p_133_);
lean_dec(v_p_133_);
lean_dec(v_r_132_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear(uint8_t v_leap_136_){
_start:
{
lean_object* v___f_137_; 
v___f_137_ = ((lean_object*)(l_Std_Time_Day_Ordinal_instReprOfYear___closed__0));
return v___f_137_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instReprOfYear___boxed(lean_object* v_leap_138_){
_start:
{
uint8_t v_leap_boxed_139_; lean_object* v_res_140_; 
v_leap_boxed_139_ = lean_unbox(v_leap_138_);
v_res_140_ = l_Std_Time_Day_Ordinal_instReprOfYear(v_leap_boxed_139_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instToStringOfYear(uint8_t v_leap_141_){
_start:
{
lean_object* v___f_142_; 
v___f_142_ = ((lean_object*)(l_Std_Time_Day_instToStringOffset___closed__0));
return v___f_142_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instToStringOfYear___boxed(lean_object* v_leap_143_){
_start:
{
uint8_t v_leap_boxed_144_; lean_object* v_res_145_; 
v_leap_boxed_144_ = lean_unbox(v_leap_143_);
v_res_145_ = l_Std_Time_Day_Ordinal_instToStringOfYear(v_leap_boxed_144_);
return v_res_145_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_Ordinal_instDecidableEqOfYear___redArg(lean_object* v_a_146_, lean_object* v_b_147_){
_start:
{
uint8_t v___x_148_; 
v___x_148_ = lean_int_dec_eq(v_a_146_, v_b_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instDecidableEqOfYear___redArg___boxed(lean_object* v_a_149_, lean_object* v_b_150_){
_start:
{
uint8_t v_res_151_; lean_object* v_r_152_; 
v_res_151_ = l_Std_Time_Day_Ordinal_instDecidableEqOfYear___redArg(v_a_149_, v_b_150_);
lean_dec(v_b_150_);
lean_dec(v_a_149_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Day_Ordinal_instDecidableEqOfYear(uint8_t v_leap_153_, lean_object* v_a_154_, lean_object* v_b_155_){
_start:
{
uint8_t v___x_156_; 
v___x_156_ = lean_int_dec_eq(v_a_154_, v_b_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instDecidableEqOfYear___boxed(lean_object* v_leap_157_, lean_object* v_a_158_, lean_object* v_b_159_){
_start:
{
uint8_t v_leap_boxed_160_; uint8_t v_res_161_; lean_object* v_r_162_; 
v_leap_boxed_160_ = lean_unbox(v_leap_157_);
v_res_161_ = l_Std_Time_Day_Ordinal_instDecidableEqOfYear(v_leap_boxed_160_, v_a_158_, v_b_159_);
lean_dec(v_b_159_);
lean_dec(v_a_158_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOrdOfYear(uint8_t v_leap_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = ((lean_object*)(l_Std_Time_Day_instOrdOrdinal___closed__2));
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOrdOfYear___boxed(lean_object* v_leap_165_){
_start:
{
uint8_t v_leap_boxed_166_; lean_object* v_res_167_; 
v_leap_boxed_166_ = lean_unbox(v_leap_165_);
v_res_167_ = l_Std_Time_Day_Ordinal_instOrdOfYear(v_leap_boxed_166_);
return v_res_167_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__12(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__10));
v___x_195_ = l_Lean_mkAtom(v___x_194_);
return v___x_195_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__13(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_196_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__12, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__12_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__12);
v___x_197_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5));
v___x_198_ = lean_array_push(v___x_197_, v___x_196_);
return v___x_198_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__17(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_209_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__16));
v___x_210_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5));
v___x_211_ = lean_array_push(v___x_210_, v___x_209_);
return v___x_211_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__18(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_212_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__17, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__17_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__17);
v___x_213_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__15));
v___x_214_ = lean_box(2);
v___x_215_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v___x_213_);
lean_ctor_set(v___x_215_, 2, v___x_212_);
return v___x_215_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__19(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_216_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__18, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__18_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__18);
v___x_217_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__13, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__13_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__13);
v___x_218_ = lean_array_push(v___x_217_, v___x_216_);
return v___x_218_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__20(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_219_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__19, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__19_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__19);
v___x_220_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__11));
v___x_221_ = lean_box(2);
v___x_222_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v___x_220_);
lean_ctor_set(v___x_222_, 2, v___x_219_);
return v___x_222_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__21(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_223_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__20, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__20_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__20);
v___x_224_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5));
v___x_225_ = lean_array_push(v___x_224_, v___x_223_);
return v___x_225_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__22(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_226_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__21, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__21_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__21);
v___x_227_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__9));
v___x_228_ = lean_box(2);
v___x_229_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v___x_227_);
lean_ctor_set(v___x_229_, 2, v___x_226_);
return v___x_229_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__23(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_230_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__22, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__22_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__22);
v___x_231_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5));
v___x_232_ = lean_array_push(v___x_231_, v___x_230_);
return v___x_232_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__24(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_233_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__23, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__23_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__23);
v___x_234_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__7));
v___x_235_ = lean_box(2);
v___x_236_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set(v___x_236_, 1, v___x_234_);
lean_ctor_set(v___x_236_, 2, v___x_233_);
return v___x_236_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__25(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_237_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__24, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__24_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__24);
v___x_238_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5));
v___x_239_ = lean_array_push(v___x_238_, v___x_237_);
return v___x_239_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_240_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__25, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__25_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__25);
v___x_241_ = ((lean_object*)(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__4));
v___x_242_ = lean_box(2);
v___x_243_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v___x_241_);
lean_ctor_set(v___x_243_, 2, v___x_240_);
return v___x_243_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3(void){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___redArg(lean_object* v_data_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = lean_nat_to_int(v_data_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat(uint8_t v_leap_247_, lean_object* v_data_248_, lean_object* v_h_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = lean_nat_to_int(v_data_248_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_ofNat___boxed(lean_object* v_leap_251_, lean_object* v_data_252_, lean_object* v_h_253_){
_start:
{
uint8_t v_leap_boxed_254_; lean_object* v_res_255_; 
v_leap_boxed_254_ = lean_unbox(v_leap_251_);
v_res_255_ = l_Std_Time_Day_Ordinal_OfYear_ofNat(v_leap_boxed_254_, v_data_252_, v_h_253_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear(uint8_t v_leap_256_, lean_object* v_n_257_){
_start:
{
if (v_leap_256_ == 0)
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_258_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___closed__0, &l_Std_Time_Day_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___closed__0);
v___x_259_ = lean_unsigned_to_nat(364u);
v___x_260_ = l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast(v___x_258_, v_n_257_, v___x_259_);
return v___x_260_;
}
else
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___closed__0, &l_Std_Time_Day_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___closed__0);
v___x_262_ = lean_unsigned_to_nat(365u);
v___x_263_ = l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast(v___x_261_, v_n_257_, v___x_262_);
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instOfNatOfYear___boxed(lean_object* v_leap_264_, lean_object* v_n_265_){
_start:
{
uint8_t v_leap_boxed_266_; lean_object* v_res_267_; 
v_leap_boxed_266_ = lean_unbox(v_leap_264_);
v_res_267_ = l_Std_Time_Day_Ordinal_instOfNatOfYear(v_leap_boxed_266_, v_n_265_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instInhabitedOfYear(uint8_t v_leap_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = lean_obj_once(&l_Std_Time_Day_instOfNatOrdinal___closed__0, &l_Std_Time_Day_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Day_instOfNatOrdinal___closed__0);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_instInhabitedOfYear___boxed(lean_object* v_leap_270_){
_start:
{
uint8_t v_leap_boxed_271_; lean_object* v_res_272_; 
v_leap_boxed_271_ = lean_unbox(v_leap_270_);
v_res_272_ = l_Std_Time_Day_Ordinal_instInhabitedOfYear(v_leap_boxed_271_);
return v_res_272_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_ofNat___auto__1(void){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = lean_obj_once(&l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26, &l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26_once, _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofNat___redArg(lean_object* v_data_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = lean_nat_to_int(v_data_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofNat(lean_object* v_data_276_, lean_object* v_h_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = lean_nat_to_int(v_data_276_);
return v___x_278_;
}
}
static lean_object* _init_l_Std_Time_Day_Ordinal_ofFin___closed__0(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_unsigned_to_nat(1u);
v___x_280_ = lean_nat_to_int(v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_ofFin(lean_object* v_data_281_){
_start:
{
lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_282_ = lean_unsigned_to_nat(1u);
v___x_283_ = lean_nat_dec_le(v___x_282_, v_data_281_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; 
lean_dec(v_data_281_);
v___x_284_ = lean_obj_once(&l_Std_Time_Day_Ordinal_ofFin___closed__0, &l_Std_Time_Day_Ordinal_ofFin___closed__0_once, _init_l_Std_Time_Day_Ordinal_ofFin___closed__0);
return v___x_284_;
}
else
{
lean_object* v___x_285_; 
v___x_285_ = lean_nat_to_int(v_data_281_);
return v___x_285_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_toOffset(lean_object* v_ordinal_286_){
_start:
{
lean_inc(v_ordinal_286_);
return v_ordinal_286_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_toOffset___boxed(lean_object* v_ordinal_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Std_Time_Day_Ordinal_toOffset(v_ordinal_287_);
lean_dec(v_ordinal_287_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_toOffset___redArg(lean_object* v_ofYear_289_){
_start:
{
lean_inc(v_ofYear_289_);
return v_ofYear_289_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_toOffset___redArg___boxed(lean_object* v_ofYear_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Std_Time_Day_Ordinal_OfYear_toOffset___redArg(v_ofYear_290_);
lean_dec(v_ofYear_290_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_toOffset(uint8_t v_leap_292_, lean_object* v_ofYear_293_){
_start:
{
lean_inc(v_ofYear_293_);
return v_ofYear_293_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Ordinal_OfYear_toOffset___boxed(lean_object* v_leap_294_, lean_object* v_ofYear_295_){
_start:
{
uint8_t v_leap_boxed_296_; lean_object* v_res_297_; 
v_leap_boxed_296_ = lean_unbox(v_leap_294_);
v_res_297_ = l_Std_Time_Day_Ordinal_OfYear_toOffset(v_leap_boxed_296_, v_ofYear_295_);
lean_dec(v_ofYear_295_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toOrdinal___redArg(lean_object* v_off_298_){
_start:
{
lean_inc(v_off_298_);
return v_off_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toOrdinal___redArg___boxed(lean_object* v_off_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Std_Time_Day_Offset_toOrdinal___redArg(v_off_299_);
lean_dec(v_off_299_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toOrdinal(lean_object* v_off_301_, lean_object* v_h_302_){
_start:
{
lean_inc(v_off_301_);
return v_off_301_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toOrdinal___boxed(lean_object* v_off_303_, lean_object* v_h_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Std_Time_Day_Offset_toOrdinal(v_off_303_, v_h_304_);
lean_dec(v_off_303_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofNat(lean_object* v_data_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = lean_nat_to_int(v_data_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofInt(lean_object* v_data_308_){
_start:
{
lean_inc(v_data_308_);
return v_data_308_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofInt___boxed(lean_object* v_data_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Std_Time_Day_Offset_ofInt(v_data_309_);
lean_dec(v_data_309_);
return v_res_310_;
}
}
static lean_object* _init_l_Std_Time_Day_Offset_toNanoseconds___closed__0(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = lean_cstr_to_nat("86400000000000");
v___x_312_ = lean_nat_to_int(v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toNanoseconds(lean_object* v_days_313_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_obj_once(&l_Std_Time_Day_Offset_toNanoseconds___closed__0, &l_Std_Time_Day_Offset_toNanoseconds___closed__0_once, _init_l_Std_Time_Day_Offset_toNanoseconds___closed__0);
v___x_315_ = lean_int_mul(v_days_313_, v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toNanoseconds___boxed(lean_object* v_days_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Std_Time_Day_Offset_toNanoseconds(v_days_316_);
lean_dec(v_days_316_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofNanoseconds(lean_object* v_ns_318_){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_obj_once(&l_Std_Time_Day_Offset_toNanoseconds___closed__0, &l_Std_Time_Day_Offset_toNanoseconds___closed__0_once, _init_l_Std_Time_Day_Offset_toNanoseconds___closed__0);
v___x_320_ = lean_int_ediv(v_ns_318_, v___x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofNanoseconds___boxed(lean_object* v_ns_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Std_Time_Day_Offset_ofNanoseconds(v_ns_321_);
lean_dec(v_ns_321_);
return v_res_322_;
}
}
static lean_object* _init_l_Std_Time_Day_Offset_toMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_unsigned_to_nat(86400000u);
v___x_324_ = lean_nat_to_int(v___x_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toMilliseconds(lean_object* v_days_325_){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = lean_obj_once(&l_Std_Time_Day_Offset_toMilliseconds___closed__0, &l_Std_Time_Day_Offset_toMilliseconds___closed__0_once, _init_l_Std_Time_Day_Offset_toMilliseconds___closed__0);
v___x_327_ = lean_int_mul(v_days_325_, v___x_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toMilliseconds___boxed(lean_object* v_days_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Std_Time_Day_Offset_toMilliseconds(v_days_328_);
lean_dec(v_days_328_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofMilliseconds(lean_object* v_ms_330_){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_obj_once(&l_Std_Time_Day_Offset_toMilliseconds___closed__0, &l_Std_Time_Day_Offset_toMilliseconds___closed__0_once, _init_l_Std_Time_Day_Offset_toMilliseconds___closed__0);
v___x_332_ = lean_int_ediv(v_ms_330_, v___x_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofMilliseconds___boxed(lean_object* v_ms_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Std_Time_Day_Offset_ofMilliseconds(v_ms_333_);
lean_dec(v_ms_333_);
return v_res_334_;
}
}
static lean_object* _init_l_Std_Time_Day_Offset_toSeconds___closed__0(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_unsigned_to_nat(86400u);
v___x_336_ = lean_nat_to_int(v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toSeconds(lean_object* v_days_337_){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lean_obj_once(&l_Std_Time_Day_Offset_toSeconds___closed__0, &l_Std_Time_Day_Offset_toSeconds___closed__0_once, _init_l_Std_Time_Day_Offset_toSeconds___closed__0);
v___x_339_ = lean_int_mul(v_days_337_, v___x_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toSeconds___boxed(lean_object* v_days_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Std_Time_Day_Offset_toSeconds(v_days_340_);
lean_dec(v_days_340_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofSeconds(lean_object* v_secs_342_){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_obj_once(&l_Std_Time_Day_Offset_toSeconds___closed__0, &l_Std_Time_Day_Offset_toSeconds___closed__0_once, _init_l_Std_Time_Day_Offset_toSeconds___closed__0);
v___x_344_ = lean_int_ediv(v_secs_342_, v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofSeconds___boxed(lean_object* v_secs_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Std_Time_Day_Offset_ofSeconds(v_secs_345_);
lean_dec(v_secs_345_);
return v_res_346_;
}
}
static lean_object* _init_l_Std_Time_Day_Offset_toMinutes___closed__0(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_unsigned_to_nat(1440u);
v___x_348_ = lean_nat_to_int(v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toMinutes(lean_object* v_days_349_){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_obj_once(&l_Std_Time_Day_Offset_toMinutes___closed__0, &l_Std_Time_Day_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Day_Offset_toMinutes___closed__0);
v___x_351_ = lean_int_mul(v_days_349_, v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toMinutes___boxed(lean_object* v_days_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Std_Time_Day_Offset_toMinutes(v_days_352_);
lean_dec(v_days_352_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofMinutes(lean_object* v_minutes_354_){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_obj_once(&l_Std_Time_Day_Offset_toMinutes___closed__0, &l_Std_Time_Day_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Day_Offset_toMinutes___closed__0);
v___x_356_ = lean_int_ediv(v_minutes_354_, v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofMinutes___boxed(lean_object* v_minutes_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Std_Time_Day_Offset_ofMinutes(v_minutes_357_);
lean_dec(v_minutes_357_);
return v_res_358_;
}
}
static lean_object* _init_l_Std_Time_Day_Offset_toHours___closed__0(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_unsigned_to_nat(24u);
v___x_360_ = lean_nat_to_int(v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toHours(lean_object* v_days_361_){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_obj_once(&l_Std_Time_Day_Offset_toHours___closed__0, &l_Std_Time_Day_Offset_toHours___closed__0_once, _init_l_Std_Time_Day_Offset_toHours___closed__0);
v___x_363_ = lean_int_mul(v_days_361_, v___x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_toHours___boxed(lean_object* v_days_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Std_Time_Day_Offset_toHours(v_days_364_);
lean_dec(v_days_364_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofHours(lean_object* v_hours_366_){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = lean_obj_once(&l_Std_Time_Day_Offset_toHours___closed__0, &l_Std_Time_Day_Offset_toHours___closed__0_once, _init_l_Std_Time_Day_Offset_toHours___closed__0);
v___x_368_ = lean_int_ediv(v_hours_366_, v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Day_Offset_ofHours___boxed(lean_object* v_hours_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Std_Time_Day_Offset_ofHours(v_hours_369_);
lean_dec(v_hours_369_);
return v_res_370_;
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
l_Std_Time_Day_instInhabitedOffset = _init_l_Std_Time_Day_instInhabitedOffset();
lean_mark_persistent(l_Std_Time_Day_instInhabitedOffset);
l_Std_Time_Day_instAddOffset = _init_l_Std_Time_Day_instAddOffset();
lean_mark_persistent(l_Std_Time_Day_instAddOffset);
l_Std_Time_Day_instSubOffset = _init_l_Std_Time_Day_instSubOffset();
lean_mark_persistent(l_Std_Time_Day_instSubOffset);
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
