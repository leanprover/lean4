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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Int_repr___boxed(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_instInhabitedUnitVal_default___redArg();
lean_object* l_Int_neg___boxed(lean_object*);
lean_object* lean_int_neg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Week_instReprOffset___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instReprOffset___aux__1___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Week_instReprOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instReprOffset___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instReprOffset___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instReprOffset___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Week_instReprOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Week_instReprOffset___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Week_instReprOffset___closed__0 = (const lean_object*)&l_Std_Time_Week_instReprOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Week_instReprOffset = (const lean_object*)&l_Std_Time_Week_instReprOffset___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableEqOffset___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableEqOffset___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Week_instDecidableEqOffset___aux__1_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Week_instDecidableEqOffset___aux__1_spec__0(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableEqOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableEqOffset___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Week_instInhabitedOffset___aux__1;
LEAN_EXPORT lean_object* l_Std_Time_Week_instInhabitedOffset;
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
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instReprOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instReprOrdinal___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT const lean_object* l_Std_Time_Week_OfYear_instReprOrdinal = (const lean_object*)&l_Std_Time_Week_instReprOffset___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Week_OfYear_instDecidableEqOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instDecidableEqOrdinal___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Week_OfYear_instDecidableEqOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instDecidableEqOrdinal___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instLEOrdinal;
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instLTOrdinal;
static lean_once_cell_t l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0;
static lean_once_cell_t l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__1;
static lean_once_cell_t l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__2;
static lean_once_cell_t l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__3;
static lean_once_cell_t l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4;
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instOfNatOrdinal(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Week_OfYear_instDecidableLeOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instDecidableLeOrdinal___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Week_OfYear_instDecidableLeOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instDecidableLeOrdinal___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Week_OfYear_instDecidableLtOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instDecidableLtOrdinal___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Week_OfYear_instDecidableLtOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instDecidableLtOrdinal___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__0;
static lean_once_cell_t l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__1;
static lean_once_cell_t l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__2;
static lean_once_cell_t l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__3;
static lean_once_cell_t l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__4;
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instInhabitedOrdinal;
LEAN_EXPORT uint8_t l_Std_Time_Week_OfYear_instOrdOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instOrdOrdinal___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Week_OfYear_instOrdOrdinal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Week_OfYear_instOrdOrdinal___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Week_OfYear_instOrdOrdinal___closed__0 = (const lean_object*)&l_Std_Time_Week_OfYear_instOrdOrdinal___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Week_OfYear_instOrdOrdinal = (const lean_object*)&l_Std_Time_Week_OfYear_instOrdOrdinal___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_Ordinal_ofInt___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_Ordinal_ofInt___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_Ordinal_ofInt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_Ordinal_ofInt___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__0 = (const lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__0_value;
static const lean_string_object l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__1 = (const lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__1_value;
static const lean_string_object l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__2 = (const lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__2_value;
static const lean_string_object l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__3 = (const lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__3_value;
static const lean_ctor_object l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__4_value_aux_0),((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__4_value_aux_1),((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__4_value_aux_2),((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__4 = (const lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__4_value;
static const lean_array_object l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__5 = (const lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__5_value;
static const lean_string_object l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__6 = (const lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__6_value;
static const lean_ctor_object l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__7_value_aux_0),((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__7_value_aux_1),((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__7_value_aux_2),((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__7 = (const lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__7_value;
static const lean_string_object l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__8 = (const lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__8_value;
static const lean_ctor_object l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__9 = (const lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__9_value;
static const lean_string_object l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__10 = (const lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__10_value;
static const lean_ctor_object l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__11_value_aux_0),((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__11_value_aux_1),((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__11_value_aux_2),((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(53, 158, 1, 232, 101, 200, 191, 197)}};
static const lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__11 = (const lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__11_value;
static lean_once_cell_t l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__12;
static lean_once_cell_t l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__13;
static const lean_string_object l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__14 = (const lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__14_value;
static const lean_ctor_object l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__15_value_aux_0),((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__15_value_aux_1),((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__15_value_aux_2),((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__15 = (const lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__15_value;
static const lean_ctor_object l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__9_value),((lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__5_value)}};
static const lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__16 = (const lean_object*)&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__16_value;
static lean_once_cell_t l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__17;
static lean_once_cell_t l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__18;
static lean_once_cell_t l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__19;
static lean_once_cell_t l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__20;
static lean_once_cell_t l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__21;
static lean_once_cell_t l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__22;
static lean_once_cell_t l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__23;
static lean_once_cell_t l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__24;
static lean_once_cell_t l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__25;
static lean_once_cell_t l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__26;
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1;
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Week_OfYear_Ordinal_ofFin___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_OfYear_Ordinal_ofFin___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_Ordinal_ofFin(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_Ordinal_toOffset(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_Ordinal_toOffset___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Aligned_instReprOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Aligned_instReprOrdinal___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT const lean_object* l_Std_Time_Week_Aligned_instReprOrdinal = (const lean_object*)&l_Std_Time_Week_instReprOffset___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Week_Aligned_instDecidableEqOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Aligned_instDecidableEqOrdinal___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Week_Aligned_instDecidableEqOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Aligned_instDecidableEqOrdinal___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__0;
static lean_once_cell_t l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__1;
static lean_once_cell_t l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__2;
static lean_once_cell_t l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Aligned_instOfNatOrdinal(lean_object*);
static lean_once_cell_t l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__0;
static lean_once_cell_t l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__1;
static lean_once_cell_t l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__2;
static lean_once_cell_t l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_Week_Aligned_instInhabitedOrdinal;
LEAN_EXPORT uint8_t l_Std_Time_Week_Aligned_instOrdOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Aligned_instOrdOrdinal___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Week_Aligned_instOrdOrdinal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Week_Aligned_instOrdOrdinal___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Week_Aligned_instOrdOrdinal___closed__0 = (const lean_object*)&l_Std_Time_Week_Aligned_instOrdOrdinal___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Week_Aligned_instOrdOrdinal = (const lean_object*)&l_Std_Time_Week_Aligned_instOrdOrdinal___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Week_instReprOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instReprOrdinal___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT const lean_object* l_Std_Time_Week_instReprOrdinal = (const lean_object*)&l_Std_Time_Week_instReprOffset___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableEqOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableEqOrdinal___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableEqOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableEqOrdinal___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0;
static lean_once_cell_t l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__1;
static lean_once_cell_t l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__2;
static lean_once_cell_t l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_Week_instOfNatOrdinal___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instOfNatOrdinal(lean_object*);
static lean_once_cell_t l_Std_Time_Week_instInhabitedOrdinal___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instInhabitedOrdinal___closed__0;
static lean_once_cell_t l_Std_Time_Week_instInhabitedOrdinal___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instInhabitedOrdinal___closed__1;
static lean_once_cell_t l_Std_Time_Week_instInhabitedOrdinal___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instInhabitedOrdinal___closed__2;
static lean_once_cell_t l_Std_Time_Week_instInhabitedOrdinal___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instInhabitedOrdinal___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_Week_instInhabitedOrdinal;
LEAN_EXPORT uint8_t l_Std_Time_Week_instOrdOrdinal___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instOrdOrdinal___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Week_instOrdOrdinal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Week_instOrdOrdinal___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Week_instOrdOrdinal___closed__0 = (const lean_object*)&l_Std_Time_Week_instOrdOrdinal___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Week_instOrdOrdinal = (const lean_object*)&l_Std_Time_Week_instOrdOrdinal___closed__0_value;
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
static lean_object* _init_l_Std_Time_Week_instReprOffset___aux__1___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instReprOffset___aux__1(lean_object* v_x_3_, lean_object* v_p_4_){
_start:
{
lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_5_ = lean_obj_once(&l_Std_Time_Week_instReprOffset___aux__1___closed__0, &l_Std_Time_Week_instReprOffset___aux__1___closed__0_once, _init_l_Std_Time_Week_instReprOffset___aux__1___closed__0);
v___x_6_ = lean_int_dec_lt(v_x_3_, v___x_5_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = l_Int_repr(v_x_3_);
v___x_8_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
return v___x_8_;
}
else
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_9_ = l_Int_repr(v_x_3_);
v___x_10_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
v___x_11_ = l_Repr_addAppParen(v___x_10_, v_p_4_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instReprOffset___aux__1___boxed(lean_object* v_x_12_, lean_object* v_p_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_Time_Week_instReprOffset___aux__1(v_x_12_, v_p_13_);
lean_dec(v_p_13_);
lean_dec(v_x_12_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instReprOffset___lam__0(lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
lean_object* v___x_17_; uint8_t v___x_18_; 
v___x_17_ = lean_obj_once(&l_Std_Time_Week_instReprOffset___aux__1___closed__0, &l_Std_Time_Week_instReprOffset___aux__1___closed__0_once, _init_l_Std_Time_Week_instReprOffset___aux__1___closed__0);
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
LEAN_EXPORT lean_object* l_Std_Time_Week_instReprOffset___lam__0___boxed(lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Std_Time_Week_instReprOffset___lam__0(v___y_24_, v___y_25_);
lean_dec(v___y_25_);
lean_dec(v___y_24_);
return v_res_26_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableEqOffset___aux__1(lean_object* v_a_29_, lean_object* v_b_30_){
_start:
{
uint8_t v___x_31_; 
v___x_31_ = lean_int_dec_eq(v_a_29_, v_b_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableEqOffset___aux__1___boxed(lean_object* v_a_32_, lean_object* v_b_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l_Std_Time_Week_instDecidableEqOffset___aux__1(v_a_32_, v_b_33_);
lean_dec(v_b_33_);
lean_dec(v_a_32_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Week_instDecidableEqOffset___aux__1_spec__0_spec__0(lean_object* v_a_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_nat_to_int(v_a_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Week_instDecidableEqOffset___aux__1_spec__0(lean_object* v_a_38_){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = lean_nat_to_int(v_a_38_);
v___x_40_ = l_Rat_ofInt(v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableEqOffset(lean_object* v_a_41_, lean_object* v_b_42_){
_start:
{
uint8_t v___x_43_; 
v___x_43_ = lean_int_dec_eq(v_a_41_, v_b_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableEqOffset___boxed(lean_object* v_a_44_, lean_object* v_b_45_){
_start:
{
uint8_t v_res_46_; lean_object* v_r_47_; 
v_res_46_ = l_Std_Time_Week_instDecidableEqOffset(v_a_44_, v_b_45_);
lean_dec(v_b_45_);
lean_dec(v_a_44_);
v_r_47_ = lean_box(v_res_46_);
return v_r_47_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0(void){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Std_Time_Internal_instInhabitedUnitVal_default___redArg();
return v___x_48_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset___aux__1(void){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0, &l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0_once, _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0);
return v___x_49_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset(void){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0, &l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0_once, _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instAddOffset___aux__1(lean_object* v_u1_51_, lean_object* v_u2_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lean_int_add(v_u1_51_, v_u2_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instAddOffset___aux__1___boxed(lean_object* v_u1_54_, lean_object* v_u2_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Std_Time_Week_instAddOffset___aux__1(v_u1_54_, v_u2_55_);
lean_dec(v_u2_55_);
lean_dec(v_u1_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instSubOffset___aux__1(lean_object* v_u1_59_, lean_object* v_u2_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lean_int_sub(v_u1_59_, v_u2_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instSubOffset___aux__1___boxed(lean_object* v_u1_62_, lean_object* v_u2_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Std_Time_Week_instSubOffset___aux__1(v_u1_62_, v_u2_63_);
lean_dec(v_u2_63_);
lean_dec(v_u1_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instNegOffset___aux__1(lean_object* v_x_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lean_int_neg(v_x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instNegOffset___aux__1___boxed(lean_object* v_x_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Std_Time_Week_instNegOffset___aux__1(v_x_69_);
lean_dec(v_x_69_);
return v_res_70_;
}
}
static lean_object* _init_l_Std_Time_Week_instLEOffset(void){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lean_box(0);
return v___x_73_;
}
}
static lean_object* _init_l_Std_Time_Week_instLTOffset(void){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_box(0);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instToStringOffset___aux__1(lean_object* v_n_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Int_repr(v_n_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instToStringOffset___aux__1___boxed(lean_object* v_n_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Std_Time_Week_instToStringOffset___aux__1(v_n_77_);
lean_dec(v_n_77_);
return v_res_78_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLeOffset___aux__1(lean_object* v_x_81_, lean_object* v_y_82_){
_start:
{
uint8_t v___x_83_; 
v___x_83_ = lean_int_dec_le(v_x_81_, v_y_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLeOffset___aux__1___boxed(lean_object* v_x_84_, lean_object* v_y_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l_Std_Time_Week_instDecidableLeOffset___aux__1(v_x_84_, v_y_85_);
lean_dec(v_y_85_);
lean_dec(v_x_84_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLeOffset(lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
uint8_t v___x_90_; 
v___x_90_ = lean_int_dec_le(v___y_88_, v___y_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLeOffset___boxed(lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
uint8_t v_res_93_; lean_object* v_r_94_; 
v_res_93_ = l_Std_Time_Week_instDecidableLeOffset(v___y_91_, v___y_92_);
lean_dec(v___y_92_);
lean_dec(v___y_91_);
v_r_94_ = lean_box(v_res_93_);
return v_r_94_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLtOffset___aux__1(lean_object* v_x_95_, lean_object* v_y_96_){
_start:
{
uint8_t v___x_97_; 
v___x_97_ = lean_int_dec_lt(v_x_95_, v_y_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLtOffset___aux__1___boxed(lean_object* v_x_98_, lean_object* v_y_99_){
_start:
{
uint8_t v_res_100_; lean_object* v_r_101_; 
v_res_100_ = l_Std_Time_Week_instDecidableLtOffset___aux__1(v_x_98_, v_y_99_);
lean_dec(v_y_99_);
lean_dec(v_x_98_);
v_r_101_ = lean_box(v_res_100_);
return v_r_101_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLtOffset(lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
uint8_t v___x_104_; 
v___x_104_ = lean_int_dec_lt(v___y_102_, v___y_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLtOffset___boxed(lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
uint8_t v_res_107_; lean_object* v_r_108_; 
v_res_107_ = l_Std_Time_Week_instDecidableLtOffset(v___y_105_, v___y_106_);
lean_dec(v___y_106_);
lean_dec(v___y_105_);
v_r_108_ = lean_box(v_res_107_);
return v_r_108_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instOfNatOffset(lean_object* v_n_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_nat_to_int(v_n_109_);
return v___x_110_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instOrdOffset___aux__1(lean_object* v_x_111_, lean_object* v_y_112_){
_start:
{
uint8_t v___x_113_; 
v___x_113_ = lean_int_dec_lt(v_x_111_, v_y_112_);
if (v___x_113_ == 0)
{
uint8_t v___x_114_; 
v___x_114_ = lean_int_dec_eq(v_x_111_, v_y_112_);
if (v___x_114_ == 0)
{
uint8_t v___x_115_; 
v___x_115_ = 2;
return v___x_115_;
}
else
{
uint8_t v___x_116_; 
v___x_116_ = 1;
return v___x_116_;
}
}
else
{
uint8_t v___x_117_; 
v___x_117_ = 0;
return v___x_117_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instOrdOffset___aux__1___boxed(lean_object* v_x_118_, lean_object* v_y_119_){
_start:
{
uint8_t v_res_120_; lean_object* v_r_121_; 
v_res_120_ = l_Std_Time_Week_instOrdOffset___aux__1(v_x_118_, v_y_119_);
lean_dec(v_y_119_);
lean_dec(v_x_118_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instReprOrdinal___aux__1(lean_object* v_n_124_, lean_object* v_a_125_){
_start:
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = lean_obj_once(&l_Std_Time_Week_instReprOffset___aux__1___closed__0, &l_Std_Time_Week_instReprOffset___aux__1___closed__0_once, _init_l_Std_Time_Week_instReprOffset___aux__1___closed__0);
v___x_127_ = lean_int_dec_lt(v_n_124_, v___x_126_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = l_Int_repr(v_n_124_);
v___x_129_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
return v___x_129_;
}
else
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_130_ = l_Int_repr(v_n_124_);
v___x_131_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
v___x_132_ = l_Repr_addAppParen(v___x_131_, v_a_125_);
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instReprOrdinal___aux__1___boxed(lean_object* v_n_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Std_Time_Week_OfYear_instReprOrdinal___aux__1(v_n_133_, v_a_134_);
lean_dec(v_a_134_);
lean_dec(v_n_133_);
return v_res_135_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_OfYear_instDecidableEqOrdinal___aux__1(lean_object* v_a_137_, lean_object* v_b_138_){
_start:
{
uint8_t v___x_139_; 
v___x_139_ = lean_int_dec_eq(v_a_137_, v_b_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instDecidableEqOrdinal___aux__1___boxed(lean_object* v_a_140_, lean_object* v_b_141_){
_start:
{
uint8_t v_res_142_; lean_object* v_r_143_; 
v_res_142_ = l_Std_Time_Week_OfYear_instDecidableEqOrdinal___aux__1(v_a_140_, v_b_141_);
lean_dec(v_b_141_);
lean_dec(v_a_140_);
v_r_143_ = lean_box(v_res_142_);
return v_r_143_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_OfYear_instDecidableEqOrdinal(lean_object* v_a_144_, lean_object* v_b_145_){
_start:
{
uint8_t v___x_146_; 
v___x_146_ = lean_int_dec_eq(v_a_144_, v_b_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instDecidableEqOrdinal___boxed(lean_object* v_a_147_, lean_object* v_b_148_){
_start:
{
uint8_t v_res_149_; lean_object* v_r_150_; 
v_res_149_ = l_Std_Time_Week_OfYear_instDecidableEqOrdinal(v_a_147_, v_b_148_);
lean_dec(v_b_148_);
lean_dec(v_a_147_);
v_r_150_ = lean_box(v_res_149_);
return v_r_150_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_instLEOrdinal(void){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lean_box(0);
return v___x_151_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_instLTOrdinal(void){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = lean_box(0);
return v___x_152_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_unsigned_to_nat(1u);
v___x_154_ = lean_nat_to_int(v___x_153_);
return v___x_154_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__1(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_unsigned_to_nat(52u);
v___x_156_ = lean_nat_to_int(v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__2(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__1, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__1_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__1);
v___x_158_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_159_ = lean_int_add(v___x_158_, v___x_157_);
return v___x_159_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__3(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_161_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__2, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__2_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__2);
v___x_162_ = lean_int_sub(v___x_161_, v___x_160_);
return v___x_162_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v_range_165_; 
v___x_163_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_164_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__3);
v_range_165_ = lean_int_add(v___x_164_, v___x_163_);
return v_range_165_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1(lean_object* v_n_166_){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v_range_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_167_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_168_ = lean_nat_to_int(v_n_166_);
v_range_169_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4);
v___x_170_ = lean_int_sub(v___x_168_, v___x_167_);
lean_dec(v___x_168_);
v___x_171_ = lean_int_emod(v___x_170_, v_range_169_);
lean_dec(v___x_170_);
v___x_172_ = lean_int_add(v___x_171_, v_range_169_);
lean_dec(v___x_171_);
v___x_173_ = lean_int_emod(v___x_172_, v_range_169_);
lean_dec(v___x_172_);
v___x_174_ = lean_int_add(v___x_173_, v___x_167_);
lean_dec(v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instOfNatOrdinal(lean_object* v_n_175_){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v_range_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_176_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_177_ = lean_nat_to_int(v_n_175_);
v_range_178_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4);
v___x_179_ = lean_int_sub(v___x_177_, v___x_176_);
lean_dec(v___x_177_);
v___x_180_ = lean_int_emod(v___x_179_, v_range_178_);
lean_dec(v___x_179_);
v___x_181_ = lean_int_add(v___x_180_, v_range_178_);
lean_dec(v___x_180_);
v___x_182_ = lean_int_emod(v___x_181_, v_range_178_);
lean_dec(v___x_181_);
v___x_183_ = lean_int_add(v___x_182_, v___x_176_);
lean_dec(v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_OfYear_instDecidableLeOrdinal___aux__1(lean_object* v_x_184_, lean_object* v_y_185_){
_start:
{
uint8_t v___x_186_; 
v___x_186_ = lean_int_dec_le(v_x_184_, v_y_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instDecidableLeOrdinal___aux__1___boxed(lean_object* v_x_187_, lean_object* v_y_188_){
_start:
{
uint8_t v_res_189_; lean_object* v_r_190_; 
v_res_189_ = l_Std_Time_Week_OfYear_instDecidableLeOrdinal___aux__1(v_x_187_, v_y_188_);
lean_dec(v_y_188_);
lean_dec(v_x_187_);
v_r_190_ = lean_box(v_res_189_);
return v_r_190_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_OfYear_instDecidableLeOrdinal(lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
uint8_t v___x_193_; 
v___x_193_ = lean_int_dec_le(v___y_191_, v___y_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instDecidableLeOrdinal___boxed(lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
uint8_t v_res_196_; lean_object* v_r_197_; 
v_res_196_ = l_Std_Time_Week_OfYear_instDecidableLeOrdinal(v___y_194_, v___y_195_);
lean_dec(v___y_195_);
lean_dec(v___y_194_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_OfYear_instDecidableLtOrdinal___aux__1(lean_object* v_x_198_, lean_object* v_y_199_){
_start:
{
uint8_t v___x_200_; 
v___x_200_ = lean_int_dec_lt(v_x_198_, v_y_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instDecidableLtOrdinal___aux__1___boxed(lean_object* v_x_201_, lean_object* v_y_202_){
_start:
{
uint8_t v_res_203_; lean_object* v_r_204_; 
v_res_203_ = l_Std_Time_Week_OfYear_instDecidableLtOrdinal___aux__1(v_x_201_, v_y_202_);
lean_dec(v_y_202_);
lean_dec(v_x_201_);
v_r_204_ = lean_box(v_res_203_);
return v_r_204_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_OfYear_instDecidableLtOrdinal(lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
uint8_t v___x_207_; 
v___x_207_ = lean_int_dec_lt(v___y_205_, v___y_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instDecidableLtOrdinal___boxed(lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
uint8_t v_res_210_; lean_object* v_r_211_; 
v_res_210_ = l_Std_Time_Week_OfYear_instDecidableLtOrdinal(v___y_208_, v___y_209_);
lean_dec(v___y_209_);
lean_dec(v___y_208_);
v_r_211_ = lean_box(v_res_210_);
return v_r_211_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__0(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_213_ = lean_int_sub(v___x_212_, v___x_212_);
return v___x_213_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__1(void){
_start:
{
lean_object* v_range_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v_range_214_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4);
v___x_215_ = lean_obj_once(&l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__0, &l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__0);
v___x_216_ = lean_int_emod(v___x_215_, v_range_214_);
return v___x_216_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__2(void){
_start:
{
lean_object* v_range_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v_range_217_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4);
v___x_218_ = lean_obj_once(&l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__1, &l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__1_once, _init_l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__1);
v___x_219_ = lean_int_add(v___x_218_, v_range_217_);
return v___x_219_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__3(void){
_start:
{
lean_object* v_range_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v_range_220_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4);
v___x_221_ = lean_obj_once(&l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__2, &l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__2_once, _init_l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__2);
v___x_222_ = lean_int_emod(v___x_221_, v_range_220_);
return v___x_222_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__4(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_223_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_224_ = lean_obj_once(&l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__3, &l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__3);
v___x_225_ = lean_int_add(v___x_224_, v___x_223_);
return v___x_225_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_instInhabitedOrdinal(void){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = lean_obj_once(&l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__4, &l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__4_once, _init_l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__4);
return v___x_226_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_OfYear_instOrdOrdinal___aux__1(lean_object* v_x_227_, lean_object* v_y_228_){
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
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instOrdOrdinal___aux__1___boxed(lean_object* v_x_234_, lean_object* v_y_235_){
_start:
{
uint8_t v_res_236_; lean_object* v_r_237_; 
v_res_236_ = l_Std_Time_Week_OfYear_instOrdOrdinal___aux__1(v_x_234_, v_y_235_);
lean_dec(v_y_235_);
lean_dec(v_x_234_);
v_r_237_ = lean_box(v_res_236_);
return v_r_237_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_Ordinal_ofInt___redArg(lean_object* v_data_240_){
_start:
{
lean_inc(v_data_240_);
return v_data_240_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_Ordinal_ofInt___redArg___boxed(lean_object* v_data_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Std_Time_Week_OfYear_Ordinal_ofInt___redArg(v_data_241_);
lean_dec(v_data_241_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_Ordinal_ofInt(lean_object* v_data_243_, lean_object* v_h_244_){
_start:
{
lean_inc(v_data_243_);
return v_data_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_Ordinal_ofInt___boxed(lean_object* v_data_245_, lean_object* v_h_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Std_Time_Week_OfYear_Ordinal_ofInt(v_data_245_, v_h_246_);
lean_dec(v_data_245_);
return v_res_247_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__12(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = ((lean_object*)(l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__10));
v___x_275_ = l_Lean_mkAtom(v___x_274_);
return v___x_275_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__13(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_276_ = lean_obj_once(&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__12, &l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__12_once, _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__12);
v___x_277_ = ((lean_object*)(l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__5));
v___x_278_ = lean_array_push(v___x_277_, v___x_276_);
return v___x_278_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__17(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_289_ = ((lean_object*)(l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__16));
v___x_290_ = ((lean_object*)(l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__5));
v___x_291_ = lean_array_push(v___x_290_, v___x_289_);
return v___x_291_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__18(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_292_ = lean_obj_once(&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__17, &l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__17_once, _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__17);
v___x_293_ = ((lean_object*)(l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__15));
v___x_294_ = lean_box(2);
v___x_295_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v___x_293_);
lean_ctor_set(v___x_295_, 2, v___x_292_);
return v___x_295_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__19(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = lean_obj_once(&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__18, &l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__18_once, _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__18);
v___x_297_ = lean_obj_once(&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__13, &l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__13_once, _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__13);
v___x_298_ = lean_array_push(v___x_297_, v___x_296_);
return v___x_298_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__20(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_299_ = lean_obj_once(&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__19, &l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__19_once, _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__19);
v___x_300_ = ((lean_object*)(l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__11));
v___x_301_ = lean_box(2);
v___x_302_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set(v___x_302_, 1, v___x_300_);
lean_ctor_set(v___x_302_, 2, v___x_299_);
return v___x_302_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__21(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_303_ = lean_obj_once(&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__20, &l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__20_once, _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__20);
v___x_304_ = ((lean_object*)(l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__5));
v___x_305_ = lean_array_push(v___x_304_, v___x_303_);
return v___x_305_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__22(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_306_ = lean_obj_once(&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__21, &l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__21_once, _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__21);
v___x_307_ = ((lean_object*)(l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__9));
v___x_308_ = lean_box(2);
v___x_309_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v___x_307_);
lean_ctor_set(v___x_309_, 2, v___x_306_);
return v___x_309_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__23(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_310_ = lean_obj_once(&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__22, &l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__22_once, _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__22);
v___x_311_ = ((lean_object*)(l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__5));
v___x_312_ = lean_array_push(v___x_311_, v___x_310_);
return v___x_312_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__24(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_313_ = lean_obj_once(&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__23, &l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__23_once, _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__23);
v___x_314_ = ((lean_object*)(l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__7));
v___x_315_ = lean_box(2);
v___x_316_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___x_314_);
lean_ctor_set(v___x_316_, 2, v___x_313_);
return v___x_316_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__25(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = lean_obj_once(&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__24, &l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__24_once, _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__24);
v___x_318_ = ((lean_object*)(l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__5));
v___x_319_ = lean_array_push(v___x_318_, v___x_317_);
return v___x_319_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__26(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_320_ = lean_obj_once(&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__25, &l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__25_once, _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__25);
v___x_321_ = ((lean_object*)(l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__4));
v___x_322_ = lean_box(2);
v___x_323_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v___x_321_);
lean_ctor_set(v___x_323_, 2, v___x_320_);
return v___x_323_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1(void){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = lean_obj_once(&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__26, &l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__26_once, _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__26);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___redArg(lean_object* v_data_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = lean_nat_to_int(v_data_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat(lean_object* v_data_327_, lean_object* v_h_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = lean_nat_to_int(v_data_327_);
return v___x_329_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_Ordinal_ofFin___closed__0(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_unsigned_to_nat(1u);
v___x_331_ = lean_nat_to_int(v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_Ordinal_ofFin(lean_object* v_data_332_){
_start:
{
lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_333_ = lean_unsigned_to_nat(1u);
v___x_334_ = lean_nat_dec_le(v___x_333_, v_data_332_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; 
lean_dec(v_data_332_);
v___x_335_ = lean_obj_once(&l_Std_Time_Week_OfYear_Ordinal_ofFin___closed__0, &l_Std_Time_Week_OfYear_Ordinal_ofFin___closed__0_once, _init_l_Std_Time_Week_OfYear_Ordinal_ofFin___closed__0);
return v___x_335_;
}
else
{
lean_object* v___x_336_; 
v___x_336_ = lean_nat_to_int(v_data_332_);
return v___x_336_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_Ordinal_toOffset(lean_object* v_ordinal_337_){
_start:
{
lean_inc(v_ordinal_337_);
return v_ordinal_337_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_Ordinal_toOffset___boxed(lean_object* v_ordinal_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Std_Time_Week_OfYear_Ordinal_toOffset(v_ordinal_338_);
lean_dec(v_ordinal_338_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Aligned_instReprOrdinal___aux__1(lean_object* v_n_340_, lean_object* v_a_341_){
_start:
{
lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_342_ = lean_obj_once(&l_Std_Time_Week_instReprOffset___aux__1___closed__0, &l_Std_Time_Week_instReprOffset___aux__1___closed__0_once, _init_l_Std_Time_Week_instReprOffset___aux__1___closed__0);
v___x_343_ = lean_int_dec_lt(v_n_340_, v___x_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = l_Int_repr(v_n_340_);
v___x_345_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
return v___x_345_;
}
else
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_346_ = l_Int_repr(v_n_340_);
v___x_347_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
v___x_348_ = l_Repr_addAppParen(v___x_347_, v_a_341_);
return v___x_348_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Aligned_instReprOrdinal___aux__1___boxed(lean_object* v_n_349_, lean_object* v_a_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Std_Time_Week_Aligned_instReprOrdinal___aux__1(v_n_349_, v_a_350_);
lean_dec(v_a_350_);
lean_dec(v_n_349_);
return v_res_351_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_Aligned_instDecidableEqOrdinal___aux__1(lean_object* v_a_353_, lean_object* v_b_354_){
_start:
{
uint8_t v___x_355_; 
v___x_355_ = lean_int_dec_eq(v_a_353_, v_b_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Aligned_instDecidableEqOrdinal___aux__1___boxed(lean_object* v_a_356_, lean_object* v_b_357_){
_start:
{
uint8_t v_res_358_; lean_object* v_r_359_; 
v_res_358_ = l_Std_Time_Week_Aligned_instDecidableEqOrdinal___aux__1(v_a_356_, v_b_357_);
lean_dec(v_b_357_);
lean_dec(v_a_356_);
v_r_359_ = lean_box(v_res_358_);
return v_r_359_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_Aligned_instDecidableEqOrdinal(lean_object* v_a_360_, lean_object* v_b_361_){
_start:
{
uint8_t v___x_362_; 
v___x_362_ = lean_int_dec_eq(v_a_360_, v_b_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Aligned_instDecidableEqOrdinal___boxed(lean_object* v_a_363_, lean_object* v_b_364_){
_start:
{
uint8_t v_res_365_; lean_object* v_r_366_; 
v_res_365_ = l_Std_Time_Week_Aligned_instDecidableEqOrdinal(v_a_363_, v_b_364_);
lean_dec(v_b_364_);
lean_dec(v_a_363_);
v_r_366_ = lean_box(v_res_365_);
return v_r_366_;
}
}
static lean_object* _init_l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__0(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = lean_unsigned_to_nat(4u);
v___x_368_ = lean_nat_to_int(v___x_367_);
return v___x_368_;
}
}
static lean_object* _init_l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__1(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_369_ = lean_obj_once(&l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__0);
v___x_370_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_371_ = lean_int_add(v___x_370_, v___x_369_);
return v___x_371_;
}
}
static lean_object* _init_l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__2(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_372_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_373_ = lean_obj_once(&l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__1, &l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__1_once, _init_l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__1);
v___x_374_ = lean_int_sub(v___x_373_, v___x_372_);
return v___x_374_;
}
}
static lean_object* _init_l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v_range_377_; 
v___x_375_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_376_ = lean_obj_once(&l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__2, &l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__2_once, _init_l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__2);
v_range_377_ = lean_int_add(v___x_376_, v___x_375_);
return v_range_377_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1(lean_object* v_n_378_){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v_range_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_379_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_380_ = lean_nat_to_int(v_n_378_);
v_range_381_ = lean_obj_once(&l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3);
v___x_382_ = lean_int_sub(v___x_380_, v___x_379_);
lean_dec(v___x_380_);
v___x_383_ = lean_int_emod(v___x_382_, v_range_381_);
lean_dec(v___x_382_);
v___x_384_ = lean_int_add(v___x_383_, v_range_381_);
lean_dec(v___x_383_);
v___x_385_ = lean_int_emod(v___x_384_, v_range_381_);
lean_dec(v___x_384_);
v___x_386_ = lean_int_add(v___x_385_, v___x_379_);
lean_dec(v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Aligned_instOfNatOrdinal(lean_object* v_n_387_){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v_range_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_388_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_389_ = lean_nat_to_int(v_n_387_);
v_range_390_ = lean_obj_once(&l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3);
v___x_391_ = lean_int_sub(v___x_389_, v___x_388_);
lean_dec(v___x_389_);
v___x_392_ = lean_int_emod(v___x_391_, v_range_390_);
lean_dec(v___x_391_);
v___x_393_ = lean_int_add(v___x_392_, v_range_390_);
lean_dec(v___x_392_);
v___x_394_ = lean_int_emod(v___x_393_, v_range_390_);
lean_dec(v___x_393_);
v___x_395_ = lean_int_add(v___x_394_, v___x_388_);
lean_dec(v___x_394_);
return v___x_395_;
}
}
static lean_object* _init_l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__0(void){
_start:
{
lean_object* v_range_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_range_396_ = lean_obj_once(&l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3);
v___x_397_ = lean_obj_once(&l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__0, &l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__0);
v___x_398_ = lean_int_emod(v___x_397_, v_range_396_);
return v___x_398_;
}
}
static lean_object* _init_l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__1(void){
_start:
{
lean_object* v_range_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v_range_399_ = lean_obj_once(&l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3);
v___x_400_ = lean_obj_once(&l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__0, &l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__0);
v___x_401_ = lean_int_add(v___x_400_, v_range_399_);
return v___x_401_;
}
}
static lean_object* _init_l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__2(void){
_start:
{
lean_object* v_range_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v_range_402_ = lean_obj_once(&l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3);
v___x_403_ = lean_obj_once(&l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__1, &l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__1_once, _init_l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__1);
v___x_404_ = lean_int_emod(v___x_403_, v_range_402_);
return v___x_404_;
}
}
static lean_object* _init_l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__3(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_406_ = lean_obj_once(&l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__2, &l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__2_once, _init_l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__2);
v___x_407_ = lean_int_add(v___x_406_, v___x_405_);
return v___x_407_;
}
}
static lean_object* _init_l_Std_Time_Week_Aligned_instInhabitedOrdinal(void){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = lean_obj_once(&l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__3, &l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__3);
return v___x_408_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_Aligned_instOrdOrdinal___aux__1(lean_object* v_x_409_, lean_object* v_y_410_){
_start:
{
uint8_t v___x_411_; 
v___x_411_ = lean_int_dec_lt(v_x_409_, v_y_410_);
if (v___x_411_ == 0)
{
uint8_t v___x_412_; 
v___x_412_ = lean_int_dec_eq(v_x_409_, v_y_410_);
if (v___x_412_ == 0)
{
uint8_t v___x_413_; 
v___x_413_ = 2;
return v___x_413_;
}
else
{
uint8_t v___x_414_; 
v___x_414_ = 1;
return v___x_414_;
}
}
else
{
uint8_t v___x_415_; 
v___x_415_ = 0;
return v___x_415_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Aligned_instOrdOrdinal___aux__1___boxed(lean_object* v_x_416_, lean_object* v_y_417_){
_start:
{
uint8_t v_res_418_; lean_object* v_r_419_; 
v_res_418_ = l_Std_Time_Week_Aligned_instOrdOrdinal___aux__1(v_x_416_, v_y_417_);
lean_dec(v_y_417_);
lean_dec(v_x_416_);
v_r_419_ = lean_box(v_res_418_);
return v_r_419_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instReprOrdinal___aux__1(lean_object* v_n_422_, lean_object* v_a_423_){
_start:
{
lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_424_ = lean_obj_once(&l_Std_Time_Week_instReprOffset___aux__1___closed__0, &l_Std_Time_Week_instReprOffset___aux__1___closed__0_once, _init_l_Std_Time_Week_instReprOffset___aux__1___closed__0);
v___x_425_ = lean_int_dec_lt(v_n_422_, v___x_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = l_Int_repr(v_n_422_);
v___x_427_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
return v___x_427_;
}
else
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_428_ = l_Int_repr(v_n_422_);
v___x_429_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
v___x_430_ = l_Repr_addAppParen(v___x_429_, v_a_423_);
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instReprOrdinal___aux__1___boxed(lean_object* v_n_431_, lean_object* v_a_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_Time_Week_instReprOrdinal___aux__1(v_n_431_, v_a_432_);
lean_dec(v_a_432_);
lean_dec(v_n_431_);
return v_res_433_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableEqOrdinal___aux__1(lean_object* v_a_435_, lean_object* v_b_436_){
_start:
{
uint8_t v___x_437_; 
v___x_437_ = lean_int_dec_eq(v_a_435_, v_b_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableEqOrdinal___aux__1___boxed(lean_object* v_a_438_, lean_object* v_b_439_){
_start:
{
uint8_t v_res_440_; lean_object* v_r_441_; 
v_res_440_ = l_Std_Time_Week_instDecidableEqOrdinal___aux__1(v_a_438_, v_b_439_);
lean_dec(v_b_439_);
lean_dec(v_a_438_);
v_r_441_ = lean_box(v_res_440_);
return v_r_441_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableEqOrdinal(lean_object* v_a_442_, lean_object* v_b_443_){
_start:
{
uint8_t v___x_444_; 
v___x_444_ = lean_int_dec_eq(v_a_442_, v_b_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableEqOrdinal___boxed(lean_object* v_a_445_, lean_object* v_b_446_){
_start:
{
uint8_t v_res_447_; lean_object* v_r_448_; 
v_res_447_ = l_Std_Time_Week_instDecidableEqOrdinal(v_a_445_, v_b_446_);
lean_dec(v_b_446_);
lean_dec(v_a_445_);
v_r_448_ = lean_box(v_res_447_);
return v_r_448_;
}
}
static lean_object* _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_unsigned_to_nat(5u);
v___x_450_ = lean_nat_to_int(v___x_449_);
return v___x_450_;
}
}
static lean_object* _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__1(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_451_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0);
v___x_452_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_453_ = lean_int_add(v___x_452_, v___x_451_);
return v___x_453_;
}
}
static lean_object* _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__2(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_454_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_455_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__1, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__1_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__1);
v___x_456_ = lean_int_sub(v___x_455_, v___x_454_);
return v___x_456_;
}
}
static lean_object* _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v_range_459_; 
v___x_457_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_458_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__2, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__2_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__2);
v_range_459_ = lean_int_add(v___x_458_, v___x_457_);
return v_range_459_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instOfNatOrdinal___aux__1(lean_object* v_n_460_){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v_range_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_461_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_462_ = lean_nat_to_int(v_n_460_);
v_range_463_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3);
v___x_464_ = lean_int_sub(v___x_462_, v___x_461_);
lean_dec(v___x_462_);
v___x_465_ = lean_int_emod(v___x_464_, v_range_463_);
lean_dec(v___x_464_);
v___x_466_ = lean_int_add(v___x_465_, v_range_463_);
lean_dec(v___x_465_);
v___x_467_ = lean_int_emod(v___x_466_, v_range_463_);
lean_dec(v___x_466_);
v___x_468_ = lean_int_add(v___x_467_, v___x_461_);
lean_dec(v___x_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instOfNatOrdinal(lean_object* v_n_469_){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v_range_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_470_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_471_ = lean_nat_to_int(v_n_469_);
v_range_472_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3);
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
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal___closed__0(void){
_start:
{
lean_object* v_range_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v_range_478_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3);
v___x_479_ = lean_obj_once(&l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__0, &l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__0);
v___x_480_ = lean_int_emod(v___x_479_, v_range_478_);
return v___x_480_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal___closed__1(void){
_start:
{
lean_object* v_range_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v_range_481_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3);
v___x_482_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__0, &l_Std_Time_Week_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__0);
v___x_483_ = lean_int_add(v___x_482_, v_range_481_);
return v___x_483_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal___closed__2(void){
_start:
{
lean_object* v_range_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_range_484_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3);
v___x_485_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__1, &l_Std_Time_Week_instInhabitedOrdinal___closed__1_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__1);
v___x_486_ = lean_int_emod(v___x_485_, v_range_484_);
return v___x_486_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal___closed__3(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_488_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__2, &l_Std_Time_Week_instInhabitedOrdinal___closed__2_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__2);
v___x_489_ = lean_int_add(v___x_488_, v___x_487_);
return v___x_489_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal(void){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__3, &l_Std_Time_Week_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__3);
return v___x_490_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instOrdOrdinal___aux__1(lean_object* v_x_491_, lean_object* v_y_492_){
_start:
{
uint8_t v___x_493_; 
v___x_493_ = lean_int_dec_lt(v_x_491_, v_y_492_);
if (v___x_493_ == 0)
{
uint8_t v___x_494_; 
v___x_494_ = lean_int_dec_eq(v_x_491_, v_y_492_);
if (v___x_494_ == 0)
{
uint8_t v___x_495_; 
v___x_495_ = 2;
return v___x_495_;
}
else
{
uint8_t v___x_496_; 
v___x_496_ = 1;
return v___x_496_;
}
}
else
{
uint8_t v___x_497_; 
v___x_497_ = 0;
return v___x_497_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instOrdOrdinal___aux__1___boxed(lean_object* v_x_498_, lean_object* v_y_499_){
_start:
{
uint8_t v_res_500_; lean_object* v_r_501_; 
v_res_500_ = l_Std_Time_Week_instOrdOrdinal___aux__1(v_x_498_, v_y_499_);
lean_dec(v_y_499_);
lean_dec(v_x_498_);
v_r_501_ = lean_box(v_res_500_);
return v_r_501_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofNat(lean_object* v_data_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = lean_nat_to_int(v_data_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofInt(lean_object* v_data_506_){
_start:
{
lean_inc(v_data_506_);
return v_data_506_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofInt___boxed(lean_object* v_data_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Std_Time_Week_Offset_ofInt(v_data_507_);
lean_dec(v_data_507_);
return v_res_508_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = lean_unsigned_to_nat(604800000u);
v___x_510_ = lean_nat_to_int(v___x_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toMilliseconds(lean_object* v_weeks_511_){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_obj_once(&l_Std_Time_Week_Offset_toMilliseconds___closed__0, &l_Std_Time_Week_Offset_toMilliseconds___closed__0_once, _init_l_Std_Time_Week_Offset_toMilliseconds___closed__0);
v___x_513_ = lean_int_mul(v_weeks_511_, v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toMilliseconds___boxed(lean_object* v_weeks_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Std_Time_Week_Offset_toMilliseconds(v_weeks_514_);
lean_dec(v_weeks_514_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofMilliseconds(lean_object* v_millis_516_){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_obj_once(&l_Std_Time_Week_Offset_toMilliseconds___closed__0, &l_Std_Time_Week_Offset_toMilliseconds___closed__0_once, _init_l_Std_Time_Week_Offset_toMilliseconds___closed__0);
v___x_518_ = lean_int_ediv(v_millis_516_, v___x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofMilliseconds___boxed(lean_object* v_millis_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Std_Time_Week_Offset_ofMilliseconds(v_millis_519_);
lean_dec(v_millis_519_);
return v_res_520_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toNanoseconds___closed__0(void){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_cstr_to_nat("604800000000000");
v___x_522_ = lean_nat_to_int(v___x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toNanoseconds(lean_object* v_weeks_523_){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_obj_once(&l_Std_Time_Week_Offset_toNanoseconds___closed__0, &l_Std_Time_Week_Offset_toNanoseconds___closed__0_once, _init_l_Std_Time_Week_Offset_toNanoseconds___closed__0);
v___x_525_ = lean_int_mul(v_weeks_523_, v___x_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toNanoseconds___boxed(lean_object* v_weeks_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Std_Time_Week_Offset_toNanoseconds(v_weeks_526_);
lean_dec(v_weeks_526_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofNanoseconds(lean_object* v_nanos_528_){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_obj_once(&l_Std_Time_Week_Offset_toNanoseconds___closed__0, &l_Std_Time_Week_Offset_toNanoseconds___closed__0_once, _init_l_Std_Time_Week_Offset_toNanoseconds___closed__0);
v___x_530_ = lean_int_ediv(v_nanos_528_, v___x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofNanoseconds___boxed(lean_object* v_nanos_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Std_Time_Week_Offset_ofNanoseconds(v_nanos_531_);
lean_dec(v_nanos_531_);
return v_res_532_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toSeconds___closed__0(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_unsigned_to_nat(604800u);
v___x_534_ = lean_nat_to_int(v___x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toSeconds(lean_object* v_weeks_535_){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = lean_obj_once(&l_Std_Time_Week_Offset_toSeconds___closed__0, &l_Std_Time_Week_Offset_toSeconds___closed__0_once, _init_l_Std_Time_Week_Offset_toSeconds___closed__0);
v___x_537_ = lean_int_mul(v_weeks_535_, v___x_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toSeconds___boxed(lean_object* v_weeks_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Std_Time_Week_Offset_toSeconds(v_weeks_538_);
lean_dec(v_weeks_538_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofSeconds(lean_object* v_secs_540_){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_obj_once(&l_Std_Time_Week_Offset_toSeconds___closed__0, &l_Std_Time_Week_Offset_toSeconds___closed__0_once, _init_l_Std_Time_Week_Offset_toSeconds___closed__0);
v___x_542_ = lean_int_ediv(v_secs_540_, v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofSeconds___boxed(lean_object* v_secs_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Std_Time_Week_Offset_ofSeconds(v_secs_543_);
lean_dec(v_secs_543_);
return v_res_544_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toMinutes___closed__0(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = lean_unsigned_to_nat(10080u);
v___x_546_ = lean_nat_to_int(v___x_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toMinutes(lean_object* v_weeks_547_){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_obj_once(&l_Std_Time_Week_Offset_toMinutes___closed__0, &l_Std_Time_Week_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Week_Offset_toMinutes___closed__0);
v___x_549_ = lean_int_mul(v_weeks_547_, v___x_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toMinutes___boxed(lean_object* v_weeks_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Std_Time_Week_Offset_toMinutes(v_weeks_550_);
lean_dec(v_weeks_550_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofMinutes(lean_object* v_minutes_552_){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = lean_obj_once(&l_Std_Time_Week_Offset_toMinutes___closed__0, &l_Std_Time_Week_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Week_Offset_toMinutes___closed__0);
v___x_554_ = lean_int_ediv(v_minutes_552_, v___x_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofMinutes___boxed(lean_object* v_minutes_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Std_Time_Week_Offset_ofMinutes(v_minutes_555_);
lean_dec(v_minutes_555_);
return v_res_556_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toHours___closed__0(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_unsigned_to_nat(168u);
v___x_558_ = lean_nat_to_int(v___x_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toHours(lean_object* v_weeks_559_){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = lean_obj_once(&l_Std_Time_Week_Offset_toHours___closed__0, &l_Std_Time_Week_Offset_toHours___closed__0_once, _init_l_Std_Time_Week_Offset_toHours___closed__0);
v___x_561_ = lean_int_mul(v_weeks_559_, v___x_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toHours___boxed(lean_object* v_weeks_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Std_Time_Week_Offset_toHours(v_weeks_562_);
lean_dec(v_weeks_562_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofHours(lean_object* v_hours_564_){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_obj_once(&l_Std_Time_Week_Offset_toHours___closed__0, &l_Std_Time_Week_Offset_toHours___closed__0_once, _init_l_Std_Time_Week_Offset_toHours___closed__0);
v___x_566_ = lean_int_ediv(v_hours_564_, v___x_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofHours___boxed(lean_object* v_hours_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Std_Time_Week_Offset_ofHours(v_hours_567_);
lean_dec(v_hours_567_);
return v_res_568_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toDays___closed__0(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = lean_unsigned_to_nat(7u);
v___x_570_ = lean_nat_to_int(v___x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toDays(lean_object* v_weeks_571_){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = lean_obj_once(&l_Std_Time_Week_Offset_toDays___closed__0, &l_Std_Time_Week_Offset_toDays___closed__0_once, _init_l_Std_Time_Week_Offset_toDays___closed__0);
v___x_573_ = lean_int_mul(v_weeks_571_, v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toDays___boxed(lean_object* v_weeks_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Std_Time_Week_Offset_toDays(v_weeks_574_);
lean_dec(v_weeks_574_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofDays(lean_object* v_days_576_){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = lean_obj_once(&l_Std_Time_Week_Offset_toDays___closed__0, &l_Std_Time_Week_Offset_toDays___closed__0_once, _init_l_Std_Time_Week_Offset_toDays___closed__0);
v___x_578_ = lean_int_ediv(v_days_576_, v___x_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofDays___boxed(lean_object* v_days_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Std_Time_Week_Offset_ofDays(v_days_579_);
lean_dec(v_days_579_);
return v_res_580_;
}
}
lean_object* runtime_initialize_Std_Time_Date_Unit_Day(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Date_Unit_Week(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Time_Date_Unit_Day(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_Week_instInhabitedOffset___aux__1 = _init_l_Std_Time_Week_instInhabitedOffset___aux__1();
lean_mark_persistent(l_Std_Time_Week_instInhabitedOffset___aux__1);
l_Std_Time_Week_instInhabitedOffset = _init_l_Std_Time_Week_instInhabitedOffset();
lean_mark_persistent(l_Std_Time_Week_instInhabitedOffset);
l_Std_Time_Week_instLEOffset = _init_l_Std_Time_Week_instLEOffset();
lean_mark_persistent(l_Std_Time_Week_instLEOffset);
l_Std_Time_Week_instLTOffset = _init_l_Std_Time_Week_instLTOffset();
lean_mark_persistent(l_Std_Time_Week_instLTOffset);
l_Std_Time_Week_OfYear_instLEOrdinal = _init_l_Std_Time_Week_OfYear_instLEOrdinal();
lean_mark_persistent(l_Std_Time_Week_OfYear_instLEOrdinal);
l_Std_Time_Week_OfYear_instLTOrdinal = _init_l_Std_Time_Week_OfYear_instLTOrdinal();
lean_mark_persistent(l_Std_Time_Week_OfYear_instLTOrdinal);
l_Std_Time_Week_OfYear_instInhabitedOrdinal = _init_l_Std_Time_Week_OfYear_instInhabitedOrdinal();
lean_mark_persistent(l_Std_Time_Week_OfYear_instInhabitedOrdinal);
l_Std_Time_Week_Aligned_instInhabitedOrdinal = _init_l_Std_Time_Week_Aligned_instInhabitedOrdinal();
lean_mark_persistent(l_Std_Time_Week_Aligned_instInhabitedOrdinal);
l_Std_Time_Week_instInhabitedOrdinal = _init_l_Std_Time_Week_instInhabitedOrdinal();
lean_mark_persistent(l_Std_Time_Week_instInhabitedOrdinal);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Date_Unit_Week(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1 = _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1();
lean_mark_persistent(l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1);
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
