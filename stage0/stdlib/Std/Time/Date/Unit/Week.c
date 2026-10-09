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
uint8_t l_Std_Time_Week_instDecidableEqOffset___aux__1(lean_object* v_a_29_, lean_object* v_b_30_){
_start:
{
uint8_t v___x_31_; 
v___x_31_ = lean_int_dec_eq(v_a_29_, v_b_30_);
return v___x_31_;
}
}
LEAN_EXPORT void l_Std_Time_Week_instDecidableEqOffset___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_29_ = stack[0].m_obj;
lean_object* v_b_30_ = stack[1].m_obj;
uint8_t v_res_32_;
v_res_32_ = l_Std_Time_Week_instDecidableEqOffset___aux__1(v_a_29_, v_b_30_);
stack->m_num = v_res_32_;
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableEqOffset___aux__1___boxed(lean_object* v_a_33_, lean_object* v_b_34_){
_start:
{
uint8_t v_res_35_; lean_object* v_r_36_; 
v_res_35_ = l_Std_Time_Week_instDecidableEqOffset___aux__1(v_a_33_, v_b_34_);
lean_dec(v_b_34_);
lean_dec(v_a_33_);
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Week_instDecidableEqOffset___aux__1_spec__0_spec__0(lean_object* v_a_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_nat_to_int(v_a_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Week_instDecidableEqOffset___aux__1_spec__0(lean_object* v_a_39_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = lean_nat_to_int(v_a_39_);
v___x_41_ = l_Rat_ofInt(v___x_40_);
return v___x_41_;
}
}
uint8_t l_Std_Time_Week_instDecidableEqOffset(lean_object* v_a_42_, lean_object* v_b_43_){
_start:
{
uint8_t v___x_44_; 
v___x_44_ = lean_int_dec_eq(v_a_42_, v_b_43_);
return v___x_44_;
}
}
LEAN_EXPORT void l_Std_Time_Week_instDecidableEqOffset_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_42_ = stack[0].m_obj;
lean_object* v_b_43_ = stack[1].m_obj;
uint8_t v_res_45_;
v_res_45_ = l_Std_Time_Week_instDecidableEqOffset(v_a_42_, v_b_43_);
stack->m_num = v_res_45_;
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableEqOffset___boxed(lean_object* v_a_46_, lean_object* v_b_47_){
_start:
{
uint8_t v_res_48_; lean_object* v_r_49_; 
v_res_48_ = l_Std_Time_Week_instDecidableEqOffset(v_a_46_, v_b_47_);
lean_dec(v_b_47_);
lean_dec(v_a_46_);
v_r_49_ = lean_box(v_res_48_);
return v_r_49_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0(void){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Std_Time_Internal_instInhabitedUnitVal_default___redArg();
return v___x_50_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset___aux__1(void){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0, &l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0_once, _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0);
return v___x_51_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset(void){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0, &l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0_once, _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instAddOffset___aux__1(lean_object* v_u1_53_, lean_object* v_u2_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lean_int_add(v_u1_53_, v_u2_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instAddOffset___aux__1___boxed(lean_object* v_u1_56_, lean_object* v_u2_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Std_Time_Week_instAddOffset___aux__1(v_u1_56_, v_u2_57_);
lean_dec(v_u2_57_);
lean_dec(v_u1_56_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instSubOffset___aux__1(lean_object* v_u1_61_, lean_object* v_u2_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lean_int_sub(v_u1_61_, v_u2_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instSubOffset___aux__1___boxed(lean_object* v_u1_64_, lean_object* v_u2_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Std_Time_Week_instSubOffset___aux__1(v_u1_64_, v_u2_65_);
lean_dec(v_u2_65_);
lean_dec(v_u1_64_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instNegOffset___aux__1(lean_object* v_x_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lean_int_neg(v_x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instNegOffset___aux__1___boxed(lean_object* v_x_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Std_Time_Week_instNegOffset___aux__1(v_x_71_);
lean_dec(v_x_71_);
return v_res_72_;
}
}
static lean_object* _init_l_Std_Time_Week_instLEOffset(void){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_box(0);
return v___x_75_;
}
}
static lean_object* _init_l_Std_Time_Week_instLTOffset(void){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_box(0);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instToStringOffset___aux__1(lean_object* v_n_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Int_repr(v_n_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instToStringOffset___aux__1___boxed(lean_object* v_n_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Std_Time_Week_instToStringOffset___aux__1(v_n_79_);
lean_dec(v_n_79_);
return v_res_80_;
}
}
uint8_t l_Std_Time_Week_instDecidableLeOffset___aux__1(lean_object* v_x_83_, lean_object* v_y_84_){
_start:
{
uint8_t v___x_85_; 
v___x_85_ = lean_int_dec_le(v_x_83_, v_y_84_);
return v___x_85_;
}
}
LEAN_EXPORT void l_Std_Time_Week_instDecidableLeOffset___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_83_ = stack[0].m_obj;
lean_object* v_y_84_ = stack[1].m_obj;
uint8_t v_res_86_;
v_res_86_ = l_Std_Time_Week_instDecidableLeOffset___aux__1(v_x_83_, v_y_84_);
stack->m_num = v_res_86_;
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLeOffset___aux__1___boxed(lean_object* v_x_87_, lean_object* v_y_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_Std_Time_Week_instDecidableLeOffset___aux__1(v_x_87_, v_y_88_);
lean_dec(v_y_88_);
lean_dec(v_x_87_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
uint8_t l_Std_Time_Week_instDecidableLeOffset(lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
uint8_t v___x_93_; 
v___x_93_ = lean_int_dec_le(v___y_91_, v___y_92_);
return v___x_93_;
}
}
LEAN_EXPORT void l_Std_Time_Week_instDecidableLeOffset_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_91_ = stack[0].m_obj;
lean_object* v___y_92_ = stack[1].m_obj;
uint8_t v_res_94_;
v_res_94_ = l_Std_Time_Week_instDecidableLeOffset(v___y_91_, v___y_92_);
stack->m_num = v_res_94_;
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLeOffset___boxed(lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
uint8_t v_res_97_; lean_object* v_r_98_; 
v_res_97_ = l_Std_Time_Week_instDecidableLeOffset(v___y_95_, v___y_96_);
lean_dec(v___y_96_);
lean_dec(v___y_95_);
v_r_98_ = lean_box(v_res_97_);
return v_r_98_;
}
}
uint8_t l_Std_Time_Week_instDecidableLtOffset___aux__1(lean_object* v_x_99_, lean_object* v_y_100_){
_start:
{
uint8_t v___x_101_; 
v___x_101_ = lean_int_dec_lt(v_x_99_, v_y_100_);
return v___x_101_;
}
}
LEAN_EXPORT void l_Std_Time_Week_instDecidableLtOffset___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_99_ = stack[0].m_obj;
lean_object* v_y_100_ = stack[1].m_obj;
uint8_t v_res_102_;
v_res_102_ = l_Std_Time_Week_instDecidableLtOffset___aux__1(v_x_99_, v_y_100_);
stack->m_num = v_res_102_;
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLtOffset___aux__1___boxed(lean_object* v_x_103_, lean_object* v_y_104_){
_start:
{
uint8_t v_res_105_; lean_object* v_r_106_; 
v_res_105_ = l_Std_Time_Week_instDecidableLtOffset___aux__1(v_x_103_, v_y_104_);
lean_dec(v_y_104_);
lean_dec(v_x_103_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
uint8_t l_Std_Time_Week_instDecidableLtOffset(lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
uint8_t v___x_109_; 
v___x_109_ = lean_int_dec_lt(v___y_107_, v___y_108_);
return v___x_109_;
}
}
LEAN_EXPORT void l_Std_Time_Week_instDecidableLtOffset_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_107_ = stack[0].m_obj;
lean_object* v___y_108_ = stack[1].m_obj;
uint8_t v_res_110_;
v_res_110_ = l_Std_Time_Week_instDecidableLtOffset(v___y_107_, v___y_108_);
stack->m_num = v_res_110_;
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLtOffset___boxed(lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
uint8_t v_res_113_; lean_object* v_r_114_; 
v_res_113_ = l_Std_Time_Week_instDecidableLtOffset(v___y_111_, v___y_112_);
lean_dec(v___y_112_);
lean_dec(v___y_111_);
v_r_114_ = lean_box(v_res_113_);
return v_r_114_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instOfNatOffset(lean_object* v_n_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_nat_to_int(v_n_115_);
return v___x_116_;
}
}
uint8_t l_Std_Time_Week_instOrdOffset___aux__1(lean_object* v_x_117_, lean_object* v_y_118_){
_start:
{
uint8_t v___x_119_; 
v___x_119_ = lean_int_dec_lt(v_x_117_, v_y_118_);
if (v___x_119_ == 0)
{
uint8_t v___x_120_; 
v___x_120_ = lean_int_dec_eq(v_x_117_, v_y_118_);
if (v___x_120_ == 0)
{
uint8_t v___x_121_; 
v___x_121_ = 2;
return v___x_121_;
}
else
{
uint8_t v___x_122_; 
v___x_122_ = 1;
return v___x_122_;
}
}
else
{
uint8_t v___x_123_; 
v___x_123_ = 0;
return v___x_123_;
}
}
}
LEAN_EXPORT void l_Std_Time_Week_instOrdOffset___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_117_ = stack[0].m_obj;
lean_object* v_y_118_ = stack[1].m_obj;
uint8_t v_res_124_;
v_res_124_ = l_Std_Time_Week_instOrdOffset___aux__1(v_x_117_, v_y_118_);
stack->m_num = v_res_124_;
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instOrdOffset___aux__1___boxed(lean_object* v_x_125_, lean_object* v_y_126_){
_start:
{
uint8_t v_res_127_; lean_object* v_r_128_; 
v_res_127_ = l_Std_Time_Week_instOrdOffset___aux__1(v_x_125_, v_y_126_);
lean_dec(v_y_126_);
lean_dec(v_x_125_);
v_r_128_ = lean_box(v_res_127_);
return v_r_128_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instReprOrdinal___aux__1(lean_object* v_n_131_, lean_object* v_a_132_){
_start:
{
lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_133_ = lean_obj_once(&l_Std_Time_Week_instReprOffset___aux__1___closed__0, &l_Std_Time_Week_instReprOffset___aux__1___closed__0_once, _init_l_Std_Time_Week_instReprOffset___aux__1___closed__0);
v___x_134_ = lean_int_dec_lt(v_n_131_, v___x_133_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = l_Int_repr(v_n_131_);
v___x_136_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
return v___x_136_;
}
else
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_137_ = l_Int_repr(v_n_131_);
v___x_138_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
v___x_139_ = l_Repr_addAppParen(v___x_138_, v_a_132_);
return v___x_139_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instReprOrdinal___aux__1___boxed(lean_object* v_n_140_, lean_object* v_a_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Std_Time_Week_OfYear_instReprOrdinal___aux__1(v_n_140_, v_a_141_);
lean_dec(v_a_141_);
lean_dec(v_n_140_);
return v_res_142_;
}
}
uint8_t l_Std_Time_Week_OfYear_instDecidableEqOrdinal___aux__1(lean_object* v_a_144_, lean_object* v_b_145_){
_start:
{
uint8_t v___x_146_; 
v___x_146_ = lean_int_dec_eq(v_a_144_, v_b_145_);
return v___x_146_;
}
}
LEAN_EXPORT void l_Std_Time_Week_OfYear_instDecidableEqOrdinal___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_144_ = stack[0].m_obj;
lean_object* v_b_145_ = stack[1].m_obj;
uint8_t v_res_147_;
v_res_147_ = l_Std_Time_Week_OfYear_instDecidableEqOrdinal___aux__1(v_a_144_, v_b_145_);
stack->m_num = v_res_147_;
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instDecidableEqOrdinal___aux__1___boxed(lean_object* v_a_148_, lean_object* v_b_149_){
_start:
{
uint8_t v_res_150_; lean_object* v_r_151_; 
v_res_150_ = l_Std_Time_Week_OfYear_instDecidableEqOrdinal___aux__1(v_a_148_, v_b_149_);
lean_dec(v_b_149_);
lean_dec(v_a_148_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
uint8_t l_Std_Time_Week_OfYear_instDecidableEqOrdinal(lean_object* v_a_152_, lean_object* v_b_153_){
_start:
{
uint8_t v___x_154_; 
v___x_154_ = lean_int_dec_eq(v_a_152_, v_b_153_);
return v___x_154_;
}
}
LEAN_EXPORT void l_Std_Time_Week_OfYear_instDecidableEqOrdinal_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_152_ = stack[0].m_obj;
lean_object* v_b_153_ = stack[1].m_obj;
uint8_t v_res_155_;
v_res_155_ = l_Std_Time_Week_OfYear_instDecidableEqOrdinal(v_a_152_, v_b_153_);
stack->m_num = v_res_155_;
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instDecidableEqOrdinal___boxed(lean_object* v_a_156_, lean_object* v_b_157_){
_start:
{
uint8_t v_res_158_; lean_object* v_r_159_; 
v_res_158_ = l_Std_Time_Week_OfYear_instDecidableEqOrdinal(v_a_156_, v_b_157_);
lean_dec(v_b_157_);
lean_dec(v_a_156_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_instLEOrdinal(void){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lean_box(0);
return v___x_160_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_instLTOrdinal(void){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = lean_box(0);
return v___x_161_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_unsigned_to_nat(1u);
v___x_163_ = lean_nat_to_int(v___x_162_);
return v___x_163_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__1(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_unsigned_to_nat(52u);
v___x_165_ = lean_nat_to_int(v___x_164_);
return v___x_165_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__2(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_166_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__1, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__1_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__1);
v___x_167_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_168_ = lean_int_add(v___x_167_, v___x_166_);
return v___x_168_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__3(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_169_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_170_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__2, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__2_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__2);
v___x_171_ = lean_int_sub(v___x_170_, v___x_169_);
return v___x_171_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v_range_174_; 
v___x_172_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_173_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__3);
v_range_174_ = lean_int_add(v___x_173_, v___x_172_);
return v_range_174_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1(lean_object* v_n_175_){
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
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instOfNatOrdinal(lean_object* v_n_184_){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v_range_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_185_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_186_ = lean_nat_to_int(v_n_184_);
v_range_187_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4);
v___x_188_ = lean_int_sub(v___x_186_, v___x_185_);
lean_dec(v___x_186_);
v___x_189_ = lean_int_emod(v___x_188_, v_range_187_);
lean_dec(v___x_188_);
v___x_190_ = lean_int_add(v___x_189_, v_range_187_);
lean_dec(v___x_189_);
v___x_191_ = lean_int_emod(v___x_190_, v_range_187_);
lean_dec(v___x_190_);
v___x_192_ = lean_int_add(v___x_191_, v___x_185_);
lean_dec(v___x_191_);
return v___x_192_;
}
}
uint8_t l_Std_Time_Week_OfYear_instDecidableLeOrdinal___aux__1(lean_object* v_x_193_, lean_object* v_y_194_){
_start:
{
uint8_t v___x_195_; 
v___x_195_ = lean_int_dec_le(v_x_193_, v_y_194_);
return v___x_195_;
}
}
LEAN_EXPORT void l_Std_Time_Week_OfYear_instDecidableLeOrdinal___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_193_ = stack[0].m_obj;
lean_object* v_y_194_ = stack[1].m_obj;
uint8_t v_res_196_;
v_res_196_ = l_Std_Time_Week_OfYear_instDecidableLeOrdinal___aux__1(v_x_193_, v_y_194_);
stack->m_num = v_res_196_;
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instDecidableLeOrdinal___aux__1___boxed(lean_object* v_x_197_, lean_object* v_y_198_){
_start:
{
uint8_t v_res_199_; lean_object* v_r_200_; 
v_res_199_ = l_Std_Time_Week_OfYear_instDecidableLeOrdinal___aux__1(v_x_197_, v_y_198_);
lean_dec(v_y_198_);
lean_dec(v_x_197_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
uint8_t l_Std_Time_Week_OfYear_instDecidableLeOrdinal(lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
uint8_t v___x_203_; 
v___x_203_ = lean_int_dec_le(v___y_201_, v___y_202_);
return v___x_203_;
}
}
LEAN_EXPORT void l_Std_Time_Week_OfYear_instDecidableLeOrdinal_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_201_ = stack[0].m_obj;
lean_object* v___y_202_ = stack[1].m_obj;
uint8_t v_res_204_;
v_res_204_ = l_Std_Time_Week_OfYear_instDecidableLeOrdinal(v___y_201_, v___y_202_);
stack->m_num = v_res_204_;
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instDecidableLeOrdinal___boxed(lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
uint8_t v_res_207_; lean_object* v_r_208_; 
v_res_207_ = l_Std_Time_Week_OfYear_instDecidableLeOrdinal(v___y_205_, v___y_206_);
lean_dec(v___y_206_);
lean_dec(v___y_205_);
v_r_208_ = lean_box(v_res_207_);
return v_r_208_;
}
}
uint8_t l_Std_Time_Week_OfYear_instDecidableLtOrdinal___aux__1(lean_object* v_x_209_, lean_object* v_y_210_){
_start:
{
uint8_t v___x_211_; 
v___x_211_ = lean_int_dec_lt(v_x_209_, v_y_210_);
return v___x_211_;
}
}
LEAN_EXPORT void l_Std_Time_Week_OfYear_instDecidableLtOrdinal___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_209_ = stack[0].m_obj;
lean_object* v_y_210_ = stack[1].m_obj;
uint8_t v_res_212_;
v_res_212_ = l_Std_Time_Week_OfYear_instDecidableLtOrdinal___aux__1(v_x_209_, v_y_210_);
stack->m_num = v_res_212_;
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instDecidableLtOrdinal___aux__1___boxed(lean_object* v_x_213_, lean_object* v_y_214_){
_start:
{
uint8_t v_res_215_; lean_object* v_r_216_; 
v_res_215_ = l_Std_Time_Week_OfYear_instDecidableLtOrdinal___aux__1(v_x_213_, v_y_214_);
lean_dec(v_y_214_);
lean_dec(v_x_213_);
v_r_216_ = lean_box(v_res_215_);
return v_r_216_;
}
}
uint8_t l_Std_Time_Week_OfYear_instDecidableLtOrdinal(lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
uint8_t v___x_219_; 
v___x_219_ = lean_int_dec_lt(v___y_217_, v___y_218_);
return v___x_219_;
}
}
LEAN_EXPORT void l_Std_Time_Week_OfYear_instDecidableLtOrdinal_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_217_ = stack[0].m_obj;
lean_object* v___y_218_ = stack[1].m_obj;
uint8_t v_res_220_;
v_res_220_ = l_Std_Time_Week_OfYear_instDecidableLtOrdinal(v___y_217_, v___y_218_);
stack->m_num = v_res_220_;
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instDecidableLtOrdinal___boxed(lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
uint8_t v_res_223_; lean_object* v_r_224_; 
v_res_223_ = l_Std_Time_Week_OfYear_instDecidableLtOrdinal(v___y_221_, v___y_222_);
lean_dec(v___y_222_);
lean_dec(v___y_221_);
v_r_224_ = lean_box(v_res_223_);
return v_r_224_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__0(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_226_ = lean_int_sub(v___x_225_, v___x_225_);
return v___x_226_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__1(void){
_start:
{
lean_object* v_range_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_range_227_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4);
v___x_228_ = lean_obj_once(&l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__0, &l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__0);
v___x_229_ = lean_int_emod(v___x_228_, v_range_227_);
return v___x_229_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__2(void){
_start:
{
lean_object* v_range_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v_range_230_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4);
v___x_231_ = lean_obj_once(&l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__1, &l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__1_once, _init_l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__1);
v___x_232_ = lean_int_add(v___x_231_, v_range_230_);
return v___x_232_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__3(void){
_start:
{
lean_object* v_range_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v_range_233_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__4);
v___x_234_ = lean_obj_once(&l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__2, &l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__2_once, _init_l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__2);
v___x_235_ = lean_int_emod(v___x_234_, v_range_233_);
return v___x_235_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__4(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_236_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_237_ = lean_obj_once(&l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__3, &l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__3);
v___x_238_ = lean_int_add(v___x_237_, v___x_236_);
return v___x_238_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_instInhabitedOrdinal(void){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = lean_obj_once(&l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__4, &l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__4_once, _init_l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__4);
return v___x_239_;
}
}
uint8_t l_Std_Time_Week_OfYear_instOrdOrdinal___aux__1(lean_object* v_x_240_, lean_object* v_y_241_){
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
LEAN_EXPORT void l_Std_Time_Week_OfYear_instOrdOrdinal___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_240_ = stack[0].m_obj;
lean_object* v_y_241_ = stack[1].m_obj;
uint8_t v_res_247_;
v_res_247_ = l_Std_Time_Week_OfYear_instOrdOrdinal___aux__1(v_x_240_, v_y_241_);
stack->m_num = v_res_247_;
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_instOrdOrdinal___aux__1___boxed(lean_object* v_x_248_, lean_object* v_y_249_){
_start:
{
uint8_t v_res_250_; lean_object* v_r_251_; 
v_res_250_ = l_Std_Time_Week_OfYear_instOrdOrdinal___aux__1(v_x_248_, v_y_249_);
lean_dec(v_y_249_);
lean_dec(v_x_248_);
v_r_251_ = lean_box(v_res_250_);
return v_r_251_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_Ordinal_ofInt___redArg(lean_object* v_data_254_){
_start:
{
lean_inc(v_data_254_);
return v_data_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_Ordinal_ofInt___redArg___boxed(lean_object* v_data_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Std_Time_Week_OfYear_Ordinal_ofInt___redArg(v_data_255_);
lean_dec(v_data_255_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_Ordinal_ofInt(lean_object* v_data_257_, lean_object* v_h_258_){
_start:
{
lean_inc(v_data_257_);
return v_data_257_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_Ordinal_ofInt___boxed(lean_object* v_data_259_, lean_object* v_h_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Std_Time_Week_OfYear_Ordinal_ofInt(v_data_259_, v_h_260_);
lean_dec(v_data_259_);
return v_res_261_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__12(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = ((lean_object*)(l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__10));
v___x_289_ = l_Lean_mkAtom(v___x_288_);
return v___x_289_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__13(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_290_ = lean_obj_once(&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__12, &l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__12_once, _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__12);
v___x_291_ = ((lean_object*)(l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__5));
v___x_292_ = lean_array_push(v___x_291_, v___x_290_);
return v___x_292_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__17(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_303_ = ((lean_object*)(l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__16));
v___x_304_ = ((lean_object*)(l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__5));
v___x_305_ = lean_array_push(v___x_304_, v___x_303_);
return v___x_305_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__18(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_306_ = lean_obj_once(&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__17, &l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__17_once, _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__17);
v___x_307_ = ((lean_object*)(l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__15));
v___x_308_ = lean_box(2);
v___x_309_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v___x_307_);
lean_ctor_set(v___x_309_, 2, v___x_306_);
return v___x_309_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__19(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_310_ = lean_obj_once(&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__18, &l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__18_once, _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__18);
v___x_311_ = lean_obj_once(&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__13, &l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__13_once, _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__13);
v___x_312_ = lean_array_push(v___x_311_, v___x_310_);
return v___x_312_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__20(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_313_ = lean_obj_once(&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__19, &l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__19_once, _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__19);
v___x_314_ = ((lean_object*)(l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__11));
v___x_315_ = lean_box(2);
v___x_316_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___x_314_);
lean_ctor_set(v___x_316_, 2, v___x_313_);
return v___x_316_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__21(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = lean_obj_once(&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__20, &l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__20_once, _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__20);
v___x_318_ = ((lean_object*)(l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__5));
v___x_319_ = lean_array_push(v___x_318_, v___x_317_);
return v___x_319_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__22(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_320_ = lean_obj_once(&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__21, &l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__21_once, _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__21);
v___x_321_ = ((lean_object*)(l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__9));
v___x_322_ = lean_box(2);
v___x_323_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v___x_321_);
lean_ctor_set(v___x_323_, 2, v___x_320_);
return v___x_323_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__23(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_324_ = lean_obj_once(&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__22, &l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__22_once, _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__22);
v___x_325_ = ((lean_object*)(l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__5));
v___x_326_ = lean_array_push(v___x_325_, v___x_324_);
return v___x_326_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__24(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_327_ = lean_obj_once(&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__23, &l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__23_once, _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__23);
v___x_328_ = ((lean_object*)(l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__7));
v___x_329_ = lean_box(2);
v___x_330_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v___x_328_);
lean_ctor_set(v___x_330_, 2, v___x_327_);
return v___x_330_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__25(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = lean_obj_once(&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__24, &l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__24_once, _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__24);
v___x_332_ = ((lean_object*)(l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__5));
v___x_333_ = lean_array_push(v___x_332_, v___x_331_);
return v___x_333_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__26(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_334_ = lean_obj_once(&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__25, &l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__25_once, _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__25);
v___x_335_ = ((lean_object*)(l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__4));
v___x_336_ = lean_box(2);
v___x_337_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v___x_335_);
lean_ctor_set(v___x_337_, 2, v___x_334_);
return v___x_337_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1(void){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = lean_obj_once(&l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__26, &l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__26_once, _init_l_Std_Time_Week_OfYear_Ordinal_ofNat___auto__1___closed__26);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat___redArg(lean_object* v_data_339_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = lean_nat_to_int(v_data_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_Ordinal_ofNat(lean_object* v_data_341_, lean_object* v_h_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = lean_nat_to_int(v_data_341_);
return v___x_343_;
}
}
static lean_object* _init_l_Std_Time_Week_OfYear_Ordinal_ofFin___closed__0(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_unsigned_to_nat(1u);
v___x_345_ = lean_nat_to_int(v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_Ordinal_ofFin(lean_object* v_data_346_){
_start:
{
lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = lean_unsigned_to_nat(1u);
v___x_348_ = lean_nat_dec_le(v___x_347_, v_data_346_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; 
lean_dec(v_data_346_);
v___x_349_ = lean_obj_once(&l_Std_Time_Week_OfYear_Ordinal_ofFin___closed__0, &l_Std_Time_Week_OfYear_Ordinal_ofFin___closed__0_once, _init_l_Std_Time_Week_OfYear_Ordinal_ofFin___closed__0);
return v___x_349_;
}
else
{
lean_object* v___x_350_; 
v___x_350_ = lean_nat_to_int(v_data_346_);
return v___x_350_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_Ordinal_toOffset(lean_object* v_ordinal_351_){
_start:
{
lean_inc(v_ordinal_351_);
return v_ordinal_351_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_OfYear_Ordinal_toOffset___boxed(lean_object* v_ordinal_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Std_Time_Week_OfYear_Ordinal_toOffset(v_ordinal_352_);
lean_dec(v_ordinal_352_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Aligned_instReprOrdinal___aux__1(lean_object* v_n_354_, lean_object* v_a_355_){
_start:
{
lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_356_ = lean_obj_once(&l_Std_Time_Week_instReprOffset___aux__1___closed__0, &l_Std_Time_Week_instReprOffset___aux__1___closed__0_once, _init_l_Std_Time_Week_instReprOffset___aux__1___closed__0);
v___x_357_ = lean_int_dec_lt(v_n_354_, v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = l_Int_repr(v_n_354_);
v___x_359_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
return v___x_359_;
}
else
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_360_ = l_Int_repr(v_n_354_);
v___x_361_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
v___x_362_ = l_Repr_addAppParen(v___x_361_, v_a_355_);
return v___x_362_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Aligned_instReprOrdinal___aux__1___boxed(lean_object* v_n_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Std_Time_Week_Aligned_instReprOrdinal___aux__1(v_n_363_, v_a_364_);
lean_dec(v_a_364_);
lean_dec(v_n_363_);
return v_res_365_;
}
}
uint8_t l_Std_Time_Week_Aligned_instDecidableEqOrdinal___aux__1(lean_object* v_a_367_, lean_object* v_b_368_){
_start:
{
uint8_t v___x_369_; 
v___x_369_ = lean_int_dec_eq(v_a_367_, v_b_368_);
return v___x_369_;
}
}
LEAN_EXPORT void l_Std_Time_Week_Aligned_instDecidableEqOrdinal___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_367_ = stack[0].m_obj;
lean_object* v_b_368_ = stack[1].m_obj;
uint8_t v_res_370_;
v_res_370_ = l_Std_Time_Week_Aligned_instDecidableEqOrdinal___aux__1(v_a_367_, v_b_368_);
stack->m_num = v_res_370_;
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Aligned_instDecidableEqOrdinal___aux__1___boxed(lean_object* v_a_371_, lean_object* v_b_372_){
_start:
{
uint8_t v_res_373_; lean_object* v_r_374_; 
v_res_373_ = l_Std_Time_Week_Aligned_instDecidableEqOrdinal___aux__1(v_a_371_, v_b_372_);
lean_dec(v_b_372_);
lean_dec(v_a_371_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
uint8_t l_Std_Time_Week_Aligned_instDecidableEqOrdinal(lean_object* v_a_375_, lean_object* v_b_376_){
_start:
{
uint8_t v___x_377_; 
v___x_377_ = lean_int_dec_eq(v_a_375_, v_b_376_);
return v___x_377_;
}
}
LEAN_EXPORT void l_Std_Time_Week_Aligned_instDecidableEqOrdinal_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_375_ = stack[0].m_obj;
lean_object* v_b_376_ = stack[1].m_obj;
uint8_t v_res_378_;
v_res_378_ = l_Std_Time_Week_Aligned_instDecidableEqOrdinal(v_a_375_, v_b_376_);
stack->m_num = v_res_378_;
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Aligned_instDecidableEqOrdinal___boxed(lean_object* v_a_379_, lean_object* v_b_380_){
_start:
{
uint8_t v_res_381_; lean_object* v_r_382_; 
v_res_381_ = l_Std_Time_Week_Aligned_instDecidableEqOrdinal(v_a_379_, v_b_380_);
lean_dec(v_b_380_);
lean_dec(v_a_379_);
v_r_382_ = lean_box(v_res_381_);
return v_r_382_;
}
}
static lean_object* _init_l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__0(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = lean_unsigned_to_nat(4u);
v___x_384_ = lean_nat_to_int(v___x_383_);
return v___x_384_;
}
}
static lean_object* _init_l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__1(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_385_ = lean_obj_once(&l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__0);
v___x_386_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_387_ = lean_int_add(v___x_386_, v___x_385_);
return v___x_387_;
}
}
static lean_object* _init_l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__2(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_388_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_389_ = lean_obj_once(&l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__1, &l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__1_once, _init_l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__1);
v___x_390_ = lean_int_sub(v___x_389_, v___x_388_);
return v___x_390_;
}
}
static lean_object* _init_l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v_range_393_; 
v___x_391_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_392_ = lean_obj_once(&l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__2, &l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__2_once, _init_l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__2);
v_range_393_ = lean_int_add(v___x_392_, v___x_391_);
return v_range_393_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1(lean_object* v_n_394_){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v_range_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_395_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_396_ = lean_nat_to_int(v_n_394_);
v_range_397_ = lean_obj_once(&l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3);
v___x_398_ = lean_int_sub(v___x_396_, v___x_395_);
lean_dec(v___x_396_);
v___x_399_ = lean_int_emod(v___x_398_, v_range_397_);
lean_dec(v___x_398_);
v___x_400_ = lean_int_add(v___x_399_, v_range_397_);
lean_dec(v___x_399_);
v___x_401_ = lean_int_emod(v___x_400_, v_range_397_);
lean_dec(v___x_400_);
v___x_402_ = lean_int_add(v___x_401_, v___x_395_);
lean_dec(v___x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Aligned_instOfNatOrdinal(lean_object* v_n_403_){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v_range_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_404_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_405_ = lean_nat_to_int(v_n_403_);
v_range_406_ = lean_obj_once(&l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3);
v___x_407_ = lean_int_sub(v___x_405_, v___x_404_);
lean_dec(v___x_405_);
v___x_408_ = lean_int_emod(v___x_407_, v_range_406_);
lean_dec(v___x_407_);
v___x_409_ = lean_int_add(v___x_408_, v_range_406_);
lean_dec(v___x_408_);
v___x_410_ = lean_int_emod(v___x_409_, v_range_406_);
lean_dec(v___x_409_);
v___x_411_ = lean_int_add(v___x_410_, v___x_404_);
lean_dec(v___x_410_);
return v___x_411_;
}
}
static lean_object* _init_l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__0(void){
_start:
{
lean_object* v_range_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_range_412_ = lean_obj_once(&l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3);
v___x_413_ = lean_obj_once(&l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__0, &l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__0);
v___x_414_ = lean_int_emod(v___x_413_, v_range_412_);
return v___x_414_;
}
}
static lean_object* _init_l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__1(void){
_start:
{
lean_object* v_range_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v_range_415_ = lean_obj_once(&l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3);
v___x_416_ = lean_obj_once(&l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__0, &l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__0);
v___x_417_ = lean_int_add(v___x_416_, v_range_415_);
return v___x_417_;
}
}
static lean_object* _init_l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__2(void){
_start:
{
lean_object* v_range_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v_range_418_ = lean_obj_once(&l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Week_Aligned_instOfNatOrdinal___aux__1___closed__3);
v___x_419_ = lean_obj_once(&l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__1, &l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__1_once, _init_l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__1);
v___x_420_ = lean_int_emod(v___x_419_, v_range_418_);
return v___x_420_;
}
}
static lean_object* _init_l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__3(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_421_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_422_ = lean_obj_once(&l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__2, &l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__2_once, _init_l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__2);
v___x_423_ = lean_int_add(v___x_422_, v___x_421_);
return v___x_423_;
}
}
static lean_object* _init_l_Std_Time_Week_Aligned_instInhabitedOrdinal(void){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = lean_obj_once(&l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__3, &l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Week_Aligned_instInhabitedOrdinal___closed__3);
return v___x_424_;
}
}
uint8_t l_Std_Time_Week_Aligned_instOrdOrdinal___aux__1(lean_object* v_x_425_, lean_object* v_y_426_){
_start:
{
uint8_t v___x_427_; 
v___x_427_ = lean_int_dec_lt(v_x_425_, v_y_426_);
if (v___x_427_ == 0)
{
uint8_t v___x_428_; 
v___x_428_ = lean_int_dec_eq(v_x_425_, v_y_426_);
if (v___x_428_ == 0)
{
uint8_t v___x_429_; 
v___x_429_ = 2;
return v___x_429_;
}
else
{
uint8_t v___x_430_; 
v___x_430_ = 1;
return v___x_430_;
}
}
else
{
uint8_t v___x_431_; 
v___x_431_ = 0;
return v___x_431_;
}
}
}
LEAN_EXPORT void l_Std_Time_Week_Aligned_instOrdOrdinal___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_425_ = stack[0].m_obj;
lean_object* v_y_426_ = stack[1].m_obj;
uint8_t v_res_432_;
v_res_432_ = l_Std_Time_Week_Aligned_instOrdOrdinal___aux__1(v_x_425_, v_y_426_);
stack->m_num = v_res_432_;
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Aligned_instOrdOrdinal___aux__1___boxed(lean_object* v_x_433_, lean_object* v_y_434_){
_start:
{
uint8_t v_res_435_; lean_object* v_r_436_; 
v_res_435_ = l_Std_Time_Week_Aligned_instOrdOrdinal___aux__1(v_x_433_, v_y_434_);
lean_dec(v_y_434_);
lean_dec(v_x_433_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instReprOrdinal___aux__1(lean_object* v_n_439_, lean_object* v_a_440_){
_start:
{
lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_441_ = lean_obj_once(&l_Std_Time_Week_instReprOffset___aux__1___closed__0, &l_Std_Time_Week_instReprOffset___aux__1___closed__0_once, _init_l_Std_Time_Week_instReprOffset___aux__1___closed__0);
v___x_442_ = lean_int_dec_lt(v_n_439_, v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = l_Int_repr(v_n_439_);
v___x_444_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
return v___x_444_;
}
else
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_445_ = l_Int_repr(v_n_439_);
v___x_446_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
v___x_447_ = l_Repr_addAppParen(v___x_446_, v_a_440_);
return v___x_447_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instReprOrdinal___aux__1___boxed(lean_object* v_n_448_, lean_object* v_a_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Std_Time_Week_instReprOrdinal___aux__1(v_n_448_, v_a_449_);
lean_dec(v_a_449_);
lean_dec(v_n_448_);
return v_res_450_;
}
}
uint8_t l_Std_Time_Week_instDecidableEqOrdinal___aux__1(lean_object* v_a_452_, lean_object* v_b_453_){
_start:
{
uint8_t v___x_454_; 
v___x_454_ = lean_int_dec_eq(v_a_452_, v_b_453_);
return v___x_454_;
}
}
LEAN_EXPORT void l_Std_Time_Week_instDecidableEqOrdinal___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_452_ = stack[0].m_obj;
lean_object* v_b_453_ = stack[1].m_obj;
uint8_t v_res_455_;
v_res_455_ = l_Std_Time_Week_instDecidableEqOrdinal___aux__1(v_a_452_, v_b_453_);
stack->m_num = v_res_455_;
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableEqOrdinal___aux__1___boxed(lean_object* v_a_456_, lean_object* v_b_457_){
_start:
{
uint8_t v_res_458_; lean_object* v_r_459_; 
v_res_458_ = l_Std_Time_Week_instDecidableEqOrdinal___aux__1(v_a_456_, v_b_457_);
lean_dec(v_b_457_);
lean_dec(v_a_456_);
v_r_459_ = lean_box(v_res_458_);
return v_r_459_;
}
}
uint8_t l_Std_Time_Week_instDecidableEqOrdinal(lean_object* v_a_460_, lean_object* v_b_461_){
_start:
{
uint8_t v___x_462_; 
v___x_462_ = lean_int_dec_eq(v_a_460_, v_b_461_);
return v___x_462_;
}
}
LEAN_EXPORT void l_Std_Time_Week_instDecidableEqOrdinal_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_460_ = stack[0].m_obj;
lean_object* v_b_461_ = stack[1].m_obj;
uint8_t v_res_463_;
v_res_463_ = l_Std_Time_Week_instDecidableEqOrdinal(v_a_460_, v_b_461_);
stack->m_num = v_res_463_;
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableEqOrdinal___boxed(lean_object* v_a_464_, lean_object* v_b_465_){
_start:
{
uint8_t v_res_466_; lean_object* v_r_467_; 
v_res_466_ = l_Std_Time_Week_instDecidableEqOrdinal(v_a_464_, v_b_465_);
lean_dec(v_b_465_);
lean_dec(v_a_464_);
v_r_467_ = lean_box(v_res_466_);
return v_r_467_;
}
}
static lean_object* _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_unsigned_to_nat(5u);
v___x_469_ = lean_nat_to_int(v___x_468_);
return v___x_469_;
}
}
static lean_object* _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__1(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_470_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0);
v___x_471_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_472_ = lean_int_add(v___x_471_, v___x_470_);
return v___x_472_;
}
}
static lean_object* _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__2(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_473_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_474_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__1, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__1_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__1);
v___x_475_ = lean_int_sub(v___x_474_, v___x_473_);
return v___x_475_;
}
}
static lean_object* _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v_range_478_; 
v___x_476_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_477_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__2, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__2_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__2);
v_range_478_ = lean_int_add(v___x_477_, v___x_476_);
return v_range_478_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instOfNatOrdinal___aux__1(lean_object* v_n_479_){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v_range_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_480_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_481_ = lean_nat_to_int(v_n_479_);
v_range_482_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3);
v___x_483_ = lean_int_sub(v___x_481_, v___x_480_);
lean_dec(v___x_481_);
v___x_484_ = lean_int_emod(v___x_483_, v_range_482_);
lean_dec(v___x_483_);
v___x_485_ = lean_int_add(v___x_484_, v_range_482_);
lean_dec(v___x_484_);
v___x_486_ = lean_int_emod(v___x_485_, v_range_482_);
lean_dec(v___x_485_);
v___x_487_ = lean_int_add(v___x_486_, v___x_480_);
lean_dec(v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instOfNatOrdinal(lean_object* v_n_488_){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v_range_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_489_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_490_ = lean_nat_to_int(v_n_488_);
v_range_491_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3);
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
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal___closed__0(void){
_start:
{
lean_object* v_range_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v_range_497_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3);
v___x_498_ = lean_obj_once(&l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__0, &l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Week_OfYear_instInhabitedOrdinal___closed__0);
v___x_499_ = lean_int_emod(v___x_498_, v_range_497_);
return v___x_499_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal___closed__1(void){
_start:
{
lean_object* v_range_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v_range_500_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3);
v___x_501_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__0, &l_Std_Time_Week_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__0);
v___x_502_ = lean_int_add(v___x_501_, v_range_500_);
return v___x_502_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal___closed__2(void){
_start:
{
lean_object* v_range_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v_range_503_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3, &l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3_once, _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3);
v___x_504_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__1, &l_Std_Time_Week_instInhabitedOrdinal___closed__1_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__1);
v___x_505_ = lean_int_emod(v___x_504_, v_range_503_);
return v___x_505_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal___closed__3(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_506_ = lean_obj_once(&l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0, &l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0_once, _init_l_Std_Time_Week_OfYear_instOfNatOrdinal___aux__1___closed__0);
v___x_507_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__2, &l_Std_Time_Week_instInhabitedOrdinal___closed__2_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__2);
v___x_508_ = lean_int_add(v___x_507_, v___x_506_);
return v___x_508_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal(void){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__3, &l_Std_Time_Week_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__3);
return v___x_509_;
}
}
uint8_t l_Std_Time_Week_instOrdOrdinal___aux__1(lean_object* v_x_510_, lean_object* v_y_511_){
_start:
{
uint8_t v___x_512_; 
v___x_512_ = lean_int_dec_lt(v_x_510_, v_y_511_);
if (v___x_512_ == 0)
{
uint8_t v___x_513_; 
v___x_513_ = lean_int_dec_eq(v_x_510_, v_y_511_);
if (v___x_513_ == 0)
{
uint8_t v___x_514_; 
v___x_514_ = 2;
return v___x_514_;
}
else
{
uint8_t v___x_515_; 
v___x_515_ = 1;
return v___x_515_;
}
}
else
{
uint8_t v___x_516_; 
v___x_516_ = 0;
return v___x_516_;
}
}
}
LEAN_EXPORT void l_Std_Time_Week_instOrdOrdinal___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_510_ = stack[0].m_obj;
lean_object* v_y_511_ = stack[1].m_obj;
uint8_t v_res_517_;
v_res_517_ = l_Std_Time_Week_instOrdOrdinal___aux__1(v_x_510_, v_y_511_);
stack->m_num = v_res_517_;
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instOrdOrdinal___aux__1___boxed(lean_object* v_x_518_, lean_object* v_y_519_){
_start:
{
uint8_t v_res_520_; lean_object* v_r_521_; 
v_res_520_ = l_Std_Time_Week_instOrdOrdinal___aux__1(v_x_518_, v_y_519_);
lean_dec(v_y_519_);
lean_dec(v_x_518_);
v_r_521_ = lean_box(v_res_520_);
return v_r_521_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofNat(lean_object* v_data_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = lean_nat_to_int(v_data_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofInt(lean_object* v_data_526_){
_start:
{
lean_inc(v_data_526_);
return v_data_526_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofInt___boxed(lean_object* v_data_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Std_Time_Week_Offset_ofInt(v_data_527_);
lean_dec(v_data_527_);
return v_res_528_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_unsigned_to_nat(604800000u);
v___x_530_ = lean_nat_to_int(v___x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toMilliseconds(lean_object* v_weeks_531_){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_obj_once(&l_Std_Time_Week_Offset_toMilliseconds___closed__0, &l_Std_Time_Week_Offset_toMilliseconds___closed__0_once, _init_l_Std_Time_Week_Offset_toMilliseconds___closed__0);
v___x_533_ = lean_int_mul(v_weeks_531_, v___x_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toMilliseconds___boxed(lean_object* v_weeks_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Std_Time_Week_Offset_toMilliseconds(v_weeks_534_);
lean_dec(v_weeks_534_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofMilliseconds(lean_object* v_millis_536_){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_obj_once(&l_Std_Time_Week_Offset_toMilliseconds___closed__0, &l_Std_Time_Week_Offset_toMilliseconds___closed__0_once, _init_l_Std_Time_Week_Offset_toMilliseconds___closed__0);
v___x_538_ = lean_int_ediv(v_millis_536_, v___x_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofMilliseconds___boxed(lean_object* v_millis_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Std_Time_Week_Offset_ofMilliseconds(v_millis_539_);
lean_dec(v_millis_539_);
return v_res_540_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toNanoseconds___closed__0(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_cstr_to_nat("604800000000000");
v___x_542_ = lean_nat_to_int(v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toNanoseconds(lean_object* v_weeks_543_){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = lean_obj_once(&l_Std_Time_Week_Offset_toNanoseconds___closed__0, &l_Std_Time_Week_Offset_toNanoseconds___closed__0_once, _init_l_Std_Time_Week_Offset_toNanoseconds___closed__0);
v___x_545_ = lean_int_mul(v_weeks_543_, v___x_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toNanoseconds___boxed(lean_object* v_weeks_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Std_Time_Week_Offset_toNanoseconds(v_weeks_546_);
lean_dec(v_weeks_546_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofNanoseconds(lean_object* v_nanos_548_){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = lean_obj_once(&l_Std_Time_Week_Offset_toNanoseconds___closed__0, &l_Std_Time_Week_Offset_toNanoseconds___closed__0_once, _init_l_Std_Time_Week_Offset_toNanoseconds___closed__0);
v___x_550_ = lean_int_ediv(v_nanos_548_, v___x_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofNanoseconds___boxed(lean_object* v_nanos_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Std_Time_Week_Offset_ofNanoseconds(v_nanos_551_);
lean_dec(v_nanos_551_);
return v_res_552_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toSeconds___closed__0(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = lean_unsigned_to_nat(604800u);
v___x_554_ = lean_nat_to_int(v___x_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toSeconds(lean_object* v_weeks_555_){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = lean_obj_once(&l_Std_Time_Week_Offset_toSeconds___closed__0, &l_Std_Time_Week_Offset_toSeconds___closed__0_once, _init_l_Std_Time_Week_Offset_toSeconds___closed__0);
v___x_557_ = lean_int_mul(v_weeks_555_, v___x_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toSeconds___boxed(lean_object* v_weeks_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Std_Time_Week_Offset_toSeconds(v_weeks_558_);
lean_dec(v_weeks_558_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofSeconds(lean_object* v_secs_560_){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = lean_obj_once(&l_Std_Time_Week_Offset_toSeconds___closed__0, &l_Std_Time_Week_Offset_toSeconds___closed__0_once, _init_l_Std_Time_Week_Offset_toSeconds___closed__0);
v___x_562_ = lean_int_ediv(v_secs_560_, v___x_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofSeconds___boxed(lean_object* v_secs_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Std_Time_Week_Offset_ofSeconds(v_secs_563_);
lean_dec(v_secs_563_);
return v_res_564_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toMinutes___closed__0(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_unsigned_to_nat(10080u);
v___x_566_ = lean_nat_to_int(v___x_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toMinutes(lean_object* v_weeks_567_){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_obj_once(&l_Std_Time_Week_Offset_toMinutes___closed__0, &l_Std_Time_Week_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Week_Offset_toMinutes___closed__0);
v___x_569_ = lean_int_mul(v_weeks_567_, v___x_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toMinutes___boxed(lean_object* v_weeks_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Std_Time_Week_Offset_toMinutes(v_weeks_570_);
lean_dec(v_weeks_570_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofMinutes(lean_object* v_minutes_572_){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = lean_obj_once(&l_Std_Time_Week_Offset_toMinutes___closed__0, &l_Std_Time_Week_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Week_Offset_toMinutes___closed__0);
v___x_574_ = lean_int_ediv(v_minutes_572_, v___x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofMinutes___boxed(lean_object* v_minutes_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Std_Time_Week_Offset_ofMinutes(v_minutes_575_);
lean_dec(v_minutes_575_);
return v_res_576_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toHours___closed__0(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = lean_unsigned_to_nat(168u);
v___x_578_ = lean_nat_to_int(v___x_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toHours(lean_object* v_weeks_579_){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_obj_once(&l_Std_Time_Week_Offset_toHours___closed__0, &l_Std_Time_Week_Offset_toHours___closed__0_once, _init_l_Std_Time_Week_Offset_toHours___closed__0);
v___x_581_ = lean_int_mul(v_weeks_579_, v___x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toHours___boxed(lean_object* v_weeks_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Std_Time_Week_Offset_toHours(v_weeks_582_);
lean_dec(v_weeks_582_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofHours(lean_object* v_hours_584_){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = lean_obj_once(&l_Std_Time_Week_Offset_toHours___closed__0, &l_Std_Time_Week_Offset_toHours___closed__0_once, _init_l_Std_Time_Week_Offset_toHours___closed__0);
v___x_586_ = lean_int_ediv(v_hours_584_, v___x_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofHours___boxed(lean_object* v_hours_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Std_Time_Week_Offset_ofHours(v_hours_587_);
lean_dec(v_hours_587_);
return v_res_588_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toDays___closed__0(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = lean_unsigned_to_nat(7u);
v___x_590_ = lean_nat_to_int(v___x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toDays(lean_object* v_weeks_591_){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_obj_once(&l_Std_Time_Week_Offset_toDays___closed__0, &l_Std_Time_Week_Offset_toDays___closed__0_once, _init_l_Std_Time_Week_Offset_toDays___closed__0);
v___x_593_ = lean_int_mul(v_weeks_591_, v___x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toDays___boxed(lean_object* v_weeks_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Std_Time_Week_Offset_toDays(v_weeks_594_);
lean_dec(v_weeks_594_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofDays(lean_object* v_days_596_){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_obj_once(&l_Std_Time_Week_Offset_toDays___closed__0, &l_Std_Time_Week_Offset_toDays___closed__0_once, _init_l_Std_Time_Week_Offset_toDays___closed__0);
v___x_598_ = lean_int_ediv(v_days_596_, v___x_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofDays___boxed(lean_object* v_days_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Std_Time_Week_Offset_ofDays(v_days_599_);
lean_dec(v_days_599_);
return v_res_600_;
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
