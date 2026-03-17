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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Rat_mul(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_UnitVal_add___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_UnitVal_sub___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_Bounded_instRepr___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_UnitVal_instToString___lam__0___boxed(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_Bounded_instOrd___lam__0___boxed(lean_object*);
lean_object* l_instOrdInt___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_instOrdUnitVal___lam__0___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Int_neg___boxed(lean_object*);
lean_object* l_Std_Time_Internal_instInhabitedUnitVal_default(lean_object*);
lean_object* l_Std_Time_Internal_UnitVal_instRepr___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Week_instReprOrdinal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_Bounded_instRepr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Week_instReprOrdinal___closed__0 = (const lean_object*)&l_Std_Time_Week_instReprOrdinal___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Week_instReprOrdinal = (const lean_object*)&l_Std_Time_Week_instReprOrdinal___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableEqOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableEqOrdinal___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instLEOrdinal;
LEAN_EXPORT lean_object* l_Std_Time_Week_instLTOrdinal;
static lean_once_cell_t l_Std_Time_Week_instOfNatOrdinal___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instOfNatOrdinal___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Week_instOfNatOrdinal(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLeOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLeOrdinal___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_Time_Week_instInhabitedOrdinal___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instInhabitedOrdinal___closed__5;
static lean_once_cell_t l_Std_Time_Week_instInhabitedOrdinal___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instInhabitedOrdinal___closed__6;
static lean_once_cell_t l_Std_Time_Week_instInhabitedOrdinal___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instInhabitedOrdinal___closed__7;
static lean_once_cell_t l_Std_Time_Week_instInhabitedOrdinal___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instInhabitedOrdinal___closed__8;
LEAN_EXPORT lean_object* l_Std_Time_Week_instInhabitedOrdinal;
static const lean_closure_object l_Std_Time_Week_instOrdOrdinal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_Bounded_instOrd___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Week_instOrdOrdinal___closed__0 = (const lean_object*)&l_Std_Time_Week_instOrdOrdinal___closed__0_value;
static const lean_closure_object l_Std_Time_Week_instOrdOrdinal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdInt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Week_instOrdOrdinal___closed__1 = (const lean_object*)&l_Std_Time_Week_instOrdOrdinal___closed__1_value;
static const lean_closure_object l_Std_Time_Week_instOrdOrdinal___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_compareOn___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Week_instOrdOrdinal___closed__1_value),((lean_object*)&l_Std_Time_Week_instOrdOrdinal___closed__0_value)} };
static const lean_object* l_Std_Time_Week_instOrdOrdinal___closed__2 = (const lean_object*)&l_Std_Time_Week_instOrdOrdinal___closed__2_value;
LEAN_EXPORT const lean_object* l_Std_Time_Week_instOrdOrdinal = (const lean_object*)&l_Std_Time_Week_instOrdOrdinal___closed__2_value;
static const lean_closure_object l_Std_Time_Week_instReprOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_UnitVal_instRepr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Week_instReprOffset___closed__0 = (const lean_object*)&l_Std_Time_Week_instReprOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Week_instReprOffset = (const lean_object*)&l_Std_Time_Week_instReprOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Week_instReprOffset_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Week_instReprOffset_spec__0(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableEqOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableEqOffset___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Week_instInhabitedOffset___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instInhabitedOffset___closed__0;
static lean_once_cell_t l_Std_Time_Week_instInhabitedOffset___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instInhabitedOffset___closed__1;
static lean_once_cell_t l_Std_Time_Week_instInhabitedOffset___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instInhabitedOffset___closed__2;
static lean_once_cell_t l_Std_Time_Week_instInhabitedOffset___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instInhabitedOffset___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_Week_instInhabitedOffset;
static lean_once_cell_t l_Std_Time_Week_instAddOffset___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instAddOffset___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Week_instAddOffset;
static lean_once_cell_t l_Std_Time_Week_instSubOffset___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_instSubOffset___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Week_instSubOffset;
static const lean_closure_object l_Std_Time_Week_instNegOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Week_instNegOffset___closed__0 = (const lean_object*)&l_Std_Time_Week_instNegOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Week_instNegOffset = (const lean_object*)&l_Std_Time_Week_instNegOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Week_instLEOffset;
LEAN_EXPORT lean_object* l_Std_Time_Week_instLTOffset;
static const lean_closure_object l_Std_Time_Week_instToStringOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_UnitVal_instToString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Week_instToStringOffset___closed__0 = (const lean_object*)&l_Std_Time_Week_instToStringOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Week_instToStringOffset = (const lean_object*)&l_Std_Time_Week_instToStringOffset___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLeOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLeOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLtOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLtOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_instOfNatOffset(lean_object*);
static const lean_closure_object l_Std_Time_Week_instOrdOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_instOrdUnitVal___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Week_instOrdOffset___closed__0 = (const lean_object*)&l_Std_Time_Week_instOrdOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Week_instOrdOffset = (const lean_object*)&l_Std_Time_Week_instOrdOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofInt___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofInt___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofInt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofInt___boxed(lean_object*, lean_object*);
LEAN_EXPORT const lean_object* l_Std_Time_Week_Ordinal_instReprOfMonth = (const lean_object*)&l_Std_Time_Week_instReprOrdinal___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Week_Ordinal_instDecidableEqOfMonth(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_instDecidableEqOfMonth___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_instOfNatOfMonth(lean_object*);
static lean_once_cell_t l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__0;
static lean_once_cell_t l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__1;
static lean_once_cell_t l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__2;
static lean_once_cell_t l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3;
static lean_once_cell_t l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__4;
static lean_once_cell_t l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__5;
static lean_once_cell_t l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__6;
static lean_once_cell_t l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__7;
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_instInhabitedOfMonth;
LEAN_EXPORT const lean_object* l_Std_Time_Week_Ordinal_instOrdOfMonth = (const lean_object*)&l_Std_Time_Week_instOrdOrdinal___closed__2_value;
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
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableEqOrdinal(lean_object* v_a_3_, lean_object* v_b_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_int_dec_eq(v_a_3_, v_b_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableEqOrdinal___boxed(lean_object* v_a_6_, lean_object* v_b_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = l_Std_Time_Week_instDecidableEqOrdinal(v_a_6_, v_b_7_);
lean_dec(v_b_7_);
lean_dec(v_a_6_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
static lean_object* _init_l_Std_Time_Week_instLEOrdinal(void){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_box(0);
return v___x_10_;
}
}
static lean_object* _init_l_Std_Time_Week_instLTOrdinal(void){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_box(0);
return v___x_11_;
}
}
static lean_object* _init_l_Std_Time_Week_instOfNatOrdinal___closed__0(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_unsigned_to_nat(1u);
v___x_13_ = lean_nat_to_int(v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instOfNatOrdinal(lean_object* v_n_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_15_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___closed__0, &l_Std_Time_Week_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___closed__0);
v___x_16_ = lean_unsigned_to_nat(52u);
v___x_17_ = l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast(v___x_15_, v_n_14_, v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLeOrdinal(lean_object* v_x_18_, lean_object* v_y_19_){
_start:
{
uint8_t v___x_20_; 
v___x_20_ = lean_int_dec_le(v_x_18_, v_y_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLeOrdinal___boxed(lean_object* v_x_21_, lean_object* v_y_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l_Std_Time_Week_instDecidableLeOrdinal(v_x_21_, v_y_22_);
lean_dec(v_y_22_);
lean_dec(v_x_21_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLtOrdinal(lean_object* v_x_25_, lean_object* v_y_26_){
_start:
{
uint8_t v___x_27_; 
v___x_27_ = lean_int_dec_lt(v_x_25_, v_y_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLtOrdinal___boxed(lean_object* v_x_28_, lean_object* v_y_29_){
_start:
{
uint8_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = l_Std_Time_Week_instDecidableLtOrdinal(v_x_28_, v_y_29_);
lean_dec(v_y_29_);
lean_dec(v_x_28_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal___closed__0(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = lean_unsigned_to_nat(52u);
v___x_33_ = lean_nat_to_int(v___x_32_);
return v___x_33_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal___closed__1(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_34_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__0, &l_Std_Time_Week_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__0);
v___x_35_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___closed__0, &l_Std_Time_Week_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___closed__0);
v___x_36_ = lean_int_add(v___x_35_, v___x_34_);
return v___x_36_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal___closed__2(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_37_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___closed__0, &l_Std_Time_Week_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___closed__0);
v___x_38_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__1, &l_Std_Time_Week_instInhabitedOrdinal___closed__1_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__1);
v___x_39_ = lean_int_sub(v___x_38_, v___x_37_);
return v___x_39_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal___closed__3(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v_range_42_; 
v___x_40_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___closed__0, &l_Std_Time_Week_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___closed__0);
v___x_41_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__2, &l_Std_Time_Week_instInhabitedOrdinal___closed__2_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__2);
v_range_42_ = lean_int_add(v___x_41_, v___x_40_);
return v_range_42_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal___closed__4(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___closed__0, &l_Std_Time_Week_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___closed__0);
v___x_44_ = lean_int_sub(v___x_43_, v___x_43_);
return v___x_44_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal___closed__5(void){
_start:
{
lean_object* v_range_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v_range_45_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__3, &l_Std_Time_Week_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__3);
v___x_46_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__4, &l_Std_Time_Week_instInhabitedOrdinal___closed__4_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__4);
v___x_47_ = lean_int_emod(v___x_46_, v_range_45_);
return v___x_47_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal___closed__6(void){
_start:
{
lean_object* v_range_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_range_48_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__3, &l_Std_Time_Week_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__3);
v___x_49_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__5, &l_Std_Time_Week_instInhabitedOrdinal___closed__5_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__5);
v___x_50_ = lean_int_add(v___x_49_, v_range_48_);
return v___x_50_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal___closed__7(void){
_start:
{
lean_object* v_range_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v_range_51_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__3, &l_Std_Time_Week_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__3);
v___x_52_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__6, &l_Std_Time_Week_instInhabitedOrdinal___closed__6_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__6);
v___x_53_ = lean_int_emod(v___x_52_, v_range_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal___closed__8(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___closed__0, &l_Std_Time_Week_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___closed__0);
v___x_55_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__7, &l_Std_Time_Week_instInhabitedOrdinal___closed__7_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__7);
v___x_56_ = lean_int_add(v___x_55_, v___x_54_);
return v___x_56_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOrdinal(void){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__8, &l_Std_Time_Week_instInhabitedOrdinal___closed__8_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__8);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_Week_instReprOffset_spec__0_spec__0(lean_object* v_a_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lean_nat_to_int(v_a_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Week_instReprOffset_spec__0(lean_object* v_a_68_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_nat_to_int(v_a_68_);
v___x_70_ = l_Rat_ofInt(v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableEqOffset(lean_object* v_a_71_, lean_object* v_b_72_){
_start:
{
uint8_t v___x_73_; 
v___x_73_ = lean_int_dec_eq(v_a_71_, v_b_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableEqOffset___boxed(lean_object* v_a_74_, lean_object* v_b_75_){
_start:
{
uint8_t v_res_76_; lean_object* v_r_77_; 
v_res_76_ = l_Std_Time_Week_instDecidableEqOffset(v_a_74_, v_b_75_);
lean_dec(v_b_75_);
lean_dec(v_a_74_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset___closed__0(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(86400u);
v___x_79_ = l_Nat_cast___at___00Std_Time_Week_instReprOffset_spec__0(v___x_78_);
return v___x_79_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset___closed__1(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_unsigned_to_nat(7u);
v___x_81_ = l_Nat_cast___at___00Std_Time_Week_instReprOffset_spec__0(v___x_80_);
return v___x_81_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset___closed__2(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOffset___closed__1, &l_Std_Time_Week_instInhabitedOffset___closed__1_once, _init_l_Std_Time_Week_instInhabitedOffset___closed__1);
v___x_83_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOffset___closed__0, &l_Std_Time_Week_instInhabitedOffset___closed__0_once, _init_l_Std_Time_Week_instInhabitedOffset___closed__0);
v___x_84_ = l_Rat_mul(v___x_83_, v___x_82_);
return v___x_84_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset___closed__3(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOffset___closed__2, &l_Std_Time_Week_instInhabitedOffset___closed__2_once, _init_l_Std_Time_Week_instInhabitedOffset___closed__2);
v___x_86_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_85_);
return v___x_86_;
}
}
static lean_object* _init_l_Std_Time_Week_instInhabitedOffset(void){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOffset___closed__3, &l_Std_Time_Week_instInhabitedOffset___closed__3_once, _init_l_Std_Time_Week_instInhabitedOffset___closed__3);
return v___x_87_;
}
}
static lean_object* _init_l_Std_Time_Week_instAddOffset___closed__0(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOffset___closed__2, &l_Std_Time_Week_instInhabitedOffset___closed__2_once, _init_l_Std_Time_Week_instInhabitedOffset___closed__2);
v___x_89_ = lean_alloc_closure((void*)(l_Std_Time_Internal_UnitVal_add___boxed), 3, 1);
lean_closure_set(v___x_89_, 0, v___x_88_);
return v___x_89_;
}
}
static lean_object* _init_l_Std_Time_Week_instAddOffset(void){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = lean_obj_once(&l_Std_Time_Week_instAddOffset___closed__0, &l_Std_Time_Week_instAddOffset___closed__0_once, _init_l_Std_Time_Week_instAddOffset___closed__0);
return v___x_90_;
}
}
static lean_object* _init_l_Std_Time_Week_instSubOffset___closed__0(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOffset___closed__2, &l_Std_Time_Week_instInhabitedOffset___closed__2_once, _init_l_Std_Time_Week_instInhabitedOffset___closed__2);
v___x_92_ = lean_alloc_closure((void*)(l_Std_Time_Internal_UnitVal_sub___boxed), 3, 1);
lean_closure_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
}
static lean_object* _init_l_Std_Time_Week_instSubOffset(void){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lean_obj_once(&l_Std_Time_Week_instSubOffset___closed__0, &l_Std_Time_Week_instSubOffset___closed__0_once, _init_l_Std_Time_Week_instSubOffset___closed__0);
return v___x_93_;
}
}
static lean_object* _init_l_Std_Time_Week_instLEOffset(void){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_box(0);
return v___x_96_;
}
}
static lean_object* _init_l_Std_Time_Week_instLTOffset(void){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lean_box(0);
return v___x_97_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLeOffset(lean_object* v_x_100_, lean_object* v_y_101_){
_start:
{
uint8_t v___x_102_; 
v___x_102_ = lean_int_dec_le(v_x_100_, v_y_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLeOffset___boxed(lean_object* v_x_103_, lean_object* v_y_104_){
_start:
{
uint8_t v_res_105_; lean_object* v_r_106_; 
v_res_105_ = l_Std_Time_Week_instDecidableLeOffset(v_x_103_, v_y_104_);
lean_dec(v_y_104_);
lean_dec(v_x_103_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_instDecidableLtOffset(lean_object* v_x_107_, lean_object* v_y_108_){
_start:
{
uint8_t v___x_109_; 
v___x_109_ = lean_int_dec_lt(v_x_107_, v_y_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instDecidableLtOffset___boxed(lean_object* v_x_110_, lean_object* v_y_111_){
_start:
{
uint8_t v_res_112_; lean_object* v_r_113_; 
v_res_112_ = l_Std_Time_Week_instDecidableLtOffset(v_x_110_, v_y_111_);
lean_dec(v_y_111_);
lean_dec(v_x_110_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_instOfNatOffset(lean_object* v_n_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lean_nat_to_int(v_n_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofInt___redArg(lean_object* v_data_118_){
_start:
{
lean_inc(v_data_118_);
return v_data_118_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofInt___redArg___boxed(lean_object* v_data_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Std_Time_Week_Ordinal_ofInt___redArg(v_data_119_);
lean_dec(v_data_119_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofInt(lean_object* v_data_121_, lean_object* v_h_122_){
_start:
{
lean_inc(v_data_121_);
return v_data_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofInt___boxed(lean_object* v_data_123_, lean_object* v_h_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Std_Time_Week_Ordinal_ofInt(v_data_123_, v_h_124_);
lean_dec(v_data_123_);
return v_res_125_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Week_Ordinal_instDecidableEqOfMonth(lean_object* v_a_127_, lean_object* v_b_128_){
_start:
{
uint8_t v___x_129_; 
v___x_129_ = lean_int_dec_eq(v_a_127_, v_b_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_instDecidableEqOfMonth___boxed(lean_object* v_a_130_, lean_object* v_b_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l_Std_Time_Week_Ordinal_instDecidableEqOfMonth(v_a_130_, v_b_131_);
lean_dec(v_b_131_);
lean_dec(v_a_130_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_instOfNatOfMonth(lean_object* v_n_134_){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_135_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___closed__0, &l_Std_Time_Week_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___closed__0);
v___x_136_ = lean_unsigned_to_nat(5u);
v___x_137_ = l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast(v___x_135_, v_n_134_, v___x_136_);
return v___x_137_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__0(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_unsigned_to_nat(5u);
v___x_139_ = lean_nat_to_int(v___x_138_);
return v___x_139_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__1(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_140_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__0, &l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__0_once, _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__0);
v___x_141_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___closed__0, &l_Std_Time_Week_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___closed__0);
v___x_142_ = lean_int_add(v___x_141_, v___x_140_);
return v___x_142_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__2(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_143_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___closed__0, &l_Std_Time_Week_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___closed__0);
v___x_144_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__1, &l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__1_once, _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__1);
v___x_145_ = lean_int_sub(v___x_144_, v___x_143_);
return v___x_145_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v_range_148_; 
v___x_146_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___closed__0, &l_Std_Time_Week_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___closed__0);
v___x_147_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__2, &l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__2_once, _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__2);
v_range_148_ = lean_int_add(v___x_147_, v___x_146_);
return v_range_148_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__4(void){
_start:
{
lean_object* v_range_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v_range_149_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3, &l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3_once, _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3);
v___x_150_ = lean_obj_once(&l_Std_Time_Week_instInhabitedOrdinal___closed__4, &l_Std_Time_Week_instInhabitedOrdinal___closed__4_once, _init_l_Std_Time_Week_instInhabitedOrdinal___closed__4);
v___x_151_ = lean_int_emod(v___x_150_, v_range_149_);
return v___x_151_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__5(void){
_start:
{
lean_object* v_range_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_range_152_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3, &l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3_once, _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3);
v___x_153_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__4, &l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__4_once, _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__4);
v___x_154_ = lean_int_add(v___x_153_, v_range_152_);
return v___x_154_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__6(void){
_start:
{
lean_object* v_range_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v_range_155_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3, &l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3_once, _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3);
v___x_156_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__5, &l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__5_once, _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__5);
v___x_157_ = lean_int_emod(v___x_156_, v_range_155_);
return v___x_157_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__7(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_obj_once(&l_Std_Time_Week_instOfNatOrdinal___closed__0, &l_Std_Time_Week_instOfNatOrdinal___closed__0_once, _init_l_Std_Time_Week_instOfNatOrdinal___closed__0);
v___x_159_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__6, &l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__6_once, _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__6);
v___x_160_ = lean_int_add(v___x_159_, v___x_158_);
return v___x_160_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth(void){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = lean_obj_once(&l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__7, &l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__7_once, _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__7);
return v___x_161_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__12(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__10));
v___x_190_ = l_Lean_mkAtom(v___x_189_);
return v___x_190_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__13(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_191_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__12, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__12_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__12);
v___x_192_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5));
v___x_193_ = lean_array_push(v___x_192_, v___x_191_);
return v___x_193_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__17(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_204_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__16));
v___x_205_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5));
v___x_206_ = lean_array_push(v___x_205_, v___x_204_);
return v___x_206_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__18(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_207_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__17, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__17_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__17);
v___x_208_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15));
v___x_209_ = lean_box(2);
v___x_210_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v___x_208_);
lean_ctor_set(v___x_210_, 2, v___x_207_);
return v___x_210_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__19(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_211_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__18, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__18_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__18);
v___x_212_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__13, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__13_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__13);
v___x_213_ = lean_array_push(v___x_212_, v___x_211_);
return v___x_213_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__20(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_214_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__19, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__19_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__19);
v___x_215_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11));
v___x_216_ = lean_box(2);
v___x_217_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v___x_215_);
lean_ctor_set(v___x_217_, 2, v___x_214_);
return v___x_217_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__21(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_218_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__20, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__20_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__20);
v___x_219_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5));
v___x_220_ = lean_array_push(v___x_219_, v___x_218_);
return v___x_220_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__22(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_221_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__21, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__21_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__21);
v___x_222_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__9));
v___x_223_ = lean_box(2);
v___x_224_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set(v___x_224_, 1, v___x_222_);
lean_ctor_set(v___x_224_, 2, v___x_221_);
return v___x_224_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__23(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_225_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__22, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__22_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__22);
v___x_226_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5));
v___x_227_ = lean_array_push(v___x_226_, v___x_225_);
return v___x_227_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__24(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_228_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__23, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__23_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__23);
v___x_229_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7));
v___x_230_ = lean_box(2);
v___x_231_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v___x_229_);
lean_ctor_set(v___x_231_, 2, v___x_228_);
return v___x_231_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__25(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_232_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__24, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__24_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__24);
v___x_233_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5));
v___x_234_ = lean_array_push(v___x_233_, v___x_232_);
return v___x_234_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__26(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_235_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__25, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__25_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__25);
v___x_236_ = ((lean_object*)(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4));
v___x_237_ = lean_box(2);
v___x_238_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set(v___x_238_, 1, v___x_236_);
lean_ctor_set(v___x_238_, 2, v___x_235_);
return v___x_238_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofNat___auto__1(void){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__26, &l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__26_once, _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__26);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofNat___redArg(lean_object* v_data_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = lean_nat_to_int(v_data_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofNat(lean_object* v_data_242_, lean_object* v_h_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = lean_nat_to_int(v_data_242_);
return v___x_244_;
}
}
static lean_object* _init_l_Std_Time_Week_Ordinal_ofFin___closed__0(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_unsigned_to_nat(1u);
v___x_246_ = lean_nat_to_int(v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_ofFin(lean_object* v_data_247_){
_start:
{
lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_248_ = lean_unsigned_to_nat(1u);
v___x_249_ = lean_nat_dec_le(v___x_248_, v_data_247_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; 
lean_dec(v_data_247_);
v___x_250_ = lean_obj_once(&l_Std_Time_Week_Ordinal_ofFin___closed__0, &l_Std_Time_Week_Ordinal_ofFin___closed__0_once, _init_l_Std_Time_Week_Ordinal_ofFin___closed__0);
return v___x_250_;
}
else
{
lean_object* v___x_251_; 
v___x_251_ = lean_nat_to_int(v_data_247_);
return v___x_251_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_toOffset(lean_object* v_ordinal_252_){
_start:
{
lean_inc(v_ordinal_252_);
return v_ordinal_252_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Ordinal_toOffset___boxed(lean_object* v_ordinal_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Std_Time_Week_Ordinal_toOffset(v_ordinal_253_);
lean_dec(v_ordinal_253_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofNat(lean_object* v_data_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = lean_nat_to_int(v_data_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofInt(lean_object* v_data_257_){
_start:
{
lean_inc(v_data_257_);
return v_data_257_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofInt___boxed(lean_object* v_data_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Std_Time_Week_Offset_ofInt(v_data_258_);
lean_dec(v_data_258_);
return v_res_259_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_unsigned_to_nat(604800000u);
v___x_261_ = lean_nat_to_int(v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toMilliseconds(lean_object* v_weeks_262_){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = lean_obj_once(&l_Std_Time_Week_Offset_toMilliseconds___closed__0, &l_Std_Time_Week_Offset_toMilliseconds___closed__0_once, _init_l_Std_Time_Week_Offset_toMilliseconds___closed__0);
v___x_264_ = lean_int_mul(v_weeks_262_, v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toMilliseconds___boxed(lean_object* v_weeks_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Std_Time_Week_Offset_toMilliseconds(v_weeks_265_);
lean_dec(v_weeks_265_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofMilliseconds(lean_object* v_millis_267_){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_obj_once(&l_Std_Time_Week_Offset_toMilliseconds___closed__0, &l_Std_Time_Week_Offset_toMilliseconds___closed__0_once, _init_l_Std_Time_Week_Offset_toMilliseconds___closed__0);
v___x_269_ = lean_int_ediv(v_millis_267_, v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofMilliseconds___boxed(lean_object* v_millis_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Std_Time_Week_Offset_ofMilliseconds(v_millis_270_);
lean_dec(v_millis_270_);
return v_res_271_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toNanoseconds___closed__0(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_cstr_to_nat("604800000000000");
v___x_273_ = lean_nat_to_int(v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toNanoseconds(lean_object* v_weeks_274_){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_obj_once(&l_Std_Time_Week_Offset_toNanoseconds___closed__0, &l_Std_Time_Week_Offset_toNanoseconds___closed__0_once, _init_l_Std_Time_Week_Offset_toNanoseconds___closed__0);
v___x_276_ = lean_int_mul(v_weeks_274_, v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toNanoseconds___boxed(lean_object* v_weeks_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Std_Time_Week_Offset_toNanoseconds(v_weeks_277_);
lean_dec(v_weeks_277_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofNanoseconds(lean_object* v_nanos_279_){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = lean_obj_once(&l_Std_Time_Week_Offset_toNanoseconds___closed__0, &l_Std_Time_Week_Offset_toNanoseconds___closed__0_once, _init_l_Std_Time_Week_Offset_toNanoseconds___closed__0);
v___x_281_ = lean_int_ediv(v_nanos_279_, v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofNanoseconds___boxed(lean_object* v_nanos_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Std_Time_Week_Offset_ofNanoseconds(v_nanos_282_);
lean_dec(v_nanos_282_);
return v_res_283_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toSeconds___closed__0(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_unsigned_to_nat(604800u);
v___x_285_ = lean_nat_to_int(v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toSeconds(lean_object* v_weeks_286_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_obj_once(&l_Std_Time_Week_Offset_toSeconds___closed__0, &l_Std_Time_Week_Offset_toSeconds___closed__0_once, _init_l_Std_Time_Week_Offset_toSeconds___closed__0);
v___x_288_ = lean_int_mul(v_weeks_286_, v___x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toSeconds___boxed(lean_object* v_weeks_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Std_Time_Week_Offset_toSeconds(v_weeks_289_);
lean_dec(v_weeks_289_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofSeconds(lean_object* v_secs_291_){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = lean_obj_once(&l_Std_Time_Week_Offset_toSeconds___closed__0, &l_Std_Time_Week_Offset_toSeconds___closed__0_once, _init_l_Std_Time_Week_Offset_toSeconds___closed__0);
v___x_293_ = lean_int_ediv(v_secs_291_, v___x_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofSeconds___boxed(lean_object* v_secs_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Std_Time_Week_Offset_ofSeconds(v_secs_294_);
lean_dec(v_secs_294_);
return v_res_295_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toMinutes___closed__0(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_unsigned_to_nat(10080u);
v___x_297_ = lean_nat_to_int(v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toMinutes(lean_object* v_weeks_298_){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = lean_obj_once(&l_Std_Time_Week_Offset_toMinutes___closed__0, &l_Std_Time_Week_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Week_Offset_toMinutes___closed__0);
v___x_300_ = lean_int_mul(v_weeks_298_, v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toMinutes___boxed(lean_object* v_weeks_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Std_Time_Week_Offset_toMinutes(v_weeks_301_);
lean_dec(v_weeks_301_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofMinutes(lean_object* v_minutes_303_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_obj_once(&l_Std_Time_Week_Offset_toMinutes___closed__0, &l_Std_Time_Week_Offset_toMinutes___closed__0_once, _init_l_Std_Time_Week_Offset_toMinutes___closed__0);
v___x_305_ = lean_int_ediv(v_minutes_303_, v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofMinutes___boxed(lean_object* v_minutes_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Std_Time_Week_Offset_ofMinutes(v_minutes_306_);
lean_dec(v_minutes_306_);
return v_res_307_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toHours___closed__0(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_unsigned_to_nat(168u);
v___x_309_ = lean_nat_to_int(v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toHours(lean_object* v_weeks_310_){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = lean_obj_once(&l_Std_Time_Week_Offset_toHours___closed__0, &l_Std_Time_Week_Offset_toHours___closed__0_once, _init_l_Std_Time_Week_Offset_toHours___closed__0);
v___x_312_ = lean_int_mul(v_weeks_310_, v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toHours___boxed(lean_object* v_weeks_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Std_Time_Week_Offset_toHours(v_weeks_313_);
lean_dec(v_weeks_313_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofHours(lean_object* v_hours_315_){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_obj_once(&l_Std_Time_Week_Offset_toHours___closed__0, &l_Std_Time_Week_Offset_toHours___closed__0_once, _init_l_Std_Time_Week_Offset_toHours___closed__0);
v___x_317_ = lean_int_ediv(v_hours_315_, v___x_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofHours___boxed(lean_object* v_hours_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Std_Time_Week_Offset_ofHours(v_hours_318_);
lean_dec(v_hours_318_);
return v_res_319_;
}
}
static lean_object* _init_l_Std_Time_Week_Offset_toDays___closed__0(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_unsigned_to_nat(7u);
v___x_321_ = lean_nat_to_int(v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toDays(lean_object* v_weeks_322_){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_obj_once(&l_Std_Time_Week_Offset_toDays___closed__0, &l_Std_Time_Week_Offset_toDays___closed__0_once, _init_l_Std_Time_Week_Offset_toDays___closed__0);
v___x_324_ = lean_int_mul(v_weeks_322_, v___x_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_toDays___boxed(lean_object* v_weeks_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Std_Time_Week_Offset_toDays(v_weeks_325_);
lean_dec(v_weeks_325_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofDays(lean_object* v_days_327_){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = lean_obj_once(&l_Std_Time_Week_Offset_toDays___closed__0, &l_Std_Time_Week_Offset_toDays___closed__0_once, _init_l_Std_Time_Week_Offset_toDays___closed__0);
v___x_329_ = lean_int_ediv(v_days_327_, v___x_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Week_Offset_ofDays___boxed(lean_object* v_days_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Std_Time_Week_Offset_ofDays(v_days_330_);
lean_dec(v_days_330_);
return v_res_331_;
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
l_Std_Time_Week_instInhabitedOffset = _init_l_Std_Time_Week_instInhabitedOffset();
lean_mark_persistent(l_Std_Time_Week_instInhabitedOffset);
l_Std_Time_Week_instAddOffset = _init_l_Std_Time_Week_instAddOffset();
lean_mark_persistent(l_Std_Time_Week_instAddOffset);
l_Std_Time_Week_instSubOffset = _init_l_Std_Time_Week_instSubOffset();
lean_mark_persistent(l_Std_Time_Week_instSubOffset);
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
