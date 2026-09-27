// Lean compiler output
// Module: Lean.Data.Json.Basic
// Imports: public import Init.Data.Range public import Init.Data.OfScientific public import Init.Data.Hashable public import Std.Data.TreeMap.Raw.Basic public import Init.Data.Ord.String import Init.Data.Range.Polymorphic.Iterators import Init.Data.Range.Polymorphic.Nat import Init.Data.String.Substring import Init.Data.ToString.Macro
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
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_string_compare(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_float_to_string(double);
lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Substring_Raw_nextn(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
double lean_float_negate(double);
uint8_t lean_float_isnan(double);
uint8_t lean_float_isinf(double);
uint8_t lean_float_beq(double, double);
uint8_t lean_float_decLt(double, double);
double lean_float_of_nat(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
double lean_float_mul(double, double);
LEAN_EXPORT uint8_t l_Lean_instDecidableEqJsonNumber_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instDecidableEqJsonNumber_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instDecidableEqJsonNumber(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instDecidableEqJsonNumber___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instHashableJsonNumber_hash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instHashableJsonNumber_hash___closed__0;
LEAN_EXPORT uint64_t l_Lean_instHashableJsonNumber_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableJsonNumber_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_instHashableJsonNumber___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableJsonNumber_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instHashableJsonNumber___closed__0 = (const lean_object*)&l_Lean_instHashableJsonNumber___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instHashableJsonNumber = (const lean_object*)&l_Lean_instHashableJsonNumber___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_JsonNumber_fromNat_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
static const lean_closure_object l_Lean_JsonNumber_instCoeNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_JsonNumber_fromNat, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_JsonNumber_instCoeNat___closed__0 = (const lean_object*)&l_Lean_JsonNumber_instCoeNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_JsonNumber_instCoeNat = (const lean_object*)&l_Lean_JsonNumber_instCoeNat___closed__0_value;
static const lean_closure_object l_Lean_JsonNumber_instCoeInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_JsonNumber_fromInt, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_JsonNumber_instCoeInt___closed__0 = (const lean_object*)&l_Lean_JsonNumber_instCoeInt___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_JsonNumber_instCoeInt = (const lean_object*)&l_Lean_JsonNumber_instCoeInt___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOfNat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_JsonNumber_normalize___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonNumber_normalize___closed__0;
static lean_once_cell_t l_Lean_JsonNumber_normalize___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonNumber_normalize___closed__1;
static lean_once_cell_t l_Lean_JsonNumber_normalize___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonNumber_normalize___closed__2;
static lean_once_cell_t l_Lean_JsonNumber_normalize___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonNumber_normalize___closed__3;
LEAN_EXPORT lean_object* l_Lean_JsonNumber_normalize(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonNumber_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_ltProp;
LEAN_EXPORT uint8_t l_Lean_JsonNumber_instDecidableLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instDecidableLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonNumber_instOrd___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOrd___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_JsonNumber_instOrd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_JsonNumber_instOrd___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_JsonNumber_instOrd___closed__0 = (const lean_object*)&l_Lean_JsonNumber_instOrd___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_JsonNumber_instOrd = (const lean_object*)&l_Lean_JsonNumber_instOrd___closed__0_value;
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_JsonNumber_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_JsonNumber_toString___closed__0 = (const lean_object*)&l_Lean_JsonNumber_toString___closed__0_value;
static const lean_string_object l_Lean_JsonNumber_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "e"};
static const lean_object* l_Lean_JsonNumber_toString___closed__1 = (const lean_object*)&l_Lean_JsonNumber_toString___closed__1_value;
static const lean_string_object l_Lean_JsonNumber_toString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_JsonNumber_toString___closed__2 = (const lean_object*)&l_Lean_JsonNumber_toString___closed__2_value;
static lean_once_cell_t l_Lean_JsonNumber_toString___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonNumber_toString___closed__3;
static const lean_string_object l_Lean_JsonNumber_toString___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_JsonNumber_toString___closed__4 = (const lean_object*)&l_Lean_JsonNumber_toString___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_JsonNumber_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_JsonNumber_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_JsonNumber_toString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_JsonNumber_instToString___closed__0 = (const lean_object*)&l_Lean_JsonNumber_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_JsonNumber_instToString = (const lean_object*)&l_Lean_JsonNumber_instToString___closed__0_value;
static const lean_string_object l_Lean_JsonNumber_instRepr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l_Lean_JsonNumber_instRepr___lam__0___closed__0 = (const lean_object*)&l_Lean_JsonNumber_instRepr___lam__0___closed__0_value;
static const lean_string_object l_Lean_JsonNumber_instRepr___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_JsonNumber_instRepr___lam__0___closed__1 = (const lean_object*)&l_Lean_JsonNumber_instRepr___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_JsonNumber_instRepr___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_JsonNumber_instRepr___lam__0___closed__1_value)}};
static const lean_object* l_Lean_JsonNumber_instRepr___lam__0___closed__2 = (const lean_object*)&l_Lean_JsonNumber_instRepr___lam__0___closed__2_value;
static const lean_string_object l_Lean_JsonNumber_instRepr___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l_Lean_JsonNumber_instRepr___lam__0___closed__3 = (const lean_object*)&l_Lean_JsonNumber_instRepr___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_JsonNumber_instRepr___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonNumber_instRepr___lam__0___closed__4;
static lean_once_cell_t l_Lean_JsonNumber_instRepr___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonNumber_instRepr___lam__0___closed__5;
static const lean_ctor_object l_Lean_JsonNumber_instRepr___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_JsonNumber_instRepr___lam__0___closed__0_value)}};
static const lean_object* l_Lean_JsonNumber_instRepr___lam__0___closed__6 = (const lean_object*)&l_Lean_JsonNumber_instRepr___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_JsonNumber_instRepr___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_JsonNumber_instRepr___lam__0___closed__3_value)}};
static const lean_object* l_Lean_JsonNumber_instRepr___lam__0___closed__7 = (const lean_object*)&l_Lean_JsonNumber_instRepr___lam__0___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instRepr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instRepr___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_JsonNumber_instRepr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_JsonNumber_instRepr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_JsonNumber_instRepr___closed__0 = (const lean_object*)&l_Lean_JsonNumber_instRepr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_JsonNumber_instRepr = (const lean_object*)&l_Lean_JsonNumber_instRepr___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOfScientific___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOfScientific___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_JsonNumber_instOfScientific___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_JsonNumber_instOfScientific___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_JsonNumber_instOfScientific___closed__0 = (const lean_object*)&l_Lean_JsonNumber_instOfScientific___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_JsonNumber_instOfScientific = (const lean_object*)&l_Lean_JsonNumber_instOfScientific___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instNeg___lam__0(lean_object*);
static const lean_closure_object l_Lean_JsonNumber_instNeg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_JsonNumber_instNeg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_JsonNumber_instNeg___closed__0 = (const lean_object*)&l_Lean_JsonNumber_instNeg___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_JsonNumber_instNeg = (const lean_object*)&l_Lean_JsonNumber_instNeg___closed__0_value;
static lean_once_cell_t l_Lean_JsonNumber_instInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonNumber_instInhabited___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instInhabited;
static lean_once_cell_t l_Lean_JsonNumber_toFloat___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_JsonNumber_toFloat___closed__0;
static lean_once_cell_t l_Lean_JsonNumber_toFloat___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_JsonNumber_toFloat___closed__1;
LEAN_EXPORT double l_Lean_JsonNumber_toFloat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_toFloat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Data.Json.Basic"};
static const lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0 = (const lean_object*)&l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0_value;
static const lean_string_object l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "_private.Lean.Data.Json.Basic.0.Lean.JsonNumber.fromPositiveFloat!"};
static const lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__1 = (const lean_object*)&l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__1_value;
static const lean_string_object l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Failed to parse "};
static const lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__2 = (const lean_object*)&l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(double);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___boxed(lean_object*);
static lean_once_cell_t l_Lean_JsonNumber_fromFloat_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_JsonNumber_fromFloat_x3f___closed__0;
static lean_once_cell_t l_Lean_JsonNumber_fromFloat_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonNumber_fromFloat_x3f___closed__1;
static lean_once_cell_t l_Lean_JsonNumber_fromFloat_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_JsonNumber_fromFloat_x3f___closed__2;
static const lean_string_object l_Lean_JsonNumber_fromFloat_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "-Infinity"};
static const lean_object* l_Lean_JsonNumber_fromFloat_x3f___closed__3 = (const lean_object*)&l_Lean_JsonNumber_fromFloat_x3f___closed__3_value;
static const lean_ctor_object l_Lean_JsonNumber_fromFloat_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_JsonNumber_fromFloat_x3f___closed__3_value)}};
static const lean_object* l_Lean_JsonNumber_fromFloat_x3f___closed__4 = (const lean_object*)&l_Lean_JsonNumber_fromFloat_x3f___closed__4_value;
static const lean_string_object l_Lean_JsonNumber_fromFloat_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Infinity"};
static const lean_object* l_Lean_JsonNumber_fromFloat_x3f___closed__5 = (const lean_object*)&l_Lean_JsonNumber_fromFloat_x3f___closed__5_value;
static const lean_ctor_object l_Lean_JsonNumber_fromFloat_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_JsonNumber_fromFloat_x3f___closed__5_value)}};
static const lean_object* l_Lean_JsonNumber_fromFloat_x3f___closed__6 = (const lean_object*)&l_Lean_JsonNumber_fromFloat_x3f___closed__6_value;
static const lean_string_object l_Lean_JsonNumber_fromFloat_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "NaN"};
static const lean_object* l_Lean_JsonNumber_fromFloat_x3f___closed__7 = (const lean_object*)&l_Lean_JsonNumber_fromFloat_x3f___closed__7_value;
static const lean_ctor_object l_Lean_JsonNumber_fromFloat_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_JsonNumber_fromFloat_x3f___closed__7_value)}};
static const lean_object* l_Lean_JsonNumber_fromFloat_x3f___closed__8 = (const lean_object*)&l_Lean_JsonNumber_fromFloat_x3f___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_JsonNumber_fromFloat_x3f(double);
LEAN_EXPORT lean_object* l_Lean_JsonNumber_fromFloat_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_strLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_strLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_null_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_null_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_bool_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_bool_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_num_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_num_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_str_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_str_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_arr_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_arr_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_obj_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_obj_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedJson_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedJson;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__0_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__1_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__2_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__2_value)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__3 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__3_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Json_instBEq___private__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_instBEq___private__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Json_instBEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_instBEq___private__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Json_instBEq___closed__0 = (const lean_object*)&l_Lean_Json_instBEq___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Json_instBEq = (const lean_object*)&l_Lean_Json_instBEq___closed__0_value;
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT uint64_t l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(lean_object*);
LEAN_EXPORT uint64_t l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Json_instHashable___private__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_instHashable___private__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Json_instHashable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_instHashable___private__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Json_instHashable___closed__0 = (const lean_object*)&l_Lean_Json_instHashable___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Json_instHashable = (const lean_object*)&l_Lean_Json_instHashable___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_mkObj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_instCoeNat___lam__0(lean_object*);
static const lean_closure_object l_Lean_Json_instCoeNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_instCoeNat___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Json_instCoeNat___closed__0 = (const lean_object*)&l_Lean_Json_instCoeNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Json_instCoeNat = (const lean_object*)&l_Lean_Json_instCoeNat___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_instCoeInt___lam__0(lean_object*);
static const lean_closure_object l_Lean_Json_instCoeInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_instCoeInt___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Json_instCoeInt___closed__0 = (const lean_object*)&l_Lean_Json_instCoeInt___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Json_instCoeInt = (const lean_object*)&l_Lean_Json_instCoeInt___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_instCoeString___lam__0(lean_object*);
static const lean_closure_object l_Lean_Json_instCoeString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_instCoeString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Json_instCoeString___closed__0 = (const lean_object*)&l_Lean_Json_instCoeString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Json_instCoeString = (const lean_object*)&l_Lean_Json_instCoeString___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_instCoeBool___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Json_instCoeBool___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Json_instCoeBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_instCoeBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Json_instCoeBool___closed__0 = (const lean_object*)&l_Lean_Json_instCoeBool___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Json_instCoeBool = (const lean_object*)&l_Lean_Json_instCoeBool___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_instOfNat(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Json_isNull(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_isNull___boxed(lean_object*);
static const lean_string_object l_Lean_Json_getObj_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "object expected"};
static const lean_object* l_Lean_Json_getObj_x3f___closed__0 = (const lean_object*)&l_Lean_Json_getObj_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Json_getObj_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Json_getObj_x3f___closed__0_value)}};
static const lean_object* l_Lean_Json_getObj_x3f___closed__1 = (const lean_object*)&l_Lean_Json_getObj_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObj_x3f(lean_object*);
static const lean_string_object l_Lean_Json_getArr_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "array expected"};
static const lean_object* l_Lean_Json_getArr_x3f___closed__0 = (const lean_object*)&l_Lean_Json_getArr_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Json_getArr_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Json_getArr_x3f___closed__0_value)}};
static const lean_object* l_Lean_Json_getArr_x3f___closed__1 = (const lean_object*)&l_Lean_Json_getArr_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Json_getArr_x3f(lean_object*);
static const lean_string_object l_Lean_Json_getStr_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "String expected"};
static const lean_object* l_Lean_Json_getStr_x3f___closed__0 = (const lean_object*)&l_Lean_Json_getStr_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Json_getStr_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Json_getStr_x3f___closed__0_value)}};
static const lean_object* l_Lean_Json_getStr_x3f___closed__1 = (const lean_object*)&l_Lean_Json_getStr_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Json_getStr_x3f(lean_object*);
static const lean_string_object l_Lean_Json_getNat_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Natural number expected"};
static const lean_object* l_Lean_Json_getNat_x3f___closed__0 = (const lean_object*)&l_Lean_Json_getNat_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Json_getNat_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Json_getNat_x3f___closed__0_value)}};
static const lean_object* l_Lean_Json_getNat_x3f___closed__1 = (const lean_object*)&l_Lean_Json_getNat_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Json_getNat_x3f(lean_object*);
static const lean_string_object l_Lean_Json_getInt_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Integer expected"};
static const lean_object* l_Lean_Json_getInt_x3f___closed__0 = (const lean_object*)&l_Lean_Json_getInt_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Json_getInt_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Json_getInt_x3f___closed__0_value)}};
static const lean_object* l_Lean_Json_getInt_x3f___closed__1 = (const lean_object*)&l_Lean_Json_getInt_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Json_getInt_x3f(lean_object*);
static const lean_string_object l_Lean_Json_getBool_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Bool expected"};
static const lean_object* l_Lean_Json_getBool_x3f___closed__0 = (const lean_object*)&l_Lean_Json_getBool_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Json_getBool_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Json_getBool_x3f___closed__0_value)}};
static const lean_object* l_Lean_Json_getBool_x3f___closed__1 = (const lean_object*)&l_Lean_Json_getBool_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Json_getBool_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getBool_x3f___boxed(lean_object*);
static const lean_string_object l_Lean_Json_getNum_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "number expected"};
static const lean_object* l_Lean_Json_getNum_x3f___closed__0 = (const lean_object*)&l_Lean_Json_getNum_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Json_getNum_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Json_getNum_x3f___closed__0_value)}};
static const lean_object* l_Lean_Json_getNum_x3f___closed__1 = (const lean_object*)&l_Lean_Json_getNum_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Json_getNum_x3f(lean_object*);
static const lean_string_object l_Lean_Json_getObjVal_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "property not found: "};
static const lean_object* l_Lean_Json_getObjVal_x3f___closed__0 = (const lean_object*)&l_Lean_Json_getObjVal_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Json_getObjVal_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Json_getObj_x3f___closed__0_value)}};
static const lean_object* l_Lean_Json_getObjVal_x3f___closed__1 = (const lean_object*)&l_Lean_Json_getObjVal_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjVal_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjVal_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Json_getArrVal_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "index out of bounds: "};
static const lean_object* l_Lean_Json_getArrVal_x3f___closed__0 = (const lean_object*)&l_Lean_Json_getArrVal_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Json_getArrVal_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Json_getArr_x3f___closed__0_value)}};
static const lean_object* l_Lean_Json_getArrVal_x3f___closed__1 = (const lean_object*)&l_Lean_Json_getArrVal_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Json_getArrVal_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValD___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Json_setObjVal_x21_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Data.DTreeMap.Internal.Balancing"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceL!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceL! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceR!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceR! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Json_setObjVal_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Json.setObjVal!"};
static const lean_object* l_Lean_Json_setObjVal_x21___closed__0 = (const lean_object*)&l_Lean_Json_setObjVal_x21___closed__0_value;
static const lean_string_object l_Lean_Json_setObjVal_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Json.setObjVal!: not an object: {j}"};
static const lean_object* l_Lean_Json_setObjVal_x21___closed__1 = (const lean_object*)&l_Lean_Json_setObjVal_x21___closed__1_value;
static lean_once_cell_t l_Lean_Json_setObjVal_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Json_setObjVal_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Json_setObjVal_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_mergeObj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Structured_arr_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Structured_arr_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Structured_obj_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Structured_obj_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_instCoeArrayStructured___lam__0(lean_object*);
static const lean_closure_object l_Lean_Json_instCoeArrayStructured___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_instCoeArrayStructured___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Json_instCoeArrayStructured___closed__0 = (const lean_object*)&l_Lean_Json_instCoeArrayStructured___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Json_instCoeArrayStructured = (const lean_object*)&l_Lean_Json_instCoeArrayStructured___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_instCoeRawStringStructured___lam__0(lean_object*);
static const lean_closure_object l_Lean_Json_instCoeRawStringStructured___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_instCoeRawStringStructured___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Json_instCoeRawStringStructured___closed__0 = (const lean_object*)&l_Lean_Json_instCoeRawStringStructured___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Json_instCoeRawStringStructured = (const lean_object*)&l_Lean_Json_instCoeRawStringStructured___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_instDecidableEqJsonNumber_decEq(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_mantissa_3_; lean_object* v_exponent_4_; lean_object* v_mantissa_5_; lean_object* v_exponent_6_; uint8_t v___x_7_; 
v_mantissa_3_ = lean_ctor_get(v_x_1_, 0);
v_exponent_4_ = lean_ctor_get(v_x_1_, 1);
v_mantissa_5_ = lean_ctor_get(v_x_2_, 0);
v_exponent_6_ = lean_ctor_get(v_x_2_, 1);
v___x_7_ = lean_int_dec_eq(v_mantissa_3_, v_mantissa_5_);
if (v___x_7_ == 0)
{
return v___x_7_;
}
else
{
uint8_t v___x_8_; 
v___x_8_ = lean_nat_dec_eq(v_exponent_4_, v_exponent_6_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instDecidableEqJsonNumber_decEq___boxed(lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Lean_instDecidableEqJsonNumber_decEq(v_x_9_, v_x_10_);
lean_dec_ref(v_x_10_);
lean_dec_ref(v_x_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT uint8_t l_Lean_instDecidableEqJsonNumber(lean_object* v_x_13_, lean_object* v_x_14_){
_start:
{
uint8_t v___x_15_; 
v___x_15_ = l_Lean_instDecidableEqJsonNumber_decEq(v_x_13_, v_x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_instDecidableEqJsonNumber___boxed(lean_object* v_x_16_, lean_object* v_x_17_){
_start:
{
uint8_t v_res_18_; lean_object* v_r_19_; 
v_res_18_ = l_Lean_instDecidableEqJsonNumber(v_x_16_, v_x_17_);
lean_dec_ref(v_x_17_);
lean_dec_ref(v_x_16_);
v_r_19_ = lean_box(v_res_18_);
return v_r_19_;
}
}
static lean_object* _init_l_Lean_instHashableJsonNumber_hash___closed__0(void){
_start:
{
lean_object* v_natZero_20_; lean_object* v_intZero_21_; 
v_natZero_20_ = lean_unsigned_to_nat(0u);
v_intZero_21_ = lean_nat_to_int(v_natZero_20_);
return v_intZero_21_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableJsonNumber_hash(lean_object* v_x_22_){
_start:
{
lean_object* v_mantissa_23_; lean_object* v_exponent_24_; uint64_t v___x_25_; uint64_t v___y_27_; lean_object* v_intZero_31_; uint8_t v_isNeg_32_; 
v_mantissa_23_ = lean_ctor_get(v_x_22_, 0);
v_exponent_24_ = lean_ctor_get(v_x_22_, 1);
v___x_25_ = 0ULL;
v_intZero_31_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v_isNeg_32_ = lean_int_dec_lt(v_mantissa_23_, v_intZero_31_);
if (v_isNeg_32_ == 0)
{
lean_object* v_a_33_; lean_object* v___x_34_; lean_object* v___x_35_; uint64_t v___x_36_; 
v_a_33_ = lean_nat_abs(v_mantissa_23_);
v___x_34_ = lean_unsigned_to_nat(2u);
v___x_35_ = lean_nat_mul(v___x_34_, v_a_33_);
lean_dec(v_a_33_);
v___x_36_ = lean_uint64_of_nat(v___x_35_);
lean_dec(v___x_35_);
v___y_27_ = v___x_36_;
goto v___jp_26_;
}
else
{
lean_object* v_abs_37_; lean_object* v_one_38_; lean_object* v_a_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; uint64_t v___x_43_; 
v_abs_37_ = lean_nat_abs(v_mantissa_23_);
v_one_38_ = lean_unsigned_to_nat(1u);
v_a_39_ = lean_nat_sub(v_abs_37_, v_one_38_);
lean_dec(v_abs_37_);
v___x_40_ = lean_unsigned_to_nat(2u);
v___x_41_ = lean_nat_mul(v___x_40_, v_a_39_);
lean_dec(v_a_39_);
v___x_42_ = lean_nat_add(v___x_41_, v_one_38_);
lean_dec(v___x_41_);
v___x_43_ = lean_uint64_of_nat(v___x_42_);
lean_dec(v___x_42_);
v___y_27_ = v___x_43_;
goto v___jp_26_;
}
v___jp_26_:
{
uint64_t v___x_28_; uint64_t v___x_29_; uint64_t v___x_30_; 
v___x_28_ = lean_uint64_mix_hash(v___x_25_, v___y_27_);
v___x_29_ = lean_uint64_of_nat(v_exponent_24_);
v___x_30_ = lean_uint64_mix_hash(v___x_28_, v___x_29_);
return v___x_30_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableJsonNumber_hash___boxed(lean_object* v_x_44_){
_start:
{
uint64_t v_res_45_; lean_object* v_r_46_; 
v_res_45_ = l_Lean_instHashableJsonNumber_hash(v_x_44_);
lean_dec_ref(v_x_44_);
v_r_46_ = lean_box_uint64(v_res_45_);
return v_r_46_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_JsonNumber_fromNat_spec__0(lean_object* v_a_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lean_nat_to_int(v_a_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_fromNat(lean_object* v_n_51_){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = lean_nat_to_int(v_n_51_);
v___x_53_ = lean_unsigned_to_nat(0u);
v___x_54_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_52_);
lean_ctor_set(v___x_54_, 1, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_fromInt(lean_object* v_n_55_){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lean_unsigned_to_nat(0u);
v___x_57_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_57_, 0, v_n_55_);
lean_ctor_set(v___x_57_, 1, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOfNat(lean_object* v_n_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_JsonNumber_fromNat(v_n_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits_loop(lean_object* v_n_64_, lean_object* v_digits_65_){
_start:
{
lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_66_ = lean_unsigned_to_nat(9u);
v___x_67_ = lean_nat_dec_le(v_n_64_, v___x_66_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_68_ = lean_unsigned_to_nat(10u);
v___x_69_ = lean_nat_div(v_n_64_, v___x_68_);
lean_dec(v_n_64_);
v___x_70_ = lean_unsigned_to_nat(1u);
v___x_71_ = lean_nat_add(v_digits_65_, v___x_70_);
lean_dec(v_digits_65_);
v_n_64_ = v___x_69_;
v_digits_65_ = v___x_71_;
goto _start;
}
else
{
lean_dec(v_n_64_);
return v_digits_65_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(lean_object* v_n_73_){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_unsigned_to_nat(1u);
v___x_75_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits_loop(v_n_73_, v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0___redArg(lean_object* v_upperBound_76_, lean_object* v_a_77_, lean_object* v_b_78_){
_start:
{
uint8_t v___x_79_; 
v___x_79_ = lean_nat_dec_lt(v_a_77_, v_upperBound_76_);
if (v___x_79_ == 0)
{
lean_dec(v_a_77_);
return v_b_78_;
}
else
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = lean_unsigned_to_nat(10u);
v___x_82_ = lean_nat_mod(v_b_78_, v___x_81_);
v___x_83_ = lean_nat_dec_eq(v___x_82_, v___x_80_);
lean_dec(v___x_82_);
if (v___x_83_ == 0)
{
lean_dec(v_a_77_);
return v_b_78_;
}
else
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_84_ = lean_nat_div(v_b_78_, v___x_81_);
lean_dec(v_b_78_);
v___x_85_ = lean_unsigned_to_nat(1u);
v___x_86_ = lean_nat_add(v_a_77_, v___x_85_);
lean_dec(v_a_77_);
v_a_77_ = v___x_86_;
v_b_78_ = v___x_84_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0___redArg___boxed(lean_object* v_upperBound_88_, lean_object* v_a_89_, lean_object* v_b_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0___redArg(v_upperBound_88_, v_a_89_, v_b_90_);
lean_dec(v_upperBound_88_);
return v_res_91_;
}
}
static lean_object* _init_l_Lean_JsonNumber_normalize___closed__0(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = lean_unsigned_to_nat(1u);
v___x_93_ = lean_nat_to_int(v___x_92_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_JsonNumber_normalize___closed__1(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_obj_once(&l_Lean_JsonNumber_normalize___closed__0, &l_Lean_JsonNumber_normalize___closed__0_once, _init_l_Lean_JsonNumber_normalize___closed__0);
v___x_95_ = lean_int_neg(v___x_94_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_JsonNumber_normalize___closed__2(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v___x_97_ = lean_unsigned_to_nat(0u);
v___x_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v___x_96_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_JsonNumber_normalize___closed__3(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_99_ = lean_obj_once(&l_Lean_JsonNumber_normalize___closed__2, &l_Lean_JsonNumber_normalize___closed__2_once, _init_l_Lean_JsonNumber_normalize___closed__2);
v___x_100_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v___x_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v___x_99_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_normalize(lean_object* v_x_102_){
_start:
{
lean_object* v_mantissa_103_; lean_object* v_exponent_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_128_; 
v_mantissa_103_ = lean_ctor_get(v_x_102_, 0);
v_exponent_104_ = lean_ctor_get(v_x_102_, 1);
v_isSharedCheck_128_ = !lean_is_exclusive(v_x_102_);
if (v_isSharedCheck_128_ == 0)
{
v___x_106_ = v_x_102_;
v_isShared_107_ = v_isSharedCheck_128_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_exponent_104_);
lean_inc(v_mantissa_103_);
lean_dec(v_x_102_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_128_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_108_; lean_object* v___y_110_; lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_108_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v___x_123_ = lean_int_dec_eq(v_mantissa_103_, v___x_122_);
if (v___x_123_ == 0)
{
uint8_t v___x_124_; 
v___x_124_ = lean_int_dec_lt(v___x_122_, v_mantissa_103_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; 
v___x_125_ = lean_obj_once(&l_Lean_JsonNumber_normalize___closed__1, &l_Lean_JsonNumber_normalize___closed__1_once, _init_l_Lean_JsonNumber_normalize___closed__1);
v___y_110_ = v___x_125_;
goto v___jp_109_;
}
else
{
lean_object* v___x_126_; 
v___x_126_ = lean_obj_once(&l_Lean_JsonNumber_normalize___closed__0, &l_Lean_JsonNumber_normalize___closed__0_once, _init_l_Lean_JsonNumber_normalize___closed__0);
v___y_110_ = v___x_126_;
goto v___jp_109_;
}
}
else
{
lean_object* v___x_127_; 
lean_del_object(v___x_106_);
lean_dec(v_exponent_104_);
lean_dec(v_mantissa_103_);
v___x_127_ = lean_obj_once(&l_Lean_JsonNumber_normalize___closed__3, &l_Lean_JsonNumber_normalize___closed__3_once, _init_l_Lean_JsonNumber_normalize___closed__3);
return v___x_127_;
}
v___jp_109_:
{
lean_object* v_mAbs_111_; lean_object* v_nDigits_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_119_; 
v_mAbs_111_ = lean_nat_abs(v_mantissa_103_);
lean_dec(v_mantissa_103_);
lean_inc(v_mAbs_111_);
v_nDigits_112_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(v_mAbs_111_);
v___x_113_ = l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0___redArg(v_nDigits_112_, v___x_108_, v_mAbs_111_);
v___x_114_ = lean_nat_to_int(v_exponent_104_);
v___x_115_ = lean_int_neg(v___x_114_);
lean_dec(v___x_114_);
v___x_116_ = lean_nat_to_int(v_nDigits_112_);
v___x_117_ = lean_int_add(v___x_115_, v___x_116_);
lean_dec(v___x_116_);
lean_dec(v___x_115_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 1, v___x_117_);
lean_ctor_set(v___x_106_, 0, v___x_113_);
v___x_119_ = v___x_106_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_113_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v___x_117_);
v___x_119_ = v_reuseFailAlloc_121_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
lean_object* v___x_120_; 
lean_inc(v___y_110_);
v___x_120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_120_, 0, v___y_110_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
return v___x_120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0(lean_object* v_upperBound_129_, lean_object* v_inst_130_, lean_object* v_R_131_, lean_object* v_a_132_, lean_object* v_b_133_, lean_object* v_c_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0___redArg(v_upperBound_129_, v_a_132_, v_b_133_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0___boxed(lean_object* v_upperBound_136_, lean_object* v_inst_137_, lean_object* v_R_138_, lean_object* v_a_139_, lean_object* v_b_140_, lean_object* v_c_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0(v_upperBound_136_, v_inst_137_, v_R_138_, v_a_139_, v_b_140_, v_c_141_);
lean_dec(v_upperBound_136_);
return v_res_142_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonNumber_lt(lean_object* v_a_143_, lean_object* v_b_144_){
_start:
{
lean_object* v___y_146_; lean_object* v___y_147_; lean_object* v_fst_148_; lean_object* v_snd_149_; lean_object* v_fst_154_; lean_object* v_snd_155_; lean_object* v___x_171_; lean_object* v_fst_172_; lean_object* v_snd_173_; lean_object* v___x_174_; lean_object* v_fst_175_; lean_object* v_snd_176_; lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_171_ = l_Lean_JsonNumber_normalize(v_a_143_);
v_fst_172_ = lean_ctor_get(v___x_171_, 0);
lean_inc(v_fst_172_);
v_snd_173_ = lean_ctor_get(v___x_171_, 1);
lean_inc(v_snd_173_);
lean_dec_ref(v___x_171_);
v___x_174_ = l_Lean_JsonNumber_normalize(v_b_144_);
v_fst_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_fst_175_);
v_snd_176_ = lean_ctor_get(v___x_174_, 1);
lean_inc(v_snd_176_);
lean_dec_ref(v___x_174_);
v___x_181_ = lean_obj_once(&l_Lean_JsonNumber_normalize___closed__0, &l_Lean_JsonNumber_normalize___closed__0_once, _init_l_Lean_JsonNumber_normalize___closed__0);
v___x_182_ = lean_obj_once(&l_Lean_JsonNumber_normalize___closed__1, &l_Lean_JsonNumber_normalize___closed__1_once, _init_l_Lean_JsonNumber_normalize___closed__1);
v___x_183_ = lean_int_dec_eq(v_fst_172_, v___x_182_);
if (v___x_183_ == 0)
{
uint8_t v___x_184_; 
v___x_184_ = lean_int_dec_eq(v_fst_172_, v___x_181_);
if (v___x_184_ == 0)
{
goto v___jp_177_;
}
else
{
uint8_t v___x_185_; 
v___x_185_ = lean_int_dec_eq(v_fst_175_, v___x_182_);
if (v___x_185_ == 0)
{
goto v___jp_177_;
}
else
{
lean_dec(v_snd_176_);
lean_dec(v_fst_175_);
lean_dec(v_snd_173_);
lean_dec(v_fst_172_);
return v___x_183_;
}
}
}
else
{
uint8_t v___x_186_; 
v___x_186_ = lean_int_dec_eq(v_fst_175_, v___x_181_);
if (v___x_186_ == 0)
{
goto v___jp_177_;
}
else
{
lean_dec(v_snd_176_);
lean_dec(v_fst_175_);
lean_dec(v_snd_173_);
lean_dec(v_fst_172_);
return v___x_186_;
}
}
v___jp_145_:
{
uint8_t v___x_150_; 
v___x_150_ = lean_int_dec_lt(v___y_147_, v___y_146_);
if (v___x_150_ == 0)
{
uint8_t v___x_151_; 
v___x_151_ = lean_int_dec_lt(v___y_146_, v___y_147_);
lean_dec(v___y_147_);
lean_dec(v___y_146_);
if (v___x_151_ == 0)
{
uint8_t v___x_152_; 
v___x_152_ = lean_nat_dec_lt(v_fst_148_, v_snd_149_);
lean_dec(v_snd_149_);
lean_dec(v_fst_148_);
return v___x_152_;
}
else
{
lean_dec(v_snd_149_);
lean_dec(v_fst_148_);
return v___x_150_;
}
}
else
{
lean_dec(v_snd_149_);
lean_dec(v_fst_148_);
lean_dec(v___y_147_);
lean_dec(v___y_146_);
return v___x_150_;
}
}
v___jp_153_:
{
lean_object* v_fst_156_; lean_object* v_snd_157_; lean_object* v_fst_158_; lean_object* v_snd_159_; lean_object* v_amDigits_160_; lean_object* v_bmDigits_161_; uint8_t v___x_162_; 
v_fst_156_ = lean_ctor_get(v_fst_154_, 0);
lean_inc_n(v_fst_156_, 2);
v_snd_157_ = lean_ctor_get(v_fst_154_, 1);
lean_inc(v_snd_157_);
lean_dec_ref(v_fst_154_);
v_fst_158_ = lean_ctor_get(v_snd_155_, 0);
lean_inc_n(v_fst_158_, 2);
v_snd_159_ = lean_ctor_get(v_snd_155_, 1);
lean_inc(v_snd_159_);
lean_dec_ref(v_snd_155_);
v_amDigits_160_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(v_fst_156_);
v_bmDigits_161_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(v_fst_158_);
v___x_162_ = lean_nat_dec_lt(v_amDigits_160_, v_bmDigits_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_163_ = lean_unsigned_to_nat(10u);
v___x_164_ = lean_nat_sub(v_amDigits_160_, v_bmDigits_161_);
lean_dec(v_bmDigits_161_);
lean_dec(v_amDigits_160_);
v___x_165_ = lean_nat_pow(v___x_163_, v___x_164_);
lean_dec(v___x_164_);
v___x_166_ = lean_nat_mul(v_fst_158_, v___x_165_);
lean_dec(v___x_165_);
lean_dec(v_fst_158_);
v___y_146_ = v_snd_159_;
v___y_147_ = v_snd_157_;
v_fst_148_ = v_fst_156_;
v_snd_149_ = v___x_166_;
goto v___jp_145_;
}
else
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_167_ = lean_unsigned_to_nat(10u);
v___x_168_ = lean_nat_sub(v_bmDigits_161_, v_amDigits_160_);
lean_dec(v_amDigits_160_);
lean_dec(v_bmDigits_161_);
v___x_169_ = lean_nat_pow(v___x_167_, v___x_168_);
lean_dec(v___x_168_);
v___x_170_ = lean_nat_mul(v_fst_156_, v___x_169_);
lean_dec(v___x_169_);
lean_dec(v_fst_156_);
v___y_146_ = v_snd_159_;
v___y_147_ = v_snd_157_;
v_fst_148_ = v___x_170_;
v_snd_149_ = v_fst_158_;
goto v___jp_145_;
}
}
v___jp_177_:
{
lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_178_ = lean_obj_once(&l_Lean_JsonNumber_normalize___closed__1, &l_Lean_JsonNumber_normalize___closed__1_once, _init_l_Lean_JsonNumber_normalize___closed__1);
v___x_179_ = lean_int_dec_eq(v_fst_172_, v___x_178_);
lean_dec(v_fst_172_);
if (v___x_179_ == 0)
{
lean_dec(v_fst_175_);
v_fst_154_ = v_snd_173_;
v_snd_155_ = v_snd_176_;
goto v___jp_153_;
}
else
{
uint8_t v___x_180_; 
v___x_180_ = lean_int_dec_eq(v_fst_175_, v___x_178_);
lean_dec(v_fst_175_);
if (v___x_180_ == 0)
{
v_fst_154_ = v_snd_173_;
v_snd_155_ = v_snd_176_;
goto v___jp_153_;
}
else
{
v_fst_154_ = v_snd_176_;
v_snd_155_ = v_snd_173_;
goto v___jp_153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_lt___boxed(lean_object* v_a_187_, lean_object* v_b_188_){
_start:
{
uint8_t v_res_189_; lean_object* v_r_190_; 
v_res_189_ = l_Lean_JsonNumber_lt(v_a_187_, v_b_188_);
v_r_190_ = lean_box(v_res_189_);
return v_r_190_;
}
}
static lean_object* _init_l_Lean_JsonNumber_ltProp(void){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = lean_box(0);
return v___x_191_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonNumber_instDecidableLt(lean_object* v_a_192_, lean_object* v_b_193_){
_start:
{
uint8_t v___x_194_; 
v___x_194_ = l_Lean_JsonNumber_lt(v_a_192_, v_b_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instDecidableLt___boxed(lean_object* v_a_195_, lean_object* v_b_196_){
_start:
{
uint8_t v_res_197_; lean_object* v_r_198_; 
v_res_197_ = l_Lean_JsonNumber_instDecidableLt(v_a_195_, v_b_196_);
v_r_198_ = lean_box(v_res_197_);
return v_r_198_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonNumber_instOrd___lam__0(lean_object* v_x_199_, lean_object* v_y_200_){
_start:
{
uint8_t v___x_201_; 
lean_inc_ref(v_y_200_);
lean_inc_ref(v_x_199_);
v___x_201_ = l_Lean_JsonNumber_lt(v_x_199_, v_y_200_);
if (v___x_201_ == 0)
{
uint8_t v___x_202_; 
v___x_202_ = l_Lean_JsonNumber_lt(v_y_200_, v_x_199_);
if (v___x_202_ == 0)
{
uint8_t v___x_203_; 
v___x_203_ = 1;
return v___x_203_;
}
else
{
uint8_t v___x_204_; 
v___x_204_ = 2;
return v___x_204_;
}
}
else
{
uint8_t v___x_205_; 
lean_dec_ref(v_y_200_);
lean_dec_ref(v_x_199_);
v___x_205_ = 0;
return v___x_205_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOrd___lam__0___boxed(lean_object* v_x_206_, lean_object* v_y_207_){
_start:
{
uint8_t v_res_208_; lean_object* v_r_209_; 
v_res_208_ = l_Lean_JsonNumber_instOrd___lam__0(v_x_206_, v_y_207_);
v_r_209_ = lean_box(v_res_208_);
return v_r_209_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0(lean_object* v_s_212_, lean_object* v_begPos_213_, lean_object* v_i_214_){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_215_ = lean_unsigned_to_nat(1u);
v___x_216_ = lean_nat_add(v_begPos_213_, v___x_215_);
v___x_217_ = lean_nat_dec_le(v___x_216_, v_i_214_);
lean_dec(v___x_216_);
if (v___x_217_ == 0)
{
return v_i_214_;
}
else
{
lean_object* v_i_x27_218_; uint8_t v___y_220_; uint8_t v___y_223_; uint32_t v_c_224_; uint32_t v___x_225_; uint8_t v___x_226_; 
v_i_x27_218_ = lean_string_utf8_prev(v_s_212_, v_i_214_);
v_c_224_ = lean_string_utf8_get(v_s_212_, v_i_x27_218_);
v___x_225_ = 48;
v___x_226_ = lean_uint32_dec_eq(v_c_224_, v___x_225_);
if (v___x_226_ == 0)
{
v___y_223_ = v___x_217_;
goto v___jp_222_;
}
else
{
uint8_t v___x_227_; 
v___x_227_ = 0;
v___y_223_ = v___x_227_;
goto v___jp_222_;
}
v___jp_219_:
{
if (v___y_220_ == 0)
{
lean_dec(v_i_214_);
v_i_214_ = v_i_x27_218_;
goto _start;
}
else
{
lean_dec(v_i_x27_218_);
return v_i_214_;
}
}
v___jp_222_:
{
if (v___x_217_ == 0)
{
v___y_220_ = v___x_217_;
goto v___jp_219_;
}
else
{
v___y_220_ = v___y_223_;
goto v___jp_219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0___boxed(lean_object* v_s_228_, lean_object* v_begPos_229_, lean_object* v_i_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0(v_s_228_, v_begPos_229_, v_i_230_);
lean_dec(v_begPos_229_);
lean_dec_ref(v_s_228_);
return v_res_231_;
}
}
static lean_object* _init_l_Lean_JsonNumber_toString___closed__3(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = lean_unsigned_to_nat(9u);
v___x_236_ = lean_nat_to_int(v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_toString(lean_object* v_x_238_){
_start:
{
lean_object* v___y_240_; lean_object* v___y_241_; lean_object* v___y_242_; lean_object* v___y_243_; lean_object* v_mantissa_249_; lean_object* v_exponent_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v_mantissa_249_ = lean_ctor_get(v_x_238_, 0);
lean_inc(v_mantissa_249_);
v_exponent_250_ = lean_ctor_get(v_x_238_, 1);
lean_inc(v_exponent_250_);
lean_dec_ref(v_x_238_);
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_252_ = lean_nat_dec_eq(v_exponent_250_, v___x_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___y_255_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___y_274_; lean_object* v___y_275_; lean_object* v___y_276_; lean_object* v___y_288_; uint8_t v___x_297_; 
v___x_253_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v___x_297_ = lean_int_dec_le(v___x_253_, v_mantissa_249_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; 
v___x_298_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__4));
v___y_288_ = v___x_298_;
goto v___jp_287_;
}
else
{
lean_object* v___x_299_; 
v___x_299_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__2));
v___y_288_ = v___x_299_;
goto v___jp_287_;
}
v___jp_254_:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v_e_266_; lean_object* v_right_267_; uint8_t v___x_268_; 
v___x_260_ = lean_nat_add(v___y_257_, v___y_256_);
lean_dec(v___y_256_);
lean_dec(v___y_257_);
v___x_261_ = l_Nat_reprFast(v___x_260_);
v___x_262_ = lean_string_utf8_byte_size(v___x_261_);
lean_inc_ref(v___x_261_);
v___x_263_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_263_, 0, v___x_261_);
lean_ctor_set(v___x_263_, 1, v___x_251_);
lean_ctor_set(v___x_263_, 2, v___x_262_);
v___x_264_ = lean_unsigned_to_nat(1u);
v___x_265_ = l_Substring_Raw_nextn(v___x_263_, v___x_264_, v___x_251_);
lean_dec_ref_known(v___x_263_, 3);
v_e_266_ = l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0(v___x_261_, v___x_265_, v___x_262_);
v_right_267_ = lean_string_utf8_extract(v___x_261_, v___x_265_, v_e_266_);
lean_dec(v_e_266_);
lean_dec(v___x_265_);
lean_dec_ref(v___x_261_);
v___x_268_ = lean_int_dec_eq(v___y_258_, v___x_253_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_269_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__1));
v___x_270_ = l_Int_repr(v___y_258_);
lean_dec(v___y_258_);
v___x_271_ = lean_string_append(v___x_269_, v___x_270_);
lean_dec_ref(v___x_270_);
v___y_240_ = v___y_255_;
v___y_241_ = v_right_267_;
v___y_242_ = v___y_259_;
v___y_243_ = v___x_271_;
goto v___jp_239_;
}
else
{
lean_object* v___x_272_; 
lean_dec(v___y_258_);
v___x_272_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__2));
v___y_240_ = v___y_255_;
v___y_241_ = v_right_267_;
v___y_242_ = v___y_259_;
v___y_243_ = v___x_272_;
goto v___jp_239_;
}
}
v___jp_273_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v_e_x27_280_; lean_object* v___x_281_; lean_object* v_left_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_277_ = lean_unsigned_to_nat(10u);
v___x_278_ = lean_nat_abs(v___y_276_);
v___x_279_ = lean_nat_sub(v_exponent_250_, v___x_278_);
lean_dec(v___x_278_);
lean_dec(v_exponent_250_);
v_e_x27_280_ = lean_nat_pow(v___x_277_, v___x_279_);
lean_dec(v___x_279_);
v___x_281_ = lean_nat_div(v___y_274_, v_e_x27_280_);
v_left_282_ = l_Nat_reprFast(v___x_281_);
v___x_283_ = lean_nat_mod(v___y_274_, v_e_x27_280_);
lean_dec(v___y_274_);
v___x_284_ = lean_nat_dec_eq(v___x_283_, v___x_251_);
if (v___x_284_ == 0)
{
v___y_255_ = v___y_275_;
v___y_256_ = v___x_283_;
v___y_257_ = v_e_x27_280_;
v___y_258_ = v___y_276_;
v___y_259_ = v_left_282_;
goto v___jp_254_;
}
else
{
uint8_t v___x_285_; 
v___x_285_ = lean_int_dec_eq(v___y_276_, v___x_253_);
if (v___x_285_ == 0)
{
v___y_255_ = v___y_275_;
v___y_256_ = v___x_283_;
v___y_257_ = v_e_x27_280_;
v___y_258_ = v___y_276_;
v___y_259_ = v_left_282_;
goto v___jp_254_;
}
else
{
lean_object* v___x_286_; 
lean_dec(v___x_283_);
lean_dec(v_e_x27_280_);
lean_dec(v___y_276_);
lean_inc_ref(v___y_275_);
v___x_286_ = lean_string_append(v___y_275_, v_left_282_);
lean_dec_ref(v_left_282_);
return v___x_286_;
}
}
}
v___jp_287_:
{
lean_object* v_m_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v_exp_295_; uint8_t v___x_296_; 
v_m_289_ = lean_nat_abs(v_mantissa_249_);
lean_dec(v_mantissa_249_);
v___x_290_ = lean_obj_once(&l_Lean_JsonNumber_toString___closed__3, &l_Lean_JsonNumber_toString___closed__3_once, _init_l_Lean_JsonNumber_toString___closed__3);
lean_inc(v_m_289_);
v___x_291_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(v_m_289_);
v___x_292_ = lean_nat_to_int(v___x_291_);
v___x_293_ = lean_int_add(v___x_290_, v___x_292_);
lean_dec(v___x_292_);
lean_inc(v_exponent_250_);
v___x_294_ = lean_nat_to_int(v_exponent_250_);
v_exp_295_ = lean_int_sub(v___x_293_, v___x_294_);
lean_dec(v___x_294_);
lean_dec(v___x_293_);
v___x_296_ = lean_int_dec_lt(v_exp_295_, v___x_253_);
if (v___x_296_ == 0)
{
lean_dec(v_exp_295_);
v___y_274_ = v_m_289_;
v___y_275_ = v___y_288_;
v___y_276_ = v___x_253_;
goto v___jp_273_;
}
else
{
v___y_274_ = v_m_289_;
v___y_275_ = v___y_288_;
v___y_276_ = v_exp_295_;
goto v___jp_273_;
}
}
}
else
{
lean_object* v___x_300_; 
lean_dec(v_exponent_250_);
v___x_300_ = l_Int_repr(v_mantissa_249_);
lean_dec(v_mantissa_249_);
return v___x_300_;
}
v___jp_239_:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
lean_inc_ref(v___y_240_);
v___x_244_ = lean_string_append(v___y_240_, v___y_242_);
lean_dec_ref(v___y_242_);
v___x_245_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__0));
v___x_246_ = lean_string_append(v___x_244_, v___x_245_);
v___x_247_ = lean_string_append(v___x_246_, v___y_241_);
lean_dec_ref(v___y_241_);
v___x_248_ = lean_string_append(v___x_247_, v___y_243_);
lean_dec_ref(v___y_243_);
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftl(lean_object* v_x_301_, lean_object* v_x_302_){
_start:
{
lean_object* v_mantissa_303_; lean_object* v_exponent_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_317_; 
v_mantissa_303_ = lean_ctor_get(v_x_301_, 0);
v_exponent_304_ = lean_ctor_get(v_x_301_, 1);
v_isSharedCheck_317_ = !lean_is_exclusive(v_x_301_);
if (v_isSharedCheck_317_ == 0)
{
v___x_306_ = v_x_301_;
v_isShared_307_ = v_isSharedCheck_317_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_exponent_304_);
lean_inc(v_mantissa_303_);
lean_dec(v_x_301_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_317_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_308_ = lean_unsigned_to_nat(10u);
v___x_309_ = lean_nat_sub(v_x_302_, v_exponent_304_);
v___x_310_ = lean_nat_pow(v___x_308_, v___x_309_);
lean_dec(v___x_309_);
v___x_311_ = lean_nat_to_int(v___x_310_);
v___x_312_ = lean_int_mul(v_mantissa_303_, v___x_311_);
lean_dec(v___x_311_);
lean_dec(v_mantissa_303_);
v___x_313_ = lean_nat_sub(v_exponent_304_, v_x_302_);
lean_dec(v_exponent_304_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 1, v___x_313_);
lean_ctor_set(v___x_306_, 0, v___x_312_);
v___x_315_ = v___x_306_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_312_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftl___boxed(lean_object* v_x_318_, lean_object* v_x_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_JsonNumber_shiftl(v_x_318_, v_x_319_);
lean_dec(v_x_319_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftr(lean_object* v_x_321_, lean_object* v_x_322_){
_start:
{
lean_object* v_mantissa_323_; lean_object* v_exponent_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_332_; 
v_mantissa_323_ = lean_ctor_get(v_x_321_, 0);
v_exponent_324_ = lean_ctor_get(v_x_321_, 1);
v_isSharedCheck_332_ = !lean_is_exclusive(v_x_321_);
if (v_isSharedCheck_332_ == 0)
{
v___x_326_ = v_x_321_;
v_isShared_327_ = v_isSharedCheck_332_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_exponent_324_);
lean_inc(v_mantissa_323_);
lean_dec(v_x_321_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_332_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_328_; lean_object* v___x_330_; 
v___x_328_ = lean_nat_add(v_exponent_324_, v_x_322_);
lean_dec(v_exponent_324_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 1, v___x_328_);
v___x_330_ = v___x_326_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_mantissa_323_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v___x_328_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftr___boxed(lean_object* v_x_333_, lean_object* v_x_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_JsonNumber_shiftr(v_x_333_, v_x_334_);
lean_dec(v_x_334_);
return v_res_335_;
}
}
static lean_object* _init_l_Lean_JsonNumber_instRepr___lam__0___closed__4(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = ((lean_object*)(l_Lean_JsonNumber_instRepr___lam__0___closed__0));
v___x_344_ = lean_string_length(v___x_343_);
return v___x_344_;
}
}
static lean_object* _init_l_Lean_JsonNumber_instRepr___lam__0___closed__5(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_obj_once(&l_Lean_JsonNumber_instRepr___lam__0___closed__4, &l_Lean_JsonNumber_instRepr___lam__0___closed__4_once, _init_l_Lean_JsonNumber_instRepr___lam__0___closed__4);
v___x_346_ = lean_nat_to_int(v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instRepr___lam__0(lean_object* v_x_351_, lean_object* v_x_352_){
_start:
{
lean_object* v_mantissa_353_; lean_object* v_exponent_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_383_; 
v_mantissa_353_ = lean_ctor_get(v_x_351_, 0);
v_exponent_354_ = lean_ctor_get(v_x_351_, 1);
v_isSharedCheck_383_ = !lean_is_exclusive(v_x_351_);
if (v_isSharedCheck_383_ == 0)
{
v___x_356_ = v_x_351_;
v_isShared_357_ = v_isSharedCheck_383_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_exponent_354_);
lean_inc(v_mantissa_353_);
lean_dec(v_x_351_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_383_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___y_359_; lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_375_ = lean_unsigned_to_nat(0u);
v___x_376_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v___x_377_ = lean_int_dec_lt(v_mantissa_353_, v___x_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = l_Int_repr(v_mantissa_353_);
lean_dec(v_mantissa_353_);
v___x_379_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
v___y_359_ = v___x_379_;
goto v___jp_358_;
}
else
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_380_ = l_Int_repr(v_mantissa_353_);
lean_dec(v_mantissa_353_);
v___x_381_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
v___x_382_ = l_Repr_addAppParen(v___x_381_, v___x_375_);
v___y_359_ = v___x_382_;
goto v___jp_358_;
}
v___jp_358_:
{
lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_360_ = ((lean_object*)(l_Lean_JsonNumber_instRepr___lam__0___closed__2));
if (v_isShared_357_ == 0)
{
lean_ctor_set_tag(v___x_356_, 5);
lean_ctor_set(v___x_356_, 1, v___x_360_);
lean_ctor_set(v___x_356_, 0, v___y_359_);
v___x_362_ = v___x_356_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___y_359_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v___x_360_);
v___x_362_ = v_reuseFailAlloc_374_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; uint8_t v___x_372_; lean_object* v___x_373_; 
v___x_363_ = l_Nat_reprFast(v_exponent_354_);
v___x_364_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
v___x_365_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_362_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
v___x_366_ = lean_obj_once(&l_Lean_JsonNumber_instRepr___lam__0___closed__5, &l_Lean_JsonNumber_instRepr___lam__0___closed__5_once, _init_l_Lean_JsonNumber_instRepr___lam__0___closed__5);
v___x_367_ = ((lean_object*)(l_Lean_JsonNumber_instRepr___lam__0___closed__6));
v___x_368_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
lean_ctor_set(v___x_368_, 1, v___x_365_);
v___x_369_ = ((lean_object*)(l_Lean_JsonNumber_instRepr___lam__0___closed__7));
v___x_370_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_368_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
v___x_371_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_366_);
lean_ctor_set(v___x_371_, 1, v___x_370_);
v___x_372_ = 0;
v___x_373_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_373_, 0, v___x_371_);
lean_ctor_set_uint8(v___x_373_, sizeof(void*)*1, v___x_372_);
return v___x_373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instRepr___lam__0___boxed(lean_object* v_x_384_, lean_object* v_x_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_JsonNumber_instRepr___lam__0(v_x_384_, v_x_385_);
lean_dec(v_x_385_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOfScientific___lam__0(lean_object* v_mantissa_389_, uint8_t v_exponentSign_390_, lean_object* v_decimalExponent_391_){
_start:
{
if (v_exponentSign_390_ == 0)
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_392_ = lean_unsigned_to_nat(10u);
v___x_393_ = lean_nat_pow(v___x_392_, v_decimalExponent_391_);
lean_dec(v_decimalExponent_391_);
v___x_394_ = lean_nat_mul(v_mantissa_389_, v___x_393_);
lean_dec(v___x_393_);
lean_dec(v_mantissa_389_);
v___x_395_ = lean_nat_to_int(v___x_394_);
v___x_396_ = lean_unsigned_to_nat(0u);
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_395_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
return v___x_397_;
}
else
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = lean_nat_to_int(v_mantissa_389_);
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
lean_ctor_set(v___x_399_, 1, v_decimalExponent_391_);
return v___x_399_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOfScientific___lam__0___boxed(lean_object* v_mantissa_400_, lean_object* v_exponentSign_401_, lean_object* v_decimalExponent_402_){
_start:
{
uint8_t v_exponentSign_boxed_403_; lean_object* v_res_404_; 
v_exponentSign_boxed_403_ = lean_unbox(v_exponentSign_401_);
v_res_404_ = l_Lean_JsonNumber_instOfScientific___lam__0(v_mantissa_400_, v_exponentSign_boxed_403_, v_decimalExponent_402_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instNeg___lam__0(lean_object* v_jn_407_){
_start:
{
lean_object* v_mantissa_408_; lean_object* v_exponent_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_417_; 
v_mantissa_408_ = lean_ctor_get(v_jn_407_, 0);
v_exponent_409_ = lean_ctor_get(v_jn_407_, 1);
v_isSharedCheck_417_ = !lean_is_exclusive(v_jn_407_);
if (v_isSharedCheck_417_ == 0)
{
v___x_411_ = v_jn_407_;
v_isShared_412_ = v_isSharedCheck_417_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_exponent_409_);
lean_inc(v_mantissa_408_);
lean_dec(v_jn_407_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_417_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_413_ = lean_int_neg(v_mantissa_408_);
lean_dec(v_mantissa_408_);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v___x_413_);
v___x_415_ = v___x_411_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_413_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v_exponent_409_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
static lean_object* _init_l_Lean_JsonNumber_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_unsigned_to_nat(0u);
v___x_421_ = l_Lean_JsonNumber_fromNat(v___x_420_);
return v___x_421_;
}
}
static lean_object* _init_l_Lean_JsonNumber_instInhabited(void){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = lean_obj_once(&l_Lean_JsonNumber_instInhabited___closed__0, &l_Lean_JsonNumber_instInhabited___closed__0_once, _init_l_Lean_JsonNumber_instInhabited___closed__0);
return v___x_422_;
}
}
static double _init_l_Lean_JsonNumber_toFloat___closed__0(void){
_start:
{
lean_object* v___x_423_; uint8_t v___x_424_; lean_object* v___x_425_; double v___x_426_; 
v___x_423_ = lean_unsigned_to_nat(1u);
v___x_424_ = 1;
v___x_425_ = lean_unsigned_to_nat(10u);
v___x_426_ = l_Float_ofScientific(v___x_425_, v___x_424_, v___x_423_);
return v___x_426_;
}
}
static double _init_l_Lean_JsonNumber_toFloat___closed__1(void){
_start:
{
double v___x_427_; double v___x_428_; 
v___x_427_ = lean_float_once(&l_Lean_JsonNumber_toFloat___closed__0, &l_Lean_JsonNumber_toFloat___closed__0_once, _init_l_Lean_JsonNumber_toFloat___closed__0);
v___x_428_ = lean_float_negate(v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT double l_Lean_JsonNumber_toFloat(lean_object* v_x_429_){
_start:
{
lean_object* v_mantissa_430_; lean_object* v_exponent_431_; double v___y_433_; lean_object* v___x_438_; uint8_t v___x_439_; 
v_mantissa_430_ = lean_ctor_get(v_x_429_, 0);
lean_inc(v_mantissa_430_);
v_exponent_431_ = lean_ctor_get(v_x_429_, 1);
lean_inc(v_exponent_431_);
lean_dec_ref(v_x_429_);
v___x_438_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v___x_439_ = lean_int_dec_le(v___x_438_, v_mantissa_430_);
if (v___x_439_ == 0)
{
double v___x_440_; 
v___x_440_ = lean_float_once(&l_Lean_JsonNumber_toFloat___closed__1, &l_Lean_JsonNumber_toFloat___closed__1_once, _init_l_Lean_JsonNumber_toFloat___closed__1);
v___y_433_ = v___x_440_;
goto v___jp_432_;
}
else
{
lean_object* v___x_441_; lean_object* v___x_442_; double v___x_443_; 
v___x_441_ = lean_unsigned_to_nat(10u);
v___x_442_ = lean_unsigned_to_nat(1u);
v___x_443_ = l_Float_ofScientific(v___x_441_, v___x_439_, v___x_442_);
v___y_433_ = v___x_443_;
goto v___jp_432_;
}
v___jp_432_:
{
lean_object* v___x_434_; uint8_t v___x_435_; double v___x_436_; double v___x_437_; 
v___x_434_ = lean_nat_abs(v_mantissa_430_);
lean_dec(v_mantissa_430_);
v___x_435_ = 1;
v___x_436_ = l_Float_ofScientific(v___x_434_, v___x_435_, v_exponent_431_);
v___x_437_ = lean_float_mul(v___y_433_, v___x_436_);
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_toFloat___boxed(lean_object* v_x_444_){
_start:
{
double v_res_445_; lean_object* v_r_446_; 
v_res_445_ = l_Lean_JsonNumber_toFloat(v_x_444_);
v_r_446_ = lean_box_float(v_res_445_);
return v_r_446_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21_spec__0(lean_object* v_msg_447_){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = l_Lean_JsonNumber_instInhabited;
v___x_449_ = lean_panic_fn_borrowed(v___x_448_, v_msg_447_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(double v_x_453_){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = lean_float_to_string(v_x_453_);
v___x_455_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v___x_454_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_456_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0));
v___x_457_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__1));
v___x_458_ = lean_unsigned_to_nat(160u);
v___x_459_ = lean_unsigned_to_nat(12u);
v___x_460_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__2));
v___x_461_ = lean_string_append(v___x_460_, v___x_454_);
lean_dec_ref(v___x_454_);
v___x_462_ = l_mkPanicMessageWithDecl(v___x_456_, v___x_457_, v___x_458_, v___x_459_, v___x_461_);
lean_dec_ref(v___x_461_);
v___x_463_ = l_panic___at___00__private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21_spec__0(v___x_462_);
return v___x_463_;
}
else
{
lean_object* v_val_464_; lean_object* v_snd_465_; lean_object* v_fst_466_; uint8_t v___x_467_; 
lean_dec_ref(v___x_454_);
v_val_464_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_val_464_);
lean_dec_ref_known(v___x_455_, 1);
v_snd_465_ = lean_ctor_get(v_val_464_, 1);
lean_inc(v_snd_465_);
v_fst_466_ = lean_ctor_get(v_snd_465_, 0);
v___x_467_ = lean_unbox(v_fst_466_);
if (v___x_467_ == 0)
{
lean_object* v_fst_468_; lean_object* v_snd_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_481_; 
v_fst_468_ = lean_ctor_get(v_val_464_, 0);
lean_inc(v_fst_468_);
lean_dec(v_val_464_);
v_snd_469_ = lean_ctor_get(v_snd_465_, 1);
v_isSharedCheck_481_ = !lean_is_exclusive(v_snd_465_);
if (v_isSharedCheck_481_ == 0)
{
lean_object* v_unused_482_; 
v_unused_482_ = lean_ctor_get(v_snd_465_, 0);
lean_dec(v_unused_482_);
v___x_471_ = v_snd_465_;
v_isShared_472_ = v_isSharedCheck_481_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_snd_469_);
lean_dec(v_snd_465_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_481_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_473_ = lean_unsigned_to_nat(10u);
v___x_474_ = lean_nat_pow(v___x_473_, v_snd_469_);
lean_dec(v_snd_469_);
v___x_475_ = lean_nat_mul(v_fst_468_, v___x_474_);
lean_dec(v___x_474_);
lean_dec(v_fst_468_);
v___x_476_ = lean_nat_to_int(v___x_475_);
v___x_477_ = lean_unsigned_to_nat(0u);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 1, v___x_477_);
lean_ctor_set(v___x_471_, 0, v___x_476_);
v___x_479_ = v___x_471_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v___x_477_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
else
{
lean_object* v_fst_483_; lean_object* v_snd_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_492_; 
v_fst_483_ = lean_ctor_get(v_val_464_, 0);
lean_inc(v_fst_483_);
lean_dec(v_val_464_);
v_snd_484_ = lean_ctor_get(v_snd_465_, 1);
v_isSharedCheck_492_ = !lean_is_exclusive(v_snd_465_);
if (v_isSharedCheck_492_ == 0)
{
lean_object* v_unused_493_; 
v_unused_493_ = lean_ctor_get(v_snd_465_, 0);
lean_dec(v_unused_493_);
v___x_486_ = v_snd_465_;
v_isShared_487_ = v_isSharedCheck_492_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_snd_484_);
lean_dec(v_snd_465_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_492_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_488_; lean_object* v___x_490_; 
v___x_488_ = lean_nat_to_int(v_fst_483_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v___x_488_);
v___x_490_ = v___x_486_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_snd_484_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___boxed(lean_object* v_x_494_){
_start:
{
double v_x_boxed_495_; lean_object* v_res_496_; 
v_x_boxed_495_ = lean_unbox_float(v_x_494_);
lean_dec_ref(v_x_494_);
v_res_496_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(v_x_boxed_495_);
return v_res_496_;
}
}
static double _init_l_Lean_JsonNumber_fromFloat_x3f___closed__0(void){
_start:
{
lean_object* v___x_497_; uint8_t v___x_498_; lean_object* v___x_499_; double v___x_500_; 
v___x_497_ = lean_unsigned_to_nat(1u);
v___x_498_ = 1;
v___x_499_ = lean_unsigned_to_nat(0u);
v___x_500_ = l_Float_ofScientific(v___x_499_, v___x_498_, v___x_497_);
return v___x_500_;
}
}
static lean_object* _init_l_Lean_JsonNumber_fromFloat_x3f___closed__1(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_obj_once(&l_Lean_JsonNumber_instInhabited___closed__0, &l_Lean_JsonNumber_instInhabited___closed__0_once, _init_l_Lean_JsonNumber_instInhabited___closed__0);
v___x_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
return v___x_502_;
}
}
static double _init_l_Lean_JsonNumber_fromFloat_x3f___closed__2(void){
_start:
{
lean_object* v___x_503_; double v___x_504_; 
v___x_503_ = lean_unsigned_to_nat(0u);
v___x_504_ = lean_float_of_nat(v___x_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_fromFloat_x3f(double v_x_514_){
_start:
{
uint8_t v___x_515_; 
v___x_515_ = lean_float_isnan(v_x_514_);
if (v___x_515_ == 0)
{
uint8_t v___x_516_; 
v___x_516_ = lean_float_isinf(v_x_514_);
if (v___x_516_ == 0)
{
double v___x_517_; uint8_t v___x_518_; 
v___x_517_ = lean_float_once(&l_Lean_JsonNumber_fromFloat_x3f___closed__0, &l_Lean_JsonNumber_fromFloat_x3f___closed__0_once, _init_l_Lean_JsonNumber_fromFloat_x3f___closed__0);
v___x_518_ = lean_float_beq(v_x_514_, v___x_517_);
if (v___x_518_ == 0)
{
uint8_t v___x_519_; 
v___x_519_ = lean_float_decLt(v_x_514_, v___x_517_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(v_x_514_);
v___x_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
return v___x_521_;
}
else
{
double v___x_522_; lean_object* v___x_523_; lean_object* v_mantissa_524_; lean_object* v_exponent_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_534_; 
v___x_522_ = lean_float_negate(v_x_514_);
v___x_523_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(v___x_522_);
v_mantissa_524_ = lean_ctor_get(v___x_523_, 0);
v_exponent_525_ = lean_ctor_get(v___x_523_, 1);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_534_ == 0)
{
v___x_527_ = v___x_523_;
v_isShared_528_ = v_isSharedCheck_534_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_exponent_525_);
lean_inc(v_mantissa_524_);
lean_dec(v___x_523_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_534_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_529_ = lean_int_neg(v_mantissa_524_);
lean_dec(v_mantissa_524_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___x_529_);
v___x_531_ = v___x_527_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_529_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_exponent_525_);
v___x_531_ = v_reuseFailAlloc_533_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_532_; 
v___x_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
return v___x_532_;
}
}
}
}
else
{
lean_object* v___x_535_; 
v___x_535_ = lean_obj_once(&l_Lean_JsonNumber_fromFloat_x3f___closed__1, &l_Lean_JsonNumber_fromFloat_x3f___closed__1_once, _init_l_Lean_JsonNumber_fromFloat_x3f___closed__1);
return v___x_535_;
}
}
else
{
double v___x_536_; uint8_t v___x_537_; 
v___x_536_ = lean_float_once(&l_Lean_JsonNumber_fromFloat_x3f___closed__2, &l_Lean_JsonNumber_fromFloat_x3f___closed__2_once, _init_l_Lean_JsonNumber_fromFloat_x3f___closed__2);
v___x_537_ = lean_float_decLt(v___x_536_, v_x_514_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; 
v___x_538_ = ((lean_object*)(l_Lean_JsonNumber_fromFloat_x3f___closed__4));
return v___x_538_;
}
else
{
lean_object* v___x_539_; 
v___x_539_ = ((lean_object*)(l_Lean_JsonNumber_fromFloat_x3f___closed__6));
return v___x_539_;
}
}
}
else
{
lean_object* v___x_540_; 
v___x_540_ = ((lean_object*)(l_Lean_JsonNumber_fromFloat_x3f___closed__8));
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_fromFloat_x3f___boxed(lean_object* v_x_541_){
_start:
{
double v_x_boxed_542_; lean_object* v_res_543_; 
v_x_boxed_542_ = lean_unbox_float(v_x_541_);
lean_dec_ref(v_x_541_);
v_res_543_ = l_Lean_JsonNumber_fromFloat_x3f(v_x_boxed_542_);
return v_res_543_;
}
}
LEAN_EXPORT uint8_t l_Lean_strLt(lean_object* v_a_544_, lean_object* v_b_545_){
_start:
{
uint8_t v___x_546_; 
v___x_546_ = lean_string_dec_lt(v_a_544_, v_b_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_strLt___boxed(lean_object* v_a_547_, lean_object* v_b_548_){
_start:
{
uint8_t v_res_549_; lean_object* v_r_550_; 
v_res_549_ = l_Lean_strLt(v_a_547_, v_b_548_);
lean_dec_ref(v_b_548_);
lean_dec_ref(v_a_547_);
v_r_550_ = lean_box(v_res_549_);
return v_r_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorIdx(lean_object* v_x_551_){
_start:
{
switch(lean_obj_tag(v_x_551_))
{
case 0:
{
lean_object* v___x_552_; 
v___x_552_ = lean_unsigned_to_nat(0u);
return v___x_552_;
}
case 1:
{
lean_object* v___x_553_; 
v___x_553_ = lean_unsigned_to_nat(1u);
return v___x_553_;
}
case 2:
{
lean_object* v___x_554_; 
v___x_554_ = lean_unsigned_to_nat(2u);
return v___x_554_;
}
case 3:
{
lean_object* v___x_555_; 
v___x_555_ = lean_unsigned_to_nat(3u);
return v___x_555_;
}
case 4:
{
lean_object* v___x_556_; 
v___x_556_ = lean_unsigned_to_nat(4u);
return v___x_556_;
}
default: 
{
lean_object* v___x_557_; 
v___x_557_ = lean_unsigned_to_nat(5u);
return v___x_557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorIdx___boxed(lean_object* v_x_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_Json_ctorIdx(v_x_558_);
lean_dec(v_x_558_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorElim___redArg(lean_object* v_t_560_, lean_object* v_k_561_){
_start:
{
switch(lean_obj_tag(v_t_560_))
{
case 0:
{
return v_k_561_;
}
case 1:
{
uint8_t v_b_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v_b_562_ = lean_ctor_get_uint8(v_t_560_, 0);
lean_dec_ref_known(v_t_560_, 0);
v___x_563_ = lean_box(v_b_562_);
v___x_564_ = lean_apply_1(v_k_561_, v___x_563_);
return v___x_564_;
}
case 5:
{
lean_object* v_kvPairs_565_; lean_object* v___x_566_; 
v_kvPairs_565_ = lean_ctor_get(v_t_560_, 0);
lean_inc(v_kvPairs_565_);
lean_dec_ref_known(v_t_560_, 1);
v___x_566_ = lean_apply_1(v_k_561_, v_kvPairs_565_);
return v___x_566_;
}
default: 
{
lean_object* v_n_567_; lean_object* v___x_568_; 
v_n_567_ = lean_ctor_get(v_t_560_, 0);
lean_inc_ref(v_n_567_);
lean_dec(v_t_560_);
v___x_568_ = lean_apply_1(v_k_561_, v_n_567_);
return v___x_568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorElim(lean_object* v_motive__1_569_, lean_object* v_ctorIdx_570_, lean_object* v_t_571_, lean_object* v_h_572_, lean_object* v_k_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_Json_ctorElim___redArg(v_t_571_, v_k_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorElim___boxed(lean_object* v_motive__1_575_, lean_object* v_ctorIdx_576_, lean_object* v_t_577_, lean_object* v_h_578_, lean_object* v_k_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_Json_ctorElim(v_motive__1_575_, v_ctorIdx_576_, v_t_577_, v_h_578_, v_k_579_);
lean_dec(v_ctorIdx_576_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_null_elim___redArg(lean_object* v_t_581_, lean_object* v_null_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_Json_ctorElim___redArg(v_t_581_, v_null_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_null_elim(lean_object* v_motive__1_584_, lean_object* v_t_585_, lean_object* v_h_586_, lean_object* v_null_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_Json_ctorElim___redArg(v_t_585_, v_null_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_bool_elim___redArg(lean_object* v_t_589_, lean_object* v_bool_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_Json_ctorElim___redArg(v_t_589_, v_bool_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_bool_elim(lean_object* v_motive__1_592_, lean_object* v_t_593_, lean_object* v_h_594_, lean_object* v_bool_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_Json_ctorElim___redArg(v_t_593_, v_bool_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_num_elim___redArg(lean_object* v_t_597_, lean_object* v_num_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_Json_ctorElim___redArg(v_t_597_, v_num_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_num_elim(lean_object* v_motive__1_600_, lean_object* v_t_601_, lean_object* v_h_602_, lean_object* v_num_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_Json_ctorElim___redArg(v_t_601_, v_num_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_str_elim___redArg(lean_object* v_t_605_, lean_object* v_str_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_Json_ctorElim___redArg(v_t_605_, v_str_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_str_elim(lean_object* v_motive__1_608_, lean_object* v_t_609_, lean_object* v_h_610_, lean_object* v_str_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_Json_ctorElim___redArg(v_t_609_, v_str_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_arr_elim___redArg(lean_object* v_t_613_, lean_object* v_arr_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_Lean_Json_ctorElim___redArg(v_t_613_, v_arr_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_arr_elim(lean_object* v_motive__1_616_, lean_object* v_t_617_, lean_object* v_h_618_, lean_object* v_arr_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Lean_Json_ctorElim___redArg(v_t_617_, v_arr_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_obj_elim___redArg(lean_object* v_t_621_, lean_object* v_obj_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_Json_ctorElim___redArg(v_t_621_, v_obj_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_obj_elim(lean_object* v_motive__1_624_, lean_object* v_t_625_, lean_object* v_h_626_, lean_object* v_obj_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_Json_ctorElim___redArg(v_t_625_, v_obj_627_);
return v___x_628_;
}
}
static lean_object* _init_l_Lean_instInhabitedJson_default(void){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = lean_box(0);
return v___x_629_;
}
}
static lean_object* _init_l_Lean_instInhabitedJson(void){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = lean_box(0);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(lean_object* v_init_631_, lean_object* v_x_632_){
_start:
{
if (lean_obj_tag(v_x_632_) == 0)
{
lean_object* v_l_633_; lean_object* v_r_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v_l_633_ = lean_ctor_get(v_x_632_, 3);
v_r_634_ = lean_ctor_get(v_x_632_, 4);
v___x_635_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_631_, v_l_633_);
v___x_636_ = lean_unsigned_to_nat(1u);
v___x_637_ = lean_nat_add(v___x_635_, v___x_636_);
lean_dec(v___x_635_);
v_init_631_ = v___x_637_;
v_x_632_ = v_r_634_;
goto _start;
}
else
{
return v_init_631_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1___boxed(lean_object* v_init_639_, lean_object* v_x_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_639_, v_x_640_);
lean_dec(v_x_640_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(lean_object* v_t_642_, lean_object* v_k_643_){
_start:
{
if (lean_obj_tag(v_t_642_) == 0)
{
lean_object* v_k_644_; lean_object* v_v_645_; lean_object* v_l_646_; lean_object* v_r_647_; uint8_t v___x_648_; 
v_k_644_ = lean_ctor_get(v_t_642_, 1);
v_v_645_ = lean_ctor_get(v_t_642_, 2);
v_l_646_ = lean_ctor_get(v_t_642_, 3);
v_r_647_ = lean_ctor_get(v_t_642_, 4);
v___x_648_ = lean_string_compare(v_k_643_, v_k_644_);
switch(v___x_648_)
{
case 0:
{
v_t_642_ = v_l_646_;
goto _start;
}
case 1:
{
lean_object* v___x_650_; 
lean_inc(v_v_645_);
v___x_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_650_, 0, v_v_645_);
return v___x_650_;
}
default: 
{
v_t_642_ = v_r_647_;
goto _start;
}
}
}
else
{
lean_object* v___x_652_; 
v___x_652_ = lean_box(0);
return v___x_652_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg___boxed(lean_object* v_t_653_, lean_object* v_k_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_t_653_, v_k_654_);
lean_dec_ref(v_k_654_);
lean_dec(v_t_653_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(lean_object* v_szA_667_, lean_object* v_szB_668_, lean_object* v_kvPairs_669_, lean_object* v_init_670_, lean_object* v_x_671_){
_start:
{
if (lean_obj_tag(v_x_671_) == 0)
{
lean_object* v_k_672_; lean_object* v_v_673_; lean_object* v_l_674_; lean_object* v_r_675_; uint8_t v___x_676_; lean_object* v___x_677_; 
v_k_672_ = lean_ctor_get(v_x_671_, 1);
v_v_673_ = lean_ctor_get(v_x_671_, 2);
v_l_674_ = lean_ctor_get(v_x_671_, 3);
v_r_675_ = lean_ctor_get(v_x_671_, 4);
v___x_676_ = lean_nat_dec_eq(v_szA_667_, v_szB_668_);
v___x_677_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_szA_667_, v_szB_668_, v_kvPairs_669_, v_init_670_, v_l_674_);
if (lean_obj_tag(v___x_677_) == 0)
{
return v___x_677_;
}
else
{
lean_object* v___x_678_; lean_object* v___x_682_; 
lean_dec_ref_known(v___x_677_, 1);
v___x_678_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__0));
v___x_682_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_kvPairs_669_, v_k_672_);
if (lean_obj_tag(v___x_682_) == 0)
{
goto v___jp_679_;
}
else
{
lean_object* v_val_683_; uint8_t v___x_684_; 
v_val_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_val_683_);
lean_dec_ref_known(v___x_682_, 1);
v___x_684_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_v_673_, v_val_683_);
lean_dec(v_val_683_);
if (v___x_684_ == 0)
{
goto v___jp_679_;
}
else
{
v_init_670_ = v___x_678_;
v_x_671_ = v_r_675_;
goto _start;
}
}
v___jp_679_:
{
if (v___x_676_ == 0)
{
v_init_670_ = v___x_678_;
v_x_671_ = v_r_675_;
goto _start;
}
else
{
lean_object* v___x_681_; 
v___x_681_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__3));
return v___x_681_;
}
}
}
}
else
{
lean_object* v___x_686_; 
v___x_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_686_, 0, v_init_670_);
return v___x_686_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(lean_object* v_x_687_, lean_object* v_x_688_){
_start:
{
switch(lean_obj_tag(v_x_687_))
{
case 0:
{
if (lean_obj_tag(v_x_688_) == 0)
{
uint8_t v___x_689_; 
v___x_689_ = 1;
return v___x_689_;
}
else
{
uint8_t v___x_690_; 
v___x_690_ = 0;
return v___x_690_;
}
}
case 1:
{
if (lean_obj_tag(v_x_688_) == 1)
{
uint8_t v_b_691_; 
v_b_691_ = lean_ctor_get_uint8(v_x_688_, 0);
if (v_b_691_ == 0)
{
uint8_t v_b_692_; 
v_b_692_ = lean_ctor_get_uint8(v_x_687_, 0);
if (v_b_692_ == 0)
{
uint8_t v___x_693_; 
v___x_693_ = 1;
return v___x_693_;
}
else
{
return v_b_691_;
}
}
else
{
uint8_t v_b_694_; 
v_b_694_ = lean_ctor_get_uint8(v_x_687_, 0);
return v_b_694_;
}
}
else
{
uint8_t v___x_695_; 
v___x_695_ = 0;
return v___x_695_;
}
}
case 2:
{
if (lean_obj_tag(v_x_688_) == 2)
{
lean_object* v_n_696_; lean_object* v_n_697_; uint8_t v___x_698_; 
v_n_696_ = lean_ctor_get(v_x_687_, 0);
v_n_697_ = lean_ctor_get(v_x_688_, 0);
v___x_698_ = l_Lean_instDecidableEqJsonNumber_decEq(v_n_696_, v_n_697_);
return v___x_698_;
}
else
{
uint8_t v___x_699_; 
v___x_699_ = 0;
return v___x_699_;
}
}
case 3:
{
if (lean_obj_tag(v_x_688_) == 3)
{
lean_object* v_s_700_; lean_object* v_s_701_; uint8_t v___x_702_; 
v_s_700_ = lean_ctor_get(v_x_687_, 0);
v_s_701_ = lean_ctor_get(v_x_688_, 0);
v___x_702_ = lean_string_dec_eq(v_s_700_, v_s_701_);
return v___x_702_;
}
else
{
uint8_t v___x_703_; 
v___x_703_ = 0;
return v___x_703_;
}
}
case 4:
{
if (lean_obj_tag(v_x_688_) == 4)
{
lean_object* v_elems_704_; lean_object* v_elems_705_; lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v_elems_704_ = lean_ctor_get(v_x_687_, 0);
v_elems_705_ = lean_ctor_get(v_x_688_, 0);
v___x_706_ = lean_array_get_size(v_elems_704_);
v___x_707_ = lean_array_get_size(v_elems_705_);
v___x_708_ = lean_nat_dec_eq(v___x_706_, v___x_707_);
if (v___x_708_ == 0)
{
return v___x_708_;
}
else
{
uint8_t v___x_709_; 
v___x_709_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(v_elems_704_, v_elems_705_, v___x_706_);
return v___x_709_;
}
}
else
{
uint8_t v___x_710_; 
v___x_710_ = 0;
return v___x_710_;
}
}
default: 
{
if (lean_obj_tag(v_x_688_) == 5)
{
lean_object* v_kvPairs_711_; lean_object* v_kvPairs_712_; lean_object* v___x_713_; lean_object* v_szA_714_; lean_object* v_szB_715_; uint8_t v___x_716_; lean_object* v___y_718_; 
v_kvPairs_711_ = lean_ctor_get(v_x_687_, 0);
v_kvPairs_712_ = lean_ctor_get(v_x_688_, 0);
v___x_713_ = lean_unsigned_to_nat(0u);
v_szA_714_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v___x_713_, v_kvPairs_711_);
v_szB_715_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v___x_713_, v_kvPairs_712_);
v___x_716_ = lean_nat_dec_eq(v_szA_714_, v_szB_715_);
if (v___x_716_ == 0)
{
lean_dec(v_szB_715_);
lean_dec(v_szA_714_);
return v___x_716_;
}
else
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v_a_724_; 
v___x_722_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__0));
v___x_723_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_szA_714_, v_szB_715_, v_kvPairs_712_, v___x_722_, v_kvPairs_711_);
lean_dec(v_szB_715_);
lean_dec(v_szA_714_);
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref(v___x_723_);
v___y_718_ = v_a_724_;
goto v___jp_717_;
}
v___jp_717_:
{
lean_object* v_fst_719_; 
v_fst_719_ = lean_ctor_get(v___y_718_, 0);
lean_inc(v_fst_719_);
lean_dec_ref(v___y_718_);
if (lean_obj_tag(v_fst_719_) == 0)
{
return v___x_716_;
}
else
{
lean_object* v_val_720_; uint8_t v___x_721_; 
v_val_720_ = lean_ctor_get(v_fst_719_, 0);
lean_inc(v_val_720_);
lean_dec_ref_known(v_fst_719_, 1);
v___x_721_ = lean_unbox(v_val_720_);
lean_dec(v_val_720_);
return v___x_721_;
}
}
}
else
{
uint8_t v___x_725_; 
v___x_725_ = 0;
return v___x_725_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(lean_object* v_xs_726_, lean_object* v_ys_727_, lean_object* v_x_728_){
_start:
{
lean_object* v_zero_729_; uint8_t v_isZero_730_; 
v_zero_729_ = lean_unsigned_to_nat(0u);
v_isZero_730_ = lean_nat_dec_eq(v_x_728_, v_zero_729_);
if (v_isZero_730_ == 1)
{
lean_dec(v_x_728_);
return v_isZero_730_;
}
else
{
lean_object* v_one_731_; lean_object* v_n_732_; lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v_one_731_ = lean_unsigned_to_nat(1u);
v_n_732_ = lean_nat_sub(v_x_728_, v_one_731_);
lean_dec(v_x_728_);
v___x_733_ = lean_array_fget_borrowed(v_xs_726_, v_n_732_);
v___x_734_ = lean_array_fget_borrowed(v_ys_727_, v_n_732_);
v___x_735_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v___x_733_, v___x_734_);
if (v___x_735_ == 0)
{
lean_dec(v_n_732_);
return v___x_735_;
}
else
{
v_x_728_ = v_n_732_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg___boxed(lean_object* v_xs_737_, lean_object* v_ys_738_, lean_object* v_x_739_){
_start:
{
uint8_t v_res_740_; lean_object* v_r_741_; 
v_res_740_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(v_xs_737_, v_ys_738_, v_x_739_);
lean_dec_ref(v_ys_738_);
lean_dec_ref(v_xs_737_);
v_r_741_ = lean_box(v_res_740_);
return v_r_741_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___boxed(lean_object* v_szA_742_, lean_object* v_szB_743_, lean_object* v_kvPairs_744_, lean_object* v_init_745_, lean_object* v_x_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_szA_742_, v_szB_743_, v_kvPairs_744_, v_init_745_, v_x_746_);
lean_dec(v_x_746_);
lean_dec(v_kvPairs_744_);
lean_dec(v_szB_743_);
lean_dec(v_szA_742_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___boxed(lean_object* v_x_748_, lean_object* v_x_749_){
_start:
{
uint8_t v_res_750_; lean_object* v_r_751_; 
v_res_750_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_x_748_, v_x_749_);
lean_dec(v_x_749_);
lean_dec(v_x_748_);
v_r_751_ = lean_box(v_res_750_);
return v_r_751_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0(lean_object* v_xs_752_, lean_object* v_ys_753_, lean_object* v_hsz_754_, lean_object* v_x_755_, lean_object* v_x_756_){
_start:
{
uint8_t v___x_757_; 
v___x_757_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(v_xs_752_, v_ys_753_, v_x_755_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___boxed(lean_object* v_xs_758_, lean_object* v_ys_759_, lean_object* v_hsz_760_, lean_object* v_x_761_, lean_object* v_x_762_){
_start:
{
uint8_t v_res_763_; lean_object* v_r_764_; 
v_res_763_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0(v_xs_758_, v_ys_759_, v_hsz_760_, v_x_761_, v_x_762_);
lean_dec_ref(v_ys_759_);
lean_dec_ref(v_xs_758_);
v_r_764_ = lean_box(v_res_763_);
return v_r_764_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1(lean_object* v_init_765_, lean_object* v_t_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_765_, v_t_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___boxed(lean_object* v_init_768_, lean_object* v_t_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1(v_init_768_, v_t_769_);
lean_dec(v_t_769_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2(lean_object* v_00_u03b4_771_, lean_object* v_t_772_, lean_object* v_k_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_t_772_, v_k_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___boxed(lean_object* v_00_u03b4_775_, lean_object* v_t_776_, lean_object* v_k_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2(v_00_u03b4_775_, v_t_776_, v_k_777_);
lean_dec_ref(v_k_777_);
lean_dec(v_t_776_);
return v_res_778_;
}
}
LEAN_EXPORT uint8_t l_Lean_Json_instBEq___private__1(lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
uint8_t v___x_781_; 
v___x_781_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_a_779_, v_a_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instBEq___private__1___boxed(lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
uint8_t v_res_784_; lean_object* v_r_785_; 
v_res_784_ = l_Lean_Json_instBEq___private__1(v_a_782_, v_a_783_);
lean_dec(v_a_783_);
lean_dec(v_a_782_);
v_r_785_ = lean_box(v_res_784_);
return v_r_785_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(lean_object* v_as_788_, size_t v_i_789_, size_t v_stop_790_, uint64_t v_b_791_){
_start:
{
uint8_t v___x_792_; 
v___x_792_ = lean_usize_dec_eq(v_i_789_, v_stop_790_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; uint64_t v___x_794_; uint64_t v___x_795_; size_t v___x_796_; size_t v___x_797_; 
v___x_793_ = lean_array_uget_borrowed(v_as_788_, v_i_789_);
v___x_794_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v___x_793_);
v___x_795_ = lean_uint64_mix_hash(v_b_791_, v___x_794_);
v___x_796_ = ((size_t)1ULL);
v___x_797_ = lean_usize_add(v_i_789_, v___x_796_);
v_i_789_ = v___x_797_;
v_b_791_ = v___x_795_;
goto _start;
}
else
{
return v_b_791_;
}
}
}
LEAN_EXPORT uint64_t l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(lean_object* v_x_799_){
_start:
{
switch(lean_obj_tag(v_x_799_))
{
case 0:
{
uint64_t v___x_800_; 
v___x_800_ = 11ULL;
return v___x_800_;
}
case 1:
{
uint8_t v_b_801_; 
v_b_801_ = lean_ctor_get_uint8(v_x_799_, 0);
if (v_b_801_ == 0)
{
uint64_t v___x_802_; 
v___x_802_ = 889925284873970544ULL;
return v___x_802_;
}
else
{
uint64_t v___x_803_; 
v___x_803_ = 7849220421742680397ULL;
return v___x_803_;
}
}
case 2:
{
lean_object* v_n_804_; uint64_t v___x_805_; uint64_t v___x_806_; uint64_t v___x_807_; 
v_n_804_ = lean_ctor_get(v_x_799_, 0);
v___x_805_ = 17ULL;
v___x_806_ = l_Lean_instHashableJsonNumber_hash(v_n_804_);
v___x_807_ = lean_uint64_mix_hash(v___x_805_, v___x_806_);
return v___x_807_;
}
case 3:
{
lean_object* v_s_808_; uint64_t v___x_809_; uint64_t v___x_810_; uint64_t v___x_811_; 
v_s_808_ = lean_ctor_get(v_x_799_, 0);
v___x_809_ = 19ULL;
v___x_810_ = lean_string_hash(v_s_808_);
v___x_811_ = lean_uint64_mix_hash(v___x_809_, v___x_810_);
return v___x_811_;
}
case 4:
{
lean_object* v_elems_812_; lean_object* v___x_813_; lean_object* v___x_814_; uint8_t v___x_815_; 
v_elems_812_ = lean_ctor_get(v_x_799_, 0);
v___x_813_ = lean_unsigned_to_nat(0u);
v___x_814_ = lean_array_get_size(v_elems_812_);
v___x_815_ = lean_nat_dec_lt(v___x_813_, v___x_814_);
if (v___x_815_ == 0)
{
uint64_t v___x_816_; 
v___x_816_ = 179905158410471120ULL;
return v___x_816_;
}
else
{
uint64_t v___x_817_; uint64_t v___x_818_; uint8_t v___x_819_; 
v___x_817_ = 23ULL;
v___x_818_ = 7ULL;
v___x_819_ = lean_nat_dec_le(v___x_814_, v___x_814_);
if (v___x_819_ == 0)
{
if (v___x_815_ == 0)
{
uint64_t v___x_820_; 
v___x_820_ = 179905158410471120ULL;
return v___x_820_;
}
else
{
size_t v___x_821_; size_t v___x_822_; uint64_t v___x_823_; uint64_t v___x_824_; 
v___x_821_ = ((size_t)0ULL);
v___x_822_ = lean_usize_of_nat(v___x_814_);
v___x_823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_elems_812_, v___x_821_, v___x_822_, v___x_818_);
v___x_824_ = lean_uint64_mix_hash(v___x_817_, v___x_823_);
return v___x_824_;
}
}
else
{
size_t v___x_825_; size_t v___x_826_; uint64_t v___x_827_; uint64_t v___x_828_; 
v___x_825_ = ((size_t)0ULL);
v___x_826_ = lean_usize_of_nat(v___x_814_);
v___x_827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_elems_812_, v___x_825_, v___x_826_, v___x_818_);
v___x_828_ = lean_uint64_mix_hash(v___x_817_, v___x_827_);
return v___x_828_;
}
}
}
default: 
{
lean_object* v_kvPairs_829_; uint64_t v___x_830_; uint64_t v___x_831_; uint64_t v___x_832_; uint64_t v___x_833_; 
v_kvPairs_829_ = lean_ctor_get(v_x_799_, 0);
v___x_830_ = 29ULL;
v___x_831_ = 7ULL;
v___x_832_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v___x_831_, v_kvPairs_829_);
v___x_833_ = lean_uint64_mix_hash(v___x_830_, v___x_832_);
return v___x_833_;
}
}
}
}
LEAN_EXPORT uint64_t l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(uint64_t v_init_834_, lean_object* v_x_835_){
_start:
{
if (lean_obj_tag(v_x_835_) == 0)
{
lean_object* v_k_836_; lean_object* v_v_837_; lean_object* v_l_838_; lean_object* v_r_839_; uint64_t v___x_840_; uint64_t v___x_841_; uint64_t v___x_842_; uint64_t v___x_843_; uint64_t v___x_844_; 
v_k_836_ = lean_ctor_get(v_x_835_, 1);
v_v_837_ = lean_ctor_get(v_x_835_, 2);
v_l_838_ = lean_ctor_get(v_x_835_, 3);
v_r_839_ = lean_ctor_get(v_x_835_, 4);
v___x_840_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_834_, v_l_838_);
v___x_841_ = lean_string_hash(v_k_836_);
v___x_842_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_v_837_);
v___x_843_ = lean_uint64_mix_hash(v___x_841_, v___x_842_);
v___x_844_ = lean_uint64_mix_hash(v___x_840_, v___x_843_);
v_init_834_ = v___x_844_;
v_x_835_ = v_r_839_;
goto _start;
}
else
{
return v_init_834_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1___boxed(lean_object* v_init_846_, lean_object* v_x_847_){
_start:
{
uint64_t v_init_boxed_848_; uint64_t v_res_849_; lean_object* v_r_850_; 
v_init_boxed_848_ = lean_unbox_uint64(v_init_846_);
lean_dec_ref(v_init_846_);
v_res_849_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_boxed_848_, v_x_847_);
lean_dec(v_x_847_);
v_r_850_ = lean_box_uint64(v_res_849_);
return v_r_850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0___boxed(lean_object* v_as_851_, lean_object* v_i_852_, lean_object* v_stop_853_, lean_object* v_b_854_){
_start:
{
size_t v_i_boxed_855_; size_t v_stop_boxed_856_; uint64_t v_b_boxed_857_; uint64_t v_res_858_; lean_object* v_r_859_; 
v_i_boxed_855_ = lean_unbox_usize(v_i_852_);
lean_dec(v_i_852_);
v_stop_boxed_856_ = lean_unbox_usize(v_stop_853_);
lean_dec(v_stop_853_);
v_b_boxed_857_ = lean_unbox_uint64(v_b_854_);
lean_dec_ref(v_b_854_);
v_res_858_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_as_851_, v_i_boxed_855_, v_stop_boxed_856_, v_b_boxed_857_);
lean_dec_ref(v_as_851_);
v_r_859_ = lean_box_uint64(v_res_858_);
return v_r_859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___boxed(lean_object* v_x_860_){
_start:
{
uint64_t v_res_861_; lean_object* v_r_862_; 
v_res_861_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_x_860_);
lean_dec(v_x_860_);
v_r_862_ = lean_box_uint64(v_res_861_);
return v_r_862_;
}
}
LEAN_EXPORT uint64_t l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1(uint64_t v_init_863_, lean_object* v_t_864_){
_start:
{
uint64_t v___x_865_; 
v___x_865_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_863_, v_t_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1___boxed(lean_object* v_init_866_, lean_object* v_t_867_){
_start:
{
uint64_t v_init_boxed_868_; uint64_t v_res_869_; lean_object* v_r_870_; 
v_init_boxed_868_ = lean_unbox_uint64(v_init_866_);
lean_dec_ref(v_init_866_);
v_res_869_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1(v_init_boxed_868_, v_t_867_);
lean_dec(v_t_867_);
v_r_870_ = lean_box_uint64(v_res_869_);
return v_r_870_;
}
}
LEAN_EXPORT uint64_t l_Lean_Json_instHashable___private__1(lean_object* v_a_871_){
_start:
{
uint64_t v___x_872_; 
v___x_872_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_a_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instHashable___private__1___boxed(lean_object* v_a_873_){
_start:
{
uint64_t v_res_874_; lean_object* v_r_875_; 
v_res_874_ = l_Lean_Json_instHashable___private__1(v_a_873_);
lean_dec(v_a_873_);
v_r_875_ = lean_box_uint64(v_res_874_);
return v_r_875_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(lean_object* v_k_878_, lean_object* v_v_879_, lean_object* v_t_880_){
_start:
{
if (lean_obj_tag(v_t_880_) == 0)
{
lean_object* v_size_881_; lean_object* v_k_882_; lean_object* v_v_883_; lean_object* v_l_884_; lean_object* v_r_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_1165_; 
v_size_881_ = lean_ctor_get(v_t_880_, 0);
v_k_882_ = lean_ctor_get(v_t_880_, 1);
v_v_883_ = lean_ctor_get(v_t_880_, 2);
v_l_884_ = lean_ctor_get(v_t_880_, 3);
v_r_885_ = lean_ctor_get(v_t_880_, 4);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_t_880_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_887_ = v_t_880_;
v_isShared_888_ = v_isSharedCheck_1165_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_r_885_);
lean_inc(v_l_884_);
lean_inc(v_v_883_);
lean_inc(v_k_882_);
lean_inc(v_size_881_);
lean_dec(v_t_880_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_1165_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
uint8_t v___x_889_; 
v___x_889_ = lean_string_compare(v_k_878_, v_k_882_);
switch(v___x_889_)
{
case 0:
{
lean_object* v_impl_890_; lean_object* v___x_891_; 
lean_dec(v_size_881_);
v_impl_890_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_878_, v_v_879_, v_l_884_);
v___x_891_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_885_) == 0)
{
lean_object* v_size_892_; lean_object* v_size_893_; lean_object* v_k_894_; lean_object* v_v_895_; lean_object* v_l_896_; lean_object* v_r_897_; lean_object* v___x_898_; lean_object* v___x_899_; uint8_t v___x_900_; 
v_size_892_ = lean_ctor_get(v_r_885_, 0);
v_size_893_ = lean_ctor_get(v_impl_890_, 0);
v_k_894_ = lean_ctor_get(v_impl_890_, 1);
v_v_895_ = lean_ctor_get(v_impl_890_, 2);
v_l_896_ = lean_ctor_get(v_impl_890_, 3);
v_r_897_ = lean_ctor_get(v_impl_890_, 4);
lean_inc(v_r_897_);
v___x_898_ = lean_unsigned_to_nat(3u);
v___x_899_ = lean_nat_mul(v___x_898_, v_size_892_);
v___x_900_ = lean_nat_dec_lt(v___x_899_, v_size_893_);
lean_dec(v___x_899_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_904_; 
lean_dec(v_r_897_);
v___x_901_ = lean_nat_add(v___x_891_, v_size_893_);
v___x_902_ = lean_nat_add(v___x_901_, v_size_892_);
lean_dec(v___x_901_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 3, v_impl_890_);
lean_ctor_set(v___x_887_, 0, v___x_902_);
v___x_904_ = v___x_887_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_902_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_k_882_);
lean_ctor_set(v_reuseFailAlloc_905_, 2, v_v_883_);
lean_ctor_set(v_reuseFailAlloc_905_, 3, v_impl_890_);
lean_ctor_set(v_reuseFailAlloc_905_, 4, v_r_885_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
else
{
lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_971_; 
lean_inc(v_l_896_);
lean_inc(v_v_895_);
lean_inc(v_k_894_);
lean_inc(v_size_893_);
v_isSharedCheck_971_ = !lean_is_exclusive(v_impl_890_);
if (v_isSharedCheck_971_ == 0)
{
lean_object* v_unused_972_; lean_object* v_unused_973_; lean_object* v_unused_974_; lean_object* v_unused_975_; lean_object* v_unused_976_; 
v_unused_972_ = lean_ctor_get(v_impl_890_, 4);
lean_dec(v_unused_972_);
v_unused_973_ = lean_ctor_get(v_impl_890_, 3);
lean_dec(v_unused_973_);
v_unused_974_ = lean_ctor_get(v_impl_890_, 2);
lean_dec(v_unused_974_);
v_unused_975_ = lean_ctor_get(v_impl_890_, 1);
lean_dec(v_unused_975_);
v_unused_976_ = lean_ctor_get(v_impl_890_, 0);
lean_dec(v_unused_976_);
v___x_907_ = v_impl_890_;
v_isShared_908_ = v_isSharedCheck_971_;
goto v_resetjp_906_;
}
else
{
lean_dec(v_impl_890_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_971_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v_size_909_; lean_object* v_size_910_; lean_object* v_k_911_; lean_object* v_v_912_; lean_object* v_l_913_; lean_object* v_r_914_; lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
v_size_909_ = lean_ctor_get(v_l_896_, 0);
v_size_910_ = lean_ctor_get(v_r_897_, 0);
v_k_911_ = lean_ctor_get(v_r_897_, 1);
v_v_912_ = lean_ctor_get(v_r_897_, 2);
v_l_913_ = lean_ctor_get(v_r_897_, 3);
v_r_914_ = lean_ctor_get(v_r_897_, 4);
v___x_915_ = lean_unsigned_to_nat(2u);
v___x_916_ = lean_nat_mul(v___x_915_, v_size_909_);
v___x_917_ = lean_nat_dec_lt(v_size_910_, v___x_916_);
lean_dec(v___x_916_);
if (v___x_917_ == 0)
{
lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_946_; 
lean_inc(v_r_914_);
lean_inc(v_l_913_);
lean_inc(v_v_912_);
lean_inc(v_k_911_);
v_isSharedCheck_946_ = !lean_is_exclusive(v_r_897_);
if (v_isSharedCheck_946_ == 0)
{
lean_object* v_unused_947_; lean_object* v_unused_948_; lean_object* v_unused_949_; lean_object* v_unused_950_; lean_object* v_unused_951_; 
v_unused_947_ = lean_ctor_get(v_r_897_, 4);
lean_dec(v_unused_947_);
v_unused_948_ = lean_ctor_get(v_r_897_, 3);
lean_dec(v_unused_948_);
v_unused_949_ = lean_ctor_get(v_r_897_, 2);
lean_dec(v_unused_949_);
v_unused_950_ = lean_ctor_get(v_r_897_, 1);
lean_dec(v_unused_950_);
v_unused_951_ = lean_ctor_get(v_r_897_, 0);
lean_dec(v_unused_951_);
v___x_919_ = v_r_897_;
v_isShared_920_ = v_isSharedCheck_946_;
goto v_resetjp_918_;
}
else
{
lean_dec(v_r_897_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_946_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___x_934_; lean_object* v___y_936_; 
v___x_921_ = lean_nat_add(v___x_891_, v_size_893_);
lean_dec(v_size_893_);
v___x_922_ = lean_nat_add(v___x_921_, v_size_892_);
lean_dec(v___x_921_);
v___x_934_ = lean_nat_add(v___x_891_, v_size_909_);
if (lean_obj_tag(v_l_913_) == 0)
{
lean_object* v_size_944_; 
v_size_944_ = lean_ctor_get(v_l_913_, 0);
lean_inc(v_size_944_);
v___y_936_ = v_size_944_;
goto v___jp_935_;
}
else
{
lean_object* v___x_945_; 
v___x_945_ = lean_unsigned_to_nat(0u);
v___y_936_ = v___x_945_;
goto v___jp_935_;
}
v___jp_923_:
{
lean_object* v___x_927_; lean_object* v___x_929_; 
v___x_927_ = lean_nat_add(v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec(v___y_925_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 4, v_r_885_);
lean_ctor_set(v___x_919_, 3, v_r_914_);
lean_ctor_set(v___x_919_, 2, v_v_883_);
lean_ctor_set(v___x_919_, 1, v_k_882_);
lean_ctor_set(v___x_919_, 0, v___x_927_);
v___x_929_ = v___x_919_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_927_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_k_882_);
lean_ctor_set(v_reuseFailAlloc_933_, 2, v_v_883_);
lean_ctor_set(v_reuseFailAlloc_933_, 3, v_r_914_);
lean_ctor_set(v_reuseFailAlloc_933_, 4, v_r_885_);
v___x_929_ = v_reuseFailAlloc_933_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
lean_object* v___x_931_; 
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 4, v___x_929_);
lean_ctor_set(v___x_907_, 3, v___y_924_);
lean_ctor_set(v___x_907_, 2, v_v_912_);
lean_ctor_set(v___x_907_, 1, v_k_911_);
lean_ctor_set(v___x_907_, 0, v___x_922_);
v___x_931_ = v___x_907_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_922_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_k_911_);
lean_ctor_set(v_reuseFailAlloc_932_, 2, v_v_912_);
lean_ctor_set(v_reuseFailAlloc_932_, 3, v___y_924_);
lean_ctor_set(v_reuseFailAlloc_932_, 4, v___x_929_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
v___jp_935_:
{
lean_object* v___x_937_; lean_object* v___x_939_; 
v___x_937_ = lean_nat_add(v___x_934_, v___y_936_);
lean_dec(v___y_936_);
lean_dec(v___x_934_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 4, v_l_913_);
lean_ctor_set(v___x_887_, 3, v_l_896_);
lean_ctor_set(v___x_887_, 2, v_v_895_);
lean_ctor_set(v___x_887_, 1, v_k_894_);
lean_ctor_set(v___x_887_, 0, v___x_937_);
v___x_939_ = v___x_887_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v_k_894_);
lean_ctor_set(v_reuseFailAlloc_943_, 2, v_v_895_);
lean_ctor_set(v_reuseFailAlloc_943_, 3, v_l_896_);
lean_ctor_set(v_reuseFailAlloc_943_, 4, v_l_913_);
v___x_939_ = v_reuseFailAlloc_943_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_940_; 
v___x_940_ = lean_nat_add(v___x_891_, v_size_892_);
if (lean_obj_tag(v_r_914_) == 0)
{
lean_object* v_size_941_; 
v_size_941_ = lean_ctor_get(v_r_914_, 0);
lean_inc(v_size_941_);
v___y_924_ = v___x_939_;
v___y_925_ = v___x_940_;
v___y_926_ = v_size_941_;
goto v___jp_923_;
}
else
{
lean_object* v___x_942_; 
v___x_942_ = lean_unsigned_to_nat(0u);
v___y_924_ = v___x_939_;
v___y_925_ = v___x_940_;
v___y_926_ = v___x_942_;
goto v___jp_923_;
}
}
}
}
}
else
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_957_; 
lean_del_object(v___x_887_);
v___x_952_ = lean_nat_add(v___x_891_, v_size_893_);
lean_dec(v_size_893_);
v___x_953_ = lean_nat_add(v___x_952_, v_size_892_);
lean_dec(v___x_952_);
v___x_954_ = lean_nat_add(v___x_891_, v_size_892_);
v___x_955_ = lean_nat_add(v___x_954_, v_size_910_);
lean_dec(v___x_954_);
lean_inc_ref(v_r_885_);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 4, v_r_885_);
lean_ctor_set(v___x_907_, 3, v_r_897_);
lean_ctor_set(v___x_907_, 2, v_v_883_);
lean_ctor_set(v___x_907_, 1, v_k_882_);
lean_ctor_set(v___x_907_, 0, v___x_955_);
v___x_957_ = v___x_907_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_955_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_k_882_);
lean_ctor_set(v_reuseFailAlloc_970_, 2, v_v_883_);
lean_ctor_set(v_reuseFailAlloc_970_, 3, v_r_897_);
lean_ctor_set(v_reuseFailAlloc_970_, 4, v_r_885_);
v___x_957_ = v_reuseFailAlloc_970_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
v_isSharedCheck_964_ = !lean_is_exclusive(v_r_885_);
if (v_isSharedCheck_964_ == 0)
{
lean_object* v_unused_965_; lean_object* v_unused_966_; lean_object* v_unused_967_; lean_object* v_unused_968_; lean_object* v_unused_969_; 
v_unused_965_ = lean_ctor_get(v_r_885_, 4);
lean_dec(v_unused_965_);
v_unused_966_ = lean_ctor_get(v_r_885_, 3);
lean_dec(v_unused_966_);
v_unused_967_ = lean_ctor_get(v_r_885_, 2);
lean_dec(v_unused_967_);
v_unused_968_ = lean_ctor_get(v_r_885_, 1);
lean_dec(v_unused_968_);
v_unused_969_ = lean_ctor_get(v_r_885_, 0);
lean_dec(v_unused_969_);
v___x_959_ = v_r_885_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_dec(v_r_885_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 4, v___x_957_);
lean_ctor_set(v___x_959_, 3, v_l_896_);
lean_ctor_set(v___x_959_, 2, v_v_895_);
lean_ctor_set(v___x_959_, 1, v_k_894_);
lean_ctor_set(v___x_959_, 0, v___x_953_);
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_k_894_);
lean_ctor_set(v_reuseFailAlloc_963_, 2, v_v_895_);
lean_ctor_set(v_reuseFailAlloc_963_, 3, v_l_896_);
lean_ctor_set(v_reuseFailAlloc_963_, 4, v___x_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_977_; 
v_l_977_ = lean_ctor_get(v_impl_890_, 3);
if (lean_obj_tag(v_l_977_) == 0)
{
lean_object* v_r_978_; lean_object* v_k_979_; lean_object* v_v_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_991_; 
lean_inc_ref(v_l_977_);
v_r_978_ = lean_ctor_get(v_impl_890_, 4);
v_k_979_ = lean_ctor_get(v_impl_890_, 1);
v_v_980_ = lean_ctor_get(v_impl_890_, 2);
v_isSharedCheck_991_ = !lean_is_exclusive(v_impl_890_);
if (v_isSharedCheck_991_ == 0)
{
lean_object* v_unused_992_; lean_object* v_unused_993_; 
v_unused_992_ = lean_ctor_get(v_impl_890_, 3);
lean_dec(v_unused_992_);
v_unused_993_ = lean_ctor_get(v_impl_890_, 0);
lean_dec(v_unused_993_);
v___x_982_ = v_impl_890_;
v_isShared_983_ = v_isSharedCheck_991_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_r_978_);
lean_inc(v_v_980_);
lean_inc(v_k_979_);
lean_dec(v_impl_890_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_991_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_984_; lean_object* v___x_986_; 
v___x_984_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_978_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 3, v_r_978_);
lean_ctor_set(v___x_982_, 2, v_v_883_);
lean_ctor_set(v___x_982_, 1, v_k_882_);
lean_ctor_set(v___x_982_, 0, v___x_891_);
v___x_986_ = v___x_982_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_891_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_k_882_);
lean_ctor_set(v_reuseFailAlloc_990_, 2, v_v_883_);
lean_ctor_set(v_reuseFailAlloc_990_, 3, v_r_978_);
lean_ctor_set(v_reuseFailAlloc_990_, 4, v_r_978_);
v___x_986_ = v_reuseFailAlloc_990_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_988_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 4, v___x_986_);
lean_ctor_set(v___x_887_, 3, v_l_977_);
lean_ctor_set(v___x_887_, 2, v_v_980_);
lean_ctor_set(v___x_887_, 1, v_k_979_);
lean_ctor_set(v___x_887_, 0, v___x_984_);
v___x_988_ = v___x_887_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_984_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_k_979_);
lean_ctor_set(v_reuseFailAlloc_989_, 2, v_v_980_);
lean_ctor_set(v_reuseFailAlloc_989_, 3, v_l_977_);
lean_ctor_set(v_reuseFailAlloc_989_, 4, v___x_986_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
else
{
lean_object* v_r_994_; 
v_r_994_ = lean_ctor_get(v_impl_890_, 4);
lean_inc(v_r_994_);
if (lean_obj_tag(v_r_994_) == 0)
{
lean_object* v_k_995_; lean_object* v_v_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1019_; 
lean_inc(v_l_977_);
v_k_995_ = lean_ctor_get(v_impl_890_, 1);
v_v_996_ = lean_ctor_get(v_impl_890_, 2);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_impl_890_);
if (v_isSharedCheck_1019_ == 0)
{
lean_object* v_unused_1020_; lean_object* v_unused_1021_; lean_object* v_unused_1022_; 
v_unused_1020_ = lean_ctor_get(v_impl_890_, 4);
lean_dec(v_unused_1020_);
v_unused_1021_ = lean_ctor_get(v_impl_890_, 3);
lean_dec(v_unused_1021_);
v_unused_1022_ = lean_ctor_get(v_impl_890_, 0);
lean_dec(v_unused_1022_);
v___x_998_ = v_impl_890_;
v_isShared_999_ = v_isSharedCheck_1019_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_v_996_);
lean_inc(v_k_995_);
lean_dec(v_impl_890_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1019_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v_k_1000_; lean_object* v_v_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1015_; 
v_k_1000_ = lean_ctor_get(v_r_994_, 1);
v_v_1001_ = lean_ctor_get(v_r_994_, 2);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_r_994_);
if (v_isSharedCheck_1015_ == 0)
{
lean_object* v_unused_1016_; lean_object* v_unused_1017_; lean_object* v_unused_1018_; 
v_unused_1016_ = lean_ctor_get(v_r_994_, 4);
lean_dec(v_unused_1016_);
v_unused_1017_ = lean_ctor_get(v_r_994_, 3);
lean_dec(v_unused_1017_);
v_unused_1018_ = lean_ctor_get(v_r_994_, 0);
lean_dec(v_unused_1018_);
v___x_1003_ = v_r_994_;
v_isShared_1004_ = v_isSharedCheck_1015_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_v_1001_);
lean_inc(v_k_1000_);
lean_dec(v_r_994_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1015_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1005_; lean_object* v___x_1007_; 
v___x_1005_ = lean_unsigned_to_nat(3u);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 4, v_l_977_);
lean_ctor_set(v___x_1003_, 3, v_l_977_);
lean_ctor_set(v___x_1003_, 2, v_v_996_);
lean_ctor_set(v___x_1003_, 1, v_k_995_);
lean_ctor_set(v___x_1003_, 0, v___x_891_);
v___x_1007_ = v___x_1003_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_891_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v_k_995_);
lean_ctor_set(v_reuseFailAlloc_1014_, 2, v_v_996_);
lean_ctor_set(v_reuseFailAlloc_1014_, 3, v_l_977_);
lean_ctor_set(v_reuseFailAlloc_1014_, 4, v_l_977_);
v___x_1007_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1009_; 
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 4, v_l_977_);
lean_ctor_set(v___x_998_, 2, v_v_883_);
lean_ctor_set(v___x_998_, 1, v_k_882_);
lean_ctor_set(v___x_998_, 0, v___x_891_);
v___x_1009_ = v___x_998_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_891_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_k_882_);
lean_ctor_set(v_reuseFailAlloc_1013_, 2, v_v_883_);
lean_ctor_set(v_reuseFailAlloc_1013_, 3, v_l_977_);
lean_ctor_set(v_reuseFailAlloc_1013_, 4, v_l_977_);
v___x_1009_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
lean_object* v___x_1011_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 4, v___x_1009_);
lean_ctor_set(v___x_887_, 3, v___x_1007_);
lean_ctor_set(v___x_887_, 2, v_v_1001_);
lean_ctor_set(v___x_887_, 1, v_k_1000_);
lean_ctor_set(v___x_887_, 0, v___x_1005_);
v___x_1011_ = v___x_887_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1005_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_k_1000_);
lean_ctor_set(v_reuseFailAlloc_1012_, 2, v_v_1001_);
lean_ctor_set(v_reuseFailAlloc_1012_, 3, v___x_1007_);
lean_ctor_set(v_reuseFailAlloc_1012_, 4, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
}
}
else
{
lean_object* v___x_1023_; lean_object* v___x_1025_; 
v___x_1023_ = lean_unsigned_to_nat(2u);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 4, v_r_994_);
lean_ctor_set(v___x_887_, 3, v_impl_890_);
lean_ctor_set(v___x_887_, 0, v___x_1023_);
v___x_1025_ = v___x_887_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1023_);
lean_ctor_set(v_reuseFailAlloc_1026_, 1, v_k_882_);
lean_ctor_set(v_reuseFailAlloc_1026_, 2, v_v_883_);
lean_ctor_set(v_reuseFailAlloc_1026_, 3, v_impl_890_);
lean_ctor_set(v_reuseFailAlloc_1026_, 4, v_r_994_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1028_; 
lean_dec(v_v_883_);
lean_dec(v_k_882_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 2, v_v_879_);
lean_ctor_set(v___x_887_, 1, v_k_878_);
v___x_1028_ = v___x_887_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_size_881_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_k_878_);
lean_ctor_set(v_reuseFailAlloc_1029_, 2, v_v_879_);
lean_ctor_set(v_reuseFailAlloc_1029_, 3, v_l_884_);
lean_ctor_set(v_reuseFailAlloc_1029_, 4, v_r_885_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
default: 
{
lean_object* v_impl_1030_; lean_object* v___x_1031_; 
lean_dec(v_size_881_);
v_impl_1030_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_878_, v_v_879_, v_r_885_);
v___x_1031_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_884_) == 0)
{
lean_object* v_size_1032_; lean_object* v_size_1033_; lean_object* v_k_1034_; lean_object* v_v_1035_; lean_object* v_l_1036_; lean_object* v_r_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; uint8_t v___x_1040_; 
v_size_1032_ = lean_ctor_get(v_l_884_, 0);
v_size_1033_ = lean_ctor_get(v_impl_1030_, 0);
v_k_1034_ = lean_ctor_get(v_impl_1030_, 1);
v_v_1035_ = lean_ctor_get(v_impl_1030_, 2);
v_l_1036_ = lean_ctor_get(v_impl_1030_, 3);
lean_inc(v_l_1036_);
v_r_1037_ = lean_ctor_get(v_impl_1030_, 4);
v___x_1038_ = lean_unsigned_to_nat(3u);
v___x_1039_ = lean_nat_mul(v___x_1038_, v_size_1032_);
v___x_1040_ = lean_nat_dec_lt(v___x_1039_, v_size_1033_);
lean_dec(v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1044_; 
lean_dec(v_l_1036_);
v___x_1041_ = lean_nat_add(v___x_1031_, v_size_1032_);
v___x_1042_ = lean_nat_add(v___x_1041_, v_size_1033_);
lean_dec(v___x_1041_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 4, v_impl_1030_);
lean_ctor_set(v___x_887_, 0, v___x_1042_);
v___x_1044_ = v___x_887_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_k_882_);
lean_ctor_set(v_reuseFailAlloc_1045_, 2, v_v_883_);
lean_ctor_set(v_reuseFailAlloc_1045_, 3, v_l_884_);
lean_ctor_set(v_reuseFailAlloc_1045_, 4, v_impl_1030_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
else
{
lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1109_; 
lean_inc(v_r_1037_);
lean_inc(v_v_1035_);
lean_inc(v_k_1034_);
lean_inc(v_size_1033_);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_impl_1030_);
if (v_isSharedCheck_1109_ == 0)
{
lean_object* v_unused_1110_; lean_object* v_unused_1111_; lean_object* v_unused_1112_; lean_object* v_unused_1113_; lean_object* v_unused_1114_; 
v_unused_1110_ = lean_ctor_get(v_impl_1030_, 4);
lean_dec(v_unused_1110_);
v_unused_1111_ = lean_ctor_get(v_impl_1030_, 3);
lean_dec(v_unused_1111_);
v_unused_1112_ = lean_ctor_get(v_impl_1030_, 2);
lean_dec(v_unused_1112_);
v_unused_1113_ = lean_ctor_get(v_impl_1030_, 1);
lean_dec(v_unused_1113_);
v_unused_1114_ = lean_ctor_get(v_impl_1030_, 0);
lean_dec(v_unused_1114_);
v___x_1047_ = v_impl_1030_;
v_isShared_1048_ = v_isSharedCheck_1109_;
goto v_resetjp_1046_;
}
else
{
lean_dec(v_impl_1030_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1109_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v_size_1049_; lean_object* v_k_1050_; lean_object* v_v_1051_; lean_object* v_l_1052_; lean_object* v_r_1053_; lean_object* v_size_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; uint8_t v___x_1057_; 
v_size_1049_ = lean_ctor_get(v_l_1036_, 0);
v_k_1050_ = lean_ctor_get(v_l_1036_, 1);
v_v_1051_ = lean_ctor_get(v_l_1036_, 2);
v_l_1052_ = lean_ctor_get(v_l_1036_, 3);
v_r_1053_ = lean_ctor_get(v_l_1036_, 4);
v_size_1054_ = lean_ctor_get(v_r_1037_, 0);
v___x_1055_ = lean_unsigned_to_nat(2u);
v___x_1056_ = lean_nat_mul(v___x_1055_, v_size_1054_);
v___x_1057_ = lean_nat_dec_lt(v_size_1049_, v___x_1056_);
lean_dec(v___x_1056_);
if (v___x_1057_ == 0)
{
lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1085_; 
lean_inc(v_r_1053_);
lean_inc(v_l_1052_);
lean_inc(v_v_1051_);
lean_inc(v_k_1050_);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_l_1036_);
if (v_isSharedCheck_1085_ == 0)
{
lean_object* v_unused_1086_; lean_object* v_unused_1087_; lean_object* v_unused_1088_; lean_object* v_unused_1089_; lean_object* v_unused_1090_; 
v_unused_1086_ = lean_ctor_get(v_l_1036_, 4);
lean_dec(v_unused_1086_);
v_unused_1087_ = lean_ctor_get(v_l_1036_, 3);
lean_dec(v_unused_1087_);
v_unused_1088_ = lean_ctor_get(v_l_1036_, 2);
lean_dec(v_unused_1088_);
v_unused_1089_ = lean_ctor_get(v_l_1036_, 1);
lean_dec(v_unused_1089_);
v_unused_1090_ = lean_ctor_get(v_l_1036_, 0);
lean_dec(v_unused_1090_);
v___x_1059_ = v_l_1036_;
v_isShared_1060_ = v_isSharedCheck_1085_;
goto v_resetjp_1058_;
}
else
{
lean_dec(v_l_1036_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1085_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1075_; 
v___x_1061_ = lean_nat_add(v___x_1031_, v_size_1032_);
v___x_1062_ = lean_nat_add(v___x_1061_, v_size_1033_);
lean_dec(v_size_1033_);
if (lean_obj_tag(v_l_1052_) == 0)
{
lean_object* v_size_1083_; 
v_size_1083_ = lean_ctor_get(v_l_1052_, 0);
lean_inc(v_size_1083_);
v___y_1075_ = v_size_1083_;
goto v___jp_1074_;
}
else
{
lean_object* v___x_1084_; 
v___x_1084_ = lean_unsigned_to_nat(0u);
v___y_1075_ = v___x_1084_;
goto v___jp_1074_;
}
v___jp_1063_:
{
lean_object* v___x_1067_; lean_object* v___x_1069_; 
v___x_1067_ = lean_nat_add(v___y_1064_, v___y_1066_);
lean_dec(v___y_1066_);
lean_dec(v___y_1064_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 4, v_r_1037_);
lean_ctor_set(v___x_1059_, 3, v_r_1053_);
lean_ctor_set(v___x_1059_, 2, v_v_1035_);
lean_ctor_set(v___x_1059_, 1, v_k_1034_);
lean_ctor_set(v___x_1059_, 0, v___x_1067_);
v___x_1069_ = v___x_1059_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1067_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_k_1034_);
lean_ctor_set(v_reuseFailAlloc_1073_, 2, v_v_1035_);
lean_ctor_set(v_reuseFailAlloc_1073_, 3, v_r_1053_);
lean_ctor_set(v_reuseFailAlloc_1073_, 4, v_r_1037_);
v___x_1069_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
lean_object* v___x_1071_; 
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 4, v___x_1069_);
lean_ctor_set(v___x_1047_, 3, v___y_1065_);
lean_ctor_set(v___x_1047_, 2, v_v_1051_);
lean_ctor_set(v___x_1047_, 1, v_k_1050_);
lean_ctor_set(v___x_1047_, 0, v___x_1062_);
v___x_1071_ = v___x_1047_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1062_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v_k_1050_);
lean_ctor_set(v_reuseFailAlloc_1072_, 2, v_v_1051_);
lean_ctor_set(v_reuseFailAlloc_1072_, 3, v___y_1065_);
lean_ctor_set(v_reuseFailAlloc_1072_, 4, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
v___jp_1074_:
{
lean_object* v___x_1076_; lean_object* v___x_1078_; 
v___x_1076_ = lean_nat_add(v___x_1061_, v___y_1075_);
lean_dec(v___y_1075_);
lean_dec(v___x_1061_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 4, v_l_1052_);
lean_ctor_set(v___x_887_, 0, v___x_1076_);
v___x_1078_ = v___x_887_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_k_882_);
lean_ctor_set(v_reuseFailAlloc_1082_, 2, v_v_883_);
lean_ctor_set(v_reuseFailAlloc_1082_, 3, v_l_884_);
lean_ctor_set(v_reuseFailAlloc_1082_, 4, v_l_1052_);
v___x_1078_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_nat_add(v___x_1031_, v_size_1054_);
if (lean_obj_tag(v_r_1053_) == 0)
{
lean_object* v_size_1080_; 
v_size_1080_ = lean_ctor_get(v_r_1053_, 0);
lean_inc(v_size_1080_);
v___y_1064_ = v___x_1079_;
v___y_1065_ = v___x_1078_;
v___y_1066_ = v_size_1080_;
goto v___jp_1063_;
}
else
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_unsigned_to_nat(0u);
v___y_1064_ = v___x_1079_;
v___y_1065_ = v___x_1078_;
v___y_1066_ = v___x_1081_;
goto v___jp_1063_;
}
}
}
}
}
else
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1095_; 
lean_del_object(v___x_887_);
v___x_1091_ = lean_nat_add(v___x_1031_, v_size_1032_);
v___x_1092_ = lean_nat_add(v___x_1091_, v_size_1033_);
lean_dec(v_size_1033_);
v___x_1093_ = lean_nat_add(v___x_1091_, v_size_1049_);
lean_dec(v___x_1091_);
lean_inc_ref(v_l_884_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 4, v_l_1036_);
lean_ctor_set(v___x_1047_, 3, v_l_884_);
lean_ctor_set(v___x_1047_, 2, v_v_883_);
lean_ctor_set(v___x_1047_, 1, v_k_882_);
lean_ctor_set(v___x_1047_, 0, v___x_1093_);
v___x_1095_ = v___x_1047_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_k_882_);
lean_ctor_set(v_reuseFailAlloc_1108_, 2, v_v_883_);
lean_ctor_set(v_reuseFailAlloc_1108_, 3, v_l_884_);
lean_ctor_set(v_reuseFailAlloc_1108_, 4, v_l_1036_);
v___x_1095_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
v_isSharedCheck_1102_ = !lean_is_exclusive(v_l_884_);
if (v_isSharedCheck_1102_ == 0)
{
lean_object* v_unused_1103_; lean_object* v_unused_1104_; lean_object* v_unused_1105_; lean_object* v_unused_1106_; lean_object* v_unused_1107_; 
v_unused_1103_ = lean_ctor_get(v_l_884_, 4);
lean_dec(v_unused_1103_);
v_unused_1104_ = lean_ctor_get(v_l_884_, 3);
lean_dec(v_unused_1104_);
v_unused_1105_ = lean_ctor_get(v_l_884_, 2);
lean_dec(v_unused_1105_);
v_unused_1106_ = lean_ctor_get(v_l_884_, 1);
lean_dec(v_unused_1106_);
v_unused_1107_ = lean_ctor_get(v_l_884_, 0);
lean_dec(v_unused_1107_);
v___x_1097_ = v_l_884_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_dec(v_l_884_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 4, v_r_1037_);
lean_ctor_set(v___x_1097_, 3, v___x_1095_);
lean_ctor_set(v___x_1097_, 2, v_v_1035_);
lean_ctor_set(v___x_1097_, 1, v_k_1034_);
lean_ctor_set(v___x_1097_, 0, v___x_1092_);
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v_k_1034_);
lean_ctor_set(v_reuseFailAlloc_1101_, 2, v_v_1035_);
lean_ctor_set(v_reuseFailAlloc_1101_, 3, v___x_1095_);
lean_ctor_set(v_reuseFailAlloc_1101_, 4, v_r_1037_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1115_; 
v_l_1115_ = lean_ctor_get(v_impl_1030_, 3);
lean_inc(v_l_1115_);
if (lean_obj_tag(v_l_1115_) == 0)
{
lean_object* v_r_1116_; lean_object* v_k_1117_; lean_object* v_v_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1141_; 
v_r_1116_ = lean_ctor_get(v_impl_1030_, 4);
v_k_1117_ = lean_ctor_get(v_impl_1030_, 1);
v_v_1118_ = lean_ctor_get(v_impl_1030_, 2);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_impl_1030_);
if (v_isSharedCheck_1141_ == 0)
{
lean_object* v_unused_1142_; lean_object* v_unused_1143_; 
v_unused_1142_ = lean_ctor_get(v_impl_1030_, 3);
lean_dec(v_unused_1142_);
v_unused_1143_ = lean_ctor_get(v_impl_1030_, 0);
lean_dec(v_unused_1143_);
v___x_1120_ = v_impl_1030_;
v_isShared_1121_ = v_isSharedCheck_1141_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_r_1116_);
lean_inc(v_v_1118_);
lean_inc(v_k_1117_);
lean_dec(v_impl_1030_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1141_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v_k_1122_; lean_object* v_v_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1137_; 
v_k_1122_ = lean_ctor_get(v_l_1115_, 1);
v_v_1123_ = lean_ctor_get(v_l_1115_, 2);
v_isSharedCheck_1137_ = !lean_is_exclusive(v_l_1115_);
if (v_isSharedCheck_1137_ == 0)
{
lean_object* v_unused_1138_; lean_object* v_unused_1139_; lean_object* v_unused_1140_; 
v_unused_1138_ = lean_ctor_get(v_l_1115_, 4);
lean_dec(v_unused_1138_);
v_unused_1139_ = lean_ctor_get(v_l_1115_, 3);
lean_dec(v_unused_1139_);
v_unused_1140_ = lean_ctor_get(v_l_1115_, 0);
lean_dec(v_unused_1140_);
v___x_1125_ = v_l_1115_;
v_isShared_1126_ = v_isSharedCheck_1137_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_v_1123_);
lean_inc(v_k_1122_);
lean_dec(v_l_1115_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1137_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; lean_object* v___x_1129_; 
v___x_1127_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1116_, 2);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 4, v_r_1116_);
lean_ctor_set(v___x_1125_, 3, v_r_1116_);
lean_ctor_set(v___x_1125_, 2, v_v_883_);
lean_ctor_set(v___x_1125_, 1, v_k_882_);
lean_ctor_set(v___x_1125_, 0, v___x_1031_);
v___x_1129_ = v___x_1125_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1031_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_k_882_);
lean_ctor_set(v_reuseFailAlloc_1136_, 2, v_v_883_);
lean_ctor_set(v_reuseFailAlloc_1136_, 3, v_r_1116_);
lean_ctor_set(v_reuseFailAlloc_1136_, 4, v_r_1116_);
v___x_1129_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_object* v___x_1131_; 
lean_inc(v_r_1116_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 3, v_r_1116_);
lean_ctor_set(v___x_1120_, 0, v___x_1031_);
v___x_1131_ = v___x_1120_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1031_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_k_1117_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v_v_1118_);
lean_ctor_set(v_reuseFailAlloc_1135_, 3, v_r_1116_);
lean_ctor_set(v_reuseFailAlloc_1135_, 4, v_r_1116_);
v___x_1131_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1133_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 4, v___x_1131_);
lean_ctor_set(v___x_887_, 3, v___x_1129_);
lean_ctor_set(v___x_887_, 2, v_v_1123_);
lean_ctor_set(v___x_887_, 1, v_k_1122_);
lean_ctor_set(v___x_887_, 0, v___x_1127_);
v___x_1133_ = v___x_887_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_k_1122_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v_v_1123_);
lean_ctor_set(v_reuseFailAlloc_1134_, 3, v___x_1129_);
lean_ctor_set(v_reuseFailAlloc_1134_, 4, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
}
}
else
{
lean_object* v_r_1144_; 
v_r_1144_ = lean_ctor_get(v_impl_1030_, 4);
lean_inc(v_r_1144_);
if (lean_obj_tag(v_r_1144_) == 0)
{
lean_object* v_k_1145_; lean_object* v_v_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1157_; 
v_k_1145_ = lean_ctor_get(v_impl_1030_, 1);
v_v_1146_ = lean_ctor_get(v_impl_1030_, 2);
v_isSharedCheck_1157_ = !lean_is_exclusive(v_impl_1030_);
if (v_isSharedCheck_1157_ == 0)
{
lean_object* v_unused_1158_; lean_object* v_unused_1159_; lean_object* v_unused_1160_; 
v_unused_1158_ = lean_ctor_get(v_impl_1030_, 4);
lean_dec(v_unused_1158_);
v_unused_1159_ = lean_ctor_get(v_impl_1030_, 3);
lean_dec(v_unused_1159_);
v_unused_1160_ = lean_ctor_get(v_impl_1030_, 0);
lean_dec(v_unused_1160_);
v___x_1148_ = v_impl_1030_;
v_isShared_1149_ = v_isSharedCheck_1157_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_v_1146_);
lean_inc(v_k_1145_);
lean_dec(v_impl_1030_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1157_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1150_ = lean_unsigned_to_nat(3u);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 4, v_l_1115_);
lean_ctor_set(v___x_1148_, 2, v_v_883_);
lean_ctor_set(v___x_1148_, 1, v_k_882_);
lean_ctor_set(v___x_1148_, 0, v___x_1031_);
v___x_1152_ = v___x_1148_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1031_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_k_882_);
lean_ctor_set(v_reuseFailAlloc_1156_, 2, v_v_883_);
lean_ctor_set(v_reuseFailAlloc_1156_, 3, v_l_1115_);
lean_ctor_set(v_reuseFailAlloc_1156_, 4, v_l_1115_);
v___x_1152_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
lean_object* v___x_1154_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 4, v_r_1144_);
lean_ctor_set(v___x_887_, 3, v___x_1152_);
lean_ctor_set(v___x_887_, 2, v_v_1146_);
lean_ctor_set(v___x_887_, 1, v_k_1145_);
lean_ctor_set(v___x_887_, 0, v___x_1150_);
v___x_1154_ = v___x_887_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1150_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_k_1145_);
lean_ctor_set(v_reuseFailAlloc_1155_, 2, v_v_1146_);
lean_ctor_set(v_reuseFailAlloc_1155_, 3, v___x_1152_);
lean_ctor_set(v_reuseFailAlloc_1155_, 4, v_r_1144_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
else
{
lean_object* v___x_1161_; lean_object* v___x_1163_; 
v___x_1161_ = lean_unsigned_to_nat(2u);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 4, v_impl_1030_);
lean_ctor_set(v___x_887_, 3, v_r_1144_);
lean_ctor_set(v___x_887_, 0, v___x_1161_);
v___x_1163_ = v___x_887_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_k_882_);
lean_ctor_set(v_reuseFailAlloc_1164_, 2, v_v_883_);
lean_ctor_set(v_reuseFailAlloc_1164_, 3, v_r_1144_);
lean_ctor_set(v_reuseFailAlloc_1164_, 4, v_impl_1030_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = lean_unsigned_to_nat(1u);
v___x_1167_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
lean_ctor_set(v___x_1167_, 1, v_k_878_);
lean_ctor_set(v___x_1167_, 2, v_v_879_);
lean_ctor_set(v___x_1167_, 3, v_t_880_);
lean_ctor_set(v___x_1167_, 4, v_t_880_);
return v___x_1167_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(lean_object* v_as_x27_1168_, lean_object* v_b_1169_){
_start:
{
if (lean_obj_tag(v_as_x27_1168_) == 0)
{
return v_b_1169_;
}
else
{
lean_object* v_head_1170_; lean_object* v_tail_1171_; lean_object* v_fst_1172_; lean_object* v_snd_1173_; lean_object* v_r_1174_; 
v_head_1170_ = lean_ctor_get(v_as_x27_1168_, 0);
v_tail_1171_ = lean_ctor_get(v_as_x27_1168_, 1);
v_fst_1172_ = lean_ctor_get(v_head_1170_, 0);
v_snd_1173_ = lean_ctor_get(v_head_1170_, 1);
lean_inc(v_snd_1173_);
lean_inc(v_fst_1172_);
v_r_1174_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_fst_1172_, v_snd_1173_, v_b_1169_);
v_as_x27_1168_ = v_tail_1171_;
v_b_1169_ = v_r_1174_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg___boxed(lean_object* v_as_x27_1176_, lean_object* v_b_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_as_x27_1176_, v_b_1177_);
lean_dec(v_as_x27_1176_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mkObj(lean_object* v_o_1179_){
_start:
{
lean_object* v_r_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v_r_1180_ = lean_box(1);
v___x_1181_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_o_1179_, v_r_1180_);
v___x_1182_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mkObj___boxed(lean_object* v_o_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_Json_mkObj(v_o_1183_);
lean_dec(v_o_1183_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0(lean_object* v_00_u03b2_1185_, lean_object* v_k_1186_, lean_object* v_v_1187_, lean_object* v_t_1188_, lean_object* v_hl_1189_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_1186_, v_v_1187_, v_t_1188_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1(lean_object* v_as_1191_, lean_object* v_as_x27_1192_, lean_object* v_b_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_as_x27_1192_, v_b_1193_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___boxed(lean_object* v_as_1196_, lean_object* v_as_x27_1197_, lean_object* v_b_1198_, lean_object* v_a_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1(v_as_1196_, v_as_x27_1197_, v_b_1198_, v_a_1199_);
lean_dec(v_as_x27_1197_);
lean_dec(v_as_1196_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeNat___lam__0(lean_object* v_n_1201_){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = l_Lean_JsonNumber_fromNat(v_n_1201_);
v___x_1203_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeInt___lam__0(lean_object* v_n_1206_){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = l_Lean_JsonNumber_fromInt(v_n_1206_);
v___x_1208_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeString___lam__0(lean_object* v_s_1211_){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1212_, 0, v_s_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeBool___lam__0(uint8_t v_b_1215_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1216_, 0, v_b_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeBool___lam__0___boxed(lean_object* v_b_1217_){
_start:
{
uint8_t v_b_boxed_1218_; lean_object* v_res_1219_; 
v_b_boxed_1218_ = lean_unbox(v_b_1217_);
v_res_1219_ = l_Lean_Json_instCoeBool___lam__0(v_b_boxed_1218_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instOfNat(lean_object* v_n_1222_){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = l_Lean_JsonNumber_fromNat(v_n_1222_);
v___x_1224_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
return v___x_1224_;
}
}
LEAN_EXPORT uint8_t l_Lean_Json_isNull(lean_object* v_x_1225_){
_start:
{
if (lean_obj_tag(v_x_1225_) == 0)
{
uint8_t v___x_1226_; 
v___x_1226_ = 1;
return v___x_1226_;
}
else
{
uint8_t v___x_1227_; 
v___x_1227_ = 0;
return v___x_1227_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_isNull___boxed(lean_object* v_x_1228_){
_start:
{
uint8_t v_res_1229_; lean_object* v_r_1230_; 
v_res_1229_ = l_Lean_Json_isNull(v_x_1228_);
lean_dec(v_x_1228_);
v_r_1230_ = lean_box(v_res_1229_);
return v_r_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObj_x3f(lean_object* v_x_1234_){
_start:
{
if (lean_obj_tag(v_x_1234_) == 5)
{
lean_object* v_kvPairs_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
v_kvPairs_1235_ = lean_ctor_get(v_x_1234_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_x_1234_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v_x_1234_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_kvPairs_1235_);
lean_dec(v_x_1234_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
lean_ctor_set_tag(v___x_1237_, 1);
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_kvPairs_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
else
{
lean_object* v___x_1243_; 
lean_dec(v_x_1234_);
v___x_1243_ = ((lean_object*)(l_Lean_Json_getObj_x3f___closed__1));
return v___x_1243_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getArr_x3f(lean_object* v_x_1247_){
_start:
{
if (lean_obj_tag(v_x_1247_) == 4)
{
lean_object* v_elems_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
v_elems_1248_ = lean_ctor_get(v_x_1247_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v_x_1247_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v_x_1247_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_elems_1248_);
lean_dec(v_x_1247_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
lean_ctor_set_tag(v___x_1250_, 1);
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_elems_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
else
{
lean_object* v___x_1256_; 
lean_dec(v_x_1247_);
v___x_1256_ = ((lean_object*)(l_Lean_Json_getArr_x3f___closed__1));
return v___x_1256_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getStr_x3f(lean_object* v_x_1260_){
_start:
{
if (lean_obj_tag(v_x_1260_) == 3)
{
lean_object* v_s_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
v_s_1261_ = lean_ctor_get(v_x_1260_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_x_1260_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v_x_1260_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_s_1261_);
lean_dec(v_x_1260_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
lean_ctor_set_tag(v___x_1263_, 1);
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_s_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
else
{
lean_object* v___x_1269_; 
lean_dec(v_x_1260_);
v___x_1269_ = ((lean_object*)(l_Lean_Json_getStr_x3f___closed__1));
return v___x_1269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getNat_x3f(lean_object* v_x_1273_){
_start:
{
if (lean_obj_tag(v_x_1273_) == 2)
{
lean_object* v_n_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1290_; 
v_n_1276_ = lean_ctor_get(v_x_1273_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v_x_1273_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1278_ = v_x_1273_;
v_isShared_1279_ = v_isSharedCheck_1290_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_n_1276_);
lean_dec(v_x_1273_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1290_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v_mantissa_1280_; lean_object* v_exponent_1281_; lean_object* v_natZero_1282_; lean_object* v_intZero_1283_; uint8_t v_isNeg_1284_; 
v_mantissa_1280_ = lean_ctor_get(v_n_1276_, 0);
lean_inc(v_mantissa_1280_);
v_exponent_1281_ = lean_ctor_get(v_n_1276_, 1);
lean_inc(v_exponent_1281_);
lean_dec_ref(v_n_1276_);
v_natZero_1282_ = lean_unsigned_to_nat(0u);
v_intZero_1283_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v_isNeg_1284_ = lean_int_dec_lt(v_mantissa_1280_, v_intZero_1283_);
if (v_isNeg_1284_ == 0)
{
uint8_t v___x_1285_; 
v___x_1285_ = lean_nat_dec_eq(v_exponent_1281_, v_natZero_1282_);
lean_dec(v_exponent_1281_);
if (v___x_1285_ == 0)
{
lean_dec(v_mantissa_1280_);
lean_del_object(v___x_1278_);
goto v___jp_1274_;
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; 
v_a_1286_ = lean_nat_abs(v_mantissa_1280_);
lean_dec(v_mantissa_1280_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set_tag(v___x_1278_, 1);
lean_ctor_set(v___x_1278_, 0, v_a_1286_);
v___x_1288_ = v___x_1278_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
else
{
lean_dec(v_exponent_1281_);
lean_dec(v_mantissa_1280_);
lean_del_object(v___x_1278_);
goto v___jp_1274_;
}
}
}
else
{
lean_dec(v_x_1273_);
goto v___jp_1274_;
}
v___jp_1274_:
{
lean_object* v___x_1275_; 
v___x_1275_ = ((lean_object*)(l_Lean_Json_getNat_x3f___closed__1));
return v___x_1275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getInt_x3f(lean_object* v_x_1294_){
_start:
{
if (lean_obj_tag(v_x_1294_) == 2)
{
lean_object* v_n_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1308_; 
v_n_1297_ = lean_ctor_get(v_x_1294_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v_x_1294_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1299_ = v_x_1294_;
v_isShared_1300_ = v_isSharedCheck_1308_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_n_1297_);
lean_dec(v_x_1294_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1308_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v_mantissa_1301_; lean_object* v_exponent_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; 
v_mantissa_1301_ = lean_ctor_get(v_n_1297_, 0);
lean_inc(v_mantissa_1301_);
v_exponent_1302_ = lean_ctor_get(v_n_1297_, 1);
lean_inc(v_exponent_1302_);
lean_dec_ref(v_n_1297_);
v___x_1303_ = lean_unsigned_to_nat(0u);
v___x_1304_ = lean_nat_dec_eq(v_exponent_1302_, v___x_1303_);
lean_dec(v_exponent_1302_);
if (v___x_1304_ == 0)
{
lean_dec(v_mantissa_1301_);
lean_del_object(v___x_1299_);
goto v___jp_1295_;
}
else
{
lean_object* v___x_1306_; 
if (v_isShared_1300_ == 0)
{
lean_ctor_set_tag(v___x_1299_, 1);
lean_ctor_set(v___x_1299_, 0, v_mantissa_1301_);
v___x_1306_ = v___x_1299_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_mantissa_1301_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
else
{
lean_dec(v_x_1294_);
goto v___jp_1295_;
}
v___jp_1295_:
{
lean_object* v___x_1296_; 
v___x_1296_ = ((lean_object*)(l_Lean_Json_getInt_x3f___closed__1));
return v___x_1296_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getBool_x3f(lean_object* v_x_1312_){
_start:
{
if (lean_obj_tag(v_x_1312_) == 1)
{
uint8_t v_b_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v_b_1313_ = lean_ctor_get_uint8(v_x_1312_, 0);
v___x_1314_ = lean_box(v_b_1313_);
v___x_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
return v___x_1315_;
}
else
{
lean_object* v___x_1316_; 
v___x_1316_ = ((lean_object*)(l_Lean_Json_getBool_x3f___closed__1));
return v___x_1316_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getBool_x3f___boxed(lean_object* v_x_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Lean_Json_getBool_x3f(v_x_1317_);
lean_dec(v_x_1317_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getNum_x3f(lean_object* v_x_1322_){
_start:
{
if (lean_obj_tag(v_x_1322_) == 2)
{
lean_object* v_n_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
v_n_1323_ = lean_ctor_get(v_x_1322_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v_x_1322_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1325_ = v_x_1322_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_n_1323_);
lean_dec(v_x_1322_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
lean_ctor_set_tag(v___x_1325_, 1);
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_n_1323_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
else
{
lean_object* v___x_1331_; 
lean_dec(v_x_1322_);
v___x_1331_ = ((lean_object*)(l_Lean_Json_getNum_x3f___closed__1));
return v___x_1331_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjVal_x3f(lean_object* v_x_1335_, lean_object* v_x_1336_){
_start:
{
if (lean_obj_tag(v_x_1335_) == 5)
{
lean_object* v_kvPairs_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1355_; 
v_kvPairs_1337_ = lean_ctor_get(v_x_1335_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v_x_1335_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1339_ = v_x_1335_;
v_isShared_1340_ = v_isSharedCheck_1355_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_kvPairs_1337_);
lean_dec(v_x_1335_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1355_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1341_; 
v___x_1341_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_kvPairs_1337_, v_x_1336_);
lean_dec(v_kvPairs_1337_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1342_ = ((lean_object*)(l_Lean_Json_getObjVal_x3f___closed__0));
v___x_1343_ = lean_string_append(v___x_1342_, v_x_1336_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set_tag(v___x_1339_, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1343_);
v___x_1345_ = v___x_1339_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1343_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
else
{
lean_object* v_val_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1354_; 
lean_del_object(v___x_1339_);
v_val_1347_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1349_ = v___x_1341_;
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_val_1347_);
lean_dec(v___x_1341_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_val_1347_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
}
else
{
lean_object* v___x_1356_; 
lean_dec(v_x_1335_);
v___x_1356_ = ((lean_object*)(l_Lean_Json_getObjVal_x3f___closed__1));
return v___x_1356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjVal_x3f___boxed(lean_object* v_x_1357_, lean_object* v_x_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Lean_Json_getObjVal_x3f(v_x_1357_, v_x_1358_);
lean_dec_ref(v_x_1358_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getArrVal_x3f(lean_object* v_x_1363_, lean_object* v_x_1364_){
_start:
{
if (lean_obj_tag(v_x_1363_) == 4)
{
lean_object* v_elems_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1381_; 
v_elems_1365_ = lean_ctor_get(v_x_1363_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v_x_1363_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1367_ = v_x_1363_;
v_isShared_1368_ = v_isSharedCheck_1381_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_elems_1365_);
lean_dec(v_x_1363_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1381_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1369_; uint8_t v___x_1370_; 
v___x_1369_ = lean_array_get_size(v_elems_1365_);
v___x_1370_ = lean_nat_dec_lt(v_x_1364_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1375_; 
lean_dec_ref(v_elems_1365_);
v___x_1371_ = ((lean_object*)(l_Lean_Json_getArrVal_x3f___closed__0));
v___x_1372_ = l_Nat_reprFast(v_x_1364_);
v___x_1373_ = lean_string_append(v___x_1371_, v___x_1372_);
lean_dec_ref(v___x_1372_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set_tag(v___x_1367_, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1373_);
v___x_1375_ = v___x_1367_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
else
{
lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1377_ = lean_array_fget(v_elems_1365_, v_x_1364_);
lean_dec(v_x_1364_);
lean_dec_ref(v_elems_1365_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set_tag(v___x_1367_, 1);
lean_ctor_set(v___x_1367_, 0, v___x_1377_);
v___x_1379_ = v___x_1367_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
else
{
lean_object* v___x_1382_; 
lean_dec(v_x_1364_);
lean_dec(v_x_1363_);
v___x_1382_ = ((lean_object*)(l_Lean_Json_getArrVal_x3f___closed__1));
return v___x_1382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValD(lean_object* v_j_1383_, lean_object* v_k_1384_){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = l_Lean_Json_getObjVal_x3f(v_j_1383_, v_k_1384_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v___x_1386_; 
lean_dec_ref_known(v___x_1385_, 1);
v___x_1386_ = lean_box(0);
return v___x_1386_;
}
else
{
lean_object* v_a_1387_; 
v_a_1387_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_a_1387_);
lean_dec_ref_known(v___x_1385_, 1);
return v_a_1387_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValD___boxed(lean_object* v_j_1388_, lean_object* v_k_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Lean_Json_getObjValD(v_j_1388_, v_k_1389_);
lean_dec_ref(v_k_1389_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Json_setObjVal_x21_spec__1(lean_object* v_msg_1391_){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = lean_box(0);
v___x_1393_ = lean_panic_fn_borrowed(v___x_1392_, v_msg_1391_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(lean_object* v_msg_1394_){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = lean_box(1);
v___x_1396_ = lean_panic_fn_borrowed(v___x_1395_, v_msg_1394_);
return v___x_1396_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1400_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2));
v___x_1401_ = lean_unsigned_to_nat(35u);
v___x_1402_ = lean_unsigned_to_nat(182u);
v___x_1403_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1));
v___x_1404_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1405_ = l_mkPanicMessageWithDecl(v___x_1404_, v___x_1403_, v___x_1402_, v___x_1401_, v___x_1400_);
return v___x_1405_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1406_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2));
v___x_1407_ = lean_unsigned_to_nat(21u);
v___x_1408_ = lean_unsigned_to_nat(183u);
v___x_1409_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1));
v___x_1410_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1411_ = l_mkPanicMessageWithDecl(v___x_1410_, v___x_1409_, v___x_1408_, v___x_1407_, v___x_1406_);
return v___x_1411_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1414_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6));
v___x_1415_ = lean_unsigned_to_nat(35u);
v___x_1416_ = lean_unsigned_to_nat(276u);
v___x_1417_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5));
v___x_1418_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1419_ = l_mkPanicMessageWithDecl(v___x_1418_, v___x_1417_, v___x_1416_, v___x_1415_, v___x_1414_);
return v___x_1419_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1420_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6));
v___x_1421_ = lean_unsigned_to_nat(21u);
v___x_1422_ = lean_unsigned_to_nat(277u);
v___x_1423_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5));
v___x_1424_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1425_ = l_mkPanicMessageWithDecl(v___x_1424_, v___x_1423_, v___x_1422_, v___x_1421_, v___x_1420_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(lean_object* v_k_1426_, lean_object* v_v_1427_, lean_object* v_t_1428_){
_start:
{
if (lean_obj_tag(v_t_1428_) == 0)
{
lean_object* v_size_1429_; lean_object* v_k_1430_; lean_object* v_v_1431_; lean_object* v_l_1432_; lean_object* v_r_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1789_; 
v_size_1429_ = lean_ctor_get(v_t_1428_, 0);
v_k_1430_ = lean_ctor_get(v_t_1428_, 1);
v_v_1431_ = lean_ctor_get(v_t_1428_, 2);
v_l_1432_ = lean_ctor_get(v_t_1428_, 3);
v_r_1433_ = lean_ctor_get(v_t_1428_, 4);
v_isSharedCheck_1789_ = !lean_is_exclusive(v_t_1428_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1435_ = v_t_1428_;
v_isShared_1436_ = v_isSharedCheck_1789_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_r_1433_);
lean_inc(v_l_1432_);
lean_inc(v_v_1431_);
lean_inc(v_k_1430_);
lean_inc(v_size_1429_);
lean_dec(v_t_1428_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1789_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
uint8_t v___x_1437_; 
v___x_1437_ = lean_string_compare(v_k_1426_, v_k_1430_);
switch(v___x_1437_)
{
case 0:
{
lean_object* v___x_1438_; 
lean_dec(v_size_1429_);
v___x_1438_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1426_, v_v_1427_, v_l_1432_);
if (lean_obj_tag(v_r_1433_) == 0)
{
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_size_1439_; lean_object* v_size_1440_; lean_object* v_k_1441_; lean_object* v_v_1442_; lean_object* v_l_1443_; lean_object* v_r_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; uint8_t v___x_1447_; 
v_size_1439_ = lean_ctor_get(v_r_1433_, 0);
v_size_1440_ = lean_ctor_get(v___x_1438_, 0);
v_k_1441_ = lean_ctor_get(v___x_1438_, 1);
v_v_1442_ = lean_ctor_get(v___x_1438_, 2);
v_l_1443_ = lean_ctor_get(v___x_1438_, 3);
v_r_1444_ = lean_ctor_get(v___x_1438_, 4);
lean_inc(v_r_1444_);
v___x_1445_ = lean_unsigned_to_nat(3u);
v___x_1446_ = lean_nat_mul(v___x_1445_, v_size_1439_);
v___x_1447_ = lean_nat_dec_lt(v___x_1446_, v_size_1440_);
lean_dec(v___x_1446_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1452_; 
lean_dec(v_r_1444_);
v___x_1448_ = lean_unsigned_to_nat(1u);
v___x_1449_ = lean_nat_add(v___x_1448_, v_size_1440_);
v___x_1450_ = lean_nat_add(v___x_1449_, v_size_1439_);
lean_dec(v___x_1449_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 3, v___x_1438_);
lean_ctor_set(v___x_1435_, 0, v___x_1450_);
v___x_1452_ = v___x_1435_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1450_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_k_1430_);
lean_ctor_set(v_reuseFailAlloc_1453_, 2, v_v_1431_);
lean_ctor_set(v_reuseFailAlloc_1453_, 3, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1453_, 4, v_r_1433_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
else
{
lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1525_; 
lean_inc(v_l_1443_);
lean_inc(v_v_1442_);
lean_inc(v_k_1441_);
lean_inc(v_size_1440_);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1525_ == 0)
{
lean_object* v_unused_1526_; lean_object* v_unused_1527_; lean_object* v_unused_1528_; lean_object* v_unused_1529_; lean_object* v_unused_1530_; 
v_unused_1526_ = lean_ctor_get(v___x_1438_, 4);
lean_dec(v_unused_1526_);
v_unused_1527_ = lean_ctor_get(v___x_1438_, 3);
lean_dec(v_unused_1527_);
v_unused_1528_ = lean_ctor_get(v___x_1438_, 2);
lean_dec(v_unused_1528_);
v_unused_1529_ = lean_ctor_get(v___x_1438_, 1);
lean_dec(v_unused_1529_);
v_unused_1530_ = lean_ctor_get(v___x_1438_, 0);
lean_dec(v_unused_1530_);
v___x_1455_ = v___x_1438_;
v_isShared_1456_ = v_isSharedCheck_1525_;
goto v_resetjp_1454_;
}
else
{
lean_dec(v___x_1438_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1525_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
if (lean_obj_tag(v_l_1443_) == 0)
{
if (lean_obj_tag(v_r_1444_) == 0)
{
lean_object* v_size_1457_; lean_object* v_size_1458_; lean_object* v_k_1459_; lean_object* v_v_1460_; lean_object* v_l_1461_; lean_object* v_r_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; uint8_t v___x_1465_; 
v_size_1457_ = lean_ctor_get(v_l_1443_, 0);
v_size_1458_ = lean_ctor_get(v_r_1444_, 0);
v_k_1459_ = lean_ctor_get(v_r_1444_, 1);
v_v_1460_ = lean_ctor_get(v_r_1444_, 2);
v_l_1461_ = lean_ctor_get(v_r_1444_, 3);
v_r_1462_ = lean_ctor_get(v_r_1444_, 4);
v___x_1463_ = lean_unsigned_to_nat(2u);
v___x_1464_ = lean_nat_mul(v___x_1463_, v_size_1457_);
v___x_1465_ = lean_nat_dec_lt(v_size_1458_, v___x_1464_);
lean_dec(v___x_1464_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1495_; 
lean_inc(v_r_1462_);
lean_inc(v_l_1461_);
lean_inc(v_v_1460_);
lean_inc(v_k_1459_);
v_isSharedCheck_1495_ = !lean_is_exclusive(v_r_1444_);
if (v_isSharedCheck_1495_ == 0)
{
lean_object* v_unused_1496_; lean_object* v_unused_1497_; lean_object* v_unused_1498_; lean_object* v_unused_1499_; lean_object* v_unused_1500_; 
v_unused_1496_ = lean_ctor_get(v_r_1444_, 4);
lean_dec(v_unused_1496_);
v_unused_1497_ = lean_ctor_get(v_r_1444_, 3);
lean_dec(v_unused_1497_);
v_unused_1498_ = lean_ctor_get(v_r_1444_, 2);
lean_dec(v_unused_1498_);
v_unused_1499_ = lean_ctor_get(v_r_1444_, 1);
lean_dec(v_unused_1499_);
v_unused_1500_ = lean_ctor_get(v_r_1444_, 0);
lean_dec(v_unused_1500_);
v___x_1467_ = v_r_1444_;
v_isShared_1468_ = v_isSharedCheck_1495_;
goto v_resetjp_1466_;
}
else
{
lean_dec(v_r_1444_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1495_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___x_1483_; lean_object* v___y_1485_; 
v___x_1469_ = lean_unsigned_to_nat(1u);
v___x_1470_ = lean_nat_add(v___x_1469_, v_size_1440_);
lean_dec(v_size_1440_);
v___x_1471_ = lean_nat_add(v___x_1470_, v_size_1439_);
lean_dec(v___x_1470_);
v___x_1483_ = lean_nat_add(v___x_1469_, v_size_1457_);
if (lean_obj_tag(v_l_1461_) == 0)
{
lean_object* v_size_1493_; 
v_size_1493_ = lean_ctor_get(v_l_1461_, 0);
lean_inc(v_size_1493_);
v___y_1485_ = v_size_1493_;
goto v___jp_1484_;
}
else
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_unsigned_to_nat(0u);
v___y_1485_ = v___x_1494_;
goto v___jp_1484_;
}
v___jp_1472_:
{
lean_object* v___x_1476_; lean_object* v___x_1478_; 
v___x_1476_ = lean_nat_add(v___y_1474_, v___y_1475_);
lean_dec(v___y_1475_);
lean_dec(v___y_1474_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 4, v_r_1433_);
lean_ctor_set(v___x_1467_, 3, v_r_1462_);
lean_ctor_set(v___x_1467_, 2, v_v_1431_);
lean_ctor_set(v___x_1467_, 1, v_k_1430_);
lean_ctor_set(v___x_1467_, 0, v___x_1476_);
v___x_1478_ = v___x_1467_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1476_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v_k_1430_);
lean_ctor_set(v_reuseFailAlloc_1482_, 2, v_v_1431_);
lean_ctor_set(v_reuseFailAlloc_1482_, 3, v_r_1462_);
lean_ctor_set(v_reuseFailAlloc_1482_, 4, v_r_1433_);
v___x_1478_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
lean_object* v___x_1480_; 
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 4, v___x_1478_);
lean_ctor_set(v___x_1455_, 3, v___y_1473_);
lean_ctor_set(v___x_1455_, 2, v_v_1460_);
lean_ctor_set(v___x_1455_, 1, v_k_1459_);
lean_ctor_set(v___x_1455_, 0, v___x_1471_);
v___x_1480_ = v___x_1455_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1471_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_k_1459_);
lean_ctor_set(v_reuseFailAlloc_1481_, 2, v_v_1460_);
lean_ctor_set(v_reuseFailAlloc_1481_, 3, v___y_1473_);
lean_ctor_set(v_reuseFailAlloc_1481_, 4, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
v___jp_1484_:
{
lean_object* v___x_1486_; lean_object* v___x_1488_; 
v___x_1486_ = lean_nat_add(v___x_1483_, v___y_1485_);
lean_dec(v___y_1485_);
lean_dec(v___x_1483_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 4, v_l_1461_);
lean_ctor_set(v___x_1435_, 3, v_l_1443_);
lean_ctor_set(v___x_1435_, 2, v_v_1442_);
lean_ctor_set(v___x_1435_, 1, v_k_1441_);
lean_ctor_set(v___x_1435_, 0, v___x_1486_);
v___x_1488_ = v___x_1435_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v_k_1441_);
lean_ctor_set(v_reuseFailAlloc_1492_, 2, v_v_1442_);
lean_ctor_set(v_reuseFailAlloc_1492_, 3, v_l_1443_);
lean_ctor_set(v_reuseFailAlloc_1492_, 4, v_l_1461_);
v___x_1488_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_nat_add(v___x_1469_, v_size_1439_);
if (lean_obj_tag(v_r_1462_) == 0)
{
lean_object* v_size_1490_; 
v_size_1490_ = lean_ctor_get(v_r_1462_, 0);
lean_inc(v_size_1490_);
v___y_1473_ = v___x_1488_;
v___y_1474_ = v___x_1489_;
v___y_1475_ = v_size_1490_;
goto v___jp_1472_;
}
else
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_unsigned_to_nat(0u);
v___y_1473_ = v___x_1488_;
v___y_1474_ = v___x_1489_;
v___y_1475_ = v___x_1491_;
goto v___jp_1472_;
}
}
}
}
}
else
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1507_; 
lean_del_object(v___x_1435_);
v___x_1501_ = lean_unsigned_to_nat(1u);
v___x_1502_ = lean_nat_add(v___x_1501_, v_size_1440_);
lean_dec(v_size_1440_);
v___x_1503_ = lean_nat_add(v___x_1502_, v_size_1439_);
lean_dec(v___x_1502_);
v___x_1504_ = lean_nat_add(v___x_1501_, v_size_1439_);
v___x_1505_ = lean_nat_add(v___x_1504_, v_size_1458_);
lean_dec(v___x_1504_);
lean_inc_ref(v_r_1433_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 4, v_r_1433_);
lean_ctor_set(v___x_1455_, 3, v_r_1444_);
lean_ctor_set(v___x_1455_, 2, v_v_1431_);
lean_ctor_set(v___x_1455_, 1, v_k_1430_);
lean_ctor_set(v___x_1455_, 0, v___x_1505_);
v___x_1507_ = v___x_1455_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1520_, 1, v_k_1430_);
lean_ctor_set(v_reuseFailAlloc_1520_, 2, v_v_1431_);
lean_ctor_set(v_reuseFailAlloc_1520_, 3, v_r_1444_);
lean_ctor_set(v_reuseFailAlloc_1520_, 4, v_r_1433_);
v___x_1507_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1514_; 
v_isSharedCheck_1514_ = !lean_is_exclusive(v_r_1433_);
if (v_isSharedCheck_1514_ == 0)
{
lean_object* v_unused_1515_; lean_object* v_unused_1516_; lean_object* v_unused_1517_; lean_object* v_unused_1518_; lean_object* v_unused_1519_; 
v_unused_1515_ = lean_ctor_get(v_r_1433_, 4);
lean_dec(v_unused_1515_);
v_unused_1516_ = lean_ctor_get(v_r_1433_, 3);
lean_dec(v_unused_1516_);
v_unused_1517_ = lean_ctor_get(v_r_1433_, 2);
lean_dec(v_unused_1517_);
v_unused_1518_ = lean_ctor_get(v_r_1433_, 1);
lean_dec(v_unused_1518_);
v_unused_1519_ = lean_ctor_get(v_r_1433_, 0);
lean_dec(v_unused_1519_);
v___x_1509_ = v_r_1433_;
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
else
{
lean_dec(v_r_1433_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 4, v___x_1507_);
lean_ctor_set(v___x_1509_, 3, v_l_1443_);
lean_ctor_set(v___x_1509_, 2, v_v_1442_);
lean_ctor_set(v___x_1509_, 1, v_k_1441_);
lean_ctor_set(v___x_1509_, 0, v___x_1503_);
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1503_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v_k_1441_);
lean_ctor_set(v_reuseFailAlloc_1513_, 2, v_v_1442_);
lean_ctor_set(v_reuseFailAlloc_1513_, 3, v_l_1443_);
lean_ctor_set(v_reuseFailAlloc_1513_, 4, v___x_1507_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
}
else
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
lean_dec_ref_known(v_l_1443_, 5);
lean_del_object(v___x_1455_);
lean_dec(v_v_1442_);
lean_dec(v_k_1441_);
lean_dec(v_size_1440_);
lean_dec_ref_known(v_r_1433_, 5);
lean_del_object(v___x_1435_);
lean_dec(v_v_1431_);
lean_dec(v_k_1430_);
v___x_1521_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3);
v___x_1522_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1521_);
return v___x_1522_;
}
}
else
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
lean_del_object(v___x_1455_);
lean_dec(v_r_1444_);
lean_dec(v_v_1442_);
lean_dec(v_k_1441_);
lean_dec(v_size_1440_);
lean_dec_ref_known(v_r_1433_, 5);
lean_del_object(v___x_1435_);
lean_dec(v_v_1431_);
lean_dec(v_k_1430_);
v___x_1523_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4);
v___x_1524_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1523_);
return v___x_1524_;
}
}
}
}
else
{
lean_object* v_size_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1535_; 
v_size_1531_ = lean_ctor_get(v_r_1433_, 0);
v___x_1532_ = lean_unsigned_to_nat(1u);
v___x_1533_ = lean_nat_add(v___x_1532_, v_size_1531_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 3, v___x_1438_);
lean_ctor_set(v___x_1435_, 0, v___x_1533_);
v___x_1535_ = v___x_1435_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1533_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_k_1430_);
lean_ctor_set(v_reuseFailAlloc_1536_, 2, v_v_1431_);
lean_ctor_set(v_reuseFailAlloc_1536_, 3, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1536_, 4, v_r_1433_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
else
{
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_l_1537_; 
v_l_1537_ = lean_ctor_get(v___x_1438_, 3);
if (lean_obj_tag(v_l_1537_) == 0)
{
lean_object* v_r_1538_; 
lean_inc_ref(v_l_1537_);
v_r_1538_ = lean_ctor_get(v___x_1438_, 4);
lean_inc(v_r_1538_);
if (lean_obj_tag(v_r_1538_) == 0)
{
lean_object* v_size_1539_; lean_object* v_k_1540_; lean_object* v_v_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1555_; 
v_size_1539_ = lean_ctor_get(v___x_1438_, 0);
v_k_1540_ = lean_ctor_get(v___x_1438_, 1);
v_v_1541_ = lean_ctor_get(v___x_1438_, 2);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1555_ == 0)
{
lean_object* v_unused_1556_; lean_object* v_unused_1557_; 
v_unused_1556_ = lean_ctor_get(v___x_1438_, 4);
lean_dec(v_unused_1556_);
v_unused_1557_ = lean_ctor_get(v___x_1438_, 3);
lean_dec(v_unused_1557_);
v___x_1543_ = v___x_1438_;
v_isShared_1544_ = v_isSharedCheck_1555_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_v_1541_);
lean_inc(v_k_1540_);
lean_inc(v_size_1539_);
lean_dec(v___x_1438_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1555_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v_size_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1550_; 
v_size_1545_ = lean_ctor_get(v_r_1538_, 0);
v___x_1546_ = lean_unsigned_to_nat(1u);
v___x_1547_ = lean_nat_add(v___x_1546_, v_size_1539_);
lean_dec(v_size_1539_);
v___x_1548_ = lean_nat_add(v___x_1546_, v_size_1545_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 4, v_r_1433_);
lean_ctor_set(v___x_1543_, 3, v_r_1538_);
lean_ctor_set(v___x_1543_, 2, v_v_1431_);
lean_ctor_set(v___x_1543_, 1, v_k_1430_);
lean_ctor_set(v___x_1543_, 0, v___x_1548_);
v___x_1550_ = v___x_1543_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1548_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v_k_1430_);
lean_ctor_set(v_reuseFailAlloc_1554_, 2, v_v_1431_);
lean_ctor_set(v_reuseFailAlloc_1554_, 3, v_r_1538_);
lean_ctor_set(v_reuseFailAlloc_1554_, 4, v_r_1433_);
v___x_1550_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
lean_object* v___x_1552_; 
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 4, v___x_1550_);
lean_ctor_set(v___x_1435_, 3, v_l_1537_);
lean_ctor_set(v___x_1435_, 2, v_v_1541_);
lean_ctor_set(v___x_1435_, 1, v_k_1540_);
lean_ctor_set(v___x_1435_, 0, v___x_1547_);
v___x_1552_ = v___x_1435_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v_k_1540_);
lean_ctor_set(v_reuseFailAlloc_1553_, 2, v_v_1541_);
lean_ctor_set(v_reuseFailAlloc_1553_, 3, v_l_1537_);
lean_ctor_set(v_reuseFailAlloc_1553_, 4, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
else
{
lean_object* v_k_1558_; lean_object* v_v_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1571_; 
v_k_1558_ = lean_ctor_get(v___x_1438_, 1);
v_v_1559_ = lean_ctor_get(v___x_1438_, 2);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1571_ == 0)
{
lean_object* v_unused_1572_; lean_object* v_unused_1573_; lean_object* v_unused_1574_; 
v_unused_1572_ = lean_ctor_get(v___x_1438_, 4);
lean_dec(v_unused_1572_);
v_unused_1573_ = lean_ctor_get(v___x_1438_, 3);
lean_dec(v_unused_1573_);
v_unused_1574_ = lean_ctor_get(v___x_1438_, 0);
lean_dec(v_unused_1574_);
v___x_1561_ = v___x_1438_;
v_isShared_1562_ = v_isSharedCheck_1571_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_v_1559_);
lean_inc(v_k_1558_);
lean_dec(v___x_1438_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1571_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1566_; 
v___x_1563_ = lean_unsigned_to_nat(3u);
v___x_1564_ = lean_unsigned_to_nat(1u);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 3, v_r_1538_);
lean_ctor_set(v___x_1561_, 2, v_v_1431_);
lean_ctor_set(v___x_1561_, 1, v_k_1430_);
lean_ctor_set(v___x_1561_, 0, v___x_1564_);
v___x_1566_ = v___x_1561_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_k_1430_);
lean_ctor_set(v_reuseFailAlloc_1570_, 2, v_v_1431_);
lean_ctor_set(v_reuseFailAlloc_1570_, 3, v_r_1538_);
lean_ctor_set(v_reuseFailAlloc_1570_, 4, v_r_1538_);
v___x_1566_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
lean_object* v___x_1568_; 
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 4, v___x_1566_);
lean_ctor_set(v___x_1435_, 3, v_l_1537_);
lean_ctor_set(v___x_1435_, 2, v_v_1559_);
lean_ctor_set(v___x_1435_, 1, v_k_1558_);
lean_ctor_set(v___x_1435_, 0, v___x_1563_);
v___x_1568_ = v___x_1435_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v_k_1558_);
lean_ctor_set(v_reuseFailAlloc_1569_, 2, v_v_1559_);
lean_ctor_set(v_reuseFailAlloc_1569_, 3, v_l_1537_);
lean_ctor_set(v_reuseFailAlloc_1569_, 4, v___x_1566_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
}
else
{
lean_object* v_r_1575_; 
v_r_1575_ = lean_ctor_get(v___x_1438_, 4);
lean_inc(v_r_1575_);
if (lean_obj_tag(v_r_1575_) == 0)
{
lean_object* v_k_1576_; lean_object* v_v_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1601_; 
lean_inc(v_l_1537_);
v_k_1576_ = lean_ctor_get(v___x_1438_, 1);
v_v_1577_ = lean_ctor_get(v___x_1438_, 2);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1601_ == 0)
{
lean_object* v_unused_1602_; lean_object* v_unused_1603_; lean_object* v_unused_1604_; 
v_unused_1602_ = lean_ctor_get(v___x_1438_, 4);
lean_dec(v_unused_1602_);
v_unused_1603_ = lean_ctor_get(v___x_1438_, 3);
lean_dec(v_unused_1603_);
v_unused_1604_ = lean_ctor_get(v___x_1438_, 0);
lean_dec(v_unused_1604_);
v___x_1579_ = v___x_1438_;
v_isShared_1580_ = v_isSharedCheck_1601_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_v_1577_);
lean_inc(v_k_1576_);
lean_dec(v___x_1438_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1601_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v_k_1581_; lean_object* v_v_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1597_; 
v_k_1581_ = lean_ctor_get(v_r_1575_, 1);
v_v_1582_ = lean_ctor_get(v_r_1575_, 2);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_r_1575_);
if (v_isSharedCheck_1597_ == 0)
{
lean_object* v_unused_1598_; lean_object* v_unused_1599_; lean_object* v_unused_1600_; 
v_unused_1598_ = lean_ctor_get(v_r_1575_, 4);
lean_dec(v_unused_1598_);
v_unused_1599_ = lean_ctor_get(v_r_1575_, 3);
lean_dec(v_unused_1599_);
v_unused_1600_ = lean_ctor_get(v_r_1575_, 0);
lean_dec(v_unused_1600_);
v___x_1584_ = v_r_1575_;
v_isShared_1585_ = v_isSharedCheck_1597_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_v_1582_);
lean_inc(v_k_1581_);
lean_dec(v_r_1575_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1597_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1589_; 
v___x_1586_ = lean_unsigned_to_nat(3u);
v___x_1587_ = lean_unsigned_to_nat(1u);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 4, v_l_1537_);
lean_ctor_set(v___x_1584_, 3, v_l_1537_);
lean_ctor_set(v___x_1584_, 2, v_v_1577_);
lean_ctor_set(v___x_1584_, 1, v_k_1576_);
lean_ctor_set(v___x_1584_, 0, v___x_1587_);
v___x_1589_ = v___x_1584_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1587_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_k_1576_);
lean_ctor_set(v_reuseFailAlloc_1596_, 2, v_v_1577_);
lean_ctor_set(v_reuseFailAlloc_1596_, 3, v_l_1537_);
lean_ctor_set(v_reuseFailAlloc_1596_, 4, v_l_1537_);
v___x_1589_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
lean_object* v___x_1591_; 
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 4, v_l_1537_);
lean_ctor_set(v___x_1579_, 2, v_v_1431_);
lean_ctor_set(v___x_1579_, 1, v_k_1430_);
lean_ctor_set(v___x_1579_, 0, v___x_1587_);
v___x_1591_ = v___x_1579_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1587_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_k_1430_);
lean_ctor_set(v_reuseFailAlloc_1595_, 2, v_v_1431_);
lean_ctor_set(v_reuseFailAlloc_1595_, 3, v_l_1537_);
lean_ctor_set(v_reuseFailAlloc_1595_, 4, v_l_1537_);
v___x_1591_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_object* v___x_1593_; 
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 4, v___x_1591_);
lean_ctor_set(v___x_1435_, 3, v___x_1589_);
lean_ctor_set(v___x_1435_, 2, v_v_1582_);
lean_ctor_set(v___x_1435_, 1, v_k_1581_);
lean_ctor_set(v___x_1435_, 0, v___x_1586_);
v___x_1593_ = v___x_1435_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_k_1581_);
lean_ctor_set(v_reuseFailAlloc_1594_, 2, v_v_1582_);
lean_ctor_set(v_reuseFailAlloc_1594_, 3, v___x_1589_);
lean_ctor_set(v_reuseFailAlloc_1594_, 4, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
}
}
else
{
lean_object* v___x_1605_; lean_object* v___x_1607_; 
v___x_1605_ = lean_unsigned_to_nat(2u);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 4, v_r_1575_);
lean_ctor_set(v___x_1435_, 3, v___x_1438_);
lean_ctor_set(v___x_1435_, 0, v___x_1605_);
v___x_1607_ = v___x_1435_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1605_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_k_1430_);
lean_ctor_set(v_reuseFailAlloc_1608_, 2, v_v_1431_);
lean_ctor_set(v_reuseFailAlloc_1608_, 3, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1608_, 4, v_r_1575_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
else
{
lean_object* v___x_1609_; lean_object* v___x_1611_; 
v___x_1609_ = lean_unsigned_to_nat(1u);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 4, v___x_1438_);
lean_ctor_set(v___x_1435_, 3, v___x_1438_);
lean_ctor_set(v___x_1435_, 0, v___x_1609_);
v___x_1611_ = v___x_1435_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v_k_1430_);
lean_ctor_set(v_reuseFailAlloc_1612_, 2, v_v_1431_);
lean_ctor_set(v_reuseFailAlloc_1612_, 3, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1612_, 4, v___x_1438_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
case 1:
{
lean_object* v___x_1614_; 
lean_dec(v_v_1431_);
lean_dec(v_k_1430_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 2, v_v_1427_);
lean_ctor_set(v___x_1435_, 1, v_k_1426_);
v___x_1614_ = v___x_1435_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_size_1429_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_k_1426_);
lean_ctor_set(v_reuseFailAlloc_1615_, 2, v_v_1427_);
lean_ctor_set(v_reuseFailAlloc_1615_, 3, v_l_1432_);
lean_ctor_set(v_reuseFailAlloc_1615_, 4, v_r_1433_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
default: 
{
lean_object* v___x_1616_; 
lean_dec(v_size_1429_);
v___x_1616_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1426_, v_v_1427_, v_r_1433_);
if (lean_obj_tag(v_l_1432_) == 0)
{
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_size_1617_; lean_object* v_size_1618_; lean_object* v_k_1619_; lean_object* v_v_1620_; lean_object* v_l_1621_; lean_object* v_r_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; 
v_size_1617_ = lean_ctor_get(v_l_1432_, 0);
v_size_1618_ = lean_ctor_get(v___x_1616_, 0);
v_k_1619_ = lean_ctor_get(v___x_1616_, 1);
v_v_1620_ = lean_ctor_get(v___x_1616_, 2);
v_l_1621_ = lean_ctor_get(v___x_1616_, 3);
lean_inc(v_l_1621_);
v_r_1622_ = lean_ctor_get(v___x_1616_, 4);
v___x_1623_ = lean_unsigned_to_nat(3u);
v___x_1624_ = lean_nat_mul(v___x_1623_, v_size_1617_);
v___x_1625_ = lean_nat_dec_lt(v___x_1624_, v_size_1618_);
lean_dec(v___x_1624_);
if (v___x_1625_ == 0)
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1630_; 
lean_dec(v_l_1621_);
v___x_1626_ = lean_unsigned_to_nat(1u);
v___x_1627_ = lean_nat_add(v___x_1626_, v_size_1617_);
v___x_1628_ = lean_nat_add(v___x_1627_, v_size_1618_);
lean_dec(v___x_1627_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 4, v___x_1616_);
lean_ctor_set(v___x_1435_, 0, v___x_1628_);
v___x_1630_ = v___x_1435_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1628_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v_k_1430_);
lean_ctor_set(v_reuseFailAlloc_1631_, 2, v_v_1431_);
lean_ctor_set(v_reuseFailAlloc_1631_, 3, v_l_1432_);
lean_ctor_set(v_reuseFailAlloc_1631_, 4, v___x_1616_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
else
{
lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1701_; 
lean_inc(v_r_1622_);
lean_inc(v_v_1620_);
lean_inc(v_k_1619_);
lean_inc(v_size_1618_);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1701_ == 0)
{
lean_object* v_unused_1702_; lean_object* v_unused_1703_; lean_object* v_unused_1704_; lean_object* v_unused_1705_; lean_object* v_unused_1706_; 
v_unused_1702_ = lean_ctor_get(v___x_1616_, 4);
lean_dec(v_unused_1702_);
v_unused_1703_ = lean_ctor_get(v___x_1616_, 3);
lean_dec(v_unused_1703_);
v_unused_1704_ = lean_ctor_get(v___x_1616_, 2);
lean_dec(v_unused_1704_);
v_unused_1705_ = lean_ctor_get(v___x_1616_, 1);
lean_dec(v_unused_1705_);
v_unused_1706_ = lean_ctor_get(v___x_1616_, 0);
lean_dec(v_unused_1706_);
v___x_1633_ = v___x_1616_;
v_isShared_1634_ = v_isSharedCheck_1701_;
goto v_resetjp_1632_;
}
else
{
lean_dec(v___x_1616_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1701_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
if (lean_obj_tag(v_l_1621_) == 0)
{
if (lean_obj_tag(v_r_1622_) == 0)
{
lean_object* v_size_1635_; lean_object* v_k_1636_; lean_object* v_v_1637_; lean_object* v_l_1638_; lean_object* v_r_1639_; lean_object* v_size_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; uint8_t v___x_1643_; 
v_size_1635_ = lean_ctor_get(v_l_1621_, 0);
v_k_1636_ = lean_ctor_get(v_l_1621_, 1);
v_v_1637_ = lean_ctor_get(v_l_1621_, 2);
v_l_1638_ = lean_ctor_get(v_l_1621_, 3);
v_r_1639_ = lean_ctor_get(v_l_1621_, 4);
v_size_1640_ = lean_ctor_get(v_r_1622_, 0);
v___x_1641_ = lean_unsigned_to_nat(2u);
v___x_1642_ = lean_nat_mul(v___x_1641_, v_size_1640_);
v___x_1643_ = lean_nat_dec_lt(v_size_1635_, v___x_1642_);
lean_dec(v___x_1642_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1672_; 
lean_inc(v_r_1639_);
lean_inc(v_l_1638_);
lean_inc(v_v_1637_);
lean_inc(v_k_1636_);
v_isSharedCheck_1672_ = !lean_is_exclusive(v_l_1621_);
if (v_isSharedCheck_1672_ == 0)
{
lean_object* v_unused_1673_; lean_object* v_unused_1674_; lean_object* v_unused_1675_; lean_object* v_unused_1676_; lean_object* v_unused_1677_; 
v_unused_1673_ = lean_ctor_get(v_l_1621_, 4);
lean_dec(v_unused_1673_);
v_unused_1674_ = lean_ctor_get(v_l_1621_, 3);
lean_dec(v_unused_1674_);
v_unused_1675_ = lean_ctor_get(v_l_1621_, 2);
lean_dec(v_unused_1675_);
v_unused_1676_ = lean_ctor_get(v_l_1621_, 1);
lean_dec(v_unused_1676_);
v_unused_1677_ = lean_ctor_get(v_l_1621_, 0);
lean_dec(v_unused_1677_);
v___x_1645_ = v_l_1621_;
v_isShared_1646_ = v_isSharedCheck_1672_;
goto v_resetjp_1644_;
}
else
{
lean_dec(v_l_1621_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1672_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1662_; 
v___x_1647_ = lean_unsigned_to_nat(1u);
v___x_1648_ = lean_nat_add(v___x_1647_, v_size_1617_);
v___x_1649_ = lean_nat_add(v___x_1648_, v_size_1618_);
lean_dec(v_size_1618_);
if (lean_obj_tag(v_l_1638_) == 0)
{
lean_object* v_size_1670_; 
v_size_1670_ = lean_ctor_get(v_l_1638_, 0);
lean_inc(v_size_1670_);
v___y_1662_ = v_size_1670_;
goto v___jp_1661_;
}
else
{
lean_object* v___x_1671_; 
v___x_1671_ = lean_unsigned_to_nat(0u);
v___y_1662_ = v___x_1671_;
goto v___jp_1661_;
}
v___jp_1650_:
{
lean_object* v___x_1654_; lean_object* v___x_1656_; 
v___x_1654_ = lean_nat_add(v___y_1651_, v___y_1653_);
lean_dec(v___y_1653_);
lean_dec(v___y_1651_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 4, v_r_1622_);
lean_ctor_set(v___x_1645_, 3, v_r_1639_);
lean_ctor_set(v___x_1645_, 2, v_v_1620_);
lean_ctor_set(v___x_1645_, 1, v_k_1619_);
lean_ctor_set(v___x_1645_, 0, v___x_1654_);
v___x_1656_ = v___x_1645_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1654_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_k_1619_);
lean_ctor_set(v_reuseFailAlloc_1660_, 2, v_v_1620_);
lean_ctor_set(v_reuseFailAlloc_1660_, 3, v_r_1639_);
lean_ctor_set(v_reuseFailAlloc_1660_, 4, v_r_1622_);
v___x_1656_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
lean_object* v___x_1658_; 
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 4, v___x_1656_);
lean_ctor_set(v___x_1633_, 3, v___y_1652_);
lean_ctor_set(v___x_1633_, 2, v_v_1637_);
lean_ctor_set(v___x_1633_, 1, v_k_1636_);
lean_ctor_set(v___x_1633_, 0, v___x_1649_);
v___x_1658_ = v___x_1633_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1649_);
lean_ctor_set(v_reuseFailAlloc_1659_, 1, v_k_1636_);
lean_ctor_set(v_reuseFailAlloc_1659_, 2, v_v_1637_);
lean_ctor_set(v_reuseFailAlloc_1659_, 3, v___y_1652_);
lean_ctor_set(v_reuseFailAlloc_1659_, 4, v___x_1656_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
v___jp_1661_:
{
lean_object* v___x_1663_; lean_object* v___x_1665_; 
v___x_1663_ = lean_nat_add(v___x_1648_, v___y_1662_);
lean_dec(v___y_1662_);
lean_dec(v___x_1648_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 4, v_l_1638_);
lean_ctor_set(v___x_1435_, 0, v___x_1663_);
v___x_1665_ = v___x_1435_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1663_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_k_1430_);
lean_ctor_set(v_reuseFailAlloc_1669_, 2, v_v_1431_);
lean_ctor_set(v_reuseFailAlloc_1669_, 3, v_l_1432_);
lean_ctor_set(v_reuseFailAlloc_1669_, 4, v_l_1638_);
v___x_1665_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
lean_object* v___x_1666_; 
v___x_1666_ = lean_nat_add(v___x_1647_, v_size_1640_);
if (lean_obj_tag(v_r_1639_) == 0)
{
lean_object* v_size_1667_; 
v_size_1667_ = lean_ctor_get(v_r_1639_, 0);
lean_inc(v_size_1667_);
v___y_1651_ = v___x_1666_;
v___y_1652_ = v___x_1665_;
v___y_1653_ = v_size_1667_;
goto v___jp_1650_;
}
else
{
lean_object* v___x_1668_; 
v___x_1668_ = lean_unsigned_to_nat(0u);
v___y_1651_ = v___x_1666_;
v___y_1652_ = v___x_1665_;
v___y_1653_ = v___x_1668_;
goto v___jp_1650_;
}
}
}
}
}
else
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1683_; 
lean_del_object(v___x_1435_);
v___x_1678_ = lean_unsigned_to_nat(1u);
v___x_1679_ = lean_nat_add(v___x_1678_, v_size_1617_);
v___x_1680_ = lean_nat_add(v___x_1679_, v_size_1618_);
lean_dec(v_size_1618_);
v___x_1681_ = lean_nat_add(v___x_1679_, v_size_1635_);
lean_dec(v___x_1679_);
lean_inc_ref(v_l_1432_);
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 4, v_l_1621_);
lean_ctor_set(v___x_1633_, 3, v_l_1432_);
lean_ctor_set(v___x_1633_, 2, v_v_1431_);
lean_ctor_set(v___x_1633_, 1, v_k_1430_);
lean_ctor_set(v___x_1633_, 0, v___x_1681_);
v___x_1683_ = v___x_1633_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1681_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_k_1430_);
lean_ctor_set(v_reuseFailAlloc_1696_, 2, v_v_1431_);
lean_ctor_set(v_reuseFailAlloc_1696_, 3, v_l_1432_);
lean_ctor_set(v_reuseFailAlloc_1696_, 4, v_l_1621_);
v___x_1683_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
v_isSharedCheck_1690_ = !lean_is_exclusive(v_l_1432_);
if (v_isSharedCheck_1690_ == 0)
{
lean_object* v_unused_1691_; lean_object* v_unused_1692_; lean_object* v_unused_1693_; lean_object* v_unused_1694_; lean_object* v_unused_1695_; 
v_unused_1691_ = lean_ctor_get(v_l_1432_, 4);
lean_dec(v_unused_1691_);
v_unused_1692_ = lean_ctor_get(v_l_1432_, 3);
lean_dec(v_unused_1692_);
v_unused_1693_ = lean_ctor_get(v_l_1432_, 2);
lean_dec(v_unused_1693_);
v_unused_1694_ = lean_ctor_get(v_l_1432_, 1);
lean_dec(v_unused_1694_);
v_unused_1695_ = lean_ctor_get(v_l_1432_, 0);
lean_dec(v_unused_1695_);
v___x_1685_ = v_l_1432_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_dec(v_l_1432_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 4, v_r_1622_);
lean_ctor_set(v___x_1685_, 3, v___x_1683_);
lean_ctor_set(v___x_1685_, 2, v_v_1620_);
lean_ctor_set(v___x_1685_, 1, v_k_1619_);
lean_ctor_set(v___x_1685_, 0, v___x_1680_);
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1680_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v_k_1619_);
lean_ctor_set(v_reuseFailAlloc_1689_, 2, v_v_1620_);
lean_ctor_set(v_reuseFailAlloc_1689_, 3, v___x_1683_);
lean_ctor_set(v_reuseFailAlloc_1689_, 4, v_r_1622_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
}
else
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
lean_dec_ref_known(v_l_1621_, 5);
lean_del_object(v___x_1633_);
lean_dec(v_v_1620_);
lean_dec(v_k_1619_);
lean_dec(v_size_1618_);
lean_dec_ref_known(v_l_1432_, 5);
lean_del_object(v___x_1435_);
lean_dec(v_v_1431_);
lean_dec(v_k_1430_);
v___x_1697_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7);
v___x_1698_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1697_);
return v___x_1698_;
}
}
else
{
lean_object* v___x_1699_; lean_object* v___x_1700_; 
lean_del_object(v___x_1633_);
lean_dec(v_r_1622_);
lean_dec(v_v_1620_);
lean_dec(v_k_1619_);
lean_dec(v_size_1618_);
lean_dec_ref_known(v_l_1432_, 5);
lean_del_object(v___x_1435_);
lean_dec(v_v_1431_);
lean_dec(v_k_1430_);
v___x_1699_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8);
v___x_1700_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1699_);
return v___x_1700_;
}
}
}
}
else
{
lean_object* v_size_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1711_; 
v_size_1707_ = lean_ctor_get(v_l_1432_, 0);
v___x_1708_ = lean_unsigned_to_nat(1u);
v___x_1709_ = lean_nat_add(v___x_1708_, v_size_1707_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 4, v___x_1616_);
lean_ctor_set(v___x_1435_, 0, v___x_1709_);
v___x_1711_ = v___x_1435_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1709_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v_k_1430_);
lean_ctor_set(v_reuseFailAlloc_1712_, 2, v_v_1431_);
lean_ctor_set(v_reuseFailAlloc_1712_, 3, v_l_1432_);
lean_ctor_set(v_reuseFailAlloc_1712_, 4, v___x_1616_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
else
{
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_l_1713_; 
v_l_1713_ = lean_ctor_get(v___x_1616_, 3);
lean_inc(v_l_1713_);
if (lean_obj_tag(v_l_1713_) == 0)
{
lean_object* v_r_1714_; 
v_r_1714_ = lean_ctor_get(v___x_1616_, 4);
lean_inc(v_r_1714_);
if (lean_obj_tag(v_r_1714_) == 0)
{
lean_object* v_size_1715_; lean_object* v_k_1716_; lean_object* v_v_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1731_; 
v_size_1715_ = lean_ctor_get(v___x_1616_, 0);
v_k_1716_ = lean_ctor_get(v___x_1616_, 1);
v_v_1717_ = lean_ctor_get(v___x_1616_, 2);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1731_ == 0)
{
lean_object* v_unused_1732_; lean_object* v_unused_1733_; 
v_unused_1732_ = lean_ctor_get(v___x_1616_, 4);
lean_dec(v_unused_1732_);
v_unused_1733_ = lean_ctor_get(v___x_1616_, 3);
lean_dec(v_unused_1733_);
v___x_1719_ = v___x_1616_;
v_isShared_1720_ = v_isSharedCheck_1731_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_v_1717_);
lean_inc(v_k_1716_);
lean_inc(v_size_1715_);
lean_dec(v___x_1616_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1731_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v_size_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1726_; 
v_size_1721_ = lean_ctor_get(v_l_1713_, 0);
v___x_1722_ = lean_unsigned_to_nat(1u);
v___x_1723_ = lean_nat_add(v___x_1722_, v_size_1715_);
lean_dec(v_size_1715_);
v___x_1724_ = lean_nat_add(v___x_1722_, v_size_1721_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 4, v_l_1713_);
lean_ctor_set(v___x_1719_, 3, v_l_1432_);
lean_ctor_set(v___x_1719_, 2, v_v_1431_);
lean_ctor_set(v___x_1719_, 1, v_k_1430_);
lean_ctor_set(v___x_1719_, 0, v___x_1724_);
v___x_1726_ = v___x_1719_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1724_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_k_1430_);
lean_ctor_set(v_reuseFailAlloc_1730_, 2, v_v_1431_);
lean_ctor_set(v_reuseFailAlloc_1730_, 3, v_l_1432_);
lean_ctor_set(v_reuseFailAlloc_1730_, 4, v_l_1713_);
v___x_1726_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
lean_object* v___x_1728_; 
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 4, v_r_1714_);
lean_ctor_set(v___x_1435_, 3, v___x_1726_);
lean_ctor_set(v___x_1435_, 2, v_v_1717_);
lean_ctor_set(v___x_1435_, 1, v_k_1716_);
lean_ctor_set(v___x_1435_, 0, v___x_1723_);
v___x_1728_ = v___x_1435_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1723_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_k_1716_);
lean_ctor_set(v_reuseFailAlloc_1729_, 2, v_v_1717_);
lean_ctor_set(v_reuseFailAlloc_1729_, 3, v___x_1726_);
lean_ctor_set(v_reuseFailAlloc_1729_, 4, v_r_1714_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
else
{
lean_object* v_k_1734_; lean_object* v_v_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1759_; 
v_k_1734_ = lean_ctor_get(v___x_1616_, 1);
v_v_1735_ = lean_ctor_get(v___x_1616_, 2);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1759_ == 0)
{
lean_object* v_unused_1760_; lean_object* v_unused_1761_; lean_object* v_unused_1762_; 
v_unused_1760_ = lean_ctor_get(v___x_1616_, 4);
lean_dec(v_unused_1760_);
v_unused_1761_ = lean_ctor_get(v___x_1616_, 3);
lean_dec(v_unused_1761_);
v_unused_1762_ = lean_ctor_get(v___x_1616_, 0);
lean_dec(v_unused_1762_);
v___x_1737_ = v___x_1616_;
v_isShared_1738_ = v_isSharedCheck_1759_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_v_1735_);
lean_inc(v_k_1734_);
lean_dec(v___x_1616_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1759_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v_k_1739_; lean_object* v_v_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1755_; 
v_k_1739_ = lean_ctor_get(v_l_1713_, 1);
v_v_1740_ = lean_ctor_get(v_l_1713_, 2);
v_isSharedCheck_1755_ = !lean_is_exclusive(v_l_1713_);
if (v_isSharedCheck_1755_ == 0)
{
lean_object* v_unused_1756_; lean_object* v_unused_1757_; lean_object* v_unused_1758_; 
v_unused_1756_ = lean_ctor_get(v_l_1713_, 4);
lean_dec(v_unused_1756_);
v_unused_1757_ = lean_ctor_get(v_l_1713_, 3);
lean_dec(v_unused_1757_);
v_unused_1758_ = lean_ctor_get(v_l_1713_, 0);
lean_dec(v_unused_1758_);
v___x_1742_ = v_l_1713_;
v_isShared_1743_ = v_isSharedCheck_1755_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_v_1740_);
lean_inc(v_k_1739_);
lean_dec(v_l_1713_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1755_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1747_; 
v___x_1744_ = lean_unsigned_to_nat(3u);
v___x_1745_ = lean_unsigned_to_nat(1u);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 4, v_r_1714_);
lean_ctor_set(v___x_1742_, 3, v_r_1714_);
lean_ctor_set(v___x_1742_, 2, v_v_1431_);
lean_ctor_set(v___x_1742_, 1, v_k_1430_);
lean_ctor_set(v___x_1742_, 0, v___x_1745_);
v___x_1747_ = v___x_1742_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v___x_1745_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v_k_1430_);
lean_ctor_set(v_reuseFailAlloc_1754_, 2, v_v_1431_);
lean_ctor_set(v_reuseFailAlloc_1754_, 3, v_r_1714_);
lean_ctor_set(v_reuseFailAlloc_1754_, 4, v_r_1714_);
v___x_1747_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
lean_object* v___x_1749_; 
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 3, v_r_1714_);
lean_ctor_set(v___x_1737_, 0, v___x_1745_);
v___x_1749_ = v___x_1737_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1745_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v_k_1734_);
lean_ctor_set(v_reuseFailAlloc_1753_, 2, v_v_1735_);
lean_ctor_set(v_reuseFailAlloc_1753_, 3, v_r_1714_);
lean_ctor_set(v_reuseFailAlloc_1753_, 4, v_r_1714_);
v___x_1749_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
lean_object* v___x_1751_; 
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 4, v___x_1749_);
lean_ctor_set(v___x_1435_, 3, v___x_1747_);
lean_ctor_set(v___x_1435_, 2, v_v_1740_);
lean_ctor_set(v___x_1435_, 1, v_k_1739_);
lean_ctor_set(v___x_1435_, 0, v___x_1744_);
v___x_1751_ = v___x_1435_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1744_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_k_1739_);
lean_ctor_set(v_reuseFailAlloc_1752_, 2, v_v_1740_);
lean_ctor_set(v_reuseFailAlloc_1752_, 3, v___x_1747_);
lean_ctor_set(v_reuseFailAlloc_1752_, 4, v___x_1749_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1763_; 
v_r_1763_ = lean_ctor_get(v___x_1616_, 4);
lean_inc(v_r_1763_);
if (lean_obj_tag(v_r_1763_) == 0)
{
lean_object* v_k_1764_; lean_object* v_v_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1777_; 
v_k_1764_ = lean_ctor_get(v___x_1616_, 1);
v_v_1765_ = lean_ctor_get(v___x_1616_, 2);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1777_ == 0)
{
lean_object* v_unused_1778_; lean_object* v_unused_1779_; lean_object* v_unused_1780_; 
v_unused_1778_ = lean_ctor_get(v___x_1616_, 4);
lean_dec(v_unused_1778_);
v_unused_1779_ = lean_ctor_get(v___x_1616_, 3);
lean_dec(v_unused_1779_);
v_unused_1780_ = lean_ctor_get(v___x_1616_, 0);
lean_dec(v_unused_1780_);
v___x_1767_ = v___x_1616_;
v_isShared_1768_ = v_isSharedCheck_1777_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_v_1765_);
lean_inc(v_k_1764_);
lean_dec(v___x_1616_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1777_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1772_; 
v___x_1769_ = lean_unsigned_to_nat(3u);
v___x_1770_ = lean_unsigned_to_nat(1u);
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 4, v_l_1713_);
lean_ctor_set(v___x_1767_, 2, v_v_1431_);
lean_ctor_set(v___x_1767_, 1, v_k_1430_);
lean_ctor_set(v___x_1767_, 0, v___x_1770_);
v___x_1772_ = v___x_1767_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1770_);
lean_ctor_set(v_reuseFailAlloc_1776_, 1, v_k_1430_);
lean_ctor_set(v_reuseFailAlloc_1776_, 2, v_v_1431_);
lean_ctor_set(v_reuseFailAlloc_1776_, 3, v_l_1713_);
lean_ctor_set(v_reuseFailAlloc_1776_, 4, v_l_1713_);
v___x_1772_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1774_; 
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 4, v_r_1763_);
lean_ctor_set(v___x_1435_, 3, v___x_1772_);
lean_ctor_set(v___x_1435_, 2, v_v_1765_);
lean_ctor_set(v___x_1435_, 1, v_k_1764_);
lean_ctor_set(v___x_1435_, 0, v___x_1769_);
v___x_1774_ = v___x_1435_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1769_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v_k_1764_);
lean_ctor_set(v_reuseFailAlloc_1775_, 2, v_v_1765_);
lean_ctor_set(v_reuseFailAlloc_1775_, 3, v___x_1772_);
lean_ctor_set(v_reuseFailAlloc_1775_, 4, v_r_1763_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
else
{
lean_object* v___x_1781_; lean_object* v___x_1783_; 
v___x_1781_ = lean_unsigned_to_nat(2u);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 4, v___x_1616_);
lean_ctor_set(v___x_1435_, 3, v_r_1763_);
lean_ctor_set(v___x_1435_, 0, v___x_1781_);
v___x_1783_ = v___x_1435_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1781_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_k_1430_);
lean_ctor_set(v_reuseFailAlloc_1784_, 2, v_v_1431_);
lean_ctor_set(v_reuseFailAlloc_1784_, 3, v_r_1763_);
lean_ctor_set(v_reuseFailAlloc_1784_, 4, v___x_1616_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
else
{
lean_object* v___x_1785_; lean_object* v___x_1787_; 
v___x_1785_ = lean_unsigned_to_nat(1u);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 4, v___x_1616_);
lean_ctor_set(v___x_1435_, 3, v___x_1616_);
lean_ctor_set(v___x_1435_, 0, v___x_1785_);
v___x_1787_ = v___x_1435_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1785_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v_k_1430_);
lean_ctor_set(v_reuseFailAlloc_1788_, 2, v_v_1431_);
lean_ctor_set(v_reuseFailAlloc_1788_, 3, v___x_1616_);
lean_ctor_set(v_reuseFailAlloc_1788_, 4, v___x_1616_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = lean_unsigned_to_nat(1u);
v___x_1791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1790_);
lean_ctor_set(v___x_1791_, 1, v_k_1426_);
lean_ctor_set(v___x_1791_, 2, v_v_1427_);
lean_ctor_set(v___x_1791_, 3, v_t_1428_);
lean_ctor_set(v___x_1791_, 4, v_t_1428_);
return v___x_1791_;
}
}
}
static lean_object* _init_l_Lean_Json_setObjVal_x21___closed__2(void){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1794_ = ((lean_object*)(l_Lean_Json_setObjVal_x21___closed__1));
v___x_1795_ = lean_unsigned_to_nat(21u);
v___x_1796_ = lean_unsigned_to_nat(285u);
v___x_1797_ = ((lean_object*)(l_Lean_Json_setObjVal_x21___closed__0));
v___x_1798_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0));
v___x_1799_ = l_mkPanicMessageWithDecl(v___x_1798_, v___x_1797_, v___x_1796_, v___x_1795_, v___x_1794_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_setObjVal_x21(lean_object* v_x_1800_, lean_object* v_x_1801_, lean_object* v_x_1802_){
_start:
{
if (lean_obj_tag(v_x_1800_) == 5)
{
lean_object* v_kvPairs_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1811_; 
v_kvPairs_1803_ = lean_ctor_get(v_x_1800_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v_x_1800_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1805_ = v_x_1800_;
v_isShared_1806_ = v_isSharedCheck_1811_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_kvPairs_1803_);
lean_dec(v_x_1800_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1811_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1807_; lean_object* v___x_1809_; 
v___x_1807_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_x_1801_, v_x_1802_, v_kvPairs_1803_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v___x_1807_);
v___x_1809_ = v___x_1805_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1807_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
else
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
lean_dec(v_x_1802_);
lean_dec_ref(v_x_1801_);
lean_dec(v_x_1800_);
v___x_1812_ = lean_obj_once(&l_Lean_Json_setObjVal_x21___closed__2, &l_Lean_Json_setObjVal_x21___closed__2_once, _init_l_Lean_Json_setObjVal_x21___closed__2);
v___x_1813_ = l_panic___at___00Lean_Json_setObjVal_x21_spec__1(v___x_1812_);
return v___x_1813_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0(lean_object* v_00_u03b2_1814_, lean_object* v_msg_1815_){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v_msg_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0(lean_object* v_00_u03b2_1817_, lean_object* v_k_1818_, lean_object* v_v_1819_, lean_object* v_t_1820_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1818_, v_v_1819_, v_t_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(lean_object* v_init_1822_, lean_object* v_x_1823_){
_start:
{
if (lean_obj_tag(v_x_1823_) == 0)
{
lean_object* v_k_1824_; lean_object* v_v_1825_; lean_object* v_l_1826_; lean_object* v_r_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v_k_1824_ = lean_ctor_get(v_x_1823_, 1);
lean_inc(v_k_1824_);
v_v_1825_ = lean_ctor_get(v_x_1823_, 2);
lean_inc(v_v_1825_);
v_l_1826_ = lean_ctor_get(v_x_1823_, 3);
lean_inc(v_l_1826_);
v_r_1827_ = lean_ctor_get(v_x_1823_, 4);
lean_inc(v_r_1827_);
lean_dec_ref_known(v_x_1823_, 5);
v___x_1828_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_init_1822_, v_l_1826_);
v___x_1829_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1824_, v_v_1825_, v___x_1828_);
v_init_1822_ = v___x_1829_;
v_x_1823_ = v_r_1827_;
goto _start;
}
else
{
return v_init_1822_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mergeObj(lean_object* v_x_1831_, lean_object* v_x_1832_){
_start:
{
if (lean_obj_tag(v_x_1831_) == 5)
{
if (lean_obj_tag(v_x_1832_) == 5)
{
lean_object* v_kvPairs_1833_; lean_object* v_kvPairs_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1842_; 
v_kvPairs_1833_ = lean_ctor_get(v_x_1831_, 0);
lean_inc(v_kvPairs_1833_);
lean_dec_ref_known(v_x_1831_, 1);
v_kvPairs_1834_ = lean_ctor_get(v_x_1832_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v_x_1832_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1836_ = v_x_1832_;
v_isShared_1837_ = v_isSharedCheck_1842_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_kvPairs_1834_);
lean_dec(v_x_1832_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1842_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1838_; lean_object* v___x_1840_; 
v___x_1838_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_kvPairs_1833_, v_kvPairs_1834_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1838_);
v___x_1840_ = v___x_1836_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
else
{
lean_dec_ref_known(v_x_1831_, 1);
return v_x_1832_;
}
}
else
{
lean_dec(v_x_1831_);
return v_x_1832_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0(lean_object* v_init_1843_, lean_object* v_t_1844_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_init_1843_, v_t_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorIdx(lean_object* v_x_1846_){
_start:
{
if (lean_obj_tag(v_x_1846_) == 0)
{
lean_object* v___x_1847_; 
v___x_1847_ = lean_unsigned_to_nat(0u);
return v___x_1847_;
}
else
{
lean_object* v___x_1848_; 
v___x_1848_ = lean_unsigned_to_nat(1u);
return v___x_1848_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorIdx___boxed(lean_object* v_x_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_Lean_Json_Structured_ctorIdx(v_x_1849_);
lean_dec_ref(v_x_1849_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim___redArg(lean_object* v_t_1851_, lean_object* v_k_1852_){
_start:
{
if (lean_obj_tag(v_t_1851_) == 0)
{
lean_object* v_elems_1853_; lean_object* v___x_1854_; 
v_elems_1853_ = lean_ctor_get(v_t_1851_, 0);
lean_inc_ref(v_elems_1853_);
lean_dec_ref_known(v_t_1851_, 1);
v___x_1854_ = lean_apply_1(v_k_1852_, v_elems_1853_);
return v___x_1854_;
}
else
{
lean_object* v_kvPairs_1855_; lean_object* v___x_1856_; 
v_kvPairs_1855_ = lean_ctor_get(v_t_1851_, 0);
lean_inc(v_kvPairs_1855_);
lean_dec_ref_known(v_t_1851_, 1);
v___x_1856_ = lean_apply_1(v_k_1852_, v_kvPairs_1855_);
return v___x_1856_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim(lean_object* v_motive_1857_, lean_object* v_ctorIdx_1858_, lean_object* v_t_1859_, lean_object* v_h_1860_, lean_object* v_k_1861_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1859_, v_k_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim___boxed(lean_object* v_motive_1863_, lean_object* v_ctorIdx_1864_, lean_object* v_t_1865_, lean_object* v_h_1866_, lean_object* v_k_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_Json_Structured_ctorElim(v_motive_1863_, v_ctorIdx_1864_, v_t_1865_, v_h_1866_, v_k_1867_);
lean_dec(v_ctorIdx_1864_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_arr_elim___redArg(lean_object* v_t_1869_, lean_object* v_arr_1870_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1869_, v_arr_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_arr_elim(lean_object* v_motive_1872_, lean_object* v_t_1873_, lean_object* v_h_1874_, lean_object* v_arr_1875_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1873_, v_arr_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_obj_elim___redArg(lean_object* v_t_1877_, lean_object* v_obj_1878_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1877_, v_obj_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_obj_elim(lean_object* v_motive_1880_, lean_object* v_t_1881_, lean_object* v_h_1882_, lean_object* v_obj_1883_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1881_, v_obj_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeArrayStructured___lam__0(lean_object* v_elems_1885_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1886_, 0, v_elems_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeRawStringStructured___lam__0(lean_object* v_kvPairs_1889_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1890_, 0, v_kvPairs_1889_);
return v___x_1890_;
}
}
lean_object* runtime_initialize_Init_Data_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_OfScientific(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_TreeMap_Raw_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_String(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Substring(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Json_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_OfScientific(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeMap_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Substring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_JsonNumber_ltProp = _init_l_Lean_JsonNumber_ltProp();
lean_mark_persistent(l_Lean_JsonNumber_ltProp);
l_Lean_JsonNumber_instInhabited = _init_l_Lean_JsonNumber_instInhabited();
lean_mark_persistent(l_Lean_JsonNumber_instInhabited);
l_Lean_instInhabitedJson_default = _init_l_Lean_instInhabitedJson_default();
lean_mark_persistent(l_Lean_instInhabitedJson_default);
l_Lean_instInhabitedJson = _init_l_Lean_instInhabitedJson();
lean_mark_persistent(l_Lean_instInhabitedJson);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Json_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Range(uint8_t builtin);
lean_object* initialize_Init_Data_OfScientific(uint8_t builtin);
lean_object* initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* initialize_Std_Data_TreeMap_Raw_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_String(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
lean_object* initialize_Init_Data_String_Substring(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Json_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_OfScientific(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeMap_Raw_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Substring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Json_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Json_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Json_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
