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
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_bool_not(uint8_t);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__0;
static lean_once_cell_t l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__1;
static lean_once_cell_t l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2;
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
lean_object* v___y_146_; uint8_t v___y_147_; lean_object* v___y_148_; lean_object* v_fst_149_; lean_object* v_snd_150_; lean_object* v_fst_154_; lean_object* v_snd_155_; lean_object* v___x_172_; lean_object* v_fst_173_; lean_object* v_snd_174_; lean_object* v___x_175_; lean_object* v_fst_176_; lean_object* v_snd_177_; uint8_t v___y_179_; lean_object* v___x_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_172_ = l_Lean_JsonNumber_normalize(v_a_143_);
v_fst_173_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_fst_173_);
v_snd_174_ = lean_ctor_get(v___x_172_, 1);
lean_inc(v_snd_174_);
lean_dec_ref(v___x_172_);
v___x_175_ = l_Lean_JsonNumber_normalize(v_b_144_);
v_fst_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_fst_176_);
v_snd_177_ = lean_ctor_get(v___x_175_, 1);
lean_inc(v_snd_177_);
lean_dec_ref(v___x_175_);
v___x_184_ = lean_obj_once(&l_Lean_JsonNumber_normalize___closed__0, &l_Lean_JsonNumber_normalize___closed__0_once, _init_l_Lean_JsonNumber_normalize___closed__0);
v___x_185_ = lean_obj_once(&l_Lean_JsonNumber_normalize___closed__1, &l_Lean_JsonNumber_normalize___closed__1_once, _init_l_Lean_JsonNumber_normalize___closed__1);
v___x_186_ = lean_int_dec_eq(v_fst_173_, v___x_185_);
if (v___x_186_ == 0)
{
uint8_t v___x_187_; 
v___x_187_ = lean_int_dec_eq(v_fst_173_, v___x_184_);
if (v___x_187_ == 0)
{
goto v___jp_180_;
}
else
{
uint8_t v___x_188_; 
v___x_188_ = lean_int_dec_eq(v_fst_176_, v___x_185_);
if (v___x_188_ == 0)
{
goto v___jp_180_;
}
else
{
lean_dec(v_snd_177_);
lean_dec(v_fst_176_);
lean_dec(v_snd_174_);
lean_dec(v_fst_173_);
return v___x_186_;
}
}
}
else
{
uint8_t v___x_189_; 
v___x_189_ = lean_int_dec_eq(v_fst_176_, v___x_184_);
if (v___x_189_ == 0)
{
goto v___jp_180_;
}
else
{
lean_dec(v_snd_177_);
lean_dec(v_fst_176_);
lean_dec(v_snd_174_);
lean_dec(v_fst_173_);
return v___x_189_;
}
}
v___jp_145_:
{
if (v___y_147_ == 0)
{
uint8_t v___x_151_; 
v___x_151_ = lean_int_dec_lt(v___y_146_, v___y_148_);
lean_dec(v___y_148_);
lean_dec(v___y_146_);
if (v___x_151_ == 0)
{
uint8_t v___x_152_; 
v___x_152_ = lean_nat_dec_lt(v_fst_149_, v_snd_150_);
lean_dec(v_snd_150_);
lean_dec(v_fst_149_);
return v___x_152_;
}
else
{
lean_dec(v_snd_150_);
lean_dec(v_fst_149_);
return v___y_147_;
}
}
else
{
lean_dec(v_snd_150_);
lean_dec(v_fst_149_);
lean_dec(v___y_148_);
lean_dec(v___y_146_);
return v___y_147_;
}
}
v___jp_153_:
{
lean_object* v_fst_156_; lean_object* v_snd_157_; lean_object* v_fst_158_; lean_object* v_snd_159_; lean_object* v_amDigits_160_; lean_object* v_bmDigits_161_; uint8_t v___x_162_; uint8_t v___x_163_; 
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
v___x_162_ = lean_int_dec_lt(v_snd_157_, v_snd_159_);
v___x_163_ = lean_nat_dec_lt(v_amDigits_160_, v_bmDigits_161_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_164_ = lean_unsigned_to_nat(10u);
v___x_165_ = lean_nat_sub(v_amDigits_160_, v_bmDigits_161_);
lean_dec(v_bmDigits_161_);
lean_dec(v_amDigits_160_);
v___x_166_ = lean_nat_pow(v___x_164_, v___x_165_);
lean_dec(v___x_165_);
v___x_167_ = lean_nat_mul(v_fst_158_, v___x_166_);
lean_dec(v___x_166_);
lean_dec(v_fst_158_);
v___y_146_ = v_snd_159_;
v___y_147_ = v___x_162_;
v___y_148_ = v_snd_157_;
v_fst_149_ = v_fst_156_;
v_snd_150_ = v___x_167_;
goto v___jp_145_;
}
else
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_168_ = lean_unsigned_to_nat(10u);
v___x_169_ = lean_nat_sub(v_bmDigits_161_, v_amDigits_160_);
lean_dec(v_amDigits_160_);
lean_dec(v_bmDigits_161_);
v___x_170_ = lean_nat_pow(v___x_168_, v___x_169_);
lean_dec(v___x_169_);
v___x_171_ = lean_nat_mul(v_fst_156_, v___x_170_);
lean_dec(v___x_170_);
lean_dec(v_fst_156_);
v___y_146_ = v_snd_159_;
v___y_147_ = v___x_162_;
v___y_148_ = v_snd_157_;
v_fst_149_ = v___x_171_;
v_snd_150_ = v_fst_158_;
goto v___jp_145_;
}
}
v___jp_178_:
{
if (v___y_179_ == 0)
{
v_fst_154_ = v_snd_174_;
v_snd_155_ = v_snd_177_;
goto v___jp_153_;
}
else
{
v_fst_154_ = v_snd_177_;
v_snd_155_ = v_snd_174_;
goto v___jp_153_;
}
}
v___jp_180_:
{
lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_181_ = lean_obj_once(&l_Lean_JsonNumber_normalize___closed__1, &l_Lean_JsonNumber_normalize___closed__1_once, _init_l_Lean_JsonNumber_normalize___closed__1);
v___x_182_ = lean_int_dec_eq(v_fst_173_, v___x_181_);
lean_dec(v_fst_173_);
if (v___x_182_ == 0)
{
lean_dec(v_fst_176_);
v___y_179_ = v___x_182_;
goto v___jp_178_;
}
else
{
uint8_t v___x_183_; 
v___x_183_ = lean_int_dec_eq(v_fst_176_, v___x_181_);
lean_dec(v_fst_176_);
v___y_179_ = v___x_183_;
goto v___jp_178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_lt___boxed(lean_object* v_a_190_, lean_object* v_b_191_){
_start:
{
uint8_t v_res_192_; lean_object* v_r_193_; 
v_res_192_ = l_Lean_JsonNumber_lt(v_a_190_, v_b_191_);
v_r_193_ = lean_box(v_res_192_);
return v_r_193_;
}
}
static lean_object* _init_l_Lean_JsonNumber_ltProp(void){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = lean_box(0);
return v___x_194_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonNumber_instDecidableLt(lean_object* v_a_195_, lean_object* v_b_196_){
_start:
{
uint8_t v___x_197_; 
v___x_197_ = l_Lean_JsonNumber_lt(v_a_195_, v_b_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instDecidableLt___boxed(lean_object* v_a_198_, lean_object* v_b_199_){
_start:
{
uint8_t v_res_200_; lean_object* v_r_201_; 
v_res_200_ = l_Lean_JsonNumber_instDecidableLt(v_a_198_, v_b_199_);
v_r_201_ = lean_box(v_res_200_);
return v_r_201_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonNumber_instOrd___lam__0(lean_object* v_x_202_, lean_object* v_y_203_){
_start:
{
uint8_t v___x_204_; 
lean_inc_ref(v_y_203_);
lean_inc_ref(v_x_202_);
v___x_204_ = l_Lean_JsonNumber_lt(v_x_202_, v_y_203_);
if (v___x_204_ == 0)
{
uint8_t v___x_205_; 
v___x_205_ = l_Lean_JsonNumber_lt(v_y_203_, v_x_202_);
if (v___x_205_ == 0)
{
uint8_t v___x_206_; 
v___x_206_ = 1;
return v___x_206_;
}
else
{
uint8_t v___x_207_; 
v___x_207_ = 2;
return v___x_207_;
}
}
else
{
uint8_t v___x_208_; 
lean_dec_ref(v_y_203_);
lean_dec_ref(v_x_202_);
v___x_208_ = 0;
return v___x_208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOrd___lam__0___boxed(lean_object* v_x_209_, lean_object* v_y_210_){
_start:
{
uint8_t v_res_211_; lean_object* v_r_212_; 
v_res_211_ = l_Lean_JsonNumber_instOrd___lam__0(v_x_209_, v_y_210_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0(lean_object* v_s_215_, lean_object* v_begPos_216_, lean_object* v_i_217_){
_start:
{
uint8_t v___x_218_; 
v___x_218_ = lean_nat_dec_lt(v_begPos_216_, v_i_217_);
if (v___x_218_ == 0)
{
return v_i_217_;
}
else
{
lean_object* v_i_x27_219_; uint32_t v_c_220_; uint32_t v___x_221_; uint8_t v___x_222_; uint8_t v___x_223_; 
v_i_x27_219_ = lean_string_utf8_prev(v_s_215_, v_i_217_);
v_c_220_ = lean_string_utf8_get(v_s_215_, v_i_x27_219_);
v___x_221_ = 48;
v___x_222_ = lean_uint32_dec_eq(v_c_220_, v___x_221_);
v___x_223_ = lean_bool_not(v___x_222_);
if (v___x_223_ == 0)
{
lean_dec(v_i_217_);
v_i_217_ = v_i_x27_219_;
goto _start;
}
else
{
lean_dec(v_i_x27_219_);
return v_i_217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0___boxed(lean_object* v_s_225_, lean_object* v_begPos_226_, lean_object* v_i_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0(v_s_225_, v_begPos_226_, v_i_227_);
lean_dec(v_begPos_226_);
lean_dec_ref(v_s_225_);
return v_res_228_;
}
}
static lean_object* _init_l_Lean_JsonNumber_toString___closed__3(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_unsigned_to_nat(9u);
v___x_233_ = lean_nat_to_int(v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_toString(lean_object* v_x_235_){
_start:
{
lean_object* v___y_237_; lean_object* v___y_238_; lean_object* v___y_239_; lean_object* v___y_240_; lean_object* v_mantissa_246_; lean_object* v_exponent_247_; lean_object* v___x_248_; lean_object* v___y_250_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___y_253_; uint8_t v___y_254_; lean_object* v___y_255_; uint8_t v___y_256_; uint8_t v___x_270_; 
v_mantissa_246_ = lean_ctor_get(v_x_235_, 0);
lean_inc(v_mantissa_246_);
v_exponent_247_ = lean_ctor_get(v_x_235_, 1);
lean_inc(v_exponent_247_);
lean_dec_ref(v_x_235_);
v___x_248_ = lean_unsigned_to_nat(0u);
v___x_270_ = lean_nat_dec_eq(v_exponent_247_, v___x_248_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v___y_275_; lean_object* v___y_286_; uint8_t v___x_295_; 
v___x_271_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v___x_295_ = lean_int_dec_le(v___x_271_, v_mantissa_246_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; 
v___x_296_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__4));
v___y_286_ = v___x_296_;
goto v___jp_285_;
}
else
{
lean_object* v___x_297_; 
v___x_297_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__2));
v___y_286_ = v___x_297_;
goto v___jp_285_;
}
v___jp_272_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v_e_x27_279_; lean_object* v___x_280_; lean_object* v_left_281_; uint8_t v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_276_ = lean_unsigned_to_nat(10u);
v___x_277_ = lean_nat_abs(v___y_275_);
v___x_278_ = lean_nat_sub(v_exponent_247_, v___x_277_);
lean_dec(v___x_277_);
lean_dec(v_exponent_247_);
v_e_x27_279_ = lean_nat_pow(v___x_276_, v___x_278_);
lean_dec(v___x_278_);
v___x_280_ = lean_nat_div(v___y_273_, v_e_x27_279_);
v_left_281_ = l_Nat_reprFast(v___x_280_);
v___x_282_ = lean_int_dec_eq(v___y_275_, v___x_271_);
v___x_283_ = lean_nat_mod(v___y_273_, v_e_x27_279_);
lean_dec(v___y_273_);
v___x_284_ = lean_nat_dec_eq(v___x_283_, v___x_248_);
if (v___x_284_ == 0)
{
v___y_250_ = v_e_x27_279_;
v___y_251_ = v___x_283_;
v___y_252_ = v_left_281_;
v___y_253_ = v___y_275_;
v___y_254_ = v___x_282_;
v___y_255_ = v___y_274_;
v___y_256_ = v___x_284_;
goto v___jp_249_;
}
else
{
v___y_250_ = v_e_x27_279_;
v___y_251_ = v___x_283_;
v___y_252_ = v_left_281_;
v___y_253_ = v___y_275_;
v___y_254_ = v___x_282_;
v___y_255_ = v___y_274_;
v___y_256_ = v___x_282_;
goto v___jp_249_;
}
}
v___jp_285_:
{
lean_object* v_m_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v_exp_293_; uint8_t v___x_294_; 
v_m_287_ = lean_nat_abs(v_mantissa_246_);
lean_dec(v_mantissa_246_);
v___x_288_ = lean_obj_once(&l_Lean_JsonNumber_toString___closed__3, &l_Lean_JsonNumber_toString___closed__3_once, _init_l_Lean_JsonNumber_toString___closed__3);
lean_inc(v_m_287_);
v___x_289_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(v_m_287_);
v___x_290_ = lean_nat_to_int(v___x_289_);
v___x_291_ = lean_int_add(v___x_288_, v___x_290_);
lean_dec(v___x_290_);
lean_inc(v_exponent_247_);
v___x_292_ = lean_nat_to_int(v_exponent_247_);
v_exp_293_ = lean_int_sub(v___x_291_, v___x_292_);
lean_dec(v___x_292_);
lean_dec(v___x_291_);
v___x_294_ = lean_int_dec_lt(v_exp_293_, v___x_271_);
if (v___x_294_ == 0)
{
lean_dec(v_exp_293_);
v___y_273_ = v_m_287_;
v___y_274_ = v___y_286_;
v___y_275_ = v___x_271_;
goto v___jp_272_;
}
else
{
v___y_273_ = v_m_287_;
v___y_274_ = v___y_286_;
v___y_275_ = v_exp_293_;
goto v___jp_272_;
}
}
}
else
{
lean_object* v___x_298_; 
lean_dec(v_exponent_247_);
v___x_298_ = l_Int_repr(v_mantissa_246_);
lean_dec(v_mantissa_246_);
return v___x_298_;
}
v___jp_236_:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
lean_inc_ref(v___y_239_);
v___x_241_ = lean_string_append(v___y_239_, v___y_238_);
lean_dec_ref(v___y_238_);
v___x_242_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__0));
v___x_243_ = lean_string_append(v___x_241_, v___x_242_);
v___x_244_ = lean_string_append(v___x_243_, v___y_237_);
lean_dec_ref(v___y_237_);
v___x_245_ = lean_string_append(v___x_244_, v___y_240_);
lean_dec_ref(v___y_240_);
return v___x_245_;
}
v___jp_249_:
{
if (v___y_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v_e_263_; lean_object* v_right_264_; 
v___x_257_ = lean_nat_add(v___y_250_, v___y_251_);
lean_dec(v___y_251_);
lean_dec(v___y_250_);
v___x_258_ = l_Nat_reprFast(v___x_257_);
v___x_259_ = lean_string_utf8_byte_size(v___x_258_);
lean_inc_ref(v___x_258_);
v___x_260_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_260_, 0, v___x_258_);
lean_ctor_set(v___x_260_, 1, v___x_248_);
lean_ctor_set(v___x_260_, 2, v___x_259_);
v___x_261_ = lean_unsigned_to_nat(1u);
v___x_262_ = l_Substring_Raw_nextn(v___x_260_, v___x_261_, v___x_248_);
lean_dec_ref_known(v___x_260_, 3);
v_e_263_ = l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0(v___x_258_, v___x_262_, v___x_259_);
v_right_264_ = lean_string_utf8_extract(v___x_258_, v___x_262_, v_e_263_);
lean_dec(v_e_263_);
lean_dec(v___x_262_);
lean_dec_ref(v___x_258_);
if (v___y_254_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__1));
v___x_266_ = l_Int_repr(v___y_253_);
lean_dec(v___y_253_);
v___x_267_ = lean_string_append(v___x_265_, v___x_266_);
lean_dec_ref(v___x_266_);
v___y_237_ = v_right_264_;
v___y_238_ = v___y_252_;
v___y_239_ = v___y_255_;
v___y_240_ = v___x_267_;
goto v___jp_236_;
}
else
{
lean_object* v___x_268_; 
lean_dec(v___y_253_);
v___x_268_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__2));
v___y_237_ = v_right_264_;
v___y_238_ = v___y_252_;
v___y_239_ = v___y_255_;
v___y_240_ = v___x_268_;
goto v___jp_236_;
}
}
else
{
lean_object* v___x_269_; 
lean_dec(v___y_253_);
lean_dec(v___y_251_);
lean_dec(v___y_250_);
lean_inc_ref(v___y_255_);
v___x_269_ = lean_string_append(v___y_255_, v___y_252_);
lean_dec_ref(v___y_252_);
return v___x_269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftl(lean_object* v_x_299_, lean_object* v_x_300_){
_start:
{
lean_object* v_mantissa_301_; lean_object* v_exponent_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_315_; 
v_mantissa_301_ = lean_ctor_get(v_x_299_, 0);
v_exponent_302_ = lean_ctor_get(v_x_299_, 1);
v_isSharedCheck_315_ = !lean_is_exclusive(v_x_299_);
if (v_isSharedCheck_315_ == 0)
{
v___x_304_ = v_x_299_;
v_isShared_305_ = v_isSharedCheck_315_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_exponent_302_);
lean_inc(v_mantissa_301_);
lean_dec(v_x_299_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_315_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_306_ = lean_unsigned_to_nat(10u);
v___x_307_ = lean_nat_sub(v_x_300_, v_exponent_302_);
v___x_308_ = lean_nat_pow(v___x_306_, v___x_307_);
lean_dec(v___x_307_);
v___x_309_ = lean_nat_to_int(v___x_308_);
v___x_310_ = lean_int_mul(v_mantissa_301_, v___x_309_);
lean_dec(v___x_309_);
lean_dec(v_mantissa_301_);
v___x_311_ = lean_nat_sub(v_exponent_302_, v_x_300_);
lean_dec(v_exponent_302_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 1, v___x_311_);
lean_ctor_set(v___x_304_, 0, v___x_310_);
v___x_313_ = v___x_304_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftl___boxed(lean_object* v_x_316_, lean_object* v_x_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_JsonNumber_shiftl(v_x_316_, v_x_317_);
lean_dec(v_x_317_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftr(lean_object* v_x_319_, lean_object* v_x_320_){
_start:
{
lean_object* v_mantissa_321_; lean_object* v_exponent_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_330_; 
v_mantissa_321_ = lean_ctor_get(v_x_319_, 0);
v_exponent_322_ = lean_ctor_get(v_x_319_, 1);
v_isSharedCheck_330_ = !lean_is_exclusive(v_x_319_);
if (v_isSharedCheck_330_ == 0)
{
v___x_324_ = v_x_319_;
v_isShared_325_ = v_isSharedCheck_330_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_exponent_322_);
lean_inc(v_mantissa_321_);
lean_dec(v_x_319_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_330_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_326_ = lean_nat_add(v_exponent_322_, v_x_320_);
lean_dec(v_exponent_322_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 1, v___x_326_);
v___x_328_ = v___x_324_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_mantissa_321_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v___x_326_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftr___boxed(lean_object* v_x_331_, lean_object* v_x_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_JsonNumber_shiftr(v_x_331_, v_x_332_);
lean_dec(v_x_332_);
return v_res_333_;
}
}
static lean_object* _init_l_Lean_JsonNumber_instRepr___lam__0___closed__4(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = ((lean_object*)(l_Lean_JsonNumber_instRepr___lam__0___closed__0));
v___x_342_ = lean_string_length(v___x_341_);
return v___x_342_;
}
}
static lean_object* _init_l_Lean_JsonNumber_instRepr___lam__0___closed__5(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_obj_once(&l_Lean_JsonNumber_instRepr___lam__0___closed__4, &l_Lean_JsonNumber_instRepr___lam__0___closed__4_once, _init_l_Lean_JsonNumber_instRepr___lam__0___closed__4);
v___x_344_ = lean_nat_to_int(v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instRepr___lam__0(lean_object* v_x_349_, lean_object* v_x_350_){
_start:
{
lean_object* v_mantissa_351_; lean_object* v_exponent_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_381_; 
v_mantissa_351_ = lean_ctor_get(v_x_349_, 0);
v_exponent_352_ = lean_ctor_get(v_x_349_, 1);
v_isSharedCheck_381_ = !lean_is_exclusive(v_x_349_);
if (v_isSharedCheck_381_ == 0)
{
v___x_354_ = v_x_349_;
v_isShared_355_ = v_isSharedCheck_381_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_exponent_352_);
lean_inc(v_mantissa_351_);
lean_dec(v_x_349_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_381_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___y_357_; lean_object* v___x_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_373_ = lean_unsigned_to_nat(0u);
v___x_374_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v___x_375_ = lean_int_dec_lt(v_mantissa_351_, v___x_374_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = l_Int_repr(v_mantissa_351_);
lean_dec(v_mantissa_351_);
v___x_377_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
v___y_357_ = v___x_377_;
goto v___jp_356_;
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_378_ = l_Int_repr(v_mantissa_351_);
lean_dec(v_mantissa_351_);
v___x_379_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
v___x_380_ = l_Repr_addAppParen(v___x_379_, v___x_373_);
v___y_357_ = v___x_380_;
goto v___jp_356_;
}
v___jp_356_:
{
lean_object* v___x_358_; lean_object* v___x_360_; 
v___x_358_ = ((lean_object*)(l_Lean_JsonNumber_instRepr___lam__0___closed__2));
if (v_isShared_355_ == 0)
{
lean_ctor_set_tag(v___x_354_, 5);
lean_ctor_set(v___x_354_, 1, v___x_358_);
lean_ctor_set(v___x_354_, 0, v___y_357_);
v___x_360_ = v___x_354_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___y_357_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v___x_358_);
v___x_360_ = v_reuseFailAlloc_372_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; lean_object* v___x_371_; 
v___x_361_ = l_Nat_reprFast(v_exponent_352_);
v___x_362_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
v___x_363_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_360_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___x_364_ = lean_obj_once(&l_Lean_JsonNumber_instRepr___lam__0___closed__5, &l_Lean_JsonNumber_instRepr___lam__0___closed__5_once, _init_l_Lean_JsonNumber_instRepr___lam__0___closed__5);
v___x_365_ = ((lean_object*)(l_Lean_JsonNumber_instRepr___lam__0___closed__6));
v___x_366_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
lean_ctor_set(v___x_366_, 1, v___x_363_);
v___x_367_ = ((lean_object*)(l_Lean_JsonNumber_instRepr___lam__0___closed__7));
v___x_368_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_366_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v___x_369_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_364_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
v___x_370_ = 0;
v___x_371_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_371_, 0, v___x_369_);
lean_ctor_set_uint8(v___x_371_, sizeof(void*)*1, v___x_370_);
return v___x_371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instRepr___lam__0___boxed(lean_object* v_x_382_, lean_object* v_x_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_JsonNumber_instRepr___lam__0(v_x_382_, v_x_383_);
lean_dec(v_x_383_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOfScientific___lam__0(lean_object* v_mantissa_387_, uint8_t v_exponentSign_388_, lean_object* v_decimalExponent_389_){
_start:
{
if (v_exponentSign_388_ == 0)
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_390_ = lean_unsigned_to_nat(10u);
v___x_391_ = lean_nat_pow(v___x_390_, v_decimalExponent_389_);
lean_dec(v_decimalExponent_389_);
v___x_392_ = lean_nat_mul(v_mantissa_387_, v___x_391_);
lean_dec(v___x_391_);
lean_dec(v_mantissa_387_);
v___x_393_ = lean_nat_to_int(v___x_392_);
v___x_394_ = lean_unsigned_to_nat(0u);
v___x_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_393_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
return v___x_395_;
}
else
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = lean_nat_to_int(v_mantissa_387_);
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
lean_ctor_set(v___x_397_, 1, v_decimalExponent_389_);
return v___x_397_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOfScientific___lam__0___boxed(lean_object* v_mantissa_398_, lean_object* v_exponentSign_399_, lean_object* v_decimalExponent_400_){
_start:
{
uint8_t v_exponentSign_boxed_401_; lean_object* v_res_402_; 
v_exponentSign_boxed_401_ = lean_unbox(v_exponentSign_399_);
v_res_402_ = l_Lean_JsonNumber_instOfScientific___lam__0(v_mantissa_398_, v_exponentSign_boxed_401_, v_decimalExponent_400_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instNeg___lam__0(lean_object* v_jn_405_){
_start:
{
lean_object* v_mantissa_406_; lean_object* v_exponent_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_415_; 
v_mantissa_406_ = lean_ctor_get(v_jn_405_, 0);
v_exponent_407_ = lean_ctor_get(v_jn_405_, 1);
v_isSharedCheck_415_ = !lean_is_exclusive(v_jn_405_);
if (v_isSharedCheck_415_ == 0)
{
v___x_409_ = v_jn_405_;
v_isShared_410_ = v_isSharedCheck_415_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_exponent_407_);
lean_inc(v_mantissa_406_);
lean_dec(v_jn_405_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_415_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_411_ = lean_int_neg(v_mantissa_406_);
lean_dec(v_mantissa_406_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_411_);
v___x_413_ = v___x_409_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_411_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v_exponent_407_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
static lean_object* _init_l_Lean_JsonNumber_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = l_Lean_JsonNumber_fromNat(v___x_418_);
return v___x_419_;
}
}
static lean_object* _init_l_Lean_JsonNumber_instInhabited(void){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = lean_obj_once(&l_Lean_JsonNumber_instInhabited___closed__0, &l_Lean_JsonNumber_instInhabited___closed__0_once, _init_l_Lean_JsonNumber_instInhabited___closed__0);
return v___x_420_;
}
}
static double _init_l_Lean_JsonNumber_toFloat___closed__0(void){
_start:
{
lean_object* v___x_421_; uint8_t v___x_422_; lean_object* v___x_423_; double v___x_424_; 
v___x_421_ = lean_unsigned_to_nat(1u);
v___x_422_ = 1;
v___x_423_ = lean_unsigned_to_nat(10u);
v___x_424_ = l_Float_ofScientific(v___x_423_, v___x_422_, v___x_421_);
return v___x_424_;
}
}
static double _init_l_Lean_JsonNumber_toFloat___closed__1(void){
_start:
{
double v___x_425_; double v___x_426_; 
v___x_425_ = lean_float_once(&l_Lean_JsonNumber_toFloat___closed__0, &l_Lean_JsonNumber_toFloat___closed__0_once, _init_l_Lean_JsonNumber_toFloat___closed__0);
v___x_426_ = lean_float_negate(v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT double l_Lean_JsonNumber_toFloat(lean_object* v_x_427_){
_start:
{
lean_object* v_mantissa_428_; lean_object* v_exponent_429_; double v___y_431_; lean_object* v___x_436_; uint8_t v___x_437_; 
v_mantissa_428_ = lean_ctor_get(v_x_427_, 0);
lean_inc(v_mantissa_428_);
v_exponent_429_ = lean_ctor_get(v_x_427_, 1);
lean_inc(v_exponent_429_);
lean_dec_ref(v_x_427_);
v___x_436_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v___x_437_ = lean_int_dec_le(v___x_436_, v_mantissa_428_);
if (v___x_437_ == 0)
{
double v___x_438_; 
v___x_438_ = lean_float_once(&l_Lean_JsonNumber_toFloat___closed__1, &l_Lean_JsonNumber_toFloat___closed__1_once, _init_l_Lean_JsonNumber_toFloat___closed__1);
v___y_431_ = v___x_438_;
goto v___jp_430_;
}
else
{
lean_object* v___x_439_; lean_object* v___x_440_; double v___x_441_; 
v___x_439_ = lean_unsigned_to_nat(10u);
v___x_440_ = lean_unsigned_to_nat(1u);
v___x_441_ = l_Float_ofScientific(v___x_439_, v___x_437_, v___x_440_);
v___y_431_ = v___x_441_;
goto v___jp_430_;
}
v___jp_430_:
{
lean_object* v___x_432_; uint8_t v___x_433_; double v___x_434_; double v___x_435_; 
v___x_432_ = lean_nat_abs(v_mantissa_428_);
lean_dec(v_mantissa_428_);
v___x_433_ = 1;
v___x_434_ = l_Float_ofScientific(v___x_432_, v___x_433_, v_exponent_429_);
v___x_435_ = lean_float_mul(v___y_431_, v___x_434_);
return v___x_435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_toFloat___boxed(lean_object* v_x_442_){
_start:
{
double v_res_443_; lean_object* v_r_444_; 
v_res_443_ = l_Lean_JsonNumber_toFloat(v_x_442_);
v_r_444_ = lean_box_float(v_res_443_);
return v_r_444_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21_spec__0(lean_object* v_msg_445_){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = l_Lean_JsonNumber_instInhabited;
v___x_447_ = lean_panic_fn_borrowed(v___x_446_, v_msg_445_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(double v_x_451_){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = lean_float_to_string(v_x_451_);
v___x_453_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v___x_452_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_454_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0));
v___x_455_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__1));
v___x_456_ = lean_unsigned_to_nat(160u);
v___x_457_ = lean_unsigned_to_nat(12u);
v___x_458_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__2));
v___x_459_ = lean_string_append(v___x_458_, v___x_452_);
lean_dec_ref(v___x_452_);
v___x_460_ = l_mkPanicMessageWithDecl(v___x_454_, v___x_455_, v___x_456_, v___x_457_, v___x_459_);
lean_dec_ref(v___x_459_);
v___x_461_ = l_panic___at___00__private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21_spec__0(v___x_460_);
return v___x_461_;
}
else
{
lean_object* v_val_462_; lean_object* v_snd_463_; lean_object* v_fst_464_; uint8_t v___x_465_; 
lean_dec_ref(v___x_452_);
v_val_462_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_val_462_);
lean_dec_ref_known(v___x_453_, 1);
v_snd_463_ = lean_ctor_get(v_val_462_, 1);
lean_inc(v_snd_463_);
v_fst_464_ = lean_ctor_get(v_snd_463_, 0);
v___x_465_ = lean_unbox(v_fst_464_);
if (v___x_465_ == 0)
{
lean_object* v_fst_466_; lean_object* v_snd_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_479_; 
v_fst_466_ = lean_ctor_get(v_val_462_, 0);
lean_inc(v_fst_466_);
lean_dec(v_val_462_);
v_snd_467_ = lean_ctor_get(v_snd_463_, 1);
v_isSharedCheck_479_ = !lean_is_exclusive(v_snd_463_);
if (v_isSharedCheck_479_ == 0)
{
lean_object* v_unused_480_; 
v_unused_480_ = lean_ctor_get(v_snd_463_, 0);
lean_dec(v_unused_480_);
v___x_469_ = v_snd_463_;
v_isShared_470_ = v_isSharedCheck_479_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_snd_467_);
lean_dec(v_snd_463_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_479_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_471_ = lean_unsigned_to_nat(10u);
v___x_472_ = lean_nat_pow(v___x_471_, v_snd_467_);
lean_dec(v_snd_467_);
v___x_473_ = lean_nat_mul(v_fst_466_, v___x_472_);
lean_dec(v___x_472_);
lean_dec(v_fst_466_);
v___x_474_ = lean_nat_to_int(v___x_473_);
v___x_475_ = lean_unsigned_to_nat(0u);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 1, v___x_475_);
lean_ctor_set(v___x_469_, 0, v___x_474_);
v___x_477_ = v___x_469_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
else
{
lean_object* v_fst_481_; lean_object* v_snd_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_490_; 
v_fst_481_ = lean_ctor_get(v_val_462_, 0);
lean_inc(v_fst_481_);
lean_dec(v_val_462_);
v_snd_482_ = lean_ctor_get(v_snd_463_, 1);
v_isSharedCheck_490_ = !lean_is_exclusive(v_snd_463_);
if (v_isSharedCheck_490_ == 0)
{
lean_object* v_unused_491_; 
v_unused_491_ = lean_ctor_get(v_snd_463_, 0);
lean_dec(v_unused_491_);
v___x_484_ = v_snd_463_;
v_isShared_485_ = v_isSharedCheck_490_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_snd_482_);
lean_dec(v_snd_463_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_490_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_486_; lean_object* v___x_488_; 
v___x_486_ = lean_nat_to_int(v_fst_481_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v___x_486_);
v___x_488_ = v___x_484_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v_snd_482_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___boxed(lean_object* v_x_492_){
_start:
{
double v_x_boxed_493_; lean_object* v_res_494_; 
v_x_boxed_493_ = lean_unbox_float(v_x_492_);
lean_dec_ref(v_x_492_);
v_res_494_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(v_x_boxed_493_);
return v_res_494_;
}
}
static double _init_l_Lean_JsonNumber_fromFloat_x3f___closed__0(void){
_start:
{
lean_object* v___x_495_; uint8_t v___x_496_; lean_object* v___x_497_; double v___x_498_; 
v___x_495_ = lean_unsigned_to_nat(1u);
v___x_496_ = 1;
v___x_497_ = lean_unsigned_to_nat(0u);
v___x_498_ = l_Float_ofScientific(v___x_497_, v___x_496_, v___x_495_);
return v___x_498_;
}
}
static lean_object* _init_l_Lean_JsonNumber_fromFloat_x3f___closed__1(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_obj_once(&l_Lean_JsonNumber_instInhabited___closed__0, &l_Lean_JsonNumber_instInhabited___closed__0_once, _init_l_Lean_JsonNumber_instInhabited___closed__0);
v___x_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
return v___x_500_;
}
}
static double _init_l_Lean_JsonNumber_fromFloat_x3f___closed__2(void){
_start:
{
lean_object* v___x_501_; double v___x_502_; 
v___x_501_ = lean_unsigned_to_nat(0u);
v___x_502_ = lean_float_of_nat(v___x_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_fromFloat_x3f(double v_x_512_){
_start:
{
uint8_t v___x_513_; 
v___x_513_ = lean_float_isnan(v_x_512_);
if (v___x_513_ == 0)
{
uint8_t v___x_514_; 
v___x_514_ = lean_float_isinf(v_x_512_);
if (v___x_514_ == 0)
{
double v___x_515_; uint8_t v___x_516_; 
v___x_515_ = lean_float_once(&l_Lean_JsonNumber_fromFloat_x3f___closed__0, &l_Lean_JsonNumber_fromFloat_x3f___closed__0_once, _init_l_Lean_JsonNumber_fromFloat_x3f___closed__0);
v___x_516_ = lean_float_beq(v_x_512_, v___x_515_);
if (v___x_516_ == 0)
{
uint8_t v___x_517_; 
v___x_517_ = lean_float_decLt(v_x_512_, v___x_515_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(v_x_512_);
v___x_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
return v___x_519_;
}
else
{
double v___x_520_; lean_object* v___x_521_; lean_object* v_mantissa_522_; lean_object* v_exponent_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_532_; 
v___x_520_ = lean_float_negate(v_x_512_);
v___x_521_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(v___x_520_);
v_mantissa_522_ = lean_ctor_get(v___x_521_, 0);
v_exponent_523_ = lean_ctor_get(v___x_521_, 1);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_532_ == 0)
{
v___x_525_ = v___x_521_;
v_isShared_526_ = v_isSharedCheck_532_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_exponent_523_);
lean_inc(v_mantissa_522_);
lean_dec(v___x_521_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_532_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_527_ = lean_int_neg(v_mantissa_522_);
lean_dec(v_mantissa_522_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___x_527_);
v___x_529_ = v___x_525_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_exponent_523_);
v___x_529_ = v_reuseFailAlloc_531_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
lean_object* v___x_530_; 
v___x_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
}
}
}
else
{
lean_object* v___x_533_; 
v___x_533_ = lean_obj_once(&l_Lean_JsonNumber_fromFloat_x3f___closed__1, &l_Lean_JsonNumber_fromFloat_x3f___closed__1_once, _init_l_Lean_JsonNumber_fromFloat_x3f___closed__1);
return v___x_533_;
}
}
else
{
double v___x_534_; uint8_t v___x_535_; 
v___x_534_ = lean_float_once(&l_Lean_JsonNumber_fromFloat_x3f___closed__2, &l_Lean_JsonNumber_fromFloat_x3f___closed__2_once, _init_l_Lean_JsonNumber_fromFloat_x3f___closed__2);
v___x_535_ = lean_float_decLt(v___x_534_, v_x_512_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; 
v___x_536_ = ((lean_object*)(l_Lean_JsonNumber_fromFloat_x3f___closed__4));
return v___x_536_;
}
else
{
lean_object* v___x_537_; 
v___x_537_ = ((lean_object*)(l_Lean_JsonNumber_fromFloat_x3f___closed__6));
return v___x_537_;
}
}
}
else
{
lean_object* v___x_538_; 
v___x_538_ = ((lean_object*)(l_Lean_JsonNumber_fromFloat_x3f___closed__8));
return v___x_538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_fromFloat_x3f___boxed(lean_object* v_x_539_){
_start:
{
double v_x_boxed_540_; lean_object* v_res_541_; 
v_x_boxed_540_ = lean_unbox_float(v_x_539_);
lean_dec_ref(v_x_539_);
v_res_541_ = l_Lean_JsonNumber_fromFloat_x3f(v_x_boxed_540_);
return v_res_541_;
}
}
LEAN_EXPORT uint8_t l_Lean_strLt(lean_object* v_a_542_, lean_object* v_b_543_){
_start:
{
uint8_t v___x_544_; 
v___x_544_ = lean_string_dec_lt(v_a_542_, v_b_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_strLt___boxed(lean_object* v_a_545_, lean_object* v_b_546_){
_start:
{
uint8_t v_res_547_; lean_object* v_r_548_; 
v_res_547_ = l_Lean_strLt(v_a_545_, v_b_546_);
lean_dec_ref(v_b_546_);
lean_dec_ref(v_a_545_);
v_r_548_ = lean_box(v_res_547_);
return v_r_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorIdx(lean_object* v_x_549_){
_start:
{
switch(lean_obj_tag(v_x_549_))
{
case 0:
{
lean_object* v___x_550_; 
v___x_550_ = lean_unsigned_to_nat(0u);
return v___x_550_;
}
case 1:
{
lean_object* v___x_551_; 
v___x_551_ = lean_unsigned_to_nat(1u);
return v___x_551_;
}
case 2:
{
lean_object* v___x_552_; 
v___x_552_ = lean_unsigned_to_nat(2u);
return v___x_552_;
}
case 3:
{
lean_object* v___x_553_; 
v___x_553_ = lean_unsigned_to_nat(3u);
return v___x_553_;
}
case 4:
{
lean_object* v___x_554_; 
v___x_554_ = lean_unsigned_to_nat(4u);
return v___x_554_;
}
default: 
{
lean_object* v___x_555_; 
v___x_555_ = lean_unsigned_to_nat(5u);
return v___x_555_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorIdx___boxed(lean_object* v_x_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_Json_ctorIdx(v_x_556_);
lean_dec(v_x_556_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorElim___redArg(lean_object* v_t_558_, lean_object* v_k_559_){
_start:
{
switch(lean_obj_tag(v_t_558_))
{
case 0:
{
return v_k_559_;
}
case 1:
{
uint8_t v_b_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v_b_560_ = lean_ctor_get_uint8(v_t_558_, 0);
lean_dec_ref_known(v_t_558_, 0);
v___x_561_ = lean_box(v_b_560_);
v___x_562_ = lean_apply_1(v_k_559_, v___x_561_);
return v___x_562_;
}
case 5:
{
lean_object* v_kvPairs_563_; lean_object* v___x_564_; 
v_kvPairs_563_ = lean_ctor_get(v_t_558_, 0);
lean_inc(v_kvPairs_563_);
lean_dec_ref_known(v_t_558_, 1);
v___x_564_ = lean_apply_1(v_k_559_, v_kvPairs_563_);
return v___x_564_;
}
default: 
{
lean_object* v_n_565_; lean_object* v___x_566_; 
v_n_565_ = lean_ctor_get(v_t_558_, 0);
lean_inc_ref(v_n_565_);
lean_dec(v_t_558_);
v___x_566_ = lean_apply_1(v_k_559_, v_n_565_);
return v___x_566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorElim(lean_object* v_motive__1_567_, lean_object* v_ctorIdx_568_, lean_object* v_t_569_, lean_object* v_h_570_, lean_object* v_k_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_Json_ctorElim___redArg(v_t_569_, v_k_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorElim___boxed(lean_object* v_motive__1_573_, lean_object* v_ctorIdx_574_, lean_object* v_t_575_, lean_object* v_h_576_, lean_object* v_k_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_Json_ctorElim(v_motive__1_573_, v_ctorIdx_574_, v_t_575_, v_h_576_, v_k_577_);
lean_dec(v_ctorIdx_574_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_null_elim___redArg(lean_object* v_t_579_, lean_object* v_null_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_Json_ctorElim___redArg(v_t_579_, v_null_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_null_elim(lean_object* v_motive__1_582_, lean_object* v_t_583_, lean_object* v_h_584_, lean_object* v_null_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_Json_ctorElim___redArg(v_t_583_, v_null_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_bool_elim___redArg(lean_object* v_t_587_, lean_object* v_bool_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_Lean_Json_ctorElim___redArg(v_t_587_, v_bool_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_bool_elim(lean_object* v_motive__1_590_, lean_object* v_t_591_, lean_object* v_h_592_, lean_object* v_bool_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_Json_ctorElim___redArg(v_t_591_, v_bool_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_num_elim___redArg(lean_object* v_t_595_, lean_object* v_num_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_Json_ctorElim___redArg(v_t_595_, v_num_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_num_elim(lean_object* v_motive__1_598_, lean_object* v_t_599_, lean_object* v_h_600_, lean_object* v_num_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_Json_ctorElim___redArg(v_t_599_, v_num_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_str_elim___redArg(lean_object* v_t_603_, lean_object* v_str_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_Json_ctorElim___redArg(v_t_603_, v_str_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_str_elim(lean_object* v_motive__1_606_, lean_object* v_t_607_, lean_object* v_h_608_, lean_object* v_str_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_Json_ctorElim___redArg(v_t_607_, v_str_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_arr_elim___redArg(lean_object* v_t_611_, lean_object* v_arr_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Lean_Json_ctorElim___redArg(v_t_611_, v_arr_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_arr_elim(lean_object* v_motive__1_614_, lean_object* v_t_615_, lean_object* v_h_616_, lean_object* v_arr_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Lean_Json_ctorElim___redArg(v_t_615_, v_arr_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_obj_elim___redArg(lean_object* v_t_619_, lean_object* v_obj_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_Json_ctorElim___redArg(v_t_619_, v_obj_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_obj_elim(lean_object* v_motive__1_622_, lean_object* v_t_623_, lean_object* v_h_624_, lean_object* v_obj_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Lean_Json_ctorElim___redArg(v_t_623_, v_obj_625_);
return v___x_626_;
}
}
static lean_object* _init_l_Lean_instInhabitedJson_default(void){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = lean_box(0);
return v___x_627_;
}
}
static lean_object* _init_l_Lean_instInhabitedJson(void){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = lean_box(0);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(lean_object* v_init_629_, lean_object* v_x_630_){
_start:
{
if (lean_obj_tag(v_x_630_) == 0)
{
lean_object* v_l_631_; lean_object* v_r_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v_l_631_ = lean_ctor_get(v_x_630_, 3);
v_r_632_ = lean_ctor_get(v_x_630_, 4);
v___x_633_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_629_, v_l_631_);
v___x_634_ = lean_unsigned_to_nat(1u);
v___x_635_ = lean_nat_add(v___x_633_, v___x_634_);
lean_dec(v___x_633_);
v_init_629_ = v___x_635_;
v_x_630_ = v_r_632_;
goto _start;
}
else
{
return v_init_629_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1___boxed(lean_object* v_init_637_, lean_object* v_x_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_637_, v_x_638_);
lean_dec(v_x_638_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(lean_object* v_t_640_, lean_object* v_k_641_){
_start:
{
if (lean_obj_tag(v_t_640_) == 0)
{
lean_object* v_k_642_; lean_object* v_v_643_; lean_object* v_l_644_; lean_object* v_r_645_; uint8_t v___x_646_; 
v_k_642_ = lean_ctor_get(v_t_640_, 1);
v_v_643_ = lean_ctor_get(v_t_640_, 2);
v_l_644_ = lean_ctor_get(v_t_640_, 3);
v_r_645_ = lean_ctor_get(v_t_640_, 4);
v___x_646_ = lean_string_compare(v_k_641_, v_k_642_);
switch(v___x_646_)
{
case 0:
{
v_t_640_ = v_l_644_;
goto _start;
}
case 1:
{
lean_object* v___x_648_; 
lean_inc(v_v_643_);
v___x_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_648_, 0, v_v_643_);
return v___x_648_;
}
default: 
{
v_t_640_ = v_r_645_;
goto _start;
}
}
}
else
{
lean_object* v___x_650_; 
v___x_650_ = lean_box(0);
return v___x_650_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg___boxed(lean_object* v_t_651_, lean_object* v_k_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_t_651_, v_k_652_);
lean_dec_ref(v_k_652_);
lean_dec(v_t_651_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(lean_object* v_kvPairs_657_, lean_object* v_init_658_, lean_object* v_x_659_){
_start:
{
if (lean_obj_tag(v_x_659_) == 0)
{
lean_object* v_k_660_; lean_object* v_v_661_; lean_object* v_l_662_; lean_object* v_r_663_; lean_object* v___x_664_; 
v_k_660_ = lean_ctor_get(v_x_659_, 1);
v_v_661_ = lean_ctor_get(v_x_659_, 2);
v_l_662_ = lean_ctor_get(v_x_659_, 3);
v_r_663_ = lean_ctor_get(v_x_659_, 4);
v___x_664_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_kvPairs_657_, v_init_658_, v_l_662_);
if (lean_obj_tag(v___x_664_) == 0)
{
return v___x_664_;
}
else
{
lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_683_; 
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_683_ == 0)
{
lean_object* v_unused_684_; 
v_unused_684_ = lean_ctor_get(v___x_664_, 0);
lean_dec(v_unused_684_);
v___x_666_ = v___x_664_;
v_isShared_667_ = v_isSharedCheck_683_;
goto v_resetjp_665_;
}
else
{
lean_dec(v___x_664_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_683_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; uint8_t v___y_670_; lean_object* v___x_677_; 
v___x_668_ = lean_box(0);
v___x_677_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_kvPairs_657_, v_k_660_);
if (lean_obj_tag(v___x_677_) == 0)
{
uint8_t v___x_678_; 
v___x_678_ = 0;
v___y_670_ = v___x_678_;
goto v___jp_669_;
}
else
{
lean_object* v_val_679_; uint8_t v___x_680_; 
v_val_679_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_val_679_);
lean_dec_ref_known(v___x_677_, 1);
v___x_680_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_v_661_, v_val_679_);
lean_dec(v_val_679_);
if (v___x_680_ == 0)
{
v___y_670_ = v___x_680_;
goto v___jp_669_;
}
else
{
lean_object* v___x_681_; 
lean_del_object(v___x_666_);
v___x_681_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__0));
v_init_658_ = v___x_681_;
v_x_659_ = v_r_663_;
goto _start;
}
}
v___jp_669_:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_671_ = lean_box(v___y_670_);
v___x_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
v___x_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
lean_ctor_set(v___x_673_, 1, v___x_668_);
if (v_isShared_667_ == 0)
{
lean_ctor_set_tag(v___x_666_, 0);
lean_ctor_set(v___x_666_, 0, v___x_673_);
v___x_675_ = v___x_666_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
else
{
lean_object* v___x_685_; 
v___x_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_685_, 0, v_init_658_);
return v___x_685_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(lean_object* v_x_686_, lean_object* v_x_687_){
_start:
{
switch(lean_obj_tag(v_x_686_))
{
case 0:
{
if (lean_obj_tag(v_x_687_) == 0)
{
uint8_t v___x_688_; 
v___x_688_ = 1;
return v___x_688_;
}
else
{
uint8_t v___x_689_; 
v___x_689_ = 0;
return v___x_689_;
}
}
case 1:
{
if (lean_obj_tag(v_x_687_) == 1)
{
uint8_t v_b_690_; 
v_b_690_ = lean_ctor_get_uint8(v_x_686_, 0);
if (v_b_690_ == 0)
{
uint8_t v_b_691_; 
v_b_691_ = lean_ctor_get_uint8(v_x_687_, 0);
if (v_b_691_ == 0)
{
uint8_t v___x_692_; 
v___x_692_ = 1;
return v___x_692_;
}
else
{
return v_b_690_;
}
}
else
{
uint8_t v_b_693_; 
v_b_693_ = lean_ctor_get_uint8(v_x_687_, 0);
return v_b_693_;
}
}
else
{
uint8_t v___x_694_; 
v___x_694_ = 0;
return v___x_694_;
}
}
case 2:
{
if (lean_obj_tag(v_x_687_) == 2)
{
lean_object* v_n_695_; lean_object* v_n_696_; uint8_t v___x_697_; 
v_n_695_ = lean_ctor_get(v_x_686_, 0);
v_n_696_ = lean_ctor_get(v_x_687_, 0);
v___x_697_ = l_Lean_instDecidableEqJsonNumber_decEq(v_n_695_, v_n_696_);
return v___x_697_;
}
else
{
uint8_t v___x_698_; 
v___x_698_ = 0;
return v___x_698_;
}
}
case 3:
{
if (lean_obj_tag(v_x_687_) == 3)
{
lean_object* v_s_699_; lean_object* v_s_700_; uint8_t v___x_701_; 
v_s_699_ = lean_ctor_get(v_x_686_, 0);
v_s_700_ = lean_ctor_get(v_x_687_, 0);
v___x_701_ = lean_string_dec_eq(v_s_699_, v_s_700_);
return v___x_701_;
}
else
{
uint8_t v___x_702_; 
v___x_702_ = 0;
return v___x_702_;
}
}
case 4:
{
if (lean_obj_tag(v_x_687_) == 4)
{
lean_object* v_elems_703_; lean_object* v_elems_704_; lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
v_elems_703_ = lean_ctor_get(v_x_686_, 0);
v_elems_704_ = lean_ctor_get(v_x_687_, 0);
v___x_705_ = lean_array_get_size(v_elems_703_);
v___x_706_ = lean_array_get_size(v_elems_704_);
v___x_707_ = lean_nat_dec_eq(v___x_705_, v___x_706_);
if (v___x_707_ == 0)
{
return v___x_707_;
}
else
{
uint8_t v___x_708_; 
v___x_708_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(v_elems_703_, v_elems_704_, v___x_705_);
return v___x_708_;
}
}
else
{
uint8_t v___x_709_; 
v___x_709_ = 0;
return v___x_709_;
}
}
default: 
{
if (lean_obj_tag(v_x_687_) == 5)
{
lean_object* v_kvPairs_710_; lean_object* v_kvPairs_711_; lean_object* v___x_712_; lean_object* v_szA_713_; lean_object* v_szB_714_; uint8_t v___x_715_; lean_object* v___y_717_; 
v_kvPairs_710_ = lean_ctor_get(v_x_686_, 0);
v_kvPairs_711_ = lean_ctor_get(v_x_687_, 0);
v___x_712_ = lean_unsigned_to_nat(0u);
v_szA_713_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v___x_712_, v_kvPairs_710_);
v_szB_714_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v___x_712_, v_kvPairs_711_);
v___x_715_ = lean_nat_dec_eq(v_szA_713_, v_szB_714_);
lean_dec(v_szB_714_);
lean_dec(v_szA_713_);
if (v___x_715_ == 0)
{
return v___x_715_;
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v_a_723_; 
v___x_721_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__0));
v___x_722_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_kvPairs_711_, v___x_721_, v_kvPairs_710_);
v_a_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_a_723_);
lean_dec_ref(v___x_722_);
v___y_717_ = v_a_723_;
goto v___jp_716_;
}
v___jp_716_:
{
lean_object* v_fst_718_; 
v_fst_718_ = lean_ctor_get(v___y_717_, 0);
lean_inc(v_fst_718_);
lean_dec_ref(v___y_717_);
if (lean_obj_tag(v_fst_718_) == 0)
{
return v___x_715_;
}
else
{
lean_object* v_val_719_; uint8_t v___x_720_; 
v_val_719_ = lean_ctor_get(v_fst_718_, 0);
lean_inc(v_val_719_);
lean_dec_ref_known(v_fst_718_, 1);
v___x_720_ = lean_unbox(v_val_719_);
lean_dec(v_val_719_);
return v___x_720_;
}
}
}
else
{
uint8_t v___x_724_; 
v___x_724_ = 0;
return v___x_724_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(lean_object* v_xs_725_, lean_object* v_ys_726_, lean_object* v_x_727_){
_start:
{
lean_object* v_zero_728_; uint8_t v_isZero_729_; 
v_zero_728_ = lean_unsigned_to_nat(0u);
v_isZero_729_ = lean_nat_dec_eq(v_x_727_, v_zero_728_);
if (v_isZero_729_ == 1)
{
lean_dec(v_x_727_);
return v_isZero_729_;
}
else
{
lean_object* v_one_730_; lean_object* v_n_731_; lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v_one_730_ = lean_unsigned_to_nat(1u);
v_n_731_ = lean_nat_sub(v_x_727_, v_one_730_);
lean_dec(v_x_727_);
v___x_732_ = lean_array_fget_borrowed(v_xs_725_, v_n_731_);
v___x_733_ = lean_array_fget_borrowed(v_ys_726_, v_n_731_);
v___x_734_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v___x_732_, v___x_733_);
if (v___x_734_ == 0)
{
lean_dec(v_n_731_);
return v___x_734_;
}
else
{
v_x_727_ = v_n_731_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg___boxed(lean_object* v_xs_736_, lean_object* v_ys_737_, lean_object* v_x_738_){
_start:
{
uint8_t v_res_739_; lean_object* v_r_740_; 
v_res_739_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(v_xs_736_, v_ys_737_, v_x_738_);
lean_dec_ref(v_ys_737_);
lean_dec_ref(v_xs_736_);
v_r_740_ = lean_box(v_res_739_);
return v_r_740_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___boxed(lean_object* v_kvPairs_741_, lean_object* v_init_742_, lean_object* v_x_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_kvPairs_741_, v_init_742_, v_x_743_);
lean_dec(v_x_743_);
lean_dec(v_kvPairs_741_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___boxed(lean_object* v_x_745_, lean_object* v_x_746_){
_start:
{
uint8_t v_res_747_; lean_object* v_r_748_; 
v_res_747_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_x_745_, v_x_746_);
lean_dec(v_x_746_);
lean_dec(v_x_745_);
v_r_748_ = lean_box(v_res_747_);
return v_r_748_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0(lean_object* v_xs_749_, lean_object* v_ys_750_, lean_object* v_hsz_751_, lean_object* v_x_752_, lean_object* v_x_753_){
_start:
{
uint8_t v___x_754_; 
v___x_754_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(v_xs_749_, v_ys_750_, v_x_752_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___boxed(lean_object* v_xs_755_, lean_object* v_ys_756_, lean_object* v_hsz_757_, lean_object* v_x_758_, lean_object* v_x_759_){
_start:
{
uint8_t v_res_760_; lean_object* v_r_761_; 
v_res_760_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0(v_xs_755_, v_ys_756_, v_hsz_757_, v_x_758_, v_x_759_);
lean_dec_ref(v_ys_756_);
lean_dec_ref(v_xs_755_);
v_r_761_ = lean_box(v_res_760_);
return v_r_761_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1(lean_object* v_init_762_, lean_object* v_t_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_762_, v_t_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___boxed(lean_object* v_init_765_, lean_object* v_t_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1(v_init_765_, v_t_766_);
lean_dec(v_t_766_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2(lean_object* v_00_u03b4_768_, lean_object* v_t_769_, lean_object* v_k_770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_t_769_, v_k_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___boxed(lean_object* v_00_u03b4_772_, lean_object* v_t_773_, lean_object* v_k_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2(v_00_u03b4_772_, v_t_773_, v_k_774_);
lean_dec_ref(v_k_774_);
lean_dec(v_t_773_);
return v_res_775_;
}
}
LEAN_EXPORT uint8_t l_Lean_Json_instBEq___private__1(lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
uint8_t v___x_778_; 
v___x_778_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_a_776_, v_a_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instBEq___private__1___boxed(lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
uint8_t v_res_781_; lean_object* v_r_782_; 
v_res_781_ = l_Lean_Json_instBEq___private__1(v_a_779_, v_a_780_);
lean_dec(v_a_780_);
lean_dec(v_a_779_);
v_r_782_ = lean_box(v_res_781_);
return v_r_782_;
}
}
static uint64_t _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__0(void){
_start:
{
uint64_t v___x_785_; uint64_t v___x_786_; 
v___x_785_ = 13ULL;
v___x_786_ = lean_uint64_mix_hash(v___x_785_, v___x_785_);
return v___x_786_;
}
}
static uint64_t _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__1(void){
_start:
{
uint64_t v___x_787_; uint64_t v___x_788_; uint64_t v___x_789_; 
v___x_787_ = 11ULL;
v___x_788_ = 13ULL;
v___x_789_ = lean_uint64_mix_hash(v___x_788_, v___x_787_);
return v___x_789_;
}
}
static uint64_t _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2(void){
_start:
{
uint64_t v___x_790_; uint64_t v___x_791_; uint64_t v___x_792_; 
v___x_790_ = 7ULL;
v___x_791_ = 23ULL;
v___x_792_ = lean_uint64_mix_hash(v___x_791_, v___x_790_);
return v___x_792_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(lean_object* v_as_793_, size_t v_i_794_, size_t v_stop_795_, uint64_t v_b_796_){
_start:
{
uint8_t v___x_797_; 
v___x_797_ = lean_usize_dec_eq(v_i_794_, v_stop_795_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; uint64_t v___x_799_; uint64_t v___x_800_; size_t v___x_801_; size_t v___x_802_; 
v___x_798_ = lean_array_uget_borrowed(v_as_793_, v_i_794_);
v___x_799_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v___x_798_);
v___x_800_ = lean_uint64_mix_hash(v_b_796_, v___x_799_);
v___x_801_ = ((size_t)1ULL);
v___x_802_ = lean_usize_add(v_i_794_, v___x_801_);
v_i_794_ = v___x_802_;
v_b_796_ = v___x_800_;
goto _start;
}
else
{
return v_b_796_;
}
}
}
LEAN_EXPORT uint64_t l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(lean_object* v_x_804_){
_start:
{
switch(lean_obj_tag(v_x_804_))
{
case 0:
{
uint64_t v___x_805_; 
v___x_805_ = 11ULL;
return v___x_805_;
}
case 1:
{
uint8_t v_b_806_; 
v_b_806_ = lean_ctor_get_uint8(v_x_804_, 0);
if (v_b_806_ == 0)
{
uint64_t v___x_807_; 
v___x_807_ = lean_uint64_once(&l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__0, &l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__0_once, _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__0);
return v___x_807_;
}
else
{
uint64_t v___x_808_; 
v___x_808_ = lean_uint64_once(&l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__1, &l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__1_once, _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__1);
return v___x_808_;
}
}
case 2:
{
lean_object* v_n_809_; uint64_t v___x_810_; uint64_t v___x_811_; uint64_t v___x_812_; 
v_n_809_ = lean_ctor_get(v_x_804_, 0);
v___x_810_ = 17ULL;
v___x_811_ = l_Lean_instHashableJsonNumber_hash(v_n_809_);
v___x_812_ = lean_uint64_mix_hash(v___x_810_, v___x_811_);
return v___x_812_;
}
case 3:
{
lean_object* v_s_813_; uint64_t v___x_814_; uint64_t v___x_815_; uint64_t v___x_816_; 
v_s_813_ = lean_ctor_get(v_x_804_, 0);
v___x_814_ = 19ULL;
v___x_815_ = lean_string_hash(v_s_813_);
v___x_816_ = lean_uint64_mix_hash(v___x_814_, v___x_815_);
return v___x_816_;
}
case 4:
{
lean_object* v_elems_817_; uint64_t v___x_818_; uint64_t v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; uint8_t v___x_822_; 
v_elems_817_ = lean_ctor_get(v_x_804_, 0);
v___x_818_ = 23ULL;
v___x_819_ = 7ULL;
v___x_820_ = lean_unsigned_to_nat(0u);
v___x_821_ = lean_array_get_size(v_elems_817_);
v___x_822_ = lean_nat_dec_lt(v___x_820_, v___x_821_);
if (v___x_822_ == 0)
{
uint64_t v___x_823_; 
v___x_823_ = lean_uint64_once(&l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2, &l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2_once, _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2);
return v___x_823_;
}
else
{
uint8_t v___x_824_; 
v___x_824_ = lean_nat_dec_le(v___x_821_, v___x_821_);
if (v___x_824_ == 0)
{
if (v___x_822_ == 0)
{
uint64_t v___x_825_; 
v___x_825_ = lean_uint64_once(&l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2, &l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2_once, _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2);
return v___x_825_;
}
else
{
size_t v___x_826_; size_t v___x_827_; uint64_t v___x_828_; uint64_t v___x_829_; 
v___x_826_ = ((size_t)0ULL);
v___x_827_ = lean_usize_of_nat(v___x_821_);
v___x_828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_elems_817_, v___x_826_, v___x_827_, v___x_819_);
v___x_829_ = lean_uint64_mix_hash(v___x_818_, v___x_828_);
return v___x_829_;
}
}
else
{
size_t v___x_830_; size_t v___x_831_; uint64_t v___x_832_; uint64_t v___x_833_; 
v___x_830_ = ((size_t)0ULL);
v___x_831_ = lean_usize_of_nat(v___x_821_);
v___x_832_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_elems_817_, v___x_830_, v___x_831_, v___x_819_);
v___x_833_ = lean_uint64_mix_hash(v___x_818_, v___x_832_);
return v___x_833_;
}
}
}
default: 
{
lean_object* v_kvPairs_834_; uint64_t v___x_835_; uint64_t v___x_836_; uint64_t v___x_837_; uint64_t v___x_838_; 
v_kvPairs_834_ = lean_ctor_get(v_x_804_, 0);
v___x_835_ = 29ULL;
v___x_836_ = 7ULL;
v___x_837_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v___x_836_, v_kvPairs_834_);
v___x_838_ = lean_uint64_mix_hash(v___x_835_, v___x_837_);
return v___x_838_;
}
}
}
}
LEAN_EXPORT uint64_t l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(uint64_t v_init_839_, lean_object* v_x_840_){
_start:
{
if (lean_obj_tag(v_x_840_) == 0)
{
lean_object* v_k_841_; lean_object* v_v_842_; lean_object* v_l_843_; lean_object* v_r_844_; uint64_t v___x_845_; uint64_t v___x_846_; uint64_t v___x_847_; uint64_t v___x_848_; uint64_t v___x_849_; 
v_k_841_ = lean_ctor_get(v_x_840_, 1);
v_v_842_ = lean_ctor_get(v_x_840_, 2);
v_l_843_ = lean_ctor_get(v_x_840_, 3);
v_r_844_ = lean_ctor_get(v_x_840_, 4);
v___x_845_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_839_, v_l_843_);
v___x_846_ = lean_string_hash(v_k_841_);
v___x_847_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_v_842_);
v___x_848_ = lean_uint64_mix_hash(v___x_846_, v___x_847_);
v___x_849_ = lean_uint64_mix_hash(v___x_845_, v___x_848_);
v_init_839_ = v___x_849_;
v_x_840_ = v_r_844_;
goto _start;
}
else
{
return v_init_839_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1___boxed(lean_object* v_init_851_, lean_object* v_x_852_){
_start:
{
uint64_t v_init_boxed_853_; uint64_t v_res_854_; lean_object* v_r_855_; 
v_init_boxed_853_ = lean_unbox_uint64(v_init_851_);
lean_dec_ref(v_init_851_);
v_res_854_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_boxed_853_, v_x_852_);
lean_dec(v_x_852_);
v_r_855_ = lean_box_uint64(v_res_854_);
return v_r_855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0___boxed(lean_object* v_as_856_, lean_object* v_i_857_, lean_object* v_stop_858_, lean_object* v_b_859_){
_start:
{
size_t v_i_boxed_860_; size_t v_stop_boxed_861_; uint64_t v_b_boxed_862_; uint64_t v_res_863_; lean_object* v_r_864_; 
v_i_boxed_860_ = lean_unbox_usize(v_i_857_);
lean_dec(v_i_857_);
v_stop_boxed_861_ = lean_unbox_usize(v_stop_858_);
lean_dec(v_stop_858_);
v_b_boxed_862_ = lean_unbox_uint64(v_b_859_);
lean_dec_ref(v_b_859_);
v_res_863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_as_856_, v_i_boxed_860_, v_stop_boxed_861_, v_b_boxed_862_);
lean_dec_ref(v_as_856_);
v_r_864_ = lean_box_uint64(v_res_863_);
return v_r_864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___boxed(lean_object* v_x_865_){
_start:
{
uint64_t v_res_866_; lean_object* v_r_867_; 
v_res_866_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_x_865_);
lean_dec(v_x_865_);
v_r_867_ = lean_box_uint64(v_res_866_);
return v_r_867_;
}
}
LEAN_EXPORT uint64_t l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1(uint64_t v_init_868_, lean_object* v_t_869_){
_start:
{
uint64_t v___x_870_; 
v___x_870_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_868_, v_t_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1___boxed(lean_object* v_init_871_, lean_object* v_t_872_){
_start:
{
uint64_t v_init_boxed_873_; uint64_t v_res_874_; lean_object* v_r_875_; 
v_init_boxed_873_ = lean_unbox_uint64(v_init_871_);
lean_dec_ref(v_init_871_);
v_res_874_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1(v_init_boxed_873_, v_t_872_);
lean_dec(v_t_872_);
v_r_875_ = lean_box_uint64(v_res_874_);
return v_r_875_;
}
}
LEAN_EXPORT uint64_t l_Lean_Json_instHashable___private__1(lean_object* v_a_876_){
_start:
{
uint64_t v___x_877_; 
v___x_877_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_a_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instHashable___private__1___boxed(lean_object* v_a_878_){
_start:
{
uint64_t v_res_879_; lean_object* v_r_880_; 
v_res_879_ = l_Lean_Json_instHashable___private__1(v_a_878_);
lean_dec(v_a_878_);
v_r_880_ = lean_box_uint64(v_res_879_);
return v_r_880_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(lean_object* v_k_883_, lean_object* v_v_884_, lean_object* v_t_885_){
_start:
{
if (lean_obj_tag(v_t_885_) == 0)
{
lean_object* v_size_886_; lean_object* v_k_887_; lean_object* v_v_888_; lean_object* v_l_889_; lean_object* v_r_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_1170_; 
v_size_886_ = lean_ctor_get(v_t_885_, 0);
v_k_887_ = lean_ctor_get(v_t_885_, 1);
v_v_888_ = lean_ctor_get(v_t_885_, 2);
v_l_889_ = lean_ctor_get(v_t_885_, 3);
v_r_890_ = lean_ctor_get(v_t_885_, 4);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_t_885_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_892_ = v_t_885_;
v_isShared_893_ = v_isSharedCheck_1170_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_r_890_);
lean_inc(v_l_889_);
lean_inc(v_v_888_);
lean_inc(v_k_887_);
lean_inc(v_size_886_);
lean_dec(v_t_885_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_1170_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
uint8_t v___x_894_; 
v___x_894_ = lean_string_compare(v_k_883_, v_k_887_);
switch(v___x_894_)
{
case 0:
{
lean_object* v_impl_895_; lean_object* v___x_896_; 
lean_dec(v_size_886_);
v_impl_895_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_883_, v_v_884_, v_l_889_);
v___x_896_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_890_) == 0)
{
lean_object* v_size_897_; lean_object* v_size_898_; lean_object* v_k_899_; lean_object* v_v_900_; lean_object* v_l_901_; lean_object* v_r_902_; lean_object* v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v_size_897_ = lean_ctor_get(v_r_890_, 0);
v_size_898_ = lean_ctor_get(v_impl_895_, 0);
lean_inc(v_size_898_);
v_k_899_ = lean_ctor_get(v_impl_895_, 1);
lean_inc(v_k_899_);
v_v_900_ = lean_ctor_get(v_impl_895_, 2);
lean_inc(v_v_900_);
v_l_901_ = lean_ctor_get(v_impl_895_, 3);
lean_inc(v_l_901_);
v_r_902_ = lean_ctor_get(v_impl_895_, 4);
lean_inc(v_r_902_);
v___x_903_ = lean_unsigned_to_nat(3u);
v___x_904_ = lean_nat_mul(v___x_903_, v_size_897_);
v___x_905_ = lean_nat_dec_lt(v___x_904_, v_size_898_);
lean_dec(v___x_904_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_909_; 
lean_dec(v_r_902_);
lean_dec(v_l_901_);
lean_dec(v_v_900_);
lean_dec(v_k_899_);
v___x_906_ = lean_nat_add(v___x_896_, v_size_898_);
lean_dec(v_size_898_);
v___x_907_ = lean_nat_add(v___x_906_, v_size_897_);
lean_dec(v___x_906_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 3, v_impl_895_);
lean_ctor_set(v___x_892_, 0, v___x_907_);
v___x_909_ = v___x_892_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_910_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_910_, 3, v_impl_895_);
lean_ctor_set(v_reuseFailAlloc_910_, 4, v_r_890_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
else
{
lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_976_; 
v_isSharedCheck_976_ = !lean_is_exclusive(v_impl_895_);
if (v_isSharedCheck_976_ == 0)
{
lean_object* v_unused_977_; lean_object* v_unused_978_; lean_object* v_unused_979_; lean_object* v_unused_980_; lean_object* v_unused_981_; 
v_unused_977_ = lean_ctor_get(v_impl_895_, 4);
lean_dec(v_unused_977_);
v_unused_978_ = lean_ctor_get(v_impl_895_, 3);
lean_dec(v_unused_978_);
v_unused_979_ = lean_ctor_get(v_impl_895_, 2);
lean_dec(v_unused_979_);
v_unused_980_ = lean_ctor_get(v_impl_895_, 1);
lean_dec(v_unused_980_);
v_unused_981_ = lean_ctor_get(v_impl_895_, 0);
lean_dec(v_unused_981_);
v___x_912_ = v_impl_895_;
v_isShared_913_ = v_isSharedCheck_976_;
goto v_resetjp_911_;
}
else
{
lean_dec(v_impl_895_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_976_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v_size_914_; lean_object* v_size_915_; lean_object* v_k_916_; lean_object* v_v_917_; lean_object* v_l_918_; lean_object* v_r_919_; lean_object* v___x_920_; lean_object* v___x_921_; uint8_t v___x_922_; 
v_size_914_ = lean_ctor_get(v_l_901_, 0);
v_size_915_ = lean_ctor_get(v_r_902_, 0);
v_k_916_ = lean_ctor_get(v_r_902_, 1);
v_v_917_ = lean_ctor_get(v_r_902_, 2);
v_l_918_ = lean_ctor_get(v_r_902_, 3);
v_r_919_ = lean_ctor_get(v_r_902_, 4);
v___x_920_ = lean_unsigned_to_nat(2u);
v___x_921_ = lean_nat_mul(v___x_920_, v_size_914_);
v___x_922_ = lean_nat_dec_lt(v_size_915_, v___x_921_);
lean_dec(v___x_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_951_; 
lean_inc(v_r_919_);
lean_inc(v_l_918_);
lean_inc(v_v_917_);
lean_inc(v_k_916_);
v_isSharedCheck_951_ = !lean_is_exclusive(v_r_902_);
if (v_isSharedCheck_951_ == 0)
{
lean_object* v_unused_952_; lean_object* v_unused_953_; lean_object* v_unused_954_; lean_object* v_unused_955_; lean_object* v_unused_956_; 
v_unused_952_ = lean_ctor_get(v_r_902_, 4);
lean_dec(v_unused_952_);
v_unused_953_ = lean_ctor_get(v_r_902_, 3);
lean_dec(v_unused_953_);
v_unused_954_ = lean_ctor_get(v_r_902_, 2);
lean_dec(v_unused_954_);
v_unused_955_ = lean_ctor_get(v_r_902_, 1);
lean_dec(v_unused_955_);
v_unused_956_ = lean_ctor_get(v_r_902_, 0);
lean_dec(v_unused_956_);
v___x_924_ = v_r_902_;
v_isShared_925_ = v_isSharedCheck_951_;
goto v_resetjp_923_;
}
else
{
lean_dec(v_r_902_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_951_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___x_939_; lean_object* v___y_941_; 
v___x_926_ = lean_nat_add(v___x_896_, v_size_898_);
lean_dec(v_size_898_);
v___x_927_ = lean_nat_add(v___x_926_, v_size_897_);
lean_dec(v___x_926_);
v___x_939_ = lean_nat_add(v___x_896_, v_size_914_);
if (lean_obj_tag(v_l_918_) == 0)
{
lean_object* v_size_949_; 
v_size_949_ = lean_ctor_get(v_l_918_, 0);
lean_inc(v_size_949_);
v___y_941_ = v_size_949_;
goto v___jp_940_;
}
else
{
lean_object* v___x_950_; 
v___x_950_ = lean_unsigned_to_nat(0u);
v___y_941_ = v___x_950_;
goto v___jp_940_;
}
v___jp_928_:
{
lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_932_ = lean_nat_add(v___y_929_, v___y_931_);
lean_dec(v___y_931_);
lean_dec(v___y_929_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 4, v_r_890_);
lean_ctor_set(v___x_924_, 3, v_r_919_);
lean_ctor_set(v___x_924_, 2, v_v_888_);
lean_ctor_set(v___x_924_, 1, v_k_887_);
lean_ctor_set(v___x_924_, 0, v___x_932_);
v___x_934_ = v___x_924_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_938_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_938_, 3, v_r_919_);
lean_ctor_set(v_reuseFailAlloc_938_, 4, v_r_890_);
v___x_934_ = v_reuseFailAlloc_938_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_936_; 
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 4, v___x_934_);
lean_ctor_set(v___x_912_, 3, v___y_930_);
lean_ctor_set(v___x_912_, 2, v_v_917_);
lean_ctor_set(v___x_912_, 1, v_k_916_);
lean_ctor_set(v___x_912_, 0, v___x_927_);
v___x_936_ = v___x_912_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_927_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v_k_916_);
lean_ctor_set(v_reuseFailAlloc_937_, 2, v_v_917_);
lean_ctor_set(v_reuseFailAlloc_937_, 3, v___y_930_);
lean_ctor_set(v_reuseFailAlloc_937_, 4, v___x_934_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
v___jp_940_:
{
lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_942_ = lean_nat_add(v___x_939_, v___y_941_);
lean_dec(v___y_941_);
lean_dec(v___x_939_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 4, v_l_918_);
lean_ctor_set(v___x_892_, 3, v_l_901_);
lean_ctor_set(v___x_892_, 2, v_v_900_);
lean_ctor_set(v___x_892_, 1, v_k_899_);
lean_ctor_set(v___x_892_, 0, v___x_942_);
v___x_944_ = v___x_892_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_k_899_);
lean_ctor_set(v_reuseFailAlloc_948_, 2, v_v_900_);
lean_ctor_set(v_reuseFailAlloc_948_, 3, v_l_901_);
lean_ctor_set(v_reuseFailAlloc_948_, 4, v_l_918_);
v___x_944_ = v_reuseFailAlloc_948_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_945_; 
v___x_945_ = lean_nat_add(v___x_896_, v_size_897_);
if (lean_obj_tag(v_r_919_) == 0)
{
lean_object* v_size_946_; 
v_size_946_ = lean_ctor_get(v_r_919_, 0);
lean_inc(v_size_946_);
v___y_929_ = v___x_945_;
v___y_930_ = v___x_944_;
v___y_931_ = v_size_946_;
goto v___jp_928_;
}
else
{
lean_object* v___x_947_; 
v___x_947_ = lean_unsigned_to_nat(0u);
v___y_929_ = v___x_945_;
v___y_930_ = v___x_944_;
v___y_931_ = v___x_947_;
goto v___jp_928_;
}
}
}
}
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_962_; 
lean_del_object(v___x_892_);
v___x_957_ = lean_nat_add(v___x_896_, v_size_898_);
lean_dec(v_size_898_);
v___x_958_ = lean_nat_add(v___x_957_, v_size_897_);
lean_dec(v___x_957_);
v___x_959_ = lean_nat_add(v___x_896_, v_size_897_);
v___x_960_ = lean_nat_add(v___x_959_, v_size_915_);
lean_dec(v___x_959_);
lean_inc_ref(v_r_890_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 4, v_r_890_);
lean_ctor_set(v___x_912_, 3, v_r_902_);
lean_ctor_set(v___x_912_, 2, v_v_888_);
lean_ctor_set(v___x_912_, 1, v_k_887_);
lean_ctor_set(v___x_912_, 0, v___x_960_);
v___x_962_ = v___x_912_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_975_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_975_, 3, v_r_902_);
lean_ctor_set(v_reuseFailAlloc_975_, 4, v_r_890_);
v___x_962_ = v_reuseFailAlloc_975_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
v_isSharedCheck_969_ = !lean_is_exclusive(v_r_890_);
if (v_isSharedCheck_969_ == 0)
{
lean_object* v_unused_970_; lean_object* v_unused_971_; lean_object* v_unused_972_; lean_object* v_unused_973_; lean_object* v_unused_974_; 
v_unused_970_ = lean_ctor_get(v_r_890_, 4);
lean_dec(v_unused_970_);
v_unused_971_ = lean_ctor_get(v_r_890_, 3);
lean_dec(v_unused_971_);
v_unused_972_ = lean_ctor_get(v_r_890_, 2);
lean_dec(v_unused_972_);
v_unused_973_ = lean_ctor_get(v_r_890_, 1);
lean_dec(v_unused_973_);
v_unused_974_ = lean_ctor_get(v_r_890_, 0);
lean_dec(v_unused_974_);
v___x_964_ = v_r_890_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_dec(v_r_890_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 4, v___x_962_);
lean_ctor_set(v___x_964_, 3, v_l_901_);
lean_ctor_set(v___x_964_, 2, v_v_900_);
lean_ctor_set(v___x_964_, 1, v_k_899_);
lean_ctor_set(v___x_964_, 0, v___x_958_);
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_958_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v_k_899_);
lean_ctor_set(v_reuseFailAlloc_968_, 2, v_v_900_);
lean_ctor_set(v_reuseFailAlloc_968_, 3, v_l_901_);
lean_ctor_set(v_reuseFailAlloc_968_, 4, v___x_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_982_; 
v_l_982_ = lean_ctor_get(v_impl_895_, 3);
lean_inc(v_l_982_);
if (lean_obj_tag(v_l_982_) == 0)
{
lean_object* v_r_983_; lean_object* v_k_984_; lean_object* v_v_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_996_; 
v_r_983_ = lean_ctor_get(v_impl_895_, 4);
v_k_984_ = lean_ctor_get(v_impl_895_, 1);
v_v_985_ = lean_ctor_get(v_impl_895_, 2);
v_isSharedCheck_996_ = !lean_is_exclusive(v_impl_895_);
if (v_isSharedCheck_996_ == 0)
{
lean_object* v_unused_997_; lean_object* v_unused_998_; 
v_unused_997_ = lean_ctor_get(v_impl_895_, 3);
lean_dec(v_unused_997_);
v_unused_998_ = lean_ctor_get(v_impl_895_, 0);
lean_dec(v_unused_998_);
v___x_987_ = v_impl_895_;
v_isShared_988_ = v_isSharedCheck_996_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_r_983_);
lean_inc(v_v_985_);
lean_inc(v_k_984_);
lean_dec(v_impl_895_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_996_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_989_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_983_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 3, v_r_983_);
lean_ctor_set(v___x_987_, 2, v_v_888_);
lean_ctor_set(v___x_987_, 1, v_k_887_);
lean_ctor_set(v___x_987_, 0, v___x_896_);
v___x_991_ = v___x_987_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_995_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_995_, 3, v_r_983_);
lean_ctor_set(v_reuseFailAlloc_995_, 4, v_r_983_);
v___x_991_ = v_reuseFailAlloc_995_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_993_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 4, v___x_991_);
lean_ctor_set(v___x_892_, 3, v_l_982_);
lean_ctor_set(v___x_892_, 2, v_v_985_);
lean_ctor_set(v___x_892_, 1, v_k_984_);
lean_ctor_set(v___x_892_, 0, v___x_989_);
v___x_993_ = v___x_892_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_989_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_k_984_);
lean_ctor_set(v_reuseFailAlloc_994_, 2, v_v_985_);
lean_ctor_set(v_reuseFailAlloc_994_, 3, v_l_982_);
lean_ctor_set(v_reuseFailAlloc_994_, 4, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
else
{
lean_object* v_r_999_; 
v_r_999_ = lean_ctor_get(v_impl_895_, 4);
lean_inc(v_r_999_);
if (lean_obj_tag(v_r_999_) == 0)
{
lean_object* v_k_1000_; lean_object* v_v_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1024_; 
v_k_1000_ = lean_ctor_get(v_impl_895_, 1);
v_v_1001_ = lean_ctor_get(v_impl_895_, 2);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_impl_895_);
if (v_isSharedCheck_1024_ == 0)
{
lean_object* v_unused_1025_; lean_object* v_unused_1026_; lean_object* v_unused_1027_; 
v_unused_1025_ = lean_ctor_get(v_impl_895_, 4);
lean_dec(v_unused_1025_);
v_unused_1026_ = lean_ctor_get(v_impl_895_, 3);
lean_dec(v_unused_1026_);
v_unused_1027_ = lean_ctor_get(v_impl_895_, 0);
lean_dec(v_unused_1027_);
v___x_1003_ = v_impl_895_;
v_isShared_1004_ = v_isSharedCheck_1024_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_v_1001_);
lean_inc(v_k_1000_);
lean_dec(v_impl_895_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1024_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v_k_1005_; lean_object* v_v_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1020_; 
v_k_1005_ = lean_ctor_get(v_r_999_, 1);
v_v_1006_ = lean_ctor_get(v_r_999_, 2);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_r_999_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; lean_object* v_unused_1022_; lean_object* v_unused_1023_; 
v_unused_1021_ = lean_ctor_get(v_r_999_, 4);
lean_dec(v_unused_1021_);
v_unused_1022_ = lean_ctor_get(v_r_999_, 3);
lean_dec(v_unused_1022_);
v_unused_1023_ = lean_ctor_get(v_r_999_, 0);
lean_dec(v_unused_1023_);
v___x_1008_ = v_r_999_;
v_isShared_1009_ = v_isSharedCheck_1020_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_v_1006_);
lean_inc(v_k_1005_);
lean_dec(v_r_999_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1020_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1010_ = lean_unsigned_to_nat(3u);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 4, v_l_982_);
lean_ctor_set(v___x_1008_, 3, v_l_982_);
lean_ctor_set(v___x_1008_, 2, v_v_1001_);
lean_ctor_set(v___x_1008_, 1, v_k_1000_);
lean_ctor_set(v___x_1008_, 0, v___x_896_);
v___x_1012_ = v___x_1008_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_k_1000_);
lean_ctor_set(v_reuseFailAlloc_1019_, 2, v_v_1001_);
lean_ctor_set(v_reuseFailAlloc_1019_, 3, v_l_982_);
lean_ctor_set(v_reuseFailAlloc_1019_, 4, v_l_982_);
v___x_1012_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1014_; 
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 4, v_l_982_);
lean_ctor_set(v___x_1003_, 2, v_v_888_);
lean_ctor_set(v___x_1003_, 1, v_k_887_);
lean_ctor_set(v___x_1003_, 0, v___x_896_);
v___x_1014_ = v___x_1003_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_1018_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_1018_, 3, v_l_982_);
lean_ctor_set(v_reuseFailAlloc_1018_, 4, v_l_982_);
v___x_1014_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1016_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 4, v___x_1014_);
lean_ctor_set(v___x_892_, 3, v___x_1012_);
lean_ctor_set(v___x_892_, 2, v_v_1006_);
lean_ctor_set(v___x_892_, 1, v_k_1005_);
lean_ctor_set(v___x_892_, 0, v___x_1010_);
v___x_1016_ = v___x_892_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_k_1005_);
lean_ctor_set(v_reuseFailAlloc_1017_, 2, v_v_1006_);
lean_ctor_set(v_reuseFailAlloc_1017_, 3, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1017_, 4, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
}
else
{
lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1028_ = lean_unsigned_to_nat(2u);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 4, v_r_999_);
lean_ctor_set(v___x_892_, 3, v_impl_895_);
lean_ctor_set(v___x_892_, 0, v___x_1028_);
v___x_1030_ = v___x_892_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1028_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_1031_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_1031_, 3, v_impl_895_);
lean_ctor_set(v_reuseFailAlloc_1031_, 4, v_r_999_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1033_; 
lean_dec(v_v_888_);
lean_dec(v_k_887_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 2, v_v_884_);
lean_ctor_set(v___x_892_, 1, v_k_883_);
v___x_1033_ = v___x_892_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_size_886_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v_k_883_);
lean_ctor_set(v_reuseFailAlloc_1034_, 2, v_v_884_);
lean_ctor_set(v_reuseFailAlloc_1034_, 3, v_l_889_);
lean_ctor_set(v_reuseFailAlloc_1034_, 4, v_r_890_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
default: 
{
lean_object* v_impl_1035_; lean_object* v___x_1036_; 
lean_dec(v_size_886_);
v_impl_1035_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_883_, v_v_884_, v_r_890_);
v___x_1036_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_889_) == 0)
{
lean_object* v_size_1037_; lean_object* v_size_1038_; lean_object* v_k_1039_; lean_object* v_v_1040_; lean_object* v_l_1041_; lean_object* v_r_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v_size_1037_ = lean_ctor_get(v_l_889_, 0);
v_size_1038_ = lean_ctor_get(v_impl_1035_, 0);
lean_inc(v_size_1038_);
v_k_1039_ = lean_ctor_get(v_impl_1035_, 1);
lean_inc(v_k_1039_);
v_v_1040_ = lean_ctor_get(v_impl_1035_, 2);
lean_inc(v_v_1040_);
v_l_1041_ = lean_ctor_get(v_impl_1035_, 3);
lean_inc(v_l_1041_);
v_r_1042_ = lean_ctor_get(v_impl_1035_, 4);
lean_inc(v_r_1042_);
v___x_1043_ = lean_unsigned_to_nat(3u);
v___x_1044_ = lean_nat_mul(v___x_1043_, v_size_1037_);
v___x_1045_ = lean_nat_dec_lt(v___x_1044_, v_size_1038_);
lean_dec(v___x_1044_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1049_; 
lean_dec(v_r_1042_);
lean_dec(v_l_1041_);
lean_dec(v_v_1040_);
lean_dec(v_k_1039_);
v___x_1046_ = lean_nat_add(v___x_1036_, v_size_1037_);
v___x_1047_ = lean_nat_add(v___x_1046_, v_size_1038_);
lean_dec(v_size_1038_);
lean_dec(v___x_1046_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 4, v_impl_1035_);
lean_ctor_set(v___x_892_, 0, v___x_1047_);
v___x_1049_ = v___x_892_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_1050_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_1050_, 3, v_l_889_);
lean_ctor_set(v_reuseFailAlloc_1050_, 4, v_impl_1035_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
else
{
lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1114_; 
v_isSharedCheck_1114_ = !lean_is_exclusive(v_impl_1035_);
if (v_isSharedCheck_1114_ == 0)
{
lean_object* v_unused_1115_; lean_object* v_unused_1116_; lean_object* v_unused_1117_; lean_object* v_unused_1118_; lean_object* v_unused_1119_; 
v_unused_1115_ = lean_ctor_get(v_impl_1035_, 4);
lean_dec(v_unused_1115_);
v_unused_1116_ = lean_ctor_get(v_impl_1035_, 3);
lean_dec(v_unused_1116_);
v_unused_1117_ = lean_ctor_get(v_impl_1035_, 2);
lean_dec(v_unused_1117_);
v_unused_1118_ = lean_ctor_get(v_impl_1035_, 1);
lean_dec(v_unused_1118_);
v_unused_1119_ = lean_ctor_get(v_impl_1035_, 0);
lean_dec(v_unused_1119_);
v___x_1052_ = v_impl_1035_;
v_isShared_1053_ = v_isSharedCheck_1114_;
goto v_resetjp_1051_;
}
else
{
lean_dec(v_impl_1035_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1114_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v_size_1054_; lean_object* v_k_1055_; lean_object* v_v_1056_; lean_object* v_l_1057_; lean_object* v_r_1058_; lean_object* v_size_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
v_size_1054_ = lean_ctor_get(v_l_1041_, 0);
v_k_1055_ = lean_ctor_get(v_l_1041_, 1);
v_v_1056_ = lean_ctor_get(v_l_1041_, 2);
v_l_1057_ = lean_ctor_get(v_l_1041_, 3);
v_r_1058_ = lean_ctor_get(v_l_1041_, 4);
v_size_1059_ = lean_ctor_get(v_r_1042_, 0);
v___x_1060_ = lean_unsigned_to_nat(2u);
v___x_1061_ = lean_nat_mul(v___x_1060_, v_size_1059_);
v___x_1062_ = lean_nat_dec_lt(v_size_1054_, v___x_1061_);
lean_dec(v___x_1061_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1090_; 
lean_inc(v_r_1058_);
lean_inc(v_l_1057_);
lean_inc(v_v_1056_);
lean_inc(v_k_1055_);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_l_1041_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; lean_object* v_unused_1092_; lean_object* v_unused_1093_; lean_object* v_unused_1094_; lean_object* v_unused_1095_; 
v_unused_1091_ = lean_ctor_get(v_l_1041_, 4);
lean_dec(v_unused_1091_);
v_unused_1092_ = lean_ctor_get(v_l_1041_, 3);
lean_dec(v_unused_1092_);
v_unused_1093_ = lean_ctor_get(v_l_1041_, 2);
lean_dec(v_unused_1093_);
v_unused_1094_ = lean_ctor_get(v_l_1041_, 1);
lean_dec(v_unused_1094_);
v_unused_1095_ = lean_ctor_get(v_l_1041_, 0);
lean_dec(v_unused_1095_);
v___x_1064_ = v_l_1041_;
v_isShared_1065_ = v_isSharedCheck_1090_;
goto v_resetjp_1063_;
}
else
{
lean_dec(v_l_1041_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1090_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1080_; 
v___x_1066_ = lean_nat_add(v___x_1036_, v_size_1037_);
v___x_1067_ = lean_nat_add(v___x_1066_, v_size_1038_);
lean_dec(v_size_1038_);
if (lean_obj_tag(v_l_1057_) == 0)
{
lean_object* v_size_1088_; 
v_size_1088_ = lean_ctor_get(v_l_1057_, 0);
lean_inc(v_size_1088_);
v___y_1080_ = v_size_1088_;
goto v___jp_1079_;
}
else
{
lean_object* v___x_1089_; 
v___x_1089_ = lean_unsigned_to_nat(0u);
v___y_1080_ = v___x_1089_;
goto v___jp_1079_;
}
v___jp_1068_:
{
lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1072_ = lean_nat_add(v___y_1069_, v___y_1071_);
lean_dec(v___y_1071_);
lean_dec(v___y_1069_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 4, v_r_1042_);
lean_ctor_set(v___x_1064_, 3, v_r_1058_);
lean_ctor_set(v___x_1064_, 2, v_v_1040_);
lean_ctor_set(v___x_1064_, 1, v_k_1039_);
lean_ctor_set(v___x_1064_, 0, v___x_1072_);
v___x_1074_ = v___x_1064_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_k_1039_);
lean_ctor_set(v_reuseFailAlloc_1078_, 2, v_v_1040_);
lean_ctor_set(v_reuseFailAlloc_1078_, 3, v_r_1058_);
lean_ctor_set(v_reuseFailAlloc_1078_, 4, v_r_1042_);
v___x_1074_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1076_; 
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 4, v___x_1074_);
lean_ctor_set(v___x_1052_, 3, v___y_1070_);
lean_ctor_set(v___x_1052_, 2, v_v_1056_);
lean_ctor_set(v___x_1052_, 1, v_k_1055_);
lean_ctor_set(v___x_1052_, 0, v___x_1067_);
v___x_1076_ = v___x_1052_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1067_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v_k_1055_);
lean_ctor_set(v_reuseFailAlloc_1077_, 2, v_v_1056_);
lean_ctor_set(v_reuseFailAlloc_1077_, 3, v___y_1070_);
lean_ctor_set(v_reuseFailAlloc_1077_, 4, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
v___jp_1079_:
{
lean_object* v___x_1081_; lean_object* v___x_1083_; 
v___x_1081_ = lean_nat_add(v___x_1066_, v___y_1080_);
lean_dec(v___y_1080_);
lean_dec(v___x_1066_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 4, v_l_1057_);
lean_ctor_set(v___x_892_, 0, v___x_1081_);
v___x_1083_ = v___x_892_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_1087_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_1087_, 3, v_l_889_);
lean_ctor_set(v_reuseFailAlloc_1087_, 4, v_l_1057_);
v___x_1083_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1084_; 
v___x_1084_ = lean_nat_add(v___x_1036_, v_size_1059_);
if (lean_obj_tag(v_r_1058_) == 0)
{
lean_object* v_size_1085_; 
v_size_1085_ = lean_ctor_get(v_r_1058_, 0);
lean_inc(v_size_1085_);
v___y_1069_ = v___x_1084_;
v___y_1070_ = v___x_1083_;
v___y_1071_ = v_size_1085_;
goto v___jp_1068_;
}
else
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_unsigned_to_nat(0u);
v___y_1069_ = v___x_1084_;
v___y_1070_ = v___x_1083_;
v___y_1071_ = v___x_1086_;
goto v___jp_1068_;
}
}
}
}
}
else
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1100_; 
lean_del_object(v___x_892_);
v___x_1096_ = lean_nat_add(v___x_1036_, v_size_1037_);
v___x_1097_ = lean_nat_add(v___x_1096_, v_size_1038_);
lean_dec(v_size_1038_);
v___x_1098_ = lean_nat_add(v___x_1096_, v_size_1054_);
lean_dec(v___x_1096_);
lean_inc_ref(v_l_889_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 4, v_l_1041_);
lean_ctor_set(v___x_1052_, 3, v_l_889_);
lean_ctor_set(v___x_1052_, 2, v_v_888_);
lean_ctor_set(v___x_1052_, 1, v_k_887_);
lean_ctor_set(v___x_1052_, 0, v___x_1098_);
v___x_1100_ = v___x_1052_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1098_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_1113_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_1113_, 3, v_l_889_);
lean_ctor_set(v_reuseFailAlloc_1113_, 4, v_l_1041_);
v___x_1100_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
v_isSharedCheck_1107_ = !lean_is_exclusive(v_l_889_);
if (v_isSharedCheck_1107_ == 0)
{
lean_object* v_unused_1108_; lean_object* v_unused_1109_; lean_object* v_unused_1110_; lean_object* v_unused_1111_; lean_object* v_unused_1112_; 
v_unused_1108_ = lean_ctor_get(v_l_889_, 4);
lean_dec(v_unused_1108_);
v_unused_1109_ = lean_ctor_get(v_l_889_, 3);
lean_dec(v_unused_1109_);
v_unused_1110_ = lean_ctor_get(v_l_889_, 2);
lean_dec(v_unused_1110_);
v_unused_1111_ = lean_ctor_get(v_l_889_, 1);
lean_dec(v_unused_1111_);
v_unused_1112_ = lean_ctor_get(v_l_889_, 0);
lean_dec(v_unused_1112_);
v___x_1102_ = v_l_889_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_dec(v_l_889_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 4, v_r_1042_);
lean_ctor_set(v___x_1102_, 3, v___x_1100_);
lean_ctor_set(v___x_1102_, 2, v_v_1040_);
lean_ctor_set(v___x_1102_, 1, v_k_1039_);
lean_ctor_set(v___x_1102_, 0, v___x_1097_);
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1097_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_k_1039_);
lean_ctor_set(v_reuseFailAlloc_1106_, 2, v_v_1040_);
lean_ctor_set(v_reuseFailAlloc_1106_, 3, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1106_, 4, v_r_1042_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1120_; 
v_l_1120_ = lean_ctor_get(v_impl_1035_, 3);
lean_inc(v_l_1120_);
if (lean_obj_tag(v_l_1120_) == 0)
{
lean_object* v_r_1121_; lean_object* v_k_1122_; lean_object* v_v_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1146_; 
v_r_1121_ = lean_ctor_get(v_impl_1035_, 4);
v_k_1122_ = lean_ctor_get(v_impl_1035_, 1);
v_v_1123_ = lean_ctor_get(v_impl_1035_, 2);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_impl_1035_);
if (v_isSharedCheck_1146_ == 0)
{
lean_object* v_unused_1147_; lean_object* v_unused_1148_; 
v_unused_1147_ = lean_ctor_get(v_impl_1035_, 3);
lean_dec(v_unused_1147_);
v_unused_1148_ = lean_ctor_get(v_impl_1035_, 0);
lean_dec(v_unused_1148_);
v___x_1125_ = v_impl_1035_;
v_isShared_1126_ = v_isSharedCheck_1146_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_r_1121_);
lean_inc(v_v_1123_);
lean_inc(v_k_1122_);
lean_dec(v_impl_1035_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1146_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v_k_1127_; lean_object* v_v_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1142_; 
v_k_1127_ = lean_ctor_get(v_l_1120_, 1);
v_v_1128_ = lean_ctor_get(v_l_1120_, 2);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_l_1120_);
if (v_isSharedCheck_1142_ == 0)
{
lean_object* v_unused_1143_; lean_object* v_unused_1144_; lean_object* v_unused_1145_; 
v_unused_1143_ = lean_ctor_get(v_l_1120_, 4);
lean_dec(v_unused_1143_);
v_unused_1144_ = lean_ctor_get(v_l_1120_, 3);
lean_dec(v_unused_1144_);
v_unused_1145_ = lean_ctor_get(v_l_1120_, 0);
lean_dec(v_unused_1145_);
v___x_1130_ = v_l_1120_;
v_isShared_1131_ = v_isSharedCheck_1142_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_v_1128_);
lean_inc(v_k_1127_);
lean_dec(v_l_1120_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1142_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1132_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1121_, 2);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 4, v_r_1121_);
lean_ctor_set(v___x_1130_, 3, v_r_1121_);
lean_ctor_set(v___x_1130_, 2, v_v_888_);
lean_ctor_set(v___x_1130_, 1, v_k_887_);
lean_ctor_set(v___x_1130_, 0, v___x_1036_);
v___x_1134_ = v___x_1130_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_1141_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_1141_, 3, v_r_1121_);
lean_ctor_set(v_reuseFailAlloc_1141_, 4, v_r_1121_);
v___x_1134_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1136_; 
lean_inc(v_r_1121_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 3, v_r_1121_);
lean_ctor_set(v___x_1125_, 0, v___x_1036_);
v___x_1136_ = v___x_1125_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_k_1122_);
lean_ctor_set(v_reuseFailAlloc_1140_, 2, v_v_1123_);
lean_ctor_set(v_reuseFailAlloc_1140_, 3, v_r_1121_);
lean_ctor_set(v_reuseFailAlloc_1140_, 4, v_r_1121_);
v___x_1136_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
lean_object* v___x_1138_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 4, v___x_1136_);
lean_ctor_set(v___x_892_, 3, v___x_1134_);
lean_ctor_set(v___x_892_, 2, v_v_1128_);
lean_ctor_set(v___x_892_, 1, v_k_1127_);
lean_ctor_set(v___x_892_, 0, v___x_1132_);
v___x_1138_ = v___x_892_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1132_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_k_1127_);
lean_ctor_set(v_reuseFailAlloc_1139_, 2, v_v_1128_);
lean_ctor_set(v_reuseFailAlloc_1139_, 3, v___x_1134_);
lean_ctor_set(v_reuseFailAlloc_1139_, 4, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
}
}
else
{
lean_object* v_r_1149_; 
v_r_1149_ = lean_ctor_get(v_impl_1035_, 4);
lean_inc(v_r_1149_);
if (lean_obj_tag(v_r_1149_) == 0)
{
lean_object* v_k_1150_; lean_object* v_v_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1162_; 
v_k_1150_ = lean_ctor_get(v_impl_1035_, 1);
v_v_1151_ = lean_ctor_get(v_impl_1035_, 2);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_impl_1035_);
if (v_isSharedCheck_1162_ == 0)
{
lean_object* v_unused_1163_; lean_object* v_unused_1164_; lean_object* v_unused_1165_; 
v_unused_1163_ = lean_ctor_get(v_impl_1035_, 4);
lean_dec(v_unused_1163_);
v_unused_1164_ = lean_ctor_get(v_impl_1035_, 3);
lean_dec(v_unused_1164_);
v_unused_1165_ = lean_ctor_get(v_impl_1035_, 0);
lean_dec(v_unused_1165_);
v___x_1153_ = v_impl_1035_;
v_isShared_1154_ = v_isSharedCheck_1162_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_v_1151_);
lean_inc(v_k_1150_);
lean_dec(v_impl_1035_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1162_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1155_ = lean_unsigned_to_nat(3u);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 4, v_l_1120_);
lean_ctor_set(v___x_1153_, 2, v_v_888_);
lean_ctor_set(v___x_1153_, 1, v_k_887_);
lean_ctor_set(v___x_1153_, 0, v___x_1036_);
v___x_1157_ = v___x_1153_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_1161_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_1161_, 3, v_l_1120_);
lean_ctor_set(v_reuseFailAlloc_1161_, 4, v_l_1120_);
v___x_1157_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1159_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 4, v_r_1149_);
lean_ctor_set(v___x_892_, 3, v___x_1157_);
lean_ctor_set(v___x_892_, 2, v_v_1151_);
lean_ctor_set(v___x_892_, 1, v_k_1150_);
lean_ctor_set(v___x_892_, 0, v___x_1155_);
v___x_1159_ = v___x_892_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1155_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v_k_1150_);
lean_ctor_set(v_reuseFailAlloc_1160_, 2, v_v_1151_);
lean_ctor_set(v_reuseFailAlloc_1160_, 3, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1160_, 4, v_r_1149_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
else
{
lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1166_ = lean_unsigned_to_nat(2u);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 4, v_impl_1035_);
lean_ctor_set(v___x_892_, 3, v_r_1149_);
lean_ctor_set(v___x_892_, 0, v___x_1166_);
v___x_1168_ = v___x_892_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_1169_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_1169_, 3, v_r_1149_);
lean_ctor_set(v_reuseFailAlloc_1169_, 4, v_impl_1035_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
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
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = lean_unsigned_to_nat(1u);
v___x_1172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
lean_ctor_set(v___x_1172_, 1, v_k_883_);
lean_ctor_set(v___x_1172_, 2, v_v_884_);
lean_ctor_set(v___x_1172_, 3, v_t_885_);
lean_ctor_set(v___x_1172_, 4, v_t_885_);
return v___x_1172_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(lean_object* v_as_x27_1173_, lean_object* v_b_1174_){
_start:
{
if (lean_obj_tag(v_as_x27_1173_) == 0)
{
return v_b_1174_;
}
else
{
lean_object* v_head_1175_; lean_object* v_tail_1176_; lean_object* v_fst_1177_; lean_object* v_snd_1178_; lean_object* v_r_1179_; 
v_head_1175_ = lean_ctor_get(v_as_x27_1173_, 0);
v_tail_1176_ = lean_ctor_get(v_as_x27_1173_, 1);
v_fst_1177_ = lean_ctor_get(v_head_1175_, 0);
v_snd_1178_ = lean_ctor_get(v_head_1175_, 1);
lean_inc(v_snd_1178_);
lean_inc(v_fst_1177_);
v_r_1179_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_fst_1177_, v_snd_1178_, v_b_1174_);
v_as_x27_1173_ = v_tail_1176_;
v_b_1174_ = v_r_1179_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg___boxed(lean_object* v_as_x27_1181_, lean_object* v_b_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_as_x27_1181_, v_b_1182_);
lean_dec(v_as_x27_1181_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mkObj(lean_object* v_o_1184_){
_start:
{
lean_object* v_r_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v_r_1185_ = lean_box(1);
v___x_1186_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_o_1184_, v_r_1185_);
v___x_1187_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mkObj___boxed(lean_object* v_o_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_Json_mkObj(v_o_1188_);
lean_dec(v_o_1188_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0(lean_object* v_00_u03b2_1190_, lean_object* v_k_1191_, lean_object* v_v_1192_, lean_object* v_t_1193_, lean_object* v_hl_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_1191_, v_v_1192_, v_t_1193_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1(lean_object* v_as_1196_, lean_object* v_as_x27_1197_, lean_object* v_b_1198_, lean_object* v_a_1199_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_as_x27_1197_, v_b_1198_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___boxed(lean_object* v_as_1201_, lean_object* v_as_x27_1202_, lean_object* v_b_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1(v_as_1201_, v_as_x27_1202_, v_b_1203_, v_a_1204_);
lean_dec(v_as_x27_1202_);
lean_dec(v_as_1201_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeNat___lam__0(lean_object* v_n_1206_){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = l_Lean_JsonNumber_fromNat(v_n_1206_);
v___x_1208_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeInt___lam__0(lean_object* v_n_1211_){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = l_Lean_JsonNumber_fromInt(v_n_1211_);
v___x_1213_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeString___lam__0(lean_object* v_s_1216_){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1217_, 0, v_s_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeBool___lam__0(uint8_t v_b_1220_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1221_, 0, v_b_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeBool___lam__0___boxed(lean_object* v_b_1222_){
_start:
{
uint8_t v_b_boxed_1223_; lean_object* v_res_1224_; 
v_b_boxed_1223_ = lean_unbox(v_b_1222_);
v_res_1224_ = l_Lean_Json_instCoeBool___lam__0(v_b_boxed_1223_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instOfNat(lean_object* v_n_1227_){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = l_Lean_JsonNumber_fromNat(v_n_1227_);
v___x_1229_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT uint8_t l_Lean_Json_isNull(lean_object* v_x_1230_){
_start:
{
if (lean_obj_tag(v_x_1230_) == 0)
{
uint8_t v___x_1231_; 
v___x_1231_ = 1;
return v___x_1231_;
}
else
{
uint8_t v___x_1232_; 
v___x_1232_ = 0;
return v___x_1232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_isNull___boxed(lean_object* v_x_1233_){
_start:
{
uint8_t v_res_1234_; lean_object* v_r_1235_; 
v_res_1234_ = l_Lean_Json_isNull(v_x_1233_);
lean_dec(v_x_1233_);
v_r_1235_ = lean_box(v_res_1234_);
return v_r_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObj_x3f(lean_object* v_x_1239_){
_start:
{
if (lean_obj_tag(v_x_1239_) == 5)
{
lean_object* v_kvPairs_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
v_kvPairs_1240_ = lean_ctor_get(v_x_1239_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v_x_1239_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v_x_1239_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_kvPairs_1240_);
lean_dec(v_x_1239_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set_tag(v___x_1242_, 1);
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_kvPairs_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
else
{
lean_object* v___x_1248_; 
lean_dec(v_x_1239_);
v___x_1248_ = ((lean_object*)(l_Lean_Json_getObj_x3f___closed__1));
return v___x_1248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getArr_x3f(lean_object* v_x_1252_){
_start:
{
if (lean_obj_tag(v_x_1252_) == 4)
{
lean_object* v_elems_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
v_elems_1253_ = lean_ctor_get(v_x_1252_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_x_1252_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v_x_1252_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_elems_1253_);
lean_dec(v_x_1252_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
lean_ctor_set_tag(v___x_1255_, 1);
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_elems_1253_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
else
{
lean_object* v___x_1261_; 
lean_dec(v_x_1252_);
v___x_1261_ = ((lean_object*)(l_Lean_Json_getArr_x3f___closed__1));
return v___x_1261_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getStr_x3f(lean_object* v_x_1265_){
_start:
{
if (lean_obj_tag(v_x_1265_) == 3)
{
lean_object* v_s_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
v_s_1266_ = lean_ctor_get(v_x_1265_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_x_1265_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v_x_1265_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_s_1266_);
lean_dec(v_x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set_tag(v___x_1268_, 1);
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_s_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
else
{
lean_object* v___x_1274_; 
lean_dec(v_x_1265_);
v___x_1274_ = ((lean_object*)(l_Lean_Json_getStr_x3f___closed__1));
return v___x_1274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getNat_x3f(lean_object* v_x_1278_){
_start:
{
if (lean_obj_tag(v_x_1278_) == 2)
{
lean_object* v_n_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1295_; 
v_n_1281_ = lean_ctor_get(v_x_1278_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v_x_1278_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1283_ = v_x_1278_;
v_isShared_1284_ = v_isSharedCheck_1295_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_n_1281_);
lean_dec(v_x_1278_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1295_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v_mantissa_1285_; lean_object* v_exponent_1286_; lean_object* v_natZero_1287_; lean_object* v_intZero_1288_; uint8_t v_isNeg_1289_; 
v_mantissa_1285_ = lean_ctor_get(v_n_1281_, 0);
lean_inc(v_mantissa_1285_);
v_exponent_1286_ = lean_ctor_get(v_n_1281_, 1);
lean_inc(v_exponent_1286_);
lean_dec_ref(v_n_1281_);
v_natZero_1287_ = lean_unsigned_to_nat(0u);
v_intZero_1288_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v_isNeg_1289_ = lean_int_dec_lt(v_mantissa_1285_, v_intZero_1288_);
if (v_isNeg_1289_ == 0)
{
uint8_t v___x_1290_; 
v___x_1290_ = lean_nat_dec_eq(v_exponent_1286_, v_natZero_1287_);
lean_dec(v_exponent_1286_);
if (v___x_1290_ == 0)
{
lean_dec(v_mantissa_1285_);
lean_del_object(v___x_1283_);
goto v___jp_1279_;
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; 
v_a_1291_ = lean_nat_abs(v_mantissa_1285_);
lean_dec(v_mantissa_1285_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set_tag(v___x_1283_, 1);
lean_ctor_set(v___x_1283_, 0, v_a_1291_);
v___x_1293_ = v___x_1283_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
else
{
lean_dec(v_exponent_1286_);
lean_dec(v_mantissa_1285_);
lean_del_object(v___x_1283_);
goto v___jp_1279_;
}
}
}
else
{
lean_dec(v_x_1278_);
goto v___jp_1279_;
}
v___jp_1279_:
{
lean_object* v___x_1280_; 
v___x_1280_ = ((lean_object*)(l_Lean_Json_getNat_x3f___closed__1));
return v___x_1280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getInt_x3f(lean_object* v_x_1299_){
_start:
{
if (lean_obj_tag(v_x_1299_) == 2)
{
lean_object* v_n_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1313_; 
v_n_1302_ = lean_ctor_get(v_x_1299_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v_x_1299_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1304_ = v_x_1299_;
v_isShared_1305_ = v_isSharedCheck_1313_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_n_1302_);
lean_dec(v_x_1299_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1313_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v_mantissa_1306_; lean_object* v_exponent_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v_mantissa_1306_ = lean_ctor_get(v_n_1302_, 0);
lean_inc(v_mantissa_1306_);
v_exponent_1307_ = lean_ctor_get(v_n_1302_, 1);
lean_inc(v_exponent_1307_);
lean_dec_ref(v_n_1302_);
v___x_1308_ = lean_unsigned_to_nat(0u);
v___x_1309_ = lean_nat_dec_eq(v_exponent_1307_, v___x_1308_);
lean_dec(v_exponent_1307_);
if (v___x_1309_ == 0)
{
lean_dec(v_mantissa_1306_);
lean_del_object(v___x_1304_);
goto v___jp_1300_;
}
else
{
lean_object* v___x_1311_; 
if (v_isShared_1305_ == 0)
{
lean_ctor_set_tag(v___x_1304_, 1);
lean_ctor_set(v___x_1304_, 0, v_mantissa_1306_);
v___x_1311_ = v___x_1304_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_mantissa_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
else
{
lean_dec(v_x_1299_);
goto v___jp_1300_;
}
v___jp_1300_:
{
lean_object* v___x_1301_; 
v___x_1301_ = ((lean_object*)(l_Lean_Json_getInt_x3f___closed__1));
return v___x_1301_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getBool_x3f(lean_object* v_x_1317_){
_start:
{
if (lean_obj_tag(v_x_1317_) == 1)
{
uint8_t v_b_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v_b_1318_ = lean_ctor_get_uint8(v_x_1317_, 0);
v___x_1319_ = lean_box(v_b_1318_);
v___x_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
return v___x_1320_;
}
else
{
lean_object* v___x_1321_; 
v___x_1321_ = ((lean_object*)(l_Lean_Json_getBool_x3f___closed__1));
return v___x_1321_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getBool_x3f___boxed(lean_object* v_x_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lean_Json_getBool_x3f(v_x_1322_);
lean_dec(v_x_1322_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getNum_x3f(lean_object* v_x_1327_){
_start:
{
if (lean_obj_tag(v_x_1327_) == 2)
{
lean_object* v_n_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
v_n_1328_ = lean_ctor_get(v_x_1327_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_x_1327_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v_x_1327_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_n_1328_);
lean_dec(v_x_1327_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
lean_ctor_set_tag(v___x_1330_, 1);
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_n_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
else
{
lean_object* v___x_1336_; 
lean_dec(v_x_1327_);
v___x_1336_ = ((lean_object*)(l_Lean_Json_getNum_x3f___closed__1));
return v___x_1336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjVal_x3f(lean_object* v_x_1340_, lean_object* v_x_1341_){
_start:
{
if (lean_obj_tag(v_x_1340_) == 5)
{
lean_object* v_kvPairs_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1360_; 
v_kvPairs_1342_ = lean_ctor_get(v_x_1340_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v_x_1340_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1344_ = v_x_1340_;
v_isShared_1345_ = v_isSharedCheck_1360_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_kvPairs_1342_);
lean_dec(v_x_1340_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1360_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; 
v___x_1346_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_kvPairs_1342_, v_x_1341_);
lean_dec(v_kvPairs_1342_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1347_ = ((lean_object*)(l_Lean_Json_getObjVal_x3f___closed__0));
v___x_1348_ = lean_string_append(v___x_1347_, v_x_1341_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set_tag(v___x_1344_, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1348_);
v___x_1350_ = v___x_1344_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
else
{
lean_object* v_val_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
lean_del_object(v___x_1344_);
v_val_1352_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1346_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_val_1352_);
lean_dec(v___x_1346_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_val_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
}
else
{
lean_object* v___x_1361_; 
lean_dec(v_x_1340_);
v___x_1361_ = ((lean_object*)(l_Lean_Json_getObjVal_x3f___closed__1));
return v___x_1361_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjVal_x3f___boxed(lean_object* v_x_1362_, lean_object* v_x_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lean_Json_getObjVal_x3f(v_x_1362_, v_x_1363_);
lean_dec_ref(v_x_1363_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getArrVal_x3f(lean_object* v_x_1368_, lean_object* v_x_1369_){
_start:
{
if (lean_obj_tag(v_x_1368_) == 4)
{
lean_object* v_elems_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1386_; 
v_elems_1370_ = lean_ctor_get(v_x_1368_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v_x_1368_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1372_ = v_x_1368_;
v_isShared_1373_ = v_isSharedCheck_1386_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_elems_1370_);
lean_dec(v_x_1368_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1386_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1374_; uint8_t v___x_1375_; 
v___x_1374_ = lean_array_get_size(v_elems_1370_);
v___x_1375_ = lean_nat_dec_lt(v_x_1369_, v___x_1374_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1380_; 
lean_dec_ref(v_elems_1370_);
v___x_1376_ = ((lean_object*)(l_Lean_Json_getArrVal_x3f___closed__0));
v___x_1377_ = l_Nat_reprFast(v_x_1369_);
v___x_1378_ = lean_string_append(v___x_1376_, v___x_1377_);
lean_dec_ref(v___x_1377_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set_tag(v___x_1372_, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1378_);
v___x_1380_ = v___x_1372_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
else
{
lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1382_ = lean_array_fget(v_elems_1370_, v_x_1369_);
lean_dec(v_x_1369_);
lean_dec_ref(v_elems_1370_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set_tag(v___x_1372_, 1);
lean_ctor_set(v___x_1372_, 0, v___x_1382_);
v___x_1384_ = v___x_1372_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
else
{
lean_object* v___x_1387_; 
lean_dec(v_x_1369_);
lean_dec(v_x_1368_);
v___x_1387_ = ((lean_object*)(l_Lean_Json_getArrVal_x3f___closed__1));
return v___x_1387_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValD(lean_object* v_j_1388_, lean_object* v_k_1389_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Lean_Json_getObjVal_x3f(v_j_1388_, v_k_1389_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v___x_1391_; 
lean_dec_ref_known(v___x_1390_, 1);
v___x_1391_ = lean_box(0);
return v___x_1391_;
}
else
{
lean_object* v_a_1392_; 
v_a_1392_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1390_, 1);
return v_a_1392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValD___boxed(lean_object* v_j_1393_, lean_object* v_k_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_Json_getObjValD(v_j_1393_, v_k_1394_);
lean_dec_ref(v_k_1394_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Json_setObjVal_x21_spec__1(lean_object* v_msg_1396_){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = lean_box(0);
v___x_1398_ = lean_panic_fn_borrowed(v___x_1397_, v_msg_1396_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(lean_object* v_msg_1399_){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = lean_box(1);
v___x_1401_ = lean_panic_fn_borrowed(v___x_1400_, v_msg_1399_);
return v___x_1401_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1405_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2));
v___x_1406_ = lean_unsigned_to_nat(35u);
v___x_1407_ = lean_unsigned_to_nat(182u);
v___x_1408_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1));
v___x_1409_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1410_ = l_mkPanicMessageWithDecl(v___x_1409_, v___x_1408_, v___x_1407_, v___x_1406_, v___x_1405_);
return v___x_1410_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1411_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2));
v___x_1412_ = lean_unsigned_to_nat(21u);
v___x_1413_ = lean_unsigned_to_nat(183u);
v___x_1414_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1));
v___x_1415_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1416_ = l_mkPanicMessageWithDecl(v___x_1415_, v___x_1414_, v___x_1413_, v___x_1412_, v___x_1411_);
return v___x_1416_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1419_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6));
v___x_1420_ = lean_unsigned_to_nat(35u);
v___x_1421_ = lean_unsigned_to_nat(276u);
v___x_1422_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5));
v___x_1423_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1424_ = l_mkPanicMessageWithDecl(v___x_1423_, v___x_1422_, v___x_1421_, v___x_1420_, v___x_1419_);
return v___x_1424_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1425_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6));
v___x_1426_ = lean_unsigned_to_nat(21u);
v___x_1427_ = lean_unsigned_to_nat(277u);
v___x_1428_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5));
v___x_1429_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1430_ = l_mkPanicMessageWithDecl(v___x_1429_, v___x_1428_, v___x_1427_, v___x_1426_, v___x_1425_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(lean_object* v_k_1431_, lean_object* v_v_1432_, lean_object* v_t_1433_){
_start:
{
if (lean_obj_tag(v_t_1433_) == 0)
{
lean_object* v_size_1434_; lean_object* v_k_1435_; lean_object* v_v_1436_; lean_object* v_l_1437_; lean_object* v_r_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1794_; 
v_size_1434_ = lean_ctor_get(v_t_1433_, 0);
v_k_1435_ = lean_ctor_get(v_t_1433_, 1);
v_v_1436_ = lean_ctor_get(v_t_1433_, 2);
v_l_1437_ = lean_ctor_get(v_t_1433_, 3);
v_r_1438_ = lean_ctor_get(v_t_1433_, 4);
v_isSharedCheck_1794_ = !lean_is_exclusive(v_t_1433_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1440_ = v_t_1433_;
v_isShared_1441_ = v_isSharedCheck_1794_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_r_1438_);
lean_inc(v_l_1437_);
lean_inc(v_v_1436_);
lean_inc(v_k_1435_);
lean_inc(v_size_1434_);
lean_dec(v_t_1433_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1794_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
uint8_t v___x_1442_; 
v___x_1442_ = lean_string_compare(v_k_1431_, v_k_1435_);
switch(v___x_1442_)
{
case 0:
{
lean_object* v___x_1443_; 
lean_dec(v_size_1434_);
v___x_1443_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1431_, v_v_1432_, v_l_1437_);
if (lean_obj_tag(v_r_1438_) == 0)
{
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v_size_1444_; lean_object* v_size_1445_; lean_object* v_k_1446_; lean_object* v_v_1447_; lean_object* v_l_1448_; lean_object* v_r_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; uint8_t v___x_1452_; 
v_size_1444_ = lean_ctor_get(v_r_1438_, 0);
v_size_1445_ = lean_ctor_get(v___x_1443_, 0);
lean_inc(v_size_1445_);
v_k_1446_ = lean_ctor_get(v___x_1443_, 1);
lean_inc(v_k_1446_);
v_v_1447_ = lean_ctor_get(v___x_1443_, 2);
lean_inc(v_v_1447_);
v_l_1448_ = lean_ctor_get(v___x_1443_, 3);
lean_inc(v_l_1448_);
v_r_1449_ = lean_ctor_get(v___x_1443_, 4);
lean_inc(v_r_1449_);
v___x_1450_ = lean_unsigned_to_nat(3u);
v___x_1451_ = lean_nat_mul(v___x_1450_, v_size_1444_);
v___x_1452_ = lean_nat_dec_lt(v___x_1451_, v_size_1445_);
lean_dec(v___x_1451_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1457_; 
lean_dec(v_r_1449_);
lean_dec(v_l_1448_);
lean_dec(v_v_1447_);
lean_dec(v_k_1446_);
v___x_1453_ = lean_unsigned_to_nat(1u);
v___x_1454_ = lean_nat_add(v___x_1453_, v_size_1445_);
lean_dec(v_size_1445_);
v___x_1455_ = lean_nat_add(v___x_1454_, v_size_1444_);
lean_dec(v___x_1454_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 3, v___x_1443_);
lean_ctor_set(v___x_1440_, 0, v___x_1455_);
v___x_1457_ = v___x_1440_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v_k_1435_);
lean_ctor_set(v_reuseFailAlloc_1458_, 2, v_v_1436_);
lean_ctor_set(v_reuseFailAlloc_1458_, 3, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1458_, 4, v_r_1438_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
else
{
lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1530_; 
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1530_ == 0)
{
lean_object* v_unused_1531_; lean_object* v_unused_1532_; lean_object* v_unused_1533_; lean_object* v_unused_1534_; lean_object* v_unused_1535_; 
v_unused_1531_ = lean_ctor_get(v___x_1443_, 4);
lean_dec(v_unused_1531_);
v_unused_1532_ = lean_ctor_get(v___x_1443_, 3);
lean_dec(v_unused_1532_);
v_unused_1533_ = lean_ctor_get(v___x_1443_, 2);
lean_dec(v_unused_1533_);
v_unused_1534_ = lean_ctor_get(v___x_1443_, 1);
lean_dec(v_unused_1534_);
v_unused_1535_ = lean_ctor_get(v___x_1443_, 0);
lean_dec(v_unused_1535_);
v___x_1460_ = v___x_1443_;
v_isShared_1461_ = v_isSharedCheck_1530_;
goto v_resetjp_1459_;
}
else
{
lean_dec(v___x_1443_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1530_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
if (lean_obj_tag(v_l_1448_) == 0)
{
if (lean_obj_tag(v_r_1449_) == 0)
{
lean_object* v_size_1462_; lean_object* v_size_1463_; lean_object* v_k_1464_; lean_object* v_v_1465_; lean_object* v_l_1466_; lean_object* v_r_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; uint8_t v___x_1470_; 
v_size_1462_ = lean_ctor_get(v_l_1448_, 0);
v_size_1463_ = lean_ctor_get(v_r_1449_, 0);
v_k_1464_ = lean_ctor_get(v_r_1449_, 1);
v_v_1465_ = lean_ctor_get(v_r_1449_, 2);
v_l_1466_ = lean_ctor_get(v_r_1449_, 3);
v_r_1467_ = lean_ctor_get(v_r_1449_, 4);
v___x_1468_ = lean_unsigned_to_nat(2u);
v___x_1469_ = lean_nat_mul(v___x_1468_, v_size_1462_);
v___x_1470_ = lean_nat_dec_lt(v_size_1463_, v___x_1469_);
lean_dec(v___x_1469_);
if (v___x_1470_ == 0)
{
lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1500_; 
lean_inc(v_r_1467_);
lean_inc(v_l_1466_);
lean_inc(v_v_1465_);
lean_inc(v_k_1464_);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_r_1449_);
if (v_isSharedCheck_1500_ == 0)
{
lean_object* v_unused_1501_; lean_object* v_unused_1502_; lean_object* v_unused_1503_; lean_object* v_unused_1504_; lean_object* v_unused_1505_; 
v_unused_1501_ = lean_ctor_get(v_r_1449_, 4);
lean_dec(v_unused_1501_);
v_unused_1502_ = lean_ctor_get(v_r_1449_, 3);
lean_dec(v_unused_1502_);
v_unused_1503_ = lean_ctor_get(v_r_1449_, 2);
lean_dec(v_unused_1503_);
v_unused_1504_ = lean_ctor_get(v_r_1449_, 1);
lean_dec(v_unused_1504_);
v_unused_1505_ = lean_ctor_get(v_r_1449_, 0);
lean_dec(v_unused_1505_);
v___x_1472_ = v_r_1449_;
v_isShared_1473_ = v_isSharedCheck_1500_;
goto v_resetjp_1471_;
}
else
{
lean_dec(v_r_1449_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1500_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___x_1488_; lean_object* v___y_1490_; 
v___x_1474_ = lean_unsigned_to_nat(1u);
v___x_1475_ = lean_nat_add(v___x_1474_, v_size_1445_);
lean_dec(v_size_1445_);
v___x_1476_ = lean_nat_add(v___x_1475_, v_size_1444_);
lean_dec(v___x_1475_);
v___x_1488_ = lean_nat_add(v___x_1474_, v_size_1462_);
if (lean_obj_tag(v_l_1466_) == 0)
{
lean_object* v_size_1498_; 
v_size_1498_ = lean_ctor_get(v_l_1466_, 0);
lean_inc(v_size_1498_);
v___y_1490_ = v_size_1498_;
goto v___jp_1489_;
}
else
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_unsigned_to_nat(0u);
v___y_1490_ = v___x_1499_;
goto v___jp_1489_;
}
v___jp_1477_:
{
lean_object* v___x_1481_; lean_object* v___x_1483_; 
v___x_1481_ = lean_nat_add(v___y_1478_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec(v___y_1478_);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 4, v_r_1438_);
lean_ctor_set(v___x_1472_, 3, v_r_1467_);
lean_ctor_set(v___x_1472_, 2, v_v_1436_);
lean_ctor_set(v___x_1472_, 1, v_k_1435_);
lean_ctor_set(v___x_1472_, 0, v___x_1481_);
v___x_1483_ = v___x_1472_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1481_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v_k_1435_);
lean_ctor_set(v_reuseFailAlloc_1487_, 2, v_v_1436_);
lean_ctor_set(v_reuseFailAlloc_1487_, 3, v_r_1467_);
lean_ctor_set(v_reuseFailAlloc_1487_, 4, v_r_1438_);
v___x_1483_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
lean_object* v___x_1485_; 
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 4, v___x_1483_);
lean_ctor_set(v___x_1460_, 3, v___y_1479_);
lean_ctor_set(v___x_1460_, 2, v_v_1465_);
lean_ctor_set(v___x_1460_, 1, v_k_1464_);
lean_ctor_set(v___x_1460_, 0, v___x_1476_);
v___x_1485_ = v___x_1460_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1476_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v_k_1464_);
lean_ctor_set(v_reuseFailAlloc_1486_, 2, v_v_1465_);
lean_ctor_set(v_reuseFailAlloc_1486_, 3, v___y_1479_);
lean_ctor_set(v_reuseFailAlloc_1486_, 4, v___x_1483_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
v___jp_1489_:
{
lean_object* v___x_1491_; lean_object* v___x_1493_; 
v___x_1491_ = lean_nat_add(v___x_1488_, v___y_1490_);
lean_dec(v___y_1490_);
lean_dec(v___x_1488_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 4, v_l_1466_);
lean_ctor_set(v___x_1440_, 3, v_l_1448_);
lean_ctor_set(v___x_1440_, 2, v_v_1447_);
lean_ctor_set(v___x_1440_, 1, v_k_1446_);
lean_ctor_set(v___x_1440_, 0, v___x_1491_);
v___x_1493_ = v___x_1440_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1491_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v_k_1446_);
lean_ctor_set(v_reuseFailAlloc_1497_, 2, v_v_1447_);
lean_ctor_set(v_reuseFailAlloc_1497_, 3, v_l_1448_);
lean_ctor_set(v_reuseFailAlloc_1497_, 4, v_l_1466_);
v___x_1493_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_nat_add(v___x_1474_, v_size_1444_);
if (lean_obj_tag(v_r_1467_) == 0)
{
lean_object* v_size_1495_; 
v_size_1495_ = lean_ctor_get(v_r_1467_, 0);
lean_inc(v_size_1495_);
v___y_1478_ = v___x_1494_;
v___y_1479_ = v___x_1493_;
v___y_1480_ = v_size_1495_;
goto v___jp_1477_;
}
else
{
lean_object* v___x_1496_; 
v___x_1496_ = lean_unsigned_to_nat(0u);
v___y_1478_ = v___x_1494_;
v___y_1479_ = v___x_1493_;
v___y_1480_ = v___x_1496_;
goto v___jp_1477_;
}
}
}
}
}
else
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; 
lean_del_object(v___x_1440_);
v___x_1506_ = lean_unsigned_to_nat(1u);
v___x_1507_ = lean_nat_add(v___x_1506_, v_size_1445_);
lean_dec(v_size_1445_);
v___x_1508_ = lean_nat_add(v___x_1507_, v_size_1444_);
lean_dec(v___x_1507_);
v___x_1509_ = lean_nat_add(v___x_1506_, v_size_1444_);
v___x_1510_ = lean_nat_add(v___x_1509_, v_size_1463_);
lean_dec(v___x_1509_);
lean_inc_ref(v_r_1438_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 4, v_r_1438_);
lean_ctor_set(v___x_1460_, 3, v_r_1449_);
lean_ctor_set(v___x_1460_, 2, v_v_1436_);
lean_ctor_set(v___x_1460_, 1, v_k_1435_);
lean_ctor_set(v___x_1460_, 0, v___x_1510_);
v___x_1512_ = v___x_1460_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1510_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_k_1435_);
lean_ctor_set(v_reuseFailAlloc_1525_, 2, v_v_1436_);
lean_ctor_set(v_reuseFailAlloc_1525_, 3, v_r_1449_);
lean_ctor_set(v_reuseFailAlloc_1525_, 4, v_r_1438_);
v___x_1512_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1519_; 
v_isSharedCheck_1519_ = !lean_is_exclusive(v_r_1438_);
if (v_isSharedCheck_1519_ == 0)
{
lean_object* v_unused_1520_; lean_object* v_unused_1521_; lean_object* v_unused_1522_; lean_object* v_unused_1523_; lean_object* v_unused_1524_; 
v_unused_1520_ = lean_ctor_get(v_r_1438_, 4);
lean_dec(v_unused_1520_);
v_unused_1521_ = lean_ctor_get(v_r_1438_, 3);
lean_dec(v_unused_1521_);
v_unused_1522_ = lean_ctor_get(v_r_1438_, 2);
lean_dec(v_unused_1522_);
v_unused_1523_ = lean_ctor_get(v_r_1438_, 1);
lean_dec(v_unused_1523_);
v_unused_1524_ = lean_ctor_get(v_r_1438_, 0);
lean_dec(v_unused_1524_);
v___x_1514_ = v_r_1438_;
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
else
{
lean_dec(v_r_1438_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 4, v___x_1512_);
lean_ctor_set(v___x_1514_, 3, v_l_1448_);
lean_ctor_set(v___x_1514_, 2, v_v_1447_);
lean_ctor_set(v___x_1514_, 1, v_k_1446_);
lean_ctor_set(v___x_1514_, 0, v___x_1508_);
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1508_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_k_1446_);
lean_ctor_set(v_reuseFailAlloc_1518_, 2, v_v_1447_);
lean_ctor_set(v_reuseFailAlloc_1518_, 3, v_l_1448_);
lean_ctor_set(v_reuseFailAlloc_1518_, 4, v___x_1512_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
}
}
else
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
lean_dec_ref_known(v_l_1448_, 5);
lean_del_object(v___x_1460_);
lean_dec(v_v_1447_);
lean_dec(v_k_1446_);
lean_dec(v_size_1445_);
lean_dec_ref_known(v_r_1438_, 5);
lean_del_object(v___x_1440_);
lean_dec(v_v_1436_);
lean_dec(v_k_1435_);
v___x_1526_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3);
v___x_1527_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1526_);
return v___x_1527_;
}
}
else
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
lean_del_object(v___x_1460_);
lean_dec(v_r_1449_);
lean_dec(v_v_1447_);
lean_dec(v_k_1446_);
lean_dec(v_size_1445_);
lean_dec_ref_known(v_r_1438_, 5);
lean_del_object(v___x_1440_);
lean_dec(v_v_1436_);
lean_dec(v_k_1435_);
v___x_1528_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4);
v___x_1529_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1528_);
return v___x_1529_;
}
}
}
}
else
{
lean_object* v_size_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1540_; 
v_size_1536_ = lean_ctor_get(v_r_1438_, 0);
v___x_1537_ = lean_unsigned_to_nat(1u);
v___x_1538_ = lean_nat_add(v___x_1537_, v_size_1536_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 3, v___x_1443_);
lean_ctor_set(v___x_1440_, 0, v___x_1538_);
v___x_1540_ = v___x_1440_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1538_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_k_1435_);
lean_ctor_set(v_reuseFailAlloc_1541_, 2, v_v_1436_);
lean_ctor_set(v_reuseFailAlloc_1541_, 3, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1541_, 4, v_r_1438_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
else
{
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v_l_1542_; 
v_l_1542_ = lean_ctor_get(v___x_1443_, 3);
lean_inc(v_l_1542_);
if (lean_obj_tag(v_l_1542_) == 0)
{
lean_object* v_r_1543_; 
v_r_1543_ = lean_ctor_get(v___x_1443_, 4);
lean_inc(v_r_1543_);
if (lean_obj_tag(v_r_1543_) == 0)
{
lean_object* v_size_1544_; lean_object* v_k_1545_; lean_object* v_v_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1560_; 
v_size_1544_ = lean_ctor_get(v___x_1443_, 0);
v_k_1545_ = lean_ctor_get(v___x_1443_, 1);
v_v_1546_ = lean_ctor_get(v___x_1443_, 2);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1560_ == 0)
{
lean_object* v_unused_1561_; lean_object* v_unused_1562_; 
v_unused_1561_ = lean_ctor_get(v___x_1443_, 4);
lean_dec(v_unused_1561_);
v_unused_1562_ = lean_ctor_get(v___x_1443_, 3);
lean_dec(v_unused_1562_);
v___x_1548_ = v___x_1443_;
v_isShared_1549_ = v_isSharedCheck_1560_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_v_1546_);
lean_inc(v_k_1545_);
lean_inc(v_size_1544_);
lean_dec(v___x_1443_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1560_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v_size_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1555_; 
v_size_1550_ = lean_ctor_get(v_r_1543_, 0);
v___x_1551_ = lean_unsigned_to_nat(1u);
v___x_1552_ = lean_nat_add(v___x_1551_, v_size_1544_);
lean_dec(v_size_1544_);
v___x_1553_ = lean_nat_add(v___x_1551_, v_size_1550_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 4, v_r_1438_);
lean_ctor_set(v___x_1548_, 3, v_r_1543_);
lean_ctor_set(v___x_1548_, 2, v_v_1436_);
lean_ctor_set(v___x_1548_, 1, v_k_1435_);
lean_ctor_set(v___x_1548_, 0, v___x_1553_);
v___x_1555_ = v___x_1548_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1553_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_k_1435_);
lean_ctor_set(v_reuseFailAlloc_1559_, 2, v_v_1436_);
lean_ctor_set(v_reuseFailAlloc_1559_, 3, v_r_1543_);
lean_ctor_set(v_reuseFailAlloc_1559_, 4, v_r_1438_);
v___x_1555_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
lean_object* v___x_1557_; 
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 4, v___x_1555_);
lean_ctor_set(v___x_1440_, 3, v_l_1542_);
lean_ctor_set(v___x_1440_, 2, v_v_1546_);
lean_ctor_set(v___x_1440_, 1, v_k_1545_);
lean_ctor_set(v___x_1440_, 0, v___x_1552_);
v___x_1557_ = v___x_1440_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1552_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_k_1545_);
lean_ctor_set(v_reuseFailAlloc_1558_, 2, v_v_1546_);
lean_ctor_set(v_reuseFailAlloc_1558_, 3, v_l_1542_);
lean_ctor_set(v_reuseFailAlloc_1558_, 4, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
else
{
lean_object* v_k_1563_; lean_object* v_v_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1576_; 
v_k_1563_ = lean_ctor_get(v___x_1443_, 1);
v_v_1564_ = lean_ctor_get(v___x_1443_, 2);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1576_ == 0)
{
lean_object* v_unused_1577_; lean_object* v_unused_1578_; lean_object* v_unused_1579_; 
v_unused_1577_ = lean_ctor_get(v___x_1443_, 4);
lean_dec(v_unused_1577_);
v_unused_1578_ = lean_ctor_get(v___x_1443_, 3);
lean_dec(v_unused_1578_);
v_unused_1579_ = lean_ctor_get(v___x_1443_, 0);
lean_dec(v_unused_1579_);
v___x_1566_ = v___x_1443_;
v_isShared_1567_ = v_isSharedCheck_1576_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_v_1564_);
lean_inc(v_k_1563_);
lean_dec(v___x_1443_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1576_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1571_; 
v___x_1568_ = lean_unsigned_to_nat(3u);
v___x_1569_ = lean_unsigned_to_nat(1u);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 3, v_r_1543_);
lean_ctor_set(v___x_1566_, 2, v_v_1436_);
lean_ctor_set(v___x_1566_, 1, v_k_1435_);
lean_ctor_set(v___x_1566_, 0, v___x_1569_);
v___x_1571_ = v___x_1566_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1569_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_k_1435_);
lean_ctor_set(v_reuseFailAlloc_1575_, 2, v_v_1436_);
lean_ctor_set(v_reuseFailAlloc_1575_, 3, v_r_1543_);
lean_ctor_set(v_reuseFailAlloc_1575_, 4, v_r_1543_);
v___x_1571_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
lean_object* v___x_1573_; 
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 4, v___x_1571_);
lean_ctor_set(v___x_1440_, 3, v_l_1542_);
lean_ctor_set(v___x_1440_, 2, v_v_1564_);
lean_ctor_set(v___x_1440_, 1, v_k_1563_);
lean_ctor_set(v___x_1440_, 0, v___x_1568_);
v___x_1573_ = v___x_1440_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1568_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v_k_1563_);
lean_ctor_set(v_reuseFailAlloc_1574_, 2, v_v_1564_);
lean_ctor_set(v_reuseFailAlloc_1574_, 3, v_l_1542_);
lean_ctor_set(v_reuseFailAlloc_1574_, 4, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
}
else
{
lean_object* v_r_1580_; 
v_r_1580_ = lean_ctor_get(v___x_1443_, 4);
lean_inc(v_r_1580_);
if (lean_obj_tag(v_r_1580_) == 0)
{
lean_object* v_k_1581_; lean_object* v_v_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1606_; 
v_k_1581_ = lean_ctor_get(v___x_1443_, 1);
v_v_1582_ = lean_ctor_get(v___x_1443_, 2);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1606_ == 0)
{
lean_object* v_unused_1607_; lean_object* v_unused_1608_; lean_object* v_unused_1609_; 
v_unused_1607_ = lean_ctor_get(v___x_1443_, 4);
lean_dec(v_unused_1607_);
v_unused_1608_ = lean_ctor_get(v___x_1443_, 3);
lean_dec(v_unused_1608_);
v_unused_1609_ = lean_ctor_get(v___x_1443_, 0);
lean_dec(v_unused_1609_);
v___x_1584_ = v___x_1443_;
v_isShared_1585_ = v_isSharedCheck_1606_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_v_1582_);
lean_inc(v_k_1581_);
lean_dec(v___x_1443_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1606_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v_k_1586_; lean_object* v_v_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1602_; 
v_k_1586_ = lean_ctor_get(v_r_1580_, 1);
v_v_1587_ = lean_ctor_get(v_r_1580_, 2);
v_isSharedCheck_1602_ = !lean_is_exclusive(v_r_1580_);
if (v_isSharedCheck_1602_ == 0)
{
lean_object* v_unused_1603_; lean_object* v_unused_1604_; lean_object* v_unused_1605_; 
v_unused_1603_ = lean_ctor_get(v_r_1580_, 4);
lean_dec(v_unused_1603_);
v_unused_1604_ = lean_ctor_get(v_r_1580_, 3);
lean_dec(v_unused_1604_);
v_unused_1605_ = lean_ctor_get(v_r_1580_, 0);
lean_dec(v_unused_1605_);
v___x_1589_ = v_r_1580_;
v_isShared_1590_ = v_isSharedCheck_1602_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_v_1587_);
lean_inc(v_k_1586_);
lean_dec(v_r_1580_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1602_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1594_; 
v___x_1591_ = lean_unsigned_to_nat(3u);
v___x_1592_ = lean_unsigned_to_nat(1u);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 4, v_l_1542_);
lean_ctor_set(v___x_1589_, 3, v_l_1542_);
lean_ctor_set(v___x_1589_, 2, v_v_1582_);
lean_ctor_set(v___x_1589_, 1, v_k_1581_);
lean_ctor_set(v___x_1589_, 0, v___x_1592_);
v___x_1594_ = v___x_1589_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1592_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_k_1581_);
lean_ctor_set(v_reuseFailAlloc_1601_, 2, v_v_1582_);
lean_ctor_set(v_reuseFailAlloc_1601_, 3, v_l_1542_);
lean_ctor_set(v_reuseFailAlloc_1601_, 4, v_l_1542_);
v___x_1594_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
lean_object* v___x_1596_; 
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 4, v_l_1542_);
lean_ctor_set(v___x_1584_, 2, v_v_1436_);
lean_ctor_set(v___x_1584_, 1, v_k_1435_);
lean_ctor_set(v___x_1584_, 0, v___x_1592_);
v___x_1596_ = v___x_1584_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1592_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v_k_1435_);
lean_ctor_set(v_reuseFailAlloc_1600_, 2, v_v_1436_);
lean_ctor_set(v_reuseFailAlloc_1600_, 3, v_l_1542_);
lean_ctor_set(v_reuseFailAlloc_1600_, 4, v_l_1542_);
v___x_1596_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_object* v___x_1598_; 
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 4, v___x_1596_);
lean_ctor_set(v___x_1440_, 3, v___x_1594_);
lean_ctor_set(v___x_1440_, 2, v_v_1587_);
lean_ctor_set(v___x_1440_, 1, v_k_1586_);
lean_ctor_set(v___x_1440_, 0, v___x_1591_);
v___x_1598_ = v___x_1440_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1591_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v_k_1586_);
lean_ctor_set(v_reuseFailAlloc_1599_, 2, v_v_1587_);
lean_ctor_set(v_reuseFailAlloc_1599_, 3, v___x_1594_);
lean_ctor_set(v_reuseFailAlloc_1599_, 4, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
}
}
else
{
lean_object* v___x_1610_; lean_object* v___x_1612_; 
v___x_1610_ = lean_unsigned_to_nat(2u);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 4, v_r_1580_);
lean_ctor_set(v___x_1440_, 3, v___x_1443_);
lean_ctor_set(v___x_1440_, 0, v___x_1610_);
v___x_1612_ = v___x_1440_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1610_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_k_1435_);
lean_ctor_set(v_reuseFailAlloc_1613_, 2, v_v_1436_);
lean_ctor_set(v_reuseFailAlloc_1613_, 3, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1613_, 4, v_r_1580_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
else
{
lean_object* v___x_1614_; lean_object* v___x_1616_; 
v___x_1614_ = lean_unsigned_to_nat(1u);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 4, v___x_1443_);
lean_ctor_set(v___x_1440_, 3, v___x_1443_);
lean_ctor_set(v___x_1440_, 0, v___x_1614_);
v___x_1616_ = v___x_1440_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1614_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v_k_1435_);
lean_ctor_set(v_reuseFailAlloc_1617_, 2, v_v_1436_);
lean_ctor_set(v_reuseFailAlloc_1617_, 3, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1617_, 4, v___x_1443_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
case 1:
{
lean_object* v___x_1619_; 
lean_dec(v_v_1436_);
lean_dec(v_k_1435_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 2, v_v_1432_);
lean_ctor_set(v___x_1440_, 1, v_k_1431_);
v___x_1619_ = v___x_1440_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_size_1434_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_k_1431_);
lean_ctor_set(v_reuseFailAlloc_1620_, 2, v_v_1432_);
lean_ctor_set(v_reuseFailAlloc_1620_, 3, v_l_1437_);
lean_ctor_set(v_reuseFailAlloc_1620_, 4, v_r_1438_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
default: 
{
lean_object* v___x_1621_; 
lean_dec(v_size_1434_);
v___x_1621_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1431_, v_v_1432_, v_r_1438_);
if (lean_obj_tag(v_l_1437_) == 0)
{
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_size_1622_; lean_object* v_size_1623_; lean_object* v_k_1624_; lean_object* v_v_1625_; lean_object* v_l_1626_; lean_object* v_r_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; uint8_t v___x_1630_; 
v_size_1622_ = lean_ctor_get(v_l_1437_, 0);
v_size_1623_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_size_1623_);
v_k_1624_ = lean_ctor_get(v___x_1621_, 1);
lean_inc(v_k_1624_);
v_v_1625_ = lean_ctor_get(v___x_1621_, 2);
lean_inc(v_v_1625_);
v_l_1626_ = lean_ctor_get(v___x_1621_, 3);
lean_inc(v_l_1626_);
v_r_1627_ = lean_ctor_get(v___x_1621_, 4);
lean_inc(v_r_1627_);
v___x_1628_ = lean_unsigned_to_nat(3u);
v___x_1629_ = lean_nat_mul(v___x_1628_, v_size_1622_);
v___x_1630_ = lean_nat_dec_lt(v___x_1629_, v_size_1623_);
lean_dec(v___x_1629_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1635_; 
lean_dec(v_r_1627_);
lean_dec(v_l_1626_);
lean_dec(v_v_1625_);
lean_dec(v_k_1624_);
v___x_1631_ = lean_unsigned_to_nat(1u);
v___x_1632_ = lean_nat_add(v___x_1631_, v_size_1622_);
v___x_1633_ = lean_nat_add(v___x_1632_, v_size_1623_);
lean_dec(v_size_1623_);
lean_dec(v___x_1632_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 4, v___x_1621_);
lean_ctor_set(v___x_1440_, 0, v___x_1633_);
v___x_1635_ = v___x_1440_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1633_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_k_1435_);
lean_ctor_set(v_reuseFailAlloc_1636_, 2, v_v_1436_);
lean_ctor_set(v_reuseFailAlloc_1636_, 3, v_l_1437_);
lean_ctor_set(v_reuseFailAlloc_1636_, 4, v___x_1621_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
else
{
lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1706_; 
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1706_ == 0)
{
lean_object* v_unused_1707_; lean_object* v_unused_1708_; lean_object* v_unused_1709_; lean_object* v_unused_1710_; lean_object* v_unused_1711_; 
v_unused_1707_ = lean_ctor_get(v___x_1621_, 4);
lean_dec(v_unused_1707_);
v_unused_1708_ = lean_ctor_get(v___x_1621_, 3);
lean_dec(v_unused_1708_);
v_unused_1709_ = lean_ctor_get(v___x_1621_, 2);
lean_dec(v_unused_1709_);
v_unused_1710_ = lean_ctor_get(v___x_1621_, 1);
lean_dec(v_unused_1710_);
v_unused_1711_ = lean_ctor_get(v___x_1621_, 0);
lean_dec(v_unused_1711_);
v___x_1638_ = v___x_1621_;
v_isShared_1639_ = v_isSharedCheck_1706_;
goto v_resetjp_1637_;
}
else
{
lean_dec(v___x_1621_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1706_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
if (lean_obj_tag(v_l_1626_) == 0)
{
if (lean_obj_tag(v_r_1627_) == 0)
{
lean_object* v_size_1640_; lean_object* v_k_1641_; lean_object* v_v_1642_; lean_object* v_l_1643_; lean_object* v_r_1644_; lean_object* v_size_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; uint8_t v___x_1648_; 
v_size_1640_ = lean_ctor_get(v_l_1626_, 0);
v_k_1641_ = lean_ctor_get(v_l_1626_, 1);
v_v_1642_ = lean_ctor_get(v_l_1626_, 2);
v_l_1643_ = lean_ctor_get(v_l_1626_, 3);
v_r_1644_ = lean_ctor_get(v_l_1626_, 4);
v_size_1645_ = lean_ctor_get(v_r_1627_, 0);
v___x_1646_ = lean_unsigned_to_nat(2u);
v___x_1647_ = lean_nat_mul(v___x_1646_, v_size_1645_);
v___x_1648_ = lean_nat_dec_lt(v_size_1640_, v___x_1647_);
lean_dec(v___x_1647_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1677_; 
lean_inc(v_r_1644_);
lean_inc(v_l_1643_);
lean_inc(v_v_1642_);
lean_inc(v_k_1641_);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_l_1626_);
if (v_isSharedCheck_1677_ == 0)
{
lean_object* v_unused_1678_; lean_object* v_unused_1679_; lean_object* v_unused_1680_; lean_object* v_unused_1681_; lean_object* v_unused_1682_; 
v_unused_1678_ = lean_ctor_get(v_l_1626_, 4);
lean_dec(v_unused_1678_);
v_unused_1679_ = lean_ctor_get(v_l_1626_, 3);
lean_dec(v_unused_1679_);
v_unused_1680_ = lean_ctor_get(v_l_1626_, 2);
lean_dec(v_unused_1680_);
v_unused_1681_ = lean_ctor_get(v_l_1626_, 1);
lean_dec(v_unused_1681_);
v_unused_1682_ = lean_ctor_get(v_l_1626_, 0);
lean_dec(v_unused_1682_);
v___x_1650_ = v_l_1626_;
v_isShared_1651_ = v_isSharedCheck_1677_;
goto v_resetjp_1649_;
}
else
{
lean_dec(v_l_1626_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1677_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1667_; 
v___x_1652_ = lean_unsigned_to_nat(1u);
v___x_1653_ = lean_nat_add(v___x_1652_, v_size_1622_);
v___x_1654_ = lean_nat_add(v___x_1653_, v_size_1623_);
lean_dec(v_size_1623_);
if (lean_obj_tag(v_l_1643_) == 0)
{
lean_object* v_size_1675_; 
v_size_1675_ = lean_ctor_get(v_l_1643_, 0);
lean_inc(v_size_1675_);
v___y_1667_ = v_size_1675_;
goto v___jp_1666_;
}
else
{
lean_object* v___x_1676_; 
v___x_1676_ = lean_unsigned_to_nat(0u);
v___y_1667_ = v___x_1676_;
goto v___jp_1666_;
}
v___jp_1655_:
{
lean_object* v___x_1659_; lean_object* v___x_1661_; 
v___x_1659_ = lean_nat_add(v___y_1656_, v___y_1658_);
lean_dec(v___y_1658_);
lean_dec(v___y_1656_);
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 4, v_r_1627_);
lean_ctor_set(v___x_1650_, 3, v_r_1644_);
lean_ctor_set(v___x_1650_, 2, v_v_1625_);
lean_ctor_set(v___x_1650_, 1, v_k_1624_);
lean_ctor_set(v___x_1650_, 0, v___x_1659_);
v___x_1661_ = v___x_1650_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1659_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_k_1624_);
lean_ctor_set(v_reuseFailAlloc_1665_, 2, v_v_1625_);
lean_ctor_set(v_reuseFailAlloc_1665_, 3, v_r_1644_);
lean_ctor_set(v_reuseFailAlloc_1665_, 4, v_r_1627_);
v___x_1661_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
lean_object* v___x_1663_; 
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 4, v___x_1661_);
lean_ctor_set(v___x_1638_, 3, v___y_1657_);
lean_ctor_set(v___x_1638_, 2, v_v_1642_);
lean_ctor_set(v___x_1638_, 1, v_k_1641_);
lean_ctor_set(v___x_1638_, 0, v___x_1654_);
v___x_1663_ = v___x_1638_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1654_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v_k_1641_);
lean_ctor_set(v_reuseFailAlloc_1664_, 2, v_v_1642_);
lean_ctor_set(v_reuseFailAlloc_1664_, 3, v___y_1657_);
lean_ctor_set(v_reuseFailAlloc_1664_, 4, v___x_1661_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
v___jp_1666_:
{
lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1668_ = lean_nat_add(v___x_1653_, v___y_1667_);
lean_dec(v___y_1667_);
lean_dec(v___x_1653_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 4, v_l_1643_);
lean_ctor_set(v___x_1440_, 0, v___x_1668_);
v___x_1670_ = v___x_1440_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1668_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v_k_1435_);
lean_ctor_set(v_reuseFailAlloc_1674_, 2, v_v_1436_);
lean_ctor_set(v_reuseFailAlloc_1674_, 3, v_l_1437_);
lean_ctor_set(v_reuseFailAlloc_1674_, 4, v_l_1643_);
v___x_1670_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
lean_object* v___x_1671_; 
v___x_1671_ = lean_nat_add(v___x_1652_, v_size_1645_);
if (lean_obj_tag(v_r_1644_) == 0)
{
lean_object* v_size_1672_; 
v_size_1672_ = lean_ctor_get(v_r_1644_, 0);
lean_inc(v_size_1672_);
v___y_1656_ = v___x_1671_;
v___y_1657_ = v___x_1670_;
v___y_1658_ = v_size_1672_;
goto v___jp_1655_;
}
else
{
lean_object* v___x_1673_; 
v___x_1673_ = lean_unsigned_to_nat(0u);
v___y_1656_ = v___x_1671_;
v___y_1657_ = v___x_1670_;
v___y_1658_ = v___x_1673_;
goto v___jp_1655_;
}
}
}
}
}
else
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1688_; 
lean_del_object(v___x_1440_);
v___x_1683_ = lean_unsigned_to_nat(1u);
v___x_1684_ = lean_nat_add(v___x_1683_, v_size_1622_);
v___x_1685_ = lean_nat_add(v___x_1684_, v_size_1623_);
lean_dec(v_size_1623_);
v___x_1686_ = lean_nat_add(v___x_1684_, v_size_1640_);
lean_dec(v___x_1684_);
lean_inc_ref(v_l_1437_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 4, v_l_1626_);
lean_ctor_set(v___x_1638_, 3, v_l_1437_);
lean_ctor_set(v___x_1638_, 2, v_v_1436_);
lean_ctor_set(v___x_1638_, 1, v_k_1435_);
lean_ctor_set(v___x_1638_, 0, v___x_1686_);
v___x_1688_ = v___x_1638_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1686_);
lean_ctor_set(v_reuseFailAlloc_1701_, 1, v_k_1435_);
lean_ctor_set(v_reuseFailAlloc_1701_, 2, v_v_1436_);
lean_ctor_set(v_reuseFailAlloc_1701_, 3, v_l_1437_);
lean_ctor_set(v_reuseFailAlloc_1701_, 4, v_l_1626_);
v___x_1688_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
v_isSharedCheck_1695_ = !lean_is_exclusive(v_l_1437_);
if (v_isSharedCheck_1695_ == 0)
{
lean_object* v_unused_1696_; lean_object* v_unused_1697_; lean_object* v_unused_1698_; lean_object* v_unused_1699_; lean_object* v_unused_1700_; 
v_unused_1696_ = lean_ctor_get(v_l_1437_, 4);
lean_dec(v_unused_1696_);
v_unused_1697_ = lean_ctor_get(v_l_1437_, 3);
lean_dec(v_unused_1697_);
v_unused_1698_ = lean_ctor_get(v_l_1437_, 2);
lean_dec(v_unused_1698_);
v_unused_1699_ = lean_ctor_get(v_l_1437_, 1);
lean_dec(v_unused_1699_);
v_unused_1700_ = lean_ctor_get(v_l_1437_, 0);
lean_dec(v_unused_1700_);
v___x_1690_ = v_l_1437_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_dec(v_l_1437_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 4, v_r_1627_);
lean_ctor_set(v___x_1690_, 3, v___x_1688_);
lean_ctor_set(v___x_1690_, 2, v_v_1625_);
lean_ctor_set(v___x_1690_, 1, v_k_1624_);
lean_ctor_set(v___x_1690_, 0, v___x_1685_);
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1685_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v_k_1624_);
lean_ctor_set(v_reuseFailAlloc_1694_, 2, v_v_1625_);
lean_ctor_set(v_reuseFailAlloc_1694_, 3, v___x_1688_);
lean_ctor_set(v_reuseFailAlloc_1694_, 4, v_r_1627_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
}
else
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
lean_dec_ref_known(v_l_1626_, 5);
lean_del_object(v___x_1638_);
lean_dec(v_v_1625_);
lean_dec(v_k_1624_);
lean_dec(v_size_1623_);
lean_dec_ref_known(v_l_1437_, 5);
lean_del_object(v___x_1440_);
lean_dec(v_v_1436_);
lean_dec(v_k_1435_);
v___x_1702_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7);
v___x_1703_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1702_);
return v___x_1703_;
}
}
else
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
lean_del_object(v___x_1638_);
lean_dec(v_r_1627_);
lean_dec(v_v_1625_);
lean_dec(v_k_1624_);
lean_dec(v_size_1623_);
lean_dec_ref_known(v_l_1437_, 5);
lean_del_object(v___x_1440_);
lean_dec(v_v_1436_);
lean_dec(v_k_1435_);
v___x_1704_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8);
v___x_1705_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1704_);
return v___x_1705_;
}
}
}
}
else
{
lean_object* v_size_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1716_; 
v_size_1712_ = lean_ctor_get(v_l_1437_, 0);
v___x_1713_ = lean_unsigned_to_nat(1u);
v___x_1714_ = lean_nat_add(v___x_1713_, v_size_1712_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 4, v___x_1621_);
lean_ctor_set(v___x_1440_, 0, v___x_1714_);
v___x_1716_ = v___x_1440_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1714_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_k_1435_);
lean_ctor_set(v_reuseFailAlloc_1717_, 2, v_v_1436_);
lean_ctor_set(v_reuseFailAlloc_1717_, 3, v_l_1437_);
lean_ctor_set(v_reuseFailAlloc_1717_, 4, v___x_1621_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
else
{
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_l_1718_; 
v_l_1718_ = lean_ctor_get(v___x_1621_, 3);
lean_inc(v_l_1718_);
if (lean_obj_tag(v_l_1718_) == 0)
{
lean_object* v_r_1719_; 
v_r_1719_ = lean_ctor_get(v___x_1621_, 4);
lean_inc(v_r_1719_);
if (lean_obj_tag(v_r_1719_) == 0)
{
lean_object* v_size_1720_; lean_object* v_k_1721_; lean_object* v_v_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1736_; 
v_size_1720_ = lean_ctor_get(v___x_1621_, 0);
v_k_1721_ = lean_ctor_get(v___x_1621_, 1);
v_v_1722_ = lean_ctor_get(v___x_1621_, 2);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1736_ == 0)
{
lean_object* v_unused_1737_; lean_object* v_unused_1738_; 
v_unused_1737_ = lean_ctor_get(v___x_1621_, 4);
lean_dec(v_unused_1737_);
v_unused_1738_ = lean_ctor_get(v___x_1621_, 3);
lean_dec(v_unused_1738_);
v___x_1724_ = v___x_1621_;
v_isShared_1725_ = v_isSharedCheck_1736_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_v_1722_);
lean_inc(v_k_1721_);
lean_inc(v_size_1720_);
lean_dec(v___x_1621_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1736_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v_size_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1731_; 
v_size_1726_ = lean_ctor_get(v_l_1718_, 0);
v___x_1727_ = lean_unsigned_to_nat(1u);
v___x_1728_ = lean_nat_add(v___x_1727_, v_size_1720_);
lean_dec(v_size_1720_);
v___x_1729_ = lean_nat_add(v___x_1727_, v_size_1726_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 4, v_l_1718_);
lean_ctor_set(v___x_1724_, 3, v_l_1437_);
lean_ctor_set(v___x_1724_, 2, v_v_1436_);
lean_ctor_set(v___x_1724_, 1, v_k_1435_);
lean_ctor_set(v___x_1724_, 0, v___x_1729_);
v___x_1731_ = v___x_1724_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1729_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_k_1435_);
lean_ctor_set(v_reuseFailAlloc_1735_, 2, v_v_1436_);
lean_ctor_set(v_reuseFailAlloc_1735_, 3, v_l_1437_);
lean_ctor_set(v_reuseFailAlloc_1735_, 4, v_l_1718_);
v___x_1731_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1733_; 
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 4, v_r_1719_);
lean_ctor_set(v___x_1440_, 3, v___x_1731_);
lean_ctor_set(v___x_1440_, 2, v_v_1722_);
lean_ctor_set(v___x_1440_, 1, v_k_1721_);
lean_ctor_set(v___x_1440_, 0, v___x_1728_);
v___x_1733_ = v___x_1440_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v___x_1728_);
lean_ctor_set(v_reuseFailAlloc_1734_, 1, v_k_1721_);
lean_ctor_set(v_reuseFailAlloc_1734_, 2, v_v_1722_);
lean_ctor_set(v_reuseFailAlloc_1734_, 3, v___x_1731_);
lean_ctor_set(v_reuseFailAlloc_1734_, 4, v_r_1719_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
else
{
lean_object* v_k_1739_; lean_object* v_v_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1764_; 
v_k_1739_ = lean_ctor_get(v___x_1621_, 1);
v_v_1740_ = lean_ctor_get(v___x_1621_, 2);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1764_ == 0)
{
lean_object* v_unused_1765_; lean_object* v_unused_1766_; lean_object* v_unused_1767_; 
v_unused_1765_ = lean_ctor_get(v___x_1621_, 4);
lean_dec(v_unused_1765_);
v_unused_1766_ = lean_ctor_get(v___x_1621_, 3);
lean_dec(v_unused_1766_);
v_unused_1767_ = lean_ctor_get(v___x_1621_, 0);
lean_dec(v_unused_1767_);
v___x_1742_ = v___x_1621_;
v_isShared_1743_ = v_isSharedCheck_1764_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_v_1740_);
lean_inc(v_k_1739_);
lean_dec(v___x_1621_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1764_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v_k_1744_; lean_object* v_v_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1760_; 
v_k_1744_ = lean_ctor_get(v_l_1718_, 1);
v_v_1745_ = lean_ctor_get(v_l_1718_, 2);
v_isSharedCheck_1760_ = !lean_is_exclusive(v_l_1718_);
if (v_isSharedCheck_1760_ == 0)
{
lean_object* v_unused_1761_; lean_object* v_unused_1762_; lean_object* v_unused_1763_; 
v_unused_1761_ = lean_ctor_get(v_l_1718_, 4);
lean_dec(v_unused_1761_);
v_unused_1762_ = lean_ctor_get(v_l_1718_, 3);
lean_dec(v_unused_1762_);
v_unused_1763_ = lean_ctor_get(v_l_1718_, 0);
lean_dec(v_unused_1763_);
v___x_1747_ = v_l_1718_;
v_isShared_1748_ = v_isSharedCheck_1760_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_v_1745_);
lean_inc(v_k_1744_);
lean_dec(v_l_1718_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1760_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1752_; 
v___x_1749_ = lean_unsigned_to_nat(3u);
v___x_1750_ = lean_unsigned_to_nat(1u);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 4, v_r_1719_);
lean_ctor_set(v___x_1747_, 3, v_r_1719_);
lean_ctor_set(v___x_1747_, 2, v_v_1436_);
lean_ctor_set(v___x_1747_, 1, v_k_1435_);
lean_ctor_set(v___x_1747_, 0, v___x_1750_);
v___x_1752_ = v___x_1747_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1750_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v_k_1435_);
lean_ctor_set(v_reuseFailAlloc_1759_, 2, v_v_1436_);
lean_ctor_set(v_reuseFailAlloc_1759_, 3, v_r_1719_);
lean_ctor_set(v_reuseFailAlloc_1759_, 4, v_r_1719_);
v___x_1752_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
lean_object* v___x_1754_; 
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 3, v_r_1719_);
lean_ctor_set(v___x_1742_, 0, v___x_1750_);
v___x_1754_ = v___x_1742_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1750_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_k_1739_);
lean_ctor_set(v_reuseFailAlloc_1758_, 2, v_v_1740_);
lean_ctor_set(v_reuseFailAlloc_1758_, 3, v_r_1719_);
lean_ctor_set(v_reuseFailAlloc_1758_, 4, v_r_1719_);
v___x_1754_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
lean_object* v___x_1756_; 
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 4, v___x_1754_);
lean_ctor_set(v___x_1440_, 3, v___x_1752_);
lean_ctor_set(v___x_1440_, 2, v_v_1745_);
lean_ctor_set(v___x_1440_, 1, v_k_1744_);
lean_ctor_set(v___x_1440_, 0, v___x_1749_);
v___x_1756_ = v___x_1440_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1749_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v_k_1744_);
lean_ctor_set(v_reuseFailAlloc_1757_, 2, v_v_1745_);
lean_ctor_set(v_reuseFailAlloc_1757_, 3, v___x_1752_);
lean_ctor_set(v_reuseFailAlloc_1757_, 4, v___x_1754_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1768_; 
v_r_1768_ = lean_ctor_get(v___x_1621_, 4);
lean_inc(v_r_1768_);
if (lean_obj_tag(v_r_1768_) == 0)
{
lean_object* v_k_1769_; lean_object* v_v_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1782_; 
v_k_1769_ = lean_ctor_get(v___x_1621_, 1);
v_v_1770_ = lean_ctor_get(v___x_1621_, 2);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1782_ == 0)
{
lean_object* v_unused_1783_; lean_object* v_unused_1784_; lean_object* v_unused_1785_; 
v_unused_1783_ = lean_ctor_get(v___x_1621_, 4);
lean_dec(v_unused_1783_);
v_unused_1784_ = lean_ctor_get(v___x_1621_, 3);
lean_dec(v_unused_1784_);
v_unused_1785_ = lean_ctor_get(v___x_1621_, 0);
lean_dec(v_unused_1785_);
v___x_1772_ = v___x_1621_;
v_isShared_1773_ = v_isSharedCheck_1782_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_v_1770_);
lean_inc(v_k_1769_);
lean_dec(v___x_1621_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1782_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1777_; 
v___x_1774_ = lean_unsigned_to_nat(3u);
v___x_1775_ = lean_unsigned_to_nat(1u);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 4, v_l_1718_);
lean_ctor_set(v___x_1772_, 2, v_v_1436_);
lean_ctor_set(v___x_1772_, 1, v_k_1435_);
lean_ctor_set(v___x_1772_, 0, v___x_1775_);
v___x_1777_ = v___x_1772_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1775_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_k_1435_);
lean_ctor_set(v_reuseFailAlloc_1781_, 2, v_v_1436_);
lean_ctor_set(v_reuseFailAlloc_1781_, 3, v_l_1718_);
lean_ctor_set(v_reuseFailAlloc_1781_, 4, v_l_1718_);
v___x_1777_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
lean_object* v___x_1779_; 
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 4, v_r_1768_);
lean_ctor_set(v___x_1440_, 3, v___x_1777_);
lean_ctor_set(v___x_1440_, 2, v_v_1770_);
lean_ctor_set(v___x_1440_, 1, v_k_1769_);
lean_ctor_set(v___x_1440_, 0, v___x_1774_);
v___x_1779_ = v___x_1440_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1774_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v_k_1769_);
lean_ctor_set(v_reuseFailAlloc_1780_, 2, v_v_1770_);
lean_ctor_set(v_reuseFailAlloc_1780_, 3, v___x_1777_);
lean_ctor_set(v_reuseFailAlloc_1780_, 4, v_r_1768_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
else
{
lean_object* v___x_1786_; lean_object* v___x_1788_; 
v___x_1786_ = lean_unsigned_to_nat(2u);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 4, v___x_1621_);
lean_ctor_set(v___x_1440_, 3, v_r_1768_);
lean_ctor_set(v___x_1440_, 0, v___x_1786_);
v___x_1788_ = v___x_1440_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1786_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v_k_1435_);
lean_ctor_set(v_reuseFailAlloc_1789_, 2, v_v_1436_);
lean_ctor_set(v_reuseFailAlloc_1789_, 3, v_r_1768_);
lean_ctor_set(v_reuseFailAlloc_1789_, 4, v___x_1621_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
else
{
lean_object* v___x_1790_; lean_object* v___x_1792_; 
v___x_1790_ = lean_unsigned_to_nat(1u);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 4, v___x_1621_);
lean_ctor_set(v___x_1440_, 3, v___x_1621_);
lean_ctor_set(v___x_1440_, 0, v___x_1790_);
v___x_1792_ = v___x_1440_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1790_);
lean_ctor_set(v_reuseFailAlloc_1793_, 1, v_k_1435_);
lean_ctor_set(v_reuseFailAlloc_1793_, 2, v_v_1436_);
lean_ctor_set(v_reuseFailAlloc_1793_, 3, v___x_1621_);
lean_ctor_set(v_reuseFailAlloc_1793_, 4, v___x_1621_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = lean_unsigned_to_nat(1u);
v___x_1796_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
lean_ctor_set(v___x_1796_, 1, v_k_1431_);
lean_ctor_set(v___x_1796_, 2, v_v_1432_);
lean_ctor_set(v___x_1796_, 3, v_t_1433_);
lean_ctor_set(v___x_1796_, 4, v_t_1433_);
return v___x_1796_;
}
}
}
static lean_object* _init_l_Lean_Json_setObjVal_x21___closed__2(void){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1799_ = ((lean_object*)(l_Lean_Json_setObjVal_x21___closed__1));
v___x_1800_ = lean_unsigned_to_nat(21u);
v___x_1801_ = lean_unsigned_to_nat(285u);
v___x_1802_ = ((lean_object*)(l_Lean_Json_setObjVal_x21___closed__0));
v___x_1803_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0));
v___x_1804_ = l_mkPanicMessageWithDecl(v___x_1803_, v___x_1802_, v___x_1801_, v___x_1800_, v___x_1799_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_setObjVal_x21(lean_object* v_x_1805_, lean_object* v_x_1806_, lean_object* v_x_1807_){
_start:
{
if (lean_obj_tag(v_x_1805_) == 5)
{
lean_object* v_kvPairs_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1816_; 
v_kvPairs_1808_ = lean_ctor_get(v_x_1805_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v_x_1805_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1810_ = v_x_1805_;
v_isShared_1811_ = v_isSharedCheck_1816_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_kvPairs_1808_);
lean_dec(v_x_1805_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1816_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1812_; lean_object* v___x_1814_; 
v___x_1812_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_x_1806_, v_x_1807_, v_kvPairs_1808_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 0, v___x_1812_);
v___x_1814_ = v___x_1810_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
else
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
lean_dec(v_x_1807_);
lean_dec_ref(v_x_1806_);
lean_dec(v_x_1805_);
v___x_1817_ = lean_obj_once(&l_Lean_Json_setObjVal_x21___closed__2, &l_Lean_Json_setObjVal_x21___closed__2_once, _init_l_Lean_Json_setObjVal_x21___closed__2);
v___x_1818_ = l_panic___at___00Lean_Json_setObjVal_x21_spec__1(v___x_1817_);
return v___x_1818_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0(lean_object* v_00_u03b2_1819_, lean_object* v_msg_1820_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v_msg_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0(lean_object* v_00_u03b2_1822_, lean_object* v_k_1823_, lean_object* v_v_1824_, lean_object* v_t_1825_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1823_, v_v_1824_, v_t_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(lean_object* v_init_1827_, lean_object* v_x_1828_){
_start:
{
if (lean_obj_tag(v_x_1828_) == 0)
{
lean_object* v_k_1829_; lean_object* v_v_1830_; lean_object* v_l_1831_; lean_object* v_r_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v_k_1829_ = lean_ctor_get(v_x_1828_, 1);
lean_inc(v_k_1829_);
v_v_1830_ = lean_ctor_get(v_x_1828_, 2);
lean_inc(v_v_1830_);
v_l_1831_ = lean_ctor_get(v_x_1828_, 3);
lean_inc(v_l_1831_);
v_r_1832_ = lean_ctor_get(v_x_1828_, 4);
lean_inc(v_r_1832_);
lean_dec_ref_known(v_x_1828_, 5);
v___x_1833_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_init_1827_, v_l_1831_);
v___x_1834_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1829_, v_v_1830_, v___x_1833_);
v_init_1827_ = v___x_1834_;
v_x_1828_ = v_r_1832_;
goto _start;
}
else
{
return v_init_1827_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mergeObj(lean_object* v_x_1836_, lean_object* v_x_1837_){
_start:
{
if (lean_obj_tag(v_x_1836_) == 5)
{
if (lean_obj_tag(v_x_1837_) == 5)
{
lean_object* v_kvPairs_1838_; lean_object* v_kvPairs_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1847_; 
v_kvPairs_1838_ = lean_ctor_get(v_x_1836_, 0);
lean_inc(v_kvPairs_1838_);
lean_dec_ref_known(v_x_1836_, 1);
v_kvPairs_1839_ = lean_ctor_get(v_x_1837_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v_x_1837_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1841_ = v_x_1837_;
v_isShared_1842_ = v_isSharedCheck_1847_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_kvPairs_1839_);
lean_dec(v_x_1837_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1847_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1843_; lean_object* v___x_1845_; 
v___x_1843_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_kvPairs_1838_, v_kvPairs_1839_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 0, v___x_1843_);
v___x_1845_ = v___x_1841_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
else
{
lean_dec_ref_known(v_x_1836_, 1);
return v_x_1837_;
}
}
else
{
lean_dec(v_x_1836_);
return v_x_1837_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0(lean_object* v_init_1848_, lean_object* v_t_1849_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_init_1848_, v_t_1849_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorIdx(lean_object* v_x_1851_){
_start:
{
if (lean_obj_tag(v_x_1851_) == 0)
{
lean_object* v___x_1852_; 
v___x_1852_ = lean_unsigned_to_nat(0u);
return v___x_1852_;
}
else
{
lean_object* v___x_1853_; 
v___x_1853_ = lean_unsigned_to_nat(1u);
return v___x_1853_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorIdx___boxed(lean_object* v_x_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_Lean_Json_Structured_ctorIdx(v_x_1854_);
lean_dec_ref(v_x_1854_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim___redArg(lean_object* v_t_1856_, lean_object* v_k_1857_){
_start:
{
if (lean_obj_tag(v_t_1856_) == 0)
{
lean_object* v_elems_1858_; lean_object* v___x_1859_; 
v_elems_1858_ = lean_ctor_get(v_t_1856_, 0);
lean_inc_ref(v_elems_1858_);
lean_dec_ref_known(v_t_1856_, 1);
v___x_1859_ = lean_apply_1(v_k_1857_, v_elems_1858_);
return v___x_1859_;
}
else
{
lean_object* v_kvPairs_1860_; lean_object* v___x_1861_; 
v_kvPairs_1860_ = lean_ctor_get(v_t_1856_, 0);
lean_inc(v_kvPairs_1860_);
lean_dec_ref_known(v_t_1856_, 1);
v___x_1861_ = lean_apply_1(v_k_1857_, v_kvPairs_1860_);
return v___x_1861_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim(lean_object* v_motive_1862_, lean_object* v_ctorIdx_1863_, lean_object* v_t_1864_, lean_object* v_h_1865_, lean_object* v_k_1866_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1864_, v_k_1866_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim___boxed(lean_object* v_motive_1868_, lean_object* v_ctorIdx_1869_, lean_object* v_t_1870_, lean_object* v_h_1871_, lean_object* v_k_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lean_Json_Structured_ctorElim(v_motive_1868_, v_ctorIdx_1869_, v_t_1870_, v_h_1871_, v_k_1872_);
lean_dec(v_ctorIdx_1869_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_arr_elim___redArg(lean_object* v_t_1874_, lean_object* v_arr_1875_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1874_, v_arr_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_arr_elim(lean_object* v_motive_1877_, lean_object* v_t_1878_, lean_object* v_h_1879_, lean_object* v_arr_1880_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1878_, v_arr_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_obj_elim___redArg(lean_object* v_t_1882_, lean_object* v_obj_1883_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1882_, v_obj_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_obj_elim(lean_object* v_motive_1885_, lean_object* v_t_1886_, lean_object* v_h_1887_, lean_object* v_obj_1888_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1886_, v_obj_1888_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeArrayStructured___lam__0(lean_object* v_elems_1890_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1891_, 0, v_elems_1890_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeRawStringStructured___lam__0(lean_object* v_kvPairs_1894_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1895_, 0, v_kvPairs_1894_);
return v___x_1895_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Json_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
