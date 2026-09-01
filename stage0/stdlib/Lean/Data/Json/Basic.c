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
uint8_t v___y_146_; uint8_t v___y_147_; lean_object* v_fst_148_; lean_object* v_snd_149_; lean_object* v_fst_152_; lean_object* v_snd_153_; lean_object* v___x_171_; lean_object* v_fst_172_; lean_object* v_snd_173_; lean_object* v___x_174_; lean_object* v_fst_175_; lean_object* v_snd_176_; lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
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
if (v___y_146_ == 0)
{
if (v___y_147_ == 0)
{
uint8_t v___x_150_; 
v___x_150_ = lean_nat_dec_lt(v_fst_148_, v_snd_149_);
lean_dec(v_snd_149_);
lean_dec(v_fst_148_);
return v___x_150_;
}
else
{
lean_dec(v_snd_149_);
lean_dec(v_fst_148_);
return v___y_146_;
}
}
else
{
lean_dec(v_snd_149_);
lean_dec(v_fst_148_);
return v___y_146_;
}
}
v___jp_151_:
{
lean_object* v_fst_154_; lean_object* v_snd_155_; lean_object* v_fst_156_; lean_object* v_snd_157_; lean_object* v_amDigits_158_; lean_object* v_bmDigits_159_; uint8_t v___x_160_; uint8_t v___x_161_; uint8_t v___x_162_; 
v_fst_154_ = lean_ctor_get(v_fst_152_, 0);
lean_inc_n(v_fst_154_, 2);
v_snd_155_ = lean_ctor_get(v_fst_152_, 1);
lean_inc(v_snd_155_);
lean_dec_ref(v_fst_152_);
v_fst_156_ = lean_ctor_get(v_snd_153_, 0);
lean_inc_n(v_fst_156_, 2);
v_snd_157_ = lean_ctor_get(v_snd_153_, 1);
lean_inc(v_snd_157_);
lean_dec_ref(v_snd_153_);
v_amDigits_158_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(v_fst_154_);
v_bmDigits_159_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(v_fst_156_);
v___x_160_ = lean_int_dec_lt(v_snd_155_, v_snd_157_);
v___x_161_ = lean_int_dec_lt(v_snd_157_, v_snd_155_);
lean_dec(v_snd_155_);
lean_dec(v_snd_157_);
v___x_162_ = lean_nat_dec_lt(v_amDigits_158_, v_bmDigits_159_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_163_ = lean_unsigned_to_nat(10u);
v___x_164_ = lean_nat_sub(v_amDigits_158_, v_bmDigits_159_);
lean_dec(v_bmDigits_159_);
lean_dec(v_amDigits_158_);
v___x_165_ = lean_nat_pow(v___x_163_, v___x_164_);
lean_dec(v___x_164_);
v___x_166_ = lean_nat_mul(v_fst_156_, v___x_165_);
lean_dec(v___x_165_);
lean_dec(v_fst_156_);
v___y_146_ = v___x_160_;
v___y_147_ = v___x_161_;
v_fst_148_ = v_fst_154_;
v_snd_149_ = v___x_166_;
goto v___jp_145_;
}
else
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_167_ = lean_unsigned_to_nat(10u);
v___x_168_ = lean_nat_sub(v_bmDigits_159_, v_amDigits_158_);
lean_dec(v_amDigits_158_);
lean_dec(v_bmDigits_159_);
v___x_169_ = lean_nat_pow(v___x_167_, v___x_168_);
lean_dec(v___x_168_);
v___x_170_ = lean_nat_mul(v_fst_154_, v___x_169_);
lean_dec(v___x_169_);
lean_dec(v_fst_154_);
v___y_146_ = v___x_160_;
v___y_147_ = v___x_161_;
v_fst_148_ = v___x_170_;
v_snd_149_ = v_fst_156_;
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
v_fst_152_ = v_snd_173_;
v_snd_153_ = v_snd_176_;
goto v___jp_151_;
}
else
{
uint8_t v___x_180_; 
v___x_180_ = lean_int_dec_eq(v_fst_175_, v___x_178_);
lean_dec(v_fst_175_);
if (v___x_180_ == 0)
{
v_fst_152_ = v_snd_173_;
v_snd_153_ = v_snd_176_;
goto v___jp_151_;
}
else
{
v_fst_152_ = v_snd_176_;
v_snd_153_ = v_snd_173_;
goto v___jp_151_;
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
lean_object* v___y_240_; lean_object* v___y_241_; lean_object* v___y_242_; lean_object* v___y_243_; lean_object* v_mantissa_249_; lean_object* v_exponent_250_; lean_object* v___x_251_; lean_object* v___y_253_; lean_object* v___y_254_; uint8_t v___y_255_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; uint8_t v___x_271_; 
v_mantissa_249_ = lean_ctor_get(v_x_238_, 0);
lean_inc(v_mantissa_249_);
v_exponent_250_ = lean_ctor_get(v_x_238_, 1);
lean_inc(v_exponent_250_);
lean_dec_ref(v_x_238_);
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_271_ = lean_nat_dec_eq(v_exponent_250_, v___x_251_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; lean_object* v___y_274_; lean_object* v___y_275_; lean_object* v___y_276_; lean_object* v___y_288_; uint8_t v___x_297_; 
v___x_272_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v___x_297_ = lean_int_dec_le(v___x_272_, v_mantissa_249_);
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
v___jp_273_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v_e_x27_280_; lean_object* v___x_281_; lean_object* v_left_282_; uint8_t v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_277_ = lean_unsigned_to_nat(10u);
v___x_278_ = lean_nat_abs(v___y_276_);
v___x_279_ = lean_nat_sub(v_exponent_250_, v___x_278_);
lean_dec(v___x_278_);
lean_dec(v_exponent_250_);
v_e_x27_280_ = lean_nat_pow(v___x_277_, v___x_279_);
lean_dec(v___x_279_);
v___x_281_ = lean_nat_div(v___y_274_, v_e_x27_280_);
v_left_282_ = l_Nat_reprFast(v___x_281_);
v___x_283_ = lean_int_dec_eq(v___y_276_, v___x_272_);
v___x_284_ = lean_nat_mod(v___y_274_, v_e_x27_280_);
lean_dec(v___y_274_);
v___x_285_ = lean_nat_dec_eq(v___x_284_, v___x_251_);
if (v___x_285_ == 0)
{
v___y_253_ = v_left_282_;
v___y_254_ = v___y_275_;
v___y_255_ = v___x_283_;
v___y_256_ = v___x_284_;
v___y_257_ = v_e_x27_280_;
v___y_258_ = v___y_276_;
goto v___jp_252_;
}
else
{
if (v___x_283_ == 0)
{
v___y_253_ = v_left_282_;
v___y_254_ = v___y_275_;
v___y_255_ = v___x_283_;
v___y_256_ = v___x_284_;
v___y_257_ = v_e_x27_280_;
v___y_258_ = v___y_276_;
goto v___jp_252_;
}
else
{
lean_object* v___x_286_; 
lean_dec(v___x_284_);
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
v___x_296_ = lean_int_dec_lt(v_exp_295_, v___x_272_);
if (v___x_296_ == 0)
{
lean_dec(v_exp_295_);
v___y_274_ = v_m_289_;
v___y_275_ = v___y_288_;
v___y_276_ = v___x_272_;
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
lean_inc_ref(v___y_241_);
v___x_244_ = lean_string_append(v___y_241_, v___y_240_);
lean_dec_ref(v___y_240_);
v___x_245_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__0));
v___x_246_ = lean_string_append(v___x_244_, v___x_245_);
v___x_247_ = lean_string_append(v___x_246_, v___y_242_);
lean_dec_ref(v___y_242_);
v___x_248_ = lean_string_append(v___x_247_, v___y_243_);
lean_dec_ref(v___y_243_);
return v___x_248_;
}
v___jp_252_:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v_e_265_; lean_object* v_right_266_; 
v___x_259_ = lean_nat_add(v___y_257_, v___y_256_);
lean_dec(v___y_256_);
lean_dec(v___y_257_);
v___x_260_ = l_Nat_reprFast(v___x_259_);
v___x_261_ = lean_string_utf8_byte_size(v___x_260_);
lean_inc_ref(v___x_260_);
v___x_262_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_262_, 0, v___x_260_);
lean_ctor_set(v___x_262_, 1, v___x_251_);
lean_ctor_set(v___x_262_, 2, v___x_261_);
v___x_263_ = lean_unsigned_to_nat(1u);
v___x_264_ = l_Substring_Raw_nextn(v___x_262_, v___x_263_, v___x_251_);
lean_dec_ref_known(v___x_262_, 3);
v_e_265_ = l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0(v___x_260_, v___x_264_, v___x_261_);
v_right_266_ = lean_string_utf8_extract(v___x_260_, v___x_264_, v_e_265_);
lean_dec(v_e_265_);
lean_dec(v___x_264_);
lean_dec_ref(v___x_260_);
if (v___y_255_ == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_267_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__1));
v___x_268_ = l_Int_repr(v___y_258_);
lean_dec(v___y_258_);
v___x_269_ = lean_string_append(v___x_267_, v___x_268_);
lean_dec_ref(v___x_268_);
v___y_240_ = v___y_253_;
v___y_241_ = v___y_254_;
v___y_242_ = v_right_266_;
v___y_243_ = v___x_269_;
goto v___jp_239_;
}
else
{
lean_object* v___x_270_; 
lean_dec(v___y_258_);
v___x_270_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__2));
v___y_240_ = v___y_253_;
v___y_241_ = v___y_254_;
v___y_242_ = v_right_266_;
v___y_243_ = v___x_270_;
goto v___jp_239_;
}
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
static uint64_t _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__0(void){
_start:
{
uint64_t v___x_788_; uint64_t v___x_789_; 
v___x_788_ = 13ULL;
v___x_789_ = lean_uint64_mix_hash(v___x_788_, v___x_788_);
return v___x_789_;
}
}
static uint64_t _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__1(void){
_start:
{
uint64_t v___x_790_; uint64_t v___x_791_; uint64_t v___x_792_; 
v___x_790_ = 11ULL;
v___x_791_ = 13ULL;
v___x_792_ = lean_uint64_mix_hash(v___x_791_, v___x_790_);
return v___x_792_;
}
}
static uint64_t _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2(void){
_start:
{
uint64_t v___x_793_; uint64_t v___x_794_; uint64_t v___x_795_; 
v___x_793_ = 7ULL;
v___x_794_ = 23ULL;
v___x_795_ = lean_uint64_mix_hash(v___x_794_, v___x_793_);
return v___x_795_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(lean_object* v_as_796_, size_t v_i_797_, size_t v_stop_798_, uint64_t v_b_799_){
_start:
{
uint8_t v___x_800_; 
v___x_800_ = lean_usize_dec_eq(v_i_797_, v_stop_798_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; uint64_t v___x_802_; uint64_t v___x_803_; size_t v___x_804_; size_t v___x_805_; 
v___x_801_ = lean_array_uget_borrowed(v_as_796_, v_i_797_);
v___x_802_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v___x_801_);
v___x_803_ = lean_uint64_mix_hash(v_b_799_, v___x_802_);
v___x_804_ = ((size_t)1ULL);
v___x_805_ = lean_usize_add(v_i_797_, v___x_804_);
v_i_797_ = v___x_805_;
v_b_799_ = v___x_803_;
goto _start;
}
else
{
return v_b_799_;
}
}
}
LEAN_EXPORT uint64_t l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(lean_object* v_x_807_){
_start:
{
switch(lean_obj_tag(v_x_807_))
{
case 0:
{
uint64_t v___x_808_; 
v___x_808_ = 11ULL;
return v___x_808_;
}
case 1:
{
uint8_t v_b_809_; 
v_b_809_ = lean_ctor_get_uint8(v_x_807_, 0);
if (v_b_809_ == 0)
{
uint64_t v___x_810_; 
v___x_810_ = lean_uint64_once(&l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__0, &l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__0_once, _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__0);
return v___x_810_;
}
else
{
uint64_t v___x_811_; 
v___x_811_ = lean_uint64_once(&l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__1, &l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__1_once, _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__1);
return v___x_811_;
}
}
case 2:
{
lean_object* v_n_812_; uint64_t v___x_813_; uint64_t v___x_814_; uint64_t v___x_815_; 
v_n_812_ = lean_ctor_get(v_x_807_, 0);
v___x_813_ = 17ULL;
v___x_814_ = l_Lean_instHashableJsonNumber_hash(v_n_812_);
v___x_815_ = lean_uint64_mix_hash(v___x_813_, v___x_814_);
return v___x_815_;
}
case 3:
{
lean_object* v_s_816_; uint64_t v___x_817_; uint64_t v___x_818_; uint64_t v___x_819_; 
v_s_816_ = lean_ctor_get(v_x_807_, 0);
v___x_817_ = 19ULL;
v___x_818_ = lean_string_hash(v_s_816_);
v___x_819_ = lean_uint64_mix_hash(v___x_817_, v___x_818_);
return v___x_819_;
}
case 4:
{
lean_object* v_elems_820_; uint64_t v___x_821_; uint64_t v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
v_elems_820_ = lean_ctor_get(v_x_807_, 0);
v___x_821_ = 23ULL;
v___x_822_ = 7ULL;
v___x_823_ = lean_unsigned_to_nat(0u);
v___x_824_ = lean_array_get_size(v_elems_820_);
v___x_825_ = lean_nat_dec_lt(v___x_823_, v___x_824_);
if (v___x_825_ == 0)
{
uint64_t v___x_826_; 
v___x_826_ = lean_uint64_once(&l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2, &l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2_once, _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2);
return v___x_826_;
}
else
{
uint8_t v___x_827_; 
v___x_827_ = lean_nat_dec_le(v___x_824_, v___x_824_);
if (v___x_827_ == 0)
{
if (v___x_825_ == 0)
{
uint64_t v___x_828_; 
v___x_828_ = lean_uint64_once(&l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2, &l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2_once, _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2);
return v___x_828_;
}
else
{
size_t v___x_829_; size_t v___x_830_; uint64_t v___x_831_; uint64_t v___x_832_; 
v___x_829_ = ((size_t)0ULL);
v___x_830_ = lean_usize_of_nat(v___x_824_);
v___x_831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_elems_820_, v___x_829_, v___x_830_, v___x_822_);
v___x_832_ = lean_uint64_mix_hash(v___x_821_, v___x_831_);
return v___x_832_;
}
}
else
{
size_t v___x_833_; size_t v___x_834_; uint64_t v___x_835_; uint64_t v___x_836_; 
v___x_833_ = ((size_t)0ULL);
v___x_834_ = lean_usize_of_nat(v___x_824_);
v___x_835_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_elems_820_, v___x_833_, v___x_834_, v___x_822_);
v___x_836_ = lean_uint64_mix_hash(v___x_821_, v___x_835_);
return v___x_836_;
}
}
}
default: 
{
lean_object* v_kvPairs_837_; uint64_t v___x_838_; uint64_t v___x_839_; uint64_t v___x_840_; uint64_t v___x_841_; 
v_kvPairs_837_ = lean_ctor_get(v_x_807_, 0);
v___x_838_ = 29ULL;
v___x_839_ = 7ULL;
v___x_840_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v___x_839_, v_kvPairs_837_);
v___x_841_ = lean_uint64_mix_hash(v___x_838_, v___x_840_);
return v___x_841_;
}
}
}
}
LEAN_EXPORT uint64_t l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(uint64_t v_init_842_, lean_object* v_x_843_){
_start:
{
if (lean_obj_tag(v_x_843_) == 0)
{
lean_object* v_k_844_; lean_object* v_v_845_; lean_object* v_l_846_; lean_object* v_r_847_; uint64_t v___x_848_; uint64_t v___x_849_; uint64_t v___x_850_; uint64_t v___x_851_; uint64_t v___x_852_; 
v_k_844_ = lean_ctor_get(v_x_843_, 1);
v_v_845_ = lean_ctor_get(v_x_843_, 2);
v_l_846_ = lean_ctor_get(v_x_843_, 3);
v_r_847_ = lean_ctor_get(v_x_843_, 4);
v___x_848_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_842_, v_l_846_);
v___x_849_ = lean_string_hash(v_k_844_);
v___x_850_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_v_845_);
v___x_851_ = lean_uint64_mix_hash(v___x_849_, v___x_850_);
v___x_852_ = lean_uint64_mix_hash(v___x_848_, v___x_851_);
v_init_842_ = v___x_852_;
v_x_843_ = v_r_847_;
goto _start;
}
else
{
return v_init_842_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1___boxed(lean_object* v_init_854_, lean_object* v_x_855_){
_start:
{
uint64_t v_init_boxed_856_; uint64_t v_res_857_; lean_object* v_r_858_; 
v_init_boxed_856_ = lean_unbox_uint64(v_init_854_);
lean_dec_ref(v_init_854_);
v_res_857_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_boxed_856_, v_x_855_);
lean_dec(v_x_855_);
v_r_858_ = lean_box_uint64(v_res_857_);
return v_r_858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0___boxed(lean_object* v_as_859_, lean_object* v_i_860_, lean_object* v_stop_861_, lean_object* v_b_862_){
_start:
{
size_t v_i_boxed_863_; size_t v_stop_boxed_864_; uint64_t v_b_boxed_865_; uint64_t v_res_866_; lean_object* v_r_867_; 
v_i_boxed_863_ = lean_unbox_usize(v_i_860_);
lean_dec(v_i_860_);
v_stop_boxed_864_ = lean_unbox_usize(v_stop_861_);
lean_dec(v_stop_861_);
v_b_boxed_865_ = lean_unbox_uint64(v_b_862_);
lean_dec_ref(v_b_862_);
v_res_866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_as_859_, v_i_boxed_863_, v_stop_boxed_864_, v_b_boxed_865_);
lean_dec_ref(v_as_859_);
v_r_867_ = lean_box_uint64(v_res_866_);
return v_r_867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___boxed(lean_object* v_x_868_){
_start:
{
uint64_t v_res_869_; lean_object* v_r_870_; 
v_res_869_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_x_868_);
lean_dec(v_x_868_);
v_r_870_ = lean_box_uint64(v_res_869_);
return v_r_870_;
}
}
LEAN_EXPORT uint64_t l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1(uint64_t v_init_871_, lean_object* v_t_872_){
_start:
{
uint64_t v___x_873_; 
v___x_873_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_871_, v_t_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1___boxed(lean_object* v_init_874_, lean_object* v_t_875_){
_start:
{
uint64_t v_init_boxed_876_; uint64_t v_res_877_; lean_object* v_r_878_; 
v_init_boxed_876_ = lean_unbox_uint64(v_init_874_);
lean_dec_ref(v_init_874_);
v_res_877_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1(v_init_boxed_876_, v_t_875_);
lean_dec(v_t_875_);
v_r_878_ = lean_box_uint64(v_res_877_);
return v_r_878_;
}
}
LEAN_EXPORT uint64_t l_Lean_Json_instHashable___private__1(lean_object* v_a_879_){
_start:
{
uint64_t v___x_880_; 
v___x_880_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_a_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instHashable___private__1___boxed(lean_object* v_a_881_){
_start:
{
uint64_t v_res_882_; lean_object* v_r_883_; 
v_res_882_ = l_Lean_Json_instHashable___private__1(v_a_881_);
lean_dec(v_a_881_);
v_r_883_ = lean_box_uint64(v_res_882_);
return v_r_883_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(lean_object* v_k_886_, lean_object* v_v_887_, lean_object* v_t_888_){
_start:
{
if (lean_obj_tag(v_t_888_) == 0)
{
lean_object* v_size_889_; lean_object* v_k_890_; lean_object* v_v_891_; lean_object* v_l_892_; lean_object* v_r_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_1173_; 
v_size_889_ = lean_ctor_get(v_t_888_, 0);
v_k_890_ = lean_ctor_get(v_t_888_, 1);
v_v_891_ = lean_ctor_get(v_t_888_, 2);
v_l_892_ = lean_ctor_get(v_t_888_, 3);
v_r_893_ = lean_ctor_get(v_t_888_, 4);
v_isSharedCheck_1173_ = !lean_is_exclusive(v_t_888_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_895_ = v_t_888_;
v_isShared_896_ = v_isSharedCheck_1173_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_r_893_);
lean_inc(v_l_892_);
lean_inc(v_v_891_);
lean_inc(v_k_890_);
lean_inc(v_size_889_);
lean_dec(v_t_888_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_1173_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
uint8_t v___x_897_; 
v___x_897_ = lean_string_compare(v_k_886_, v_k_890_);
switch(v___x_897_)
{
case 0:
{
lean_object* v_impl_898_; lean_object* v___x_899_; 
lean_dec(v_size_889_);
v_impl_898_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_886_, v_v_887_, v_l_892_);
v___x_899_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_893_) == 0)
{
lean_object* v_size_900_; lean_object* v_size_901_; lean_object* v_k_902_; lean_object* v_v_903_; lean_object* v_l_904_; lean_object* v_r_905_; lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v_size_900_ = lean_ctor_get(v_r_893_, 0);
v_size_901_ = lean_ctor_get(v_impl_898_, 0);
lean_inc(v_size_901_);
v_k_902_ = lean_ctor_get(v_impl_898_, 1);
lean_inc(v_k_902_);
v_v_903_ = lean_ctor_get(v_impl_898_, 2);
lean_inc(v_v_903_);
v_l_904_ = lean_ctor_get(v_impl_898_, 3);
lean_inc(v_l_904_);
v_r_905_ = lean_ctor_get(v_impl_898_, 4);
lean_inc(v_r_905_);
v___x_906_ = lean_unsigned_to_nat(3u);
v___x_907_ = lean_nat_mul(v___x_906_, v_size_900_);
v___x_908_ = lean_nat_dec_lt(v___x_907_, v_size_901_);
lean_dec(v___x_907_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_912_; 
lean_dec(v_r_905_);
lean_dec(v_l_904_);
lean_dec(v_v_903_);
lean_dec(v_k_902_);
v___x_909_ = lean_nat_add(v___x_899_, v_size_901_);
lean_dec(v_size_901_);
v___x_910_ = lean_nat_add(v___x_909_, v_size_900_);
lean_dec(v___x_909_);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 3, v_impl_898_);
lean_ctor_set(v___x_895_, 0, v___x_910_);
v___x_912_ = v___x_895_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_910_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_k_890_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v_v_891_);
lean_ctor_set(v_reuseFailAlloc_913_, 3, v_impl_898_);
lean_ctor_set(v_reuseFailAlloc_913_, 4, v_r_893_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
else
{
lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_979_; 
v_isSharedCheck_979_ = !lean_is_exclusive(v_impl_898_);
if (v_isSharedCheck_979_ == 0)
{
lean_object* v_unused_980_; lean_object* v_unused_981_; lean_object* v_unused_982_; lean_object* v_unused_983_; lean_object* v_unused_984_; 
v_unused_980_ = lean_ctor_get(v_impl_898_, 4);
lean_dec(v_unused_980_);
v_unused_981_ = lean_ctor_get(v_impl_898_, 3);
lean_dec(v_unused_981_);
v_unused_982_ = lean_ctor_get(v_impl_898_, 2);
lean_dec(v_unused_982_);
v_unused_983_ = lean_ctor_get(v_impl_898_, 1);
lean_dec(v_unused_983_);
v_unused_984_ = lean_ctor_get(v_impl_898_, 0);
lean_dec(v_unused_984_);
v___x_915_ = v_impl_898_;
v_isShared_916_ = v_isSharedCheck_979_;
goto v_resetjp_914_;
}
else
{
lean_dec(v_impl_898_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_979_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v_size_917_; lean_object* v_size_918_; lean_object* v_k_919_; lean_object* v_v_920_; lean_object* v_l_921_; lean_object* v_r_922_; lean_object* v___x_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v_size_917_ = lean_ctor_get(v_l_904_, 0);
v_size_918_ = lean_ctor_get(v_r_905_, 0);
v_k_919_ = lean_ctor_get(v_r_905_, 1);
v_v_920_ = lean_ctor_get(v_r_905_, 2);
v_l_921_ = lean_ctor_get(v_r_905_, 3);
v_r_922_ = lean_ctor_get(v_r_905_, 4);
v___x_923_ = lean_unsigned_to_nat(2u);
v___x_924_ = lean_nat_mul(v___x_923_, v_size_917_);
v___x_925_ = lean_nat_dec_lt(v_size_918_, v___x_924_);
lean_dec(v___x_924_);
if (v___x_925_ == 0)
{
lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_954_; 
lean_inc(v_r_922_);
lean_inc(v_l_921_);
lean_inc(v_v_920_);
lean_inc(v_k_919_);
v_isSharedCheck_954_ = !lean_is_exclusive(v_r_905_);
if (v_isSharedCheck_954_ == 0)
{
lean_object* v_unused_955_; lean_object* v_unused_956_; lean_object* v_unused_957_; lean_object* v_unused_958_; lean_object* v_unused_959_; 
v_unused_955_ = lean_ctor_get(v_r_905_, 4);
lean_dec(v_unused_955_);
v_unused_956_ = lean_ctor_get(v_r_905_, 3);
lean_dec(v_unused_956_);
v_unused_957_ = lean_ctor_get(v_r_905_, 2);
lean_dec(v_unused_957_);
v_unused_958_ = lean_ctor_get(v_r_905_, 1);
lean_dec(v_unused_958_);
v_unused_959_ = lean_ctor_get(v_r_905_, 0);
lean_dec(v_unused_959_);
v___x_927_ = v_r_905_;
v_isShared_928_ = v_isSharedCheck_954_;
goto v_resetjp_926_;
}
else
{
lean_dec(v_r_905_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_954_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___x_942_; lean_object* v___y_944_; 
v___x_929_ = lean_nat_add(v___x_899_, v_size_901_);
lean_dec(v_size_901_);
v___x_930_ = lean_nat_add(v___x_929_, v_size_900_);
lean_dec(v___x_929_);
v___x_942_ = lean_nat_add(v___x_899_, v_size_917_);
if (lean_obj_tag(v_l_921_) == 0)
{
lean_object* v_size_952_; 
v_size_952_ = lean_ctor_get(v_l_921_, 0);
lean_inc(v_size_952_);
v___y_944_ = v_size_952_;
goto v___jp_943_;
}
else
{
lean_object* v___x_953_; 
v___x_953_ = lean_unsigned_to_nat(0u);
v___y_944_ = v___x_953_;
goto v___jp_943_;
}
v___jp_931_:
{
lean_object* v___x_935_; lean_object* v___x_937_; 
v___x_935_ = lean_nat_add(v___y_932_, v___y_934_);
lean_dec(v___y_934_);
lean_dec(v___y_932_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 4, v_r_893_);
lean_ctor_set(v___x_927_, 3, v_r_922_);
lean_ctor_set(v___x_927_, 2, v_v_891_);
lean_ctor_set(v___x_927_, 1, v_k_890_);
lean_ctor_set(v___x_927_, 0, v___x_935_);
v___x_937_ = v___x_927_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_935_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_k_890_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_v_891_);
lean_ctor_set(v_reuseFailAlloc_941_, 3, v_r_922_);
lean_ctor_set(v_reuseFailAlloc_941_, 4, v_r_893_);
v___x_937_ = v_reuseFailAlloc_941_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
lean_object* v___x_939_; 
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 4, v___x_937_);
lean_ctor_set(v___x_915_, 3, v___y_933_);
lean_ctor_set(v___x_915_, 2, v_v_920_);
lean_ctor_set(v___x_915_, 1, v_k_919_);
lean_ctor_set(v___x_915_, 0, v___x_930_);
v___x_939_ = v___x_915_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_930_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v_k_919_);
lean_ctor_set(v_reuseFailAlloc_940_, 2, v_v_920_);
lean_ctor_set(v_reuseFailAlloc_940_, 3, v___y_933_);
lean_ctor_set(v_reuseFailAlloc_940_, 4, v___x_937_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
v___jp_943_:
{
lean_object* v___x_945_; lean_object* v___x_947_; 
v___x_945_ = lean_nat_add(v___x_942_, v___y_944_);
lean_dec(v___y_944_);
lean_dec(v___x_942_);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 4, v_l_921_);
lean_ctor_set(v___x_895_, 3, v_l_904_);
lean_ctor_set(v___x_895_, 2, v_v_903_);
lean_ctor_set(v___x_895_, 1, v_k_902_);
lean_ctor_set(v___x_895_, 0, v___x_945_);
v___x_947_ = v___x_895_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_k_902_);
lean_ctor_set(v_reuseFailAlloc_951_, 2, v_v_903_);
lean_ctor_set(v_reuseFailAlloc_951_, 3, v_l_904_);
lean_ctor_set(v_reuseFailAlloc_951_, 4, v_l_921_);
v___x_947_ = v_reuseFailAlloc_951_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_948_; 
v___x_948_ = lean_nat_add(v___x_899_, v_size_900_);
if (lean_obj_tag(v_r_922_) == 0)
{
lean_object* v_size_949_; 
v_size_949_ = lean_ctor_get(v_r_922_, 0);
lean_inc(v_size_949_);
v___y_932_ = v___x_948_;
v___y_933_ = v___x_947_;
v___y_934_ = v_size_949_;
goto v___jp_931_;
}
else
{
lean_object* v___x_950_; 
v___x_950_ = lean_unsigned_to_nat(0u);
v___y_932_ = v___x_948_;
v___y_933_ = v___x_947_;
v___y_934_ = v___x_950_;
goto v___jp_931_;
}
}
}
}
}
else
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_965_; 
lean_del_object(v___x_895_);
v___x_960_ = lean_nat_add(v___x_899_, v_size_901_);
lean_dec(v_size_901_);
v___x_961_ = lean_nat_add(v___x_960_, v_size_900_);
lean_dec(v___x_960_);
v___x_962_ = lean_nat_add(v___x_899_, v_size_900_);
v___x_963_ = lean_nat_add(v___x_962_, v_size_918_);
lean_dec(v___x_962_);
lean_inc_ref(v_r_893_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 4, v_r_893_);
lean_ctor_set(v___x_915_, 3, v_r_905_);
lean_ctor_set(v___x_915_, 2, v_v_891_);
lean_ctor_set(v___x_915_, 1, v_k_890_);
lean_ctor_set(v___x_915_, 0, v___x_963_);
v___x_965_ = v___x_915_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_963_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_k_890_);
lean_ctor_set(v_reuseFailAlloc_978_, 2, v_v_891_);
lean_ctor_set(v_reuseFailAlloc_978_, 3, v_r_905_);
lean_ctor_set(v_reuseFailAlloc_978_, 4, v_r_893_);
v___x_965_ = v_reuseFailAlloc_978_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
v_isSharedCheck_972_ = !lean_is_exclusive(v_r_893_);
if (v_isSharedCheck_972_ == 0)
{
lean_object* v_unused_973_; lean_object* v_unused_974_; lean_object* v_unused_975_; lean_object* v_unused_976_; lean_object* v_unused_977_; 
v_unused_973_ = lean_ctor_get(v_r_893_, 4);
lean_dec(v_unused_973_);
v_unused_974_ = lean_ctor_get(v_r_893_, 3);
lean_dec(v_unused_974_);
v_unused_975_ = lean_ctor_get(v_r_893_, 2);
lean_dec(v_unused_975_);
v_unused_976_ = lean_ctor_get(v_r_893_, 1);
lean_dec(v_unused_976_);
v_unused_977_ = lean_ctor_get(v_r_893_, 0);
lean_dec(v_unused_977_);
v___x_967_ = v_r_893_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_dec(v_r_893_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 4, v___x_965_);
lean_ctor_set(v___x_967_, 3, v_l_904_);
lean_ctor_set(v___x_967_, 2, v_v_903_);
lean_ctor_set(v___x_967_, 1, v_k_902_);
lean_ctor_set(v___x_967_, 0, v___x_961_);
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v_k_902_);
lean_ctor_set(v_reuseFailAlloc_971_, 2, v_v_903_);
lean_ctor_set(v_reuseFailAlloc_971_, 3, v_l_904_);
lean_ctor_set(v_reuseFailAlloc_971_, 4, v___x_965_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_985_; 
v_l_985_ = lean_ctor_get(v_impl_898_, 3);
lean_inc(v_l_985_);
if (lean_obj_tag(v_l_985_) == 0)
{
lean_object* v_r_986_; lean_object* v_k_987_; lean_object* v_v_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_999_; 
v_r_986_ = lean_ctor_get(v_impl_898_, 4);
v_k_987_ = lean_ctor_get(v_impl_898_, 1);
v_v_988_ = lean_ctor_get(v_impl_898_, 2);
v_isSharedCheck_999_ = !lean_is_exclusive(v_impl_898_);
if (v_isSharedCheck_999_ == 0)
{
lean_object* v_unused_1000_; lean_object* v_unused_1001_; 
v_unused_1000_ = lean_ctor_get(v_impl_898_, 3);
lean_dec(v_unused_1000_);
v_unused_1001_ = lean_ctor_get(v_impl_898_, 0);
lean_dec(v_unused_1001_);
v___x_990_ = v_impl_898_;
v_isShared_991_ = v_isSharedCheck_999_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_r_986_);
lean_inc(v_v_988_);
lean_inc(v_k_987_);
lean_dec(v_impl_898_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_999_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_992_; lean_object* v___x_994_; 
v___x_992_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_986_);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 3, v_r_986_);
lean_ctor_set(v___x_990_, 2, v_v_891_);
lean_ctor_set(v___x_990_, 1, v_k_890_);
lean_ctor_set(v___x_990_, 0, v___x_899_);
v___x_994_ = v___x_990_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_k_890_);
lean_ctor_set(v_reuseFailAlloc_998_, 2, v_v_891_);
lean_ctor_set(v_reuseFailAlloc_998_, 3, v_r_986_);
lean_ctor_set(v_reuseFailAlloc_998_, 4, v_r_986_);
v___x_994_ = v_reuseFailAlloc_998_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
lean_object* v___x_996_; 
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 4, v___x_994_);
lean_ctor_set(v___x_895_, 3, v_l_985_);
lean_ctor_set(v___x_895_, 2, v_v_988_);
lean_ctor_set(v___x_895_, 1, v_k_987_);
lean_ctor_set(v___x_895_, 0, v___x_992_);
v___x_996_ = v___x_895_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_992_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_k_987_);
lean_ctor_set(v_reuseFailAlloc_997_, 2, v_v_988_);
lean_ctor_set(v_reuseFailAlloc_997_, 3, v_l_985_);
lean_ctor_set(v_reuseFailAlloc_997_, 4, v___x_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
else
{
lean_object* v_r_1002_; 
v_r_1002_ = lean_ctor_get(v_impl_898_, 4);
lean_inc(v_r_1002_);
if (lean_obj_tag(v_r_1002_) == 0)
{
lean_object* v_k_1003_; lean_object* v_v_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1027_; 
v_k_1003_ = lean_ctor_get(v_impl_898_, 1);
v_v_1004_ = lean_ctor_get(v_impl_898_, 2);
v_isSharedCheck_1027_ = !lean_is_exclusive(v_impl_898_);
if (v_isSharedCheck_1027_ == 0)
{
lean_object* v_unused_1028_; lean_object* v_unused_1029_; lean_object* v_unused_1030_; 
v_unused_1028_ = lean_ctor_get(v_impl_898_, 4);
lean_dec(v_unused_1028_);
v_unused_1029_ = lean_ctor_get(v_impl_898_, 3);
lean_dec(v_unused_1029_);
v_unused_1030_ = lean_ctor_get(v_impl_898_, 0);
lean_dec(v_unused_1030_);
v___x_1006_ = v_impl_898_;
v_isShared_1007_ = v_isSharedCheck_1027_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_v_1004_);
lean_inc(v_k_1003_);
lean_dec(v_impl_898_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1027_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v_k_1008_; lean_object* v_v_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1023_; 
v_k_1008_ = lean_ctor_get(v_r_1002_, 1);
v_v_1009_ = lean_ctor_get(v_r_1002_, 2);
v_isSharedCheck_1023_ = !lean_is_exclusive(v_r_1002_);
if (v_isSharedCheck_1023_ == 0)
{
lean_object* v_unused_1024_; lean_object* v_unused_1025_; lean_object* v_unused_1026_; 
v_unused_1024_ = lean_ctor_get(v_r_1002_, 4);
lean_dec(v_unused_1024_);
v_unused_1025_ = lean_ctor_get(v_r_1002_, 3);
lean_dec(v_unused_1025_);
v_unused_1026_ = lean_ctor_get(v_r_1002_, 0);
lean_dec(v_unused_1026_);
v___x_1011_ = v_r_1002_;
v_isShared_1012_ = v_isSharedCheck_1023_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_v_1009_);
lean_inc(v_k_1008_);
lean_dec(v_r_1002_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1023_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1013_ = lean_unsigned_to_nat(3u);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 4, v_l_985_);
lean_ctor_set(v___x_1011_, 3, v_l_985_);
lean_ctor_set(v___x_1011_, 2, v_v_1004_);
lean_ctor_set(v___x_1011_, 1, v_k_1003_);
lean_ctor_set(v___x_1011_, 0, v___x_899_);
v___x_1015_ = v___x_1011_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v_k_1003_);
lean_ctor_set(v_reuseFailAlloc_1022_, 2, v_v_1004_);
lean_ctor_set(v_reuseFailAlloc_1022_, 3, v_l_985_);
lean_ctor_set(v_reuseFailAlloc_1022_, 4, v_l_985_);
v___x_1015_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_object* v___x_1017_; 
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 4, v_l_985_);
lean_ctor_set(v___x_1006_, 2, v_v_891_);
lean_ctor_set(v___x_1006_, 1, v_k_890_);
lean_ctor_set(v___x_1006_, 0, v___x_899_);
v___x_1017_ = v___x_1006_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_k_890_);
lean_ctor_set(v_reuseFailAlloc_1021_, 2, v_v_891_);
lean_ctor_set(v_reuseFailAlloc_1021_, 3, v_l_985_);
lean_ctor_set(v_reuseFailAlloc_1021_, 4, v_l_985_);
v___x_1017_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1019_; 
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 4, v___x_1017_);
lean_ctor_set(v___x_895_, 3, v___x_1015_);
lean_ctor_set(v___x_895_, 2, v_v_1009_);
lean_ctor_set(v___x_895_, 1, v_k_1008_);
lean_ctor_set(v___x_895_, 0, v___x_1013_);
v___x_1019_ = v___x_895_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_k_1008_);
lean_ctor_set(v_reuseFailAlloc_1020_, 2, v_v_1009_);
lean_ctor_set(v_reuseFailAlloc_1020_, 3, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1020_, 4, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
}
}
else
{
lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1031_ = lean_unsigned_to_nat(2u);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 4, v_r_1002_);
lean_ctor_set(v___x_895_, 3, v_impl_898_);
lean_ctor_set(v___x_895_, 0, v___x_1031_);
v___x_1033_ = v___x_895_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1031_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v_k_890_);
lean_ctor_set(v_reuseFailAlloc_1034_, 2, v_v_891_);
lean_ctor_set(v_reuseFailAlloc_1034_, 3, v_impl_898_);
lean_ctor_set(v_reuseFailAlloc_1034_, 4, v_r_1002_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1036_; 
lean_dec(v_v_891_);
lean_dec(v_k_890_);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 2, v_v_887_);
lean_ctor_set(v___x_895_, 1, v_k_886_);
v___x_1036_ = v___x_895_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_size_889_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_k_886_);
lean_ctor_set(v_reuseFailAlloc_1037_, 2, v_v_887_);
lean_ctor_set(v_reuseFailAlloc_1037_, 3, v_l_892_);
lean_ctor_set(v_reuseFailAlloc_1037_, 4, v_r_893_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
default: 
{
lean_object* v_impl_1038_; lean_object* v___x_1039_; 
lean_dec(v_size_889_);
v_impl_1038_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_886_, v_v_887_, v_r_893_);
v___x_1039_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_892_) == 0)
{
lean_object* v_size_1040_; lean_object* v_size_1041_; lean_object* v_k_1042_; lean_object* v_v_1043_; lean_object* v_l_1044_; lean_object* v_r_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
v_size_1040_ = lean_ctor_get(v_l_892_, 0);
v_size_1041_ = lean_ctor_get(v_impl_1038_, 0);
lean_inc(v_size_1041_);
v_k_1042_ = lean_ctor_get(v_impl_1038_, 1);
lean_inc(v_k_1042_);
v_v_1043_ = lean_ctor_get(v_impl_1038_, 2);
lean_inc(v_v_1043_);
v_l_1044_ = lean_ctor_get(v_impl_1038_, 3);
lean_inc(v_l_1044_);
v_r_1045_ = lean_ctor_get(v_impl_1038_, 4);
lean_inc(v_r_1045_);
v___x_1046_ = lean_unsigned_to_nat(3u);
v___x_1047_ = lean_nat_mul(v___x_1046_, v_size_1040_);
v___x_1048_ = lean_nat_dec_lt(v___x_1047_, v_size_1041_);
lean_dec(v___x_1047_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1052_; 
lean_dec(v_r_1045_);
lean_dec(v_l_1044_);
lean_dec(v_v_1043_);
lean_dec(v_k_1042_);
v___x_1049_ = lean_nat_add(v___x_1039_, v_size_1040_);
v___x_1050_ = lean_nat_add(v___x_1049_, v_size_1041_);
lean_dec(v_size_1041_);
lean_dec(v___x_1049_);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 4, v_impl_1038_);
lean_ctor_set(v___x_895_, 0, v___x_1050_);
v___x_1052_ = v___x_895_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_k_890_);
lean_ctor_set(v_reuseFailAlloc_1053_, 2, v_v_891_);
lean_ctor_set(v_reuseFailAlloc_1053_, 3, v_l_892_);
lean_ctor_set(v_reuseFailAlloc_1053_, 4, v_impl_1038_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
else
{
lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1117_; 
v_isSharedCheck_1117_ = !lean_is_exclusive(v_impl_1038_);
if (v_isSharedCheck_1117_ == 0)
{
lean_object* v_unused_1118_; lean_object* v_unused_1119_; lean_object* v_unused_1120_; lean_object* v_unused_1121_; lean_object* v_unused_1122_; 
v_unused_1118_ = lean_ctor_get(v_impl_1038_, 4);
lean_dec(v_unused_1118_);
v_unused_1119_ = lean_ctor_get(v_impl_1038_, 3);
lean_dec(v_unused_1119_);
v_unused_1120_ = lean_ctor_get(v_impl_1038_, 2);
lean_dec(v_unused_1120_);
v_unused_1121_ = lean_ctor_get(v_impl_1038_, 1);
lean_dec(v_unused_1121_);
v_unused_1122_ = lean_ctor_get(v_impl_1038_, 0);
lean_dec(v_unused_1122_);
v___x_1055_ = v_impl_1038_;
v_isShared_1056_ = v_isSharedCheck_1117_;
goto v_resetjp_1054_;
}
else
{
lean_dec(v_impl_1038_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1117_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v_size_1057_; lean_object* v_k_1058_; lean_object* v_v_1059_; lean_object* v_l_1060_; lean_object* v_r_1061_; lean_object* v_size_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; uint8_t v___x_1065_; 
v_size_1057_ = lean_ctor_get(v_l_1044_, 0);
v_k_1058_ = lean_ctor_get(v_l_1044_, 1);
v_v_1059_ = lean_ctor_get(v_l_1044_, 2);
v_l_1060_ = lean_ctor_get(v_l_1044_, 3);
v_r_1061_ = lean_ctor_get(v_l_1044_, 4);
v_size_1062_ = lean_ctor_get(v_r_1045_, 0);
v___x_1063_ = lean_unsigned_to_nat(2u);
v___x_1064_ = lean_nat_mul(v___x_1063_, v_size_1062_);
v___x_1065_ = lean_nat_dec_lt(v_size_1057_, v___x_1064_);
lean_dec(v___x_1064_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1093_; 
lean_inc(v_r_1061_);
lean_inc(v_l_1060_);
lean_inc(v_v_1059_);
lean_inc(v_k_1058_);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_l_1044_);
if (v_isSharedCheck_1093_ == 0)
{
lean_object* v_unused_1094_; lean_object* v_unused_1095_; lean_object* v_unused_1096_; lean_object* v_unused_1097_; lean_object* v_unused_1098_; 
v_unused_1094_ = lean_ctor_get(v_l_1044_, 4);
lean_dec(v_unused_1094_);
v_unused_1095_ = lean_ctor_get(v_l_1044_, 3);
lean_dec(v_unused_1095_);
v_unused_1096_ = lean_ctor_get(v_l_1044_, 2);
lean_dec(v_unused_1096_);
v_unused_1097_ = lean_ctor_get(v_l_1044_, 1);
lean_dec(v_unused_1097_);
v_unused_1098_ = lean_ctor_get(v_l_1044_, 0);
lean_dec(v_unused_1098_);
v___x_1067_ = v_l_1044_;
v_isShared_1068_ = v_isSharedCheck_1093_;
goto v_resetjp_1066_;
}
else
{
lean_dec(v_l_1044_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1093_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1083_; 
v___x_1069_ = lean_nat_add(v___x_1039_, v_size_1040_);
v___x_1070_ = lean_nat_add(v___x_1069_, v_size_1041_);
lean_dec(v_size_1041_);
if (lean_obj_tag(v_l_1060_) == 0)
{
lean_object* v_size_1091_; 
v_size_1091_ = lean_ctor_get(v_l_1060_, 0);
lean_inc(v_size_1091_);
v___y_1083_ = v_size_1091_;
goto v___jp_1082_;
}
else
{
lean_object* v___x_1092_; 
v___x_1092_ = lean_unsigned_to_nat(0u);
v___y_1083_ = v___x_1092_;
goto v___jp_1082_;
}
v___jp_1071_:
{
lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1075_ = lean_nat_add(v___y_1072_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec(v___y_1072_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 4, v_r_1045_);
lean_ctor_set(v___x_1067_, 3, v_r_1061_);
lean_ctor_set(v___x_1067_, 2, v_v_1043_);
lean_ctor_set(v___x_1067_, 1, v_k_1042_);
lean_ctor_set(v___x_1067_, 0, v___x_1075_);
v___x_1077_ = v___x_1067_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1075_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v_k_1042_);
lean_ctor_set(v_reuseFailAlloc_1081_, 2, v_v_1043_);
lean_ctor_set(v_reuseFailAlloc_1081_, 3, v_r_1061_);
lean_ctor_set(v_reuseFailAlloc_1081_, 4, v_r_1045_);
v___x_1077_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1079_; 
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 4, v___x_1077_);
lean_ctor_set(v___x_1055_, 3, v___y_1073_);
lean_ctor_set(v___x_1055_, 2, v_v_1059_);
lean_ctor_set(v___x_1055_, 1, v_k_1058_);
lean_ctor_set(v___x_1055_, 0, v___x_1070_);
v___x_1079_ = v___x_1055_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_k_1058_);
lean_ctor_set(v_reuseFailAlloc_1080_, 2, v_v_1059_);
lean_ctor_set(v_reuseFailAlloc_1080_, 3, v___y_1073_);
lean_ctor_set(v_reuseFailAlloc_1080_, 4, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
v___jp_1082_:
{
lean_object* v___x_1084_; lean_object* v___x_1086_; 
v___x_1084_ = lean_nat_add(v___x_1069_, v___y_1083_);
lean_dec(v___y_1083_);
lean_dec(v___x_1069_);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 4, v_l_1060_);
lean_ctor_set(v___x_895_, 0, v___x_1084_);
v___x_1086_ = v___x_895_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_k_890_);
lean_ctor_set(v_reuseFailAlloc_1090_, 2, v_v_891_);
lean_ctor_set(v_reuseFailAlloc_1090_, 3, v_l_892_);
lean_ctor_set(v_reuseFailAlloc_1090_, 4, v_l_1060_);
v___x_1086_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_nat_add(v___x_1039_, v_size_1062_);
if (lean_obj_tag(v_r_1061_) == 0)
{
lean_object* v_size_1088_; 
v_size_1088_ = lean_ctor_get(v_r_1061_, 0);
lean_inc(v_size_1088_);
v___y_1072_ = v___x_1087_;
v___y_1073_ = v___x_1086_;
v___y_1074_ = v_size_1088_;
goto v___jp_1071_;
}
else
{
lean_object* v___x_1089_; 
v___x_1089_ = lean_unsigned_to_nat(0u);
v___y_1072_ = v___x_1087_;
v___y_1073_ = v___x_1086_;
v___y_1074_ = v___x_1089_;
goto v___jp_1071_;
}
}
}
}
}
else
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1103_; 
lean_del_object(v___x_895_);
v___x_1099_ = lean_nat_add(v___x_1039_, v_size_1040_);
v___x_1100_ = lean_nat_add(v___x_1099_, v_size_1041_);
lean_dec(v_size_1041_);
v___x_1101_ = lean_nat_add(v___x_1099_, v_size_1057_);
lean_dec(v___x_1099_);
lean_inc_ref(v_l_892_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 4, v_l_1044_);
lean_ctor_set(v___x_1055_, 3, v_l_892_);
lean_ctor_set(v___x_1055_, 2, v_v_891_);
lean_ctor_set(v___x_1055_, 1, v_k_890_);
lean_ctor_set(v___x_1055_, 0, v___x_1101_);
v___x_1103_ = v___x_1055_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_k_890_);
lean_ctor_set(v_reuseFailAlloc_1116_, 2, v_v_891_);
lean_ctor_set(v_reuseFailAlloc_1116_, 3, v_l_892_);
lean_ctor_set(v_reuseFailAlloc_1116_, 4, v_l_1044_);
v___x_1103_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
v_isSharedCheck_1110_ = !lean_is_exclusive(v_l_892_);
if (v_isSharedCheck_1110_ == 0)
{
lean_object* v_unused_1111_; lean_object* v_unused_1112_; lean_object* v_unused_1113_; lean_object* v_unused_1114_; lean_object* v_unused_1115_; 
v_unused_1111_ = lean_ctor_get(v_l_892_, 4);
lean_dec(v_unused_1111_);
v_unused_1112_ = lean_ctor_get(v_l_892_, 3);
lean_dec(v_unused_1112_);
v_unused_1113_ = lean_ctor_get(v_l_892_, 2);
lean_dec(v_unused_1113_);
v_unused_1114_ = lean_ctor_get(v_l_892_, 1);
lean_dec(v_unused_1114_);
v_unused_1115_ = lean_ctor_get(v_l_892_, 0);
lean_dec(v_unused_1115_);
v___x_1105_ = v_l_892_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_dec(v_l_892_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 4, v_r_1045_);
lean_ctor_set(v___x_1105_, 3, v___x_1103_);
lean_ctor_set(v___x_1105_, 2, v_v_1043_);
lean_ctor_set(v___x_1105_, 1, v_k_1042_);
lean_ctor_set(v___x_1105_, 0, v___x_1100_);
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v_k_1042_);
lean_ctor_set(v_reuseFailAlloc_1109_, 2, v_v_1043_);
lean_ctor_set(v_reuseFailAlloc_1109_, 3, v___x_1103_);
lean_ctor_set(v_reuseFailAlloc_1109_, 4, v_r_1045_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1123_; 
v_l_1123_ = lean_ctor_get(v_impl_1038_, 3);
lean_inc(v_l_1123_);
if (lean_obj_tag(v_l_1123_) == 0)
{
lean_object* v_r_1124_; lean_object* v_k_1125_; lean_object* v_v_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1149_; 
v_r_1124_ = lean_ctor_get(v_impl_1038_, 4);
v_k_1125_ = lean_ctor_get(v_impl_1038_, 1);
v_v_1126_ = lean_ctor_get(v_impl_1038_, 2);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_impl_1038_);
if (v_isSharedCheck_1149_ == 0)
{
lean_object* v_unused_1150_; lean_object* v_unused_1151_; 
v_unused_1150_ = lean_ctor_get(v_impl_1038_, 3);
lean_dec(v_unused_1150_);
v_unused_1151_ = lean_ctor_get(v_impl_1038_, 0);
lean_dec(v_unused_1151_);
v___x_1128_ = v_impl_1038_;
v_isShared_1129_ = v_isSharedCheck_1149_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_r_1124_);
lean_inc(v_v_1126_);
lean_inc(v_k_1125_);
lean_dec(v_impl_1038_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1149_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v_k_1130_; lean_object* v_v_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1145_; 
v_k_1130_ = lean_ctor_get(v_l_1123_, 1);
v_v_1131_ = lean_ctor_get(v_l_1123_, 2);
v_isSharedCheck_1145_ = !lean_is_exclusive(v_l_1123_);
if (v_isSharedCheck_1145_ == 0)
{
lean_object* v_unused_1146_; lean_object* v_unused_1147_; lean_object* v_unused_1148_; 
v_unused_1146_ = lean_ctor_get(v_l_1123_, 4);
lean_dec(v_unused_1146_);
v_unused_1147_ = lean_ctor_get(v_l_1123_, 3);
lean_dec(v_unused_1147_);
v_unused_1148_ = lean_ctor_get(v_l_1123_, 0);
lean_dec(v_unused_1148_);
v___x_1133_ = v_l_1123_;
v_isShared_1134_ = v_isSharedCheck_1145_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_v_1131_);
lean_inc(v_k_1130_);
lean_dec(v_l_1123_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1145_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1135_; lean_object* v___x_1137_; 
v___x_1135_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1124_, 2);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 4, v_r_1124_);
lean_ctor_set(v___x_1133_, 3, v_r_1124_);
lean_ctor_set(v___x_1133_, 2, v_v_891_);
lean_ctor_set(v___x_1133_, 1, v_k_890_);
lean_ctor_set(v___x_1133_, 0, v___x_1039_);
v___x_1137_ = v___x_1133_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_k_890_);
lean_ctor_set(v_reuseFailAlloc_1144_, 2, v_v_891_);
lean_ctor_set(v_reuseFailAlloc_1144_, 3, v_r_1124_);
lean_ctor_set(v_reuseFailAlloc_1144_, 4, v_r_1124_);
v___x_1137_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
lean_object* v___x_1139_; 
lean_inc(v_r_1124_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 3, v_r_1124_);
lean_ctor_set(v___x_1128_, 0, v___x_1039_);
v___x_1139_ = v___x_1128_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_k_1125_);
lean_ctor_set(v_reuseFailAlloc_1143_, 2, v_v_1126_);
lean_ctor_set(v_reuseFailAlloc_1143_, 3, v_r_1124_);
lean_ctor_set(v_reuseFailAlloc_1143_, 4, v_r_1124_);
v___x_1139_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
lean_object* v___x_1141_; 
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 4, v___x_1139_);
lean_ctor_set(v___x_895_, 3, v___x_1137_);
lean_ctor_set(v___x_895_, 2, v_v_1131_);
lean_ctor_set(v___x_895_, 1, v_k_1130_);
lean_ctor_set(v___x_895_, 0, v___x_1135_);
v___x_1141_ = v___x_895_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1135_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v_k_1130_);
lean_ctor_set(v_reuseFailAlloc_1142_, 2, v_v_1131_);
lean_ctor_set(v_reuseFailAlloc_1142_, 3, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1142_, 4, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
}
}
else
{
lean_object* v_r_1152_; 
v_r_1152_ = lean_ctor_get(v_impl_1038_, 4);
lean_inc(v_r_1152_);
if (lean_obj_tag(v_r_1152_) == 0)
{
lean_object* v_k_1153_; lean_object* v_v_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1165_; 
v_k_1153_ = lean_ctor_get(v_impl_1038_, 1);
v_v_1154_ = lean_ctor_get(v_impl_1038_, 2);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_impl_1038_);
if (v_isSharedCheck_1165_ == 0)
{
lean_object* v_unused_1166_; lean_object* v_unused_1167_; lean_object* v_unused_1168_; 
v_unused_1166_ = lean_ctor_get(v_impl_1038_, 4);
lean_dec(v_unused_1166_);
v_unused_1167_ = lean_ctor_get(v_impl_1038_, 3);
lean_dec(v_unused_1167_);
v_unused_1168_ = lean_ctor_get(v_impl_1038_, 0);
lean_dec(v_unused_1168_);
v___x_1156_ = v_impl_1038_;
v_isShared_1157_ = v_isSharedCheck_1165_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_v_1154_);
lean_inc(v_k_1153_);
lean_dec(v_impl_1038_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1165_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1158_ = lean_unsigned_to_nat(3u);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 4, v_l_1123_);
lean_ctor_set(v___x_1156_, 2, v_v_891_);
lean_ctor_set(v___x_1156_, 1, v_k_890_);
lean_ctor_set(v___x_1156_, 0, v___x_1039_);
v___x_1160_ = v___x_1156_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_k_890_);
lean_ctor_set(v_reuseFailAlloc_1164_, 2, v_v_891_);
lean_ctor_set(v_reuseFailAlloc_1164_, 3, v_l_1123_);
lean_ctor_set(v_reuseFailAlloc_1164_, 4, v_l_1123_);
v___x_1160_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
lean_object* v___x_1162_; 
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 4, v_r_1152_);
lean_ctor_set(v___x_895_, 3, v___x_1160_);
lean_ctor_set(v___x_895_, 2, v_v_1154_);
lean_ctor_set(v___x_895_, 1, v_k_1153_);
lean_ctor_set(v___x_895_, 0, v___x_1158_);
v___x_1162_ = v___x_895_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1158_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v_k_1153_);
lean_ctor_set(v_reuseFailAlloc_1163_, 2, v_v_1154_);
lean_ctor_set(v_reuseFailAlloc_1163_, 3, v___x_1160_);
lean_ctor_set(v_reuseFailAlloc_1163_, 4, v_r_1152_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
else
{
lean_object* v___x_1169_; lean_object* v___x_1171_; 
v___x_1169_ = lean_unsigned_to_nat(2u);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 4, v_impl_1038_);
lean_ctor_set(v___x_895_, 3, v_r_1152_);
lean_ctor_set(v___x_895_, 0, v___x_1169_);
v___x_1171_ = v___x_895_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1169_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_k_890_);
lean_ctor_set(v_reuseFailAlloc_1172_, 2, v_v_891_);
lean_ctor_set(v_reuseFailAlloc_1172_, 3, v_r_1152_);
lean_ctor_set(v_reuseFailAlloc_1172_, 4, v_impl_1038_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
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
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = lean_unsigned_to_nat(1u);
v___x_1175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
lean_ctor_set(v___x_1175_, 1, v_k_886_);
lean_ctor_set(v___x_1175_, 2, v_v_887_);
lean_ctor_set(v___x_1175_, 3, v_t_888_);
lean_ctor_set(v___x_1175_, 4, v_t_888_);
return v___x_1175_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(lean_object* v_as_x27_1176_, lean_object* v_b_1177_){
_start:
{
if (lean_obj_tag(v_as_x27_1176_) == 0)
{
return v_b_1177_;
}
else
{
lean_object* v_head_1178_; lean_object* v_tail_1179_; lean_object* v_fst_1180_; lean_object* v_snd_1181_; lean_object* v_r_1182_; 
v_head_1178_ = lean_ctor_get(v_as_x27_1176_, 0);
v_tail_1179_ = lean_ctor_get(v_as_x27_1176_, 1);
v_fst_1180_ = lean_ctor_get(v_head_1178_, 0);
v_snd_1181_ = lean_ctor_get(v_head_1178_, 1);
lean_inc(v_snd_1181_);
lean_inc(v_fst_1180_);
v_r_1182_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_fst_1180_, v_snd_1181_, v_b_1177_);
v_as_x27_1176_ = v_tail_1179_;
v_b_1177_ = v_r_1182_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg___boxed(lean_object* v_as_x27_1184_, lean_object* v_b_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_as_x27_1184_, v_b_1185_);
lean_dec(v_as_x27_1184_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mkObj(lean_object* v_o_1187_){
_start:
{
lean_object* v_r_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v_r_1188_ = lean_box(1);
v___x_1189_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_o_1187_, v_r_1188_);
v___x_1190_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mkObj___boxed(lean_object* v_o_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_Json_mkObj(v_o_1191_);
lean_dec(v_o_1191_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0(lean_object* v_00_u03b2_1193_, lean_object* v_k_1194_, lean_object* v_v_1195_, lean_object* v_t_1196_, lean_object* v_hl_1197_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_1194_, v_v_1195_, v_t_1196_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1(lean_object* v_as_1199_, lean_object* v_as_x27_1200_, lean_object* v_b_1201_, lean_object* v_a_1202_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_as_x27_1200_, v_b_1201_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___boxed(lean_object* v_as_1204_, lean_object* v_as_x27_1205_, lean_object* v_b_1206_, lean_object* v_a_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1(v_as_1204_, v_as_x27_1205_, v_b_1206_, v_a_1207_);
lean_dec(v_as_x27_1205_);
lean_dec(v_as_1204_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeNat___lam__0(lean_object* v_n_1209_){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = l_Lean_JsonNumber_fromNat(v_n_1209_);
v___x_1211_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeInt___lam__0(lean_object* v_n_1214_){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = l_Lean_JsonNumber_fromInt(v_n_1214_);
v___x_1216_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeString___lam__0(lean_object* v_s_1219_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1220_, 0, v_s_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeBool___lam__0(uint8_t v_b_1223_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1224_, 0, v_b_1223_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeBool___lam__0___boxed(lean_object* v_b_1225_){
_start:
{
uint8_t v_b_boxed_1226_; lean_object* v_res_1227_; 
v_b_boxed_1226_ = lean_unbox(v_b_1225_);
v_res_1227_ = l_Lean_Json_instCoeBool___lam__0(v_b_boxed_1226_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instOfNat(lean_object* v_n_1230_){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = l_Lean_JsonNumber_fromNat(v_n_1230_);
v___x_1232_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT uint8_t l_Lean_Json_isNull(lean_object* v_x_1233_){
_start:
{
if (lean_obj_tag(v_x_1233_) == 0)
{
uint8_t v___x_1234_; 
v___x_1234_ = 1;
return v___x_1234_;
}
else
{
uint8_t v___x_1235_; 
v___x_1235_ = 0;
return v___x_1235_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_isNull___boxed(lean_object* v_x_1236_){
_start:
{
uint8_t v_res_1237_; lean_object* v_r_1238_; 
v_res_1237_ = l_Lean_Json_isNull(v_x_1236_);
lean_dec(v_x_1236_);
v_r_1238_ = lean_box(v_res_1237_);
return v_r_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObj_x3f(lean_object* v_x_1242_){
_start:
{
if (lean_obj_tag(v_x_1242_) == 5)
{
lean_object* v_kvPairs_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
v_kvPairs_1243_ = lean_ctor_get(v_x_1242_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v_x_1242_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v_x_1242_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_kvPairs_1243_);
lean_dec(v_x_1242_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
lean_ctor_set_tag(v___x_1245_, 1);
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_kvPairs_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
else
{
lean_object* v___x_1251_; 
lean_dec(v_x_1242_);
v___x_1251_ = ((lean_object*)(l_Lean_Json_getObj_x3f___closed__1));
return v___x_1251_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getArr_x3f(lean_object* v_x_1255_){
_start:
{
if (lean_obj_tag(v_x_1255_) == 4)
{
lean_object* v_elems_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
v_elems_1256_ = lean_ctor_get(v_x_1255_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v_x_1255_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v_x_1255_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_elems_1256_);
lean_dec(v_x_1255_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
lean_ctor_set_tag(v___x_1258_, 1);
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_elems_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
else
{
lean_object* v___x_1264_; 
lean_dec(v_x_1255_);
v___x_1264_ = ((lean_object*)(l_Lean_Json_getArr_x3f___closed__1));
return v___x_1264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getStr_x3f(lean_object* v_x_1268_){
_start:
{
if (lean_obj_tag(v_x_1268_) == 3)
{
lean_object* v_s_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
v_s_1269_ = lean_ctor_get(v_x_1268_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v_x_1268_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v_x_1268_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_s_1269_);
lean_dec(v_x_1268_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
lean_ctor_set_tag(v___x_1271_, 1);
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_s_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
else
{
lean_object* v___x_1277_; 
lean_dec(v_x_1268_);
v___x_1277_ = ((lean_object*)(l_Lean_Json_getStr_x3f___closed__1));
return v___x_1277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getNat_x3f(lean_object* v_x_1281_){
_start:
{
if (lean_obj_tag(v_x_1281_) == 2)
{
lean_object* v_n_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1298_; 
v_n_1284_ = lean_ctor_get(v_x_1281_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_x_1281_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1286_ = v_x_1281_;
v_isShared_1287_ = v_isSharedCheck_1298_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_n_1284_);
lean_dec(v_x_1281_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1298_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v_mantissa_1288_; lean_object* v_exponent_1289_; lean_object* v_natZero_1290_; lean_object* v_intZero_1291_; uint8_t v_isNeg_1292_; 
v_mantissa_1288_ = lean_ctor_get(v_n_1284_, 0);
lean_inc(v_mantissa_1288_);
v_exponent_1289_ = lean_ctor_get(v_n_1284_, 1);
lean_inc(v_exponent_1289_);
lean_dec_ref(v_n_1284_);
v_natZero_1290_ = lean_unsigned_to_nat(0u);
v_intZero_1291_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v_isNeg_1292_ = lean_int_dec_lt(v_mantissa_1288_, v_intZero_1291_);
if (v_isNeg_1292_ == 0)
{
uint8_t v___x_1293_; 
v___x_1293_ = lean_nat_dec_eq(v_exponent_1289_, v_natZero_1290_);
lean_dec(v_exponent_1289_);
if (v___x_1293_ == 0)
{
lean_dec(v_mantissa_1288_);
lean_del_object(v___x_1286_);
goto v___jp_1282_;
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; 
v_a_1294_ = lean_nat_abs(v_mantissa_1288_);
lean_dec(v_mantissa_1288_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set_tag(v___x_1286_, 1);
lean_ctor_set(v___x_1286_, 0, v_a_1294_);
v___x_1296_ = v___x_1286_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1294_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
else
{
lean_dec(v_exponent_1289_);
lean_dec(v_mantissa_1288_);
lean_del_object(v___x_1286_);
goto v___jp_1282_;
}
}
}
else
{
lean_dec(v_x_1281_);
goto v___jp_1282_;
}
v___jp_1282_:
{
lean_object* v___x_1283_; 
v___x_1283_ = ((lean_object*)(l_Lean_Json_getNat_x3f___closed__1));
return v___x_1283_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getInt_x3f(lean_object* v_x_1302_){
_start:
{
if (lean_obj_tag(v_x_1302_) == 2)
{
lean_object* v_n_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1316_; 
v_n_1305_ = lean_ctor_get(v_x_1302_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v_x_1302_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1307_ = v_x_1302_;
v_isShared_1308_ = v_isSharedCheck_1316_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_n_1305_);
lean_dec(v_x_1302_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1316_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v_mantissa_1309_; lean_object* v_exponent_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
v_mantissa_1309_ = lean_ctor_get(v_n_1305_, 0);
lean_inc(v_mantissa_1309_);
v_exponent_1310_ = lean_ctor_get(v_n_1305_, 1);
lean_inc(v_exponent_1310_);
lean_dec_ref(v_n_1305_);
v___x_1311_ = lean_unsigned_to_nat(0u);
v___x_1312_ = lean_nat_dec_eq(v_exponent_1310_, v___x_1311_);
lean_dec(v_exponent_1310_);
if (v___x_1312_ == 0)
{
lean_dec(v_mantissa_1309_);
lean_del_object(v___x_1307_);
goto v___jp_1303_;
}
else
{
lean_object* v___x_1314_; 
if (v_isShared_1308_ == 0)
{
lean_ctor_set_tag(v___x_1307_, 1);
lean_ctor_set(v___x_1307_, 0, v_mantissa_1309_);
v___x_1314_ = v___x_1307_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_mantissa_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
else
{
lean_dec(v_x_1302_);
goto v___jp_1303_;
}
v___jp_1303_:
{
lean_object* v___x_1304_; 
v___x_1304_ = ((lean_object*)(l_Lean_Json_getInt_x3f___closed__1));
return v___x_1304_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getBool_x3f(lean_object* v_x_1320_){
_start:
{
if (lean_obj_tag(v_x_1320_) == 1)
{
uint8_t v_b_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v_b_1321_ = lean_ctor_get_uint8(v_x_1320_, 0);
v___x_1322_ = lean_box(v_b_1321_);
v___x_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
return v___x_1323_;
}
else
{
lean_object* v___x_1324_; 
v___x_1324_ = ((lean_object*)(l_Lean_Json_getBool_x3f___closed__1));
return v___x_1324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getBool_x3f___boxed(lean_object* v_x_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lean_Json_getBool_x3f(v_x_1325_);
lean_dec(v_x_1325_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getNum_x3f(lean_object* v_x_1330_){
_start:
{
if (lean_obj_tag(v_x_1330_) == 2)
{
lean_object* v_n_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
v_n_1331_ = lean_ctor_get(v_x_1330_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v_x_1330_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v_x_1330_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_n_1331_);
lean_dec(v_x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
lean_ctor_set_tag(v___x_1333_, 1);
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_n_1331_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
else
{
lean_object* v___x_1339_; 
lean_dec(v_x_1330_);
v___x_1339_ = ((lean_object*)(l_Lean_Json_getNum_x3f___closed__1));
return v___x_1339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjVal_x3f(lean_object* v_x_1343_, lean_object* v_x_1344_){
_start:
{
if (lean_obj_tag(v_x_1343_) == 5)
{
lean_object* v_kvPairs_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1363_; 
v_kvPairs_1345_ = lean_ctor_get(v_x_1343_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v_x_1343_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1347_ = v_x_1343_;
v_isShared_1348_ = v_isSharedCheck_1363_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_kvPairs_1345_);
lean_dec(v_x_1343_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1363_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_kvPairs_1345_, v_x_1344_);
lean_dec(v_kvPairs_1345_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1350_ = ((lean_object*)(l_Lean_Json_getObjVal_x3f___closed__0));
v___x_1351_ = lean_string_append(v___x_1350_, v_x_1344_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set_tag(v___x_1347_, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1351_);
v___x_1353_ = v___x_1347_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
else
{
lean_object* v_val_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_del_object(v___x_1347_);
v_val_1355_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1349_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_val_1355_);
lean_dec(v___x_1349_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_val_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
else
{
lean_object* v___x_1364_; 
lean_dec(v_x_1343_);
v___x_1364_ = ((lean_object*)(l_Lean_Json_getObjVal_x3f___closed__1));
return v___x_1364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjVal_x3f___boxed(lean_object* v_x_1365_, lean_object* v_x_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_Json_getObjVal_x3f(v_x_1365_, v_x_1366_);
lean_dec_ref(v_x_1366_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getArrVal_x3f(lean_object* v_x_1371_, lean_object* v_x_1372_){
_start:
{
if (lean_obj_tag(v_x_1371_) == 4)
{
lean_object* v_elems_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1389_; 
v_elems_1373_ = lean_ctor_get(v_x_1371_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v_x_1371_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1375_ = v_x_1371_;
v_isShared_1376_ = v_isSharedCheck_1389_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_elems_1373_);
lean_dec(v_x_1371_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1389_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1377_; uint8_t v___x_1378_; 
v___x_1377_ = lean_array_get_size(v_elems_1373_);
v___x_1378_ = lean_nat_dec_lt(v_x_1372_, v___x_1377_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1383_; 
lean_dec_ref(v_elems_1373_);
v___x_1379_ = ((lean_object*)(l_Lean_Json_getArrVal_x3f___closed__0));
v___x_1380_ = l_Nat_reprFast(v_x_1372_);
v___x_1381_ = lean_string_append(v___x_1379_, v___x_1380_);
lean_dec_ref(v___x_1380_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set_tag(v___x_1375_, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1381_);
v___x_1383_ = v___x_1375_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1381_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
else
{
lean_object* v___x_1385_; lean_object* v___x_1387_; 
v___x_1385_ = lean_array_fget(v_elems_1373_, v_x_1372_);
lean_dec(v_x_1372_);
lean_dec_ref(v_elems_1373_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set_tag(v___x_1375_, 1);
lean_ctor_set(v___x_1375_, 0, v___x_1385_);
v___x_1387_ = v___x_1375_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1385_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
else
{
lean_object* v___x_1390_; 
lean_dec(v_x_1372_);
lean_dec(v_x_1371_);
v___x_1390_ = ((lean_object*)(l_Lean_Json_getArrVal_x3f___closed__1));
return v___x_1390_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValD(lean_object* v_j_1391_, lean_object* v_k_1392_){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = l_Lean_Json_getObjVal_x3f(v_j_1391_, v_k_1392_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v___x_1394_; 
lean_dec_ref_known(v___x_1393_, 1);
v___x_1394_ = lean_box(0);
return v___x_1394_;
}
else
{
lean_object* v_a_1395_; 
v_a_1395_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1395_);
lean_dec_ref_known(v___x_1393_, 1);
return v_a_1395_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValD___boxed(lean_object* v_j_1396_, lean_object* v_k_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Lean_Json_getObjValD(v_j_1396_, v_k_1397_);
lean_dec_ref(v_k_1397_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Json_setObjVal_x21_spec__1(lean_object* v_msg_1399_){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = lean_box(0);
v___x_1401_ = lean_panic_fn_borrowed(v___x_1400_, v_msg_1399_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(lean_object* v_msg_1402_){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = lean_box(1);
v___x_1404_ = lean_panic_fn_borrowed(v___x_1403_, v_msg_1402_);
return v___x_1404_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1408_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2));
v___x_1409_ = lean_unsigned_to_nat(35u);
v___x_1410_ = lean_unsigned_to_nat(182u);
v___x_1411_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1));
v___x_1412_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1413_ = l_mkPanicMessageWithDecl(v___x_1412_, v___x_1411_, v___x_1410_, v___x_1409_, v___x_1408_);
return v___x_1413_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1414_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2));
v___x_1415_ = lean_unsigned_to_nat(21u);
v___x_1416_ = lean_unsigned_to_nat(183u);
v___x_1417_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1));
v___x_1418_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1419_ = l_mkPanicMessageWithDecl(v___x_1418_, v___x_1417_, v___x_1416_, v___x_1415_, v___x_1414_);
return v___x_1419_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1422_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6));
v___x_1423_ = lean_unsigned_to_nat(35u);
v___x_1424_ = lean_unsigned_to_nat(276u);
v___x_1425_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5));
v___x_1426_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1427_ = l_mkPanicMessageWithDecl(v___x_1426_, v___x_1425_, v___x_1424_, v___x_1423_, v___x_1422_);
return v___x_1427_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1428_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6));
v___x_1429_ = lean_unsigned_to_nat(21u);
v___x_1430_ = lean_unsigned_to_nat(277u);
v___x_1431_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5));
v___x_1432_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1433_ = l_mkPanicMessageWithDecl(v___x_1432_, v___x_1431_, v___x_1430_, v___x_1429_, v___x_1428_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(lean_object* v_k_1434_, lean_object* v_v_1435_, lean_object* v_t_1436_){
_start:
{
if (lean_obj_tag(v_t_1436_) == 0)
{
lean_object* v_size_1437_; lean_object* v_k_1438_; lean_object* v_v_1439_; lean_object* v_l_1440_; lean_object* v_r_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1797_; 
v_size_1437_ = lean_ctor_get(v_t_1436_, 0);
v_k_1438_ = lean_ctor_get(v_t_1436_, 1);
v_v_1439_ = lean_ctor_get(v_t_1436_, 2);
v_l_1440_ = lean_ctor_get(v_t_1436_, 3);
v_r_1441_ = lean_ctor_get(v_t_1436_, 4);
v_isSharedCheck_1797_ = !lean_is_exclusive(v_t_1436_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1443_ = v_t_1436_;
v_isShared_1444_ = v_isSharedCheck_1797_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_r_1441_);
lean_inc(v_l_1440_);
lean_inc(v_v_1439_);
lean_inc(v_k_1438_);
lean_inc(v_size_1437_);
lean_dec(v_t_1436_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1797_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
uint8_t v___x_1445_; 
v___x_1445_ = lean_string_compare(v_k_1434_, v_k_1438_);
switch(v___x_1445_)
{
case 0:
{
lean_object* v___x_1446_; 
lean_dec(v_size_1437_);
v___x_1446_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1434_, v_v_1435_, v_l_1440_);
if (lean_obj_tag(v_r_1441_) == 0)
{
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v_size_1447_; lean_object* v_size_1448_; lean_object* v_k_1449_; lean_object* v_v_1450_; lean_object* v_l_1451_; lean_object* v_r_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; uint8_t v___x_1455_; 
v_size_1447_ = lean_ctor_get(v_r_1441_, 0);
v_size_1448_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_size_1448_);
v_k_1449_ = lean_ctor_get(v___x_1446_, 1);
lean_inc(v_k_1449_);
v_v_1450_ = lean_ctor_get(v___x_1446_, 2);
lean_inc(v_v_1450_);
v_l_1451_ = lean_ctor_get(v___x_1446_, 3);
lean_inc(v_l_1451_);
v_r_1452_ = lean_ctor_get(v___x_1446_, 4);
lean_inc(v_r_1452_);
v___x_1453_ = lean_unsigned_to_nat(3u);
v___x_1454_ = lean_nat_mul(v___x_1453_, v_size_1447_);
v___x_1455_ = lean_nat_dec_lt(v___x_1454_, v_size_1448_);
lean_dec(v___x_1454_);
if (v___x_1455_ == 0)
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1460_; 
lean_dec(v_r_1452_);
lean_dec(v_l_1451_);
lean_dec(v_v_1450_);
lean_dec(v_k_1449_);
v___x_1456_ = lean_unsigned_to_nat(1u);
v___x_1457_ = lean_nat_add(v___x_1456_, v_size_1448_);
lean_dec(v_size_1448_);
v___x_1458_ = lean_nat_add(v___x_1457_, v_size_1447_);
lean_dec(v___x_1457_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 3, v___x_1446_);
lean_ctor_set(v___x_1443_, 0, v___x_1458_);
v___x_1460_ = v___x_1443_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_k_1438_);
lean_ctor_set(v_reuseFailAlloc_1461_, 2, v_v_1439_);
lean_ctor_set(v_reuseFailAlloc_1461_, 3, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1461_, 4, v_r_1441_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
else
{
lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1533_; 
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1533_ == 0)
{
lean_object* v_unused_1534_; lean_object* v_unused_1535_; lean_object* v_unused_1536_; lean_object* v_unused_1537_; lean_object* v_unused_1538_; 
v_unused_1534_ = lean_ctor_get(v___x_1446_, 4);
lean_dec(v_unused_1534_);
v_unused_1535_ = lean_ctor_get(v___x_1446_, 3);
lean_dec(v_unused_1535_);
v_unused_1536_ = lean_ctor_get(v___x_1446_, 2);
lean_dec(v_unused_1536_);
v_unused_1537_ = lean_ctor_get(v___x_1446_, 1);
lean_dec(v_unused_1537_);
v_unused_1538_ = lean_ctor_get(v___x_1446_, 0);
lean_dec(v_unused_1538_);
v___x_1463_ = v___x_1446_;
v_isShared_1464_ = v_isSharedCheck_1533_;
goto v_resetjp_1462_;
}
else
{
lean_dec(v___x_1446_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1533_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
if (lean_obj_tag(v_l_1451_) == 0)
{
if (lean_obj_tag(v_r_1452_) == 0)
{
lean_object* v_size_1465_; lean_object* v_size_1466_; lean_object* v_k_1467_; lean_object* v_v_1468_; lean_object* v_l_1469_; lean_object* v_r_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; 
v_size_1465_ = lean_ctor_get(v_l_1451_, 0);
v_size_1466_ = lean_ctor_get(v_r_1452_, 0);
v_k_1467_ = lean_ctor_get(v_r_1452_, 1);
v_v_1468_ = lean_ctor_get(v_r_1452_, 2);
v_l_1469_ = lean_ctor_get(v_r_1452_, 3);
v_r_1470_ = lean_ctor_get(v_r_1452_, 4);
v___x_1471_ = lean_unsigned_to_nat(2u);
v___x_1472_ = lean_nat_mul(v___x_1471_, v_size_1465_);
v___x_1473_ = lean_nat_dec_lt(v_size_1466_, v___x_1472_);
lean_dec(v___x_1472_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1503_; 
lean_inc(v_r_1470_);
lean_inc(v_l_1469_);
lean_inc(v_v_1468_);
lean_inc(v_k_1467_);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_r_1452_);
if (v_isSharedCheck_1503_ == 0)
{
lean_object* v_unused_1504_; lean_object* v_unused_1505_; lean_object* v_unused_1506_; lean_object* v_unused_1507_; lean_object* v_unused_1508_; 
v_unused_1504_ = lean_ctor_get(v_r_1452_, 4);
lean_dec(v_unused_1504_);
v_unused_1505_ = lean_ctor_get(v_r_1452_, 3);
lean_dec(v_unused_1505_);
v_unused_1506_ = lean_ctor_get(v_r_1452_, 2);
lean_dec(v_unused_1506_);
v_unused_1507_ = lean_ctor_get(v_r_1452_, 1);
lean_dec(v_unused_1507_);
v_unused_1508_ = lean_ctor_get(v_r_1452_, 0);
lean_dec(v_unused_1508_);
v___x_1475_ = v_r_1452_;
v_isShared_1476_ = v_isSharedCheck_1503_;
goto v_resetjp_1474_;
}
else
{
lean_dec(v_r_1452_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1503_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___x_1491_; lean_object* v___y_1493_; 
v___x_1477_ = lean_unsigned_to_nat(1u);
v___x_1478_ = lean_nat_add(v___x_1477_, v_size_1448_);
lean_dec(v_size_1448_);
v___x_1479_ = lean_nat_add(v___x_1478_, v_size_1447_);
lean_dec(v___x_1478_);
v___x_1491_ = lean_nat_add(v___x_1477_, v_size_1465_);
if (lean_obj_tag(v_l_1469_) == 0)
{
lean_object* v_size_1501_; 
v_size_1501_ = lean_ctor_get(v_l_1469_, 0);
lean_inc(v_size_1501_);
v___y_1493_ = v_size_1501_;
goto v___jp_1492_;
}
else
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_unsigned_to_nat(0u);
v___y_1493_ = v___x_1502_;
goto v___jp_1492_;
}
v___jp_1480_:
{
lean_object* v___x_1484_; lean_object* v___x_1486_; 
v___x_1484_ = lean_nat_add(v___y_1481_, v___y_1483_);
lean_dec(v___y_1483_);
lean_dec(v___y_1481_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 4, v_r_1441_);
lean_ctor_set(v___x_1475_, 3, v_r_1470_);
lean_ctor_set(v___x_1475_, 2, v_v_1439_);
lean_ctor_set(v___x_1475_, 1, v_k_1438_);
lean_ctor_set(v___x_1475_, 0, v___x_1484_);
v___x_1486_ = v___x_1475_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1484_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_k_1438_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v_v_1439_);
lean_ctor_set(v_reuseFailAlloc_1490_, 3, v_r_1470_);
lean_ctor_set(v_reuseFailAlloc_1490_, 4, v_r_1441_);
v___x_1486_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
lean_object* v___x_1488_; 
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 4, v___x_1486_);
lean_ctor_set(v___x_1463_, 3, v___y_1482_);
lean_ctor_set(v___x_1463_, 2, v_v_1468_);
lean_ctor_set(v___x_1463_, 1, v_k_1467_);
lean_ctor_set(v___x_1463_, 0, v___x_1479_);
v___x_1488_ = v___x_1463_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1479_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_k_1467_);
lean_ctor_set(v_reuseFailAlloc_1489_, 2, v_v_1468_);
lean_ctor_set(v_reuseFailAlloc_1489_, 3, v___y_1482_);
lean_ctor_set(v_reuseFailAlloc_1489_, 4, v___x_1486_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
v___jp_1492_:
{
lean_object* v___x_1494_; lean_object* v___x_1496_; 
v___x_1494_ = lean_nat_add(v___x_1491_, v___y_1493_);
lean_dec(v___y_1493_);
lean_dec(v___x_1491_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 4, v_l_1469_);
lean_ctor_set(v___x_1443_, 3, v_l_1451_);
lean_ctor_set(v___x_1443_, 2, v_v_1450_);
lean_ctor_set(v___x_1443_, 1, v_k_1449_);
lean_ctor_set(v___x_1443_, 0, v___x_1494_);
v___x_1496_ = v___x_1443_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1494_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_k_1449_);
lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_v_1450_);
lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_l_1451_);
lean_ctor_set(v_reuseFailAlloc_1500_, 4, v_l_1469_);
v___x_1496_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
lean_object* v___x_1497_; 
v___x_1497_ = lean_nat_add(v___x_1477_, v_size_1447_);
if (lean_obj_tag(v_r_1470_) == 0)
{
lean_object* v_size_1498_; 
v_size_1498_ = lean_ctor_get(v_r_1470_, 0);
lean_inc(v_size_1498_);
v___y_1481_ = v___x_1497_;
v___y_1482_ = v___x_1496_;
v___y_1483_ = v_size_1498_;
goto v___jp_1480_;
}
else
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_unsigned_to_nat(0u);
v___y_1481_ = v___x_1497_;
v___y_1482_ = v___x_1496_;
v___y_1483_ = v___x_1499_;
goto v___jp_1480_;
}
}
}
}
}
else
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1515_; 
lean_del_object(v___x_1443_);
v___x_1509_ = lean_unsigned_to_nat(1u);
v___x_1510_ = lean_nat_add(v___x_1509_, v_size_1448_);
lean_dec(v_size_1448_);
v___x_1511_ = lean_nat_add(v___x_1510_, v_size_1447_);
lean_dec(v___x_1510_);
v___x_1512_ = lean_nat_add(v___x_1509_, v_size_1447_);
v___x_1513_ = lean_nat_add(v___x_1512_, v_size_1466_);
lean_dec(v___x_1512_);
lean_inc_ref(v_r_1441_);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 4, v_r_1441_);
lean_ctor_set(v___x_1463_, 3, v_r_1452_);
lean_ctor_set(v___x_1463_, 2, v_v_1439_);
lean_ctor_set(v___x_1463_, 1, v_k_1438_);
lean_ctor_set(v___x_1463_, 0, v___x_1513_);
v___x_1515_ = v___x_1463_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1513_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_k_1438_);
lean_ctor_set(v_reuseFailAlloc_1528_, 2, v_v_1439_);
lean_ctor_set(v_reuseFailAlloc_1528_, 3, v_r_1452_);
lean_ctor_set(v_reuseFailAlloc_1528_, 4, v_r_1441_);
v___x_1515_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1522_; 
v_isSharedCheck_1522_ = !lean_is_exclusive(v_r_1441_);
if (v_isSharedCheck_1522_ == 0)
{
lean_object* v_unused_1523_; lean_object* v_unused_1524_; lean_object* v_unused_1525_; lean_object* v_unused_1526_; lean_object* v_unused_1527_; 
v_unused_1523_ = lean_ctor_get(v_r_1441_, 4);
lean_dec(v_unused_1523_);
v_unused_1524_ = lean_ctor_get(v_r_1441_, 3);
lean_dec(v_unused_1524_);
v_unused_1525_ = lean_ctor_get(v_r_1441_, 2);
lean_dec(v_unused_1525_);
v_unused_1526_ = lean_ctor_get(v_r_1441_, 1);
lean_dec(v_unused_1526_);
v_unused_1527_ = lean_ctor_get(v_r_1441_, 0);
lean_dec(v_unused_1527_);
v___x_1517_ = v_r_1441_;
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
else
{
lean_dec(v_r_1441_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1520_; 
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 4, v___x_1515_);
lean_ctor_set(v___x_1517_, 3, v_l_1451_);
lean_ctor_set(v___x_1517_, 2, v_v_1450_);
lean_ctor_set(v___x_1517_, 1, v_k_1449_);
lean_ctor_set(v___x_1517_, 0, v___x_1511_);
v___x_1520_ = v___x_1517_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1511_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v_k_1449_);
lean_ctor_set(v_reuseFailAlloc_1521_, 2, v_v_1450_);
lean_ctor_set(v_reuseFailAlloc_1521_, 3, v_l_1451_);
lean_ctor_set(v_reuseFailAlloc_1521_, 4, v___x_1515_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
}
else
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
lean_dec_ref_known(v_l_1451_, 5);
lean_del_object(v___x_1463_);
lean_dec(v_v_1450_);
lean_dec(v_k_1449_);
lean_dec(v_size_1448_);
lean_dec_ref_known(v_r_1441_, 5);
lean_del_object(v___x_1443_);
lean_dec(v_v_1439_);
lean_dec(v_k_1438_);
v___x_1529_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3);
v___x_1530_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1529_);
return v___x_1530_;
}
}
else
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
lean_del_object(v___x_1463_);
lean_dec(v_r_1452_);
lean_dec(v_v_1450_);
lean_dec(v_k_1449_);
lean_dec(v_size_1448_);
lean_dec_ref_known(v_r_1441_, 5);
lean_del_object(v___x_1443_);
lean_dec(v_v_1439_);
lean_dec(v_k_1438_);
v___x_1531_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4);
v___x_1532_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1531_);
return v___x_1532_;
}
}
}
}
else
{
lean_object* v_size_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1543_; 
v_size_1539_ = lean_ctor_get(v_r_1441_, 0);
v___x_1540_ = lean_unsigned_to_nat(1u);
v___x_1541_ = lean_nat_add(v___x_1540_, v_size_1539_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 3, v___x_1446_);
lean_ctor_set(v___x_1443_, 0, v___x_1541_);
v___x_1543_ = v___x_1443_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1541_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v_k_1438_);
lean_ctor_set(v_reuseFailAlloc_1544_, 2, v_v_1439_);
lean_ctor_set(v_reuseFailAlloc_1544_, 3, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1544_, 4, v_r_1441_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
else
{
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v_l_1545_; 
v_l_1545_ = lean_ctor_get(v___x_1446_, 3);
lean_inc(v_l_1545_);
if (lean_obj_tag(v_l_1545_) == 0)
{
lean_object* v_r_1546_; 
v_r_1546_ = lean_ctor_get(v___x_1446_, 4);
lean_inc(v_r_1546_);
if (lean_obj_tag(v_r_1546_) == 0)
{
lean_object* v_size_1547_; lean_object* v_k_1548_; lean_object* v_v_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1563_; 
v_size_1547_ = lean_ctor_get(v___x_1446_, 0);
v_k_1548_ = lean_ctor_get(v___x_1446_, 1);
v_v_1549_ = lean_ctor_get(v___x_1446_, 2);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1563_ == 0)
{
lean_object* v_unused_1564_; lean_object* v_unused_1565_; 
v_unused_1564_ = lean_ctor_get(v___x_1446_, 4);
lean_dec(v_unused_1564_);
v_unused_1565_ = lean_ctor_get(v___x_1446_, 3);
lean_dec(v_unused_1565_);
v___x_1551_ = v___x_1446_;
v_isShared_1552_ = v_isSharedCheck_1563_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_v_1549_);
lean_inc(v_k_1548_);
lean_inc(v_size_1547_);
lean_dec(v___x_1446_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1563_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v_size_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1558_; 
v_size_1553_ = lean_ctor_get(v_r_1546_, 0);
v___x_1554_ = lean_unsigned_to_nat(1u);
v___x_1555_ = lean_nat_add(v___x_1554_, v_size_1547_);
lean_dec(v_size_1547_);
v___x_1556_ = lean_nat_add(v___x_1554_, v_size_1553_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 4, v_r_1441_);
lean_ctor_set(v___x_1551_, 3, v_r_1546_);
lean_ctor_set(v___x_1551_, 2, v_v_1439_);
lean_ctor_set(v___x_1551_, 1, v_k_1438_);
lean_ctor_set(v___x_1551_, 0, v___x_1556_);
v___x_1558_ = v___x_1551_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1556_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_k_1438_);
lean_ctor_set(v_reuseFailAlloc_1562_, 2, v_v_1439_);
lean_ctor_set(v_reuseFailAlloc_1562_, 3, v_r_1546_);
lean_ctor_set(v_reuseFailAlloc_1562_, 4, v_r_1441_);
v___x_1558_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
lean_object* v___x_1560_; 
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 4, v___x_1558_);
lean_ctor_set(v___x_1443_, 3, v_l_1545_);
lean_ctor_set(v___x_1443_, 2, v_v_1549_);
lean_ctor_set(v___x_1443_, 1, v_k_1548_);
lean_ctor_set(v___x_1443_, 0, v___x_1555_);
v___x_1560_ = v___x_1443_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1555_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v_k_1548_);
lean_ctor_set(v_reuseFailAlloc_1561_, 2, v_v_1549_);
lean_ctor_set(v_reuseFailAlloc_1561_, 3, v_l_1545_);
lean_ctor_set(v_reuseFailAlloc_1561_, 4, v___x_1558_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
else
{
lean_object* v_k_1566_; lean_object* v_v_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1579_; 
v_k_1566_ = lean_ctor_get(v___x_1446_, 1);
v_v_1567_ = lean_ctor_get(v___x_1446_, 2);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1579_ == 0)
{
lean_object* v_unused_1580_; lean_object* v_unused_1581_; lean_object* v_unused_1582_; 
v_unused_1580_ = lean_ctor_get(v___x_1446_, 4);
lean_dec(v_unused_1580_);
v_unused_1581_ = lean_ctor_get(v___x_1446_, 3);
lean_dec(v_unused_1581_);
v_unused_1582_ = lean_ctor_get(v___x_1446_, 0);
lean_dec(v_unused_1582_);
v___x_1569_ = v___x_1446_;
v_isShared_1570_ = v_isSharedCheck_1579_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_v_1567_);
lean_inc(v_k_1566_);
lean_dec(v___x_1446_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1579_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1574_; 
v___x_1571_ = lean_unsigned_to_nat(3u);
v___x_1572_ = lean_unsigned_to_nat(1u);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 3, v_r_1546_);
lean_ctor_set(v___x_1569_, 2, v_v_1439_);
lean_ctor_set(v___x_1569_, 1, v_k_1438_);
lean_ctor_set(v___x_1569_, 0, v___x_1572_);
v___x_1574_ = v___x_1569_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1572_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_k_1438_);
lean_ctor_set(v_reuseFailAlloc_1578_, 2, v_v_1439_);
lean_ctor_set(v_reuseFailAlloc_1578_, 3, v_r_1546_);
lean_ctor_set(v_reuseFailAlloc_1578_, 4, v_r_1546_);
v___x_1574_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
lean_object* v___x_1576_; 
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 4, v___x_1574_);
lean_ctor_set(v___x_1443_, 3, v_l_1545_);
lean_ctor_set(v___x_1443_, 2, v_v_1567_);
lean_ctor_set(v___x_1443_, 1, v_k_1566_);
lean_ctor_set(v___x_1443_, 0, v___x_1571_);
v___x_1576_ = v___x_1443_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1571_);
lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_k_1566_);
lean_ctor_set(v_reuseFailAlloc_1577_, 2, v_v_1567_);
lean_ctor_set(v_reuseFailAlloc_1577_, 3, v_l_1545_);
lean_ctor_set(v_reuseFailAlloc_1577_, 4, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
}
else
{
lean_object* v_r_1583_; 
v_r_1583_ = lean_ctor_get(v___x_1446_, 4);
lean_inc(v_r_1583_);
if (lean_obj_tag(v_r_1583_) == 0)
{
lean_object* v_k_1584_; lean_object* v_v_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1609_; 
v_k_1584_ = lean_ctor_get(v___x_1446_, 1);
v_v_1585_ = lean_ctor_get(v___x_1446_, 2);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1609_ == 0)
{
lean_object* v_unused_1610_; lean_object* v_unused_1611_; lean_object* v_unused_1612_; 
v_unused_1610_ = lean_ctor_get(v___x_1446_, 4);
lean_dec(v_unused_1610_);
v_unused_1611_ = lean_ctor_get(v___x_1446_, 3);
lean_dec(v_unused_1611_);
v_unused_1612_ = lean_ctor_get(v___x_1446_, 0);
lean_dec(v_unused_1612_);
v___x_1587_ = v___x_1446_;
v_isShared_1588_ = v_isSharedCheck_1609_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_v_1585_);
lean_inc(v_k_1584_);
lean_dec(v___x_1446_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1609_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v_k_1589_; lean_object* v_v_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1605_; 
v_k_1589_ = lean_ctor_get(v_r_1583_, 1);
v_v_1590_ = lean_ctor_get(v_r_1583_, 2);
v_isSharedCheck_1605_ = !lean_is_exclusive(v_r_1583_);
if (v_isSharedCheck_1605_ == 0)
{
lean_object* v_unused_1606_; lean_object* v_unused_1607_; lean_object* v_unused_1608_; 
v_unused_1606_ = lean_ctor_get(v_r_1583_, 4);
lean_dec(v_unused_1606_);
v_unused_1607_ = lean_ctor_get(v_r_1583_, 3);
lean_dec(v_unused_1607_);
v_unused_1608_ = lean_ctor_get(v_r_1583_, 0);
lean_dec(v_unused_1608_);
v___x_1592_ = v_r_1583_;
v_isShared_1593_ = v_isSharedCheck_1605_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_v_1590_);
lean_inc(v_k_1589_);
lean_dec(v_r_1583_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1605_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1597_; 
v___x_1594_ = lean_unsigned_to_nat(3u);
v___x_1595_ = lean_unsigned_to_nat(1u);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 4, v_l_1545_);
lean_ctor_set(v___x_1592_, 3, v_l_1545_);
lean_ctor_set(v___x_1592_, 2, v_v_1585_);
lean_ctor_set(v___x_1592_, 1, v_k_1584_);
lean_ctor_set(v___x_1592_, 0, v___x_1595_);
v___x_1597_ = v___x_1592_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1595_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_k_1584_);
lean_ctor_set(v_reuseFailAlloc_1604_, 2, v_v_1585_);
lean_ctor_set(v_reuseFailAlloc_1604_, 3, v_l_1545_);
lean_ctor_set(v_reuseFailAlloc_1604_, 4, v_l_1545_);
v___x_1597_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1599_; 
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 4, v_l_1545_);
lean_ctor_set(v___x_1587_, 2, v_v_1439_);
lean_ctor_set(v___x_1587_, 1, v_k_1438_);
lean_ctor_set(v___x_1587_, 0, v___x_1595_);
v___x_1599_ = v___x_1587_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1595_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_k_1438_);
lean_ctor_set(v_reuseFailAlloc_1603_, 2, v_v_1439_);
lean_ctor_set(v_reuseFailAlloc_1603_, 3, v_l_1545_);
lean_ctor_set(v_reuseFailAlloc_1603_, 4, v_l_1545_);
v___x_1599_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v___x_1601_; 
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 4, v___x_1599_);
lean_ctor_set(v___x_1443_, 3, v___x_1597_);
lean_ctor_set(v___x_1443_, 2, v_v_1590_);
lean_ctor_set(v___x_1443_, 1, v_k_1589_);
lean_ctor_set(v___x_1443_, 0, v___x_1594_);
v___x_1601_ = v___x_1443_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1594_);
lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_k_1589_);
lean_ctor_set(v_reuseFailAlloc_1602_, 2, v_v_1590_);
lean_ctor_set(v_reuseFailAlloc_1602_, 3, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1602_, 4, v___x_1599_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
}
}
else
{
lean_object* v___x_1613_; lean_object* v___x_1615_; 
v___x_1613_ = lean_unsigned_to_nat(2u);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 4, v_r_1583_);
lean_ctor_set(v___x_1443_, 3, v___x_1446_);
lean_ctor_set(v___x_1443_, 0, v___x_1613_);
v___x_1615_ = v___x_1443_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1613_);
lean_ctor_set(v_reuseFailAlloc_1616_, 1, v_k_1438_);
lean_ctor_set(v_reuseFailAlloc_1616_, 2, v_v_1439_);
lean_ctor_set(v_reuseFailAlloc_1616_, 3, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1616_, 4, v_r_1583_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
else
{
lean_object* v___x_1617_; lean_object* v___x_1619_; 
v___x_1617_ = lean_unsigned_to_nat(1u);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 4, v___x_1446_);
lean_ctor_set(v___x_1443_, 3, v___x_1446_);
lean_ctor_set(v___x_1443_, 0, v___x_1617_);
v___x_1619_ = v___x_1443_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1617_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_k_1438_);
lean_ctor_set(v_reuseFailAlloc_1620_, 2, v_v_1439_);
lean_ctor_set(v_reuseFailAlloc_1620_, 3, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1620_, 4, v___x_1446_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
case 1:
{
lean_object* v___x_1622_; 
lean_dec(v_v_1439_);
lean_dec(v_k_1438_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 2, v_v_1435_);
lean_ctor_set(v___x_1443_, 1, v_k_1434_);
v___x_1622_ = v___x_1443_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_size_1437_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v_k_1434_);
lean_ctor_set(v_reuseFailAlloc_1623_, 2, v_v_1435_);
lean_ctor_set(v_reuseFailAlloc_1623_, 3, v_l_1440_);
lean_ctor_set(v_reuseFailAlloc_1623_, 4, v_r_1441_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
default: 
{
lean_object* v___x_1624_; 
lean_dec(v_size_1437_);
v___x_1624_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1434_, v_v_1435_, v_r_1441_);
if (lean_obj_tag(v_l_1440_) == 0)
{
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_size_1625_; lean_object* v_size_1626_; lean_object* v_k_1627_; lean_object* v_v_1628_; lean_object* v_l_1629_; lean_object* v_r_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; uint8_t v___x_1633_; 
v_size_1625_ = lean_ctor_get(v_l_1440_, 0);
v_size_1626_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_size_1626_);
v_k_1627_ = lean_ctor_get(v___x_1624_, 1);
lean_inc(v_k_1627_);
v_v_1628_ = lean_ctor_get(v___x_1624_, 2);
lean_inc(v_v_1628_);
v_l_1629_ = lean_ctor_get(v___x_1624_, 3);
lean_inc(v_l_1629_);
v_r_1630_ = lean_ctor_get(v___x_1624_, 4);
lean_inc(v_r_1630_);
v___x_1631_ = lean_unsigned_to_nat(3u);
v___x_1632_ = lean_nat_mul(v___x_1631_, v_size_1625_);
v___x_1633_ = lean_nat_dec_lt(v___x_1632_, v_size_1626_);
lean_dec(v___x_1632_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1638_; 
lean_dec(v_r_1630_);
lean_dec(v_l_1629_);
lean_dec(v_v_1628_);
lean_dec(v_k_1627_);
v___x_1634_ = lean_unsigned_to_nat(1u);
v___x_1635_ = lean_nat_add(v___x_1634_, v_size_1625_);
v___x_1636_ = lean_nat_add(v___x_1635_, v_size_1626_);
lean_dec(v_size_1626_);
lean_dec(v___x_1635_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 4, v___x_1624_);
lean_ctor_set(v___x_1443_, 0, v___x_1636_);
v___x_1638_ = v___x_1443_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1636_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_k_1438_);
lean_ctor_set(v_reuseFailAlloc_1639_, 2, v_v_1439_);
lean_ctor_set(v_reuseFailAlloc_1639_, 3, v_l_1440_);
lean_ctor_set(v_reuseFailAlloc_1639_, 4, v___x_1624_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
else
{
lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1709_; 
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1709_ == 0)
{
lean_object* v_unused_1710_; lean_object* v_unused_1711_; lean_object* v_unused_1712_; lean_object* v_unused_1713_; lean_object* v_unused_1714_; 
v_unused_1710_ = lean_ctor_get(v___x_1624_, 4);
lean_dec(v_unused_1710_);
v_unused_1711_ = lean_ctor_get(v___x_1624_, 3);
lean_dec(v_unused_1711_);
v_unused_1712_ = lean_ctor_get(v___x_1624_, 2);
lean_dec(v_unused_1712_);
v_unused_1713_ = lean_ctor_get(v___x_1624_, 1);
lean_dec(v_unused_1713_);
v_unused_1714_ = lean_ctor_get(v___x_1624_, 0);
lean_dec(v_unused_1714_);
v___x_1641_ = v___x_1624_;
v_isShared_1642_ = v_isSharedCheck_1709_;
goto v_resetjp_1640_;
}
else
{
lean_dec(v___x_1624_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1709_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
if (lean_obj_tag(v_l_1629_) == 0)
{
if (lean_obj_tag(v_r_1630_) == 0)
{
lean_object* v_size_1643_; lean_object* v_k_1644_; lean_object* v_v_1645_; lean_object* v_l_1646_; lean_object* v_r_1647_; lean_object* v_size_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; uint8_t v___x_1651_; 
v_size_1643_ = lean_ctor_get(v_l_1629_, 0);
v_k_1644_ = lean_ctor_get(v_l_1629_, 1);
v_v_1645_ = lean_ctor_get(v_l_1629_, 2);
v_l_1646_ = lean_ctor_get(v_l_1629_, 3);
v_r_1647_ = lean_ctor_get(v_l_1629_, 4);
v_size_1648_ = lean_ctor_get(v_r_1630_, 0);
v___x_1649_ = lean_unsigned_to_nat(2u);
v___x_1650_ = lean_nat_mul(v___x_1649_, v_size_1648_);
v___x_1651_ = lean_nat_dec_lt(v_size_1643_, v___x_1650_);
lean_dec(v___x_1650_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1680_; 
lean_inc(v_r_1647_);
lean_inc(v_l_1646_);
lean_inc(v_v_1645_);
lean_inc(v_k_1644_);
v_isSharedCheck_1680_ = !lean_is_exclusive(v_l_1629_);
if (v_isSharedCheck_1680_ == 0)
{
lean_object* v_unused_1681_; lean_object* v_unused_1682_; lean_object* v_unused_1683_; lean_object* v_unused_1684_; lean_object* v_unused_1685_; 
v_unused_1681_ = lean_ctor_get(v_l_1629_, 4);
lean_dec(v_unused_1681_);
v_unused_1682_ = lean_ctor_get(v_l_1629_, 3);
lean_dec(v_unused_1682_);
v_unused_1683_ = lean_ctor_get(v_l_1629_, 2);
lean_dec(v_unused_1683_);
v_unused_1684_ = lean_ctor_get(v_l_1629_, 1);
lean_dec(v_unused_1684_);
v_unused_1685_ = lean_ctor_get(v_l_1629_, 0);
lean_dec(v_unused_1685_);
v___x_1653_ = v_l_1629_;
v_isShared_1654_ = v_isSharedCheck_1680_;
goto v_resetjp_1652_;
}
else
{
lean_dec(v_l_1629_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1680_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1670_; 
v___x_1655_ = lean_unsigned_to_nat(1u);
v___x_1656_ = lean_nat_add(v___x_1655_, v_size_1625_);
v___x_1657_ = lean_nat_add(v___x_1656_, v_size_1626_);
lean_dec(v_size_1626_);
if (lean_obj_tag(v_l_1646_) == 0)
{
lean_object* v_size_1678_; 
v_size_1678_ = lean_ctor_get(v_l_1646_, 0);
lean_inc(v_size_1678_);
v___y_1670_ = v_size_1678_;
goto v___jp_1669_;
}
else
{
lean_object* v___x_1679_; 
v___x_1679_ = lean_unsigned_to_nat(0u);
v___y_1670_ = v___x_1679_;
goto v___jp_1669_;
}
v___jp_1658_:
{
lean_object* v___x_1662_; lean_object* v___x_1664_; 
v___x_1662_ = lean_nat_add(v___y_1659_, v___y_1661_);
lean_dec(v___y_1661_);
lean_dec(v___y_1659_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 4, v_r_1630_);
lean_ctor_set(v___x_1653_, 3, v_r_1647_);
lean_ctor_set(v___x_1653_, 2, v_v_1628_);
lean_ctor_set(v___x_1653_, 1, v_k_1627_);
lean_ctor_set(v___x_1653_, 0, v___x_1662_);
v___x_1664_ = v___x_1653_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1662_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v_k_1627_);
lean_ctor_set(v_reuseFailAlloc_1668_, 2, v_v_1628_);
lean_ctor_set(v_reuseFailAlloc_1668_, 3, v_r_1647_);
lean_ctor_set(v_reuseFailAlloc_1668_, 4, v_r_1630_);
v___x_1664_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
lean_object* v___x_1666_; 
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 4, v___x_1664_);
lean_ctor_set(v___x_1641_, 3, v___y_1660_);
lean_ctor_set(v___x_1641_, 2, v_v_1645_);
lean_ctor_set(v___x_1641_, 1, v_k_1644_);
lean_ctor_set(v___x_1641_, 0, v___x_1657_);
v___x_1666_ = v___x_1641_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1657_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_k_1644_);
lean_ctor_set(v_reuseFailAlloc_1667_, 2, v_v_1645_);
lean_ctor_set(v_reuseFailAlloc_1667_, 3, v___y_1660_);
lean_ctor_set(v_reuseFailAlloc_1667_, 4, v___x_1664_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
v___jp_1669_:
{
lean_object* v___x_1671_; lean_object* v___x_1673_; 
v___x_1671_ = lean_nat_add(v___x_1656_, v___y_1670_);
lean_dec(v___y_1670_);
lean_dec(v___x_1656_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 4, v_l_1646_);
lean_ctor_set(v___x_1443_, 0, v___x_1671_);
v___x_1673_ = v___x_1443_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1671_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v_k_1438_);
lean_ctor_set(v_reuseFailAlloc_1677_, 2, v_v_1439_);
lean_ctor_set(v_reuseFailAlloc_1677_, 3, v_l_1440_);
lean_ctor_set(v_reuseFailAlloc_1677_, 4, v_l_1646_);
v___x_1673_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
lean_object* v___x_1674_; 
v___x_1674_ = lean_nat_add(v___x_1655_, v_size_1648_);
if (lean_obj_tag(v_r_1647_) == 0)
{
lean_object* v_size_1675_; 
v_size_1675_ = lean_ctor_get(v_r_1647_, 0);
lean_inc(v_size_1675_);
v___y_1659_ = v___x_1674_;
v___y_1660_ = v___x_1673_;
v___y_1661_ = v_size_1675_;
goto v___jp_1658_;
}
else
{
lean_object* v___x_1676_; 
v___x_1676_ = lean_unsigned_to_nat(0u);
v___y_1659_ = v___x_1674_;
v___y_1660_ = v___x_1673_;
v___y_1661_ = v___x_1676_;
goto v___jp_1658_;
}
}
}
}
}
else
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1691_; 
lean_del_object(v___x_1443_);
v___x_1686_ = lean_unsigned_to_nat(1u);
v___x_1687_ = lean_nat_add(v___x_1686_, v_size_1625_);
v___x_1688_ = lean_nat_add(v___x_1687_, v_size_1626_);
lean_dec(v_size_1626_);
v___x_1689_ = lean_nat_add(v___x_1687_, v_size_1643_);
lean_dec(v___x_1687_);
lean_inc_ref(v_l_1440_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 4, v_l_1629_);
lean_ctor_set(v___x_1641_, 3, v_l_1440_);
lean_ctor_set(v___x_1641_, 2, v_v_1439_);
lean_ctor_set(v___x_1641_, 1, v_k_1438_);
lean_ctor_set(v___x_1641_, 0, v___x_1689_);
v___x_1691_ = v___x_1641_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1689_);
lean_ctor_set(v_reuseFailAlloc_1704_, 1, v_k_1438_);
lean_ctor_set(v_reuseFailAlloc_1704_, 2, v_v_1439_);
lean_ctor_set(v_reuseFailAlloc_1704_, 3, v_l_1440_);
lean_ctor_set(v_reuseFailAlloc_1704_, 4, v_l_1629_);
v___x_1691_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
v_isSharedCheck_1698_ = !lean_is_exclusive(v_l_1440_);
if (v_isSharedCheck_1698_ == 0)
{
lean_object* v_unused_1699_; lean_object* v_unused_1700_; lean_object* v_unused_1701_; lean_object* v_unused_1702_; lean_object* v_unused_1703_; 
v_unused_1699_ = lean_ctor_get(v_l_1440_, 4);
lean_dec(v_unused_1699_);
v_unused_1700_ = lean_ctor_get(v_l_1440_, 3);
lean_dec(v_unused_1700_);
v_unused_1701_ = lean_ctor_get(v_l_1440_, 2);
lean_dec(v_unused_1701_);
v_unused_1702_ = lean_ctor_get(v_l_1440_, 1);
lean_dec(v_unused_1702_);
v_unused_1703_ = lean_ctor_get(v_l_1440_, 0);
lean_dec(v_unused_1703_);
v___x_1693_ = v_l_1440_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_dec(v_l_1440_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 4, v_r_1630_);
lean_ctor_set(v___x_1693_, 3, v___x_1691_);
lean_ctor_set(v___x_1693_, 2, v_v_1628_);
lean_ctor_set(v___x_1693_, 1, v_k_1627_);
lean_ctor_set(v___x_1693_, 0, v___x_1688_);
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1688_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v_k_1627_);
lean_ctor_set(v_reuseFailAlloc_1697_, 2, v_v_1628_);
lean_ctor_set(v_reuseFailAlloc_1697_, 3, v___x_1691_);
lean_ctor_set(v_reuseFailAlloc_1697_, 4, v_r_1630_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
}
else
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
lean_dec_ref_known(v_l_1629_, 5);
lean_del_object(v___x_1641_);
lean_dec(v_v_1628_);
lean_dec(v_k_1627_);
lean_dec(v_size_1626_);
lean_dec_ref_known(v_l_1440_, 5);
lean_del_object(v___x_1443_);
lean_dec(v_v_1439_);
lean_dec(v_k_1438_);
v___x_1705_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7);
v___x_1706_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1705_);
return v___x_1706_;
}
}
else
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
lean_del_object(v___x_1641_);
lean_dec(v_r_1630_);
lean_dec(v_v_1628_);
lean_dec(v_k_1627_);
lean_dec(v_size_1626_);
lean_dec_ref_known(v_l_1440_, 5);
lean_del_object(v___x_1443_);
lean_dec(v_v_1439_);
lean_dec(v_k_1438_);
v___x_1707_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8);
v___x_1708_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1707_);
return v___x_1708_;
}
}
}
}
else
{
lean_object* v_size_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1719_; 
v_size_1715_ = lean_ctor_get(v_l_1440_, 0);
v___x_1716_ = lean_unsigned_to_nat(1u);
v___x_1717_ = lean_nat_add(v___x_1716_, v_size_1715_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 4, v___x_1624_);
lean_ctor_set(v___x_1443_, 0, v___x_1717_);
v___x_1719_ = v___x_1443_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1717_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v_k_1438_);
lean_ctor_set(v_reuseFailAlloc_1720_, 2, v_v_1439_);
lean_ctor_set(v_reuseFailAlloc_1720_, 3, v_l_1440_);
lean_ctor_set(v_reuseFailAlloc_1720_, 4, v___x_1624_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
else
{
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_l_1721_; 
v_l_1721_ = lean_ctor_get(v___x_1624_, 3);
lean_inc(v_l_1721_);
if (lean_obj_tag(v_l_1721_) == 0)
{
lean_object* v_r_1722_; 
v_r_1722_ = lean_ctor_get(v___x_1624_, 4);
lean_inc(v_r_1722_);
if (lean_obj_tag(v_r_1722_) == 0)
{
lean_object* v_size_1723_; lean_object* v_k_1724_; lean_object* v_v_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1739_; 
v_size_1723_ = lean_ctor_get(v___x_1624_, 0);
v_k_1724_ = lean_ctor_get(v___x_1624_, 1);
v_v_1725_ = lean_ctor_get(v___x_1624_, 2);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1739_ == 0)
{
lean_object* v_unused_1740_; lean_object* v_unused_1741_; 
v_unused_1740_ = lean_ctor_get(v___x_1624_, 4);
lean_dec(v_unused_1740_);
v_unused_1741_ = lean_ctor_get(v___x_1624_, 3);
lean_dec(v_unused_1741_);
v___x_1727_ = v___x_1624_;
v_isShared_1728_ = v_isSharedCheck_1739_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_v_1725_);
lean_inc(v_k_1724_);
lean_inc(v_size_1723_);
lean_dec(v___x_1624_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1739_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v_size_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1734_; 
v_size_1729_ = lean_ctor_get(v_l_1721_, 0);
v___x_1730_ = lean_unsigned_to_nat(1u);
v___x_1731_ = lean_nat_add(v___x_1730_, v_size_1723_);
lean_dec(v_size_1723_);
v___x_1732_ = lean_nat_add(v___x_1730_, v_size_1729_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 4, v_l_1721_);
lean_ctor_set(v___x_1727_, 3, v_l_1440_);
lean_ctor_set(v___x_1727_, 2, v_v_1439_);
lean_ctor_set(v___x_1727_, 1, v_k_1438_);
lean_ctor_set(v___x_1727_, 0, v___x_1732_);
v___x_1734_ = v___x_1727_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1732_);
lean_ctor_set(v_reuseFailAlloc_1738_, 1, v_k_1438_);
lean_ctor_set(v_reuseFailAlloc_1738_, 2, v_v_1439_);
lean_ctor_set(v_reuseFailAlloc_1738_, 3, v_l_1440_);
lean_ctor_set(v_reuseFailAlloc_1738_, 4, v_l_1721_);
v___x_1734_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
lean_object* v___x_1736_; 
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 4, v_r_1722_);
lean_ctor_set(v___x_1443_, 3, v___x_1734_);
lean_ctor_set(v___x_1443_, 2, v_v_1725_);
lean_ctor_set(v___x_1443_, 1, v_k_1724_);
lean_ctor_set(v___x_1443_, 0, v___x_1731_);
v___x_1736_ = v___x_1443_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1731_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v_k_1724_);
lean_ctor_set(v_reuseFailAlloc_1737_, 2, v_v_1725_);
lean_ctor_set(v_reuseFailAlloc_1737_, 3, v___x_1734_);
lean_ctor_set(v_reuseFailAlloc_1737_, 4, v_r_1722_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
}
else
{
lean_object* v_k_1742_; lean_object* v_v_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1767_; 
v_k_1742_ = lean_ctor_get(v___x_1624_, 1);
v_v_1743_ = lean_ctor_get(v___x_1624_, 2);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1767_ == 0)
{
lean_object* v_unused_1768_; lean_object* v_unused_1769_; lean_object* v_unused_1770_; 
v_unused_1768_ = lean_ctor_get(v___x_1624_, 4);
lean_dec(v_unused_1768_);
v_unused_1769_ = lean_ctor_get(v___x_1624_, 3);
lean_dec(v_unused_1769_);
v_unused_1770_ = lean_ctor_get(v___x_1624_, 0);
lean_dec(v_unused_1770_);
v___x_1745_ = v___x_1624_;
v_isShared_1746_ = v_isSharedCheck_1767_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_v_1743_);
lean_inc(v_k_1742_);
lean_dec(v___x_1624_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1767_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v_k_1747_; lean_object* v_v_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1763_; 
v_k_1747_ = lean_ctor_get(v_l_1721_, 1);
v_v_1748_ = lean_ctor_get(v_l_1721_, 2);
v_isSharedCheck_1763_ = !lean_is_exclusive(v_l_1721_);
if (v_isSharedCheck_1763_ == 0)
{
lean_object* v_unused_1764_; lean_object* v_unused_1765_; lean_object* v_unused_1766_; 
v_unused_1764_ = lean_ctor_get(v_l_1721_, 4);
lean_dec(v_unused_1764_);
v_unused_1765_ = lean_ctor_get(v_l_1721_, 3);
lean_dec(v_unused_1765_);
v_unused_1766_ = lean_ctor_get(v_l_1721_, 0);
lean_dec(v_unused_1766_);
v___x_1750_ = v_l_1721_;
v_isShared_1751_ = v_isSharedCheck_1763_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_v_1748_);
lean_inc(v_k_1747_);
lean_dec(v_l_1721_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1763_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1755_; 
v___x_1752_ = lean_unsigned_to_nat(3u);
v___x_1753_ = lean_unsigned_to_nat(1u);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 4, v_r_1722_);
lean_ctor_set(v___x_1750_, 3, v_r_1722_);
lean_ctor_set(v___x_1750_, 2, v_v_1439_);
lean_ctor_set(v___x_1750_, 1, v_k_1438_);
lean_ctor_set(v___x_1750_, 0, v___x_1753_);
v___x_1755_ = v___x_1750_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1753_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_k_1438_);
lean_ctor_set(v_reuseFailAlloc_1762_, 2, v_v_1439_);
lean_ctor_set(v_reuseFailAlloc_1762_, 3, v_r_1722_);
lean_ctor_set(v_reuseFailAlloc_1762_, 4, v_r_1722_);
v___x_1755_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
lean_object* v___x_1757_; 
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 3, v_r_1722_);
lean_ctor_set(v___x_1745_, 0, v___x_1753_);
v___x_1757_ = v___x_1745_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1753_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v_k_1742_);
lean_ctor_set(v_reuseFailAlloc_1761_, 2, v_v_1743_);
lean_ctor_set(v_reuseFailAlloc_1761_, 3, v_r_1722_);
lean_ctor_set(v_reuseFailAlloc_1761_, 4, v_r_1722_);
v___x_1757_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
lean_object* v___x_1759_; 
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 4, v___x_1757_);
lean_ctor_set(v___x_1443_, 3, v___x_1755_);
lean_ctor_set(v___x_1443_, 2, v_v_1748_);
lean_ctor_set(v___x_1443_, 1, v_k_1747_);
lean_ctor_set(v___x_1443_, 0, v___x_1752_);
v___x_1759_ = v___x_1443_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1752_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_k_1747_);
lean_ctor_set(v_reuseFailAlloc_1760_, 2, v_v_1748_);
lean_ctor_set(v_reuseFailAlloc_1760_, 3, v___x_1755_);
lean_ctor_set(v_reuseFailAlloc_1760_, 4, v___x_1757_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1771_; 
v_r_1771_ = lean_ctor_get(v___x_1624_, 4);
lean_inc(v_r_1771_);
if (lean_obj_tag(v_r_1771_) == 0)
{
lean_object* v_k_1772_; lean_object* v_v_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1785_; 
v_k_1772_ = lean_ctor_get(v___x_1624_, 1);
v_v_1773_ = lean_ctor_get(v___x_1624_, 2);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1785_ == 0)
{
lean_object* v_unused_1786_; lean_object* v_unused_1787_; lean_object* v_unused_1788_; 
v_unused_1786_ = lean_ctor_get(v___x_1624_, 4);
lean_dec(v_unused_1786_);
v_unused_1787_ = lean_ctor_get(v___x_1624_, 3);
lean_dec(v_unused_1787_);
v_unused_1788_ = lean_ctor_get(v___x_1624_, 0);
lean_dec(v_unused_1788_);
v___x_1775_ = v___x_1624_;
v_isShared_1776_ = v_isSharedCheck_1785_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_v_1773_);
lean_inc(v_k_1772_);
lean_dec(v___x_1624_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1785_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1780_; 
v___x_1777_ = lean_unsigned_to_nat(3u);
v___x_1778_ = lean_unsigned_to_nat(1u);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 4, v_l_1721_);
lean_ctor_set(v___x_1775_, 2, v_v_1439_);
lean_ctor_set(v___x_1775_, 1, v_k_1438_);
lean_ctor_set(v___x_1775_, 0, v___x_1778_);
v___x_1780_ = v___x_1775_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1778_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_k_1438_);
lean_ctor_set(v_reuseFailAlloc_1784_, 2, v_v_1439_);
lean_ctor_set(v_reuseFailAlloc_1784_, 3, v_l_1721_);
lean_ctor_set(v_reuseFailAlloc_1784_, 4, v_l_1721_);
v___x_1780_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
lean_object* v___x_1782_; 
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 4, v_r_1771_);
lean_ctor_set(v___x_1443_, 3, v___x_1780_);
lean_ctor_set(v___x_1443_, 2, v_v_1773_);
lean_ctor_set(v___x_1443_, 1, v_k_1772_);
lean_ctor_set(v___x_1443_, 0, v___x_1777_);
v___x_1782_ = v___x_1443_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1777_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v_k_1772_);
lean_ctor_set(v_reuseFailAlloc_1783_, 2, v_v_1773_);
lean_ctor_set(v_reuseFailAlloc_1783_, 3, v___x_1780_);
lean_ctor_set(v_reuseFailAlloc_1783_, 4, v_r_1771_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
else
{
lean_object* v___x_1789_; lean_object* v___x_1791_; 
v___x_1789_ = lean_unsigned_to_nat(2u);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 4, v___x_1624_);
lean_ctor_set(v___x_1443_, 3, v_r_1771_);
lean_ctor_set(v___x_1443_, 0, v___x_1789_);
v___x_1791_ = v___x_1443_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1789_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_k_1438_);
lean_ctor_set(v_reuseFailAlloc_1792_, 2, v_v_1439_);
lean_ctor_set(v_reuseFailAlloc_1792_, 3, v_r_1771_);
lean_ctor_set(v_reuseFailAlloc_1792_, 4, v___x_1624_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
else
{
lean_object* v___x_1793_; lean_object* v___x_1795_; 
v___x_1793_ = lean_unsigned_to_nat(1u);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 4, v___x_1624_);
lean_ctor_set(v___x_1443_, 3, v___x_1624_);
lean_ctor_set(v___x_1443_, 0, v___x_1793_);
v___x_1795_ = v___x_1443_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1793_);
lean_ctor_set(v_reuseFailAlloc_1796_, 1, v_k_1438_);
lean_ctor_set(v_reuseFailAlloc_1796_, 2, v_v_1439_);
lean_ctor_set(v_reuseFailAlloc_1796_, 3, v___x_1624_);
lean_ctor_set(v_reuseFailAlloc_1796_, 4, v___x_1624_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1798_ = lean_unsigned_to_nat(1u);
v___x_1799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
lean_ctor_set(v___x_1799_, 1, v_k_1434_);
lean_ctor_set(v___x_1799_, 2, v_v_1435_);
lean_ctor_set(v___x_1799_, 3, v_t_1436_);
lean_ctor_set(v___x_1799_, 4, v_t_1436_);
return v___x_1799_;
}
}
}
static lean_object* _init_l_Lean_Json_setObjVal_x21___closed__2(void){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1802_ = ((lean_object*)(l_Lean_Json_setObjVal_x21___closed__1));
v___x_1803_ = lean_unsigned_to_nat(21u);
v___x_1804_ = lean_unsigned_to_nat(285u);
v___x_1805_ = ((lean_object*)(l_Lean_Json_setObjVal_x21___closed__0));
v___x_1806_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0));
v___x_1807_ = l_mkPanicMessageWithDecl(v___x_1806_, v___x_1805_, v___x_1804_, v___x_1803_, v___x_1802_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_setObjVal_x21(lean_object* v_x_1808_, lean_object* v_x_1809_, lean_object* v_x_1810_){
_start:
{
if (lean_obj_tag(v_x_1808_) == 5)
{
lean_object* v_kvPairs_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1819_; 
v_kvPairs_1811_ = lean_ctor_get(v_x_1808_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v_x_1808_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1813_ = v_x_1808_;
v_isShared_1814_ = v_isSharedCheck_1819_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_kvPairs_1811_);
lean_dec(v_x_1808_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1819_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; lean_object* v___x_1817_; 
v___x_1815_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_x_1809_, v_x_1810_, v_kvPairs_1811_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1815_);
v___x_1817_ = v___x_1813_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1815_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
else
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
lean_dec(v_x_1810_);
lean_dec_ref(v_x_1809_);
lean_dec(v_x_1808_);
v___x_1820_ = lean_obj_once(&l_Lean_Json_setObjVal_x21___closed__2, &l_Lean_Json_setObjVal_x21___closed__2_once, _init_l_Lean_Json_setObjVal_x21___closed__2);
v___x_1821_ = l_panic___at___00Lean_Json_setObjVal_x21_spec__1(v___x_1820_);
return v___x_1821_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0(lean_object* v_00_u03b2_1822_, lean_object* v_msg_1823_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v_msg_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0(lean_object* v_00_u03b2_1825_, lean_object* v_k_1826_, lean_object* v_v_1827_, lean_object* v_t_1828_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1826_, v_v_1827_, v_t_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(lean_object* v_init_1830_, lean_object* v_x_1831_){
_start:
{
if (lean_obj_tag(v_x_1831_) == 0)
{
lean_object* v_k_1832_; lean_object* v_v_1833_; lean_object* v_l_1834_; lean_object* v_r_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v_k_1832_ = lean_ctor_get(v_x_1831_, 1);
lean_inc(v_k_1832_);
v_v_1833_ = lean_ctor_get(v_x_1831_, 2);
lean_inc(v_v_1833_);
v_l_1834_ = lean_ctor_get(v_x_1831_, 3);
lean_inc(v_l_1834_);
v_r_1835_ = lean_ctor_get(v_x_1831_, 4);
lean_inc(v_r_1835_);
lean_dec_ref_known(v_x_1831_, 5);
v___x_1836_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_init_1830_, v_l_1834_);
v___x_1837_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1832_, v_v_1833_, v___x_1836_);
v_init_1830_ = v___x_1837_;
v_x_1831_ = v_r_1835_;
goto _start;
}
else
{
return v_init_1830_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mergeObj(lean_object* v_x_1839_, lean_object* v_x_1840_){
_start:
{
if (lean_obj_tag(v_x_1839_) == 5)
{
if (lean_obj_tag(v_x_1840_) == 5)
{
lean_object* v_kvPairs_1841_; lean_object* v_kvPairs_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1850_; 
v_kvPairs_1841_ = lean_ctor_get(v_x_1839_, 0);
lean_inc(v_kvPairs_1841_);
lean_dec_ref_known(v_x_1839_, 1);
v_kvPairs_1842_ = lean_ctor_get(v_x_1840_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v_x_1840_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1844_ = v_x_1840_;
v_isShared_1845_ = v_isSharedCheck_1850_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_kvPairs_1842_);
lean_dec(v_x_1840_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1850_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1846_; lean_object* v___x_1848_; 
v___x_1846_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_kvPairs_1841_, v_kvPairs_1842_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v___x_1846_);
v___x_1848_ = v___x_1844_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1846_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
else
{
lean_dec_ref_known(v_x_1839_, 1);
return v_x_1840_;
}
}
else
{
lean_dec(v_x_1839_);
return v_x_1840_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0(lean_object* v_init_1851_, lean_object* v_t_1852_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_init_1851_, v_t_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorIdx(lean_object* v_x_1854_){
_start:
{
if (lean_obj_tag(v_x_1854_) == 0)
{
lean_object* v___x_1855_; 
v___x_1855_ = lean_unsigned_to_nat(0u);
return v___x_1855_;
}
else
{
lean_object* v___x_1856_; 
v___x_1856_ = lean_unsigned_to_nat(1u);
return v___x_1856_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorIdx___boxed(lean_object* v_x_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lean_Json_Structured_ctorIdx(v_x_1857_);
lean_dec_ref(v_x_1857_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim___redArg(lean_object* v_t_1859_, lean_object* v_k_1860_){
_start:
{
if (lean_obj_tag(v_t_1859_) == 0)
{
lean_object* v_elems_1861_; lean_object* v___x_1862_; 
v_elems_1861_ = lean_ctor_get(v_t_1859_, 0);
lean_inc_ref(v_elems_1861_);
lean_dec_ref_known(v_t_1859_, 1);
v___x_1862_ = lean_apply_1(v_k_1860_, v_elems_1861_);
return v___x_1862_;
}
else
{
lean_object* v_kvPairs_1863_; lean_object* v___x_1864_; 
v_kvPairs_1863_ = lean_ctor_get(v_t_1859_, 0);
lean_inc(v_kvPairs_1863_);
lean_dec_ref_known(v_t_1859_, 1);
v___x_1864_ = lean_apply_1(v_k_1860_, v_kvPairs_1863_);
return v___x_1864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim(lean_object* v_motive_1865_, lean_object* v_ctorIdx_1866_, lean_object* v_t_1867_, lean_object* v_h_1868_, lean_object* v_k_1869_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1867_, v_k_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim___boxed(lean_object* v_motive_1871_, lean_object* v_ctorIdx_1872_, lean_object* v_t_1873_, lean_object* v_h_1874_, lean_object* v_k_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_Json_Structured_ctorElim(v_motive_1871_, v_ctorIdx_1872_, v_t_1873_, v_h_1874_, v_k_1875_);
lean_dec(v_ctorIdx_1872_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_arr_elim___redArg(lean_object* v_t_1877_, lean_object* v_arr_1878_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1877_, v_arr_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_arr_elim(lean_object* v_motive_1880_, lean_object* v_t_1881_, lean_object* v_h_1882_, lean_object* v_arr_1883_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1881_, v_arr_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_obj_elim___redArg(lean_object* v_t_1885_, lean_object* v_obj_1886_){
_start:
{
lean_object* v___x_1887_; 
v___x_1887_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1885_, v_obj_1886_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_obj_elim(lean_object* v_motive_1888_, lean_object* v_t_1889_, lean_object* v_h_1890_, lean_object* v_obj_1891_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1889_, v_obj_1891_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeArrayStructured___lam__0(lean_object* v_elems_1893_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1894_, 0, v_elems_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeRawStringStructured___lam__0(lean_object* v_kvPairs_1897_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1898_, 0, v_kvPairs_1897_);
return v___x_1898_;
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
