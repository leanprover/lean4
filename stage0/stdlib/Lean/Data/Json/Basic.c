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
uint8_t v___y_146_; lean_object* v___y_147_; lean_object* v___y_148_; lean_object* v_fst_149_; lean_object* v_snd_150_; lean_object* v_fst_154_; lean_object* v_snd_155_; lean_object* v___x_172_; lean_object* v_fst_173_; lean_object* v_snd_174_; lean_object* v___x_175_; lean_object* v_fst_176_; lean_object* v_snd_177_; uint8_t v___y_179_; lean_object* v___x_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
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
if (v___y_146_ == 0)
{
uint8_t v___x_151_; 
v___x_151_ = lean_int_dec_lt(v___y_148_, v___y_147_);
lean_dec(v___y_147_);
lean_dec(v___y_148_);
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
return v___y_146_;
}
}
else
{
lean_dec(v_snd_150_);
lean_dec(v_fst_149_);
lean_dec(v___y_148_);
lean_dec(v___y_147_);
return v___y_146_;
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
v___y_146_ = v___x_162_;
v___y_147_ = v_snd_157_;
v___y_148_ = v_snd_159_;
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
v___y_146_ = v___x_162_;
v___y_147_ = v_snd_157_;
v___y_148_ = v_snd_159_;
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
lean_object* v_i_x27_219_; uint32_t v_c_220_; uint32_t v___x_221_; uint8_t v___x_222_; 
v_i_x27_219_ = lean_string_utf8_prev(v_s_215_, v_i_217_);
v_c_220_ = lean_string_utf8_get(v_s_215_, v_i_x27_219_);
v___x_221_ = 48;
v___x_222_ = lean_uint32_dec_eq(v_c_220_, v___x_221_);
if (v___x_222_ == 0)
{
lean_dec(v_i_x27_219_);
return v_i_217_;
}
else
{
lean_dec(v_i_217_);
v_i_217_ = v_i_x27_219_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0___boxed(lean_object* v_s_224_, lean_object* v_begPos_225_, lean_object* v_i_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0(v_s_224_, v_begPos_225_, v_i_226_);
lean_dec(v_begPos_225_);
lean_dec_ref(v_s_224_);
return v_res_227_;
}
}
static lean_object* _init_l_Lean_JsonNumber_toString___closed__3(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = lean_unsigned_to_nat(9u);
v___x_232_ = lean_nat_to_int(v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_toString(lean_object* v_x_234_){
_start:
{
lean_object* v___y_236_; lean_object* v___y_237_; lean_object* v___y_238_; lean_object* v___y_239_; lean_object* v_mantissa_245_; lean_object* v_exponent_246_; lean_object* v___x_247_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v___y_251_; uint8_t v___y_252_; lean_object* v___y_253_; lean_object* v___y_254_; uint8_t v___y_255_; uint8_t v___x_269_; 
v_mantissa_245_ = lean_ctor_get(v_x_234_, 0);
lean_inc(v_mantissa_245_);
v_exponent_246_ = lean_ctor_get(v_x_234_, 1);
lean_inc(v_exponent_246_);
lean_dec_ref(v_x_234_);
v___x_247_ = lean_unsigned_to_nat(0u);
v___x_269_ = lean_nat_dec_eq(v_exponent_246_, v___x_247_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; lean_object* v___y_272_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v___y_285_; uint8_t v___x_294_; 
v___x_270_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v___x_294_ = lean_int_dec_le(v___x_270_, v_mantissa_245_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; 
v___x_295_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__4));
v___y_285_ = v___x_295_;
goto v___jp_284_;
}
else
{
lean_object* v___x_296_; 
v___x_296_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__2));
v___y_285_ = v___x_296_;
goto v___jp_284_;
}
v___jp_271_:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v_e_x27_278_; lean_object* v___x_279_; lean_object* v_left_280_; uint8_t v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_275_ = lean_unsigned_to_nat(10u);
v___x_276_ = lean_nat_abs(v___y_274_);
v___x_277_ = lean_nat_sub(v_exponent_246_, v___x_276_);
lean_dec(v___x_276_);
lean_dec(v_exponent_246_);
v_e_x27_278_ = lean_nat_pow(v___x_275_, v___x_277_);
lean_dec(v___x_277_);
v___x_279_ = lean_nat_div(v___y_272_, v_e_x27_278_);
v_left_280_ = l_Nat_reprFast(v___x_279_);
v___x_281_ = lean_int_dec_eq(v___y_274_, v___x_270_);
v___x_282_ = lean_nat_mod(v___y_272_, v_e_x27_278_);
lean_dec(v___y_272_);
v___x_283_ = lean_nat_dec_eq(v___x_282_, v___x_247_);
if (v___x_283_ == 0)
{
v___y_249_ = v___y_274_;
v___y_250_ = v___x_282_;
v___y_251_ = v_e_x27_278_;
v___y_252_ = v___x_281_;
v___y_253_ = v___y_273_;
v___y_254_ = v_left_280_;
v___y_255_ = v___x_283_;
goto v___jp_248_;
}
else
{
v___y_249_ = v___y_274_;
v___y_250_ = v___x_282_;
v___y_251_ = v_e_x27_278_;
v___y_252_ = v___x_281_;
v___y_253_ = v___y_273_;
v___y_254_ = v_left_280_;
v___y_255_ = v___x_281_;
goto v___jp_248_;
}
}
v___jp_284_:
{
lean_object* v_m_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v_exp_292_; uint8_t v___x_293_; 
v_m_286_ = lean_nat_abs(v_mantissa_245_);
lean_dec(v_mantissa_245_);
v___x_287_ = lean_obj_once(&l_Lean_JsonNumber_toString___closed__3, &l_Lean_JsonNumber_toString___closed__3_once, _init_l_Lean_JsonNumber_toString___closed__3);
lean_inc(v_m_286_);
v___x_288_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(v_m_286_);
v___x_289_ = lean_nat_to_int(v___x_288_);
v___x_290_ = lean_int_add(v___x_287_, v___x_289_);
lean_dec(v___x_289_);
lean_inc(v_exponent_246_);
v___x_291_ = lean_nat_to_int(v_exponent_246_);
v_exp_292_ = lean_int_sub(v___x_290_, v___x_291_);
lean_dec(v___x_291_);
lean_dec(v___x_290_);
v___x_293_ = lean_int_dec_lt(v_exp_292_, v___x_270_);
if (v___x_293_ == 0)
{
lean_dec(v_exp_292_);
v___y_272_ = v_m_286_;
v___y_273_ = v___y_285_;
v___y_274_ = v___x_270_;
goto v___jp_271_;
}
else
{
v___y_272_ = v_m_286_;
v___y_273_ = v___y_285_;
v___y_274_ = v_exp_292_;
goto v___jp_271_;
}
}
}
else
{
lean_object* v___x_297_; 
lean_dec(v_exponent_246_);
v___x_297_ = l_Int_repr(v_mantissa_245_);
lean_dec(v_mantissa_245_);
return v___x_297_;
}
v___jp_235_:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
lean_inc_ref(v___y_237_);
v___x_240_ = lean_string_append(v___y_237_, v___y_238_);
lean_dec_ref(v___y_238_);
v___x_241_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__0));
v___x_242_ = lean_string_append(v___x_240_, v___x_241_);
v___x_243_ = lean_string_append(v___x_242_, v___y_236_);
lean_dec_ref(v___y_236_);
v___x_244_ = lean_string_append(v___x_243_, v___y_239_);
lean_dec_ref(v___y_239_);
return v___x_244_;
}
v___jp_248_:
{
if (v___y_255_ == 0)
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v_e_262_; lean_object* v_right_263_; 
v___x_256_ = lean_nat_add(v___y_251_, v___y_250_);
lean_dec(v___y_250_);
lean_dec(v___y_251_);
v___x_257_ = l_Nat_reprFast(v___x_256_);
v___x_258_ = lean_string_utf8_byte_size(v___x_257_);
lean_inc_ref(v___x_257_);
v___x_259_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_259_, 0, v___x_257_);
lean_ctor_set(v___x_259_, 1, v___x_247_);
lean_ctor_set(v___x_259_, 2, v___x_258_);
v___x_260_ = lean_unsigned_to_nat(1u);
v___x_261_ = l_Substring_Raw_nextn(v___x_259_, v___x_260_, v___x_247_);
lean_dec_ref_known(v___x_259_, 3);
v_e_262_ = l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0(v___x_257_, v___x_261_, v___x_258_);
v_right_263_ = lean_string_utf8_extract(v___x_257_, v___x_261_, v_e_262_);
lean_dec(v_e_262_);
lean_dec(v___x_261_);
lean_dec_ref(v___x_257_);
if (v___y_252_ == 0)
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_264_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__1));
v___x_265_ = l_Int_repr(v___y_249_);
lean_dec(v___y_249_);
v___x_266_ = lean_string_append(v___x_264_, v___x_265_);
lean_dec_ref(v___x_265_);
v___y_236_ = v_right_263_;
v___y_237_ = v___y_253_;
v___y_238_ = v___y_254_;
v___y_239_ = v___x_266_;
goto v___jp_235_;
}
else
{
lean_object* v___x_267_; 
lean_dec(v___y_249_);
v___x_267_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__2));
v___y_236_ = v_right_263_;
v___y_237_ = v___y_253_;
v___y_238_ = v___y_254_;
v___y_239_ = v___x_267_;
goto v___jp_235_;
}
}
else
{
lean_object* v___x_268_; 
lean_dec(v___y_251_);
lean_dec(v___y_250_);
lean_dec(v___y_249_);
lean_inc_ref(v___y_253_);
v___x_268_ = lean_string_append(v___y_253_, v___y_254_);
lean_dec_ref(v___y_254_);
return v___x_268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftl(lean_object* v_x_298_, lean_object* v_x_299_){
_start:
{
lean_object* v_mantissa_300_; lean_object* v_exponent_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_314_; 
v_mantissa_300_ = lean_ctor_get(v_x_298_, 0);
v_exponent_301_ = lean_ctor_get(v_x_298_, 1);
v_isSharedCheck_314_ = !lean_is_exclusive(v_x_298_);
if (v_isSharedCheck_314_ == 0)
{
v___x_303_ = v_x_298_;
v_isShared_304_ = v_isSharedCheck_314_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_exponent_301_);
lean_inc(v_mantissa_300_);
lean_dec(v_x_298_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_314_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_305_ = lean_unsigned_to_nat(10u);
v___x_306_ = lean_nat_sub(v_x_299_, v_exponent_301_);
v___x_307_ = lean_nat_pow(v___x_305_, v___x_306_);
lean_dec(v___x_306_);
v___x_308_ = lean_nat_to_int(v___x_307_);
v___x_309_ = lean_int_mul(v_mantissa_300_, v___x_308_);
lean_dec(v___x_308_);
lean_dec(v_mantissa_300_);
v___x_310_ = lean_nat_sub(v_exponent_301_, v_x_299_);
lean_dec(v_exponent_301_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 1, v___x_310_);
lean_ctor_set(v___x_303_, 0, v___x_309_);
v___x_312_ = v___x_303_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_309_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v___x_310_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftl___boxed(lean_object* v_x_315_, lean_object* v_x_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_JsonNumber_shiftl(v_x_315_, v_x_316_);
lean_dec(v_x_316_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftr(lean_object* v_x_318_, lean_object* v_x_319_){
_start:
{
lean_object* v_mantissa_320_; lean_object* v_exponent_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_329_; 
v_mantissa_320_ = lean_ctor_get(v_x_318_, 0);
v_exponent_321_ = lean_ctor_get(v_x_318_, 1);
v_isSharedCheck_329_ = !lean_is_exclusive(v_x_318_);
if (v_isSharedCheck_329_ == 0)
{
v___x_323_ = v_x_318_;
v_isShared_324_ = v_isSharedCheck_329_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_exponent_321_);
lean_inc(v_mantissa_320_);
lean_dec(v_x_318_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_329_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_325_ = lean_nat_add(v_exponent_321_, v_x_319_);
lean_dec(v_exponent_321_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 1, v___x_325_);
v___x_327_ = v___x_323_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_mantissa_320_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v___x_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftr___boxed(lean_object* v_x_330_, lean_object* v_x_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_JsonNumber_shiftr(v_x_330_, v_x_331_);
lean_dec(v_x_331_);
return v_res_332_;
}
}
static lean_object* _init_l_Lean_JsonNumber_instRepr___lam__0___closed__4(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = ((lean_object*)(l_Lean_JsonNumber_instRepr___lam__0___closed__0));
v___x_341_ = lean_string_length(v___x_340_);
return v___x_341_;
}
}
static lean_object* _init_l_Lean_JsonNumber_instRepr___lam__0___closed__5(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_obj_once(&l_Lean_JsonNumber_instRepr___lam__0___closed__4, &l_Lean_JsonNumber_instRepr___lam__0___closed__4_once, _init_l_Lean_JsonNumber_instRepr___lam__0___closed__4);
v___x_343_ = lean_nat_to_int(v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instRepr___lam__0(lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
lean_object* v_mantissa_350_; lean_object* v_exponent_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_380_; 
v_mantissa_350_ = lean_ctor_get(v_x_348_, 0);
v_exponent_351_ = lean_ctor_get(v_x_348_, 1);
v_isSharedCheck_380_ = !lean_is_exclusive(v_x_348_);
if (v_isSharedCheck_380_ == 0)
{
v___x_353_ = v_x_348_;
v_isShared_354_ = v_isSharedCheck_380_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_exponent_351_);
lean_inc(v_mantissa_350_);
lean_dec(v_x_348_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_380_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___y_356_; lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_372_ = lean_unsigned_to_nat(0u);
v___x_373_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v___x_374_ = lean_int_dec_lt(v_mantissa_350_, v___x_373_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = l_Int_repr(v_mantissa_350_);
lean_dec(v_mantissa_350_);
v___x_376_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
v___y_356_ = v___x_376_;
goto v___jp_355_;
}
else
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_377_ = l_Int_repr(v_mantissa_350_);
lean_dec(v_mantissa_350_);
v___x_378_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
v___x_379_ = l_Repr_addAppParen(v___x_378_, v___x_372_);
v___y_356_ = v___x_379_;
goto v___jp_355_;
}
v___jp_355_:
{
lean_object* v___x_357_; lean_object* v___x_359_; 
v___x_357_ = ((lean_object*)(l_Lean_JsonNumber_instRepr___lam__0___closed__2));
if (v_isShared_354_ == 0)
{
lean_ctor_set_tag(v___x_353_, 5);
lean_ctor_set(v___x_353_, 1, v___x_357_);
lean_ctor_set(v___x_353_, 0, v___y_356_);
v___x_359_ = v___x_353_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___y_356_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v___x_357_);
v___x_359_ = v_reuseFailAlloc_371_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; uint8_t v___x_369_; lean_object* v___x_370_; 
v___x_360_ = l_Nat_reprFast(v_exponent_351_);
v___x_361_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
v___x_362_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_359_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = lean_obj_once(&l_Lean_JsonNumber_instRepr___lam__0___closed__5, &l_Lean_JsonNumber_instRepr___lam__0___closed__5_once, _init_l_Lean_JsonNumber_instRepr___lam__0___closed__5);
v___x_364_ = ((lean_object*)(l_Lean_JsonNumber_instRepr___lam__0___closed__6));
v___x_365_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v___x_362_);
v___x_366_ = ((lean_object*)(l_Lean_JsonNumber_instRepr___lam__0___closed__7));
v___x_367_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_365_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
v___x_368_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_363_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v___x_369_ = 0;
v___x_370_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_370_, 0, v___x_368_);
lean_ctor_set_uint8(v___x_370_, sizeof(void*)*1, v___x_369_);
return v___x_370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instRepr___lam__0___boxed(lean_object* v_x_381_, lean_object* v_x_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_JsonNumber_instRepr___lam__0(v_x_381_, v_x_382_);
lean_dec(v_x_382_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOfScientific___lam__0(lean_object* v_mantissa_386_, uint8_t v_exponentSign_387_, lean_object* v_decimalExponent_388_){
_start:
{
if (v_exponentSign_387_ == 0)
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_389_ = lean_unsigned_to_nat(10u);
v___x_390_ = lean_nat_pow(v___x_389_, v_decimalExponent_388_);
lean_dec(v_decimalExponent_388_);
v___x_391_ = lean_nat_mul(v_mantissa_386_, v___x_390_);
lean_dec(v___x_390_);
lean_dec(v_mantissa_386_);
v___x_392_ = lean_nat_to_int(v___x_391_);
v___x_393_ = lean_unsigned_to_nat(0u);
v___x_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_392_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
return v___x_394_;
}
else
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = lean_nat_to_int(v_mantissa_386_);
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v_decimalExponent_388_);
return v___x_396_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOfScientific___lam__0___boxed(lean_object* v_mantissa_397_, lean_object* v_exponentSign_398_, lean_object* v_decimalExponent_399_){
_start:
{
uint8_t v_exponentSign_boxed_400_; lean_object* v_res_401_; 
v_exponentSign_boxed_400_ = lean_unbox(v_exponentSign_398_);
v_res_401_ = l_Lean_JsonNumber_instOfScientific___lam__0(v_mantissa_397_, v_exponentSign_boxed_400_, v_decimalExponent_399_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instNeg___lam__0(lean_object* v_jn_404_){
_start:
{
lean_object* v_mantissa_405_; lean_object* v_exponent_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_414_; 
v_mantissa_405_ = lean_ctor_get(v_jn_404_, 0);
v_exponent_406_ = lean_ctor_get(v_jn_404_, 1);
v_isSharedCheck_414_ = !lean_is_exclusive(v_jn_404_);
if (v_isSharedCheck_414_ == 0)
{
v___x_408_ = v_jn_404_;
v_isShared_409_ = v_isSharedCheck_414_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_exponent_406_);
lean_inc(v_mantissa_405_);
lean_dec(v_jn_404_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_414_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_410_; lean_object* v___x_412_; 
v___x_410_ = lean_int_neg(v_mantissa_405_);
lean_dec(v_mantissa_405_);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 0, v___x_410_);
v___x_412_ = v___x_408_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_410_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_exponent_406_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
static lean_object* _init_l_Lean_JsonNumber_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_418_ = l_Lean_JsonNumber_fromNat(v___x_417_);
return v___x_418_;
}
}
static lean_object* _init_l_Lean_JsonNumber_instInhabited(void){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = lean_obj_once(&l_Lean_JsonNumber_instInhabited___closed__0, &l_Lean_JsonNumber_instInhabited___closed__0_once, _init_l_Lean_JsonNumber_instInhabited___closed__0);
return v___x_419_;
}
}
static double _init_l_Lean_JsonNumber_toFloat___closed__0(void){
_start:
{
lean_object* v___x_420_; uint8_t v___x_421_; lean_object* v___x_422_; double v___x_423_; 
v___x_420_ = lean_unsigned_to_nat(1u);
v___x_421_ = 1;
v___x_422_ = lean_unsigned_to_nat(10u);
v___x_423_ = l_Float_ofScientific(v___x_422_, v___x_421_, v___x_420_);
return v___x_423_;
}
}
static double _init_l_Lean_JsonNumber_toFloat___closed__1(void){
_start:
{
double v___x_424_; double v___x_425_; 
v___x_424_ = lean_float_once(&l_Lean_JsonNumber_toFloat___closed__0, &l_Lean_JsonNumber_toFloat___closed__0_once, _init_l_Lean_JsonNumber_toFloat___closed__0);
v___x_425_ = lean_float_negate(v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT double l_Lean_JsonNumber_toFloat(lean_object* v_x_426_){
_start:
{
lean_object* v_mantissa_427_; lean_object* v_exponent_428_; double v___y_430_; lean_object* v___x_435_; uint8_t v___x_436_; 
v_mantissa_427_ = lean_ctor_get(v_x_426_, 0);
lean_inc(v_mantissa_427_);
v_exponent_428_ = lean_ctor_get(v_x_426_, 1);
lean_inc(v_exponent_428_);
lean_dec_ref(v_x_426_);
v___x_435_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v___x_436_ = lean_int_dec_le(v___x_435_, v_mantissa_427_);
if (v___x_436_ == 0)
{
double v___x_437_; 
v___x_437_ = lean_float_once(&l_Lean_JsonNumber_toFloat___closed__1, &l_Lean_JsonNumber_toFloat___closed__1_once, _init_l_Lean_JsonNumber_toFloat___closed__1);
v___y_430_ = v___x_437_;
goto v___jp_429_;
}
else
{
lean_object* v___x_438_; lean_object* v___x_439_; double v___x_440_; 
v___x_438_ = lean_unsigned_to_nat(10u);
v___x_439_ = lean_unsigned_to_nat(1u);
v___x_440_ = l_Float_ofScientific(v___x_438_, v___x_436_, v___x_439_);
v___y_430_ = v___x_440_;
goto v___jp_429_;
}
v___jp_429_:
{
lean_object* v___x_431_; uint8_t v___x_432_; double v___x_433_; double v___x_434_; 
v___x_431_ = lean_nat_abs(v_mantissa_427_);
lean_dec(v_mantissa_427_);
v___x_432_ = 1;
v___x_433_ = l_Float_ofScientific(v___x_431_, v___x_432_, v_exponent_428_);
v___x_434_ = lean_float_mul(v___y_430_, v___x_433_);
return v___x_434_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_toFloat___boxed(lean_object* v_x_441_){
_start:
{
double v_res_442_; lean_object* v_r_443_; 
v_res_442_ = l_Lean_JsonNumber_toFloat(v_x_441_);
v_r_443_ = lean_box_float(v_res_442_);
return v_r_443_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21_spec__0(lean_object* v_msg_444_){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = l_Lean_JsonNumber_instInhabited;
v___x_446_ = lean_panic_fn_borrowed(v___x_445_, v_msg_444_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(double v_x_450_){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = lean_float_to_string(v_x_450_);
v___x_452_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v___x_451_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_453_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0));
v___x_454_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__1));
v___x_455_ = lean_unsigned_to_nat(160u);
v___x_456_ = lean_unsigned_to_nat(12u);
v___x_457_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__2));
v___x_458_ = lean_string_append(v___x_457_, v___x_451_);
lean_dec_ref(v___x_451_);
v___x_459_ = l_mkPanicMessageWithDecl(v___x_453_, v___x_454_, v___x_455_, v___x_456_, v___x_458_);
lean_dec_ref(v___x_458_);
v___x_460_ = l_panic___at___00__private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21_spec__0(v___x_459_);
return v___x_460_;
}
else
{
lean_object* v_val_461_; lean_object* v_snd_462_; lean_object* v_fst_463_; uint8_t v___x_464_; 
lean_dec_ref(v___x_451_);
v_val_461_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_val_461_);
lean_dec_ref_known(v___x_452_, 1);
v_snd_462_ = lean_ctor_get(v_val_461_, 1);
lean_inc(v_snd_462_);
v_fst_463_ = lean_ctor_get(v_snd_462_, 0);
v___x_464_ = lean_unbox(v_fst_463_);
if (v___x_464_ == 0)
{
lean_object* v_fst_465_; lean_object* v_snd_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_478_; 
v_fst_465_ = lean_ctor_get(v_val_461_, 0);
lean_inc(v_fst_465_);
lean_dec(v_val_461_);
v_snd_466_ = lean_ctor_get(v_snd_462_, 1);
v_isSharedCheck_478_ = !lean_is_exclusive(v_snd_462_);
if (v_isSharedCheck_478_ == 0)
{
lean_object* v_unused_479_; 
v_unused_479_ = lean_ctor_get(v_snd_462_, 0);
lean_dec(v_unused_479_);
v___x_468_ = v_snd_462_;
v_isShared_469_ = v_isSharedCheck_478_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_snd_466_);
lean_dec(v_snd_462_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_478_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_470_ = lean_unsigned_to_nat(10u);
v___x_471_ = lean_nat_pow(v___x_470_, v_snd_466_);
lean_dec(v_snd_466_);
v___x_472_ = lean_nat_mul(v_fst_465_, v___x_471_);
lean_dec(v___x_471_);
lean_dec(v_fst_465_);
v___x_473_ = lean_nat_to_int(v___x_472_);
v___x_474_ = lean_unsigned_to_nat(0u);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 1, v___x_474_);
lean_ctor_set(v___x_468_, 0, v___x_473_);
v___x_476_ = v___x_468_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v___x_474_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
else
{
lean_object* v_fst_480_; lean_object* v_snd_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_489_; 
v_fst_480_ = lean_ctor_get(v_val_461_, 0);
lean_inc(v_fst_480_);
lean_dec(v_val_461_);
v_snd_481_ = lean_ctor_get(v_snd_462_, 1);
v_isSharedCheck_489_ = !lean_is_exclusive(v_snd_462_);
if (v_isSharedCheck_489_ == 0)
{
lean_object* v_unused_490_; 
v_unused_490_ = lean_ctor_get(v_snd_462_, 0);
lean_dec(v_unused_490_);
v___x_483_ = v_snd_462_;
v_isShared_484_ = v_isSharedCheck_489_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_snd_481_);
lean_dec(v_snd_462_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_489_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_485_ = lean_nat_to_int(v_fst_480_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v___x_485_);
v___x_487_ = v___x_483_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_snd_481_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___boxed(lean_object* v_x_491_){
_start:
{
double v_x_boxed_492_; lean_object* v_res_493_; 
v_x_boxed_492_ = lean_unbox_float(v_x_491_);
lean_dec_ref(v_x_491_);
v_res_493_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(v_x_boxed_492_);
return v_res_493_;
}
}
static double _init_l_Lean_JsonNumber_fromFloat_x3f___closed__0(void){
_start:
{
lean_object* v___x_494_; uint8_t v___x_495_; lean_object* v___x_496_; double v___x_497_; 
v___x_494_ = lean_unsigned_to_nat(1u);
v___x_495_ = 1;
v___x_496_ = lean_unsigned_to_nat(0u);
v___x_497_ = l_Float_ofScientific(v___x_496_, v___x_495_, v___x_494_);
return v___x_497_;
}
}
static lean_object* _init_l_Lean_JsonNumber_fromFloat_x3f___closed__1(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_obj_once(&l_Lean_JsonNumber_instInhabited___closed__0, &l_Lean_JsonNumber_instInhabited___closed__0_once, _init_l_Lean_JsonNumber_instInhabited___closed__0);
v___x_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
return v___x_499_;
}
}
static double _init_l_Lean_JsonNumber_fromFloat_x3f___closed__2(void){
_start:
{
lean_object* v___x_500_; double v___x_501_; 
v___x_500_ = lean_unsigned_to_nat(0u);
v___x_501_ = lean_float_of_nat(v___x_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_fromFloat_x3f(double v_x_511_){
_start:
{
uint8_t v___x_512_; 
v___x_512_ = lean_float_isnan(v_x_511_);
if (v___x_512_ == 0)
{
uint8_t v___x_513_; 
v___x_513_ = lean_float_isinf(v_x_511_);
if (v___x_513_ == 0)
{
double v___x_514_; uint8_t v___x_515_; 
v___x_514_ = lean_float_once(&l_Lean_JsonNumber_fromFloat_x3f___closed__0, &l_Lean_JsonNumber_fromFloat_x3f___closed__0_once, _init_l_Lean_JsonNumber_fromFloat_x3f___closed__0);
v___x_515_ = lean_float_beq(v_x_511_, v___x_514_);
if (v___x_515_ == 0)
{
uint8_t v___x_516_; 
v___x_516_ = lean_float_decLt(v_x_511_, v___x_514_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(v_x_511_);
v___x_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
return v___x_518_;
}
else
{
double v___x_519_; lean_object* v___x_520_; lean_object* v_mantissa_521_; lean_object* v_exponent_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_531_; 
v___x_519_ = lean_float_negate(v_x_511_);
v___x_520_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(v___x_519_);
v_mantissa_521_ = lean_ctor_get(v___x_520_, 0);
v_exponent_522_ = lean_ctor_get(v___x_520_, 1);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_531_ == 0)
{
v___x_524_ = v___x_520_;
v_isShared_525_ = v_isSharedCheck_531_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_exponent_522_);
lean_inc(v_mantissa_521_);
lean_dec(v___x_520_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_531_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_526_ = lean_int_neg(v_mantissa_521_);
lean_dec(v_mantissa_521_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v___x_526_);
v___x_528_ = v___x_524_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_exponent_522_);
v___x_528_ = v_reuseFailAlloc_530_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_529_; 
v___x_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
return v___x_529_;
}
}
}
}
else
{
lean_object* v___x_532_; 
v___x_532_ = lean_obj_once(&l_Lean_JsonNumber_fromFloat_x3f___closed__1, &l_Lean_JsonNumber_fromFloat_x3f___closed__1_once, _init_l_Lean_JsonNumber_fromFloat_x3f___closed__1);
return v___x_532_;
}
}
else
{
double v___x_533_; uint8_t v___x_534_; 
v___x_533_ = lean_float_once(&l_Lean_JsonNumber_fromFloat_x3f___closed__2, &l_Lean_JsonNumber_fromFloat_x3f___closed__2_once, _init_l_Lean_JsonNumber_fromFloat_x3f___closed__2);
v___x_534_ = lean_float_decLt(v___x_533_, v_x_511_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; 
v___x_535_ = ((lean_object*)(l_Lean_JsonNumber_fromFloat_x3f___closed__4));
return v___x_535_;
}
else
{
lean_object* v___x_536_; 
v___x_536_ = ((lean_object*)(l_Lean_JsonNumber_fromFloat_x3f___closed__6));
return v___x_536_;
}
}
}
else
{
lean_object* v___x_537_; 
v___x_537_ = ((lean_object*)(l_Lean_JsonNumber_fromFloat_x3f___closed__8));
return v___x_537_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_fromFloat_x3f___boxed(lean_object* v_x_538_){
_start:
{
double v_x_boxed_539_; lean_object* v_res_540_; 
v_x_boxed_539_ = lean_unbox_float(v_x_538_);
lean_dec_ref(v_x_538_);
v_res_540_ = l_Lean_JsonNumber_fromFloat_x3f(v_x_boxed_539_);
return v_res_540_;
}
}
LEAN_EXPORT uint8_t l_Lean_strLt(lean_object* v_a_541_, lean_object* v_b_542_){
_start:
{
uint8_t v___x_543_; 
v___x_543_ = lean_string_dec_lt(v_a_541_, v_b_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_strLt___boxed(lean_object* v_a_544_, lean_object* v_b_545_){
_start:
{
uint8_t v_res_546_; lean_object* v_r_547_; 
v_res_546_ = l_Lean_strLt(v_a_544_, v_b_545_);
lean_dec_ref(v_b_545_);
lean_dec_ref(v_a_544_);
v_r_547_ = lean_box(v_res_546_);
return v_r_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorIdx(lean_object* v_x_548_){
_start:
{
switch(lean_obj_tag(v_x_548_))
{
case 0:
{
lean_object* v___x_549_; 
v___x_549_ = lean_unsigned_to_nat(0u);
return v___x_549_;
}
case 1:
{
lean_object* v___x_550_; 
v___x_550_ = lean_unsigned_to_nat(1u);
return v___x_550_;
}
case 2:
{
lean_object* v___x_551_; 
v___x_551_ = lean_unsigned_to_nat(2u);
return v___x_551_;
}
case 3:
{
lean_object* v___x_552_; 
v___x_552_ = lean_unsigned_to_nat(3u);
return v___x_552_;
}
case 4:
{
lean_object* v___x_553_; 
v___x_553_ = lean_unsigned_to_nat(4u);
return v___x_553_;
}
default: 
{
lean_object* v___x_554_; 
v___x_554_ = lean_unsigned_to_nat(5u);
return v___x_554_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorIdx___boxed(lean_object* v_x_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_Json_ctorIdx(v_x_555_);
lean_dec(v_x_555_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorElim___redArg(lean_object* v_t_557_, lean_object* v_k_558_){
_start:
{
switch(lean_obj_tag(v_t_557_))
{
case 0:
{
return v_k_558_;
}
case 1:
{
uint8_t v_b_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_b_559_ = lean_ctor_get_uint8(v_t_557_, 0);
lean_dec_ref_known(v_t_557_, 0);
v___x_560_ = lean_box(v_b_559_);
v___x_561_ = lean_apply_1(v_k_558_, v___x_560_);
return v___x_561_;
}
case 5:
{
lean_object* v_kvPairs_562_; lean_object* v___x_563_; 
v_kvPairs_562_ = lean_ctor_get(v_t_557_, 0);
lean_inc(v_kvPairs_562_);
lean_dec_ref_known(v_t_557_, 1);
v___x_563_ = lean_apply_1(v_k_558_, v_kvPairs_562_);
return v___x_563_;
}
default: 
{
lean_object* v_n_564_; lean_object* v___x_565_; 
v_n_564_ = lean_ctor_get(v_t_557_, 0);
lean_inc_ref(v_n_564_);
lean_dec(v_t_557_);
v___x_565_ = lean_apply_1(v_k_558_, v_n_564_);
return v___x_565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorElim(lean_object* v_motive__1_566_, lean_object* v_ctorIdx_567_, lean_object* v_t_568_, lean_object* v_h_569_, lean_object* v_k_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Lean_Json_ctorElim___redArg(v_t_568_, v_k_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorElim___boxed(lean_object* v_motive__1_572_, lean_object* v_ctorIdx_573_, lean_object* v_t_574_, lean_object* v_h_575_, lean_object* v_k_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_Json_ctorElim(v_motive__1_572_, v_ctorIdx_573_, v_t_574_, v_h_575_, v_k_576_);
lean_dec(v_ctorIdx_573_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_null_elim___redArg(lean_object* v_t_578_, lean_object* v_null_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_Json_ctorElim___redArg(v_t_578_, v_null_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_null_elim(lean_object* v_motive__1_581_, lean_object* v_t_582_, lean_object* v_h_583_, lean_object* v_null_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_Json_ctorElim___redArg(v_t_582_, v_null_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_bool_elim___redArg(lean_object* v_t_586_, lean_object* v_bool_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_Json_ctorElim___redArg(v_t_586_, v_bool_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_bool_elim(lean_object* v_motive__1_589_, lean_object* v_t_590_, lean_object* v_h_591_, lean_object* v_bool_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_Json_ctorElim___redArg(v_t_590_, v_bool_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_num_elim___redArg(lean_object* v_t_594_, lean_object* v_num_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_Json_ctorElim___redArg(v_t_594_, v_num_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_num_elim(lean_object* v_motive__1_597_, lean_object* v_t_598_, lean_object* v_h_599_, lean_object* v_num_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_Json_ctorElim___redArg(v_t_598_, v_num_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_str_elim___redArg(lean_object* v_t_602_, lean_object* v_str_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_Json_ctorElim___redArg(v_t_602_, v_str_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_str_elim(lean_object* v_motive__1_605_, lean_object* v_t_606_, lean_object* v_h_607_, lean_object* v_str_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Lean_Json_ctorElim___redArg(v_t_606_, v_str_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_arr_elim___redArg(lean_object* v_t_610_, lean_object* v_arr_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_Json_ctorElim___redArg(v_t_610_, v_arr_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_arr_elim(lean_object* v_motive__1_613_, lean_object* v_t_614_, lean_object* v_h_615_, lean_object* v_arr_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Lean_Json_ctorElim___redArg(v_t_614_, v_arr_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_obj_elim___redArg(lean_object* v_t_618_, lean_object* v_obj_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Lean_Json_ctorElim___redArg(v_t_618_, v_obj_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_obj_elim(lean_object* v_motive__1_621_, lean_object* v_t_622_, lean_object* v_h_623_, lean_object* v_obj_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_Json_ctorElim___redArg(v_t_622_, v_obj_624_);
return v___x_625_;
}
}
static lean_object* _init_l_Lean_instInhabitedJson_default(void){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = lean_box(0);
return v___x_626_;
}
}
static lean_object* _init_l_Lean_instInhabitedJson(void){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = lean_box(0);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(lean_object* v_init_628_, lean_object* v_x_629_){
_start:
{
if (lean_obj_tag(v_x_629_) == 0)
{
lean_object* v_l_630_; lean_object* v_r_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v_l_630_ = lean_ctor_get(v_x_629_, 3);
v_r_631_ = lean_ctor_get(v_x_629_, 4);
v___x_632_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_628_, v_l_630_);
v___x_633_ = lean_unsigned_to_nat(1u);
v___x_634_ = lean_nat_add(v___x_632_, v___x_633_);
lean_dec(v___x_632_);
v_init_628_ = v___x_634_;
v_x_629_ = v_r_631_;
goto _start;
}
else
{
return v_init_628_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1___boxed(lean_object* v_init_636_, lean_object* v_x_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_636_, v_x_637_);
lean_dec(v_x_637_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(lean_object* v_t_639_, lean_object* v_k_640_){
_start:
{
if (lean_obj_tag(v_t_639_) == 0)
{
lean_object* v_k_641_; lean_object* v_v_642_; lean_object* v_l_643_; lean_object* v_r_644_; uint8_t v___x_645_; 
v_k_641_ = lean_ctor_get(v_t_639_, 1);
v_v_642_ = lean_ctor_get(v_t_639_, 2);
v_l_643_ = lean_ctor_get(v_t_639_, 3);
v_r_644_ = lean_ctor_get(v_t_639_, 4);
v___x_645_ = lean_string_compare(v_k_640_, v_k_641_);
switch(v___x_645_)
{
case 0:
{
v_t_639_ = v_l_643_;
goto _start;
}
case 1:
{
lean_object* v___x_647_; 
lean_inc(v_v_642_);
v___x_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_647_, 0, v_v_642_);
return v___x_647_;
}
default: 
{
v_t_639_ = v_r_644_;
goto _start;
}
}
}
else
{
lean_object* v___x_649_; 
v___x_649_ = lean_box(0);
return v___x_649_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg___boxed(lean_object* v_t_650_, lean_object* v_k_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_t_650_, v_k_651_);
lean_dec_ref(v_k_651_);
lean_dec(v_t_650_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(lean_object* v_kvPairs_656_, lean_object* v_init_657_, lean_object* v_x_658_){
_start:
{
if (lean_obj_tag(v_x_658_) == 0)
{
lean_object* v_k_659_; lean_object* v_v_660_; lean_object* v_l_661_; lean_object* v_r_662_; lean_object* v___x_663_; 
v_k_659_ = lean_ctor_get(v_x_658_, 1);
v_v_660_ = lean_ctor_get(v_x_658_, 2);
v_l_661_ = lean_ctor_get(v_x_658_, 3);
v_r_662_ = lean_ctor_get(v_x_658_, 4);
v___x_663_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_kvPairs_656_, v_init_657_, v_l_661_);
if (lean_obj_tag(v___x_663_) == 0)
{
return v___x_663_;
}
else
{
lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_682_; 
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_682_ == 0)
{
lean_object* v_unused_683_; 
v_unused_683_ = lean_ctor_get(v___x_663_, 0);
lean_dec(v_unused_683_);
v___x_665_ = v___x_663_;
v_isShared_666_ = v_isSharedCheck_682_;
goto v_resetjp_664_;
}
else
{
lean_dec(v___x_663_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_682_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; uint8_t v___y_669_; lean_object* v___x_676_; 
v___x_667_ = lean_box(0);
v___x_676_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_kvPairs_656_, v_k_659_);
if (lean_obj_tag(v___x_676_) == 0)
{
uint8_t v___x_677_; 
v___x_677_ = 0;
v___y_669_ = v___x_677_;
goto v___jp_668_;
}
else
{
lean_object* v_val_678_; uint8_t v___x_679_; 
v_val_678_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_val_678_);
lean_dec_ref_known(v___x_676_, 1);
v___x_679_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_v_660_, v_val_678_);
lean_dec(v_val_678_);
if (v___x_679_ == 0)
{
v___y_669_ = v___x_679_;
goto v___jp_668_;
}
else
{
lean_object* v___x_680_; 
lean_del_object(v___x_665_);
v___x_680_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__0));
v_init_657_ = v___x_680_;
v_x_658_ = v_r_662_;
goto _start;
}
}
v___jp_668_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_670_ = lean_box(v___y_669_);
v___x_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
v___x_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set(v___x_672_, 1, v___x_667_);
if (v_isShared_666_ == 0)
{
lean_ctor_set_tag(v___x_665_, 0);
lean_ctor_set(v___x_665_, 0, v___x_672_);
v___x_674_ = v___x_665_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_672_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
}
else
{
lean_object* v___x_684_; 
v___x_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_684_, 0, v_init_657_);
return v___x_684_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(lean_object* v_x_685_, lean_object* v_x_686_){
_start:
{
switch(lean_obj_tag(v_x_685_))
{
case 0:
{
if (lean_obj_tag(v_x_686_) == 0)
{
uint8_t v___x_687_; 
v___x_687_ = 1;
return v___x_687_;
}
else
{
uint8_t v___x_688_; 
v___x_688_ = 0;
return v___x_688_;
}
}
case 1:
{
if (lean_obj_tag(v_x_686_) == 1)
{
uint8_t v_b_689_; 
v_b_689_ = lean_ctor_get_uint8(v_x_685_, 0);
if (v_b_689_ == 0)
{
uint8_t v_b_690_; 
v_b_690_ = lean_ctor_get_uint8(v_x_686_, 0);
if (v_b_690_ == 0)
{
uint8_t v___x_691_; 
v___x_691_ = 1;
return v___x_691_;
}
else
{
return v_b_689_;
}
}
else
{
uint8_t v_b_692_; 
v_b_692_ = lean_ctor_get_uint8(v_x_686_, 0);
return v_b_692_;
}
}
else
{
uint8_t v___x_693_; 
v___x_693_ = 0;
return v___x_693_;
}
}
case 2:
{
if (lean_obj_tag(v_x_686_) == 2)
{
lean_object* v_n_694_; lean_object* v_n_695_; uint8_t v___x_696_; 
v_n_694_ = lean_ctor_get(v_x_685_, 0);
v_n_695_ = lean_ctor_get(v_x_686_, 0);
v___x_696_ = l_Lean_instDecidableEqJsonNumber_decEq(v_n_694_, v_n_695_);
return v___x_696_;
}
else
{
uint8_t v___x_697_; 
v___x_697_ = 0;
return v___x_697_;
}
}
case 3:
{
if (lean_obj_tag(v_x_686_) == 3)
{
lean_object* v_s_698_; lean_object* v_s_699_; uint8_t v___x_700_; 
v_s_698_ = lean_ctor_get(v_x_685_, 0);
v_s_699_ = lean_ctor_get(v_x_686_, 0);
v___x_700_ = lean_string_dec_eq(v_s_698_, v_s_699_);
return v___x_700_;
}
else
{
uint8_t v___x_701_; 
v___x_701_ = 0;
return v___x_701_;
}
}
case 4:
{
if (lean_obj_tag(v_x_686_) == 4)
{
lean_object* v_elems_702_; lean_object* v_elems_703_; lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v_elems_702_ = lean_ctor_get(v_x_685_, 0);
v_elems_703_ = lean_ctor_get(v_x_686_, 0);
v___x_704_ = lean_array_get_size(v_elems_702_);
v___x_705_ = lean_array_get_size(v_elems_703_);
v___x_706_ = lean_nat_dec_eq(v___x_704_, v___x_705_);
if (v___x_706_ == 0)
{
return v___x_706_;
}
else
{
uint8_t v___x_707_; 
v___x_707_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(v_elems_702_, v_elems_703_, v___x_704_);
return v___x_707_;
}
}
else
{
uint8_t v___x_708_; 
v___x_708_ = 0;
return v___x_708_;
}
}
default: 
{
if (lean_obj_tag(v_x_686_) == 5)
{
lean_object* v_kvPairs_709_; lean_object* v_kvPairs_710_; lean_object* v___x_711_; lean_object* v_szA_712_; lean_object* v_szB_713_; uint8_t v___x_714_; lean_object* v___y_716_; 
v_kvPairs_709_ = lean_ctor_get(v_x_685_, 0);
v_kvPairs_710_ = lean_ctor_get(v_x_686_, 0);
v___x_711_ = lean_unsigned_to_nat(0u);
v_szA_712_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v___x_711_, v_kvPairs_709_);
v_szB_713_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v___x_711_, v_kvPairs_710_);
v___x_714_ = lean_nat_dec_eq(v_szA_712_, v_szB_713_);
lean_dec(v_szB_713_);
lean_dec(v_szA_712_);
if (v___x_714_ == 0)
{
return v___x_714_;
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v_a_722_; 
v___x_720_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__0));
v___x_721_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_kvPairs_710_, v___x_720_, v_kvPairs_709_);
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_a_722_);
lean_dec_ref(v___x_721_);
v___y_716_ = v_a_722_;
goto v___jp_715_;
}
v___jp_715_:
{
lean_object* v_fst_717_; 
v_fst_717_ = lean_ctor_get(v___y_716_, 0);
lean_inc(v_fst_717_);
lean_dec_ref(v___y_716_);
if (lean_obj_tag(v_fst_717_) == 0)
{
return v___x_714_;
}
else
{
lean_object* v_val_718_; uint8_t v___x_719_; 
v_val_718_ = lean_ctor_get(v_fst_717_, 0);
lean_inc(v_val_718_);
lean_dec_ref_known(v_fst_717_, 1);
v___x_719_ = lean_unbox(v_val_718_);
lean_dec(v_val_718_);
return v___x_719_;
}
}
}
else
{
uint8_t v___x_723_; 
v___x_723_ = 0;
return v___x_723_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(lean_object* v_xs_724_, lean_object* v_ys_725_, lean_object* v_x_726_){
_start:
{
lean_object* v_zero_727_; uint8_t v_isZero_728_; 
v_zero_727_ = lean_unsigned_to_nat(0u);
v_isZero_728_ = lean_nat_dec_eq(v_x_726_, v_zero_727_);
if (v_isZero_728_ == 1)
{
lean_dec(v_x_726_);
return v_isZero_728_;
}
else
{
lean_object* v_one_729_; lean_object* v_n_730_; lean_object* v___x_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v_one_729_ = lean_unsigned_to_nat(1u);
v_n_730_ = lean_nat_sub(v_x_726_, v_one_729_);
lean_dec(v_x_726_);
v___x_731_ = lean_array_fget_borrowed(v_xs_724_, v_n_730_);
v___x_732_ = lean_array_fget_borrowed(v_ys_725_, v_n_730_);
v___x_733_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v___x_731_, v___x_732_);
if (v___x_733_ == 0)
{
lean_dec(v_n_730_);
return v___x_733_;
}
else
{
v_x_726_ = v_n_730_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg___boxed(lean_object* v_xs_735_, lean_object* v_ys_736_, lean_object* v_x_737_){
_start:
{
uint8_t v_res_738_; lean_object* v_r_739_; 
v_res_738_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(v_xs_735_, v_ys_736_, v_x_737_);
lean_dec_ref(v_ys_736_);
lean_dec_ref(v_xs_735_);
v_r_739_ = lean_box(v_res_738_);
return v_r_739_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___boxed(lean_object* v_kvPairs_740_, lean_object* v_init_741_, lean_object* v_x_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_kvPairs_740_, v_init_741_, v_x_742_);
lean_dec(v_x_742_);
lean_dec(v_kvPairs_740_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___boxed(lean_object* v_x_744_, lean_object* v_x_745_){
_start:
{
uint8_t v_res_746_; lean_object* v_r_747_; 
v_res_746_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_x_744_, v_x_745_);
lean_dec(v_x_745_);
lean_dec(v_x_744_);
v_r_747_ = lean_box(v_res_746_);
return v_r_747_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0(lean_object* v_xs_748_, lean_object* v_ys_749_, lean_object* v_hsz_750_, lean_object* v_x_751_, lean_object* v_x_752_){
_start:
{
uint8_t v___x_753_; 
v___x_753_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(v_xs_748_, v_ys_749_, v_x_751_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___boxed(lean_object* v_xs_754_, lean_object* v_ys_755_, lean_object* v_hsz_756_, lean_object* v_x_757_, lean_object* v_x_758_){
_start:
{
uint8_t v_res_759_; lean_object* v_r_760_; 
v_res_759_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0(v_xs_754_, v_ys_755_, v_hsz_756_, v_x_757_, v_x_758_);
lean_dec_ref(v_ys_755_);
lean_dec_ref(v_xs_754_);
v_r_760_ = lean_box(v_res_759_);
return v_r_760_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1(lean_object* v_init_761_, lean_object* v_t_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_761_, v_t_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___boxed(lean_object* v_init_764_, lean_object* v_t_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1(v_init_764_, v_t_765_);
lean_dec(v_t_765_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2(lean_object* v_00_u03b4_767_, lean_object* v_t_768_, lean_object* v_k_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_t_768_, v_k_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___boxed(lean_object* v_00_u03b4_771_, lean_object* v_t_772_, lean_object* v_k_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2(v_00_u03b4_771_, v_t_772_, v_k_773_);
lean_dec_ref(v_k_773_);
lean_dec(v_t_772_);
return v_res_774_;
}
}
LEAN_EXPORT uint8_t l_Lean_Json_instBEq___private__1(lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
uint8_t v___x_777_; 
v___x_777_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_a_775_, v_a_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instBEq___private__1___boxed(lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
uint8_t v_res_780_; lean_object* v_r_781_; 
v_res_780_ = l_Lean_Json_instBEq___private__1(v_a_778_, v_a_779_);
lean_dec(v_a_779_);
lean_dec(v_a_778_);
v_r_781_ = lean_box(v_res_780_);
return v_r_781_;
}
}
static uint64_t _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__0(void){
_start:
{
uint64_t v___x_784_; uint64_t v___x_785_; 
v___x_784_ = 13ULL;
v___x_785_ = lean_uint64_mix_hash(v___x_784_, v___x_784_);
return v___x_785_;
}
}
static uint64_t _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__1(void){
_start:
{
uint64_t v___x_786_; uint64_t v___x_787_; uint64_t v___x_788_; 
v___x_786_ = 11ULL;
v___x_787_ = 13ULL;
v___x_788_ = lean_uint64_mix_hash(v___x_787_, v___x_786_);
return v___x_788_;
}
}
static uint64_t _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2(void){
_start:
{
uint64_t v___x_789_; uint64_t v___x_790_; uint64_t v___x_791_; 
v___x_789_ = 7ULL;
v___x_790_ = 23ULL;
v___x_791_ = lean_uint64_mix_hash(v___x_790_, v___x_789_);
return v___x_791_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(lean_object* v_as_792_, size_t v_i_793_, size_t v_stop_794_, uint64_t v_b_795_){
_start:
{
uint8_t v___x_796_; 
v___x_796_ = lean_usize_dec_eq(v_i_793_, v_stop_794_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; uint64_t v___x_798_; uint64_t v___x_799_; size_t v___x_800_; size_t v___x_801_; 
v___x_797_ = lean_array_uget_borrowed(v_as_792_, v_i_793_);
v___x_798_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v___x_797_);
v___x_799_ = lean_uint64_mix_hash(v_b_795_, v___x_798_);
v___x_800_ = ((size_t)1ULL);
v___x_801_ = lean_usize_add(v_i_793_, v___x_800_);
v_i_793_ = v___x_801_;
v_b_795_ = v___x_799_;
goto _start;
}
else
{
return v_b_795_;
}
}
}
LEAN_EXPORT uint64_t l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(lean_object* v_x_803_){
_start:
{
switch(lean_obj_tag(v_x_803_))
{
case 0:
{
uint64_t v___x_804_; 
v___x_804_ = 11ULL;
return v___x_804_;
}
case 1:
{
uint8_t v_b_805_; 
v_b_805_ = lean_ctor_get_uint8(v_x_803_, 0);
if (v_b_805_ == 0)
{
uint64_t v___x_806_; 
v___x_806_ = lean_uint64_once(&l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__0, &l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__0_once, _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__0);
return v___x_806_;
}
else
{
uint64_t v___x_807_; 
v___x_807_ = lean_uint64_once(&l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__1, &l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__1_once, _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__1);
return v___x_807_;
}
}
case 2:
{
lean_object* v_n_808_; uint64_t v___x_809_; uint64_t v___x_810_; uint64_t v___x_811_; 
v_n_808_ = lean_ctor_get(v_x_803_, 0);
v___x_809_ = 17ULL;
v___x_810_ = l_Lean_instHashableJsonNumber_hash(v_n_808_);
v___x_811_ = lean_uint64_mix_hash(v___x_809_, v___x_810_);
return v___x_811_;
}
case 3:
{
lean_object* v_s_812_; uint64_t v___x_813_; uint64_t v___x_814_; uint64_t v___x_815_; 
v_s_812_ = lean_ctor_get(v_x_803_, 0);
v___x_813_ = 19ULL;
v___x_814_ = lean_string_hash(v_s_812_);
v___x_815_ = lean_uint64_mix_hash(v___x_813_, v___x_814_);
return v___x_815_;
}
case 4:
{
lean_object* v_elems_816_; uint64_t v___x_817_; uint64_t v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; uint8_t v___x_821_; 
v_elems_816_ = lean_ctor_get(v_x_803_, 0);
v___x_817_ = 23ULL;
v___x_818_ = 7ULL;
v___x_819_ = lean_unsigned_to_nat(0u);
v___x_820_ = lean_array_get_size(v_elems_816_);
v___x_821_ = lean_nat_dec_lt(v___x_819_, v___x_820_);
if (v___x_821_ == 0)
{
uint64_t v___x_822_; 
v___x_822_ = lean_uint64_once(&l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2, &l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2_once, _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2);
return v___x_822_;
}
else
{
uint8_t v___x_823_; 
v___x_823_ = lean_nat_dec_le(v___x_820_, v___x_820_);
if (v___x_823_ == 0)
{
if (v___x_821_ == 0)
{
uint64_t v___x_824_; 
v___x_824_ = lean_uint64_once(&l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2, &l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2_once, _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2);
return v___x_824_;
}
else
{
size_t v___x_825_; size_t v___x_826_; uint64_t v___x_827_; uint64_t v___x_828_; 
v___x_825_ = ((size_t)0ULL);
v___x_826_ = lean_usize_of_nat(v___x_820_);
v___x_827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_elems_816_, v___x_825_, v___x_826_, v___x_818_);
v___x_828_ = lean_uint64_mix_hash(v___x_817_, v___x_827_);
return v___x_828_;
}
}
else
{
size_t v___x_829_; size_t v___x_830_; uint64_t v___x_831_; uint64_t v___x_832_; 
v___x_829_ = ((size_t)0ULL);
v___x_830_ = lean_usize_of_nat(v___x_820_);
v___x_831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_elems_816_, v___x_829_, v___x_830_, v___x_818_);
v___x_832_ = lean_uint64_mix_hash(v___x_817_, v___x_831_);
return v___x_832_;
}
}
}
default: 
{
lean_object* v_kvPairs_833_; uint64_t v___x_834_; uint64_t v___x_835_; uint64_t v___x_836_; uint64_t v___x_837_; 
v_kvPairs_833_ = lean_ctor_get(v_x_803_, 0);
v___x_834_ = 29ULL;
v___x_835_ = 7ULL;
v___x_836_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v___x_835_, v_kvPairs_833_);
v___x_837_ = lean_uint64_mix_hash(v___x_834_, v___x_836_);
return v___x_837_;
}
}
}
}
LEAN_EXPORT uint64_t l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(uint64_t v_init_838_, lean_object* v_x_839_){
_start:
{
if (lean_obj_tag(v_x_839_) == 0)
{
lean_object* v_k_840_; lean_object* v_v_841_; lean_object* v_l_842_; lean_object* v_r_843_; uint64_t v___x_844_; uint64_t v___x_845_; uint64_t v___x_846_; uint64_t v___x_847_; uint64_t v___x_848_; 
v_k_840_ = lean_ctor_get(v_x_839_, 1);
v_v_841_ = lean_ctor_get(v_x_839_, 2);
v_l_842_ = lean_ctor_get(v_x_839_, 3);
v_r_843_ = lean_ctor_get(v_x_839_, 4);
v___x_844_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_838_, v_l_842_);
v___x_845_ = lean_string_hash(v_k_840_);
v___x_846_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_v_841_);
v___x_847_ = lean_uint64_mix_hash(v___x_845_, v___x_846_);
v___x_848_ = lean_uint64_mix_hash(v___x_844_, v___x_847_);
v_init_838_ = v___x_848_;
v_x_839_ = v_r_843_;
goto _start;
}
else
{
return v_init_838_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1___boxed(lean_object* v_init_850_, lean_object* v_x_851_){
_start:
{
uint64_t v_init_boxed_852_; uint64_t v_res_853_; lean_object* v_r_854_; 
v_init_boxed_852_ = lean_unbox_uint64(v_init_850_);
lean_dec_ref(v_init_850_);
v_res_853_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_boxed_852_, v_x_851_);
lean_dec(v_x_851_);
v_r_854_ = lean_box_uint64(v_res_853_);
return v_r_854_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0___boxed(lean_object* v_as_855_, lean_object* v_i_856_, lean_object* v_stop_857_, lean_object* v_b_858_){
_start:
{
size_t v_i_boxed_859_; size_t v_stop_boxed_860_; uint64_t v_b_boxed_861_; uint64_t v_res_862_; lean_object* v_r_863_; 
v_i_boxed_859_ = lean_unbox_usize(v_i_856_);
lean_dec(v_i_856_);
v_stop_boxed_860_ = lean_unbox_usize(v_stop_857_);
lean_dec(v_stop_857_);
v_b_boxed_861_ = lean_unbox_uint64(v_b_858_);
lean_dec_ref(v_b_858_);
v_res_862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_as_855_, v_i_boxed_859_, v_stop_boxed_860_, v_b_boxed_861_);
lean_dec_ref(v_as_855_);
v_r_863_ = lean_box_uint64(v_res_862_);
return v_r_863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___boxed(lean_object* v_x_864_){
_start:
{
uint64_t v_res_865_; lean_object* v_r_866_; 
v_res_865_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_x_864_);
lean_dec(v_x_864_);
v_r_866_ = lean_box_uint64(v_res_865_);
return v_r_866_;
}
}
LEAN_EXPORT uint64_t l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1(uint64_t v_init_867_, lean_object* v_t_868_){
_start:
{
uint64_t v___x_869_; 
v___x_869_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_867_, v_t_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1___boxed(lean_object* v_init_870_, lean_object* v_t_871_){
_start:
{
uint64_t v_init_boxed_872_; uint64_t v_res_873_; lean_object* v_r_874_; 
v_init_boxed_872_ = lean_unbox_uint64(v_init_870_);
lean_dec_ref(v_init_870_);
v_res_873_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1(v_init_boxed_872_, v_t_871_);
lean_dec(v_t_871_);
v_r_874_ = lean_box_uint64(v_res_873_);
return v_r_874_;
}
}
LEAN_EXPORT uint64_t l_Lean_Json_instHashable___private__1(lean_object* v_a_875_){
_start:
{
uint64_t v___x_876_; 
v___x_876_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_a_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instHashable___private__1___boxed(lean_object* v_a_877_){
_start:
{
uint64_t v_res_878_; lean_object* v_r_879_; 
v_res_878_ = l_Lean_Json_instHashable___private__1(v_a_877_);
lean_dec(v_a_877_);
v_r_879_ = lean_box_uint64(v_res_878_);
return v_r_879_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(lean_object* v_k_882_, lean_object* v_v_883_, lean_object* v_t_884_){
_start:
{
if (lean_obj_tag(v_t_884_) == 0)
{
lean_object* v_size_885_; lean_object* v_k_886_; lean_object* v_v_887_; lean_object* v_l_888_; lean_object* v_r_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_1169_; 
v_size_885_ = lean_ctor_get(v_t_884_, 0);
v_k_886_ = lean_ctor_get(v_t_884_, 1);
v_v_887_ = lean_ctor_get(v_t_884_, 2);
v_l_888_ = lean_ctor_get(v_t_884_, 3);
v_r_889_ = lean_ctor_get(v_t_884_, 4);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_t_884_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_891_ = v_t_884_;
v_isShared_892_ = v_isSharedCheck_1169_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_r_889_);
lean_inc(v_l_888_);
lean_inc(v_v_887_);
lean_inc(v_k_886_);
lean_inc(v_size_885_);
lean_dec(v_t_884_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_1169_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
uint8_t v___x_893_; 
v___x_893_ = lean_string_compare(v_k_882_, v_k_886_);
switch(v___x_893_)
{
case 0:
{
lean_object* v_impl_894_; lean_object* v___x_895_; 
lean_dec(v_size_885_);
v_impl_894_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_882_, v_v_883_, v_l_888_);
v___x_895_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_889_) == 0)
{
lean_object* v_size_896_; lean_object* v_size_897_; lean_object* v_k_898_; lean_object* v_v_899_; lean_object* v_l_900_; lean_object* v_r_901_; lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v_size_896_ = lean_ctor_get(v_r_889_, 0);
v_size_897_ = lean_ctor_get(v_impl_894_, 0);
lean_inc(v_size_897_);
v_k_898_ = lean_ctor_get(v_impl_894_, 1);
lean_inc(v_k_898_);
v_v_899_ = lean_ctor_get(v_impl_894_, 2);
lean_inc(v_v_899_);
v_l_900_ = lean_ctor_get(v_impl_894_, 3);
lean_inc(v_l_900_);
v_r_901_ = lean_ctor_get(v_impl_894_, 4);
lean_inc(v_r_901_);
v___x_902_ = lean_unsigned_to_nat(3u);
v___x_903_ = lean_nat_mul(v___x_902_, v_size_896_);
v___x_904_ = lean_nat_dec_lt(v___x_903_, v_size_897_);
lean_dec(v___x_903_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_908_; 
lean_dec(v_r_901_);
lean_dec(v_l_900_);
lean_dec(v_v_899_);
lean_dec(v_k_898_);
v___x_905_ = lean_nat_add(v___x_895_, v_size_897_);
lean_dec(v_size_897_);
v___x_906_ = lean_nat_add(v___x_905_, v_size_896_);
lean_dec(v___x_905_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 3, v_impl_894_);
lean_ctor_set(v___x_891_, 0, v___x_906_);
v___x_908_ = v___x_891_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_k_886_);
lean_ctor_set(v_reuseFailAlloc_909_, 2, v_v_887_);
lean_ctor_set(v_reuseFailAlloc_909_, 3, v_impl_894_);
lean_ctor_set(v_reuseFailAlloc_909_, 4, v_r_889_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
else
{
lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_975_; 
v_isSharedCheck_975_ = !lean_is_exclusive(v_impl_894_);
if (v_isSharedCheck_975_ == 0)
{
lean_object* v_unused_976_; lean_object* v_unused_977_; lean_object* v_unused_978_; lean_object* v_unused_979_; lean_object* v_unused_980_; 
v_unused_976_ = lean_ctor_get(v_impl_894_, 4);
lean_dec(v_unused_976_);
v_unused_977_ = lean_ctor_get(v_impl_894_, 3);
lean_dec(v_unused_977_);
v_unused_978_ = lean_ctor_get(v_impl_894_, 2);
lean_dec(v_unused_978_);
v_unused_979_ = lean_ctor_get(v_impl_894_, 1);
lean_dec(v_unused_979_);
v_unused_980_ = lean_ctor_get(v_impl_894_, 0);
lean_dec(v_unused_980_);
v___x_911_ = v_impl_894_;
v_isShared_912_ = v_isSharedCheck_975_;
goto v_resetjp_910_;
}
else
{
lean_dec(v_impl_894_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_975_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v_size_913_; lean_object* v_size_914_; lean_object* v_k_915_; lean_object* v_v_916_; lean_object* v_l_917_; lean_object* v_r_918_; lean_object* v___x_919_; lean_object* v___x_920_; uint8_t v___x_921_; 
v_size_913_ = lean_ctor_get(v_l_900_, 0);
v_size_914_ = lean_ctor_get(v_r_901_, 0);
v_k_915_ = lean_ctor_get(v_r_901_, 1);
v_v_916_ = lean_ctor_get(v_r_901_, 2);
v_l_917_ = lean_ctor_get(v_r_901_, 3);
v_r_918_ = lean_ctor_get(v_r_901_, 4);
v___x_919_ = lean_unsigned_to_nat(2u);
v___x_920_ = lean_nat_mul(v___x_919_, v_size_913_);
v___x_921_ = lean_nat_dec_lt(v_size_914_, v___x_920_);
lean_dec(v___x_920_);
if (v___x_921_ == 0)
{
lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_950_; 
lean_inc(v_r_918_);
lean_inc(v_l_917_);
lean_inc(v_v_916_);
lean_inc(v_k_915_);
v_isSharedCheck_950_ = !lean_is_exclusive(v_r_901_);
if (v_isSharedCheck_950_ == 0)
{
lean_object* v_unused_951_; lean_object* v_unused_952_; lean_object* v_unused_953_; lean_object* v_unused_954_; lean_object* v_unused_955_; 
v_unused_951_ = lean_ctor_get(v_r_901_, 4);
lean_dec(v_unused_951_);
v_unused_952_ = lean_ctor_get(v_r_901_, 3);
lean_dec(v_unused_952_);
v_unused_953_ = lean_ctor_get(v_r_901_, 2);
lean_dec(v_unused_953_);
v_unused_954_ = lean_ctor_get(v_r_901_, 1);
lean_dec(v_unused_954_);
v_unused_955_ = lean_ctor_get(v_r_901_, 0);
lean_dec(v_unused_955_);
v___x_923_ = v_r_901_;
v_isShared_924_ = v_isSharedCheck_950_;
goto v_resetjp_922_;
}
else
{
lean_dec(v_r_901_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_950_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___x_938_; lean_object* v___y_940_; 
v___x_925_ = lean_nat_add(v___x_895_, v_size_897_);
lean_dec(v_size_897_);
v___x_926_ = lean_nat_add(v___x_925_, v_size_896_);
lean_dec(v___x_925_);
v___x_938_ = lean_nat_add(v___x_895_, v_size_913_);
if (lean_obj_tag(v_l_917_) == 0)
{
lean_object* v_size_948_; 
v_size_948_ = lean_ctor_get(v_l_917_, 0);
lean_inc(v_size_948_);
v___y_940_ = v_size_948_;
goto v___jp_939_;
}
else
{
lean_object* v___x_949_; 
v___x_949_ = lean_unsigned_to_nat(0u);
v___y_940_ = v___x_949_;
goto v___jp_939_;
}
v___jp_927_:
{
lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_931_ = lean_nat_add(v___y_929_, v___y_930_);
lean_dec(v___y_930_);
lean_dec(v___y_929_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 4, v_r_889_);
lean_ctor_set(v___x_923_, 3, v_r_918_);
lean_ctor_set(v___x_923_, 2, v_v_887_);
lean_ctor_set(v___x_923_, 1, v_k_886_);
lean_ctor_set(v___x_923_, 0, v___x_931_);
v___x_933_ = v___x_923_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_931_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v_k_886_);
lean_ctor_set(v_reuseFailAlloc_937_, 2, v_v_887_);
lean_ctor_set(v_reuseFailAlloc_937_, 3, v_r_918_);
lean_ctor_set(v_reuseFailAlloc_937_, 4, v_r_889_);
v___x_933_ = v_reuseFailAlloc_937_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
lean_object* v___x_935_; 
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 4, v___x_933_);
lean_ctor_set(v___x_911_, 3, v___y_928_);
lean_ctor_set(v___x_911_, 2, v_v_916_);
lean_ctor_set(v___x_911_, 1, v_k_915_);
lean_ctor_set(v___x_911_, 0, v___x_926_);
v___x_935_ = v___x_911_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_926_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v_k_915_);
lean_ctor_set(v_reuseFailAlloc_936_, 2, v_v_916_);
lean_ctor_set(v_reuseFailAlloc_936_, 3, v___y_928_);
lean_ctor_set(v_reuseFailAlloc_936_, 4, v___x_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
v___jp_939_:
{
lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_941_ = lean_nat_add(v___x_938_, v___y_940_);
lean_dec(v___y_940_);
lean_dec(v___x_938_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 4, v_l_917_);
lean_ctor_set(v___x_891_, 3, v_l_900_);
lean_ctor_set(v___x_891_, 2, v_v_899_);
lean_ctor_set(v___x_891_, 1, v_k_898_);
lean_ctor_set(v___x_891_, 0, v___x_941_);
v___x_943_ = v___x_891_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_k_898_);
lean_ctor_set(v_reuseFailAlloc_947_, 2, v_v_899_);
lean_ctor_set(v_reuseFailAlloc_947_, 3, v_l_900_);
lean_ctor_set(v_reuseFailAlloc_947_, 4, v_l_917_);
v___x_943_ = v_reuseFailAlloc_947_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_944_; 
v___x_944_ = lean_nat_add(v___x_895_, v_size_896_);
if (lean_obj_tag(v_r_918_) == 0)
{
lean_object* v_size_945_; 
v_size_945_ = lean_ctor_get(v_r_918_, 0);
lean_inc(v_size_945_);
v___y_928_ = v___x_943_;
v___y_929_ = v___x_944_;
v___y_930_ = v_size_945_;
goto v___jp_927_;
}
else
{
lean_object* v___x_946_; 
v___x_946_ = lean_unsigned_to_nat(0u);
v___y_928_ = v___x_943_;
v___y_929_ = v___x_944_;
v___y_930_ = v___x_946_;
goto v___jp_927_;
}
}
}
}
}
else
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_961_; 
lean_del_object(v___x_891_);
v___x_956_ = lean_nat_add(v___x_895_, v_size_897_);
lean_dec(v_size_897_);
v___x_957_ = lean_nat_add(v___x_956_, v_size_896_);
lean_dec(v___x_956_);
v___x_958_ = lean_nat_add(v___x_895_, v_size_896_);
v___x_959_ = lean_nat_add(v___x_958_, v_size_914_);
lean_dec(v___x_958_);
lean_inc_ref(v_r_889_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 4, v_r_889_);
lean_ctor_set(v___x_911_, 3, v_r_901_);
lean_ctor_set(v___x_911_, 2, v_v_887_);
lean_ctor_set(v___x_911_, 1, v_k_886_);
lean_ctor_set(v___x_911_, 0, v___x_959_);
v___x_961_ = v___x_911_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_959_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_k_886_);
lean_ctor_set(v_reuseFailAlloc_974_, 2, v_v_887_);
lean_ctor_set(v_reuseFailAlloc_974_, 3, v_r_901_);
lean_ctor_set(v_reuseFailAlloc_974_, 4, v_r_889_);
v___x_961_ = v_reuseFailAlloc_974_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
v_isSharedCheck_968_ = !lean_is_exclusive(v_r_889_);
if (v_isSharedCheck_968_ == 0)
{
lean_object* v_unused_969_; lean_object* v_unused_970_; lean_object* v_unused_971_; lean_object* v_unused_972_; lean_object* v_unused_973_; 
v_unused_969_ = lean_ctor_get(v_r_889_, 4);
lean_dec(v_unused_969_);
v_unused_970_ = lean_ctor_get(v_r_889_, 3);
lean_dec(v_unused_970_);
v_unused_971_ = lean_ctor_get(v_r_889_, 2);
lean_dec(v_unused_971_);
v_unused_972_ = lean_ctor_get(v_r_889_, 1);
lean_dec(v_unused_972_);
v_unused_973_ = lean_ctor_get(v_r_889_, 0);
lean_dec(v_unused_973_);
v___x_963_ = v_r_889_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_dec(v_r_889_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 4, v___x_961_);
lean_ctor_set(v___x_963_, 3, v_l_900_);
lean_ctor_set(v___x_963_, 2, v_v_899_);
lean_ctor_set(v___x_963_, 1, v_k_898_);
lean_ctor_set(v___x_963_, 0, v___x_957_);
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_957_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_k_898_);
lean_ctor_set(v_reuseFailAlloc_967_, 2, v_v_899_);
lean_ctor_set(v_reuseFailAlloc_967_, 3, v_l_900_);
lean_ctor_set(v_reuseFailAlloc_967_, 4, v___x_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_981_; 
v_l_981_ = lean_ctor_get(v_impl_894_, 3);
lean_inc(v_l_981_);
if (lean_obj_tag(v_l_981_) == 0)
{
lean_object* v_r_982_; lean_object* v_k_983_; lean_object* v_v_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_995_; 
v_r_982_ = lean_ctor_get(v_impl_894_, 4);
v_k_983_ = lean_ctor_get(v_impl_894_, 1);
v_v_984_ = lean_ctor_get(v_impl_894_, 2);
v_isSharedCheck_995_ = !lean_is_exclusive(v_impl_894_);
if (v_isSharedCheck_995_ == 0)
{
lean_object* v_unused_996_; lean_object* v_unused_997_; 
v_unused_996_ = lean_ctor_get(v_impl_894_, 3);
lean_dec(v_unused_996_);
v_unused_997_ = lean_ctor_get(v_impl_894_, 0);
lean_dec(v_unused_997_);
v___x_986_ = v_impl_894_;
v_isShared_987_ = v_isSharedCheck_995_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_r_982_);
lean_inc(v_v_984_);
lean_inc(v_k_983_);
lean_dec(v_impl_894_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_995_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_988_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_982_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 3, v_r_982_);
lean_ctor_set(v___x_986_, 2, v_v_887_);
lean_ctor_set(v___x_986_, 1, v_k_886_);
lean_ctor_set(v___x_986_, 0, v___x_895_);
v___x_990_ = v___x_986_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_895_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_k_886_);
lean_ctor_set(v_reuseFailAlloc_994_, 2, v_v_887_);
lean_ctor_set(v_reuseFailAlloc_994_, 3, v_r_982_);
lean_ctor_set(v_reuseFailAlloc_994_, 4, v_r_982_);
v___x_990_ = v_reuseFailAlloc_994_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v___x_992_; 
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 4, v___x_990_);
lean_ctor_set(v___x_891_, 3, v_l_981_);
lean_ctor_set(v___x_891_, 2, v_v_984_);
lean_ctor_set(v___x_891_, 1, v_k_983_);
lean_ctor_set(v___x_891_, 0, v___x_988_);
v___x_992_ = v___x_891_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_k_983_);
lean_ctor_set(v_reuseFailAlloc_993_, 2, v_v_984_);
lean_ctor_set(v_reuseFailAlloc_993_, 3, v_l_981_);
lean_ctor_set(v_reuseFailAlloc_993_, 4, v___x_990_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
else
{
lean_object* v_r_998_; 
v_r_998_ = lean_ctor_get(v_impl_894_, 4);
lean_inc(v_r_998_);
if (lean_obj_tag(v_r_998_) == 0)
{
lean_object* v_k_999_; lean_object* v_v_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1023_; 
v_k_999_ = lean_ctor_get(v_impl_894_, 1);
v_v_1000_ = lean_ctor_get(v_impl_894_, 2);
v_isSharedCheck_1023_ = !lean_is_exclusive(v_impl_894_);
if (v_isSharedCheck_1023_ == 0)
{
lean_object* v_unused_1024_; lean_object* v_unused_1025_; lean_object* v_unused_1026_; 
v_unused_1024_ = lean_ctor_get(v_impl_894_, 4);
lean_dec(v_unused_1024_);
v_unused_1025_ = lean_ctor_get(v_impl_894_, 3);
lean_dec(v_unused_1025_);
v_unused_1026_ = lean_ctor_get(v_impl_894_, 0);
lean_dec(v_unused_1026_);
v___x_1002_ = v_impl_894_;
v_isShared_1003_ = v_isSharedCheck_1023_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_v_1000_);
lean_inc(v_k_999_);
lean_dec(v_impl_894_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1023_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v_k_1004_; lean_object* v_v_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1019_; 
v_k_1004_ = lean_ctor_get(v_r_998_, 1);
v_v_1005_ = lean_ctor_get(v_r_998_, 2);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_r_998_);
if (v_isSharedCheck_1019_ == 0)
{
lean_object* v_unused_1020_; lean_object* v_unused_1021_; lean_object* v_unused_1022_; 
v_unused_1020_ = lean_ctor_get(v_r_998_, 4);
lean_dec(v_unused_1020_);
v_unused_1021_ = lean_ctor_get(v_r_998_, 3);
lean_dec(v_unused_1021_);
v_unused_1022_ = lean_ctor_get(v_r_998_, 0);
lean_dec(v_unused_1022_);
v___x_1007_ = v_r_998_;
v_isShared_1008_ = v_isSharedCheck_1019_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_v_1005_);
lean_inc(v_k_1004_);
lean_dec(v_r_998_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1019_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1009_; lean_object* v___x_1011_; 
v___x_1009_ = lean_unsigned_to_nat(3u);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 4, v_l_981_);
lean_ctor_set(v___x_1007_, 3, v_l_981_);
lean_ctor_set(v___x_1007_, 2, v_v_1000_);
lean_ctor_set(v___x_1007_, 1, v_k_999_);
lean_ctor_set(v___x_1007_, 0, v___x_895_);
v___x_1011_ = v___x_1007_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_895_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_k_999_);
lean_ctor_set(v_reuseFailAlloc_1018_, 2, v_v_1000_);
lean_ctor_set(v_reuseFailAlloc_1018_, 3, v_l_981_);
lean_ctor_set(v_reuseFailAlloc_1018_, 4, v_l_981_);
v___x_1011_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
lean_object* v___x_1013_; 
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 4, v_l_981_);
lean_ctor_set(v___x_1002_, 2, v_v_887_);
lean_ctor_set(v___x_1002_, 1, v_k_886_);
lean_ctor_set(v___x_1002_, 0, v___x_895_);
v___x_1013_ = v___x_1002_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_895_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_k_886_);
lean_ctor_set(v_reuseFailAlloc_1017_, 2, v_v_887_);
lean_ctor_set(v_reuseFailAlloc_1017_, 3, v_l_981_);
lean_ctor_set(v_reuseFailAlloc_1017_, 4, v_l_981_);
v___x_1013_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v___x_1015_; 
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 4, v___x_1013_);
lean_ctor_set(v___x_891_, 3, v___x_1011_);
lean_ctor_set(v___x_891_, 2, v_v_1005_);
lean_ctor_set(v___x_891_, 1, v_k_1004_);
lean_ctor_set(v___x_891_, 0, v___x_1009_);
v___x_1015_ = v___x_891_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1009_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_k_1004_);
lean_ctor_set(v_reuseFailAlloc_1016_, 2, v_v_1005_);
lean_ctor_set(v_reuseFailAlloc_1016_, 3, v___x_1011_);
lean_ctor_set(v_reuseFailAlloc_1016_, 4, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
}
}
else
{
lean_object* v___x_1027_; lean_object* v___x_1029_; 
v___x_1027_ = lean_unsigned_to_nat(2u);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 4, v_r_998_);
lean_ctor_set(v___x_891_, 3, v_impl_894_);
lean_ctor_set(v___x_891_, 0, v___x_1027_);
v___x_1029_ = v___x_891_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1027_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_k_886_);
lean_ctor_set(v_reuseFailAlloc_1030_, 2, v_v_887_);
lean_ctor_set(v_reuseFailAlloc_1030_, 3, v_impl_894_);
lean_ctor_set(v_reuseFailAlloc_1030_, 4, v_r_998_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1032_; 
lean_dec(v_v_887_);
lean_dec(v_k_886_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 2, v_v_883_);
lean_ctor_set(v___x_891_, 1, v_k_882_);
v___x_1032_ = v___x_891_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_size_885_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_k_882_);
lean_ctor_set(v_reuseFailAlloc_1033_, 2, v_v_883_);
lean_ctor_set(v_reuseFailAlloc_1033_, 3, v_l_888_);
lean_ctor_set(v_reuseFailAlloc_1033_, 4, v_r_889_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
default: 
{
lean_object* v_impl_1034_; lean_object* v___x_1035_; 
lean_dec(v_size_885_);
v_impl_1034_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_882_, v_v_883_, v_r_889_);
v___x_1035_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_888_) == 0)
{
lean_object* v_size_1036_; lean_object* v_size_1037_; lean_object* v_k_1038_; lean_object* v_v_1039_; lean_object* v_l_1040_; lean_object* v_r_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; 
v_size_1036_ = lean_ctor_get(v_l_888_, 0);
v_size_1037_ = lean_ctor_get(v_impl_1034_, 0);
lean_inc(v_size_1037_);
v_k_1038_ = lean_ctor_get(v_impl_1034_, 1);
lean_inc(v_k_1038_);
v_v_1039_ = lean_ctor_get(v_impl_1034_, 2);
lean_inc(v_v_1039_);
v_l_1040_ = lean_ctor_get(v_impl_1034_, 3);
lean_inc(v_l_1040_);
v_r_1041_ = lean_ctor_get(v_impl_1034_, 4);
lean_inc(v_r_1041_);
v___x_1042_ = lean_unsigned_to_nat(3u);
v___x_1043_ = lean_nat_mul(v___x_1042_, v_size_1036_);
v___x_1044_ = lean_nat_dec_lt(v___x_1043_, v_size_1037_);
lean_dec(v___x_1043_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1048_; 
lean_dec(v_r_1041_);
lean_dec(v_l_1040_);
lean_dec(v_v_1039_);
lean_dec(v_k_1038_);
v___x_1045_ = lean_nat_add(v___x_1035_, v_size_1036_);
v___x_1046_ = lean_nat_add(v___x_1045_, v_size_1037_);
lean_dec(v_size_1037_);
lean_dec(v___x_1045_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 4, v_impl_1034_);
lean_ctor_set(v___x_891_, 0, v___x_1046_);
v___x_1048_ = v___x_891_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_k_886_);
lean_ctor_set(v_reuseFailAlloc_1049_, 2, v_v_887_);
lean_ctor_set(v_reuseFailAlloc_1049_, 3, v_l_888_);
lean_ctor_set(v_reuseFailAlloc_1049_, 4, v_impl_1034_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
else
{
lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1113_; 
v_isSharedCheck_1113_ = !lean_is_exclusive(v_impl_1034_);
if (v_isSharedCheck_1113_ == 0)
{
lean_object* v_unused_1114_; lean_object* v_unused_1115_; lean_object* v_unused_1116_; lean_object* v_unused_1117_; lean_object* v_unused_1118_; 
v_unused_1114_ = lean_ctor_get(v_impl_1034_, 4);
lean_dec(v_unused_1114_);
v_unused_1115_ = lean_ctor_get(v_impl_1034_, 3);
lean_dec(v_unused_1115_);
v_unused_1116_ = lean_ctor_get(v_impl_1034_, 2);
lean_dec(v_unused_1116_);
v_unused_1117_ = lean_ctor_get(v_impl_1034_, 1);
lean_dec(v_unused_1117_);
v_unused_1118_ = lean_ctor_get(v_impl_1034_, 0);
lean_dec(v_unused_1118_);
v___x_1051_ = v_impl_1034_;
v_isShared_1052_ = v_isSharedCheck_1113_;
goto v_resetjp_1050_;
}
else
{
lean_dec(v_impl_1034_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1113_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v_size_1053_; lean_object* v_k_1054_; lean_object* v_v_1055_; lean_object* v_l_1056_; lean_object* v_r_1057_; lean_object* v_size_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v_size_1053_ = lean_ctor_get(v_l_1040_, 0);
v_k_1054_ = lean_ctor_get(v_l_1040_, 1);
v_v_1055_ = lean_ctor_get(v_l_1040_, 2);
v_l_1056_ = lean_ctor_get(v_l_1040_, 3);
v_r_1057_ = lean_ctor_get(v_l_1040_, 4);
v_size_1058_ = lean_ctor_get(v_r_1041_, 0);
v___x_1059_ = lean_unsigned_to_nat(2u);
v___x_1060_ = lean_nat_mul(v___x_1059_, v_size_1058_);
v___x_1061_ = lean_nat_dec_lt(v_size_1053_, v___x_1060_);
lean_dec(v___x_1060_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1089_; 
lean_inc(v_r_1057_);
lean_inc(v_l_1056_);
lean_inc(v_v_1055_);
lean_inc(v_k_1054_);
v_isSharedCheck_1089_ = !lean_is_exclusive(v_l_1040_);
if (v_isSharedCheck_1089_ == 0)
{
lean_object* v_unused_1090_; lean_object* v_unused_1091_; lean_object* v_unused_1092_; lean_object* v_unused_1093_; lean_object* v_unused_1094_; 
v_unused_1090_ = lean_ctor_get(v_l_1040_, 4);
lean_dec(v_unused_1090_);
v_unused_1091_ = lean_ctor_get(v_l_1040_, 3);
lean_dec(v_unused_1091_);
v_unused_1092_ = lean_ctor_get(v_l_1040_, 2);
lean_dec(v_unused_1092_);
v_unused_1093_ = lean_ctor_get(v_l_1040_, 1);
lean_dec(v_unused_1093_);
v_unused_1094_ = lean_ctor_get(v_l_1040_, 0);
lean_dec(v_unused_1094_);
v___x_1063_ = v_l_1040_;
v_isShared_1064_ = v_isSharedCheck_1089_;
goto v_resetjp_1062_;
}
else
{
lean_dec(v_l_1040_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1089_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1079_; 
v___x_1065_ = lean_nat_add(v___x_1035_, v_size_1036_);
v___x_1066_ = lean_nat_add(v___x_1065_, v_size_1037_);
lean_dec(v_size_1037_);
if (lean_obj_tag(v_l_1056_) == 0)
{
lean_object* v_size_1087_; 
v_size_1087_ = lean_ctor_get(v_l_1056_, 0);
lean_inc(v_size_1087_);
v___y_1079_ = v_size_1087_;
goto v___jp_1078_;
}
else
{
lean_object* v___x_1088_; 
v___x_1088_ = lean_unsigned_to_nat(0u);
v___y_1079_ = v___x_1088_;
goto v___jp_1078_;
}
v___jp_1067_:
{
lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1071_ = lean_nat_add(v___y_1068_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec(v___y_1068_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 4, v_r_1041_);
lean_ctor_set(v___x_1063_, 3, v_r_1057_);
lean_ctor_set(v___x_1063_, 2, v_v_1039_);
lean_ctor_set(v___x_1063_, 1, v_k_1038_);
lean_ctor_set(v___x_1063_, 0, v___x_1071_);
v___x_1073_ = v___x_1063_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1071_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v_k_1038_);
lean_ctor_set(v_reuseFailAlloc_1077_, 2, v_v_1039_);
lean_ctor_set(v_reuseFailAlloc_1077_, 3, v_r_1057_);
lean_ctor_set(v_reuseFailAlloc_1077_, 4, v_r_1041_);
v___x_1073_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1075_; 
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 4, v___x_1073_);
lean_ctor_set(v___x_1051_, 3, v___y_1069_);
lean_ctor_set(v___x_1051_, 2, v_v_1055_);
lean_ctor_set(v___x_1051_, 1, v_k_1054_);
lean_ctor_set(v___x_1051_, 0, v___x_1066_);
v___x_1075_ = v___x_1051_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v_k_1054_);
lean_ctor_set(v_reuseFailAlloc_1076_, 2, v_v_1055_);
lean_ctor_set(v_reuseFailAlloc_1076_, 3, v___y_1069_);
lean_ctor_set(v_reuseFailAlloc_1076_, 4, v___x_1073_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
v___jp_1078_:
{
lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1080_ = lean_nat_add(v___x_1065_, v___y_1079_);
lean_dec(v___y_1079_);
lean_dec(v___x_1065_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 4, v_l_1056_);
lean_ctor_set(v___x_891_, 0, v___x_1080_);
v___x_1082_ = v___x_891_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v_k_886_);
lean_ctor_set(v_reuseFailAlloc_1086_, 2, v_v_887_);
lean_ctor_set(v_reuseFailAlloc_1086_, 3, v_l_888_);
lean_ctor_set(v_reuseFailAlloc_1086_, 4, v_l_1056_);
v___x_1082_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
lean_object* v___x_1083_; 
v___x_1083_ = lean_nat_add(v___x_1035_, v_size_1058_);
if (lean_obj_tag(v_r_1057_) == 0)
{
lean_object* v_size_1084_; 
v_size_1084_ = lean_ctor_get(v_r_1057_, 0);
lean_inc(v_size_1084_);
v___y_1068_ = v___x_1083_;
v___y_1069_ = v___x_1082_;
v___y_1070_ = v_size_1084_;
goto v___jp_1067_;
}
else
{
lean_object* v___x_1085_; 
v___x_1085_ = lean_unsigned_to_nat(0u);
v___y_1068_ = v___x_1083_;
v___y_1069_ = v___x_1082_;
v___y_1070_ = v___x_1085_;
goto v___jp_1067_;
}
}
}
}
}
else
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1099_; 
lean_del_object(v___x_891_);
v___x_1095_ = lean_nat_add(v___x_1035_, v_size_1036_);
v___x_1096_ = lean_nat_add(v___x_1095_, v_size_1037_);
lean_dec(v_size_1037_);
v___x_1097_ = lean_nat_add(v___x_1095_, v_size_1053_);
lean_dec(v___x_1095_);
lean_inc_ref(v_l_888_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 4, v_l_1040_);
lean_ctor_set(v___x_1051_, 3, v_l_888_);
lean_ctor_set(v___x_1051_, 2, v_v_887_);
lean_ctor_set(v___x_1051_, 1, v_k_886_);
lean_ctor_set(v___x_1051_, 0, v___x_1097_);
v___x_1099_ = v___x_1051_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1097_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_k_886_);
lean_ctor_set(v_reuseFailAlloc_1112_, 2, v_v_887_);
lean_ctor_set(v_reuseFailAlloc_1112_, 3, v_l_888_);
lean_ctor_set(v_reuseFailAlloc_1112_, 4, v_l_1040_);
v___x_1099_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
v_isSharedCheck_1106_ = !lean_is_exclusive(v_l_888_);
if (v_isSharedCheck_1106_ == 0)
{
lean_object* v_unused_1107_; lean_object* v_unused_1108_; lean_object* v_unused_1109_; lean_object* v_unused_1110_; lean_object* v_unused_1111_; 
v_unused_1107_ = lean_ctor_get(v_l_888_, 4);
lean_dec(v_unused_1107_);
v_unused_1108_ = lean_ctor_get(v_l_888_, 3);
lean_dec(v_unused_1108_);
v_unused_1109_ = lean_ctor_get(v_l_888_, 2);
lean_dec(v_unused_1109_);
v_unused_1110_ = lean_ctor_get(v_l_888_, 1);
lean_dec(v_unused_1110_);
v_unused_1111_ = lean_ctor_get(v_l_888_, 0);
lean_dec(v_unused_1111_);
v___x_1101_ = v_l_888_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_dec(v_l_888_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 4, v_r_1041_);
lean_ctor_set(v___x_1101_, 3, v___x_1099_);
lean_ctor_set(v___x_1101_, 2, v_v_1039_);
lean_ctor_set(v___x_1101_, 1, v_k_1038_);
lean_ctor_set(v___x_1101_, 0, v___x_1096_);
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_k_1038_);
lean_ctor_set(v_reuseFailAlloc_1105_, 2, v_v_1039_);
lean_ctor_set(v_reuseFailAlloc_1105_, 3, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1105_, 4, v_r_1041_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1119_; 
v_l_1119_ = lean_ctor_get(v_impl_1034_, 3);
lean_inc(v_l_1119_);
if (lean_obj_tag(v_l_1119_) == 0)
{
lean_object* v_r_1120_; lean_object* v_k_1121_; lean_object* v_v_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1145_; 
v_r_1120_ = lean_ctor_get(v_impl_1034_, 4);
v_k_1121_ = lean_ctor_get(v_impl_1034_, 1);
v_v_1122_ = lean_ctor_get(v_impl_1034_, 2);
v_isSharedCheck_1145_ = !lean_is_exclusive(v_impl_1034_);
if (v_isSharedCheck_1145_ == 0)
{
lean_object* v_unused_1146_; lean_object* v_unused_1147_; 
v_unused_1146_ = lean_ctor_get(v_impl_1034_, 3);
lean_dec(v_unused_1146_);
v_unused_1147_ = lean_ctor_get(v_impl_1034_, 0);
lean_dec(v_unused_1147_);
v___x_1124_ = v_impl_1034_;
v_isShared_1125_ = v_isSharedCheck_1145_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_r_1120_);
lean_inc(v_v_1122_);
lean_inc(v_k_1121_);
lean_dec(v_impl_1034_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1145_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v_k_1126_; lean_object* v_v_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1141_; 
v_k_1126_ = lean_ctor_get(v_l_1119_, 1);
v_v_1127_ = lean_ctor_get(v_l_1119_, 2);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_l_1119_);
if (v_isSharedCheck_1141_ == 0)
{
lean_object* v_unused_1142_; lean_object* v_unused_1143_; lean_object* v_unused_1144_; 
v_unused_1142_ = lean_ctor_get(v_l_1119_, 4);
lean_dec(v_unused_1142_);
v_unused_1143_ = lean_ctor_get(v_l_1119_, 3);
lean_dec(v_unused_1143_);
v_unused_1144_ = lean_ctor_get(v_l_1119_, 0);
lean_dec(v_unused_1144_);
v___x_1129_ = v_l_1119_;
v_isShared_1130_ = v_isSharedCheck_1141_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_v_1127_);
lean_inc(v_k_1126_);
lean_dec(v_l_1119_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1141_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1131_; lean_object* v___x_1133_; 
v___x_1131_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1120_, 2);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 4, v_r_1120_);
lean_ctor_set(v___x_1129_, 3, v_r_1120_);
lean_ctor_set(v___x_1129_, 2, v_v_887_);
lean_ctor_set(v___x_1129_, 1, v_k_886_);
lean_ctor_set(v___x_1129_, 0, v___x_1035_);
v___x_1133_ = v___x_1129_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_k_886_);
lean_ctor_set(v_reuseFailAlloc_1140_, 2, v_v_887_);
lean_ctor_set(v_reuseFailAlloc_1140_, 3, v_r_1120_);
lean_ctor_set(v_reuseFailAlloc_1140_, 4, v_r_1120_);
v___x_1133_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1135_; 
lean_inc(v_r_1120_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 3, v_r_1120_);
lean_ctor_set(v___x_1124_, 0, v___x_1035_);
v___x_1135_ = v___x_1124_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_k_1121_);
lean_ctor_set(v_reuseFailAlloc_1139_, 2, v_v_1122_);
lean_ctor_set(v_reuseFailAlloc_1139_, 3, v_r_1120_);
lean_ctor_set(v_reuseFailAlloc_1139_, 4, v_r_1120_);
v___x_1135_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1137_; 
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 4, v___x_1135_);
lean_ctor_set(v___x_891_, 3, v___x_1133_);
lean_ctor_set(v___x_891_, 2, v_v_1127_);
lean_ctor_set(v___x_891_, 1, v_k_1126_);
lean_ctor_set(v___x_891_, 0, v___x_1131_);
v___x_1137_ = v___x_891_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_k_1126_);
lean_ctor_set(v_reuseFailAlloc_1138_, 2, v_v_1127_);
lean_ctor_set(v_reuseFailAlloc_1138_, 3, v___x_1133_);
lean_ctor_set(v_reuseFailAlloc_1138_, 4, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
}
}
else
{
lean_object* v_r_1148_; 
v_r_1148_ = lean_ctor_get(v_impl_1034_, 4);
lean_inc(v_r_1148_);
if (lean_obj_tag(v_r_1148_) == 0)
{
lean_object* v_k_1149_; lean_object* v_v_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1161_; 
v_k_1149_ = lean_ctor_get(v_impl_1034_, 1);
v_v_1150_ = lean_ctor_get(v_impl_1034_, 2);
v_isSharedCheck_1161_ = !lean_is_exclusive(v_impl_1034_);
if (v_isSharedCheck_1161_ == 0)
{
lean_object* v_unused_1162_; lean_object* v_unused_1163_; lean_object* v_unused_1164_; 
v_unused_1162_ = lean_ctor_get(v_impl_1034_, 4);
lean_dec(v_unused_1162_);
v_unused_1163_ = lean_ctor_get(v_impl_1034_, 3);
lean_dec(v_unused_1163_);
v_unused_1164_ = lean_ctor_get(v_impl_1034_, 0);
lean_dec(v_unused_1164_);
v___x_1152_ = v_impl_1034_;
v_isShared_1153_ = v_isSharedCheck_1161_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_v_1150_);
lean_inc(v_k_1149_);
lean_dec(v_impl_1034_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1161_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1154_ = lean_unsigned_to_nat(3u);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 4, v_l_1119_);
lean_ctor_set(v___x_1152_, 2, v_v_887_);
lean_ctor_set(v___x_1152_, 1, v_k_886_);
lean_ctor_set(v___x_1152_, 0, v___x_1035_);
v___x_1156_ = v___x_1152_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v_k_886_);
lean_ctor_set(v_reuseFailAlloc_1160_, 2, v_v_887_);
lean_ctor_set(v_reuseFailAlloc_1160_, 3, v_l_1119_);
lean_ctor_set(v_reuseFailAlloc_1160_, 4, v_l_1119_);
v___x_1156_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1158_; 
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 4, v_r_1148_);
lean_ctor_set(v___x_891_, 3, v___x_1156_);
lean_ctor_set(v___x_891_, 2, v_v_1150_);
lean_ctor_set(v___x_891_, 1, v_k_1149_);
lean_ctor_set(v___x_891_, 0, v___x_1154_);
v___x_1158_ = v___x_891_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1154_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_k_1149_);
lean_ctor_set(v_reuseFailAlloc_1159_, 2, v_v_1150_);
lean_ctor_set(v_reuseFailAlloc_1159_, 3, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1159_, 4, v_r_1148_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
else
{
lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1165_ = lean_unsigned_to_nat(2u);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 4, v_impl_1034_);
lean_ctor_set(v___x_891_, 3, v_r_1148_);
lean_ctor_set(v___x_891_, 0, v___x_1165_);
v___x_1167_ = v___x_891_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1165_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_k_886_);
lean_ctor_set(v_reuseFailAlloc_1168_, 2, v_v_887_);
lean_ctor_set(v_reuseFailAlloc_1168_, 3, v_r_1148_);
lean_ctor_set(v_reuseFailAlloc_1168_, 4, v_impl_1034_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
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
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = lean_unsigned_to_nat(1u);
v___x_1171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
lean_ctor_set(v___x_1171_, 1, v_k_882_);
lean_ctor_set(v___x_1171_, 2, v_v_883_);
lean_ctor_set(v___x_1171_, 3, v_t_884_);
lean_ctor_set(v___x_1171_, 4, v_t_884_);
return v___x_1171_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(lean_object* v_as_x27_1172_, lean_object* v_b_1173_){
_start:
{
if (lean_obj_tag(v_as_x27_1172_) == 0)
{
return v_b_1173_;
}
else
{
lean_object* v_head_1174_; lean_object* v_tail_1175_; lean_object* v_fst_1176_; lean_object* v_snd_1177_; lean_object* v_r_1178_; 
v_head_1174_ = lean_ctor_get(v_as_x27_1172_, 0);
v_tail_1175_ = lean_ctor_get(v_as_x27_1172_, 1);
v_fst_1176_ = lean_ctor_get(v_head_1174_, 0);
v_snd_1177_ = lean_ctor_get(v_head_1174_, 1);
lean_inc(v_snd_1177_);
lean_inc(v_fst_1176_);
v_r_1178_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_fst_1176_, v_snd_1177_, v_b_1173_);
v_as_x27_1172_ = v_tail_1175_;
v_b_1173_ = v_r_1178_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg___boxed(lean_object* v_as_x27_1180_, lean_object* v_b_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_as_x27_1180_, v_b_1181_);
lean_dec(v_as_x27_1180_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mkObj(lean_object* v_o_1183_){
_start:
{
lean_object* v_r_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v_r_1184_ = lean_box(1);
v___x_1185_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_o_1183_, v_r_1184_);
v___x_1186_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mkObj___boxed(lean_object* v_o_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lean_Json_mkObj(v_o_1187_);
lean_dec(v_o_1187_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0(lean_object* v_00_u03b2_1189_, lean_object* v_k_1190_, lean_object* v_v_1191_, lean_object* v_t_1192_, lean_object* v_hl_1193_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_1190_, v_v_1191_, v_t_1192_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1(lean_object* v_as_1195_, lean_object* v_as_x27_1196_, lean_object* v_b_1197_, lean_object* v_a_1198_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_as_x27_1196_, v_b_1197_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___boxed(lean_object* v_as_1200_, lean_object* v_as_x27_1201_, lean_object* v_b_1202_, lean_object* v_a_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1(v_as_1200_, v_as_x27_1201_, v_b_1202_, v_a_1203_);
lean_dec(v_as_x27_1201_);
lean_dec(v_as_1200_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeNat___lam__0(lean_object* v_n_1205_){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = l_Lean_JsonNumber_fromNat(v_n_1205_);
v___x_1207_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeInt___lam__0(lean_object* v_n_1210_){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = l_Lean_JsonNumber_fromInt(v_n_1210_);
v___x_1212_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeString___lam__0(lean_object* v_s_1215_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1216_, 0, v_s_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeBool___lam__0(uint8_t v_b_1219_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1220_, 0, v_b_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeBool___lam__0___boxed(lean_object* v_b_1221_){
_start:
{
uint8_t v_b_boxed_1222_; lean_object* v_res_1223_; 
v_b_boxed_1222_ = lean_unbox(v_b_1221_);
v_res_1223_ = l_Lean_Json_instCoeBool___lam__0(v_b_boxed_1222_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instOfNat(lean_object* v_n_1226_){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = l_Lean_JsonNumber_fromNat(v_n_1226_);
v___x_1228_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT uint8_t l_Lean_Json_isNull(lean_object* v_x_1229_){
_start:
{
if (lean_obj_tag(v_x_1229_) == 0)
{
uint8_t v___x_1230_; 
v___x_1230_ = 1;
return v___x_1230_;
}
else
{
uint8_t v___x_1231_; 
v___x_1231_ = 0;
return v___x_1231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_isNull___boxed(lean_object* v_x_1232_){
_start:
{
uint8_t v_res_1233_; lean_object* v_r_1234_; 
v_res_1233_ = l_Lean_Json_isNull(v_x_1232_);
lean_dec(v_x_1232_);
v_r_1234_ = lean_box(v_res_1233_);
return v_r_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObj_x3f(lean_object* v_x_1238_){
_start:
{
if (lean_obj_tag(v_x_1238_) == 5)
{
lean_object* v_kvPairs_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
v_kvPairs_1239_ = lean_ctor_get(v_x_1238_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_x_1238_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1241_ = v_x_1238_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_kvPairs_1239_);
lean_dec(v_x_1238_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
lean_ctor_set_tag(v___x_1241_, 1);
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_kvPairs_1239_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
else
{
lean_object* v___x_1247_; 
lean_dec(v_x_1238_);
v___x_1247_ = ((lean_object*)(l_Lean_Json_getObj_x3f___closed__1));
return v___x_1247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getArr_x3f(lean_object* v_x_1251_){
_start:
{
if (lean_obj_tag(v_x_1251_) == 4)
{
lean_object* v_elems_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
v_elems_1252_ = lean_ctor_get(v_x_1251_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v_x_1251_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v_x_1251_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_elems_1252_);
lean_dec(v_x_1251_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
lean_ctor_set_tag(v___x_1254_, 1);
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_elems_1252_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
else
{
lean_object* v___x_1260_; 
lean_dec(v_x_1251_);
v___x_1260_ = ((lean_object*)(l_Lean_Json_getArr_x3f___closed__1));
return v___x_1260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getStr_x3f(lean_object* v_x_1264_){
_start:
{
if (lean_obj_tag(v_x_1264_) == 3)
{
lean_object* v_s_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
v_s_1265_ = lean_ctor_get(v_x_1264_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_x_1264_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v_x_1264_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_s_1265_);
lean_dec(v_x_1264_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
lean_ctor_set_tag(v___x_1267_, 1);
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_s_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
else
{
lean_object* v___x_1273_; 
lean_dec(v_x_1264_);
v___x_1273_ = ((lean_object*)(l_Lean_Json_getStr_x3f___closed__1));
return v___x_1273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getNat_x3f(lean_object* v_x_1277_){
_start:
{
if (lean_obj_tag(v_x_1277_) == 2)
{
lean_object* v_n_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1294_; 
v_n_1280_ = lean_ctor_get(v_x_1277_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_x_1277_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1282_ = v_x_1277_;
v_isShared_1283_ = v_isSharedCheck_1294_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_n_1280_);
lean_dec(v_x_1277_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1294_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v_mantissa_1284_; lean_object* v_exponent_1285_; lean_object* v_natZero_1286_; lean_object* v_intZero_1287_; uint8_t v_isNeg_1288_; 
v_mantissa_1284_ = lean_ctor_get(v_n_1280_, 0);
lean_inc(v_mantissa_1284_);
v_exponent_1285_ = lean_ctor_get(v_n_1280_, 1);
lean_inc(v_exponent_1285_);
lean_dec_ref(v_n_1280_);
v_natZero_1286_ = lean_unsigned_to_nat(0u);
v_intZero_1287_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v_isNeg_1288_ = lean_int_dec_lt(v_mantissa_1284_, v_intZero_1287_);
if (v_isNeg_1288_ == 0)
{
uint8_t v___x_1289_; 
v___x_1289_ = lean_nat_dec_eq(v_exponent_1285_, v_natZero_1286_);
lean_dec(v_exponent_1285_);
if (v___x_1289_ == 0)
{
lean_dec(v_mantissa_1284_);
lean_del_object(v___x_1282_);
goto v___jp_1278_;
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; 
v_a_1290_ = lean_nat_abs(v_mantissa_1284_);
lean_dec(v_mantissa_1284_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set_tag(v___x_1282_, 1);
lean_ctor_set(v___x_1282_, 0, v_a_1290_);
v___x_1292_ = v___x_1282_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1290_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
else
{
lean_dec(v_exponent_1285_);
lean_dec(v_mantissa_1284_);
lean_del_object(v___x_1282_);
goto v___jp_1278_;
}
}
}
else
{
lean_dec(v_x_1277_);
goto v___jp_1278_;
}
v___jp_1278_:
{
lean_object* v___x_1279_; 
v___x_1279_ = ((lean_object*)(l_Lean_Json_getNat_x3f___closed__1));
return v___x_1279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getInt_x3f(lean_object* v_x_1298_){
_start:
{
if (lean_obj_tag(v_x_1298_) == 2)
{
lean_object* v_n_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1312_; 
v_n_1301_ = lean_ctor_get(v_x_1298_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_x_1298_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1303_ = v_x_1298_;
v_isShared_1304_ = v_isSharedCheck_1312_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_n_1301_);
lean_dec(v_x_1298_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1312_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v_mantissa_1305_; lean_object* v_exponent_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v_mantissa_1305_ = lean_ctor_get(v_n_1301_, 0);
lean_inc(v_mantissa_1305_);
v_exponent_1306_ = lean_ctor_get(v_n_1301_, 1);
lean_inc(v_exponent_1306_);
lean_dec_ref(v_n_1301_);
v___x_1307_ = lean_unsigned_to_nat(0u);
v___x_1308_ = lean_nat_dec_eq(v_exponent_1306_, v___x_1307_);
lean_dec(v_exponent_1306_);
if (v___x_1308_ == 0)
{
lean_dec(v_mantissa_1305_);
lean_del_object(v___x_1303_);
goto v___jp_1299_;
}
else
{
lean_object* v___x_1310_; 
if (v_isShared_1304_ == 0)
{
lean_ctor_set_tag(v___x_1303_, 1);
lean_ctor_set(v___x_1303_, 0, v_mantissa_1305_);
v___x_1310_ = v___x_1303_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_mantissa_1305_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
else
{
lean_dec(v_x_1298_);
goto v___jp_1299_;
}
v___jp_1299_:
{
lean_object* v___x_1300_; 
v___x_1300_ = ((lean_object*)(l_Lean_Json_getInt_x3f___closed__1));
return v___x_1300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getBool_x3f(lean_object* v_x_1316_){
_start:
{
if (lean_obj_tag(v_x_1316_) == 1)
{
uint8_t v_b_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v_b_1317_ = lean_ctor_get_uint8(v_x_1316_, 0);
v___x_1318_ = lean_box(v_b_1317_);
v___x_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
return v___x_1319_;
}
else
{
lean_object* v___x_1320_; 
v___x_1320_ = ((lean_object*)(l_Lean_Json_getBool_x3f___closed__1));
return v___x_1320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getBool_x3f___boxed(lean_object* v_x_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Lean_Json_getBool_x3f(v_x_1321_);
lean_dec(v_x_1321_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getNum_x3f(lean_object* v_x_1326_){
_start:
{
if (lean_obj_tag(v_x_1326_) == 2)
{
lean_object* v_n_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
v_n_1327_ = lean_ctor_get(v_x_1326_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v_x_1326_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v_x_1326_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_n_1327_);
lean_dec(v_x_1326_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
lean_ctor_set_tag(v___x_1329_, 1);
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_n_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
else
{
lean_object* v___x_1335_; 
lean_dec(v_x_1326_);
v___x_1335_ = ((lean_object*)(l_Lean_Json_getNum_x3f___closed__1));
return v___x_1335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjVal_x3f(lean_object* v_x_1339_, lean_object* v_x_1340_){
_start:
{
if (lean_obj_tag(v_x_1339_) == 5)
{
lean_object* v_kvPairs_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1359_; 
v_kvPairs_1341_ = lean_ctor_get(v_x_1339_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v_x_1339_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1343_ = v_x_1339_;
v_isShared_1344_ = v_isSharedCheck_1359_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_kvPairs_1341_);
lean_dec(v_x_1339_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1359_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1345_; 
v___x_1345_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_kvPairs_1341_, v_x_1340_);
lean_dec(v_kvPairs_1341_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1346_ = ((lean_object*)(l_Lean_Json_getObjVal_x3f___closed__0));
v___x_1347_ = lean_string_append(v___x_1346_, v_x_1340_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set_tag(v___x_1343_, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1347_);
v___x_1349_ = v___x_1343_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
else
{
lean_object* v_val_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_del_object(v___x_1343_);
v_val_1351_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1345_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_val_1351_);
lean_dec(v___x_1345_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_val_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
}
else
{
lean_object* v___x_1360_; 
lean_dec(v_x_1339_);
v___x_1360_ = ((lean_object*)(l_Lean_Json_getObjVal_x3f___closed__1));
return v___x_1360_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjVal_x3f___boxed(lean_object* v_x_1361_, lean_object* v_x_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_Json_getObjVal_x3f(v_x_1361_, v_x_1362_);
lean_dec_ref(v_x_1362_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getArrVal_x3f(lean_object* v_x_1367_, lean_object* v_x_1368_){
_start:
{
if (lean_obj_tag(v_x_1367_) == 4)
{
lean_object* v_elems_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1385_; 
v_elems_1369_ = lean_ctor_get(v_x_1367_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v_x_1367_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1371_ = v_x_1367_;
v_isShared_1372_ = v_isSharedCheck_1385_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_elems_1369_);
lean_dec(v_x_1367_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1385_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1373_ = lean_array_get_size(v_elems_1369_);
v___x_1374_ = lean_nat_dec_lt(v_x_1368_, v___x_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
lean_dec_ref(v_elems_1369_);
v___x_1375_ = ((lean_object*)(l_Lean_Json_getArrVal_x3f___closed__0));
v___x_1376_ = l_Nat_reprFast(v_x_1368_);
v___x_1377_ = lean_string_append(v___x_1375_, v___x_1376_);
lean_dec_ref(v___x_1376_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set_tag(v___x_1371_, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1377_);
v___x_1379_ = v___x_1371_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
else
{
lean_object* v___x_1381_; lean_object* v___x_1383_; 
v___x_1381_ = lean_array_fget(v_elems_1369_, v_x_1368_);
lean_dec(v_x_1368_);
lean_dec_ref(v_elems_1369_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set_tag(v___x_1371_, 1);
lean_ctor_set(v___x_1371_, 0, v___x_1381_);
v___x_1383_ = v___x_1371_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1381_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
else
{
lean_object* v___x_1386_; 
lean_dec(v_x_1368_);
lean_dec(v_x_1367_);
v___x_1386_ = ((lean_object*)(l_Lean_Json_getArrVal_x3f___closed__1));
return v___x_1386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValD(lean_object* v_j_1387_, lean_object* v_k_1388_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Lean_Json_getObjVal_x3f(v_j_1387_, v_k_1388_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v___x_1390_; 
lean_dec_ref_known(v___x_1389_, 1);
v___x_1390_ = lean_box(0);
return v___x_1390_;
}
else
{
lean_object* v_a_1391_; 
v_a_1391_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_a_1391_);
lean_dec_ref_known(v___x_1389_, 1);
return v_a_1391_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValD___boxed(lean_object* v_j_1392_, lean_object* v_k_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Lean_Json_getObjValD(v_j_1392_, v_k_1393_);
lean_dec_ref(v_k_1393_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Json_setObjVal_x21_spec__1(lean_object* v_msg_1395_){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = lean_box(0);
v___x_1397_ = lean_panic_fn_borrowed(v___x_1396_, v_msg_1395_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(lean_object* v_msg_1398_){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = lean_box(1);
v___x_1400_ = lean_panic_fn_borrowed(v___x_1399_, v_msg_1398_);
return v___x_1400_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1404_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2));
v___x_1405_ = lean_unsigned_to_nat(35u);
v___x_1406_ = lean_unsigned_to_nat(182u);
v___x_1407_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1));
v___x_1408_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1409_ = l_mkPanicMessageWithDecl(v___x_1408_, v___x_1407_, v___x_1406_, v___x_1405_, v___x_1404_);
return v___x_1409_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1410_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2));
v___x_1411_ = lean_unsigned_to_nat(21u);
v___x_1412_ = lean_unsigned_to_nat(183u);
v___x_1413_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1));
v___x_1414_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1415_ = l_mkPanicMessageWithDecl(v___x_1414_, v___x_1413_, v___x_1412_, v___x_1411_, v___x_1410_);
return v___x_1415_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1418_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6));
v___x_1419_ = lean_unsigned_to_nat(35u);
v___x_1420_ = lean_unsigned_to_nat(276u);
v___x_1421_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5));
v___x_1422_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1423_ = l_mkPanicMessageWithDecl(v___x_1422_, v___x_1421_, v___x_1420_, v___x_1419_, v___x_1418_);
return v___x_1423_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1424_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6));
v___x_1425_ = lean_unsigned_to_nat(21u);
v___x_1426_ = lean_unsigned_to_nat(277u);
v___x_1427_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5));
v___x_1428_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1429_ = l_mkPanicMessageWithDecl(v___x_1428_, v___x_1427_, v___x_1426_, v___x_1425_, v___x_1424_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(lean_object* v_k_1430_, lean_object* v_v_1431_, lean_object* v_t_1432_){
_start:
{
if (lean_obj_tag(v_t_1432_) == 0)
{
lean_object* v_size_1433_; lean_object* v_k_1434_; lean_object* v_v_1435_; lean_object* v_l_1436_; lean_object* v_r_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1793_; 
v_size_1433_ = lean_ctor_get(v_t_1432_, 0);
v_k_1434_ = lean_ctor_get(v_t_1432_, 1);
v_v_1435_ = lean_ctor_get(v_t_1432_, 2);
v_l_1436_ = lean_ctor_get(v_t_1432_, 3);
v_r_1437_ = lean_ctor_get(v_t_1432_, 4);
v_isSharedCheck_1793_ = !lean_is_exclusive(v_t_1432_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1439_ = v_t_1432_;
v_isShared_1440_ = v_isSharedCheck_1793_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_r_1437_);
lean_inc(v_l_1436_);
lean_inc(v_v_1435_);
lean_inc(v_k_1434_);
lean_inc(v_size_1433_);
lean_dec(v_t_1432_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1793_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
uint8_t v___x_1441_; 
v___x_1441_ = lean_string_compare(v_k_1430_, v_k_1434_);
switch(v___x_1441_)
{
case 0:
{
lean_object* v___x_1442_; 
lean_dec(v_size_1433_);
v___x_1442_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1430_, v_v_1431_, v_l_1436_);
if (lean_obj_tag(v_r_1437_) == 0)
{
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_size_1443_; lean_object* v_size_1444_; lean_object* v_k_1445_; lean_object* v_v_1446_; lean_object* v_l_1447_; lean_object* v_r_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v_size_1443_ = lean_ctor_get(v_r_1437_, 0);
v_size_1444_ = lean_ctor_get(v___x_1442_, 0);
lean_inc(v_size_1444_);
v_k_1445_ = lean_ctor_get(v___x_1442_, 1);
lean_inc(v_k_1445_);
v_v_1446_ = lean_ctor_get(v___x_1442_, 2);
lean_inc(v_v_1446_);
v_l_1447_ = lean_ctor_get(v___x_1442_, 3);
lean_inc(v_l_1447_);
v_r_1448_ = lean_ctor_get(v___x_1442_, 4);
lean_inc(v_r_1448_);
v___x_1449_ = lean_unsigned_to_nat(3u);
v___x_1450_ = lean_nat_mul(v___x_1449_, v_size_1443_);
v___x_1451_ = lean_nat_dec_lt(v___x_1450_, v_size_1444_);
lean_dec(v___x_1450_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1456_; 
lean_dec(v_r_1448_);
lean_dec(v_l_1447_);
lean_dec(v_v_1446_);
lean_dec(v_k_1445_);
v___x_1452_ = lean_unsigned_to_nat(1u);
v___x_1453_ = lean_nat_add(v___x_1452_, v_size_1444_);
lean_dec(v_size_1444_);
v___x_1454_ = lean_nat_add(v___x_1453_, v_size_1443_);
lean_dec(v___x_1453_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 3, v___x_1442_);
lean_ctor_set(v___x_1439_, 0, v___x_1454_);
v___x_1456_ = v___x_1439_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1454_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_k_1434_);
lean_ctor_set(v_reuseFailAlloc_1457_, 2, v_v_1435_);
lean_ctor_set(v_reuseFailAlloc_1457_, 3, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1457_, 4, v_r_1437_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
else
{
lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1529_; 
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1529_ == 0)
{
lean_object* v_unused_1530_; lean_object* v_unused_1531_; lean_object* v_unused_1532_; lean_object* v_unused_1533_; lean_object* v_unused_1534_; 
v_unused_1530_ = lean_ctor_get(v___x_1442_, 4);
lean_dec(v_unused_1530_);
v_unused_1531_ = lean_ctor_get(v___x_1442_, 3);
lean_dec(v_unused_1531_);
v_unused_1532_ = lean_ctor_get(v___x_1442_, 2);
lean_dec(v_unused_1532_);
v_unused_1533_ = lean_ctor_get(v___x_1442_, 1);
lean_dec(v_unused_1533_);
v_unused_1534_ = lean_ctor_get(v___x_1442_, 0);
lean_dec(v_unused_1534_);
v___x_1459_ = v___x_1442_;
v_isShared_1460_ = v_isSharedCheck_1529_;
goto v_resetjp_1458_;
}
else
{
lean_dec(v___x_1442_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1529_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
if (lean_obj_tag(v_l_1447_) == 0)
{
if (lean_obj_tag(v_r_1448_) == 0)
{
lean_object* v_size_1461_; lean_object* v_size_1462_; lean_object* v_k_1463_; lean_object* v_v_1464_; lean_object* v_l_1465_; lean_object* v_r_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v_size_1461_ = lean_ctor_get(v_l_1447_, 0);
v_size_1462_ = lean_ctor_get(v_r_1448_, 0);
v_k_1463_ = lean_ctor_get(v_r_1448_, 1);
v_v_1464_ = lean_ctor_get(v_r_1448_, 2);
v_l_1465_ = lean_ctor_get(v_r_1448_, 3);
v_r_1466_ = lean_ctor_get(v_r_1448_, 4);
v___x_1467_ = lean_unsigned_to_nat(2u);
v___x_1468_ = lean_nat_mul(v___x_1467_, v_size_1461_);
v___x_1469_ = lean_nat_dec_lt(v_size_1462_, v___x_1468_);
lean_dec(v___x_1468_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1499_; 
lean_inc(v_r_1466_);
lean_inc(v_l_1465_);
lean_inc(v_v_1464_);
lean_inc(v_k_1463_);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_r_1448_);
if (v_isSharedCheck_1499_ == 0)
{
lean_object* v_unused_1500_; lean_object* v_unused_1501_; lean_object* v_unused_1502_; lean_object* v_unused_1503_; lean_object* v_unused_1504_; 
v_unused_1500_ = lean_ctor_get(v_r_1448_, 4);
lean_dec(v_unused_1500_);
v_unused_1501_ = lean_ctor_get(v_r_1448_, 3);
lean_dec(v_unused_1501_);
v_unused_1502_ = lean_ctor_get(v_r_1448_, 2);
lean_dec(v_unused_1502_);
v_unused_1503_ = lean_ctor_get(v_r_1448_, 1);
lean_dec(v_unused_1503_);
v_unused_1504_ = lean_ctor_get(v_r_1448_, 0);
lean_dec(v_unused_1504_);
v___x_1471_ = v_r_1448_;
v_isShared_1472_ = v_isSharedCheck_1499_;
goto v_resetjp_1470_;
}
else
{
lean_dec(v_r_1448_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1499_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___x_1487_; lean_object* v___y_1489_; 
v___x_1473_ = lean_unsigned_to_nat(1u);
v___x_1474_ = lean_nat_add(v___x_1473_, v_size_1444_);
lean_dec(v_size_1444_);
v___x_1475_ = lean_nat_add(v___x_1474_, v_size_1443_);
lean_dec(v___x_1474_);
v___x_1487_ = lean_nat_add(v___x_1473_, v_size_1461_);
if (lean_obj_tag(v_l_1465_) == 0)
{
lean_object* v_size_1497_; 
v_size_1497_ = lean_ctor_get(v_l_1465_, 0);
lean_inc(v_size_1497_);
v___y_1489_ = v_size_1497_;
goto v___jp_1488_;
}
else
{
lean_object* v___x_1498_; 
v___x_1498_ = lean_unsigned_to_nat(0u);
v___y_1489_ = v___x_1498_;
goto v___jp_1488_;
}
v___jp_1476_:
{
lean_object* v___x_1480_; lean_object* v___x_1482_; 
v___x_1480_ = lean_nat_add(v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec(v___y_1478_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 4, v_r_1437_);
lean_ctor_set(v___x_1471_, 3, v_r_1466_);
lean_ctor_set(v___x_1471_, 2, v_v_1435_);
lean_ctor_set(v___x_1471_, 1, v_k_1434_);
lean_ctor_set(v___x_1471_, 0, v___x_1480_);
v___x_1482_ = v___x_1471_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1480_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v_k_1434_);
lean_ctor_set(v_reuseFailAlloc_1486_, 2, v_v_1435_);
lean_ctor_set(v_reuseFailAlloc_1486_, 3, v_r_1466_);
lean_ctor_set(v_reuseFailAlloc_1486_, 4, v_r_1437_);
v___x_1482_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
lean_object* v___x_1484_; 
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 4, v___x_1482_);
lean_ctor_set(v___x_1459_, 3, v___y_1477_);
lean_ctor_set(v___x_1459_, 2, v_v_1464_);
lean_ctor_set(v___x_1459_, 1, v_k_1463_);
lean_ctor_set(v___x_1459_, 0, v___x_1475_);
v___x_1484_ = v___x_1459_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_k_1463_);
lean_ctor_set(v_reuseFailAlloc_1485_, 2, v_v_1464_);
lean_ctor_set(v_reuseFailAlloc_1485_, 3, v___y_1477_);
lean_ctor_set(v_reuseFailAlloc_1485_, 4, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
v___jp_1488_:
{
lean_object* v___x_1490_; lean_object* v___x_1492_; 
v___x_1490_ = lean_nat_add(v___x_1487_, v___y_1489_);
lean_dec(v___y_1489_);
lean_dec(v___x_1487_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 4, v_l_1465_);
lean_ctor_set(v___x_1439_, 3, v_l_1447_);
lean_ctor_set(v___x_1439_, 2, v_v_1446_);
lean_ctor_set(v___x_1439_, 1, v_k_1445_);
lean_ctor_set(v___x_1439_, 0, v___x_1490_);
v___x_1492_ = v___x_1439_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1490_);
lean_ctor_set(v_reuseFailAlloc_1496_, 1, v_k_1445_);
lean_ctor_set(v_reuseFailAlloc_1496_, 2, v_v_1446_);
lean_ctor_set(v_reuseFailAlloc_1496_, 3, v_l_1447_);
lean_ctor_set(v_reuseFailAlloc_1496_, 4, v_l_1465_);
v___x_1492_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_nat_add(v___x_1473_, v_size_1443_);
if (lean_obj_tag(v_r_1466_) == 0)
{
lean_object* v_size_1494_; 
v_size_1494_ = lean_ctor_get(v_r_1466_, 0);
lean_inc(v_size_1494_);
v___y_1477_ = v___x_1492_;
v___y_1478_ = v___x_1493_;
v___y_1479_ = v_size_1494_;
goto v___jp_1476_;
}
else
{
lean_object* v___x_1495_; 
v___x_1495_ = lean_unsigned_to_nat(0u);
v___y_1477_ = v___x_1492_;
v___y_1478_ = v___x_1493_;
v___y_1479_ = v___x_1495_;
goto v___jp_1476_;
}
}
}
}
}
else
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1511_; 
lean_del_object(v___x_1439_);
v___x_1505_ = lean_unsigned_to_nat(1u);
v___x_1506_ = lean_nat_add(v___x_1505_, v_size_1444_);
lean_dec(v_size_1444_);
v___x_1507_ = lean_nat_add(v___x_1506_, v_size_1443_);
lean_dec(v___x_1506_);
v___x_1508_ = lean_nat_add(v___x_1505_, v_size_1443_);
v___x_1509_ = lean_nat_add(v___x_1508_, v_size_1462_);
lean_dec(v___x_1508_);
lean_inc_ref(v_r_1437_);
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 4, v_r_1437_);
lean_ctor_set(v___x_1459_, 3, v_r_1448_);
lean_ctor_set(v___x_1459_, 2, v_v_1435_);
lean_ctor_set(v___x_1459_, 1, v_k_1434_);
lean_ctor_set(v___x_1459_, 0, v___x_1509_);
v___x_1511_ = v___x_1459_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1509_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_k_1434_);
lean_ctor_set(v_reuseFailAlloc_1524_, 2, v_v_1435_);
lean_ctor_set(v_reuseFailAlloc_1524_, 3, v_r_1448_);
lean_ctor_set(v_reuseFailAlloc_1524_, 4, v_r_1437_);
v___x_1511_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
v_isSharedCheck_1518_ = !lean_is_exclusive(v_r_1437_);
if (v_isSharedCheck_1518_ == 0)
{
lean_object* v_unused_1519_; lean_object* v_unused_1520_; lean_object* v_unused_1521_; lean_object* v_unused_1522_; lean_object* v_unused_1523_; 
v_unused_1519_ = lean_ctor_get(v_r_1437_, 4);
lean_dec(v_unused_1519_);
v_unused_1520_ = lean_ctor_get(v_r_1437_, 3);
lean_dec(v_unused_1520_);
v_unused_1521_ = lean_ctor_get(v_r_1437_, 2);
lean_dec(v_unused_1521_);
v_unused_1522_ = lean_ctor_get(v_r_1437_, 1);
lean_dec(v_unused_1522_);
v_unused_1523_ = lean_ctor_get(v_r_1437_, 0);
lean_dec(v_unused_1523_);
v___x_1513_ = v_r_1437_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_dec(v_r_1437_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 4, v___x_1511_);
lean_ctor_set(v___x_1513_, 3, v_l_1447_);
lean_ctor_set(v___x_1513_, 2, v_v_1446_);
lean_ctor_set(v___x_1513_, 1, v_k_1445_);
lean_ctor_set(v___x_1513_, 0, v___x_1507_);
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1507_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_k_1445_);
lean_ctor_set(v_reuseFailAlloc_1517_, 2, v_v_1446_);
lean_ctor_set(v_reuseFailAlloc_1517_, 3, v_l_1447_);
lean_ctor_set(v_reuseFailAlloc_1517_, 4, v___x_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
}
else
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
lean_dec_ref_known(v_l_1447_, 5);
lean_del_object(v___x_1459_);
lean_dec(v_v_1446_);
lean_dec(v_k_1445_);
lean_dec(v_size_1444_);
lean_dec_ref_known(v_r_1437_, 5);
lean_del_object(v___x_1439_);
lean_dec(v_v_1435_);
lean_dec(v_k_1434_);
v___x_1525_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3);
v___x_1526_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1525_);
return v___x_1526_;
}
}
else
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
lean_del_object(v___x_1459_);
lean_dec(v_r_1448_);
lean_dec(v_v_1446_);
lean_dec(v_k_1445_);
lean_dec(v_size_1444_);
lean_dec_ref_known(v_r_1437_, 5);
lean_del_object(v___x_1439_);
lean_dec(v_v_1435_);
lean_dec(v_k_1434_);
v___x_1527_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4);
v___x_1528_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1527_);
return v___x_1528_;
}
}
}
}
else
{
lean_object* v_size_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1539_; 
v_size_1535_ = lean_ctor_get(v_r_1437_, 0);
v___x_1536_ = lean_unsigned_to_nat(1u);
v___x_1537_ = lean_nat_add(v___x_1536_, v_size_1535_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 3, v___x_1442_);
lean_ctor_set(v___x_1439_, 0, v___x_1537_);
v___x_1539_ = v___x_1439_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1537_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v_k_1434_);
lean_ctor_set(v_reuseFailAlloc_1540_, 2, v_v_1435_);
lean_ctor_set(v_reuseFailAlloc_1540_, 3, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1540_, 4, v_r_1437_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
else
{
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_l_1541_; 
v_l_1541_ = lean_ctor_get(v___x_1442_, 3);
lean_inc(v_l_1541_);
if (lean_obj_tag(v_l_1541_) == 0)
{
lean_object* v_r_1542_; 
v_r_1542_ = lean_ctor_get(v___x_1442_, 4);
lean_inc(v_r_1542_);
if (lean_obj_tag(v_r_1542_) == 0)
{
lean_object* v_size_1543_; lean_object* v_k_1544_; lean_object* v_v_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1559_; 
v_size_1543_ = lean_ctor_get(v___x_1442_, 0);
v_k_1544_ = lean_ctor_get(v___x_1442_, 1);
v_v_1545_ = lean_ctor_get(v___x_1442_, 2);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1559_ == 0)
{
lean_object* v_unused_1560_; lean_object* v_unused_1561_; 
v_unused_1560_ = lean_ctor_get(v___x_1442_, 4);
lean_dec(v_unused_1560_);
v_unused_1561_ = lean_ctor_get(v___x_1442_, 3);
lean_dec(v_unused_1561_);
v___x_1547_ = v___x_1442_;
v_isShared_1548_ = v_isSharedCheck_1559_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_v_1545_);
lean_inc(v_k_1544_);
lean_inc(v_size_1543_);
lean_dec(v___x_1442_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1559_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v_size_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1554_; 
v_size_1549_ = lean_ctor_get(v_r_1542_, 0);
v___x_1550_ = lean_unsigned_to_nat(1u);
v___x_1551_ = lean_nat_add(v___x_1550_, v_size_1543_);
lean_dec(v_size_1543_);
v___x_1552_ = lean_nat_add(v___x_1550_, v_size_1549_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 4, v_r_1437_);
lean_ctor_set(v___x_1547_, 3, v_r_1542_);
lean_ctor_set(v___x_1547_, 2, v_v_1435_);
lean_ctor_set(v___x_1547_, 1, v_k_1434_);
lean_ctor_set(v___x_1547_, 0, v___x_1552_);
v___x_1554_ = v___x_1547_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1552_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_k_1434_);
lean_ctor_set(v_reuseFailAlloc_1558_, 2, v_v_1435_);
lean_ctor_set(v_reuseFailAlloc_1558_, 3, v_r_1542_);
lean_ctor_set(v_reuseFailAlloc_1558_, 4, v_r_1437_);
v___x_1554_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
lean_object* v___x_1556_; 
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 4, v___x_1554_);
lean_ctor_set(v___x_1439_, 3, v_l_1541_);
lean_ctor_set(v___x_1439_, 2, v_v_1545_);
lean_ctor_set(v___x_1439_, 1, v_k_1544_);
lean_ctor_set(v___x_1439_, 0, v___x_1551_);
v___x_1556_ = v___x_1439_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1551_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v_k_1544_);
lean_ctor_set(v_reuseFailAlloc_1557_, 2, v_v_1545_);
lean_ctor_set(v_reuseFailAlloc_1557_, 3, v_l_1541_);
lean_ctor_set(v_reuseFailAlloc_1557_, 4, v___x_1554_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
else
{
lean_object* v_k_1562_; lean_object* v_v_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1575_; 
v_k_1562_ = lean_ctor_get(v___x_1442_, 1);
v_v_1563_ = lean_ctor_get(v___x_1442_, 2);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1575_ == 0)
{
lean_object* v_unused_1576_; lean_object* v_unused_1577_; lean_object* v_unused_1578_; 
v_unused_1576_ = lean_ctor_get(v___x_1442_, 4);
lean_dec(v_unused_1576_);
v_unused_1577_ = lean_ctor_get(v___x_1442_, 3);
lean_dec(v_unused_1577_);
v_unused_1578_ = lean_ctor_get(v___x_1442_, 0);
lean_dec(v_unused_1578_);
v___x_1565_ = v___x_1442_;
v_isShared_1566_ = v_isSharedCheck_1575_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_v_1563_);
lean_inc(v_k_1562_);
lean_dec(v___x_1442_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1575_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1567_ = lean_unsigned_to_nat(3u);
v___x_1568_ = lean_unsigned_to_nat(1u);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 3, v_r_1542_);
lean_ctor_set(v___x_1565_, 2, v_v_1435_);
lean_ctor_set(v___x_1565_, 1, v_k_1434_);
lean_ctor_set(v___x_1565_, 0, v___x_1568_);
v___x_1570_ = v___x_1565_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1568_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v_k_1434_);
lean_ctor_set(v_reuseFailAlloc_1574_, 2, v_v_1435_);
lean_ctor_set(v_reuseFailAlloc_1574_, 3, v_r_1542_);
lean_ctor_set(v_reuseFailAlloc_1574_, 4, v_r_1542_);
v___x_1570_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
lean_object* v___x_1572_; 
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 4, v___x_1570_);
lean_ctor_set(v___x_1439_, 3, v_l_1541_);
lean_ctor_set(v___x_1439_, 2, v_v_1563_);
lean_ctor_set(v___x_1439_, 1, v_k_1562_);
lean_ctor_set(v___x_1439_, 0, v___x_1567_);
v___x_1572_ = v___x_1439_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1567_);
lean_ctor_set(v_reuseFailAlloc_1573_, 1, v_k_1562_);
lean_ctor_set(v_reuseFailAlloc_1573_, 2, v_v_1563_);
lean_ctor_set(v_reuseFailAlloc_1573_, 3, v_l_1541_);
lean_ctor_set(v_reuseFailAlloc_1573_, 4, v___x_1570_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
}
else
{
lean_object* v_r_1579_; 
v_r_1579_ = lean_ctor_get(v___x_1442_, 4);
lean_inc(v_r_1579_);
if (lean_obj_tag(v_r_1579_) == 0)
{
lean_object* v_k_1580_; lean_object* v_v_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1605_; 
v_k_1580_ = lean_ctor_get(v___x_1442_, 1);
v_v_1581_ = lean_ctor_get(v___x_1442_, 2);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1605_ == 0)
{
lean_object* v_unused_1606_; lean_object* v_unused_1607_; lean_object* v_unused_1608_; 
v_unused_1606_ = lean_ctor_get(v___x_1442_, 4);
lean_dec(v_unused_1606_);
v_unused_1607_ = lean_ctor_get(v___x_1442_, 3);
lean_dec(v_unused_1607_);
v_unused_1608_ = lean_ctor_get(v___x_1442_, 0);
lean_dec(v_unused_1608_);
v___x_1583_ = v___x_1442_;
v_isShared_1584_ = v_isSharedCheck_1605_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_v_1581_);
lean_inc(v_k_1580_);
lean_dec(v___x_1442_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1605_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v_k_1585_; lean_object* v_v_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1601_; 
v_k_1585_ = lean_ctor_get(v_r_1579_, 1);
v_v_1586_ = lean_ctor_get(v_r_1579_, 2);
v_isSharedCheck_1601_ = !lean_is_exclusive(v_r_1579_);
if (v_isSharedCheck_1601_ == 0)
{
lean_object* v_unused_1602_; lean_object* v_unused_1603_; lean_object* v_unused_1604_; 
v_unused_1602_ = lean_ctor_get(v_r_1579_, 4);
lean_dec(v_unused_1602_);
v_unused_1603_ = lean_ctor_get(v_r_1579_, 3);
lean_dec(v_unused_1603_);
v_unused_1604_ = lean_ctor_get(v_r_1579_, 0);
lean_dec(v_unused_1604_);
v___x_1588_ = v_r_1579_;
v_isShared_1589_ = v_isSharedCheck_1601_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_v_1586_);
lean_inc(v_k_1585_);
lean_dec(v_r_1579_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1601_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1593_; 
v___x_1590_ = lean_unsigned_to_nat(3u);
v___x_1591_ = lean_unsigned_to_nat(1u);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 4, v_l_1541_);
lean_ctor_set(v___x_1588_, 3, v_l_1541_);
lean_ctor_set(v___x_1588_, 2, v_v_1581_);
lean_ctor_set(v___x_1588_, 1, v_k_1580_);
lean_ctor_set(v___x_1588_, 0, v___x_1591_);
v___x_1593_ = v___x_1588_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1591_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v_k_1580_);
lean_ctor_set(v_reuseFailAlloc_1600_, 2, v_v_1581_);
lean_ctor_set(v_reuseFailAlloc_1600_, 3, v_l_1541_);
lean_ctor_set(v_reuseFailAlloc_1600_, 4, v_l_1541_);
v___x_1593_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
lean_object* v___x_1595_; 
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 4, v_l_1541_);
lean_ctor_set(v___x_1583_, 2, v_v_1435_);
lean_ctor_set(v___x_1583_, 1, v_k_1434_);
lean_ctor_set(v___x_1583_, 0, v___x_1591_);
v___x_1595_ = v___x_1583_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1591_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v_k_1434_);
lean_ctor_set(v_reuseFailAlloc_1599_, 2, v_v_1435_);
lean_ctor_set(v_reuseFailAlloc_1599_, 3, v_l_1541_);
lean_ctor_set(v_reuseFailAlloc_1599_, 4, v_l_1541_);
v___x_1595_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
lean_object* v___x_1597_; 
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 4, v___x_1595_);
lean_ctor_set(v___x_1439_, 3, v___x_1593_);
lean_ctor_set(v___x_1439_, 2, v_v_1586_);
lean_ctor_set(v___x_1439_, 1, v_k_1585_);
lean_ctor_set(v___x_1439_, 0, v___x_1590_);
v___x_1597_ = v___x_1439_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1590_);
lean_ctor_set(v_reuseFailAlloc_1598_, 1, v_k_1585_);
lean_ctor_set(v_reuseFailAlloc_1598_, 2, v_v_1586_);
lean_ctor_set(v_reuseFailAlloc_1598_, 3, v___x_1593_);
lean_ctor_set(v_reuseFailAlloc_1598_, 4, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
}
}
else
{
lean_object* v___x_1609_; lean_object* v___x_1611_; 
v___x_1609_ = lean_unsigned_to_nat(2u);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 4, v_r_1579_);
lean_ctor_set(v___x_1439_, 3, v___x_1442_);
lean_ctor_set(v___x_1439_, 0, v___x_1609_);
v___x_1611_ = v___x_1439_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v_k_1434_);
lean_ctor_set(v_reuseFailAlloc_1612_, 2, v_v_1435_);
lean_ctor_set(v_reuseFailAlloc_1612_, 3, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1612_, 4, v_r_1579_);
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
else
{
lean_object* v___x_1613_; lean_object* v___x_1615_; 
v___x_1613_ = lean_unsigned_to_nat(1u);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 4, v___x_1442_);
lean_ctor_set(v___x_1439_, 3, v___x_1442_);
lean_ctor_set(v___x_1439_, 0, v___x_1613_);
v___x_1615_ = v___x_1439_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1613_);
lean_ctor_set(v_reuseFailAlloc_1616_, 1, v_k_1434_);
lean_ctor_set(v_reuseFailAlloc_1616_, 2, v_v_1435_);
lean_ctor_set(v_reuseFailAlloc_1616_, 3, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1616_, 4, v___x_1442_);
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
case 1:
{
lean_object* v___x_1618_; 
lean_dec(v_v_1435_);
lean_dec(v_k_1434_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 2, v_v_1431_);
lean_ctor_set(v___x_1439_, 1, v_k_1430_);
v___x_1618_ = v___x_1439_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_size_1433_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_k_1430_);
lean_ctor_set(v_reuseFailAlloc_1619_, 2, v_v_1431_);
lean_ctor_set(v_reuseFailAlloc_1619_, 3, v_l_1436_);
lean_ctor_set(v_reuseFailAlloc_1619_, 4, v_r_1437_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
default: 
{
lean_object* v___x_1620_; 
lean_dec(v_size_1433_);
v___x_1620_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1430_, v_v_1431_, v_r_1437_);
if (lean_obj_tag(v_l_1436_) == 0)
{
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_size_1621_; lean_object* v_size_1622_; lean_object* v_k_1623_; lean_object* v_v_1624_; lean_object* v_l_1625_; lean_object* v_r_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; uint8_t v___x_1629_; 
v_size_1621_ = lean_ctor_get(v_l_1436_, 0);
v_size_1622_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_size_1622_);
v_k_1623_ = lean_ctor_get(v___x_1620_, 1);
lean_inc(v_k_1623_);
v_v_1624_ = lean_ctor_get(v___x_1620_, 2);
lean_inc(v_v_1624_);
v_l_1625_ = lean_ctor_get(v___x_1620_, 3);
lean_inc(v_l_1625_);
v_r_1626_ = lean_ctor_get(v___x_1620_, 4);
lean_inc(v_r_1626_);
v___x_1627_ = lean_unsigned_to_nat(3u);
v___x_1628_ = lean_nat_mul(v___x_1627_, v_size_1621_);
v___x_1629_ = lean_nat_dec_lt(v___x_1628_, v_size_1622_);
lean_dec(v___x_1628_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1634_; 
lean_dec(v_r_1626_);
lean_dec(v_l_1625_);
lean_dec(v_v_1624_);
lean_dec(v_k_1623_);
v___x_1630_ = lean_unsigned_to_nat(1u);
v___x_1631_ = lean_nat_add(v___x_1630_, v_size_1621_);
v___x_1632_ = lean_nat_add(v___x_1631_, v_size_1622_);
lean_dec(v_size_1622_);
lean_dec(v___x_1631_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 4, v___x_1620_);
lean_ctor_set(v___x_1439_, 0, v___x_1632_);
v___x_1634_ = v___x_1439_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1632_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v_k_1434_);
lean_ctor_set(v_reuseFailAlloc_1635_, 2, v_v_1435_);
lean_ctor_set(v_reuseFailAlloc_1635_, 3, v_l_1436_);
lean_ctor_set(v_reuseFailAlloc_1635_, 4, v___x_1620_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
else
{
lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1705_; 
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1705_ == 0)
{
lean_object* v_unused_1706_; lean_object* v_unused_1707_; lean_object* v_unused_1708_; lean_object* v_unused_1709_; lean_object* v_unused_1710_; 
v_unused_1706_ = lean_ctor_get(v___x_1620_, 4);
lean_dec(v_unused_1706_);
v_unused_1707_ = lean_ctor_get(v___x_1620_, 3);
lean_dec(v_unused_1707_);
v_unused_1708_ = lean_ctor_get(v___x_1620_, 2);
lean_dec(v_unused_1708_);
v_unused_1709_ = lean_ctor_get(v___x_1620_, 1);
lean_dec(v_unused_1709_);
v_unused_1710_ = lean_ctor_get(v___x_1620_, 0);
lean_dec(v_unused_1710_);
v___x_1637_ = v___x_1620_;
v_isShared_1638_ = v_isSharedCheck_1705_;
goto v_resetjp_1636_;
}
else
{
lean_dec(v___x_1620_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1705_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
if (lean_obj_tag(v_l_1625_) == 0)
{
if (lean_obj_tag(v_r_1626_) == 0)
{
lean_object* v_size_1639_; lean_object* v_k_1640_; lean_object* v_v_1641_; lean_object* v_l_1642_; lean_object* v_r_1643_; lean_object* v_size_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
v_size_1639_ = lean_ctor_get(v_l_1625_, 0);
v_k_1640_ = lean_ctor_get(v_l_1625_, 1);
v_v_1641_ = lean_ctor_get(v_l_1625_, 2);
v_l_1642_ = lean_ctor_get(v_l_1625_, 3);
v_r_1643_ = lean_ctor_get(v_l_1625_, 4);
v_size_1644_ = lean_ctor_get(v_r_1626_, 0);
v___x_1645_ = lean_unsigned_to_nat(2u);
v___x_1646_ = lean_nat_mul(v___x_1645_, v_size_1644_);
v___x_1647_ = lean_nat_dec_lt(v_size_1639_, v___x_1646_);
lean_dec(v___x_1646_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1676_; 
lean_inc(v_r_1643_);
lean_inc(v_l_1642_);
lean_inc(v_v_1641_);
lean_inc(v_k_1640_);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_l_1625_);
if (v_isSharedCheck_1676_ == 0)
{
lean_object* v_unused_1677_; lean_object* v_unused_1678_; lean_object* v_unused_1679_; lean_object* v_unused_1680_; lean_object* v_unused_1681_; 
v_unused_1677_ = lean_ctor_get(v_l_1625_, 4);
lean_dec(v_unused_1677_);
v_unused_1678_ = lean_ctor_get(v_l_1625_, 3);
lean_dec(v_unused_1678_);
v_unused_1679_ = lean_ctor_get(v_l_1625_, 2);
lean_dec(v_unused_1679_);
v_unused_1680_ = lean_ctor_get(v_l_1625_, 1);
lean_dec(v_unused_1680_);
v_unused_1681_ = lean_ctor_get(v_l_1625_, 0);
lean_dec(v_unused_1681_);
v___x_1649_ = v_l_1625_;
v_isShared_1650_ = v_isSharedCheck_1676_;
goto v_resetjp_1648_;
}
else
{
lean_dec(v_l_1625_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1676_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1666_; 
v___x_1651_ = lean_unsigned_to_nat(1u);
v___x_1652_ = lean_nat_add(v___x_1651_, v_size_1621_);
v___x_1653_ = lean_nat_add(v___x_1652_, v_size_1622_);
lean_dec(v_size_1622_);
if (lean_obj_tag(v_l_1642_) == 0)
{
lean_object* v_size_1674_; 
v_size_1674_ = lean_ctor_get(v_l_1642_, 0);
lean_inc(v_size_1674_);
v___y_1666_ = v_size_1674_;
goto v___jp_1665_;
}
else
{
lean_object* v___x_1675_; 
v___x_1675_ = lean_unsigned_to_nat(0u);
v___y_1666_ = v___x_1675_;
goto v___jp_1665_;
}
v___jp_1654_:
{
lean_object* v___x_1658_; lean_object* v___x_1660_; 
v___x_1658_ = lean_nat_add(v___y_1656_, v___y_1657_);
lean_dec(v___y_1657_);
lean_dec(v___y_1656_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 4, v_r_1626_);
lean_ctor_set(v___x_1649_, 3, v_r_1643_);
lean_ctor_set(v___x_1649_, 2, v_v_1624_);
lean_ctor_set(v___x_1649_, 1, v_k_1623_);
lean_ctor_set(v___x_1649_, 0, v___x_1658_);
v___x_1660_ = v___x_1649_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1658_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v_k_1623_);
lean_ctor_set(v_reuseFailAlloc_1664_, 2, v_v_1624_);
lean_ctor_set(v_reuseFailAlloc_1664_, 3, v_r_1643_);
lean_ctor_set(v_reuseFailAlloc_1664_, 4, v_r_1626_);
v___x_1660_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
lean_object* v___x_1662_; 
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 4, v___x_1660_);
lean_ctor_set(v___x_1637_, 3, v___y_1655_);
lean_ctor_set(v___x_1637_, 2, v_v_1641_);
lean_ctor_set(v___x_1637_, 1, v_k_1640_);
lean_ctor_set(v___x_1637_, 0, v___x_1653_);
v___x_1662_ = v___x_1637_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1653_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v_k_1640_);
lean_ctor_set(v_reuseFailAlloc_1663_, 2, v_v_1641_);
lean_ctor_set(v_reuseFailAlloc_1663_, 3, v___y_1655_);
lean_ctor_set(v_reuseFailAlloc_1663_, 4, v___x_1660_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
v___jp_1665_:
{
lean_object* v___x_1667_; lean_object* v___x_1669_; 
v___x_1667_ = lean_nat_add(v___x_1652_, v___y_1666_);
lean_dec(v___y_1666_);
lean_dec(v___x_1652_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 4, v_l_1642_);
lean_ctor_set(v___x_1439_, 0, v___x_1667_);
v___x_1669_ = v___x_1439_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1667_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v_k_1434_);
lean_ctor_set(v_reuseFailAlloc_1673_, 2, v_v_1435_);
lean_ctor_set(v_reuseFailAlloc_1673_, 3, v_l_1436_);
lean_ctor_set(v_reuseFailAlloc_1673_, 4, v_l_1642_);
v___x_1669_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_object* v___x_1670_; 
v___x_1670_ = lean_nat_add(v___x_1651_, v_size_1644_);
if (lean_obj_tag(v_r_1643_) == 0)
{
lean_object* v_size_1671_; 
v_size_1671_ = lean_ctor_get(v_r_1643_, 0);
lean_inc(v_size_1671_);
v___y_1655_ = v___x_1669_;
v___y_1656_ = v___x_1670_;
v___y_1657_ = v_size_1671_;
goto v___jp_1654_;
}
else
{
lean_object* v___x_1672_; 
v___x_1672_ = lean_unsigned_to_nat(0u);
v___y_1655_ = v___x_1669_;
v___y_1656_ = v___x_1670_;
v___y_1657_ = v___x_1672_;
goto v___jp_1654_;
}
}
}
}
}
else
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1687_; 
lean_del_object(v___x_1439_);
v___x_1682_ = lean_unsigned_to_nat(1u);
v___x_1683_ = lean_nat_add(v___x_1682_, v_size_1621_);
v___x_1684_ = lean_nat_add(v___x_1683_, v_size_1622_);
lean_dec(v_size_1622_);
v___x_1685_ = lean_nat_add(v___x_1683_, v_size_1639_);
lean_dec(v___x_1683_);
lean_inc_ref(v_l_1436_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 4, v_l_1625_);
lean_ctor_set(v___x_1637_, 3, v_l_1436_);
lean_ctor_set(v___x_1637_, 2, v_v_1435_);
lean_ctor_set(v___x_1637_, 1, v_k_1434_);
lean_ctor_set(v___x_1637_, 0, v___x_1685_);
v___x_1687_ = v___x_1637_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1685_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v_k_1434_);
lean_ctor_set(v_reuseFailAlloc_1700_, 2, v_v_1435_);
lean_ctor_set(v_reuseFailAlloc_1700_, 3, v_l_1436_);
lean_ctor_set(v_reuseFailAlloc_1700_, 4, v_l_1625_);
v___x_1687_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
v_isSharedCheck_1694_ = !lean_is_exclusive(v_l_1436_);
if (v_isSharedCheck_1694_ == 0)
{
lean_object* v_unused_1695_; lean_object* v_unused_1696_; lean_object* v_unused_1697_; lean_object* v_unused_1698_; lean_object* v_unused_1699_; 
v_unused_1695_ = lean_ctor_get(v_l_1436_, 4);
lean_dec(v_unused_1695_);
v_unused_1696_ = lean_ctor_get(v_l_1436_, 3);
lean_dec(v_unused_1696_);
v_unused_1697_ = lean_ctor_get(v_l_1436_, 2);
lean_dec(v_unused_1697_);
v_unused_1698_ = lean_ctor_get(v_l_1436_, 1);
lean_dec(v_unused_1698_);
v_unused_1699_ = lean_ctor_get(v_l_1436_, 0);
lean_dec(v_unused_1699_);
v___x_1689_ = v_l_1436_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_dec(v_l_1436_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 4, v_r_1626_);
lean_ctor_set(v___x_1689_, 3, v___x_1687_);
lean_ctor_set(v___x_1689_, 2, v_v_1624_);
lean_ctor_set(v___x_1689_, 1, v_k_1623_);
lean_ctor_set(v___x_1689_, 0, v___x_1684_);
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1684_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_k_1623_);
lean_ctor_set(v_reuseFailAlloc_1693_, 2, v_v_1624_);
lean_ctor_set(v_reuseFailAlloc_1693_, 3, v___x_1687_);
lean_ctor_set(v_reuseFailAlloc_1693_, 4, v_r_1626_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
}
else
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
lean_dec_ref_known(v_l_1625_, 5);
lean_del_object(v___x_1637_);
lean_dec(v_v_1624_);
lean_dec(v_k_1623_);
lean_dec(v_size_1622_);
lean_dec_ref_known(v_l_1436_, 5);
lean_del_object(v___x_1439_);
lean_dec(v_v_1435_);
lean_dec(v_k_1434_);
v___x_1701_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7);
v___x_1702_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1701_);
return v___x_1702_;
}
}
else
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
lean_del_object(v___x_1637_);
lean_dec(v_r_1626_);
lean_dec(v_v_1624_);
lean_dec(v_k_1623_);
lean_dec(v_size_1622_);
lean_dec_ref_known(v_l_1436_, 5);
lean_del_object(v___x_1439_);
lean_dec(v_v_1435_);
lean_dec(v_k_1434_);
v___x_1703_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8);
v___x_1704_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1703_);
return v___x_1704_;
}
}
}
}
else
{
lean_object* v_size_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1715_; 
v_size_1711_ = lean_ctor_get(v_l_1436_, 0);
v___x_1712_ = lean_unsigned_to_nat(1u);
v___x_1713_ = lean_nat_add(v___x_1712_, v_size_1711_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 4, v___x_1620_);
lean_ctor_set(v___x_1439_, 0, v___x_1713_);
v___x_1715_ = v___x_1439_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1713_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v_k_1434_);
lean_ctor_set(v_reuseFailAlloc_1716_, 2, v_v_1435_);
lean_ctor_set(v_reuseFailAlloc_1716_, 3, v_l_1436_);
lean_ctor_set(v_reuseFailAlloc_1716_, 4, v___x_1620_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
else
{
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_l_1717_; 
v_l_1717_ = lean_ctor_get(v___x_1620_, 3);
lean_inc(v_l_1717_);
if (lean_obj_tag(v_l_1717_) == 0)
{
lean_object* v_r_1718_; 
v_r_1718_ = lean_ctor_get(v___x_1620_, 4);
lean_inc(v_r_1718_);
if (lean_obj_tag(v_r_1718_) == 0)
{
lean_object* v_size_1719_; lean_object* v_k_1720_; lean_object* v_v_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1735_; 
v_size_1719_ = lean_ctor_get(v___x_1620_, 0);
v_k_1720_ = lean_ctor_get(v___x_1620_, 1);
v_v_1721_ = lean_ctor_get(v___x_1620_, 2);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1735_ == 0)
{
lean_object* v_unused_1736_; lean_object* v_unused_1737_; 
v_unused_1736_ = lean_ctor_get(v___x_1620_, 4);
lean_dec(v_unused_1736_);
v_unused_1737_ = lean_ctor_get(v___x_1620_, 3);
lean_dec(v_unused_1737_);
v___x_1723_ = v___x_1620_;
v_isShared_1724_ = v_isSharedCheck_1735_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_v_1721_);
lean_inc(v_k_1720_);
lean_inc(v_size_1719_);
lean_dec(v___x_1620_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1735_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v_size_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1730_; 
v_size_1725_ = lean_ctor_get(v_l_1717_, 0);
v___x_1726_ = lean_unsigned_to_nat(1u);
v___x_1727_ = lean_nat_add(v___x_1726_, v_size_1719_);
lean_dec(v_size_1719_);
v___x_1728_ = lean_nat_add(v___x_1726_, v_size_1725_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 4, v_l_1717_);
lean_ctor_set(v___x_1723_, 3, v_l_1436_);
lean_ctor_set(v___x_1723_, 2, v_v_1435_);
lean_ctor_set(v___x_1723_, 1, v_k_1434_);
lean_ctor_set(v___x_1723_, 0, v___x_1728_);
v___x_1730_ = v___x_1723_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v___x_1728_);
lean_ctor_set(v_reuseFailAlloc_1734_, 1, v_k_1434_);
lean_ctor_set(v_reuseFailAlloc_1734_, 2, v_v_1435_);
lean_ctor_set(v_reuseFailAlloc_1734_, 3, v_l_1436_);
lean_ctor_set(v_reuseFailAlloc_1734_, 4, v_l_1717_);
v___x_1730_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
lean_object* v___x_1732_; 
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 4, v_r_1718_);
lean_ctor_set(v___x_1439_, 3, v___x_1730_);
lean_ctor_set(v___x_1439_, 2, v_v_1721_);
lean_ctor_set(v___x_1439_, 1, v_k_1720_);
lean_ctor_set(v___x_1439_, 0, v___x_1727_);
v___x_1732_ = v___x_1439_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1727_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_k_1720_);
lean_ctor_set(v_reuseFailAlloc_1733_, 2, v_v_1721_);
lean_ctor_set(v_reuseFailAlloc_1733_, 3, v___x_1730_);
lean_ctor_set(v_reuseFailAlloc_1733_, 4, v_r_1718_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
else
{
lean_object* v_k_1738_; lean_object* v_v_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1763_; 
v_k_1738_ = lean_ctor_get(v___x_1620_, 1);
v_v_1739_ = lean_ctor_get(v___x_1620_, 2);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1763_ == 0)
{
lean_object* v_unused_1764_; lean_object* v_unused_1765_; lean_object* v_unused_1766_; 
v_unused_1764_ = lean_ctor_get(v___x_1620_, 4);
lean_dec(v_unused_1764_);
v_unused_1765_ = lean_ctor_get(v___x_1620_, 3);
lean_dec(v_unused_1765_);
v_unused_1766_ = lean_ctor_get(v___x_1620_, 0);
lean_dec(v_unused_1766_);
v___x_1741_ = v___x_1620_;
v_isShared_1742_ = v_isSharedCheck_1763_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_v_1739_);
lean_inc(v_k_1738_);
lean_dec(v___x_1620_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1763_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v_k_1743_; lean_object* v_v_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1759_; 
v_k_1743_ = lean_ctor_get(v_l_1717_, 1);
v_v_1744_ = lean_ctor_get(v_l_1717_, 2);
v_isSharedCheck_1759_ = !lean_is_exclusive(v_l_1717_);
if (v_isSharedCheck_1759_ == 0)
{
lean_object* v_unused_1760_; lean_object* v_unused_1761_; lean_object* v_unused_1762_; 
v_unused_1760_ = lean_ctor_get(v_l_1717_, 4);
lean_dec(v_unused_1760_);
v_unused_1761_ = lean_ctor_get(v_l_1717_, 3);
lean_dec(v_unused_1761_);
v_unused_1762_ = lean_ctor_get(v_l_1717_, 0);
lean_dec(v_unused_1762_);
v___x_1746_ = v_l_1717_;
v_isShared_1747_ = v_isSharedCheck_1759_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_v_1744_);
lean_inc(v_k_1743_);
lean_dec(v_l_1717_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1759_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1751_; 
v___x_1748_ = lean_unsigned_to_nat(3u);
v___x_1749_ = lean_unsigned_to_nat(1u);
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 4, v_r_1718_);
lean_ctor_set(v___x_1746_, 3, v_r_1718_);
lean_ctor_set(v___x_1746_, 2, v_v_1435_);
lean_ctor_set(v___x_1746_, 1, v_k_1434_);
lean_ctor_set(v___x_1746_, 0, v___x_1749_);
v___x_1751_ = v___x_1746_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1749_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_k_1434_);
lean_ctor_set(v_reuseFailAlloc_1758_, 2, v_v_1435_);
lean_ctor_set(v_reuseFailAlloc_1758_, 3, v_r_1718_);
lean_ctor_set(v_reuseFailAlloc_1758_, 4, v_r_1718_);
v___x_1751_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
lean_object* v___x_1753_; 
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 3, v_r_1718_);
lean_ctor_set(v___x_1741_, 0, v___x_1749_);
v___x_1753_ = v___x_1741_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1749_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v_k_1738_);
lean_ctor_set(v_reuseFailAlloc_1757_, 2, v_v_1739_);
lean_ctor_set(v_reuseFailAlloc_1757_, 3, v_r_1718_);
lean_ctor_set(v_reuseFailAlloc_1757_, 4, v_r_1718_);
v___x_1753_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
lean_object* v___x_1755_; 
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 4, v___x_1753_);
lean_ctor_set(v___x_1439_, 3, v___x_1751_);
lean_ctor_set(v___x_1439_, 2, v_v_1744_);
lean_ctor_set(v___x_1439_, 1, v_k_1743_);
lean_ctor_set(v___x_1439_, 0, v___x_1748_);
v___x_1755_ = v___x_1439_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1748_);
lean_ctor_set(v_reuseFailAlloc_1756_, 1, v_k_1743_);
lean_ctor_set(v_reuseFailAlloc_1756_, 2, v_v_1744_);
lean_ctor_set(v_reuseFailAlloc_1756_, 3, v___x_1751_);
lean_ctor_set(v_reuseFailAlloc_1756_, 4, v___x_1753_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1767_; 
v_r_1767_ = lean_ctor_get(v___x_1620_, 4);
lean_inc(v_r_1767_);
if (lean_obj_tag(v_r_1767_) == 0)
{
lean_object* v_k_1768_; lean_object* v_v_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1781_; 
v_k_1768_ = lean_ctor_get(v___x_1620_, 1);
v_v_1769_ = lean_ctor_get(v___x_1620_, 2);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1781_ == 0)
{
lean_object* v_unused_1782_; lean_object* v_unused_1783_; lean_object* v_unused_1784_; 
v_unused_1782_ = lean_ctor_get(v___x_1620_, 4);
lean_dec(v_unused_1782_);
v_unused_1783_ = lean_ctor_get(v___x_1620_, 3);
lean_dec(v_unused_1783_);
v_unused_1784_ = lean_ctor_get(v___x_1620_, 0);
lean_dec(v_unused_1784_);
v___x_1771_ = v___x_1620_;
v_isShared_1772_ = v_isSharedCheck_1781_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_v_1769_);
lean_inc(v_k_1768_);
lean_dec(v___x_1620_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1781_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1776_; 
v___x_1773_ = lean_unsigned_to_nat(3u);
v___x_1774_ = lean_unsigned_to_nat(1u);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 4, v_l_1717_);
lean_ctor_set(v___x_1771_, 2, v_v_1435_);
lean_ctor_set(v___x_1771_, 1, v_k_1434_);
lean_ctor_set(v___x_1771_, 0, v___x_1774_);
v___x_1776_ = v___x_1771_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1774_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v_k_1434_);
lean_ctor_set(v_reuseFailAlloc_1780_, 2, v_v_1435_);
lean_ctor_set(v_reuseFailAlloc_1780_, 3, v_l_1717_);
lean_ctor_set(v_reuseFailAlloc_1780_, 4, v_l_1717_);
v___x_1776_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
lean_object* v___x_1778_; 
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 4, v_r_1767_);
lean_ctor_set(v___x_1439_, 3, v___x_1776_);
lean_ctor_set(v___x_1439_, 2, v_v_1769_);
lean_ctor_set(v___x_1439_, 1, v_k_1768_);
lean_ctor_set(v___x_1439_, 0, v___x_1773_);
v___x_1778_ = v___x_1439_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1773_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_k_1768_);
lean_ctor_set(v_reuseFailAlloc_1779_, 2, v_v_1769_);
lean_ctor_set(v_reuseFailAlloc_1779_, 3, v___x_1776_);
lean_ctor_set(v_reuseFailAlloc_1779_, 4, v_r_1767_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
else
{
lean_object* v___x_1785_; lean_object* v___x_1787_; 
v___x_1785_ = lean_unsigned_to_nat(2u);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 4, v___x_1620_);
lean_ctor_set(v___x_1439_, 3, v_r_1767_);
lean_ctor_set(v___x_1439_, 0, v___x_1785_);
v___x_1787_ = v___x_1439_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1785_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v_k_1434_);
lean_ctor_set(v_reuseFailAlloc_1788_, 2, v_v_1435_);
lean_ctor_set(v_reuseFailAlloc_1788_, 3, v_r_1767_);
lean_ctor_set(v_reuseFailAlloc_1788_, 4, v___x_1620_);
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
else
{
lean_object* v___x_1789_; lean_object* v___x_1791_; 
v___x_1789_ = lean_unsigned_to_nat(1u);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 4, v___x_1620_);
lean_ctor_set(v___x_1439_, 3, v___x_1620_);
lean_ctor_set(v___x_1439_, 0, v___x_1789_);
v___x_1791_ = v___x_1439_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1789_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_k_1434_);
lean_ctor_set(v_reuseFailAlloc_1792_, 2, v_v_1435_);
lean_ctor_set(v_reuseFailAlloc_1792_, 3, v___x_1620_);
lean_ctor_set(v_reuseFailAlloc_1792_, 4, v___x_1620_);
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
}
}
}
else
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = lean_unsigned_to_nat(1u);
v___x_1795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
lean_ctor_set(v___x_1795_, 1, v_k_1430_);
lean_ctor_set(v___x_1795_, 2, v_v_1431_);
lean_ctor_set(v___x_1795_, 3, v_t_1432_);
lean_ctor_set(v___x_1795_, 4, v_t_1432_);
return v___x_1795_;
}
}
}
static lean_object* _init_l_Lean_Json_setObjVal_x21___closed__2(void){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1798_ = ((lean_object*)(l_Lean_Json_setObjVal_x21___closed__1));
v___x_1799_ = lean_unsigned_to_nat(21u);
v___x_1800_ = lean_unsigned_to_nat(285u);
v___x_1801_ = ((lean_object*)(l_Lean_Json_setObjVal_x21___closed__0));
v___x_1802_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0));
v___x_1803_ = l_mkPanicMessageWithDecl(v___x_1802_, v___x_1801_, v___x_1800_, v___x_1799_, v___x_1798_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_setObjVal_x21(lean_object* v_x_1804_, lean_object* v_x_1805_, lean_object* v_x_1806_){
_start:
{
if (lean_obj_tag(v_x_1804_) == 5)
{
lean_object* v_kvPairs_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1815_; 
v_kvPairs_1807_ = lean_ctor_get(v_x_1804_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v_x_1804_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1809_ = v_x_1804_;
v_isShared_1810_ = v_isSharedCheck_1815_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_kvPairs_1807_);
lean_dec(v_x_1804_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1815_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; lean_object* v___x_1813_; 
v___x_1811_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_x_1805_, v_x_1806_, v_kvPairs_1807_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v___x_1811_);
v___x_1813_ = v___x_1809_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
else
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
lean_dec(v_x_1806_);
lean_dec_ref(v_x_1805_);
lean_dec(v_x_1804_);
v___x_1816_ = lean_obj_once(&l_Lean_Json_setObjVal_x21___closed__2, &l_Lean_Json_setObjVal_x21___closed__2_once, _init_l_Lean_Json_setObjVal_x21___closed__2);
v___x_1817_ = l_panic___at___00Lean_Json_setObjVal_x21_spec__1(v___x_1816_);
return v___x_1817_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0(lean_object* v_00_u03b2_1818_, lean_object* v_msg_1819_){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v_msg_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0(lean_object* v_00_u03b2_1821_, lean_object* v_k_1822_, lean_object* v_v_1823_, lean_object* v_t_1824_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1822_, v_v_1823_, v_t_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(lean_object* v_init_1826_, lean_object* v_x_1827_){
_start:
{
if (lean_obj_tag(v_x_1827_) == 0)
{
lean_object* v_k_1828_; lean_object* v_v_1829_; lean_object* v_l_1830_; lean_object* v_r_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v_k_1828_ = lean_ctor_get(v_x_1827_, 1);
lean_inc(v_k_1828_);
v_v_1829_ = lean_ctor_get(v_x_1827_, 2);
lean_inc(v_v_1829_);
v_l_1830_ = lean_ctor_get(v_x_1827_, 3);
lean_inc(v_l_1830_);
v_r_1831_ = lean_ctor_get(v_x_1827_, 4);
lean_inc(v_r_1831_);
lean_dec_ref_known(v_x_1827_, 5);
v___x_1832_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_init_1826_, v_l_1830_);
v___x_1833_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1828_, v_v_1829_, v___x_1832_);
v_init_1826_ = v___x_1833_;
v_x_1827_ = v_r_1831_;
goto _start;
}
else
{
return v_init_1826_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mergeObj(lean_object* v_x_1835_, lean_object* v_x_1836_){
_start:
{
if (lean_obj_tag(v_x_1835_) == 5)
{
if (lean_obj_tag(v_x_1836_) == 5)
{
lean_object* v_kvPairs_1837_; lean_object* v_kvPairs_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1846_; 
v_kvPairs_1837_ = lean_ctor_get(v_x_1835_, 0);
lean_inc(v_kvPairs_1837_);
lean_dec_ref_known(v_x_1835_, 1);
v_kvPairs_1838_ = lean_ctor_get(v_x_1836_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v_x_1836_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1840_ = v_x_1836_;
v_isShared_1841_ = v_isSharedCheck_1846_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_kvPairs_1838_);
lean_dec(v_x_1836_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1846_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1842_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_kvPairs_1837_, v_kvPairs_1838_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1842_);
v___x_1844_ = v___x_1840_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
else
{
lean_dec_ref_known(v_x_1835_, 1);
return v_x_1836_;
}
}
else
{
lean_dec(v_x_1835_);
return v_x_1836_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0(lean_object* v_init_1847_, lean_object* v_t_1848_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_init_1847_, v_t_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorIdx(lean_object* v_x_1850_){
_start:
{
if (lean_obj_tag(v_x_1850_) == 0)
{
lean_object* v___x_1851_; 
v___x_1851_ = lean_unsigned_to_nat(0u);
return v___x_1851_;
}
else
{
lean_object* v___x_1852_; 
v___x_1852_ = lean_unsigned_to_nat(1u);
return v___x_1852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorIdx___boxed(lean_object* v_x_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lean_Json_Structured_ctorIdx(v_x_1853_);
lean_dec_ref(v_x_1853_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim___redArg(lean_object* v_t_1855_, lean_object* v_k_1856_){
_start:
{
if (lean_obj_tag(v_t_1855_) == 0)
{
lean_object* v_elems_1857_; lean_object* v___x_1858_; 
v_elems_1857_ = lean_ctor_get(v_t_1855_, 0);
lean_inc_ref(v_elems_1857_);
lean_dec_ref_known(v_t_1855_, 1);
v___x_1858_ = lean_apply_1(v_k_1856_, v_elems_1857_);
return v___x_1858_;
}
else
{
lean_object* v_kvPairs_1859_; lean_object* v___x_1860_; 
v_kvPairs_1859_ = lean_ctor_get(v_t_1855_, 0);
lean_inc(v_kvPairs_1859_);
lean_dec_ref_known(v_t_1855_, 1);
v___x_1860_ = lean_apply_1(v_k_1856_, v_kvPairs_1859_);
return v___x_1860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim(lean_object* v_motive_1861_, lean_object* v_ctorIdx_1862_, lean_object* v_t_1863_, lean_object* v_h_1864_, lean_object* v_k_1865_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1863_, v_k_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim___boxed(lean_object* v_motive_1867_, lean_object* v_ctorIdx_1868_, lean_object* v_t_1869_, lean_object* v_h_1870_, lean_object* v_k_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Lean_Json_Structured_ctorElim(v_motive_1867_, v_ctorIdx_1868_, v_t_1869_, v_h_1870_, v_k_1871_);
lean_dec(v_ctorIdx_1868_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_arr_elim___redArg(lean_object* v_t_1873_, lean_object* v_arr_1874_){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1873_, v_arr_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_arr_elim(lean_object* v_motive_1876_, lean_object* v_t_1877_, lean_object* v_h_1878_, lean_object* v_arr_1879_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1877_, v_arr_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_obj_elim___redArg(lean_object* v_t_1881_, lean_object* v_obj_1882_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1881_, v_obj_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_obj_elim(lean_object* v_motive_1884_, lean_object* v_t_1885_, lean_object* v_h_1886_, lean_object* v_obj_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1885_, v_obj_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeArrayStructured___lam__0(lean_object* v_elems_1889_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1890_, 0, v_elems_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeRawStringStructured___lam__0(lean_object* v_kvPairs_1893_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1894_, 0, v_kvPairs_1893_);
return v___x_1894_;
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
