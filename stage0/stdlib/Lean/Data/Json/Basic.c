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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
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
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceR!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceR! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceL!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceL! input was not balanced"};
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
v___x_151_ = lean_int_dec_lt(v___y_147_, v___y_148_);
lean_dec(v___y_148_);
lean_dec(v___y_147_);
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
v___y_147_ = v_snd_159_;
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
v___y_146_ = v___x_162_;
v___y_147_ = v_snd_159_;
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
v___x_279_ = lean_nat_div(v___y_273_, v_e_x27_278_);
v_left_280_ = l_Nat_reprFast(v___x_279_);
v___x_281_ = lean_int_dec_eq(v___y_274_, v___x_270_);
v___x_282_ = lean_nat_mod(v___y_273_, v_e_x27_278_);
lean_dec(v___y_273_);
v___x_283_ = lean_nat_dec_eq(v___x_282_, v___x_247_);
if (v___x_283_ == 0)
{
v___y_249_ = v_left_280_;
v___y_250_ = v___x_282_;
v___y_251_ = v_e_x27_278_;
v___y_252_ = v___x_281_;
v___y_253_ = v___y_272_;
v___y_254_ = v___y_274_;
v___y_255_ = v___x_283_;
goto v___jp_248_;
}
else
{
v___y_249_ = v_left_280_;
v___y_250_ = v___x_282_;
v___y_251_ = v_e_x27_278_;
v___y_252_ = v___x_281_;
v___y_253_ = v___y_272_;
v___y_254_ = v___y_274_;
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
v___y_272_ = v___y_285_;
v___y_273_ = v_m_286_;
v___y_274_ = v___x_270_;
goto v___jp_271_;
}
else
{
v___y_272_ = v___y_285_;
v___y_273_ = v_m_286_;
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
lean_inc_ref(v___y_238_);
v___x_240_ = lean_string_append(v___y_238_, v___y_236_);
lean_dec_ref(v___y_236_);
v___x_241_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__0));
v___x_242_ = lean_string_append(v___x_240_, v___x_241_);
v___x_243_ = lean_string_append(v___x_242_, v___y_237_);
lean_dec_ref(v___y_237_);
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
lean_dec_ref(v___x_259_);
v_e_262_ = l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0(v___x_257_, v___x_261_, v___x_258_);
v_right_263_ = lean_string_utf8_extract(v___x_257_, v___x_261_, v_e_262_);
lean_dec(v_e_262_);
lean_dec(v___x_261_);
lean_dec_ref(v___x_257_);
if (v___y_252_ == 0)
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_264_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__1));
v___x_265_ = l_Int_repr(v___y_254_);
lean_dec(v___y_254_);
v___x_266_ = lean_string_append(v___x_264_, v___x_265_);
lean_dec_ref(v___x_265_);
v___y_236_ = v___y_249_;
v___y_237_ = v_right_263_;
v___y_238_ = v___y_253_;
v___y_239_ = v___x_266_;
goto v___jp_235_;
}
else
{
lean_object* v___x_267_; 
lean_dec(v___y_254_);
v___x_267_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__2));
v___y_236_ = v___y_249_;
v___y_237_ = v_right_263_;
v___y_238_ = v___y_253_;
v___y_239_ = v___x_267_;
goto v___jp_235_;
}
}
else
{
lean_object* v___x_268_; 
lean_dec(v___y_254_);
lean_dec(v___y_251_);
lean_dec(v___y_250_);
lean_inc_ref(v___y_253_);
v___x_268_ = lean_string_append(v___y_253_, v___y_249_);
lean_dec_ref(v___y_249_);
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
lean_dec(v___x_431_);
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
lean_dec_ref(v___x_452_);
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
lean_dec_ref(v_t_557_);
v___x_560_ = lean_box(v_b_559_);
v___x_561_ = lean_apply_1(v_k_558_, v___x_560_);
return v___x_561_;
}
case 5:
{
lean_object* v_kvPairs_562_; lean_object* v___x_563_; 
v_kvPairs_562_ = lean_ctor_get(v_t_557_, 0);
lean_inc(v_kvPairs_562_);
lean_dec_ref(v_t_557_);
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
v___x_645_ = lean_string_dec_lt(v_k_640_, v_k_641_);
if (v___x_645_ == 0)
{
uint8_t v___x_646_; 
v___x_646_ = lean_string_dec_eq(v_k_640_, v_k_641_);
if (v___x_646_ == 0)
{
v_t_639_ = v_r_644_;
goto _start;
}
else
{
lean_object* v___x_648_; 
lean_inc(v_v_642_);
v___x_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_648_, 0, v_v_642_);
return v___x_648_;
}
}
else
{
v_t_639_ = v_l_643_;
goto _start;
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
lean_dec_ref(v___x_677_);
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
lean_dec_ref(v_fst_718_);
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
lean_object* v_size_886_; lean_object* v_k_887_; lean_object* v_v_888_; lean_object* v_l_889_; lean_object* v_r_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_1171_; 
v_size_886_ = lean_ctor_get(v_t_885_, 0);
v_k_887_ = lean_ctor_get(v_t_885_, 1);
v_v_888_ = lean_ctor_get(v_t_885_, 2);
v_l_889_ = lean_ctor_get(v_t_885_, 3);
v_r_890_ = lean_ctor_get(v_t_885_, 4);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_t_885_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_892_ = v_t_885_;
v_isShared_893_ = v_isSharedCheck_1171_;
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
v_isShared_893_ = v_isSharedCheck_1171_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
uint8_t v___x_894_; 
v___x_894_ = lean_string_dec_lt(v_k_883_, v_k_887_);
if (v___x_894_ == 0)
{
uint8_t v___x_895_; 
v___x_895_ = lean_string_dec_eq(v_k_883_, v_k_887_);
if (v___x_895_ == 0)
{
lean_object* v_impl_896_; lean_object* v___x_897_; 
lean_dec(v_size_886_);
v_impl_896_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_883_, v_v_884_, v_r_890_);
v___x_897_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_889_) == 0)
{
lean_object* v_size_898_; lean_object* v_size_899_; lean_object* v_k_900_; lean_object* v_v_901_; lean_object* v_l_902_; lean_object* v_r_903_; lean_object* v___x_904_; lean_object* v___x_905_; uint8_t v___x_906_; 
v_size_898_ = lean_ctor_get(v_l_889_, 0);
v_size_899_ = lean_ctor_get(v_impl_896_, 0);
lean_inc(v_size_899_);
v_k_900_ = lean_ctor_get(v_impl_896_, 1);
lean_inc(v_k_900_);
v_v_901_ = lean_ctor_get(v_impl_896_, 2);
lean_inc(v_v_901_);
v_l_902_ = lean_ctor_get(v_impl_896_, 3);
lean_inc(v_l_902_);
v_r_903_ = lean_ctor_get(v_impl_896_, 4);
lean_inc(v_r_903_);
v___x_904_ = lean_unsigned_to_nat(3u);
v___x_905_ = lean_nat_mul(v___x_904_, v_size_898_);
v___x_906_ = lean_nat_dec_lt(v___x_905_, v_size_899_);
lean_dec(v___x_905_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_910_; 
lean_dec(v_r_903_);
lean_dec(v_l_902_);
lean_dec(v_v_901_);
lean_dec(v_k_900_);
v___x_907_ = lean_nat_add(v___x_897_, v_size_898_);
v___x_908_ = lean_nat_add(v___x_907_, v_size_899_);
lean_dec(v_size_899_);
lean_dec(v___x_907_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 4, v_impl_896_);
lean_ctor_set(v___x_892_, 0, v___x_908_);
v___x_910_ = v___x_892_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_908_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_911_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_911_, 3, v_l_889_);
lean_ctor_set(v_reuseFailAlloc_911_, 4, v_impl_896_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
else
{
lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_975_; 
v_isSharedCheck_975_ = !lean_is_exclusive(v_impl_896_);
if (v_isSharedCheck_975_ == 0)
{
lean_object* v_unused_976_; lean_object* v_unused_977_; lean_object* v_unused_978_; lean_object* v_unused_979_; lean_object* v_unused_980_; 
v_unused_976_ = lean_ctor_get(v_impl_896_, 4);
lean_dec(v_unused_976_);
v_unused_977_ = lean_ctor_get(v_impl_896_, 3);
lean_dec(v_unused_977_);
v_unused_978_ = lean_ctor_get(v_impl_896_, 2);
lean_dec(v_unused_978_);
v_unused_979_ = lean_ctor_get(v_impl_896_, 1);
lean_dec(v_unused_979_);
v_unused_980_ = lean_ctor_get(v_impl_896_, 0);
lean_dec(v_unused_980_);
v___x_913_ = v_impl_896_;
v_isShared_914_ = v_isSharedCheck_975_;
goto v_resetjp_912_;
}
else
{
lean_dec(v_impl_896_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_975_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v_size_915_; lean_object* v_k_916_; lean_object* v_v_917_; lean_object* v_l_918_; lean_object* v_r_919_; lean_object* v_size_920_; lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v_size_915_ = lean_ctor_get(v_l_902_, 0);
v_k_916_ = lean_ctor_get(v_l_902_, 1);
v_v_917_ = lean_ctor_get(v_l_902_, 2);
v_l_918_ = lean_ctor_get(v_l_902_, 3);
v_r_919_ = lean_ctor_get(v_l_902_, 4);
v_size_920_ = lean_ctor_get(v_r_903_, 0);
v___x_921_ = lean_unsigned_to_nat(2u);
v___x_922_ = lean_nat_mul(v___x_921_, v_size_920_);
v___x_923_ = lean_nat_dec_lt(v_size_915_, v___x_922_);
lean_dec(v___x_922_);
if (v___x_923_ == 0)
{
lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_951_; 
lean_inc(v_r_919_);
lean_inc(v_l_918_);
lean_inc(v_v_917_);
lean_inc(v_k_916_);
v_isSharedCheck_951_ = !lean_is_exclusive(v_l_902_);
if (v_isSharedCheck_951_ == 0)
{
lean_object* v_unused_952_; lean_object* v_unused_953_; lean_object* v_unused_954_; lean_object* v_unused_955_; lean_object* v_unused_956_; 
v_unused_952_ = lean_ctor_get(v_l_902_, 4);
lean_dec(v_unused_952_);
v_unused_953_ = lean_ctor_get(v_l_902_, 3);
lean_dec(v_unused_953_);
v_unused_954_ = lean_ctor_get(v_l_902_, 2);
lean_dec(v_unused_954_);
v_unused_955_ = lean_ctor_get(v_l_902_, 1);
lean_dec(v_unused_955_);
v_unused_956_ = lean_ctor_get(v_l_902_, 0);
lean_dec(v_unused_956_);
v___x_925_ = v_l_902_;
v_isShared_926_ = v_isSharedCheck_951_;
goto v_resetjp_924_;
}
else
{
lean_dec(v_l_902_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_951_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_941_; 
v___x_927_ = lean_nat_add(v___x_897_, v_size_898_);
v___x_928_ = lean_nat_add(v___x_927_, v_size_899_);
lean_dec(v_size_899_);
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
v___jp_929_:
{
lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_933_ = lean_nat_add(v___y_930_, v___y_932_);
lean_dec(v___y_932_);
lean_dec(v___y_930_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 4, v_r_903_);
lean_ctor_set(v___x_925_, 3, v_r_919_);
lean_ctor_set(v___x_925_, 2, v_v_901_);
lean_ctor_set(v___x_925_, 1, v_k_900_);
lean_ctor_set(v___x_925_, 0, v___x_933_);
v___x_935_ = v___x_925_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_933_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_k_900_);
lean_ctor_set(v_reuseFailAlloc_939_, 2, v_v_901_);
lean_ctor_set(v_reuseFailAlloc_939_, 3, v_r_919_);
lean_ctor_set(v_reuseFailAlloc_939_, 4, v_r_903_);
v___x_935_ = v_reuseFailAlloc_939_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
lean_object* v___x_937_; 
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 4, v___x_935_);
lean_ctor_set(v___x_913_, 3, v___y_931_);
lean_ctor_set(v___x_913_, 2, v_v_917_);
lean_ctor_set(v___x_913_, 1, v_k_916_);
lean_ctor_set(v___x_913_, 0, v___x_928_);
v___x_937_ = v___x_913_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_928_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v_k_916_);
lean_ctor_set(v_reuseFailAlloc_938_, 2, v_v_917_);
lean_ctor_set(v_reuseFailAlloc_938_, 3, v___y_931_);
lean_ctor_set(v_reuseFailAlloc_938_, 4, v___x_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
v___jp_940_:
{
lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_942_ = lean_nat_add(v___x_927_, v___y_941_);
lean_dec(v___y_941_);
lean_dec(v___x_927_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 4, v_l_918_);
lean_ctor_set(v___x_892_, 0, v___x_942_);
v___x_944_ = v___x_892_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_948_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_948_, 3, v_l_889_);
lean_ctor_set(v_reuseFailAlloc_948_, 4, v_l_918_);
v___x_944_ = v_reuseFailAlloc_948_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_945_; 
v___x_945_ = lean_nat_add(v___x_897_, v_size_920_);
if (lean_obj_tag(v_r_919_) == 0)
{
lean_object* v_size_946_; 
v_size_946_ = lean_ctor_get(v_r_919_, 0);
lean_inc(v_size_946_);
v___y_930_ = v___x_945_;
v___y_931_ = v___x_944_;
v___y_932_ = v_size_946_;
goto v___jp_929_;
}
else
{
lean_object* v___x_947_; 
v___x_947_ = lean_unsigned_to_nat(0u);
v___y_930_ = v___x_945_;
v___y_931_ = v___x_944_;
v___y_932_ = v___x_947_;
goto v___jp_929_;
}
}
}
}
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_961_; 
lean_del_object(v___x_892_);
v___x_957_ = lean_nat_add(v___x_897_, v_size_898_);
v___x_958_ = lean_nat_add(v___x_957_, v_size_899_);
lean_dec(v_size_899_);
v___x_959_ = lean_nat_add(v___x_957_, v_size_915_);
lean_dec(v___x_957_);
lean_inc_ref(v_l_889_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 4, v_l_902_);
lean_ctor_set(v___x_913_, 3, v_l_889_);
lean_ctor_set(v___x_913_, 2, v_v_888_);
lean_ctor_set(v___x_913_, 1, v_k_887_);
lean_ctor_set(v___x_913_, 0, v___x_959_);
v___x_961_ = v___x_913_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_959_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_974_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_974_, 3, v_l_889_);
lean_ctor_set(v_reuseFailAlloc_974_, 4, v_l_902_);
v___x_961_ = v_reuseFailAlloc_974_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
v_isSharedCheck_968_ = !lean_is_exclusive(v_l_889_);
if (v_isSharedCheck_968_ == 0)
{
lean_object* v_unused_969_; lean_object* v_unused_970_; lean_object* v_unused_971_; lean_object* v_unused_972_; lean_object* v_unused_973_; 
v_unused_969_ = lean_ctor_get(v_l_889_, 4);
lean_dec(v_unused_969_);
v_unused_970_ = lean_ctor_get(v_l_889_, 3);
lean_dec(v_unused_970_);
v_unused_971_ = lean_ctor_get(v_l_889_, 2);
lean_dec(v_unused_971_);
v_unused_972_ = lean_ctor_get(v_l_889_, 1);
lean_dec(v_unused_972_);
v_unused_973_ = lean_ctor_get(v_l_889_, 0);
lean_dec(v_unused_973_);
v___x_963_ = v_l_889_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_dec(v_l_889_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 4, v_r_903_);
lean_ctor_set(v___x_963_, 3, v___x_961_);
lean_ctor_set(v___x_963_, 2, v_v_901_);
lean_ctor_set(v___x_963_, 1, v_k_900_);
lean_ctor_set(v___x_963_, 0, v___x_958_);
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_958_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_k_900_);
lean_ctor_set(v_reuseFailAlloc_967_, 2, v_v_901_);
lean_ctor_set(v_reuseFailAlloc_967_, 3, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_967_, 4, v_r_903_);
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
v_l_981_ = lean_ctor_get(v_impl_896_, 3);
lean_inc(v_l_981_);
if (lean_obj_tag(v_l_981_) == 0)
{
lean_object* v_r_982_; lean_object* v_k_983_; lean_object* v_v_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1007_; 
v_r_982_ = lean_ctor_get(v_impl_896_, 4);
v_k_983_ = lean_ctor_get(v_impl_896_, 1);
v_v_984_ = lean_ctor_get(v_impl_896_, 2);
v_isSharedCheck_1007_ = !lean_is_exclusive(v_impl_896_);
if (v_isSharedCheck_1007_ == 0)
{
lean_object* v_unused_1008_; lean_object* v_unused_1009_; 
v_unused_1008_ = lean_ctor_get(v_impl_896_, 3);
lean_dec(v_unused_1008_);
v_unused_1009_ = lean_ctor_get(v_impl_896_, 0);
lean_dec(v_unused_1009_);
v___x_986_ = v_impl_896_;
v_isShared_987_ = v_isSharedCheck_1007_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_r_982_);
lean_inc(v_v_984_);
lean_inc(v_k_983_);
lean_dec(v_impl_896_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1007_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v_k_988_; lean_object* v_v_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1003_; 
v_k_988_ = lean_ctor_get(v_l_981_, 1);
v_v_989_ = lean_ctor_get(v_l_981_, 2);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_l_981_);
if (v_isSharedCheck_1003_ == 0)
{
lean_object* v_unused_1004_; lean_object* v_unused_1005_; lean_object* v_unused_1006_; 
v_unused_1004_ = lean_ctor_get(v_l_981_, 4);
lean_dec(v_unused_1004_);
v_unused_1005_ = lean_ctor_get(v_l_981_, 3);
lean_dec(v_unused_1005_);
v_unused_1006_ = lean_ctor_get(v_l_981_, 0);
lean_dec(v_unused_1006_);
v___x_991_ = v_l_981_;
v_isShared_992_ = v_isSharedCheck_1003_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_v_989_);
lean_inc(v_k_988_);
lean_dec(v_l_981_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1003_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_993_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_982_, 2);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 4, v_r_982_);
lean_ctor_set(v___x_991_, 3, v_r_982_);
lean_ctor_set(v___x_991_, 2, v_v_888_);
lean_ctor_set(v___x_991_, 1, v_k_887_);
lean_ctor_set(v___x_991_, 0, v___x_897_);
v___x_995_ = v___x_991_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_897_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_1002_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_1002_, 3, v_r_982_);
lean_ctor_set(v_reuseFailAlloc_1002_, 4, v_r_982_);
v___x_995_ = v_reuseFailAlloc_1002_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_997_; 
lean_inc(v_r_982_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 3, v_r_982_);
lean_ctor_set(v___x_986_, 0, v___x_897_);
v___x_997_ = v___x_986_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_897_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_k_983_);
lean_ctor_set(v_reuseFailAlloc_1001_, 2, v_v_984_);
lean_ctor_set(v_reuseFailAlloc_1001_, 3, v_r_982_);
lean_ctor_set(v_reuseFailAlloc_1001_, 4, v_r_982_);
v___x_997_ = v_reuseFailAlloc_1001_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_999_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 4, v___x_997_);
lean_ctor_set(v___x_892_, 3, v___x_995_);
lean_ctor_set(v___x_892_, 2, v_v_989_);
lean_ctor_set(v___x_892_, 1, v_k_988_);
lean_ctor_set(v___x_892_, 0, v___x_993_);
v___x_999_ = v___x_892_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_k_988_);
lean_ctor_set(v_reuseFailAlloc_1000_, 2, v_v_989_);
lean_ctor_set(v_reuseFailAlloc_1000_, 3, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1000_, 4, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
}
else
{
lean_object* v_r_1010_; 
v_r_1010_ = lean_ctor_get(v_impl_896_, 4);
lean_inc(v_r_1010_);
if (lean_obj_tag(v_r_1010_) == 0)
{
lean_object* v_k_1011_; lean_object* v_v_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1023_; 
v_k_1011_ = lean_ctor_get(v_impl_896_, 1);
v_v_1012_ = lean_ctor_get(v_impl_896_, 2);
v_isSharedCheck_1023_ = !lean_is_exclusive(v_impl_896_);
if (v_isSharedCheck_1023_ == 0)
{
lean_object* v_unused_1024_; lean_object* v_unused_1025_; lean_object* v_unused_1026_; 
v_unused_1024_ = lean_ctor_get(v_impl_896_, 4);
lean_dec(v_unused_1024_);
v_unused_1025_ = lean_ctor_get(v_impl_896_, 3);
lean_dec(v_unused_1025_);
v_unused_1026_ = lean_ctor_get(v_impl_896_, 0);
lean_dec(v_unused_1026_);
v___x_1014_ = v_impl_896_;
v_isShared_1015_ = v_isSharedCheck_1023_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_v_1012_);
lean_inc(v_k_1011_);
lean_dec(v_impl_896_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1023_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; lean_object* v___x_1018_; 
v___x_1016_ = lean_unsigned_to_nat(3u);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 4, v_l_981_);
lean_ctor_set(v___x_1014_, 2, v_v_888_);
lean_ctor_set(v___x_1014_, 1, v_k_887_);
lean_ctor_set(v___x_1014_, 0, v___x_897_);
v___x_1018_ = v___x_1014_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_897_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_1022_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_1022_, 3, v_l_981_);
lean_ctor_set(v_reuseFailAlloc_1022_, 4, v_l_981_);
v___x_1018_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
lean_object* v___x_1020_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 4, v_r_1010_);
lean_ctor_set(v___x_892_, 3, v___x_1018_);
lean_ctor_set(v___x_892_, 2, v_v_1012_);
lean_ctor_set(v___x_892_, 1, v_k_1011_);
lean_ctor_set(v___x_892_, 0, v___x_1016_);
v___x_1020_ = v___x_892_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1016_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_k_1011_);
lean_ctor_set(v_reuseFailAlloc_1021_, 2, v_v_1012_);
lean_ctor_set(v_reuseFailAlloc_1021_, 3, v___x_1018_);
lean_ctor_set(v_reuseFailAlloc_1021_, 4, v_r_1010_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
else
{
lean_object* v___x_1027_; lean_object* v___x_1029_; 
v___x_1027_ = lean_unsigned_to_nat(2u);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 4, v_impl_896_);
lean_ctor_set(v___x_892_, 3, v_r_1010_);
lean_ctor_set(v___x_892_, 0, v___x_1027_);
v___x_1029_ = v___x_892_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1027_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_1030_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_1030_, 3, v_r_1010_);
lean_ctor_set(v_reuseFailAlloc_1030_, 4, v_impl_896_);
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
else
{
lean_object* v___x_1032_; 
lean_dec(v_v_888_);
lean_dec(v_k_887_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 2, v_v_884_);
lean_ctor_set(v___x_892_, 1, v_k_883_);
v___x_1032_ = v___x_892_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_size_886_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_k_883_);
lean_ctor_set(v_reuseFailAlloc_1033_, 2, v_v_884_);
lean_ctor_set(v_reuseFailAlloc_1033_, 3, v_l_889_);
lean_ctor_set(v_reuseFailAlloc_1033_, 4, v_r_890_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
else
{
lean_object* v_impl_1034_; lean_object* v___x_1035_; 
lean_dec(v_size_886_);
v_impl_1034_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_883_, v_v_884_, v_l_889_);
v___x_1035_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_890_) == 0)
{
lean_object* v_size_1036_; lean_object* v_size_1037_; lean_object* v_k_1038_; lean_object* v_v_1039_; lean_object* v_l_1040_; lean_object* v_r_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; 
v_size_1036_ = lean_ctor_get(v_r_890_, 0);
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
v___x_1045_ = lean_nat_add(v___x_1035_, v_size_1037_);
lean_dec(v_size_1037_);
v___x_1046_ = lean_nat_add(v___x_1045_, v_size_1036_);
lean_dec(v___x_1045_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 3, v_impl_1034_);
lean_ctor_set(v___x_892_, 0, v___x_1046_);
v___x_1048_ = v___x_892_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_1049_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_1049_, 3, v_impl_1034_);
lean_ctor_set(v_reuseFailAlloc_1049_, 4, v_r_890_);
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
lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1115_; 
v_isSharedCheck_1115_ = !lean_is_exclusive(v_impl_1034_);
if (v_isSharedCheck_1115_ == 0)
{
lean_object* v_unused_1116_; lean_object* v_unused_1117_; lean_object* v_unused_1118_; lean_object* v_unused_1119_; lean_object* v_unused_1120_; 
v_unused_1116_ = lean_ctor_get(v_impl_1034_, 4);
lean_dec(v_unused_1116_);
v_unused_1117_ = lean_ctor_get(v_impl_1034_, 3);
lean_dec(v_unused_1117_);
v_unused_1118_ = lean_ctor_get(v_impl_1034_, 2);
lean_dec(v_unused_1118_);
v_unused_1119_ = lean_ctor_get(v_impl_1034_, 1);
lean_dec(v_unused_1119_);
v_unused_1120_ = lean_ctor_get(v_impl_1034_, 0);
lean_dec(v_unused_1120_);
v___x_1051_ = v_impl_1034_;
v_isShared_1052_ = v_isSharedCheck_1115_;
goto v_resetjp_1050_;
}
else
{
lean_dec(v_impl_1034_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1115_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v_size_1053_; lean_object* v_size_1054_; lean_object* v_k_1055_; lean_object* v_v_1056_; lean_object* v_l_1057_; lean_object* v_r_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v_size_1053_ = lean_ctor_get(v_l_1040_, 0);
v_size_1054_ = lean_ctor_get(v_r_1041_, 0);
v_k_1055_ = lean_ctor_get(v_r_1041_, 1);
v_v_1056_ = lean_ctor_get(v_r_1041_, 2);
v_l_1057_ = lean_ctor_get(v_r_1041_, 3);
v_r_1058_ = lean_ctor_get(v_r_1041_, 4);
v___x_1059_ = lean_unsigned_to_nat(2u);
v___x_1060_ = lean_nat_mul(v___x_1059_, v_size_1053_);
v___x_1061_ = lean_nat_dec_lt(v_size_1054_, v___x_1060_);
lean_dec(v___x_1060_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1090_; 
lean_inc(v_r_1058_);
lean_inc(v_l_1057_);
lean_inc(v_v_1056_);
lean_inc(v_k_1055_);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_r_1041_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; lean_object* v_unused_1092_; lean_object* v_unused_1093_; lean_object* v_unused_1094_; lean_object* v_unused_1095_; 
v_unused_1091_ = lean_ctor_get(v_r_1041_, 4);
lean_dec(v_unused_1091_);
v_unused_1092_ = lean_ctor_get(v_r_1041_, 3);
lean_dec(v_unused_1092_);
v_unused_1093_ = lean_ctor_get(v_r_1041_, 2);
lean_dec(v_unused_1093_);
v_unused_1094_ = lean_ctor_get(v_r_1041_, 1);
lean_dec(v_unused_1094_);
v_unused_1095_ = lean_ctor_get(v_r_1041_, 0);
lean_dec(v_unused_1095_);
v___x_1063_ = v_r_1041_;
v_isShared_1064_ = v_isSharedCheck_1090_;
goto v_resetjp_1062_;
}
else
{
lean_dec(v_r_1041_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1090_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___x_1078_; lean_object* v___y_1080_; 
v___x_1065_ = lean_nat_add(v___x_1035_, v_size_1037_);
lean_dec(v_size_1037_);
v___x_1066_ = lean_nat_add(v___x_1065_, v_size_1036_);
lean_dec(v___x_1065_);
v___x_1078_ = lean_nat_add(v___x_1035_, v_size_1053_);
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
v___jp_1067_:
{
lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1071_ = lean_nat_add(v___y_1068_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec(v___y_1068_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 4, v_r_890_);
lean_ctor_set(v___x_1063_, 3, v_r_1058_);
lean_ctor_set(v___x_1063_, 2, v_v_888_);
lean_ctor_set(v___x_1063_, 1, v_k_887_);
lean_ctor_set(v___x_1063_, 0, v___x_1071_);
v___x_1073_ = v___x_1063_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1071_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_1077_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_1077_, 3, v_r_1058_);
lean_ctor_set(v_reuseFailAlloc_1077_, 4, v_r_890_);
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
lean_ctor_set(v___x_1051_, 2, v_v_1056_);
lean_ctor_set(v___x_1051_, 1, v_k_1055_);
lean_ctor_set(v___x_1051_, 0, v___x_1066_);
v___x_1075_ = v___x_1051_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v_k_1055_);
lean_ctor_set(v_reuseFailAlloc_1076_, 2, v_v_1056_);
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
v___jp_1079_:
{
lean_object* v___x_1081_; lean_object* v___x_1083_; 
v___x_1081_ = lean_nat_add(v___x_1078_, v___y_1080_);
lean_dec(v___y_1080_);
lean_dec(v___x_1078_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 4, v_l_1057_);
lean_ctor_set(v___x_892_, 3, v_l_1040_);
lean_ctor_set(v___x_892_, 2, v_v_1039_);
lean_ctor_set(v___x_892_, 1, v_k_1038_);
lean_ctor_set(v___x_892_, 0, v___x_1081_);
v___x_1083_ = v___x_892_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v_k_1038_);
lean_ctor_set(v_reuseFailAlloc_1087_, 2, v_v_1039_);
lean_ctor_set(v_reuseFailAlloc_1087_, 3, v_l_1040_);
lean_ctor_set(v_reuseFailAlloc_1087_, 4, v_l_1057_);
v___x_1083_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1084_; 
v___x_1084_ = lean_nat_add(v___x_1035_, v_size_1036_);
if (lean_obj_tag(v_r_1058_) == 0)
{
lean_object* v_size_1085_; 
v_size_1085_ = lean_ctor_get(v_r_1058_, 0);
lean_inc(v_size_1085_);
v___y_1068_ = v___x_1084_;
v___y_1069_ = v___x_1083_;
v___y_1070_ = v_size_1085_;
goto v___jp_1067_;
}
else
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_unsigned_to_nat(0u);
v___y_1068_ = v___x_1084_;
v___y_1069_ = v___x_1083_;
v___y_1070_ = v___x_1086_;
goto v___jp_1067_;
}
}
}
}
}
else
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1101_; 
lean_del_object(v___x_892_);
v___x_1096_ = lean_nat_add(v___x_1035_, v_size_1037_);
lean_dec(v_size_1037_);
v___x_1097_ = lean_nat_add(v___x_1096_, v_size_1036_);
lean_dec(v___x_1096_);
v___x_1098_ = lean_nat_add(v___x_1035_, v_size_1036_);
v___x_1099_ = lean_nat_add(v___x_1098_, v_size_1054_);
lean_dec(v___x_1098_);
lean_inc_ref(v_r_890_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 4, v_r_890_);
lean_ctor_set(v___x_1051_, 3, v_r_1041_);
lean_ctor_set(v___x_1051_, 2, v_v_888_);
lean_ctor_set(v___x_1051_, 1, v_k_887_);
lean_ctor_set(v___x_1051_, 0, v___x_1099_);
v___x_1101_ = v___x_1051_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_1114_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_1114_, 3, v_r_1041_);
lean_ctor_set(v_reuseFailAlloc_1114_, 4, v_r_890_);
v___x_1101_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
v_isSharedCheck_1108_ = !lean_is_exclusive(v_r_890_);
if (v_isSharedCheck_1108_ == 0)
{
lean_object* v_unused_1109_; lean_object* v_unused_1110_; lean_object* v_unused_1111_; lean_object* v_unused_1112_; lean_object* v_unused_1113_; 
v_unused_1109_ = lean_ctor_get(v_r_890_, 4);
lean_dec(v_unused_1109_);
v_unused_1110_ = lean_ctor_get(v_r_890_, 3);
lean_dec(v_unused_1110_);
v_unused_1111_ = lean_ctor_get(v_r_890_, 2);
lean_dec(v_unused_1111_);
v_unused_1112_ = lean_ctor_get(v_r_890_, 1);
lean_dec(v_unused_1112_);
v_unused_1113_ = lean_ctor_get(v_r_890_, 0);
lean_dec(v_unused_1113_);
v___x_1103_ = v_r_890_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_dec(v_r_890_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 4, v___x_1101_);
lean_ctor_set(v___x_1103_, 3, v_l_1040_);
lean_ctor_set(v___x_1103_, 2, v_v_1039_);
lean_ctor_set(v___x_1103_, 1, v_k_1038_);
lean_ctor_set(v___x_1103_, 0, v___x_1097_);
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1097_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_k_1038_);
lean_ctor_set(v_reuseFailAlloc_1107_, 2, v_v_1039_);
lean_ctor_set(v_reuseFailAlloc_1107_, 3, v_l_1040_);
lean_ctor_set(v_reuseFailAlloc_1107_, 4, v___x_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1121_; 
v_l_1121_ = lean_ctor_get(v_impl_1034_, 3);
lean_inc(v_l_1121_);
if (lean_obj_tag(v_l_1121_) == 0)
{
lean_object* v_r_1122_; lean_object* v_k_1123_; lean_object* v_v_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1135_; 
v_r_1122_ = lean_ctor_get(v_impl_1034_, 4);
v_k_1123_ = lean_ctor_get(v_impl_1034_, 1);
v_v_1124_ = lean_ctor_get(v_impl_1034_, 2);
v_isSharedCheck_1135_ = !lean_is_exclusive(v_impl_1034_);
if (v_isSharedCheck_1135_ == 0)
{
lean_object* v_unused_1136_; lean_object* v_unused_1137_; 
v_unused_1136_ = lean_ctor_get(v_impl_1034_, 3);
lean_dec(v_unused_1136_);
v_unused_1137_ = lean_ctor_get(v_impl_1034_, 0);
lean_dec(v_unused_1137_);
v___x_1126_ = v_impl_1034_;
v_isShared_1127_ = v_isSharedCheck_1135_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_r_1122_);
lean_inc(v_v_1124_);
lean_inc(v_k_1123_);
lean_dec(v_impl_1034_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1135_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1128_; lean_object* v___x_1130_; 
v___x_1128_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1122_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 3, v_r_1122_);
lean_ctor_set(v___x_1126_, 2, v_v_888_);
lean_ctor_set(v___x_1126_, 1, v_k_887_);
lean_ctor_set(v___x_1126_, 0, v___x_1035_);
v___x_1130_ = v___x_1126_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_1134_, 3, v_r_1122_);
lean_ctor_set(v_reuseFailAlloc_1134_, 4, v_r_1122_);
v___x_1130_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1132_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 4, v___x_1130_);
lean_ctor_set(v___x_892_, 3, v_l_1121_);
lean_ctor_set(v___x_892_, 2, v_v_1124_);
lean_ctor_set(v___x_892_, 1, v_k_1123_);
lean_ctor_set(v___x_892_, 0, v___x_1128_);
v___x_1132_ = v___x_892_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1128_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_k_1123_);
lean_ctor_set(v_reuseFailAlloc_1133_, 2, v_v_1124_);
lean_ctor_set(v_reuseFailAlloc_1133_, 3, v_l_1121_);
lean_ctor_set(v_reuseFailAlloc_1133_, 4, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
else
{
lean_object* v_r_1138_; 
v_r_1138_ = lean_ctor_get(v_impl_1034_, 4);
lean_inc(v_r_1138_);
if (lean_obj_tag(v_r_1138_) == 0)
{
lean_object* v_k_1139_; lean_object* v_v_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1163_; 
v_k_1139_ = lean_ctor_get(v_impl_1034_, 1);
v_v_1140_ = lean_ctor_get(v_impl_1034_, 2);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_impl_1034_);
if (v_isSharedCheck_1163_ == 0)
{
lean_object* v_unused_1164_; lean_object* v_unused_1165_; lean_object* v_unused_1166_; 
v_unused_1164_ = lean_ctor_get(v_impl_1034_, 4);
lean_dec(v_unused_1164_);
v_unused_1165_ = lean_ctor_get(v_impl_1034_, 3);
lean_dec(v_unused_1165_);
v_unused_1166_ = lean_ctor_get(v_impl_1034_, 0);
lean_dec(v_unused_1166_);
v___x_1142_ = v_impl_1034_;
v_isShared_1143_ = v_isSharedCheck_1163_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_v_1140_);
lean_inc(v_k_1139_);
lean_dec(v_impl_1034_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1163_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v_k_1144_; lean_object* v_v_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1159_; 
v_k_1144_ = lean_ctor_get(v_r_1138_, 1);
v_v_1145_ = lean_ctor_get(v_r_1138_, 2);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_r_1138_);
if (v_isSharedCheck_1159_ == 0)
{
lean_object* v_unused_1160_; lean_object* v_unused_1161_; lean_object* v_unused_1162_; 
v_unused_1160_ = lean_ctor_get(v_r_1138_, 4);
lean_dec(v_unused_1160_);
v_unused_1161_ = lean_ctor_get(v_r_1138_, 3);
lean_dec(v_unused_1161_);
v_unused_1162_ = lean_ctor_get(v_r_1138_, 0);
lean_dec(v_unused_1162_);
v___x_1147_ = v_r_1138_;
v_isShared_1148_ = v_isSharedCheck_1159_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_v_1145_);
lean_inc(v_k_1144_);
lean_dec(v_r_1138_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1159_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1149_ = lean_unsigned_to_nat(3u);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 4, v_l_1121_);
lean_ctor_set(v___x_1147_, 3, v_l_1121_);
lean_ctor_set(v___x_1147_, 2, v_v_1140_);
lean_ctor_set(v___x_1147_, 1, v_k_1139_);
lean_ctor_set(v___x_1147_, 0, v___x_1035_);
v___x_1151_ = v___x_1147_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_k_1139_);
lean_ctor_set(v_reuseFailAlloc_1158_, 2, v_v_1140_);
lean_ctor_set(v_reuseFailAlloc_1158_, 3, v_l_1121_);
lean_ctor_set(v_reuseFailAlloc_1158_, 4, v_l_1121_);
v___x_1151_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1153_; 
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 4, v_l_1121_);
lean_ctor_set(v___x_1142_, 2, v_v_888_);
lean_ctor_set(v___x_1142_, 1, v_k_887_);
lean_ctor_set(v___x_1142_, 0, v___x_1035_);
v___x_1153_ = v___x_1142_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_1157_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_1157_, 3, v_l_1121_);
lean_ctor_set(v_reuseFailAlloc_1157_, 4, v_l_1121_);
v___x_1153_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1155_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 4, v___x_1153_);
lean_ctor_set(v___x_892_, 3, v___x_1151_);
lean_ctor_set(v___x_892_, 2, v_v_1145_);
lean_ctor_set(v___x_892_, 1, v_k_1144_);
lean_ctor_set(v___x_892_, 0, v___x_1149_);
v___x_1155_ = v___x_892_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_k_1144_);
lean_ctor_set(v_reuseFailAlloc_1156_, 2, v_v_1145_);
lean_ctor_set(v_reuseFailAlloc_1156_, 3, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1156_, 4, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
}
else
{
lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1167_ = lean_unsigned_to_nat(2u);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 4, v_r_1138_);
lean_ctor_set(v___x_892_, 3, v_impl_1034_);
lean_ctor_set(v___x_892_, 0, v___x_1167_);
v___x_1169_ = v___x_892_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1167_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_k_887_);
lean_ctor_set(v_reuseFailAlloc_1170_, 2, v_v_888_);
lean_ctor_set(v_reuseFailAlloc_1170_, 3, v_impl_1034_);
lean_ctor_set(v_reuseFailAlloc_1170_, 4, v_r_1138_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = lean_unsigned_to_nat(1u);
v___x_1173_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
lean_ctor_set(v___x_1173_, 1, v_k_883_);
lean_ctor_set(v___x_1173_, 2, v_v_884_);
lean_ctor_set(v___x_1173_, 3, v_t_885_);
lean_ctor_set(v___x_1173_, 4, v_t_885_);
return v___x_1173_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(lean_object* v_as_x27_1174_, lean_object* v_b_1175_){
_start:
{
if (lean_obj_tag(v_as_x27_1174_) == 0)
{
return v_b_1175_;
}
else
{
lean_object* v_head_1176_; lean_object* v_tail_1177_; lean_object* v_fst_1178_; lean_object* v_snd_1179_; lean_object* v_r_1180_; 
v_head_1176_ = lean_ctor_get(v_as_x27_1174_, 0);
v_tail_1177_ = lean_ctor_get(v_as_x27_1174_, 1);
v_fst_1178_ = lean_ctor_get(v_head_1176_, 0);
v_snd_1179_ = lean_ctor_get(v_head_1176_, 1);
lean_inc(v_snd_1179_);
lean_inc(v_fst_1178_);
v_r_1180_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_fst_1178_, v_snd_1179_, v_b_1175_);
v_as_x27_1174_ = v_tail_1177_;
v_b_1175_ = v_r_1180_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg___boxed(lean_object* v_as_x27_1182_, lean_object* v_b_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_as_x27_1182_, v_b_1183_);
lean_dec(v_as_x27_1182_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mkObj(lean_object* v_o_1185_){
_start:
{
lean_object* v_r_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v_r_1186_ = lean_box(1);
v___x_1187_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_o_1185_, v_r_1186_);
v___x_1188_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mkObj___boxed(lean_object* v_o_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lean_Json_mkObj(v_o_1189_);
lean_dec(v_o_1189_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0(lean_object* v_00_u03b2_1191_, lean_object* v_k_1192_, lean_object* v_v_1193_, lean_object* v_t_1194_, lean_object* v_hl_1195_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_1192_, v_v_1193_, v_t_1194_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1(lean_object* v_as_1197_, lean_object* v_as_x27_1198_, lean_object* v_b_1199_, lean_object* v_a_1200_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_as_x27_1198_, v_b_1199_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___boxed(lean_object* v_as_1202_, lean_object* v_as_x27_1203_, lean_object* v_b_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1(v_as_1202_, v_as_x27_1203_, v_b_1204_, v_a_1205_);
lean_dec(v_as_x27_1203_);
lean_dec(v_as_1202_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeNat___lam__0(lean_object* v_n_1207_){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = l_Lean_JsonNumber_fromNat(v_n_1207_);
v___x_1209_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeInt___lam__0(lean_object* v_n_1212_){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = l_Lean_JsonNumber_fromInt(v_n_1212_);
v___x_1214_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeString___lam__0(lean_object* v_s_1217_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1218_, 0, v_s_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeBool___lam__0(uint8_t v_b_1221_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1222_, 0, v_b_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeBool___lam__0___boxed(lean_object* v_b_1223_){
_start:
{
uint8_t v_b_boxed_1224_; lean_object* v_res_1225_; 
v_b_boxed_1224_ = lean_unbox(v_b_1223_);
v_res_1225_ = l_Lean_Json_instCoeBool___lam__0(v_b_boxed_1224_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instOfNat(lean_object* v_n_1228_){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = l_Lean_JsonNumber_fromNat(v_n_1228_);
v___x_1230_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT uint8_t l_Lean_Json_isNull(lean_object* v_x_1231_){
_start:
{
if (lean_obj_tag(v_x_1231_) == 0)
{
uint8_t v___x_1232_; 
v___x_1232_ = 1;
return v___x_1232_;
}
else
{
uint8_t v___x_1233_; 
v___x_1233_ = 0;
return v___x_1233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_isNull___boxed(lean_object* v_x_1234_){
_start:
{
uint8_t v_res_1235_; lean_object* v_r_1236_; 
v_res_1235_ = l_Lean_Json_isNull(v_x_1234_);
lean_dec(v_x_1234_);
v_r_1236_ = lean_box(v_res_1235_);
return v_r_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObj_x3f(lean_object* v_x_1240_){
_start:
{
if (lean_obj_tag(v_x_1240_) == 5)
{
lean_object* v_kvPairs_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
v_kvPairs_1241_ = lean_ctor_get(v_x_1240_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v_x_1240_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v_x_1240_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_kvPairs_1241_);
lean_dec(v_x_1240_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
lean_ctor_set_tag(v___x_1243_, 1);
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_kvPairs_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
else
{
lean_object* v___x_1249_; 
lean_dec(v_x_1240_);
v___x_1249_ = ((lean_object*)(l_Lean_Json_getObj_x3f___closed__1));
return v___x_1249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getArr_x3f(lean_object* v_x_1253_){
_start:
{
if (lean_obj_tag(v_x_1253_) == 4)
{
lean_object* v_elems_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
v_elems_1254_ = lean_ctor_get(v_x_1253_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v_x_1253_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v_x_1253_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_elems_1254_);
lean_dec(v_x_1253_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
lean_ctor_set_tag(v___x_1256_, 1);
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_elems_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
else
{
lean_object* v___x_1262_; 
lean_dec(v_x_1253_);
v___x_1262_ = ((lean_object*)(l_Lean_Json_getArr_x3f___closed__1));
return v___x_1262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getStr_x3f(lean_object* v_x_1266_){
_start:
{
if (lean_obj_tag(v_x_1266_) == 3)
{
lean_object* v_s_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
v_s_1267_ = lean_ctor_get(v_x_1266_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_x_1266_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v_x_1266_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_s_1267_);
lean_dec(v_x_1266_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
lean_ctor_set_tag(v___x_1269_, 1);
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_s_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
else
{
lean_object* v___x_1275_; 
lean_dec(v_x_1266_);
v___x_1275_ = ((lean_object*)(l_Lean_Json_getStr_x3f___closed__1));
return v___x_1275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getNat_x3f(lean_object* v_x_1279_){
_start:
{
if (lean_obj_tag(v_x_1279_) == 2)
{
lean_object* v_n_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1296_; 
v_n_1282_ = lean_ctor_get(v_x_1279_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v_x_1279_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1284_ = v_x_1279_;
v_isShared_1285_ = v_isSharedCheck_1296_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_n_1282_);
lean_dec(v_x_1279_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1296_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v_mantissa_1286_; lean_object* v_exponent_1287_; lean_object* v_natZero_1288_; lean_object* v_intZero_1289_; uint8_t v_isNeg_1290_; 
v_mantissa_1286_ = lean_ctor_get(v_n_1282_, 0);
lean_inc(v_mantissa_1286_);
v_exponent_1287_ = lean_ctor_get(v_n_1282_, 1);
lean_inc(v_exponent_1287_);
lean_dec_ref(v_n_1282_);
v_natZero_1288_ = lean_unsigned_to_nat(0u);
v_intZero_1289_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v_isNeg_1290_ = lean_int_dec_lt(v_mantissa_1286_, v_intZero_1289_);
if (v_isNeg_1290_ == 0)
{
uint8_t v___x_1291_; 
v___x_1291_ = lean_nat_dec_eq(v_exponent_1287_, v_natZero_1288_);
lean_dec(v_exponent_1287_);
if (v___x_1291_ == 0)
{
lean_dec(v_mantissa_1286_);
lean_del_object(v___x_1284_);
goto v___jp_1280_;
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; 
v_a_1292_ = lean_nat_abs(v_mantissa_1286_);
lean_dec(v_mantissa_1286_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set_tag(v___x_1284_, 1);
lean_ctor_set(v___x_1284_, 0, v_a_1292_);
v___x_1294_ = v___x_1284_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1292_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
else
{
lean_dec(v_exponent_1287_);
lean_dec(v_mantissa_1286_);
lean_del_object(v___x_1284_);
goto v___jp_1280_;
}
}
}
else
{
lean_dec(v_x_1279_);
goto v___jp_1280_;
}
v___jp_1280_:
{
lean_object* v___x_1281_; 
v___x_1281_ = ((lean_object*)(l_Lean_Json_getNat_x3f___closed__1));
return v___x_1281_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getInt_x3f(lean_object* v_x_1300_){
_start:
{
if (lean_obj_tag(v_x_1300_) == 2)
{
lean_object* v_n_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1314_; 
v_n_1303_ = lean_ctor_get(v_x_1300_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v_x_1300_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1305_ = v_x_1300_;
v_isShared_1306_ = v_isSharedCheck_1314_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_n_1303_);
lean_dec(v_x_1300_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1314_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v_mantissa_1307_; lean_object* v_exponent_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
v_mantissa_1307_ = lean_ctor_get(v_n_1303_, 0);
lean_inc(v_mantissa_1307_);
v_exponent_1308_ = lean_ctor_get(v_n_1303_, 1);
lean_inc(v_exponent_1308_);
lean_dec_ref(v_n_1303_);
v___x_1309_ = lean_unsigned_to_nat(0u);
v___x_1310_ = lean_nat_dec_eq(v_exponent_1308_, v___x_1309_);
lean_dec(v_exponent_1308_);
if (v___x_1310_ == 0)
{
lean_dec(v_mantissa_1307_);
lean_del_object(v___x_1305_);
goto v___jp_1301_;
}
else
{
lean_object* v___x_1312_; 
if (v_isShared_1306_ == 0)
{
lean_ctor_set_tag(v___x_1305_, 1);
lean_ctor_set(v___x_1305_, 0, v_mantissa_1307_);
v___x_1312_ = v___x_1305_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_mantissa_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
else
{
lean_dec(v_x_1300_);
goto v___jp_1301_;
}
v___jp_1301_:
{
lean_object* v___x_1302_; 
v___x_1302_ = ((lean_object*)(l_Lean_Json_getInt_x3f___closed__1));
return v___x_1302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getBool_x3f(lean_object* v_x_1318_){
_start:
{
if (lean_obj_tag(v_x_1318_) == 1)
{
uint8_t v_b_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v_b_1319_ = lean_ctor_get_uint8(v_x_1318_, 0);
v___x_1320_ = lean_box(v_b_1319_);
v___x_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
return v___x_1321_;
}
else
{
lean_object* v___x_1322_; 
v___x_1322_ = ((lean_object*)(l_Lean_Json_getBool_x3f___closed__1));
return v___x_1322_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getBool_x3f___boxed(lean_object* v_x_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_Json_getBool_x3f(v_x_1323_);
lean_dec(v_x_1323_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getNum_x3f(lean_object* v_x_1328_){
_start:
{
if (lean_obj_tag(v_x_1328_) == 2)
{
lean_object* v_n_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
v_n_1329_ = lean_ctor_get(v_x_1328_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v_x_1328_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v_x_1328_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_n_1329_);
lean_dec(v_x_1328_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
lean_ctor_set_tag(v___x_1331_, 1);
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_n_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
else
{
lean_object* v___x_1337_; 
lean_dec(v_x_1328_);
v___x_1337_ = ((lean_object*)(l_Lean_Json_getNum_x3f___closed__1));
return v___x_1337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjVal_x3f(lean_object* v_x_1341_, lean_object* v_x_1342_){
_start:
{
if (lean_obj_tag(v_x_1341_) == 5)
{
lean_object* v_kvPairs_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1361_; 
v_kvPairs_1343_ = lean_ctor_get(v_x_1341_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_x_1341_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1345_ = v_x_1341_;
v_isShared_1346_ = v_isSharedCheck_1361_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_kvPairs_1343_);
lean_dec(v_x_1341_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1361_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_kvPairs_1343_, v_x_1342_);
lean_dec(v_kvPairs_1343_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1351_; 
v___x_1348_ = ((lean_object*)(l_Lean_Json_getObjVal_x3f___closed__0));
v___x_1349_ = lean_string_append(v___x_1348_, v_x_1342_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set_tag(v___x_1345_, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1349_);
v___x_1351_ = v___x_1345_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1349_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
else
{
lean_object* v_val_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
lean_del_object(v___x_1345_);
v_val_1353_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1347_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_val_1353_);
lean_dec(v___x_1347_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_val_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
else
{
lean_object* v___x_1362_; 
lean_dec(v_x_1341_);
v___x_1362_ = ((lean_object*)(l_Lean_Json_getObjVal_x3f___closed__1));
return v___x_1362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjVal_x3f___boxed(lean_object* v_x_1363_, lean_object* v_x_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_Json_getObjVal_x3f(v_x_1363_, v_x_1364_);
lean_dec_ref(v_x_1364_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getArrVal_x3f(lean_object* v_x_1369_, lean_object* v_x_1370_){
_start:
{
if (lean_obj_tag(v_x_1369_) == 4)
{
lean_object* v_elems_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1387_; 
v_elems_1371_ = lean_ctor_get(v_x_1369_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v_x_1369_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1373_ = v_x_1369_;
v_isShared_1374_ = v_isSharedCheck_1387_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_elems_1371_);
lean_dec(v_x_1369_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1387_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; uint8_t v___x_1376_; 
v___x_1375_ = lean_array_get_size(v_elems_1371_);
v___x_1376_ = lean_nat_dec_lt(v_x_1370_, v___x_1375_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1381_; 
lean_dec_ref(v_elems_1371_);
v___x_1377_ = ((lean_object*)(l_Lean_Json_getArrVal_x3f___closed__0));
v___x_1378_ = l_Nat_reprFast(v_x_1370_);
v___x_1379_ = lean_string_append(v___x_1377_, v___x_1378_);
lean_dec_ref(v___x_1378_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set_tag(v___x_1373_, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1379_);
v___x_1381_ = v___x_1373_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
else
{
lean_object* v___x_1383_; lean_object* v___x_1385_; 
v___x_1383_ = lean_array_fget(v_elems_1371_, v_x_1370_);
lean_dec(v_x_1370_);
lean_dec_ref(v_elems_1371_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set_tag(v___x_1373_, 1);
lean_ctor_set(v___x_1373_, 0, v___x_1383_);
v___x_1385_ = v___x_1373_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1383_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
else
{
lean_object* v___x_1388_; 
lean_dec(v_x_1370_);
lean_dec(v_x_1369_);
v___x_1388_ = ((lean_object*)(l_Lean_Json_getArrVal_x3f___closed__1));
return v___x_1388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValD(lean_object* v_j_1389_, lean_object* v_k_1390_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = l_Lean_Json_getObjVal_x3f(v_j_1389_, v_k_1390_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v___x_1392_; 
lean_dec_ref(v___x_1391_);
v___x_1392_ = lean_box(0);
return v___x_1392_;
}
else
{
lean_object* v_a_1393_; 
v_a_1393_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1393_);
lean_dec_ref(v___x_1391_);
return v_a_1393_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValD___boxed(lean_object* v_j_1394_, lean_object* v_k_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_Json_getObjValD(v_j_1394_, v_k_1395_);
lean_dec_ref(v_k_1395_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Json_setObjVal_x21_spec__1(lean_object* v_msg_1397_){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = lean_box(0);
v___x_1399_ = lean_panic_fn_borrowed(v___x_1398_, v_msg_1397_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(lean_object* v_msg_1400_){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = lean_box(1);
v___x_1402_ = lean_panic_fn_borrowed(v___x_1401_, v_msg_1400_);
return v___x_1402_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1406_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2));
v___x_1407_ = lean_unsigned_to_nat(35u);
v___x_1408_ = lean_unsigned_to_nat(276u);
v___x_1409_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1));
v___x_1410_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1411_ = l_mkPanicMessageWithDecl(v___x_1410_, v___x_1409_, v___x_1408_, v___x_1407_, v___x_1406_);
return v___x_1411_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1412_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2));
v___x_1413_ = lean_unsigned_to_nat(21u);
v___x_1414_ = lean_unsigned_to_nat(277u);
v___x_1415_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1));
v___x_1416_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1417_ = l_mkPanicMessageWithDecl(v___x_1416_, v___x_1415_, v___x_1414_, v___x_1413_, v___x_1412_);
return v___x_1417_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1420_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6));
v___x_1421_ = lean_unsigned_to_nat(35u);
v___x_1422_ = lean_unsigned_to_nat(182u);
v___x_1423_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5));
v___x_1424_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1425_ = l_mkPanicMessageWithDecl(v___x_1424_, v___x_1423_, v___x_1422_, v___x_1421_, v___x_1420_);
return v___x_1425_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1426_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6));
v___x_1427_ = lean_unsigned_to_nat(21u);
v___x_1428_ = lean_unsigned_to_nat(183u);
v___x_1429_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5));
v___x_1430_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1431_ = l_mkPanicMessageWithDecl(v___x_1430_, v___x_1429_, v___x_1428_, v___x_1427_, v___x_1426_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(lean_object* v_k_1432_, lean_object* v_v_1433_, lean_object* v_t_1434_){
_start:
{
if (lean_obj_tag(v_t_1434_) == 0)
{
lean_object* v_size_1435_; lean_object* v_k_1436_; lean_object* v_v_1437_; lean_object* v_l_1438_; lean_object* v_r_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1796_; 
v_size_1435_ = lean_ctor_get(v_t_1434_, 0);
v_k_1436_ = lean_ctor_get(v_t_1434_, 1);
v_v_1437_ = lean_ctor_get(v_t_1434_, 2);
v_l_1438_ = lean_ctor_get(v_t_1434_, 3);
v_r_1439_ = lean_ctor_get(v_t_1434_, 4);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_t_1434_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1441_ = v_t_1434_;
v_isShared_1442_ = v_isSharedCheck_1796_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_r_1439_);
lean_inc(v_l_1438_);
lean_inc(v_v_1437_);
lean_inc(v_k_1436_);
lean_inc(v_size_1435_);
lean_dec(v_t_1434_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1796_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
uint8_t v___x_1443_; 
v___x_1443_ = lean_string_dec_lt(v_k_1432_, v_k_1436_);
if (v___x_1443_ == 0)
{
uint8_t v___x_1444_; 
v___x_1444_ = lean_string_dec_eq(v_k_1432_, v_k_1436_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; 
lean_dec(v_size_1435_);
v___x_1445_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1432_, v_v_1433_, v_r_1439_);
if (lean_obj_tag(v_l_1438_) == 0)
{
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_size_1446_; lean_object* v_size_1447_; lean_object* v_k_1448_; lean_object* v_v_1449_; lean_object* v_l_1450_; lean_object* v_r_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
v_size_1446_ = lean_ctor_get(v_l_1438_, 0);
v_size_1447_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_size_1447_);
v_k_1448_ = lean_ctor_get(v___x_1445_, 1);
lean_inc(v_k_1448_);
v_v_1449_ = lean_ctor_get(v___x_1445_, 2);
lean_inc(v_v_1449_);
v_l_1450_ = lean_ctor_get(v___x_1445_, 3);
lean_inc(v_l_1450_);
v_r_1451_ = lean_ctor_get(v___x_1445_, 4);
lean_inc(v_r_1451_);
v___x_1452_ = lean_unsigned_to_nat(3u);
v___x_1453_ = lean_nat_mul(v___x_1452_, v_size_1446_);
v___x_1454_ = lean_nat_dec_lt(v___x_1453_, v_size_1447_);
lean_dec(v___x_1453_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1459_; 
lean_dec(v_r_1451_);
lean_dec(v_l_1450_);
lean_dec(v_v_1449_);
lean_dec(v_k_1448_);
v___x_1455_ = lean_unsigned_to_nat(1u);
v___x_1456_ = lean_nat_add(v___x_1455_, v_size_1446_);
v___x_1457_ = lean_nat_add(v___x_1456_, v_size_1447_);
lean_dec(v_size_1447_);
lean_dec(v___x_1456_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 4, v___x_1445_);
lean_ctor_set(v___x_1441_, 0, v___x_1457_);
v___x_1459_ = v___x_1441_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1457_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_k_1436_);
lean_ctor_set(v_reuseFailAlloc_1460_, 2, v_v_1437_);
lean_ctor_set(v_reuseFailAlloc_1460_, 3, v_l_1438_);
lean_ctor_set(v_reuseFailAlloc_1460_, 4, v___x_1445_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
else
{
lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1530_; 
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1530_ == 0)
{
lean_object* v_unused_1531_; lean_object* v_unused_1532_; lean_object* v_unused_1533_; lean_object* v_unused_1534_; lean_object* v_unused_1535_; 
v_unused_1531_ = lean_ctor_get(v___x_1445_, 4);
lean_dec(v_unused_1531_);
v_unused_1532_ = lean_ctor_get(v___x_1445_, 3);
lean_dec(v_unused_1532_);
v_unused_1533_ = lean_ctor_get(v___x_1445_, 2);
lean_dec(v_unused_1533_);
v_unused_1534_ = lean_ctor_get(v___x_1445_, 1);
lean_dec(v_unused_1534_);
v_unused_1535_ = lean_ctor_get(v___x_1445_, 0);
lean_dec(v_unused_1535_);
v___x_1462_ = v___x_1445_;
v_isShared_1463_ = v_isSharedCheck_1530_;
goto v_resetjp_1461_;
}
else
{
lean_dec(v___x_1445_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1530_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
if (lean_obj_tag(v_l_1450_) == 0)
{
if (lean_obj_tag(v_r_1451_) == 0)
{
lean_object* v_size_1464_; lean_object* v_k_1465_; lean_object* v_v_1466_; lean_object* v_l_1467_; lean_object* v_r_1468_; lean_object* v_size_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; uint8_t v___x_1472_; 
v_size_1464_ = lean_ctor_get(v_l_1450_, 0);
v_k_1465_ = lean_ctor_get(v_l_1450_, 1);
v_v_1466_ = lean_ctor_get(v_l_1450_, 2);
v_l_1467_ = lean_ctor_get(v_l_1450_, 3);
v_r_1468_ = lean_ctor_get(v_l_1450_, 4);
v_size_1469_ = lean_ctor_get(v_r_1451_, 0);
v___x_1470_ = lean_unsigned_to_nat(2u);
v___x_1471_ = lean_nat_mul(v___x_1470_, v_size_1469_);
v___x_1472_ = lean_nat_dec_lt(v_size_1464_, v___x_1471_);
lean_dec(v___x_1471_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1501_; 
lean_inc(v_r_1468_);
lean_inc(v_l_1467_);
lean_inc(v_v_1466_);
lean_inc(v_k_1465_);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_l_1450_);
if (v_isSharedCheck_1501_ == 0)
{
lean_object* v_unused_1502_; lean_object* v_unused_1503_; lean_object* v_unused_1504_; lean_object* v_unused_1505_; lean_object* v_unused_1506_; 
v_unused_1502_ = lean_ctor_get(v_l_1450_, 4);
lean_dec(v_unused_1502_);
v_unused_1503_ = lean_ctor_get(v_l_1450_, 3);
lean_dec(v_unused_1503_);
v_unused_1504_ = lean_ctor_get(v_l_1450_, 2);
lean_dec(v_unused_1504_);
v_unused_1505_ = lean_ctor_get(v_l_1450_, 1);
lean_dec(v_unused_1505_);
v_unused_1506_ = lean_ctor_get(v_l_1450_, 0);
lean_dec(v_unused_1506_);
v___x_1474_ = v_l_1450_;
v_isShared_1475_ = v_isSharedCheck_1501_;
goto v_resetjp_1473_;
}
else
{
lean_dec(v_l_1450_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1501_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1491_; 
v___x_1476_ = lean_unsigned_to_nat(1u);
v___x_1477_ = lean_nat_add(v___x_1476_, v_size_1446_);
v___x_1478_ = lean_nat_add(v___x_1477_, v_size_1447_);
lean_dec(v_size_1447_);
if (lean_obj_tag(v_l_1467_) == 0)
{
lean_object* v_size_1499_; 
v_size_1499_ = lean_ctor_get(v_l_1467_, 0);
lean_inc(v_size_1499_);
v___y_1491_ = v_size_1499_;
goto v___jp_1490_;
}
else
{
lean_object* v___x_1500_; 
v___x_1500_ = lean_unsigned_to_nat(0u);
v___y_1491_ = v___x_1500_;
goto v___jp_1490_;
}
v___jp_1479_:
{
lean_object* v___x_1483_; lean_object* v___x_1485_; 
v___x_1483_ = lean_nat_add(v___y_1480_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec(v___y_1480_);
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 4, v_r_1451_);
lean_ctor_set(v___x_1474_, 3, v_r_1468_);
lean_ctor_set(v___x_1474_, 2, v_v_1449_);
lean_ctor_set(v___x_1474_, 1, v_k_1448_);
lean_ctor_set(v___x_1474_, 0, v___x_1483_);
v___x_1485_ = v___x_1474_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1483_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_k_1448_);
lean_ctor_set(v_reuseFailAlloc_1489_, 2, v_v_1449_);
lean_ctor_set(v_reuseFailAlloc_1489_, 3, v_r_1468_);
lean_ctor_set(v_reuseFailAlloc_1489_, 4, v_r_1451_);
v___x_1485_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
lean_object* v___x_1487_; 
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 4, v___x_1485_);
lean_ctor_set(v___x_1462_, 3, v___y_1481_);
lean_ctor_set(v___x_1462_, 2, v_v_1466_);
lean_ctor_set(v___x_1462_, 1, v_k_1465_);
lean_ctor_set(v___x_1462_, 0, v___x_1478_);
v___x_1487_ = v___x_1462_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1478_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_k_1465_);
lean_ctor_set(v_reuseFailAlloc_1488_, 2, v_v_1466_);
lean_ctor_set(v_reuseFailAlloc_1488_, 3, v___y_1481_);
lean_ctor_set(v_reuseFailAlloc_1488_, 4, v___x_1485_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
v___jp_1490_:
{
lean_object* v___x_1492_; lean_object* v___x_1494_; 
v___x_1492_ = lean_nat_add(v___x_1477_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec(v___x_1477_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 4, v_l_1467_);
lean_ctor_set(v___x_1441_, 0, v___x_1492_);
v___x_1494_ = v___x_1441_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1492_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_k_1436_);
lean_ctor_set(v_reuseFailAlloc_1498_, 2, v_v_1437_);
lean_ctor_set(v_reuseFailAlloc_1498_, 3, v_l_1438_);
lean_ctor_set(v_reuseFailAlloc_1498_, 4, v_l_1467_);
v___x_1494_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
lean_object* v___x_1495_; 
v___x_1495_ = lean_nat_add(v___x_1476_, v_size_1469_);
if (lean_obj_tag(v_r_1468_) == 0)
{
lean_object* v_size_1496_; 
v_size_1496_ = lean_ctor_get(v_r_1468_, 0);
lean_inc(v_size_1496_);
v___y_1480_ = v___x_1495_;
v___y_1481_ = v___x_1494_;
v___y_1482_ = v_size_1496_;
goto v___jp_1479_;
}
else
{
lean_object* v___x_1497_; 
v___x_1497_ = lean_unsigned_to_nat(0u);
v___y_1480_ = v___x_1495_;
v___y_1481_ = v___x_1494_;
v___y_1482_ = v___x_1497_;
goto v___jp_1479_;
}
}
}
}
}
else
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; 
lean_del_object(v___x_1441_);
v___x_1507_ = lean_unsigned_to_nat(1u);
v___x_1508_ = lean_nat_add(v___x_1507_, v_size_1446_);
v___x_1509_ = lean_nat_add(v___x_1508_, v_size_1447_);
lean_dec(v_size_1447_);
v___x_1510_ = lean_nat_add(v___x_1508_, v_size_1464_);
lean_dec(v___x_1508_);
lean_inc_ref(v_l_1438_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 4, v_l_1450_);
lean_ctor_set(v___x_1462_, 3, v_l_1438_);
lean_ctor_set(v___x_1462_, 2, v_v_1437_);
lean_ctor_set(v___x_1462_, 1, v_k_1436_);
lean_ctor_set(v___x_1462_, 0, v___x_1510_);
v___x_1512_ = v___x_1462_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1510_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_k_1436_);
lean_ctor_set(v_reuseFailAlloc_1525_, 2, v_v_1437_);
lean_ctor_set(v_reuseFailAlloc_1525_, 3, v_l_1438_);
lean_ctor_set(v_reuseFailAlloc_1525_, 4, v_l_1450_);
v___x_1512_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1519_; 
v_isSharedCheck_1519_ = !lean_is_exclusive(v_l_1438_);
if (v_isSharedCheck_1519_ == 0)
{
lean_object* v_unused_1520_; lean_object* v_unused_1521_; lean_object* v_unused_1522_; lean_object* v_unused_1523_; lean_object* v_unused_1524_; 
v_unused_1520_ = lean_ctor_get(v_l_1438_, 4);
lean_dec(v_unused_1520_);
v_unused_1521_ = lean_ctor_get(v_l_1438_, 3);
lean_dec(v_unused_1521_);
v_unused_1522_ = lean_ctor_get(v_l_1438_, 2);
lean_dec(v_unused_1522_);
v_unused_1523_ = lean_ctor_get(v_l_1438_, 1);
lean_dec(v_unused_1523_);
v_unused_1524_ = lean_ctor_get(v_l_1438_, 0);
lean_dec(v_unused_1524_);
v___x_1514_ = v_l_1438_;
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
else
{
lean_dec(v_l_1438_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 4, v_r_1451_);
lean_ctor_set(v___x_1514_, 3, v___x_1512_);
lean_ctor_set(v___x_1514_, 2, v_v_1449_);
lean_ctor_set(v___x_1514_, 1, v_k_1448_);
lean_ctor_set(v___x_1514_, 0, v___x_1509_);
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1509_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_k_1448_);
lean_ctor_set(v_reuseFailAlloc_1518_, 2, v_v_1449_);
lean_ctor_set(v_reuseFailAlloc_1518_, 3, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1518_, 4, v_r_1451_);
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
lean_dec_ref(v_l_1450_);
lean_del_object(v___x_1462_);
lean_dec(v_v_1449_);
lean_dec(v_k_1448_);
lean_dec(v_size_1447_);
lean_dec_ref(v_l_1438_);
lean_del_object(v___x_1441_);
lean_dec(v_v_1437_);
lean_dec(v_k_1436_);
v___x_1526_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3);
v___x_1527_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1526_);
return v___x_1527_;
}
}
else
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
lean_del_object(v___x_1462_);
lean_dec(v_r_1451_);
lean_dec(v_v_1449_);
lean_dec(v_k_1448_);
lean_dec(v_size_1447_);
lean_dec_ref(v_l_1438_);
lean_del_object(v___x_1441_);
lean_dec(v_v_1437_);
lean_dec(v_k_1436_);
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
v_size_1536_ = lean_ctor_get(v_l_1438_, 0);
v___x_1537_ = lean_unsigned_to_nat(1u);
v___x_1538_ = lean_nat_add(v___x_1537_, v_size_1536_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 4, v___x_1445_);
lean_ctor_set(v___x_1441_, 0, v___x_1538_);
v___x_1540_ = v___x_1441_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1538_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_k_1436_);
lean_ctor_set(v_reuseFailAlloc_1541_, 2, v_v_1437_);
lean_ctor_set(v_reuseFailAlloc_1541_, 3, v_l_1438_);
lean_ctor_set(v_reuseFailAlloc_1541_, 4, v___x_1445_);
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
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_l_1542_; 
v_l_1542_ = lean_ctor_get(v___x_1445_, 3);
lean_inc(v_l_1542_);
if (lean_obj_tag(v_l_1542_) == 0)
{
lean_object* v_r_1543_; 
v_r_1543_ = lean_ctor_get(v___x_1445_, 4);
lean_inc(v_r_1543_);
if (lean_obj_tag(v_r_1543_) == 0)
{
lean_object* v_size_1544_; lean_object* v_k_1545_; lean_object* v_v_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1560_; 
v_size_1544_ = lean_ctor_get(v___x_1445_, 0);
v_k_1545_ = lean_ctor_get(v___x_1445_, 1);
v_v_1546_ = lean_ctor_get(v___x_1445_, 2);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1560_ == 0)
{
lean_object* v_unused_1561_; lean_object* v_unused_1562_; 
v_unused_1561_ = lean_ctor_get(v___x_1445_, 4);
lean_dec(v_unused_1561_);
v_unused_1562_ = lean_ctor_get(v___x_1445_, 3);
lean_dec(v_unused_1562_);
v___x_1548_ = v___x_1445_;
v_isShared_1549_ = v_isSharedCheck_1560_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_v_1546_);
lean_inc(v_k_1545_);
lean_inc(v_size_1544_);
lean_dec(v___x_1445_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1560_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v_size_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1555_; 
v_size_1550_ = lean_ctor_get(v_l_1542_, 0);
v___x_1551_ = lean_unsigned_to_nat(1u);
v___x_1552_ = lean_nat_add(v___x_1551_, v_size_1544_);
lean_dec(v_size_1544_);
v___x_1553_ = lean_nat_add(v___x_1551_, v_size_1550_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 4, v_l_1542_);
lean_ctor_set(v___x_1548_, 3, v_l_1438_);
lean_ctor_set(v___x_1548_, 2, v_v_1437_);
lean_ctor_set(v___x_1548_, 1, v_k_1436_);
lean_ctor_set(v___x_1548_, 0, v___x_1553_);
v___x_1555_ = v___x_1548_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1553_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_k_1436_);
lean_ctor_set(v_reuseFailAlloc_1559_, 2, v_v_1437_);
lean_ctor_set(v_reuseFailAlloc_1559_, 3, v_l_1438_);
lean_ctor_set(v_reuseFailAlloc_1559_, 4, v_l_1542_);
v___x_1555_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
lean_object* v___x_1557_; 
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 4, v_r_1543_);
lean_ctor_set(v___x_1441_, 3, v___x_1555_);
lean_ctor_set(v___x_1441_, 2, v_v_1546_);
lean_ctor_set(v___x_1441_, 1, v_k_1545_);
lean_ctor_set(v___x_1441_, 0, v___x_1552_);
v___x_1557_ = v___x_1441_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1552_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_k_1545_);
lean_ctor_set(v_reuseFailAlloc_1558_, 2, v_v_1546_);
lean_ctor_set(v_reuseFailAlloc_1558_, 3, v___x_1555_);
lean_ctor_set(v_reuseFailAlloc_1558_, 4, v_r_1543_);
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
lean_object* v_k_1563_; lean_object* v_v_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1588_; 
v_k_1563_ = lean_ctor_get(v___x_1445_, 1);
v_v_1564_ = lean_ctor_get(v___x_1445_, 2);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1588_ == 0)
{
lean_object* v_unused_1589_; lean_object* v_unused_1590_; lean_object* v_unused_1591_; 
v_unused_1589_ = lean_ctor_get(v___x_1445_, 4);
lean_dec(v_unused_1589_);
v_unused_1590_ = lean_ctor_get(v___x_1445_, 3);
lean_dec(v_unused_1590_);
v_unused_1591_ = lean_ctor_get(v___x_1445_, 0);
lean_dec(v_unused_1591_);
v___x_1566_ = v___x_1445_;
v_isShared_1567_ = v_isSharedCheck_1588_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_v_1564_);
lean_inc(v_k_1563_);
lean_dec(v___x_1445_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1588_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v_k_1568_; lean_object* v_v_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1584_; 
v_k_1568_ = lean_ctor_get(v_l_1542_, 1);
v_v_1569_ = lean_ctor_get(v_l_1542_, 2);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_l_1542_);
if (v_isSharedCheck_1584_ == 0)
{
lean_object* v_unused_1585_; lean_object* v_unused_1586_; lean_object* v_unused_1587_; 
v_unused_1585_ = lean_ctor_get(v_l_1542_, 4);
lean_dec(v_unused_1585_);
v_unused_1586_ = lean_ctor_get(v_l_1542_, 3);
lean_dec(v_unused_1586_);
v_unused_1587_ = lean_ctor_get(v_l_1542_, 0);
lean_dec(v_unused_1587_);
v___x_1571_ = v_l_1542_;
v_isShared_1572_ = v_isSharedCheck_1584_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_v_1569_);
lean_inc(v_k_1568_);
lean_dec(v_l_1542_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1584_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1576_; 
v___x_1573_ = lean_unsigned_to_nat(3u);
v___x_1574_ = lean_unsigned_to_nat(1u);
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 4, v_r_1543_);
lean_ctor_set(v___x_1571_, 3, v_r_1543_);
lean_ctor_set(v___x_1571_, 2, v_v_1437_);
lean_ctor_set(v___x_1571_, 1, v_k_1436_);
lean_ctor_set(v___x_1571_, 0, v___x_1574_);
v___x_1576_ = v___x_1571_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1574_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v_k_1436_);
lean_ctor_set(v_reuseFailAlloc_1583_, 2, v_v_1437_);
lean_ctor_set(v_reuseFailAlloc_1583_, 3, v_r_1543_);
lean_ctor_set(v_reuseFailAlloc_1583_, 4, v_r_1543_);
v___x_1576_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v___x_1578_; 
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 3, v_r_1543_);
lean_ctor_set(v___x_1566_, 0, v___x_1574_);
v___x_1578_ = v___x_1566_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1574_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v_k_1563_);
lean_ctor_set(v_reuseFailAlloc_1582_, 2, v_v_1564_);
lean_ctor_set(v_reuseFailAlloc_1582_, 3, v_r_1543_);
lean_ctor_set(v_reuseFailAlloc_1582_, 4, v_r_1543_);
v___x_1578_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
lean_object* v___x_1580_; 
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 4, v___x_1578_);
lean_ctor_set(v___x_1441_, 3, v___x_1576_);
lean_ctor_set(v___x_1441_, 2, v_v_1569_);
lean_ctor_set(v___x_1441_, 1, v_k_1568_);
lean_ctor_set(v___x_1441_, 0, v___x_1573_);
v___x_1580_ = v___x_1441_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1573_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_k_1568_);
lean_ctor_set(v_reuseFailAlloc_1581_, 2, v_v_1569_);
lean_ctor_set(v_reuseFailAlloc_1581_, 3, v___x_1576_);
lean_ctor_set(v_reuseFailAlloc_1581_, 4, v___x_1578_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1592_; 
v_r_1592_ = lean_ctor_get(v___x_1445_, 4);
lean_inc(v_r_1592_);
if (lean_obj_tag(v_r_1592_) == 0)
{
lean_object* v_k_1593_; lean_object* v_v_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1606_; 
v_k_1593_ = lean_ctor_get(v___x_1445_, 1);
v_v_1594_ = lean_ctor_get(v___x_1445_, 2);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1606_ == 0)
{
lean_object* v_unused_1607_; lean_object* v_unused_1608_; lean_object* v_unused_1609_; 
v_unused_1607_ = lean_ctor_get(v___x_1445_, 4);
lean_dec(v_unused_1607_);
v_unused_1608_ = lean_ctor_get(v___x_1445_, 3);
lean_dec(v_unused_1608_);
v_unused_1609_ = lean_ctor_get(v___x_1445_, 0);
lean_dec(v_unused_1609_);
v___x_1596_ = v___x_1445_;
v_isShared_1597_ = v_isSharedCheck_1606_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_v_1594_);
lean_inc(v_k_1593_);
lean_dec(v___x_1445_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1606_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1601_; 
v___x_1598_ = lean_unsigned_to_nat(3u);
v___x_1599_ = lean_unsigned_to_nat(1u);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 4, v_l_1542_);
lean_ctor_set(v___x_1596_, 2, v_v_1437_);
lean_ctor_set(v___x_1596_, 1, v_k_1436_);
lean_ctor_set(v___x_1596_, 0, v___x_1599_);
v___x_1601_ = v___x_1596_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1599_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_k_1436_);
lean_ctor_set(v_reuseFailAlloc_1605_, 2, v_v_1437_);
lean_ctor_set(v_reuseFailAlloc_1605_, 3, v_l_1542_);
lean_ctor_set(v_reuseFailAlloc_1605_, 4, v_l_1542_);
v___x_1601_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
lean_object* v___x_1603_; 
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 4, v_r_1592_);
lean_ctor_set(v___x_1441_, 3, v___x_1601_);
lean_ctor_set(v___x_1441_, 2, v_v_1594_);
lean_ctor_set(v___x_1441_, 1, v_k_1593_);
lean_ctor_set(v___x_1441_, 0, v___x_1598_);
v___x_1603_ = v___x_1441_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_k_1593_);
lean_ctor_set(v_reuseFailAlloc_1604_, 2, v_v_1594_);
lean_ctor_set(v_reuseFailAlloc_1604_, 3, v___x_1601_);
lean_ctor_set(v_reuseFailAlloc_1604_, 4, v_r_1592_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
else
{
lean_object* v___x_1610_; lean_object* v___x_1612_; 
v___x_1610_ = lean_unsigned_to_nat(2u);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 4, v___x_1445_);
lean_ctor_set(v___x_1441_, 3, v_r_1592_);
lean_ctor_set(v___x_1441_, 0, v___x_1610_);
v___x_1612_ = v___x_1441_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1610_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_k_1436_);
lean_ctor_set(v_reuseFailAlloc_1613_, 2, v_v_1437_);
lean_ctor_set(v_reuseFailAlloc_1613_, 3, v_r_1592_);
lean_ctor_set(v_reuseFailAlloc_1613_, 4, v___x_1445_);
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
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 4, v___x_1445_);
lean_ctor_set(v___x_1441_, 3, v___x_1445_);
lean_ctor_set(v___x_1441_, 0, v___x_1614_);
v___x_1616_ = v___x_1441_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1614_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v_k_1436_);
lean_ctor_set(v_reuseFailAlloc_1617_, 2, v_v_1437_);
lean_ctor_set(v_reuseFailAlloc_1617_, 3, v___x_1445_);
lean_ctor_set(v_reuseFailAlloc_1617_, 4, v___x_1445_);
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
else
{
lean_object* v___x_1619_; 
lean_dec(v_v_1437_);
lean_dec(v_k_1436_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 2, v_v_1433_);
lean_ctor_set(v___x_1441_, 1, v_k_1432_);
v___x_1619_ = v___x_1441_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_size_1435_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_k_1432_);
lean_ctor_set(v_reuseFailAlloc_1620_, 2, v_v_1433_);
lean_ctor_set(v_reuseFailAlloc_1620_, 3, v_l_1438_);
lean_ctor_set(v_reuseFailAlloc_1620_, 4, v_r_1439_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
else
{
lean_object* v___x_1621_; 
lean_dec(v_size_1435_);
v___x_1621_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1432_, v_v_1433_, v_l_1438_);
if (lean_obj_tag(v_r_1439_) == 0)
{
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_size_1622_; lean_object* v_size_1623_; lean_object* v_k_1624_; lean_object* v_v_1625_; lean_object* v_l_1626_; lean_object* v_r_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; uint8_t v___x_1630_; 
v_size_1622_ = lean_ctor_get(v_r_1439_, 0);
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
v___x_1632_ = lean_nat_add(v___x_1631_, v_size_1623_);
lean_dec(v_size_1623_);
v___x_1633_ = lean_nat_add(v___x_1632_, v_size_1622_);
lean_dec(v___x_1632_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 3, v___x_1621_);
lean_ctor_set(v___x_1441_, 0, v___x_1633_);
v___x_1635_ = v___x_1441_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1633_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_k_1436_);
lean_ctor_set(v_reuseFailAlloc_1636_, 2, v_v_1437_);
lean_ctor_set(v_reuseFailAlloc_1636_, 3, v___x_1621_);
lean_ctor_set(v_reuseFailAlloc_1636_, 4, v_r_1439_);
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
lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1708_; 
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1708_ == 0)
{
lean_object* v_unused_1709_; lean_object* v_unused_1710_; lean_object* v_unused_1711_; lean_object* v_unused_1712_; lean_object* v_unused_1713_; 
v_unused_1709_ = lean_ctor_get(v___x_1621_, 4);
lean_dec(v_unused_1709_);
v_unused_1710_ = lean_ctor_get(v___x_1621_, 3);
lean_dec(v_unused_1710_);
v_unused_1711_ = lean_ctor_get(v___x_1621_, 2);
lean_dec(v_unused_1711_);
v_unused_1712_ = lean_ctor_get(v___x_1621_, 1);
lean_dec(v_unused_1712_);
v_unused_1713_ = lean_ctor_get(v___x_1621_, 0);
lean_dec(v_unused_1713_);
v___x_1638_ = v___x_1621_;
v_isShared_1639_ = v_isSharedCheck_1708_;
goto v_resetjp_1637_;
}
else
{
lean_dec(v___x_1621_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1708_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
if (lean_obj_tag(v_l_1626_) == 0)
{
if (lean_obj_tag(v_r_1627_) == 0)
{
lean_object* v_size_1640_; lean_object* v_size_1641_; lean_object* v_k_1642_; lean_object* v_v_1643_; lean_object* v_l_1644_; lean_object* v_r_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; uint8_t v___x_1648_; 
v_size_1640_ = lean_ctor_get(v_l_1626_, 0);
v_size_1641_ = lean_ctor_get(v_r_1627_, 0);
v_k_1642_ = lean_ctor_get(v_r_1627_, 1);
v_v_1643_ = lean_ctor_get(v_r_1627_, 2);
v_l_1644_ = lean_ctor_get(v_r_1627_, 3);
v_r_1645_ = lean_ctor_get(v_r_1627_, 4);
v___x_1646_ = lean_unsigned_to_nat(2u);
v___x_1647_ = lean_nat_mul(v___x_1646_, v_size_1640_);
v___x_1648_ = lean_nat_dec_lt(v_size_1641_, v___x_1647_);
lean_dec(v___x_1647_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1678_; 
lean_inc(v_r_1645_);
lean_inc(v_l_1644_);
lean_inc(v_v_1643_);
lean_inc(v_k_1642_);
v_isSharedCheck_1678_ = !lean_is_exclusive(v_r_1627_);
if (v_isSharedCheck_1678_ == 0)
{
lean_object* v_unused_1679_; lean_object* v_unused_1680_; lean_object* v_unused_1681_; lean_object* v_unused_1682_; lean_object* v_unused_1683_; 
v_unused_1679_ = lean_ctor_get(v_r_1627_, 4);
lean_dec(v_unused_1679_);
v_unused_1680_ = lean_ctor_get(v_r_1627_, 3);
lean_dec(v_unused_1680_);
v_unused_1681_ = lean_ctor_get(v_r_1627_, 2);
lean_dec(v_unused_1681_);
v_unused_1682_ = lean_ctor_get(v_r_1627_, 1);
lean_dec(v_unused_1682_);
v_unused_1683_ = lean_ctor_get(v_r_1627_, 0);
lean_dec(v_unused_1683_);
v___x_1650_ = v_r_1627_;
v_isShared_1651_ = v_isSharedCheck_1678_;
goto v_resetjp_1649_;
}
else
{
lean_dec(v_r_1627_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1678_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___x_1666_; lean_object* v___y_1668_; 
v___x_1652_ = lean_unsigned_to_nat(1u);
v___x_1653_ = lean_nat_add(v___x_1652_, v_size_1623_);
lean_dec(v_size_1623_);
v___x_1654_ = lean_nat_add(v___x_1653_, v_size_1622_);
lean_dec(v___x_1653_);
v___x_1666_ = lean_nat_add(v___x_1652_, v_size_1640_);
if (lean_obj_tag(v_l_1644_) == 0)
{
lean_object* v_size_1676_; 
v_size_1676_ = lean_ctor_get(v_l_1644_, 0);
lean_inc(v_size_1676_);
v___y_1668_ = v_size_1676_;
goto v___jp_1667_;
}
else
{
lean_object* v___x_1677_; 
v___x_1677_ = lean_unsigned_to_nat(0u);
v___y_1668_ = v___x_1677_;
goto v___jp_1667_;
}
v___jp_1655_:
{
lean_object* v___x_1659_; lean_object* v___x_1661_; 
v___x_1659_ = lean_nat_add(v___y_1656_, v___y_1658_);
lean_dec(v___y_1658_);
lean_dec(v___y_1656_);
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 4, v_r_1439_);
lean_ctor_set(v___x_1650_, 3, v_r_1645_);
lean_ctor_set(v___x_1650_, 2, v_v_1437_);
lean_ctor_set(v___x_1650_, 1, v_k_1436_);
lean_ctor_set(v___x_1650_, 0, v___x_1659_);
v___x_1661_ = v___x_1650_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1659_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_k_1436_);
lean_ctor_set(v_reuseFailAlloc_1665_, 2, v_v_1437_);
lean_ctor_set(v_reuseFailAlloc_1665_, 3, v_r_1645_);
lean_ctor_set(v_reuseFailAlloc_1665_, 4, v_r_1439_);
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
lean_ctor_set(v___x_1638_, 2, v_v_1643_);
lean_ctor_set(v___x_1638_, 1, v_k_1642_);
lean_ctor_set(v___x_1638_, 0, v___x_1654_);
v___x_1663_ = v___x_1638_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1654_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v_k_1642_);
lean_ctor_set(v_reuseFailAlloc_1664_, 2, v_v_1643_);
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
v___jp_1667_:
{
lean_object* v___x_1669_; lean_object* v___x_1671_; 
v___x_1669_ = lean_nat_add(v___x_1666_, v___y_1668_);
lean_dec(v___y_1668_);
lean_dec(v___x_1666_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 4, v_l_1644_);
lean_ctor_set(v___x_1441_, 3, v_l_1626_);
lean_ctor_set(v___x_1441_, 2, v_v_1625_);
lean_ctor_set(v___x_1441_, 1, v_k_1624_);
lean_ctor_set(v___x_1441_, 0, v___x_1669_);
v___x_1671_ = v___x_1441_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1669_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_k_1624_);
lean_ctor_set(v_reuseFailAlloc_1675_, 2, v_v_1625_);
lean_ctor_set(v_reuseFailAlloc_1675_, 3, v_l_1626_);
lean_ctor_set(v_reuseFailAlloc_1675_, 4, v_l_1644_);
v___x_1671_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
lean_object* v___x_1672_; 
v___x_1672_ = lean_nat_add(v___x_1652_, v_size_1622_);
if (lean_obj_tag(v_r_1645_) == 0)
{
lean_object* v_size_1673_; 
v_size_1673_ = lean_ctor_get(v_r_1645_, 0);
lean_inc(v_size_1673_);
v___y_1656_ = v___x_1672_;
v___y_1657_ = v___x_1671_;
v___y_1658_ = v_size_1673_;
goto v___jp_1655_;
}
else
{
lean_object* v___x_1674_; 
v___x_1674_ = lean_unsigned_to_nat(0u);
v___y_1656_ = v___x_1672_;
v___y_1657_ = v___x_1671_;
v___y_1658_ = v___x_1674_;
goto v___jp_1655_;
}
}
}
}
}
else
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1690_; 
lean_del_object(v___x_1441_);
v___x_1684_ = lean_unsigned_to_nat(1u);
v___x_1685_ = lean_nat_add(v___x_1684_, v_size_1623_);
lean_dec(v_size_1623_);
v___x_1686_ = lean_nat_add(v___x_1685_, v_size_1622_);
lean_dec(v___x_1685_);
v___x_1687_ = lean_nat_add(v___x_1684_, v_size_1622_);
v___x_1688_ = lean_nat_add(v___x_1687_, v_size_1641_);
lean_dec(v___x_1687_);
lean_inc_ref(v_r_1439_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 4, v_r_1439_);
lean_ctor_set(v___x_1638_, 3, v_r_1627_);
lean_ctor_set(v___x_1638_, 2, v_v_1437_);
lean_ctor_set(v___x_1638_, 1, v_k_1436_);
lean_ctor_set(v___x_1638_, 0, v___x_1688_);
v___x_1690_ = v___x_1638_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1688_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v_k_1436_);
lean_ctor_set(v_reuseFailAlloc_1703_, 2, v_v_1437_);
lean_ctor_set(v_reuseFailAlloc_1703_, 3, v_r_1627_);
lean_ctor_set(v_reuseFailAlloc_1703_, 4, v_r_1439_);
v___x_1690_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
v_isSharedCheck_1697_ = !lean_is_exclusive(v_r_1439_);
if (v_isSharedCheck_1697_ == 0)
{
lean_object* v_unused_1698_; lean_object* v_unused_1699_; lean_object* v_unused_1700_; lean_object* v_unused_1701_; lean_object* v_unused_1702_; 
v_unused_1698_ = lean_ctor_get(v_r_1439_, 4);
lean_dec(v_unused_1698_);
v_unused_1699_ = lean_ctor_get(v_r_1439_, 3);
lean_dec(v_unused_1699_);
v_unused_1700_ = lean_ctor_get(v_r_1439_, 2);
lean_dec(v_unused_1700_);
v_unused_1701_ = lean_ctor_get(v_r_1439_, 1);
lean_dec(v_unused_1701_);
v_unused_1702_ = lean_ctor_get(v_r_1439_, 0);
lean_dec(v_unused_1702_);
v___x_1692_ = v_r_1439_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_dec(v_r_1439_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 4, v___x_1690_);
lean_ctor_set(v___x_1692_, 3, v_l_1626_);
lean_ctor_set(v___x_1692_, 2, v_v_1625_);
lean_ctor_set(v___x_1692_, 1, v_k_1624_);
lean_ctor_set(v___x_1692_, 0, v___x_1686_);
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1686_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_k_1624_);
lean_ctor_set(v_reuseFailAlloc_1696_, 2, v_v_1625_);
lean_ctor_set(v_reuseFailAlloc_1696_, 3, v_l_1626_);
lean_ctor_set(v_reuseFailAlloc_1696_, 4, v___x_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
}
else
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
lean_dec_ref(v_l_1626_);
lean_del_object(v___x_1638_);
lean_dec(v_v_1625_);
lean_dec(v_k_1624_);
lean_dec(v_size_1623_);
lean_dec_ref(v_r_1439_);
lean_del_object(v___x_1441_);
lean_dec(v_v_1437_);
lean_dec(v_k_1436_);
v___x_1704_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7);
v___x_1705_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1704_);
return v___x_1705_;
}
}
else
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
lean_del_object(v___x_1638_);
lean_dec(v_r_1627_);
lean_dec(v_v_1625_);
lean_dec(v_k_1624_);
lean_dec(v_size_1623_);
lean_dec_ref(v_r_1439_);
lean_del_object(v___x_1441_);
lean_dec(v_v_1437_);
lean_dec(v_k_1436_);
v___x_1706_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8);
v___x_1707_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1706_);
return v___x_1707_;
}
}
}
}
else
{
lean_object* v_size_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1718_; 
v_size_1714_ = lean_ctor_get(v_r_1439_, 0);
v___x_1715_ = lean_unsigned_to_nat(1u);
v___x_1716_ = lean_nat_add(v___x_1715_, v_size_1714_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 3, v___x_1621_);
lean_ctor_set(v___x_1441_, 0, v___x_1716_);
v___x_1718_ = v___x_1441_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1716_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v_k_1436_);
lean_ctor_set(v_reuseFailAlloc_1719_, 2, v_v_1437_);
lean_ctor_set(v_reuseFailAlloc_1719_, 3, v___x_1621_);
lean_ctor_set(v_reuseFailAlloc_1719_, 4, v_r_1439_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
else
{
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_l_1720_; 
v_l_1720_ = lean_ctor_get(v___x_1621_, 3);
lean_inc(v_l_1720_);
if (lean_obj_tag(v_l_1720_) == 0)
{
lean_object* v_r_1721_; 
v_r_1721_ = lean_ctor_get(v___x_1621_, 4);
lean_inc(v_r_1721_);
if (lean_obj_tag(v_r_1721_) == 0)
{
lean_object* v_size_1722_; lean_object* v_k_1723_; lean_object* v_v_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1738_; 
v_size_1722_ = lean_ctor_get(v___x_1621_, 0);
v_k_1723_ = lean_ctor_get(v___x_1621_, 1);
v_v_1724_ = lean_ctor_get(v___x_1621_, 2);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1738_ == 0)
{
lean_object* v_unused_1739_; lean_object* v_unused_1740_; 
v_unused_1739_ = lean_ctor_get(v___x_1621_, 4);
lean_dec(v_unused_1739_);
v_unused_1740_ = lean_ctor_get(v___x_1621_, 3);
lean_dec(v_unused_1740_);
v___x_1726_ = v___x_1621_;
v_isShared_1727_ = v_isSharedCheck_1738_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_v_1724_);
lean_inc(v_k_1723_);
lean_inc(v_size_1722_);
lean_dec(v___x_1621_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1738_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v_size_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1733_; 
v_size_1728_ = lean_ctor_get(v_r_1721_, 0);
v___x_1729_ = lean_unsigned_to_nat(1u);
v___x_1730_ = lean_nat_add(v___x_1729_, v_size_1722_);
lean_dec(v_size_1722_);
v___x_1731_ = lean_nat_add(v___x_1729_, v_size_1728_);
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 4, v_r_1439_);
lean_ctor_set(v___x_1726_, 3, v_r_1721_);
lean_ctor_set(v___x_1726_, 2, v_v_1437_);
lean_ctor_set(v___x_1726_, 1, v_k_1436_);
lean_ctor_set(v___x_1726_, 0, v___x_1731_);
v___x_1733_ = v___x_1726_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1731_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v_k_1436_);
lean_ctor_set(v_reuseFailAlloc_1737_, 2, v_v_1437_);
lean_ctor_set(v_reuseFailAlloc_1737_, 3, v_r_1721_);
lean_ctor_set(v_reuseFailAlloc_1737_, 4, v_r_1439_);
v___x_1733_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
lean_object* v___x_1735_; 
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 4, v___x_1733_);
lean_ctor_set(v___x_1441_, 3, v_l_1720_);
lean_ctor_set(v___x_1441_, 2, v_v_1724_);
lean_ctor_set(v___x_1441_, 1, v_k_1723_);
lean_ctor_set(v___x_1441_, 0, v___x_1730_);
v___x_1735_ = v___x_1441_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1730_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v_k_1723_);
lean_ctor_set(v_reuseFailAlloc_1736_, 2, v_v_1724_);
lean_ctor_set(v_reuseFailAlloc_1736_, 3, v_l_1720_);
lean_ctor_set(v_reuseFailAlloc_1736_, 4, v___x_1733_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
else
{
lean_object* v_k_1741_; lean_object* v_v_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1754_; 
v_k_1741_ = lean_ctor_get(v___x_1621_, 1);
v_v_1742_ = lean_ctor_get(v___x_1621_, 2);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1754_ == 0)
{
lean_object* v_unused_1755_; lean_object* v_unused_1756_; lean_object* v_unused_1757_; 
v_unused_1755_ = lean_ctor_get(v___x_1621_, 4);
lean_dec(v_unused_1755_);
v_unused_1756_ = lean_ctor_get(v___x_1621_, 3);
lean_dec(v_unused_1756_);
v_unused_1757_ = lean_ctor_get(v___x_1621_, 0);
lean_dec(v_unused_1757_);
v___x_1744_ = v___x_1621_;
v_isShared_1745_ = v_isSharedCheck_1754_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_v_1742_);
lean_inc(v_k_1741_);
lean_dec(v___x_1621_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1754_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1749_; 
v___x_1746_ = lean_unsigned_to_nat(3u);
v___x_1747_ = lean_unsigned_to_nat(1u);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 3, v_r_1721_);
lean_ctor_set(v___x_1744_, 2, v_v_1437_);
lean_ctor_set(v___x_1744_, 1, v_k_1436_);
lean_ctor_set(v___x_1744_, 0, v___x_1747_);
v___x_1749_ = v___x_1744_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1747_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v_k_1436_);
lean_ctor_set(v_reuseFailAlloc_1753_, 2, v_v_1437_);
lean_ctor_set(v_reuseFailAlloc_1753_, 3, v_r_1721_);
lean_ctor_set(v_reuseFailAlloc_1753_, 4, v_r_1721_);
v___x_1749_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
lean_object* v___x_1751_; 
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 4, v___x_1749_);
lean_ctor_set(v___x_1441_, 3, v_l_1720_);
lean_ctor_set(v___x_1441_, 2, v_v_1742_);
lean_ctor_set(v___x_1441_, 1, v_k_1741_);
lean_ctor_set(v___x_1441_, 0, v___x_1746_);
v___x_1751_ = v___x_1441_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1746_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_k_1741_);
lean_ctor_set(v_reuseFailAlloc_1752_, 2, v_v_1742_);
lean_ctor_set(v_reuseFailAlloc_1752_, 3, v_l_1720_);
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
else
{
lean_object* v_r_1758_; 
v_r_1758_ = lean_ctor_get(v___x_1621_, 4);
lean_inc(v_r_1758_);
if (lean_obj_tag(v_r_1758_) == 0)
{
lean_object* v_k_1759_; lean_object* v_v_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1784_; 
v_k_1759_ = lean_ctor_get(v___x_1621_, 1);
v_v_1760_ = lean_ctor_get(v___x_1621_, 2);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1784_ == 0)
{
lean_object* v_unused_1785_; lean_object* v_unused_1786_; lean_object* v_unused_1787_; 
v_unused_1785_ = lean_ctor_get(v___x_1621_, 4);
lean_dec(v_unused_1785_);
v_unused_1786_ = lean_ctor_get(v___x_1621_, 3);
lean_dec(v_unused_1786_);
v_unused_1787_ = lean_ctor_get(v___x_1621_, 0);
lean_dec(v_unused_1787_);
v___x_1762_ = v___x_1621_;
v_isShared_1763_ = v_isSharedCheck_1784_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_v_1760_);
lean_inc(v_k_1759_);
lean_dec(v___x_1621_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1784_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v_k_1764_; lean_object* v_v_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1780_; 
v_k_1764_ = lean_ctor_get(v_r_1758_, 1);
v_v_1765_ = lean_ctor_get(v_r_1758_, 2);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_r_1758_);
if (v_isSharedCheck_1780_ == 0)
{
lean_object* v_unused_1781_; lean_object* v_unused_1782_; lean_object* v_unused_1783_; 
v_unused_1781_ = lean_ctor_get(v_r_1758_, 4);
lean_dec(v_unused_1781_);
v_unused_1782_ = lean_ctor_get(v_r_1758_, 3);
lean_dec(v_unused_1782_);
v_unused_1783_ = lean_ctor_get(v_r_1758_, 0);
lean_dec(v_unused_1783_);
v___x_1767_ = v_r_1758_;
v_isShared_1768_ = v_isSharedCheck_1780_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_v_1765_);
lean_inc(v_k_1764_);
lean_dec(v_r_1758_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1780_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1772_; 
v___x_1769_ = lean_unsigned_to_nat(3u);
v___x_1770_ = lean_unsigned_to_nat(1u);
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 4, v_l_1720_);
lean_ctor_set(v___x_1767_, 3, v_l_1720_);
lean_ctor_set(v___x_1767_, 2, v_v_1760_);
lean_ctor_set(v___x_1767_, 1, v_k_1759_);
lean_ctor_set(v___x_1767_, 0, v___x_1770_);
v___x_1772_ = v___x_1767_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1770_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_k_1759_);
lean_ctor_set(v_reuseFailAlloc_1779_, 2, v_v_1760_);
lean_ctor_set(v_reuseFailAlloc_1779_, 3, v_l_1720_);
lean_ctor_set(v_reuseFailAlloc_1779_, 4, v_l_1720_);
v___x_1772_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1774_; 
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 4, v_l_1720_);
lean_ctor_set(v___x_1762_, 2, v_v_1437_);
lean_ctor_set(v___x_1762_, 1, v_k_1436_);
lean_ctor_set(v___x_1762_, 0, v___x_1770_);
v___x_1774_ = v___x_1762_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1770_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v_k_1436_);
lean_ctor_set(v_reuseFailAlloc_1778_, 2, v_v_1437_);
lean_ctor_set(v_reuseFailAlloc_1778_, 3, v_l_1720_);
lean_ctor_set(v_reuseFailAlloc_1778_, 4, v_l_1720_);
v___x_1774_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
lean_object* v___x_1776_; 
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 4, v___x_1774_);
lean_ctor_set(v___x_1441_, 3, v___x_1772_);
lean_ctor_set(v___x_1441_, 2, v_v_1765_);
lean_ctor_set(v___x_1441_, 1, v_k_1764_);
lean_ctor_set(v___x_1441_, 0, v___x_1769_);
v___x_1776_ = v___x_1441_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1769_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v_k_1764_);
lean_ctor_set(v_reuseFailAlloc_1777_, 2, v_v_1765_);
lean_ctor_set(v_reuseFailAlloc_1777_, 3, v___x_1772_);
lean_ctor_set(v_reuseFailAlloc_1777_, 4, v___x_1774_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
}
}
else
{
lean_object* v___x_1788_; lean_object* v___x_1790_; 
v___x_1788_ = lean_unsigned_to_nat(2u);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 4, v_r_1758_);
lean_ctor_set(v___x_1441_, 3, v___x_1621_);
lean_ctor_set(v___x_1441_, 0, v___x_1788_);
v___x_1790_ = v___x_1441_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1788_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_k_1436_);
lean_ctor_set(v_reuseFailAlloc_1791_, 2, v_v_1437_);
lean_ctor_set(v_reuseFailAlloc_1791_, 3, v___x_1621_);
lean_ctor_set(v_reuseFailAlloc_1791_, 4, v_r_1758_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
else
{
lean_object* v___x_1792_; lean_object* v___x_1794_; 
v___x_1792_ = lean_unsigned_to_nat(1u);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 4, v___x_1621_);
lean_ctor_set(v___x_1441_, 3, v___x_1621_);
lean_ctor_set(v___x_1441_, 0, v___x_1792_);
v___x_1794_ = v___x_1441_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1792_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v_k_1436_);
lean_ctor_set(v_reuseFailAlloc_1795_, 2, v_v_1437_);
lean_ctor_set(v_reuseFailAlloc_1795_, 3, v___x_1621_);
lean_ctor_set(v_reuseFailAlloc_1795_, 4, v___x_1621_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
}
}
else
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = lean_unsigned_to_nat(1u);
v___x_1798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1797_);
lean_ctor_set(v___x_1798_, 1, v_k_1432_);
lean_ctor_set(v___x_1798_, 2, v_v_1433_);
lean_ctor_set(v___x_1798_, 3, v_t_1434_);
lean_ctor_set(v___x_1798_, 4, v_t_1434_);
return v___x_1798_;
}
}
}
static lean_object* _init_l_Lean_Json_setObjVal_x21___closed__2(void){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1801_ = ((lean_object*)(l_Lean_Json_setObjVal_x21___closed__1));
v___x_1802_ = lean_unsigned_to_nat(21u);
v___x_1803_ = lean_unsigned_to_nat(285u);
v___x_1804_ = ((lean_object*)(l_Lean_Json_setObjVal_x21___closed__0));
v___x_1805_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0));
v___x_1806_ = l_mkPanicMessageWithDecl(v___x_1805_, v___x_1804_, v___x_1803_, v___x_1802_, v___x_1801_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_setObjVal_x21(lean_object* v_x_1807_, lean_object* v_x_1808_, lean_object* v_x_1809_){
_start:
{
if (lean_obj_tag(v_x_1807_) == 5)
{
lean_object* v_kvPairs_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1818_; 
v_kvPairs_1810_ = lean_ctor_get(v_x_1807_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v_x_1807_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1812_ = v_x_1807_;
v_isShared_1813_ = v_isSharedCheck_1818_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_kvPairs_1810_);
lean_dec(v_x_1807_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1818_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1814_; lean_object* v___x_1816_; 
v___x_1814_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_x_1808_, v_x_1809_, v_kvPairs_1810_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v___x_1814_);
v___x_1816_ = v___x_1812_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1814_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
else
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
lean_dec(v_x_1809_);
lean_dec_ref(v_x_1808_);
lean_dec(v_x_1807_);
v___x_1819_ = lean_obj_once(&l_Lean_Json_setObjVal_x21___closed__2, &l_Lean_Json_setObjVal_x21___closed__2_once, _init_l_Lean_Json_setObjVal_x21___closed__2);
v___x_1820_ = l_panic___at___00Lean_Json_setObjVal_x21_spec__1(v___x_1819_);
return v___x_1820_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0(lean_object* v_00_u03b2_1821_, lean_object* v_msg_1822_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v_msg_1822_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0(lean_object* v_00_u03b2_1824_, lean_object* v_k_1825_, lean_object* v_v_1826_, lean_object* v_t_1827_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1825_, v_v_1826_, v_t_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(lean_object* v_init_1829_, lean_object* v_x_1830_){
_start:
{
if (lean_obj_tag(v_x_1830_) == 0)
{
lean_object* v_k_1831_; lean_object* v_v_1832_; lean_object* v_l_1833_; lean_object* v_r_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v_k_1831_ = lean_ctor_get(v_x_1830_, 1);
lean_inc(v_k_1831_);
v_v_1832_ = lean_ctor_get(v_x_1830_, 2);
lean_inc(v_v_1832_);
v_l_1833_ = lean_ctor_get(v_x_1830_, 3);
lean_inc(v_l_1833_);
v_r_1834_ = lean_ctor_get(v_x_1830_, 4);
lean_inc(v_r_1834_);
lean_dec_ref(v_x_1830_);
v___x_1835_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_init_1829_, v_l_1833_);
v___x_1836_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1831_, v_v_1832_, v___x_1835_);
v_init_1829_ = v___x_1836_;
v_x_1830_ = v_r_1834_;
goto _start;
}
else
{
return v_init_1829_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mergeObj(lean_object* v_x_1838_, lean_object* v_x_1839_){
_start:
{
if (lean_obj_tag(v_x_1838_) == 5)
{
if (lean_obj_tag(v_x_1839_) == 5)
{
lean_object* v_kvPairs_1840_; lean_object* v_kvPairs_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1849_; 
v_kvPairs_1840_ = lean_ctor_get(v_x_1838_, 0);
lean_inc(v_kvPairs_1840_);
lean_dec_ref(v_x_1838_);
v_kvPairs_1841_ = lean_ctor_get(v_x_1839_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v_x_1839_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1843_ = v_x_1839_;
v_isShared_1844_ = v_isSharedCheck_1849_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_kvPairs_1841_);
lean_dec(v_x_1839_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1849_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1845_; lean_object* v___x_1847_; 
v___x_1845_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_kvPairs_1840_, v_kvPairs_1841_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v___x_1845_);
v___x_1847_ = v___x_1843_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1845_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
else
{
lean_dec_ref(v_x_1838_);
return v_x_1839_;
}
}
else
{
lean_dec(v_x_1838_);
return v_x_1839_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0(lean_object* v_init_1850_, lean_object* v_t_1851_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_init_1850_, v_t_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorIdx(lean_object* v_x_1853_){
_start:
{
if (lean_obj_tag(v_x_1853_) == 0)
{
lean_object* v___x_1854_; 
v___x_1854_ = lean_unsigned_to_nat(0u);
return v___x_1854_;
}
else
{
lean_object* v___x_1855_; 
v___x_1855_ = lean_unsigned_to_nat(1u);
return v___x_1855_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorIdx___boxed(lean_object* v_x_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_Lean_Json_Structured_ctorIdx(v_x_1856_);
lean_dec_ref(v_x_1856_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim___redArg(lean_object* v_t_1858_, lean_object* v_k_1859_){
_start:
{
if (lean_obj_tag(v_t_1858_) == 0)
{
lean_object* v_elems_1860_; lean_object* v___x_1861_; 
v_elems_1860_ = lean_ctor_get(v_t_1858_, 0);
lean_inc_ref(v_elems_1860_);
lean_dec_ref(v_t_1858_);
v___x_1861_ = lean_apply_1(v_k_1859_, v_elems_1860_);
return v___x_1861_;
}
else
{
lean_object* v_kvPairs_1862_; lean_object* v___x_1863_; 
v_kvPairs_1862_ = lean_ctor_get(v_t_1858_, 0);
lean_inc(v_kvPairs_1862_);
lean_dec_ref(v_t_1858_);
v___x_1863_ = lean_apply_1(v_k_1859_, v_kvPairs_1862_);
return v___x_1863_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim(lean_object* v_motive_1864_, lean_object* v_ctorIdx_1865_, lean_object* v_t_1866_, lean_object* v_h_1867_, lean_object* v_k_1868_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1866_, v_k_1868_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim___boxed(lean_object* v_motive_1870_, lean_object* v_ctorIdx_1871_, lean_object* v_t_1872_, lean_object* v_h_1873_, lean_object* v_k_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Lean_Json_Structured_ctorElim(v_motive_1870_, v_ctorIdx_1871_, v_t_1872_, v_h_1873_, v_k_1874_);
lean_dec(v_ctorIdx_1871_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_arr_elim___redArg(lean_object* v_t_1876_, lean_object* v_arr_1877_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1876_, v_arr_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_arr_elim(lean_object* v_motive_1879_, lean_object* v_t_1880_, lean_object* v_h_1881_, lean_object* v_arr_1882_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1880_, v_arr_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_obj_elim___redArg(lean_object* v_t_1884_, lean_object* v_obj_1885_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1884_, v_obj_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_obj_elim(lean_object* v_motive_1887_, lean_object* v_t_1888_, lean_object* v_h_1889_, lean_object* v_obj_1890_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1888_, v_obj_1890_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeArrayStructured___lam__0(lean_object* v_elems_1892_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1893_, 0, v_elems_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeRawStringStructured___lam__0(lean_object* v_kvPairs_1896_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1897_, 0, v_kvPairs_1896_);
return v___x_1897_;
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
