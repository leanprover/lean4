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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Json_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorIdx___impl___boxed(lean_object*);
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
lean_object* v_fst_146_; lean_object* v_snd_147_; lean_object* v___x_167_; lean_object* v_fst_168_; lean_object* v_snd_169_; lean_object* v___x_170_; lean_object* v_fst_171_; lean_object* v_snd_172_; uint8_t v___x_173_; 
v___x_167_ = l_Lean_JsonNumber_normalize(v_a_143_);
v_fst_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_fst_168_);
v_snd_169_ = lean_ctor_get(v___x_167_, 1);
lean_inc(v_snd_169_);
lean_dec_ref(v___x_167_);
v___x_170_ = l_Lean_JsonNumber_normalize(v_b_144_);
v_fst_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_fst_171_);
v_snd_172_ = lean_ctor_get(v___x_170_, 1);
lean_inc(v_snd_172_);
lean_dec_ref(v___x_170_);
v___x_173_ = lean_int_dec_eq(v_fst_168_, v_fst_171_);
if (v___x_173_ == 0)
{
uint8_t v___x_174_; 
lean_dec(v_snd_172_);
lean_dec(v_snd_169_);
v___x_174_ = lean_int_dec_lt(v_fst_168_, v_fst_171_);
lean_dec(v_fst_171_);
lean_dec(v_fst_168_);
return v___x_174_;
}
else
{
lean_object* v___x_175_; uint8_t v___x_176_; 
lean_dec(v_fst_171_);
v___x_175_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v___x_176_ = lean_int_dec_eq(v_fst_168_, v___x_175_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_177_ = lean_obj_once(&l_Lean_JsonNumber_normalize___closed__1, &l_Lean_JsonNumber_normalize___closed__1_once, _init_l_Lean_JsonNumber_normalize___closed__1);
v___x_178_ = lean_int_dec_eq(v_fst_168_, v___x_177_);
lean_dec(v_fst_168_);
if (v___x_178_ == 0)
{
v_fst_146_ = v_snd_169_;
v_snd_147_ = v_snd_172_;
goto v___jp_145_;
}
else
{
v_fst_146_ = v_snd_172_;
v_snd_147_ = v_snd_169_;
goto v___jp_145_;
}
}
else
{
uint8_t v___x_179_; 
lean_dec(v_snd_172_);
lean_dec(v_snd_169_);
lean_dec(v_fst_168_);
v___x_179_ = 0;
return v___x_179_;
}
}
v___jp_145_:
{
lean_object* v_fst_148_; lean_object* v_snd_149_; lean_object* v_fst_150_; lean_object* v_snd_151_; uint8_t v___x_152_; 
v_fst_148_ = lean_ctor_get(v_fst_146_, 0);
lean_inc(v_fst_148_);
v_snd_149_ = lean_ctor_get(v_fst_146_, 1);
lean_inc(v_snd_149_);
lean_dec_ref(v_fst_146_);
v_fst_150_ = lean_ctor_get(v_snd_147_, 0);
lean_inc(v_fst_150_);
v_snd_151_ = lean_ctor_get(v_snd_147_, 1);
lean_inc(v_snd_151_);
lean_dec_ref(v_snd_147_);
v___x_152_ = lean_int_dec_lt(v_snd_149_, v_snd_151_);
if (v___x_152_ == 0)
{
uint8_t v___x_153_; 
v___x_153_ = lean_int_dec_lt(v_snd_151_, v_snd_149_);
lean_dec(v_snd_149_);
lean_dec(v_snd_151_);
if (v___x_153_ == 0)
{
lean_object* v_amDigits_154_; lean_object* v_bmDigits_155_; uint8_t v___x_156_; 
lean_inc(v_fst_148_);
v_amDigits_154_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(v_fst_148_);
lean_inc(v_fst_150_);
v_bmDigits_155_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(v_fst_150_);
v___x_156_ = lean_nat_dec_lt(v_amDigits_154_, v_bmDigits_155_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_157_ = lean_unsigned_to_nat(10u);
v___x_158_ = lean_nat_sub(v_amDigits_154_, v_bmDigits_155_);
lean_dec(v_bmDigits_155_);
lean_dec(v_amDigits_154_);
v___x_159_ = lean_nat_pow(v___x_157_, v___x_158_);
lean_dec(v___x_158_);
v___x_160_ = lean_nat_mul(v_fst_150_, v___x_159_);
lean_dec(v___x_159_);
lean_dec(v_fst_150_);
v___x_161_ = lean_nat_dec_lt(v_fst_148_, v___x_160_);
lean_dec(v___x_160_);
lean_dec(v_fst_148_);
return v___x_161_;
}
else
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_162_ = lean_unsigned_to_nat(10u);
v___x_163_ = lean_nat_sub(v_bmDigits_155_, v_amDigits_154_);
lean_dec(v_amDigits_154_);
lean_dec(v_bmDigits_155_);
v___x_164_ = lean_nat_pow(v___x_162_, v___x_163_);
lean_dec(v___x_163_);
v___x_165_ = lean_nat_mul(v_fst_148_, v___x_164_);
lean_dec(v___x_164_);
lean_dec(v_fst_148_);
v___x_166_ = lean_nat_dec_lt(v___x_165_, v_fst_150_);
lean_dec(v_fst_150_);
lean_dec(v___x_165_);
return v___x_166_;
}
}
else
{
lean_dec(v_fst_150_);
lean_dec(v_fst_148_);
return v___x_152_;
}
}
else
{
lean_dec(v_snd_151_);
lean_dec(v_fst_150_);
lean_dec(v_snd_149_);
lean_dec(v_fst_148_);
return v___x_152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_lt___boxed(lean_object* v_a_180_, lean_object* v_b_181_){
_start:
{
uint8_t v_res_182_; lean_object* v_r_183_; 
v_res_182_ = l_Lean_JsonNumber_lt(v_a_180_, v_b_181_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
static lean_object* _init_l_Lean_JsonNumber_ltProp(void){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = lean_box(0);
return v___x_184_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonNumber_instDecidableLt(lean_object* v_a_185_, lean_object* v_b_186_){
_start:
{
uint8_t v___x_187_; 
v___x_187_ = l_Lean_JsonNumber_lt(v_a_185_, v_b_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instDecidableLt___boxed(lean_object* v_a_188_, lean_object* v_b_189_){
_start:
{
uint8_t v_res_190_; lean_object* v_r_191_; 
v_res_190_ = l_Lean_JsonNumber_instDecidableLt(v_a_188_, v_b_189_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonNumber_instOrd___lam__0(lean_object* v_x_192_, lean_object* v_y_193_){
_start:
{
uint8_t v___x_194_; 
lean_inc_ref(v_y_193_);
lean_inc_ref(v_x_192_);
v___x_194_ = l_Lean_JsonNumber_lt(v_x_192_, v_y_193_);
if (v___x_194_ == 0)
{
uint8_t v___x_195_; 
v___x_195_ = l_Lean_JsonNumber_lt(v_y_193_, v_x_192_);
if (v___x_195_ == 0)
{
uint8_t v___x_196_; 
v___x_196_ = 1;
return v___x_196_;
}
else
{
uint8_t v___x_197_; 
v___x_197_ = 2;
return v___x_197_;
}
}
else
{
uint8_t v___x_198_; 
lean_dec_ref(v_y_193_);
lean_dec_ref(v_x_192_);
v___x_198_ = 0;
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOrd___lam__0___boxed(lean_object* v_x_199_, lean_object* v_y_200_){
_start:
{
uint8_t v_res_201_; lean_object* v_r_202_; 
v_res_201_ = l_Lean_JsonNumber_instOrd___lam__0(v_x_199_, v_y_200_);
v_r_202_ = lean_box(v_res_201_);
return v_r_202_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0(lean_object* v_s_205_, lean_object* v_begPos_206_, lean_object* v_i_207_){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_208_ = lean_unsigned_to_nat(1u);
v___x_209_ = lean_nat_add(v_begPos_206_, v___x_208_);
v___x_210_ = lean_nat_dec_le(v___x_209_, v_i_207_);
lean_dec(v___x_209_);
if (v___x_210_ == 0)
{
return v_i_207_;
}
else
{
lean_object* v_i_x27_211_; uint8_t v___y_213_; uint8_t v___y_216_; uint32_t v_c_217_; uint32_t v___x_218_; uint8_t v___x_219_; 
v_i_x27_211_ = lean_string_utf8_prev(v_s_205_, v_i_207_);
v_c_217_ = lean_string_utf8_get(v_s_205_, v_i_x27_211_);
v___x_218_ = 48;
v___x_219_ = lean_uint32_dec_eq(v_c_217_, v___x_218_);
if (v___x_219_ == 0)
{
v___y_216_ = v___x_210_;
goto v___jp_215_;
}
else
{
uint8_t v___x_220_; 
v___x_220_ = 0;
v___y_216_ = v___x_220_;
goto v___jp_215_;
}
v___jp_212_:
{
if (v___y_213_ == 0)
{
lean_dec(v_i_207_);
v_i_207_ = v_i_x27_211_;
goto _start;
}
else
{
lean_dec(v_i_x27_211_);
return v_i_207_;
}
}
v___jp_215_:
{
if (v___x_210_ == 0)
{
v___y_213_ = v___x_210_;
goto v___jp_212_;
}
else
{
v___y_213_ = v___y_216_;
goto v___jp_212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0___boxed(lean_object* v_s_221_, lean_object* v_begPos_222_, lean_object* v_i_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0(v_s_221_, v_begPos_222_, v_i_223_);
lean_dec(v_begPos_222_);
lean_dec_ref(v_s_221_);
return v_res_224_;
}
}
static lean_object* _init_l_Lean_JsonNumber_toString___closed__3(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_unsigned_to_nat(9u);
v___x_229_ = lean_nat_to_int(v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_toString(lean_object* v_x_231_){
_start:
{
lean_object* v___y_233_; lean_object* v___y_234_; lean_object* v___y_235_; lean_object* v___y_236_; lean_object* v_mantissa_242_; lean_object* v_exponent_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v_mantissa_242_ = lean_ctor_get(v_x_231_, 0);
lean_inc(v_mantissa_242_);
v_exponent_243_ = lean_ctor_get(v_x_231_, 1);
lean_inc(v_exponent_243_);
lean_dec_ref(v_x_231_);
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = lean_nat_dec_eq(v_exponent_243_, v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; lean_object* v___y_248_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v___y_281_; uint8_t v___x_290_; 
v___x_246_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v___x_290_ = lean_int_dec_le(v___x_246_, v_mantissa_242_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; 
v___x_291_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__4));
v___y_281_ = v___x_291_;
goto v___jp_280_;
}
else
{
lean_object* v___x_292_; 
v___x_292_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__2));
v___y_281_ = v___x_292_;
goto v___jp_280_;
}
v___jp_247_:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v_e_259_; lean_object* v_right_260_; uint8_t v___x_261_; 
v___x_253_ = lean_nat_add(v___y_250_, v___y_251_);
lean_dec(v___y_251_);
lean_dec(v___y_250_);
v___x_254_ = l_Nat_reprFast(v___x_253_);
v___x_255_ = lean_string_utf8_byte_size(v___x_254_);
lean_inc_ref(v___x_254_);
v___x_256_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_256_, 0, v___x_254_);
lean_ctor_set(v___x_256_, 1, v___x_244_);
lean_ctor_set(v___x_256_, 2, v___x_255_);
v___x_257_ = lean_unsigned_to_nat(1u);
v___x_258_ = l_Substring_Raw_nextn(v___x_256_, v___x_257_, v___x_244_);
lean_dec_ref_known(v___x_256_, 3);
v_e_259_ = l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0(v___x_254_, v___x_258_, v___x_255_);
v_right_260_ = lean_string_utf8_extract(v___x_254_, v___x_258_, v_e_259_);
lean_dec(v_e_259_);
lean_dec(v___x_258_);
lean_dec_ref(v___x_254_);
v___x_261_ = lean_int_dec_eq(v___y_248_, v___x_246_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_262_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__1));
v___x_263_ = l_Int_repr(v___y_248_);
lean_dec(v___y_248_);
v___x_264_ = lean_string_append(v___x_262_, v___x_263_);
lean_dec_ref(v___x_263_);
v___y_233_ = v___y_249_;
v___y_234_ = v___y_252_;
v___y_235_ = v_right_260_;
v___y_236_ = v___x_264_;
goto v___jp_232_;
}
else
{
lean_object* v___x_265_; 
lean_dec(v___y_248_);
v___x_265_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__2));
v___y_233_ = v___y_249_;
v___y_234_ = v___y_252_;
v___y_235_ = v_right_260_;
v___y_236_ = v___x_265_;
goto v___jp_232_;
}
}
v___jp_266_:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v_e_x27_273_; lean_object* v___x_274_; lean_object* v_left_275_; lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_270_ = lean_unsigned_to_nat(10u);
v___x_271_ = lean_nat_abs(v___y_269_);
v___x_272_ = lean_nat_sub(v_exponent_243_, v___x_271_);
lean_dec(v___x_271_);
lean_dec(v_exponent_243_);
v_e_x27_273_ = lean_nat_pow(v___x_270_, v___x_272_);
lean_dec(v___x_272_);
v___x_274_ = lean_nat_div(v___y_268_, v_e_x27_273_);
v_left_275_ = l_Nat_reprFast(v___x_274_);
v___x_276_ = lean_nat_mod(v___y_268_, v_e_x27_273_);
lean_dec(v___y_268_);
v___x_277_ = lean_nat_dec_eq(v___x_276_, v___x_244_);
if (v___x_277_ == 0)
{
v___y_248_ = v___y_269_;
v___y_249_ = v___y_267_;
v___y_250_ = v_e_x27_273_;
v___y_251_ = v___x_276_;
v___y_252_ = v_left_275_;
goto v___jp_247_;
}
else
{
uint8_t v___x_278_; 
v___x_278_ = lean_int_dec_eq(v___y_269_, v___x_246_);
if (v___x_278_ == 0)
{
v___y_248_ = v___y_269_;
v___y_249_ = v___y_267_;
v___y_250_ = v_e_x27_273_;
v___y_251_ = v___x_276_;
v___y_252_ = v_left_275_;
goto v___jp_247_;
}
else
{
lean_object* v___x_279_; 
lean_dec(v___x_276_);
lean_dec(v_e_x27_273_);
lean_dec(v___y_269_);
lean_inc_ref(v___y_267_);
v___x_279_ = lean_string_append(v___y_267_, v_left_275_);
lean_dec_ref(v_left_275_);
return v___x_279_;
}
}
}
v___jp_280_:
{
lean_object* v_m_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v_exp_288_; uint8_t v___x_289_; 
v_m_282_ = lean_nat_abs(v_mantissa_242_);
lean_dec(v_mantissa_242_);
v___x_283_ = lean_obj_once(&l_Lean_JsonNumber_toString___closed__3, &l_Lean_JsonNumber_toString___closed__3_once, _init_l_Lean_JsonNumber_toString___closed__3);
lean_inc(v_m_282_);
v___x_284_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(v_m_282_);
v___x_285_ = lean_nat_to_int(v___x_284_);
v___x_286_ = lean_int_add(v___x_283_, v___x_285_);
lean_dec(v___x_285_);
lean_inc(v_exponent_243_);
v___x_287_ = lean_nat_to_int(v_exponent_243_);
v_exp_288_ = lean_int_sub(v___x_286_, v___x_287_);
lean_dec(v___x_287_);
lean_dec(v___x_286_);
v___x_289_ = lean_int_dec_lt(v_exp_288_, v___x_246_);
if (v___x_289_ == 0)
{
lean_dec(v_exp_288_);
v___y_267_ = v___y_281_;
v___y_268_ = v_m_282_;
v___y_269_ = v___x_246_;
goto v___jp_266_;
}
else
{
v___y_267_ = v___y_281_;
v___y_268_ = v_m_282_;
v___y_269_ = v_exp_288_;
goto v___jp_266_;
}
}
}
else
{
lean_object* v___x_293_; 
lean_dec(v_exponent_243_);
v___x_293_ = l_Int_repr(v_mantissa_242_);
lean_dec(v_mantissa_242_);
return v___x_293_;
}
v___jp_232_:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
lean_inc_ref(v___y_233_);
v___x_237_ = lean_string_append(v___y_233_, v___y_234_);
lean_dec_ref(v___y_234_);
v___x_238_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__0));
v___x_239_ = lean_string_append(v___x_237_, v___x_238_);
v___x_240_ = lean_string_append(v___x_239_, v___y_235_);
lean_dec_ref(v___y_235_);
v___x_241_ = lean_string_append(v___x_240_, v___y_236_);
lean_dec_ref(v___y_236_);
return v___x_241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftl(lean_object* v_x_294_, lean_object* v_x_295_){
_start:
{
lean_object* v_mantissa_296_; lean_object* v_exponent_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_310_; 
v_mantissa_296_ = lean_ctor_get(v_x_294_, 0);
v_exponent_297_ = lean_ctor_get(v_x_294_, 1);
v_isSharedCheck_310_ = !lean_is_exclusive(v_x_294_);
if (v_isSharedCheck_310_ == 0)
{
v___x_299_ = v_x_294_;
v_isShared_300_ = v_isSharedCheck_310_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_exponent_297_);
lean_inc(v_mantissa_296_);
lean_dec(v_x_294_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_310_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_308_; 
v___x_301_ = lean_unsigned_to_nat(10u);
v___x_302_ = lean_nat_sub(v_x_295_, v_exponent_297_);
v___x_303_ = lean_nat_pow(v___x_301_, v___x_302_);
lean_dec(v___x_302_);
v___x_304_ = lean_nat_to_int(v___x_303_);
v___x_305_ = lean_int_mul(v_mantissa_296_, v___x_304_);
lean_dec(v___x_304_);
lean_dec(v_mantissa_296_);
v___x_306_ = lean_nat_sub(v_exponent_297_, v_x_295_);
lean_dec(v_exponent_297_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 1, v___x_306_);
lean_ctor_set(v___x_299_, 0, v___x_305_);
v___x_308_ = v___x_299_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v___x_306_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftl___boxed(lean_object* v_x_311_, lean_object* v_x_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_JsonNumber_shiftl(v_x_311_, v_x_312_);
lean_dec(v_x_312_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftr(lean_object* v_x_314_, lean_object* v_x_315_){
_start:
{
lean_object* v_mantissa_316_; lean_object* v_exponent_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_325_; 
v_mantissa_316_ = lean_ctor_get(v_x_314_, 0);
v_exponent_317_ = lean_ctor_get(v_x_314_, 1);
v_isSharedCheck_325_ = !lean_is_exclusive(v_x_314_);
if (v_isSharedCheck_325_ == 0)
{
v___x_319_ = v_x_314_;
v_isShared_320_ = v_isSharedCheck_325_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_exponent_317_);
lean_inc(v_mantissa_316_);
lean_dec(v_x_314_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_325_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_321_ = lean_nat_add(v_exponent_317_, v_x_315_);
lean_dec(v_exponent_317_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 1, v___x_321_);
v___x_323_ = v___x_319_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_mantissa_316_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v___x_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftr___boxed(lean_object* v_x_326_, lean_object* v_x_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_JsonNumber_shiftr(v_x_326_, v_x_327_);
lean_dec(v_x_327_);
return v_res_328_;
}
}
static lean_object* _init_l_Lean_JsonNumber_instRepr___lam__0___closed__4(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = ((lean_object*)(l_Lean_JsonNumber_instRepr___lam__0___closed__0));
v___x_337_ = lean_string_length(v___x_336_);
return v___x_337_;
}
}
static lean_object* _init_l_Lean_JsonNumber_instRepr___lam__0___closed__5(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lean_obj_once(&l_Lean_JsonNumber_instRepr___lam__0___closed__4, &l_Lean_JsonNumber_instRepr___lam__0___closed__4_once, _init_l_Lean_JsonNumber_instRepr___lam__0___closed__4);
v___x_339_ = lean_nat_to_int(v___x_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instRepr___lam__0(lean_object* v_x_344_, lean_object* v_x_345_){
_start:
{
lean_object* v_mantissa_346_; lean_object* v_exponent_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_376_; 
v_mantissa_346_ = lean_ctor_get(v_x_344_, 0);
v_exponent_347_ = lean_ctor_get(v_x_344_, 1);
v_isSharedCheck_376_ = !lean_is_exclusive(v_x_344_);
if (v_isSharedCheck_376_ == 0)
{
v___x_349_ = v_x_344_;
v_isShared_350_ = v_isSharedCheck_376_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_exponent_347_);
lean_inc(v_mantissa_346_);
lean_dec(v_x_344_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_376_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___y_352_; lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_368_ = lean_unsigned_to_nat(0u);
v___x_369_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v___x_370_ = lean_int_dec_lt(v_mantissa_346_, v___x_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = l_Int_repr(v_mantissa_346_);
lean_dec(v_mantissa_346_);
v___x_372_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
v___y_352_ = v___x_372_;
goto v___jp_351_;
}
else
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_373_ = l_Int_repr(v_mantissa_346_);
lean_dec(v_mantissa_346_);
v___x_374_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
v___x_375_ = l_Repr_addAppParen(v___x_374_, v___x_368_);
v___y_352_ = v___x_375_;
goto v___jp_351_;
}
v___jp_351_:
{
lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_353_ = ((lean_object*)(l_Lean_JsonNumber_instRepr___lam__0___closed__2));
if (v_isShared_350_ == 0)
{
lean_ctor_set_tag(v___x_349_, 5);
lean_ctor_set(v___x_349_, 1, v___x_353_);
lean_ctor_set(v___x_349_, 0, v___y_352_);
v___x_355_ = v___x_349_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___y_352_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v___x_353_);
v___x_355_ = v_reuseFailAlloc_367_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; lean_object* v___x_366_; 
v___x_356_ = l_Nat_reprFast(v_exponent_347_);
v___x_357_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
v___x_358_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_355_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
v___x_359_ = lean_obj_once(&l_Lean_JsonNumber_instRepr___lam__0___closed__5, &l_Lean_JsonNumber_instRepr___lam__0___closed__5_once, _init_l_Lean_JsonNumber_instRepr___lam__0___closed__5);
v___x_360_ = ((lean_object*)(l_Lean_JsonNumber_instRepr___lam__0___closed__6));
v___x_361_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
lean_ctor_set(v___x_361_, 1, v___x_358_);
v___x_362_ = ((lean_object*)(l_Lean_JsonNumber_instRepr___lam__0___closed__7));
v___x_363_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_361_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___x_364_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_359_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
v___x_365_ = 0;
v___x_366_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_366_, 0, v___x_364_);
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*1, v___x_365_);
return v___x_366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instRepr___lam__0___boxed(lean_object* v_x_377_, lean_object* v_x_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_JsonNumber_instRepr___lam__0(v_x_377_, v_x_378_);
lean_dec(v_x_378_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOfScientific___lam__0(lean_object* v_mantissa_382_, uint8_t v_exponentSign_383_, lean_object* v_decimalExponent_384_){
_start:
{
if (v_exponentSign_383_ == 0)
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_385_ = lean_unsigned_to_nat(10u);
v___x_386_ = lean_nat_pow(v___x_385_, v_decimalExponent_384_);
lean_dec(v_decimalExponent_384_);
v___x_387_ = lean_nat_mul(v_mantissa_382_, v___x_386_);
lean_dec(v___x_386_);
lean_dec(v_mantissa_382_);
v___x_388_ = lean_nat_to_int(v___x_387_);
v___x_389_ = lean_unsigned_to_nat(0u);
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_388_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
return v___x_390_;
}
else
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_nat_to_int(v_mantissa_382_);
v___x_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v_decimalExponent_384_);
return v___x_392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOfScientific___lam__0___boxed(lean_object* v_mantissa_393_, lean_object* v_exponentSign_394_, lean_object* v_decimalExponent_395_){
_start:
{
uint8_t v_exponentSign_boxed_396_; lean_object* v_res_397_; 
v_exponentSign_boxed_396_ = lean_unbox(v_exponentSign_394_);
v_res_397_ = l_Lean_JsonNumber_instOfScientific___lam__0(v_mantissa_393_, v_exponentSign_boxed_396_, v_decimalExponent_395_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instNeg___lam__0(lean_object* v_jn_400_){
_start:
{
lean_object* v_mantissa_401_; lean_object* v_exponent_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_410_; 
v_mantissa_401_ = lean_ctor_get(v_jn_400_, 0);
v_exponent_402_ = lean_ctor_get(v_jn_400_, 1);
v_isSharedCheck_410_ = !lean_is_exclusive(v_jn_400_);
if (v_isSharedCheck_410_ == 0)
{
v___x_404_ = v_jn_400_;
v_isShared_405_ = v_isSharedCheck_410_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_exponent_402_);
lean_inc(v_mantissa_401_);
lean_dec(v_jn_400_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_410_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_406_ = lean_int_neg(v_mantissa_401_);
lean_dec(v_mantissa_401_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v___x_406_);
v___x_408_ = v___x_404_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_exponent_402_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
static lean_object* _init_l_Lean_JsonNumber_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = lean_unsigned_to_nat(0u);
v___x_414_ = l_Lean_JsonNumber_fromNat(v___x_413_);
return v___x_414_;
}
}
static lean_object* _init_l_Lean_JsonNumber_instInhabited(void){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = lean_obj_once(&l_Lean_JsonNumber_instInhabited___closed__0, &l_Lean_JsonNumber_instInhabited___closed__0_once, _init_l_Lean_JsonNumber_instInhabited___closed__0);
return v___x_415_;
}
}
static double _init_l_Lean_JsonNumber_toFloat___closed__0(void){
_start:
{
lean_object* v___x_416_; uint8_t v___x_417_; lean_object* v___x_418_; double v___x_419_; 
v___x_416_ = lean_unsigned_to_nat(1u);
v___x_417_ = 1;
v___x_418_ = lean_unsigned_to_nat(10u);
v___x_419_ = l_Float_ofScientific(v___x_418_, v___x_417_, v___x_416_);
return v___x_419_;
}
}
static double _init_l_Lean_JsonNumber_toFloat___closed__1(void){
_start:
{
double v___x_420_; double v___x_421_; 
v___x_420_ = lean_float_once(&l_Lean_JsonNumber_toFloat___closed__0, &l_Lean_JsonNumber_toFloat___closed__0_once, _init_l_Lean_JsonNumber_toFloat___closed__0);
v___x_421_ = lean_float_negate(v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT double l_Lean_JsonNumber_toFloat(lean_object* v_x_422_){
_start:
{
lean_object* v_mantissa_423_; lean_object* v_exponent_424_; double v___y_426_; lean_object* v___x_431_; uint8_t v___x_432_; 
v_mantissa_423_ = lean_ctor_get(v_x_422_, 0);
lean_inc(v_mantissa_423_);
v_exponent_424_ = lean_ctor_get(v_x_422_, 1);
lean_inc(v_exponent_424_);
lean_dec_ref(v_x_422_);
v___x_431_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v___x_432_ = lean_int_dec_le(v___x_431_, v_mantissa_423_);
if (v___x_432_ == 0)
{
double v___x_433_; 
v___x_433_ = lean_float_once(&l_Lean_JsonNumber_toFloat___closed__1, &l_Lean_JsonNumber_toFloat___closed__1_once, _init_l_Lean_JsonNumber_toFloat___closed__1);
v___y_426_ = v___x_433_;
goto v___jp_425_;
}
else
{
lean_object* v___x_434_; lean_object* v___x_435_; double v___x_436_; 
v___x_434_ = lean_unsigned_to_nat(10u);
v___x_435_ = lean_unsigned_to_nat(1u);
v___x_436_ = l_Float_ofScientific(v___x_434_, v___x_432_, v___x_435_);
v___y_426_ = v___x_436_;
goto v___jp_425_;
}
v___jp_425_:
{
lean_object* v___x_427_; uint8_t v___x_428_; double v___x_429_; double v___x_430_; 
v___x_427_ = lean_nat_abs(v_mantissa_423_);
lean_dec(v_mantissa_423_);
v___x_428_ = 1;
v___x_429_ = l_Float_ofScientific(v___x_427_, v___x_428_, v_exponent_424_);
v___x_430_ = lean_float_mul(v___y_426_, v___x_429_);
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_toFloat___boxed(lean_object* v_x_437_){
_start:
{
double v_res_438_; lean_object* v_r_439_; 
v_res_438_ = l_Lean_JsonNumber_toFloat(v_x_437_);
v_r_439_ = lean_box_float(v_res_438_);
return v_r_439_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21_spec__0(lean_object* v_msg_440_){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = l_Lean_JsonNumber_instInhabited;
v___x_442_ = lean_panic_fn_borrowed(v___x_441_, v_msg_440_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(double v_x_446_){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = lean_float_to_string(v_x_446_);
v___x_448_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v___x_447_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_449_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0));
v___x_450_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__1));
v___x_451_ = lean_unsigned_to_nat(164u);
v___x_452_ = lean_unsigned_to_nat(12u);
v___x_453_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__2));
v___x_454_ = lean_string_append(v___x_453_, v___x_447_);
lean_dec_ref(v___x_447_);
v___x_455_ = l_mkPanicMessageWithDecl(v___x_449_, v___x_450_, v___x_451_, v___x_452_, v___x_454_);
lean_dec_ref(v___x_454_);
v___x_456_ = l_panic___at___00__private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21_spec__0(v___x_455_);
return v___x_456_;
}
else
{
lean_object* v_val_457_; lean_object* v_snd_458_; lean_object* v_fst_459_; uint8_t v___x_460_; 
lean_dec_ref(v___x_447_);
v_val_457_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_val_457_);
lean_dec_ref_known(v___x_448_, 1);
v_snd_458_ = lean_ctor_get(v_val_457_, 1);
lean_inc(v_snd_458_);
v_fst_459_ = lean_ctor_get(v_snd_458_, 0);
v___x_460_ = lean_unbox(v_fst_459_);
if (v___x_460_ == 0)
{
lean_object* v_fst_461_; lean_object* v_snd_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_474_; 
v_fst_461_ = lean_ctor_get(v_val_457_, 0);
lean_inc(v_fst_461_);
lean_dec(v_val_457_);
v_snd_462_ = lean_ctor_get(v_snd_458_, 1);
v_isSharedCheck_474_ = !lean_is_exclusive(v_snd_458_);
if (v_isSharedCheck_474_ == 0)
{
lean_object* v_unused_475_; 
v_unused_475_ = lean_ctor_get(v_snd_458_, 0);
lean_dec(v_unused_475_);
v___x_464_ = v_snd_458_;
v_isShared_465_ = v_isSharedCheck_474_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_snd_462_);
lean_dec(v_snd_458_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_474_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_466_ = lean_unsigned_to_nat(10u);
v___x_467_ = lean_nat_pow(v___x_466_, v_snd_462_);
lean_dec(v_snd_462_);
v___x_468_ = lean_nat_mul(v_fst_461_, v___x_467_);
lean_dec(v___x_467_);
lean_dec(v_fst_461_);
v___x_469_ = lean_nat_to_int(v___x_468_);
v___x_470_ = lean_unsigned_to_nat(0u);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 1, v___x_470_);
lean_ctor_set(v___x_464_, 0, v___x_469_);
v___x_472_ = v___x_464_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v___x_470_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
else
{
lean_object* v_fst_476_; lean_object* v_snd_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_485_; 
v_fst_476_ = lean_ctor_get(v_val_457_, 0);
lean_inc(v_fst_476_);
lean_dec(v_val_457_);
v_snd_477_ = lean_ctor_get(v_snd_458_, 1);
v_isSharedCheck_485_ = !lean_is_exclusive(v_snd_458_);
if (v_isSharedCheck_485_ == 0)
{
lean_object* v_unused_486_; 
v_unused_486_ = lean_ctor_get(v_snd_458_, 0);
lean_dec(v_unused_486_);
v___x_479_ = v_snd_458_;
v_isShared_480_ = v_isSharedCheck_485_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_snd_477_);
lean_dec(v_snd_458_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_485_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_481_ = lean_nat_to_int(v_fst_476_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_481_);
v___x_483_ = v___x_479_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_481_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_snd_477_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___boxed(lean_object* v_x_487_){
_start:
{
double v_x_boxed_488_; lean_object* v_res_489_; 
v_x_boxed_488_ = lean_unbox_float(v_x_487_);
lean_dec_ref(v_x_487_);
v_res_489_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(v_x_boxed_488_);
return v_res_489_;
}
}
static double _init_l_Lean_JsonNumber_fromFloat_x3f___closed__0(void){
_start:
{
lean_object* v___x_490_; uint8_t v___x_491_; lean_object* v___x_492_; double v___x_493_; 
v___x_490_ = lean_unsigned_to_nat(1u);
v___x_491_ = 1;
v___x_492_ = lean_unsigned_to_nat(0u);
v___x_493_ = l_Float_ofScientific(v___x_492_, v___x_491_, v___x_490_);
return v___x_493_;
}
}
static lean_object* _init_l_Lean_JsonNumber_fromFloat_x3f___closed__1(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = lean_obj_once(&l_Lean_JsonNumber_instInhabited___closed__0, &l_Lean_JsonNumber_instInhabited___closed__0_once, _init_l_Lean_JsonNumber_instInhabited___closed__0);
v___x_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
}
static double _init_l_Lean_JsonNumber_fromFloat_x3f___closed__2(void){
_start:
{
lean_object* v___x_496_; double v___x_497_; 
v___x_496_ = lean_unsigned_to_nat(0u);
v___x_497_ = lean_float_of_nat(v___x_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_fromFloat_x3f(double v_x_507_){
_start:
{
uint8_t v___x_508_; 
v___x_508_ = lean_float_isnan(v_x_507_);
if (v___x_508_ == 0)
{
uint8_t v___x_509_; 
v___x_509_ = lean_float_isinf(v_x_507_);
if (v___x_509_ == 0)
{
double v___x_510_; uint8_t v___x_511_; 
v___x_510_ = lean_float_once(&l_Lean_JsonNumber_fromFloat_x3f___closed__0, &l_Lean_JsonNumber_fromFloat_x3f___closed__0_once, _init_l_Lean_JsonNumber_fromFloat_x3f___closed__0);
v___x_511_ = lean_float_beq(v_x_507_, v___x_510_);
if (v___x_511_ == 0)
{
uint8_t v___x_512_; 
v___x_512_ = lean_float_decLt(v_x_507_, v___x_510_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(v_x_507_);
v___x_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
return v___x_514_;
}
else
{
double v___x_515_; lean_object* v___x_516_; lean_object* v_mantissa_517_; lean_object* v_exponent_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_527_; 
v___x_515_ = lean_float_negate(v_x_507_);
v___x_516_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(v___x_515_);
v_mantissa_517_ = lean_ctor_get(v___x_516_, 0);
v_exponent_518_ = lean_ctor_get(v___x_516_, 1);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_527_ == 0)
{
v___x_520_ = v___x_516_;
v_isShared_521_ = v_isSharedCheck_527_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_exponent_518_);
lean_inc(v_mantissa_517_);
lean_dec(v___x_516_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_527_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; lean_object* v___x_524_; 
v___x_522_ = lean_int_neg(v_mantissa_517_);
lean_dec(v_mantissa_517_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_522_);
v___x_524_ = v___x_520_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_522_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v_exponent_518_);
v___x_524_ = v_reuseFailAlloc_526_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_525_; 
v___x_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
return v___x_525_;
}
}
}
}
else
{
lean_object* v___x_528_; 
v___x_528_ = lean_obj_once(&l_Lean_JsonNumber_fromFloat_x3f___closed__1, &l_Lean_JsonNumber_fromFloat_x3f___closed__1_once, _init_l_Lean_JsonNumber_fromFloat_x3f___closed__1);
return v___x_528_;
}
}
else
{
double v___x_529_; uint8_t v___x_530_; 
v___x_529_ = lean_float_once(&l_Lean_JsonNumber_fromFloat_x3f___closed__2, &l_Lean_JsonNumber_fromFloat_x3f___closed__2_once, _init_l_Lean_JsonNumber_fromFloat_x3f___closed__2);
v___x_530_ = lean_float_decLt(v___x_529_, v_x_507_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; 
v___x_531_ = ((lean_object*)(l_Lean_JsonNumber_fromFloat_x3f___closed__4));
return v___x_531_;
}
else
{
lean_object* v___x_532_; 
v___x_532_ = ((lean_object*)(l_Lean_JsonNumber_fromFloat_x3f___closed__6));
return v___x_532_;
}
}
}
else
{
lean_object* v___x_533_; 
v___x_533_ = ((lean_object*)(l_Lean_JsonNumber_fromFloat_x3f___closed__8));
return v___x_533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_fromFloat_x3f___boxed(lean_object* v_x_534_){
_start:
{
double v_x_boxed_535_; lean_object* v_res_536_; 
v_x_boxed_535_ = lean_unbox_float(v_x_534_);
lean_dec_ref(v_x_534_);
v_res_536_ = l_Lean_JsonNumber_fromFloat_x3f(v_x_boxed_535_);
return v_res_536_;
}
}
LEAN_EXPORT uint8_t l_Lean_strLt(lean_object* v_a_537_, lean_object* v_b_538_){
_start:
{
uint8_t v___x_539_; 
v___x_539_ = lean_string_dec_lt(v_a_537_, v_b_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_strLt___boxed(lean_object* v_a_540_, lean_object* v_b_541_){
_start:
{
uint8_t v_res_542_; lean_object* v_r_543_; 
v_res_542_ = l_Lean_strLt(v_a_540_, v_b_541_);
lean_dec_ref(v_b_541_);
lean_dec_ref(v_a_540_);
v_r_543_ = lean_box(v_res_542_);
return v_r_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorIdx___impl(lean_object* v_x_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = lean_obj_tag_nat(v_x_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorIdx___impl___boxed(lean_object* v_x_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_Json_ctorIdx___impl(v_x_546_);
lean_dec(v_x_546_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorElim___redArg(lean_object* v_t_548_, lean_object* v_k_549_){
_start:
{
switch(lean_obj_tag(v_t_548_))
{
case 0:
{
return v_k_549_;
}
case 1:
{
uint8_t v_b_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_b_550_ = lean_ctor_get_uint8(v_t_548_, 0);
lean_dec_ref_known(v_t_548_, 0);
v___x_551_ = lean_box(v_b_550_);
v___x_552_ = lean_apply_1(v_k_549_, v___x_551_);
return v___x_552_;
}
case 5:
{
lean_object* v_kvPairs_553_; lean_object* v___x_554_; 
v_kvPairs_553_ = lean_ctor_get(v_t_548_, 0);
lean_inc(v_kvPairs_553_);
lean_dec_ref_known(v_t_548_, 1);
v___x_554_ = lean_apply_1(v_k_549_, v_kvPairs_553_);
return v___x_554_;
}
default: 
{
lean_object* v_n_555_; lean_object* v___x_556_; 
v_n_555_ = lean_ctor_get(v_t_548_, 0);
lean_inc_ref(v_n_555_);
lean_dec(v_t_548_);
v___x_556_ = lean_apply_1(v_k_549_, v_n_555_);
return v___x_556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorElim(lean_object* v_motive__1_557_, lean_object* v_ctorIdx_558_, lean_object* v_t_559_, lean_object* v_h_560_, lean_object* v_k_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Lean_Json_ctorElim___redArg(v_t_559_, v_k_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorElim___boxed(lean_object* v_motive__1_563_, lean_object* v_ctorIdx_564_, lean_object* v_t_565_, lean_object* v_h_566_, lean_object* v_k_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_Json_ctorElim(v_motive__1_563_, v_ctorIdx_564_, v_t_565_, v_h_566_, v_k_567_);
lean_dec(v_ctorIdx_564_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_null_elim___redArg(lean_object* v_t_569_, lean_object* v_null_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Lean_Json_ctorElim___redArg(v_t_569_, v_null_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_null_elim(lean_object* v_motive__1_572_, lean_object* v_t_573_, lean_object* v_h_574_, lean_object* v_null_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_Json_ctorElim___redArg(v_t_573_, v_null_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_bool_elim___redArg(lean_object* v_t_577_, lean_object* v_bool_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_Json_ctorElim___redArg(v_t_577_, v_bool_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_bool_elim(lean_object* v_motive__1_580_, lean_object* v_t_581_, lean_object* v_h_582_, lean_object* v_bool_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Lean_Json_ctorElim___redArg(v_t_581_, v_bool_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_num_elim___redArg(lean_object* v_t_585_, lean_object* v_num_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_Json_ctorElim___redArg(v_t_585_, v_num_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_num_elim(lean_object* v_motive__1_588_, lean_object* v_t_589_, lean_object* v_h_590_, lean_object* v_num_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_Json_ctorElim___redArg(v_t_589_, v_num_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_str_elim___redArg(lean_object* v_t_593_, lean_object* v_str_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_Json_ctorElim___redArg(v_t_593_, v_str_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_str_elim(lean_object* v_motive__1_596_, lean_object* v_t_597_, lean_object* v_h_598_, lean_object* v_str_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_Json_ctorElim___redArg(v_t_597_, v_str_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_arr_elim___redArg(lean_object* v_t_601_, lean_object* v_arr_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_Json_ctorElim___redArg(v_t_601_, v_arr_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_arr_elim(lean_object* v_motive__1_604_, lean_object* v_t_605_, lean_object* v_h_606_, lean_object* v_arr_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_Json_ctorElim___redArg(v_t_605_, v_arr_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_obj_elim___redArg(lean_object* v_t_609_, lean_object* v_obj_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lean_Json_ctorElim___redArg(v_t_609_, v_obj_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_obj_elim(lean_object* v_motive__1_612_, lean_object* v_t_613_, lean_object* v_h_614_, lean_object* v_obj_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_Json_ctorElim___redArg(v_t_613_, v_obj_615_);
return v___x_616_;
}
}
static lean_object* _init_l_Lean_instInhabitedJson_default(void){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = lean_box(0);
return v___x_617_;
}
}
static lean_object* _init_l_Lean_instInhabitedJson(void){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = lean_box(0);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(lean_object* v_init_619_, lean_object* v_x_620_){
_start:
{
if (lean_obj_tag(v_x_620_) == 0)
{
lean_object* v_l_621_; lean_object* v_r_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v_l_621_ = lean_ctor_get(v_x_620_, 3);
v_r_622_ = lean_ctor_get(v_x_620_, 4);
v___x_623_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_619_, v_l_621_);
v___x_624_ = lean_unsigned_to_nat(1u);
v___x_625_ = lean_nat_add(v___x_623_, v___x_624_);
lean_dec(v___x_623_);
v_init_619_ = v___x_625_;
v_x_620_ = v_r_622_;
goto _start;
}
else
{
return v_init_619_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1___boxed(lean_object* v_init_627_, lean_object* v_x_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_627_, v_x_628_);
lean_dec(v_x_628_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(lean_object* v_t_630_, lean_object* v_k_631_){
_start:
{
if (lean_obj_tag(v_t_630_) == 0)
{
lean_object* v_k_632_; lean_object* v_v_633_; lean_object* v_l_634_; lean_object* v_r_635_; uint8_t v___x_636_; 
v_k_632_ = lean_ctor_get(v_t_630_, 1);
v_v_633_ = lean_ctor_get(v_t_630_, 2);
v_l_634_ = lean_ctor_get(v_t_630_, 3);
v_r_635_ = lean_ctor_get(v_t_630_, 4);
v___x_636_ = lean_string_compare(v_k_631_, v_k_632_);
switch(v___x_636_)
{
case 0:
{
v_t_630_ = v_l_634_;
goto _start;
}
case 1:
{
lean_object* v___x_638_; 
lean_inc(v_v_633_);
v___x_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_638_, 0, v_v_633_);
return v___x_638_;
}
default: 
{
v_t_630_ = v_r_635_;
goto _start;
}
}
}
else
{
lean_object* v___x_640_; 
v___x_640_ = lean_box(0);
return v___x_640_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg___boxed(lean_object* v_t_641_, lean_object* v_k_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_t_641_, v_k_642_);
lean_dec_ref(v_k_642_);
lean_dec(v_t_641_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(lean_object* v_szA_655_, lean_object* v_szB_656_, lean_object* v_kvPairs_657_, lean_object* v_init_658_, lean_object* v_x_659_){
_start:
{
if (lean_obj_tag(v_x_659_) == 0)
{
lean_object* v_k_660_; lean_object* v_v_661_; lean_object* v_l_662_; lean_object* v_r_663_; uint8_t v___x_664_; lean_object* v___x_665_; 
v_k_660_ = lean_ctor_get(v_x_659_, 1);
v_v_661_ = lean_ctor_get(v_x_659_, 2);
v_l_662_ = lean_ctor_get(v_x_659_, 3);
v_r_663_ = lean_ctor_get(v_x_659_, 4);
v___x_664_ = lean_nat_dec_eq(v_szA_655_, v_szB_656_);
v___x_665_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_szA_655_, v_szB_656_, v_kvPairs_657_, v_init_658_, v_l_662_);
if (lean_obj_tag(v___x_665_) == 0)
{
return v___x_665_;
}
else
{
lean_object* v___x_666_; lean_object* v___x_670_; 
lean_dec_ref_known(v___x_665_, 1);
v___x_666_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__0));
v___x_670_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_kvPairs_657_, v_k_660_);
if (lean_obj_tag(v___x_670_) == 0)
{
goto v___jp_667_;
}
else
{
lean_object* v_val_671_; uint8_t v___x_672_; 
v_val_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_val_671_);
lean_dec_ref_known(v___x_670_, 1);
v___x_672_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_v_661_, v_val_671_);
lean_dec(v_val_671_);
if (v___x_672_ == 0)
{
goto v___jp_667_;
}
else
{
v_init_658_ = v___x_666_;
v_x_659_ = v_r_663_;
goto _start;
}
}
v___jp_667_:
{
if (v___x_664_ == 0)
{
v_init_658_ = v___x_666_;
v_x_659_ = v_r_663_;
goto _start;
}
else
{
lean_object* v___x_669_; 
v___x_669_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__3));
return v___x_669_;
}
}
}
}
else
{
lean_object* v___x_674_; 
v___x_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_674_, 0, v_init_658_);
return v___x_674_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(lean_object* v_x_675_, lean_object* v_x_676_){
_start:
{
switch(lean_obj_tag(v_x_675_))
{
case 0:
{
if (lean_obj_tag(v_x_676_) == 0)
{
uint8_t v___x_677_; 
v___x_677_ = 1;
return v___x_677_;
}
else
{
uint8_t v___x_678_; 
v___x_678_ = 0;
return v___x_678_;
}
}
case 1:
{
if (lean_obj_tag(v_x_676_) == 1)
{
uint8_t v_b_679_; 
v_b_679_ = lean_ctor_get_uint8(v_x_676_, 0);
if (v_b_679_ == 0)
{
uint8_t v_b_680_; 
v_b_680_ = lean_ctor_get_uint8(v_x_675_, 0);
if (v_b_680_ == 0)
{
uint8_t v___x_681_; 
v___x_681_ = 1;
return v___x_681_;
}
else
{
return v_b_679_;
}
}
else
{
uint8_t v_b_682_; 
v_b_682_ = lean_ctor_get_uint8(v_x_675_, 0);
return v_b_682_;
}
}
else
{
uint8_t v___x_683_; 
v___x_683_ = 0;
return v___x_683_;
}
}
case 2:
{
if (lean_obj_tag(v_x_676_) == 2)
{
lean_object* v_n_684_; lean_object* v_n_685_; uint8_t v___x_686_; 
v_n_684_ = lean_ctor_get(v_x_675_, 0);
v_n_685_ = lean_ctor_get(v_x_676_, 0);
v___x_686_ = l_Lean_instDecidableEqJsonNumber_decEq(v_n_684_, v_n_685_);
return v___x_686_;
}
else
{
uint8_t v___x_687_; 
v___x_687_ = 0;
return v___x_687_;
}
}
case 3:
{
if (lean_obj_tag(v_x_676_) == 3)
{
lean_object* v_s_688_; lean_object* v_s_689_; uint8_t v___x_690_; 
v_s_688_ = lean_ctor_get(v_x_675_, 0);
v_s_689_ = lean_ctor_get(v_x_676_, 0);
v___x_690_ = lean_string_dec_eq(v_s_688_, v_s_689_);
return v___x_690_;
}
else
{
uint8_t v___x_691_; 
v___x_691_ = 0;
return v___x_691_;
}
}
case 4:
{
if (lean_obj_tag(v_x_676_) == 4)
{
lean_object* v_elems_692_; lean_object* v_elems_693_; lean_object* v___x_694_; lean_object* v___x_695_; uint8_t v___x_696_; 
v_elems_692_ = lean_ctor_get(v_x_675_, 0);
v_elems_693_ = lean_ctor_get(v_x_676_, 0);
v___x_694_ = lean_array_get_size(v_elems_692_);
v___x_695_ = lean_array_get_size(v_elems_693_);
v___x_696_ = lean_nat_dec_eq(v___x_694_, v___x_695_);
if (v___x_696_ == 0)
{
return v___x_696_;
}
else
{
uint8_t v___x_697_; 
v___x_697_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(v_elems_692_, v_elems_693_, v___x_694_);
return v___x_697_;
}
}
else
{
uint8_t v___x_698_; 
v___x_698_ = 0;
return v___x_698_;
}
}
default: 
{
if (lean_obj_tag(v_x_676_) == 5)
{
lean_object* v_kvPairs_699_; lean_object* v_kvPairs_700_; lean_object* v___x_701_; lean_object* v_szA_702_; lean_object* v_szB_703_; uint8_t v___x_704_; lean_object* v___y_706_; 
v_kvPairs_699_ = lean_ctor_get(v_x_675_, 0);
v_kvPairs_700_ = lean_ctor_get(v_x_676_, 0);
v___x_701_ = lean_unsigned_to_nat(0u);
v_szA_702_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v___x_701_, v_kvPairs_699_);
v_szB_703_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v___x_701_, v_kvPairs_700_);
v___x_704_ = lean_nat_dec_eq(v_szA_702_, v_szB_703_);
if (v___x_704_ == 0)
{
lean_dec(v_szB_703_);
lean_dec(v_szA_702_);
return v___x_704_;
}
else
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v_a_712_; 
v___x_710_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__0));
v___x_711_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_szA_702_, v_szB_703_, v_kvPairs_700_, v___x_710_, v_kvPairs_699_);
lean_dec(v_szB_703_);
lean_dec(v_szA_702_);
v_a_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref(v___x_711_);
v___y_706_ = v_a_712_;
goto v___jp_705_;
}
v___jp_705_:
{
lean_object* v_fst_707_; 
v_fst_707_ = lean_ctor_get(v___y_706_, 0);
lean_inc(v_fst_707_);
lean_dec_ref(v___y_706_);
if (lean_obj_tag(v_fst_707_) == 0)
{
return v___x_704_;
}
else
{
lean_object* v_val_708_; uint8_t v___x_709_; 
v_val_708_ = lean_ctor_get(v_fst_707_, 0);
lean_inc(v_val_708_);
lean_dec_ref_known(v_fst_707_, 1);
v___x_709_ = lean_unbox(v_val_708_);
lean_dec(v_val_708_);
return v___x_709_;
}
}
}
else
{
uint8_t v___x_713_; 
v___x_713_ = 0;
return v___x_713_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(lean_object* v_xs_714_, lean_object* v_ys_715_, lean_object* v_x_716_){
_start:
{
lean_object* v_zero_717_; uint8_t v_isZero_718_; 
v_zero_717_ = lean_unsigned_to_nat(0u);
v_isZero_718_ = lean_nat_dec_eq(v_x_716_, v_zero_717_);
if (v_isZero_718_ == 1)
{
lean_dec(v_x_716_);
return v_isZero_718_;
}
else
{
lean_object* v_one_719_; lean_object* v_n_720_; lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v_one_719_ = lean_unsigned_to_nat(1u);
v_n_720_ = lean_nat_sub(v_x_716_, v_one_719_);
lean_dec(v_x_716_);
v___x_721_ = lean_array_fget_borrowed(v_xs_714_, v_n_720_);
v___x_722_ = lean_array_fget_borrowed(v_ys_715_, v_n_720_);
v___x_723_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v___x_721_, v___x_722_);
if (v___x_723_ == 0)
{
lean_dec(v_n_720_);
return v___x_723_;
}
else
{
v_x_716_ = v_n_720_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg___boxed(lean_object* v_xs_725_, lean_object* v_ys_726_, lean_object* v_x_727_){
_start:
{
uint8_t v_res_728_; lean_object* v_r_729_; 
v_res_728_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(v_xs_725_, v_ys_726_, v_x_727_);
lean_dec_ref(v_ys_726_);
lean_dec_ref(v_xs_725_);
v_r_729_ = lean_box(v_res_728_);
return v_r_729_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___boxed(lean_object* v_szA_730_, lean_object* v_szB_731_, lean_object* v_kvPairs_732_, lean_object* v_init_733_, lean_object* v_x_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_szA_730_, v_szB_731_, v_kvPairs_732_, v_init_733_, v_x_734_);
lean_dec(v_x_734_);
lean_dec(v_kvPairs_732_);
lean_dec(v_szB_731_);
lean_dec(v_szA_730_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___boxed(lean_object* v_x_736_, lean_object* v_x_737_){
_start:
{
uint8_t v_res_738_; lean_object* v_r_739_; 
v_res_738_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_x_736_, v_x_737_);
lean_dec(v_x_737_);
lean_dec(v_x_736_);
v_r_739_ = lean_box(v_res_738_);
return v_r_739_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0(lean_object* v_xs_740_, lean_object* v_ys_741_, lean_object* v_hsz_742_, lean_object* v_x_743_, lean_object* v_x_744_){
_start:
{
uint8_t v___x_745_; 
v___x_745_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(v_xs_740_, v_ys_741_, v_x_743_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___boxed(lean_object* v_xs_746_, lean_object* v_ys_747_, lean_object* v_hsz_748_, lean_object* v_x_749_, lean_object* v_x_750_){
_start:
{
uint8_t v_res_751_; lean_object* v_r_752_; 
v_res_751_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0(v_xs_746_, v_ys_747_, v_hsz_748_, v_x_749_, v_x_750_);
lean_dec_ref(v_ys_747_);
lean_dec_ref(v_xs_746_);
v_r_752_ = lean_box(v_res_751_);
return v_r_752_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1(lean_object* v_init_753_, lean_object* v_t_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_753_, v_t_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___boxed(lean_object* v_init_756_, lean_object* v_t_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1(v_init_756_, v_t_757_);
lean_dec(v_t_757_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2(lean_object* v_00_u03b4_759_, lean_object* v_t_760_, lean_object* v_k_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_t_760_, v_k_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___boxed(lean_object* v_00_u03b4_763_, lean_object* v_t_764_, lean_object* v_k_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2(v_00_u03b4_763_, v_t_764_, v_k_765_);
lean_dec_ref(v_k_765_);
lean_dec(v_t_764_);
return v_res_766_;
}
}
LEAN_EXPORT uint8_t l_Lean_Json_instBEq___private__1(lean_object* v_a_767_, lean_object* v_a_768_){
_start:
{
uint8_t v___x_769_; 
v___x_769_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_a_767_, v_a_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instBEq___private__1___boxed(lean_object* v_a_770_, lean_object* v_a_771_){
_start:
{
uint8_t v_res_772_; lean_object* v_r_773_; 
v_res_772_ = l_Lean_Json_instBEq___private__1(v_a_770_, v_a_771_);
lean_dec(v_a_771_);
lean_dec(v_a_770_);
v_r_773_ = lean_box(v_res_772_);
return v_r_773_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(lean_object* v_as_776_, size_t v_i_777_, size_t v_stop_778_, uint64_t v_b_779_){
_start:
{
uint8_t v___x_780_; 
v___x_780_ = lean_usize_dec_eq(v_i_777_, v_stop_778_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; uint64_t v___x_782_; uint64_t v___x_783_; size_t v___x_784_; size_t v___x_785_; 
v___x_781_ = lean_array_uget_borrowed(v_as_776_, v_i_777_);
v___x_782_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v___x_781_);
v___x_783_ = lean_uint64_mix_hash(v_b_779_, v___x_782_);
v___x_784_ = ((size_t)1ULL);
v___x_785_ = lean_usize_add(v_i_777_, v___x_784_);
v_i_777_ = v___x_785_;
v_b_779_ = v___x_783_;
goto _start;
}
else
{
return v_b_779_;
}
}
}
LEAN_EXPORT uint64_t l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(lean_object* v_x_787_){
_start:
{
switch(lean_obj_tag(v_x_787_))
{
case 0:
{
uint64_t v___x_788_; 
v___x_788_ = 11ULL;
return v___x_788_;
}
case 1:
{
uint8_t v_b_789_; 
v_b_789_ = lean_ctor_get_uint8(v_x_787_, 0);
if (v_b_789_ == 0)
{
uint64_t v___x_790_; 
v___x_790_ = 889925284873970544ULL;
return v___x_790_;
}
else
{
uint64_t v___x_791_; 
v___x_791_ = 7849220421742680397ULL;
return v___x_791_;
}
}
case 2:
{
lean_object* v_n_792_; uint64_t v___x_793_; uint64_t v___x_794_; uint64_t v___x_795_; 
v_n_792_ = lean_ctor_get(v_x_787_, 0);
v___x_793_ = 17ULL;
v___x_794_ = l_Lean_instHashableJsonNumber_hash(v_n_792_);
v___x_795_ = lean_uint64_mix_hash(v___x_793_, v___x_794_);
return v___x_795_;
}
case 3:
{
lean_object* v_s_796_; uint64_t v___x_797_; uint64_t v___x_798_; uint64_t v___x_799_; 
v_s_796_ = lean_ctor_get(v_x_787_, 0);
v___x_797_ = 19ULL;
v___x_798_ = lean_string_hash(v_s_796_);
v___x_799_ = lean_uint64_mix_hash(v___x_797_, v___x_798_);
return v___x_799_;
}
case 4:
{
lean_object* v_elems_800_; lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v_elems_800_ = lean_ctor_get(v_x_787_, 0);
v___x_801_ = lean_unsigned_to_nat(0u);
v___x_802_ = lean_array_get_size(v_elems_800_);
v___x_803_ = lean_nat_dec_lt(v___x_801_, v___x_802_);
if (v___x_803_ == 0)
{
uint64_t v___x_804_; 
v___x_804_ = 179905158410471120ULL;
return v___x_804_;
}
else
{
uint64_t v___x_805_; uint64_t v___x_806_; uint8_t v___x_807_; 
v___x_805_ = 23ULL;
v___x_806_ = 7ULL;
v___x_807_ = lean_nat_dec_le(v___x_802_, v___x_802_);
if (v___x_807_ == 0)
{
if (v___x_803_ == 0)
{
uint64_t v___x_808_; 
v___x_808_ = 179905158410471120ULL;
return v___x_808_;
}
else
{
size_t v___x_809_; size_t v___x_810_; uint64_t v___x_811_; uint64_t v___x_812_; 
v___x_809_ = ((size_t)0ULL);
v___x_810_ = lean_usize_of_nat(v___x_802_);
v___x_811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_elems_800_, v___x_809_, v___x_810_, v___x_806_);
v___x_812_ = lean_uint64_mix_hash(v___x_805_, v___x_811_);
return v___x_812_;
}
}
else
{
size_t v___x_813_; size_t v___x_814_; uint64_t v___x_815_; uint64_t v___x_816_; 
v___x_813_ = ((size_t)0ULL);
v___x_814_ = lean_usize_of_nat(v___x_802_);
v___x_815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_elems_800_, v___x_813_, v___x_814_, v___x_806_);
v___x_816_ = lean_uint64_mix_hash(v___x_805_, v___x_815_);
return v___x_816_;
}
}
}
default: 
{
lean_object* v_kvPairs_817_; uint64_t v___x_818_; uint64_t v___x_819_; uint64_t v___x_820_; uint64_t v___x_821_; 
v_kvPairs_817_ = lean_ctor_get(v_x_787_, 0);
v___x_818_ = 29ULL;
v___x_819_ = 7ULL;
v___x_820_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v___x_819_, v_kvPairs_817_);
v___x_821_ = lean_uint64_mix_hash(v___x_818_, v___x_820_);
return v___x_821_;
}
}
}
}
LEAN_EXPORT uint64_t l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(uint64_t v_init_822_, lean_object* v_x_823_){
_start:
{
if (lean_obj_tag(v_x_823_) == 0)
{
lean_object* v_k_824_; lean_object* v_v_825_; lean_object* v_l_826_; lean_object* v_r_827_; uint64_t v___x_828_; uint64_t v___x_829_; uint64_t v___x_830_; uint64_t v___x_831_; uint64_t v___x_832_; 
v_k_824_ = lean_ctor_get(v_x_823_, 1);
v_v_825_ = lean_ctor_get(v_x_823_, 2);
v_l_826_ = lean_ctor_get(v_x_823_, 3);
v_r_827_ = lean_ctor_get(v_x_823_, 4);
v___x_828_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_822_, v_l_826_);
v___x_829_ = lean_string_hash(v_k_824_);
v___x_830_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_v_825_);
v___x_831_ = lean_uint64_mix_hash(v___x_829_, v___x_830_);
v___x_832_ = lean_uint64_mix_hash(v___x_828_, v___x_831_);
v_init_822_ = v___x_832_;
v_x_823_ = v_r_827_;
goto _start;
}
else
{
return v_init_822_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1___boxed(lean_object* v_init_834_, lean_object* v_x_835_){
_start:
{
uint64_t v_init_boxed_836_; uint64_t v_res_837_; lean_object* v_r_838_; 
v_init_boxed_836_ = lean_unbox_uint64(v_init_834_);
lean_dec_ref(v_init_834_);
v_res_837_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_boxed_836_, v_x_835_);
lean_dec(v_x_835_);
v_r_838_ = lean_box_uint64(v_res_837_);
return v_r_838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0___boxed(lean_object* v_as_839_, lean_object* v_i_840_, lean_object* v_stop_841_, lean_object* v_b_842_){
_start:
{
size_t v_i_boxed_843_; size_t v_stop_boxed_844_; uint64_t v_b_boxed_845_; uint64_t v_res_846_; lean_object* v_r_847_; 
v_i_boxed_843_ = lean_unbox_usize(v_i_840_);
lean_dec(v_i_840_);
v_stop_boxed_844_ = lean_unbox_usize(v_stop_841_);
lean_dec(v_stop_841_);
v_b_boxed_845_ = lean_unbox_uint64(v_b_842_);
lean_dec_ref(v_b_842_);
v_res_846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_as_839_, v_i_boxed_843_, v_stop_boxed_844_, v_b_boxed_845_);
lean_dec_ref(v_as_839_);
v_r_847_ = lean_box_uint64(v_res_846_);
return v_r_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___boxed(lean_object* v_x_848_){
_start:
{
uint64_t v_res_849_; lean_object* v_r_850_; 
v_res_849_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_x_848_);
lean_dec(v_x_848_);
v_r_850_ = lean_box_uint64(v_res_849_);
return v_r_850_;
}
}
LEAN_EXPORT uint64_t l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1(uint64_t v_init_851_, lean_object* v_t_852_){
_start:
{
uint64_t v___x_853_; 
v___x_853_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_851_, v_t_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1___boxed(lean_object* v_init_854_, lean_object* v_t_855_){
_start:
{
uint64_t v_init_boxed_856_; uint64_t v_res_857_; lean_object* v_r_858_; 
v_init_boxed_856_ = lean_unbox_uint64(v_init_854_);
lean_dec_ref(v_init_854_);
v_res_857_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1(v_init_boxed_856_, v_t_855_);
lean_dec(v_t_855_);
v_r_858_ = lean_box_uint64(v_res_857_);
return v_r_858_;
}
}
LEAN_EXPORT uint64_t l_Lean_Json_instHashable___private__1(lean_object* v_a_859_){
_start:
{
uint64_t v___x_860_; 
v___x_860_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_a_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instHashable___private__1___boxed(lean_object* v_a_861_){
_start:
{
uint64_t v_res_862_; lean_object* v_r_863_; 
v_res_862_ = l_Lean_Json_instHashable___private__1(v_a_861_);
lean_dec(v_a_861_);
v_r_863_ = lean_box_uint64(v_res_862_);
return v_r_863_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(lean_object* v_k_866_, lean_object* v_v_867_, lean_object* v_t_868_){
_start:
{
if (lean_obj_tag(v_t_868_) == 0)
{
lean_object* v_size_869_; lean_object* v_k_870_; lean_object* v_v_871_; lean_object* v_l_872_; lean_object* v_r_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_1153_; 
v_size_869_ = lean_ctor_get(v_t_868_, 0);
v_k_870_ = lean_ctor_get(v_t_868_, 1);
v_v_871_ = lean_ctor_get(v_t_868_, 2);
v_l_872_ = lean_ctor_get(v_t_868_, 3);
v_r_873_ = lean_ctor_get(v_t_868_, 4);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_t_868_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_875_ = v_t_868_;
v_isShared_876_ = v_isSharedCheck_1153_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_r_873_);
lean_inc(v_l_872_);
lean_inc(v_v_871_);
lean_inc(v_k_870_);
lean_inc(v_size_869_);
lean_dec(v_t_868_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_1153_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
uint8_t v___x_877_; 
v___x_877_ = lean_string_compare(v_k_866_, v_k_870_);
switch(v___x_877_)
{
case 0:
{
lean_object* v_impl_878_; lean_object* v___x_879_; 
lean_dec(v_size_869_);
v_impl_878_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_866_, v_v_867_, v_l_872_);
v___x_879_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_873_) == 0)
{
lean_object* v_size_880_; lean_object* v_size_881_; lean_object* v_k_882_; lean_object* v_v_883_; lean_object* v_l_884_; lean_object* v_r_885_; lean_object* v___x_886_; lean_object* v___x_887_; uint8_t v___x_888_; 
v_size_880_ = lean_ctor_get(v_r_873_, 0);
v_size_881_ = lean_ctor_get(v_impl_878_, 0);
v_k_882_ = lean_ctor_get(v_impl_878_, 1);
v_v_883_ = lean_ctor_get(v_impl_878_, 2);
v_l_884_ = lean_ctor_get(v_impl_878_, 3);
v_r_885_ = lean_ctor_get(v_impl_878_, 4);
lean_inc(v_r_885_);
v___x_886_ = lean_unsigned_to_nat(3u);
v___x_887_ = lean_nat_mul(v___x_886_, v_size_880_);
v___x_888_ = lean_nat_dec_lt(v___x_887_, v_size_881_);
lean_dec(v___x_887_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_892_; 
lean_dec(v_r_885_);
v___x_889_ = lean_nat_add(v___x_879_, v_size_881_);
v___x_890_ = lean_nat_add(v___x_889_, v_size_880_);
lean_dec(v___x_889_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 3, v_impl_878_);
lean_ctor_set(v___x_875_, 0, v___x_890_);
v___x_892_ = v___x_875_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_890_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_k_870_);
lean_ctor_set(v_reuseFailAlloc_893_, 2, v_v_871_);
lean_ctor_set(v_reuseFailAlloc_893_, 3, v_impl_878_);
lean_ctor_set(v_reuseFailAlloc_893_, 4, v_r_873_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
else
{
lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_959_; 
lean_inc(v_l_884_);
lean_inc(v_v_883_);
lean_inc(v_k_882_);
lean_inc(v_size_881_);
v_isSharedCheck_959_ = !lean_is_exclusive(v_impl_878_);
if (v_isSharedCheck_959_ == 0)
{
lean_object* v_unused_960_; lean_object* v_unused_961_; lean_object* v_unused_962_; lean_object* v_unused_963_; lean_object* v_unused_964_; 
v_unused_960_ = lean_ctor_get(v_impl_878_, 4);
lean_dec(v_unused_960_);
v_unused_961_ = lean_ctor_get(v_impl_878_, 3);
lean_dec(v_unused_961_);
v_unused_962_ = lean_ctor_get(v_impl_878_, 2);
lean_dec(v_unused_962_);
v_unused_963_ = lean_ctor_get(v_impl_878_, 1);
lean_dec(v_unused_963_);
v_unused_964_ = lean_ctor_get(v_impl_878_, 0);
lean_dec(v_unused_964_);
v___x_895_ = v_impl_878_;
v_isShared_896_ = v_isSharedCheck_959_;
goto v_resetjp_894_;
}
else
{
lean_dec(v_impl_878_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_959_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v_size_897_; lean_object* v_size_898_; lean_object* v_k_899_; lean_object* v_v_900_; lean_object* v_l_901_; lean_object* v_r_902_; lean_object* v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v_size_897_ = lean_ctor_get(v_l_884_, 0);
v_size_898_ = lean_ctor_get(v_r_885_, 0);
v_k_899_ = lean_ctor_get(v_r_885_, 1);
v_v_900_ = lean_ctor_get(v_r_885_, 2);
v_l_901_ = lean_ctor_get(v_r_885_, 3);
v_r_902_ = lean_ctor_get(v_r_885_, 4);
v___x_903_ = lean_unsigned_to_nat(2u);
v___x_904_ = lean_nat_mul(v___x_903_, v_size_897_);
v___x_905_ = lean_nat_dec_lt(v_size_898_, v___x_904_);
lean_dec(v___x_904_);
if (v___x_905_ == 0)
{
lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_934_; 
lean_inc(v_r_902_);
lean_inc(v_l_901_);
lean_inc(v_v_900_);
lean_inc(v_k_899_);
v_isSharedCheck_934_ = !lean_is_exclusive(v_r_885_);
if (v_isSharedCheck_934_ == 0)
{
lean_object* v_unused_935_; lean_object* v_unused_936_; lean_object* v_unused_937_; lean_object* v_unused_938_; lean_object* v_unused_939_; 
v_unused_935_ = lean_ctor_get(v_r_885_, 4);
lean_dec(v_unused_935_);
v_unused_936_ = lean_ctor_get(v_r_885_, 3);
lean_dec(v_unused_936_);
v_unused_937_ = lean_ctor_get(v_r_885_, 2);
lean_dec(v_unused_937_);
v_unused_938_ = lean_ctor_get(v_r_885_, 1);
lean_dec(v_unused_938_);
v_unused_939_ = lean_ctor_get(v_r_885_, 0);
lean_dec(v_unused_939_);
v___x_907_ = v_r_885_;
v_isShared_908_ = v_isSharedCheck_934_;
goto v_resetjp_906_;
}
else
{
lean_dec(v_r_885_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_934_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___x_922_; lean_object* v___y_924_; 
v___x_909_ = lean_nat_add(v___x_879_, v_size_881_);
lean_dec(v_size_881_);
v___x_910_ = lean_nat_add(v___x_909_, v_size_880_);
lean_dec(v___x_909_);
v___x_922_ = lean_nat_add(v___x_879_, v_size_897_);
if (lean_obj_tag(v_l_901_) == 0)
{
lean_object* v_size_932_; 
v_size_932_ = lean_ctor_get(v_l_901_, 0);
lean_inc(v_size_932_);
v___y_924_ = v_size_932_;
goto v___jp_923_;
}
else
{
lean_object* v___x_933_; 
v___x_933_ = lean_unsigned_to_nat(0u);
v___y_924_ = v___x_933_;
goto v___jp_923_;
}
v___jp_911_:
{
lean_object* v___x_915_; lean_object* v___x_917_; 
v___x_915_ = lean_nat_add(v___y_913_, v___y_914_);
lean_dec(v___y_914_);
lean_dec(v___y_913_);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 4, v_r_873_);
lean_ctor_set(v___x_907_, 3, v_r_902_);
lean_ctor_set(v___x_907_, 2, v_v_871_);
lean_ctor_set(v___x_907_, 1, v_k_870_);
lean_ctor_set(v___x_907_, 0, v___x_915_);
v___x_917_ = v___x_907_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_k_870_);
lean_ctor_set(v_reuseFailAlloc_921_, 2, v_v_871_);
lean_ctor_set(v_reuseFailAlloc_921_, 3, v_r_902_);
lean_ctor_set(v_reuseFailAlloc_921_, 4, v_r_873_);
v___x_917_ = v_reuseFailAlloc_921_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_919_; 
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 4, v___x_917_);
lean_ctor_set(v___x_895_, 3, v___y_912_);
lean_ctor_set(v___x_895_, 2, v_v_900_);
lean_ctor_set(v___x_895_, 1, v_k_899_);
lean_ctor_set(v___x_895_, 0, v___x_910_);
v___x_919_ = v___x_895_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_910_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_k_899_);
lean_ctor_set(v_reuseFailAlloc_920_, 2, v_v_900_);
lean_ctor_set(v_reuseFailAlloc_920_, 3, v___y_912_);
lean_ctor_set(v_reuseFailAlloc_920_, 4, v___x_917_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
v___jp_923_:
{
lean_object* v___x_925_; lean_object* v___x_927_; 
v___x_925_ = lean_nat_add(v___x_922_, v___y_924_);
lean_dec(v___y_924_);
lean_dec(v___x_922_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 4, v_l_901_);
lean_ctor_set(v___x_875_, 3, v_l_884_);
lean_ctor_set(v___x_875_, 2, v_v_883_);
lean_ctor_set(v___x_875_, 1, v_k_882_);
lean_ctor_set(v___x_875_, 0, v___x_925_);
v___x_927_ = v___x_875_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_925_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_k_882_);
lean_ctor_set(v_reuseFailAlloc_931_, 2, v_v_883_);
lean_ctor_set(v_reuseFailAlloc_931_, 3, v_l_884_);
lean_ctor_set(v_reuseFailAlloc_931_, 4, v_l_901_);
v___x_927_ = v_reuseFailAlloc_931_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_928_; 
v___x_928_ = lean_nat_add(v___x_879_, v_size_880_);
if (lean_obj_tag(v_r_902_) == 0)
{
lean_object* v_size_929_; 
v_size_929_ = lean_ctor_get(v_r_902_, 0);
lean_inc(v_size_929_);
v___y_912_ = v___x_927_;
v___y_913_ = v___x_928_;
v___y_914_ = v_size_929_;
goto v___jp_911_;
}
else
{
lean_object* v___x_930_; 
v___x_930_ = lean_unsigned_to_nat(0u);
v___y_912_ = v___x_927_;
v___y_913_ = v___x_928_;
v___y_914_ = v___x_930_;
goto v___jp_911_;
}
}
}
}
}
else
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_945_; 
lean_del_object(v___x_875_);
v___x_940_ = lean_nat_add(v___x_879_, v_size_881_);
lean_dec(v_size_881_);
v___x_941_ = lean_nat_add(v___x_940_, v_size_880_);
lean_dec(v___x_940_);
v___x_942_ = lean_nat_add(v___x_879_, v_size_880_);
v___x_943_ = lean_nat_add(v___x_942_, v_size_898_);
lean_dec(v___x_942_);
lean_inc_ref(v_r_873_);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 4, v_r_873_);
lean_ctor_set(v___x_895_, 3, v_r_885_);
lean_ctor_set(v___x_895_, 2, v_v_871_);
lean_ctor_set(v___x_895_, 1, v_k_870_);
lean_ctor_set(v___x_895_, 0, v___x_943_);
v___x_945_ = v___x_895_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_k_870_);
lean_ctor_set(v_reuseFailAlloc_958_, 2, v_v_871_);
lean_ctor_set(v_reuseFailAlloc_958_, 3, v_r_885_);
lean_ctor_set(v_reuseFailAlloc_958_, 4, v_r_873_);
v___x_945_ = v_reuseFailAlloc_958_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
v_isSharedCheck_952_ = !lean_is_exclusive(v_r_873_);
if (v_isSharedCheck_952_ == 0)
{
lean_object* v_unused_953_; lean_object* v_unused_954_; lean_object* v_unused_955_; lean_object* v_unused_956_; lean_object* v_unused_957_; 
v_unused_953_ = lean_ctor_get(v_r_873_, 4);
lean_dec(v_unused_953_);
v_unused_954_ = lean_ctor_get(v_r_873_, 3);
lean_dec(v_unused_954_);
v_unused_955_ = lean_ctor_get(v_r_873_, 2);
lean_dec(v_unused_955_);
v_unused_956_ = lean_ctor_get(v_r_873_, 1);
lean_dec(v_unused_956_);
v_unused_957_ = lean_ctor_get(v_r_873_, 0);
lean_dec(v_unused_957_);
v___x_947_ = v_r_873_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_dec(v_r_873_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 4, v___x_945_);
lean_ctor_set(v___x_947_, 3, v_l_884_);
lean_ctor_set(v___x_947_, 2, v_v_883_);
lean_ctor_set(v___x_947_, 1, v_k_882_);
lean_ctor_set(v___x_947_, 0, v___x_941_);
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_k_882_);
lean_ctor_set(v_reuseFailAlloc_951_, 2, v_v_883_);
lean_ctor_set(v_reuseFailAlloc_951_, 3, v_l_884_);
lean_ctor_set(v_reuseFailAlloc_951_, 4, v___x_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_965_; 
v_l_965_ = lean_ctor_get(v_impl_878_, 3);
if (lean_obj_tag(v_l_965_) == 0)
{
lean_object* v_r_966_; lean_object* v_k_967_; lean_object* v_v_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_979_; 
lean_inc_ref(v_l_965_);
v_r_966_ = lean_ctor_get(v_impl_878_, 4);
v_k_967_ = lean_ctor_get(v_impl_878_, 1);
v_v_968_ = lean_ctor_get(v_impl_878_, 2);
v_isSharedCheck_979_ = !lean_is_exclusive(v_impl_878_);
if (v_isSharedCheck_979_ == 0)
{
lean_object* v_unused_980_; lean_object* v_unused_981_; 
v_unused_980_ = lean_ctor_get(v_impl_878_, 3);
lean_dec(v_unused_980_);
v_unused_981_ = lean_ctor_get(v_impl_878_, 0);
lean_dec(v_unused_981_);
v___x_970_ = v_impl_878_;
v_isShared_971_ = v_isSharedCheck_979_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_r_966_);
lean_inc(v_v_968_);
lean_inc(v_k_967_);
lean_dec(v_impl_878_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_979_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v___x_974_; 
v___x_972_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_966_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 3, v_r_966_);
lean_ctor_set(v___x_970_, 2, v_v_871_);
lean_ctor_set(v___x_970_, 1, v_k_870_);
lean_ctor_set(v___x_970_, 0, v___x_879_);
v___x_974_ = v___x_970_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_k_870_);
lean_ctor_set(v_reuseFailAlloc_978_, 2, v_v_871_);
lean_ctor_set(v_reuseFailAlloc_978_, 3, v_r_966_);
lean_ctor_set(v_reuseFailAlloc_978_, 4, v_r_966_);
v___x_974_ = v_reuseFailAlloc_978_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_object* v___x_976_; 
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 4, v___x_974_);
lean_ctor_set(v___x_875_, 3, v_l_965_);
lean_ctor_set(v___x_875_, 2, v_v_968_);
lean_ctor_set(v___x_875_, 1, v_k_967_);
lean_ctor_set(v___x_875_, 0, v___x_972_);
v___x_976_ = v___x_875_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_972_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_k_967_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v_v_968_);
lean_ctor_set(v_reuseFailAlloc_977_, 3, v_l_965_);
lean_ctor_set(v_reuseFailAlloc_977_, 4, v___x_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
else
{
lean_object* v_r_982_; 
v_r_982_ = lean_ctor_get(v_impl_878_, 4);
lean_inc(v_r_982_);
if (lean_obj_tag(v_r_982_) == 0)
{
lean_object* v_k_983_; lean_object* v_v_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1007_; 
lean_inc(v_l_965_);
v_k_983_ = lean_ctor_get(v_impl_878_, 1);
v_v_984_ = lean_ctor_get(v_impl_878_, 2);
v_isSharedCheck_1007_ = !lean_is_exclusive(v_impl_878_);
if (v_isSharedCheck_1007_ == 0)
{
lean_object* v_unused_1008_; lean_object* v_unused_1009_; lean_object* v_unused_1010_; 
v_unused_1008_ = lean_ctor_get(v_impl_878_, 4);
lean_dec(v_unused_1008_);
v_unused_1009_ = lean_ctor_get(v_impl_878_, 3);
lean_dec(v_unused_1009_);
v_unused_1010_ = lean_ctor_get(v_impl_878_, 0);
lean_dec(v_unused_1010_);
v___x_986_ = v_impl_878_;
v_isShared_987_ = v_isSharedCheck_1007_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_v_984_);
lean_inc(v_k_983_);
lean_dec(v_impl_878_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1007_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v_k_988_; lean_object* v_v_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1003_; 
v_k_988_ = lean_ctor_get(v_r_982_, 1);
v_v_989_ = lean_ctor_get(v_r_982_, 2);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_r_982_);
if (v_isSharedCheck_1003_ == 0)
{
lean_object* v_unused_1004_; lean_object* v_unused_1005_; lean_object* v_unused_1006_; 
v_unused_1004_ = lean_ctor_get(v_r_982_, 4);
lean_dec(v_unused_1004_);
v_unused_1005_ = lean_ctor_get(v_r_982_, 3);
lean_dec(v_unused_1005_);
v_unused_1006_ = lean_ctor_get(v_r_982_, 0);
lean_dec(v_unused_1006_);
v___x_991_ = v_r_982_;
v_isShared_992_ = v_isSharedCheck_1003_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_v_989_);
lean_inc(v_k_988_);
lean_dec(v_r_982_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1003_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_993_ = lean_unsigned_to_nat(3u);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 4, v_l_965_);
lean_ctor_set(v___x_991_, 3, v_l_965_);
lean_ctor_set(v___x_991_, 2, v_v_984_);
lean_ctor_set(v___x_991_, 1, v_k_983_);
lean_ctor_set(v___x_991_, 0, v___x_879_);
v___x_995_ = v___x_991_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_k_983_);
lean_ctor_set(v_reuseFailAlloc_1002_, 2, v_v_984_);
lean_ctor_set(v_reuseFailAlloc_1002_, 3, v_l_965_);
lean_ctor_set(v_reuseFailAlloc_1002_, 4, v_l_965_);
v___x_995_ = v_reuseFailAlloc_1002_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_997_; 
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 4, v_l_965_);
lean_ctor_set(v___x_986_, 2, v_v_871_);
lean_ctor_set(v___x_986_, 1, v_k_870_);
lean_ctor_set(v___x_986_, 0, v___x_879_);
v___x_997_ = v___x_986_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_k_870_);
lean_ctor_set(v_reuseFailAlloc_1001_, 2, v_v_871_);
lean_ctor_set(v_reuseFailAlloc_1001_, 3, v_l_965_);
lean_ctor_set(v_reuseFailAlloc_1001_, 4, v_l_965_);
v___x_997_ = v_reuseFailAlloc_1001_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_999_; 
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 4, v___x_997_);
lean_ctor_set(v___x_875_, 3, v___x_995_);
lean_ctor_set(v___x_875_, 2, v_v_989_);
lean_ctor_set(v___x_875_, 1, v_k_988_);
lean_ctor_set(v___x_875_, 0, v___x_993_);
v___x_999_ = v___x_875_;
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
lean_object* v___x_1011_; lean_object* v___x_1013_; 
v___x_1011_ = lean_unsigned_to_nat(2u);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 4, v_r_982_);
lean_ctor_set(v___x_875_, 3, v_impl_878_);
lean_ctor_set(v___x_875_, 0, v___x_1011_);
v___x_1013_ = v___x_875_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1011_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v_k_870_);
lean_ctor_set(v_reuseFailAlloc_1014_, 2, v_v_871_);
lean_ctor_set(v_reuseFailAlloc_1014_, 3, v_impl_878_);
lean_ctor_set(v_reuseFailAlloc_1014_, 4, v_r_982_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1016_; 
lean_dec(v_v_871_);
lean_dec(v_k_870_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 2, v_v_867_);
lean_ctor_set(v___x_875_, 1, v_k_866_);
v___x_1016_ = v___x_875_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_size_869_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_k_866_);
lean_ctor_set(v_reuseFailAlloc_1017_, 2, v_v_867_);
lean_ctor_set(v_reuseFailAlloc_1017_, 3, v_l_872_);
lean_ctor_set(v_reuseFailAlloc_1017_, 4, v_r_873_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
default: 
{
lean_object* v_impl_1018_; lean_object* v___x_1019_; 
lean_dec(v_size_869_);
v_impl_1018_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_866_, v_v_867_, v_r_873_);
v___x_1019_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_872_) == 0)
{
lean_object* v_size_1020_; lean_object* v_size_1021_; lean_object* v_k_1022_; lean_object* v_v_1023_; lean_object* v_l_1024_; lean_object* v_r_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; 
v_size_1020_ = lean_ctor_get(v_l_872_, 0);
v_size_1021_ = lean_ctor_get(v_impl_1018_, 0);
v_k_1022_ = lean_ctor_get(v_impl_1018_, 1);
v_v_1023_ = lean_ctor_get(v_impl_1018_, 2);
v_l_1024_ = lean_ctor_get(v_impl_1018_, 3);
lean_inc(v_l_1024_);
v_r_1025_ = lean_ctor_get(v_impl_1018_, 4);
v___x_1026_ = lean_unsigned_to_nat(3u);
v___x_1027_ = lean_nat_mul(v___x_1026_, v_size_1020_);
v___x_1028_ = lean_nat_dec_lt(v___x_1027_, v_size_1021_);
lean_dec(v___x_1027_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1032_; 
lean_dec(v_l_1024_);
v___x_1029_ = lean_nat_add(v___x_1019_, v_size_1020_);
v___x_1030_ = lean_nat_add(v___x_1029_, v_size_1021_);
lean_dec(v___x_1029_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 4, v_impl_1018_);
lean_ctor_set(v___x_875_, 0, v___x_1030_);
v___x_1032_ = v___x_875_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_k_870_);
lean_ctor_set(v_reuseFailAlloc_1033_, 2, v_v_871_);
lean_ctor_set(v_reuseFailAlloc_1033_, 3, v_l_872_);
lean_ctor_set(v_reuseFailAlloc_1033_, 4, v_impl_1018_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
else
{
lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1097_; 
lean_inc(v_r_1025_);
lean_inc(v_v_1023_);
lean_inc(v_k_1022_);
lean_inc(v_size_1021_);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_impl_1018_);
if (v_isSharedCheck_1097_ == 0)
{
lean_object* v_unused_1098_; lean_object* v_unused_1099_; lean_object* v_unused_1100_; lean_object* v_unused_1101_; lean_object* v_unused_1102_; 
v_unused_1098_ = lean_ctor_get(v_impl_1018_, 4);
lean_dec(v_unused_1098_);
v_unused_1099_ = lean_ctor_get(v_impl_1018_, 3);
lean_dec(v_unused_1099_);
v_unused_1100_ = lean_ctor_get(v_impl_1018_, 2);
lean_dec(v_unused_1100_);
v_unused_1101_ = lean_ctor_get(v_impl_1018_, 1);
lean_dec(v_unused_1101_);
v_unused_1102_ = lean_ctor_get(v_impl_1018_, 0);
lean_dec(v_unused_1102_);
v___x_1035_ = v_impl_1018_;
v_isShared_1036_ = v_isSharedCheck_1097_;
goto v_resetjp_1034_;
}
else
{
lean_dec(v_impl_1018_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1097_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v_size_1037_; lean_object* v_k_1038_; lean_object* v_v_1039_; lean_object* v_l_1040_; lean_object* v_r_1041_; lean_object* v_size_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v_size_1037_ = lean_ctor_get(v_l_1024_, 0);
v_k_1038_ = lean_ctor_get(v_l_1024_, 1);
v_v_1039_ = lean_ctor_get(v_l_1024_, 2);
v_l_1040_ = lean_ctor_get(v_l_1024_, 3);
v_r_1041_ = lean_ctor_get(v_l_1024_, 4);
v_size_1042_ = lean_ctor_get(v_r_1025_, 0);
v___x_1043_ = lean_unsigned_to_nat(2u);
v___x_1044_ = lean_nat_mul(v___x_1043_, v_size_1042_);
v___x_1045_ = lean_nat_dec_lt(v_size_1037_, v___x_1044_);
lean_dec(v___x_1044_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1073_; 
lean_inc(v_r_1041_);
lean_inc(v_l_1040_);
lean_inc(v_v_1039_);
lean_inc(v_k_1038_);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_l_1024_);
if (v_isSharedCheck_1073_ == 0)
{
lean_object* v_unused_1074_; lean_object* v_unused_1075_; lean_object* v_unused_1076_; lean_object* v_unused_1077_; lean_object* v_unused_1078_; 
v_unused_1074_ = lean_ctor_get(v_l_1024_, 4);
lean_dec(v_unused_1074_);
v_unused_1075_ = lean_ctor_get(v_l_1024_, 3);
lean_dec(v_unused_1075_);
v_unused_1076_ = lean_ctor_get(v_l_1024_, 2);
lean_dec(v_unused_1076_);
v_unused_1077_ = lean_ctor_get(v_l_1024_, 1);
lean_dec(v_unused_1077_);
v_unused_1078_ = lean_ctor_get(v_l_1024_, 0);
lean_dec(v_unused_1078_);
v___x_1047_ = v_l_1024_;
v_isShared_1048_ = v_isSharedCheck_1073_;
goto v_resetjp_1046_;
}
else
{
lean_dec(v_l_1024_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1073_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1063_; 
v___x_1049_ = lean_nat_add(v___x_1019_, v_size_1020_);
v___x_1050_ = lean_nat_add(v___x_1049_, v_size_1021_);
lean_dec(v_size_1021_);
if (lean_obj_tag(v_l_1040_) == 0)
{
lean_object* v_size_1071_; 
v_size_1071_ = lean_ctor_get(v_l_1040_, 0);
lean_inc(v_size_1071_);
v___y_1063_ = v_size_1071_;
goto v___jp_1062_;
}
else
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_unsigned_to_nat(0u);
v___y_1063_ = v___x_1072_;
goto v___jp_1062_;
}
v___jp_1051_:
{
lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1055_ = lean_nat_add(v___y_1053_, v___y_1054_);
lean_dec(v___y_1054_);
lean_dec(v___y_1053_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 4, v_r_1025_);
lean_ctor_set(v___x_1047_, 3, v_r_1041_);
lean_ctor_set(v___x_1047_, 2, v_v_1023_);
lean_ctor_set(v___x_1047_, 1, v_k_1022_);
lean_ctor_set(v___x_1047_, 0, v___x_1055_);
v___x_1057_ = v___x_1047_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v_k_1022_);
lean_ctor_set(v_reuseFailAlloc_1061_, 2, v_v_1023_);
lean_ctor_set(v_reuseFailAlloc_1061_, 3, v_r_1041_);
lean_ctor_set(v_reuseFailAlloc_1061_, 4, v_r_1025_);
v___x_1057_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1059_; 
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 4, v___x_1057_);
lean_ctor_set(v___x_1035_, 3, v___y_1052_);
lean_ctor_set(v___x_1035_, 2, v_v_1039_);
lean_ctor_set(v___x_1035_, 1, v_k_1038_);
lean_ctor_set(v___x_1035_, 0, v___x_1050_);
v___x_1059_ = v___x_1035_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v_k_1038_);
lean_ctor_set(v_reuseFailAlloc_1060_, 2, v_v_1039_);
lean_ctor_set(v_reuseFailAlloc_1060_, 3, v___y_1052_);
lean_ctor_set(v_reuseFailAlloc_1060_, 4, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
v___jp_1062_:
{
lean_object* v___x_1064_; lean_object* v___x_1066_; 
v___x_1064_ = lean_nat_add(v___x_1049_, v___y_1063_);
lean_dec(v___y_1063_);
lean_dec(v___x_1049_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 4, v_l_1040_);
lean_ctor_set(v___x_875_, 0, v___x_1064_);
v___x_1066_ = v___x_875_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1064_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v_k_870_);
lean_ctor_set(v_reuseFailAlloc_1070_, 2, v_v_871_);
lean_ctor_set(v_reuseFailAlloc_1070_, 3, v_l_872_);
lean_ctor_set(v_reuseFailAlloc_1070_, 4, v_l_1040_);
v___x_1066_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_nat_add(v___x_1019_, v_size_1042_);
if (lean_obj_tag(v_r_1041_) == 0)
{
lean_object* v_size_1068_; 
v_size_1068_ = lean_ctor_get(v_r_1041_, 0);
lean_inc(v_size_1068_);
v___y_1052_ = v___x_1066_;
v___y_1053_ = v___x_1067_;
v___y_1054_ = v_size_1068_;
goto v___jp_1051_;
}
else
{
lean_object* v___x_1069_; 
v___x_1069_ = lean_unsigned_to_nat(0u);
v___y_1052_ = v___x_1066_;
v___y_1053_ = v___x_1067_;
v___y_1054_ = v___x_1069_;
goto v___jp_1051_;
}
}
}
}
}
else
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1083_; 
lean_del_object(v___x_875_);
v___x_1079_ = lean_nat_add(v___x_1019_, v_size_1020_);
v___x_1080_ = lean_nat_add(v___x_1079_, v_size_1021_);
lean_dec(v_size_1021_);
v___x_1081_ = lean_nat_add(v___x_1079_, v_size_1037_);
lean_dec(v___x_1079_);
lean_inc_ref(v_l_872_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 4, v_l_1024_);
lean_ctor_set(v___x_1035_, 3, v_l_872_);
lean_ctor_set(v___x_1035_, 2, v_v_871_);
lean_ctor_set(v___x_1035_, 1, v_k_870_);
lean_ctor_set(v___x_1035_, 0, v___x_1081_);
v___x_1083_ = v___x_1035_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_k_870_);
lean_ctor_set(v_reuseFailAlloc_1096_, 2, v_v_871_);
lean_ctor_set(v_reuseFailAlloc_1096_, 3, v_l_872_);
lean_ctor_set(v_reuseFailAlloc_1096_, 4, v_l_1024_);
v___x_1083_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
v_isSharedCheck_1090_ = !lean_is_exclusive(v_l_872_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; lean_object* v_unused_1092_; lean_object* v_unused_1093_; lean_object* v_unused_1094_; lean_object* v_unused_1095_; 
v_unused_1091_ = lean_ctor_get(v_l_872_, 4);
lean_dec(v_unused_1091_);
v_unused_1092_ = lean_ctor_get(v_l_872_, 3);
lean_dec(v_unused_1092_);
v_unused_1093_ = lean_ctor_get(v_l_872_, 2);
lean_dec(v_unused_1093_);
v_unused_1094_ = lean_ctor_get(v_l_872_, 1);
lean_dec(v_unused_1094_);
v_unused_1095_ = lean_ctor_get(v_l_872_, 0);
lean_dec(v_unused_1095_);
v___x_1085_ = v_l_872_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_dec(v_l_872_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 4, v_r_1025_);
lean_ctor_set(v___x_1085_, 3, v___x_1083_);
lean_ctor_set(v___x_1085_, 2, v_v_1023_);
lean_ctor_set(v___x_1085_, 1, v_k_1022_);
lean_ctor_set(v___x_1085_, 0, v___x_1080_);
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_k_1022_);
lean_ctor_set(v_reuseFailAlloc_1089_, 2, v_v_1023_);
lean_ctor_set(v_reuseFailAlloc_1089_, 3, v___x_1083_);
lean_ctor_set(v_reuseFailAlloc_1089_, 4, v_r_1025_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1103_; 
v_l_1103_ = lean_ctor_get(v_impl_1018_, 3);
lean_inc(v_l_1103_);
if (lean_obj_tag(v_l_1103_) == 0)
{
lean_object* v_r_1104_; lean_object* v_k_1105_; lean_object* v_v_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1129_; 
v_r_1104_ = lean_ctor_get(v_impl_1018_, 4);
v_k_1105_ = lean_ctor_get(v_impl_1018_, 1);
v_v_1106_ = lean_ctor_get(v_impl_1018_, 2);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_impl_1018_);
if (v_isSharedCheck_1129_ == 0)
{
lean_object* v_unused_1130_; lean_object* v_unused_1131_; 
v_unused_1130_ = lean_ctor_get(v_impl_1018_, 3);
lean_dec(v_unused_1130_);
v_unused_1131_ = lean_ctor_get(v_impl_1018_, 0);
lean_dec(v_unused_1131_);
v___x_1108_ = v_impl_1018_;
v_isShared_1109_ = v_isSharedCheck_1129_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_r_1104_);
lean_inc(v_v_1106_);
lean_inc(v_k_1105_);
lean_dec(v_impl_1018_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1129_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v_k_1110_; lean_object* v_v_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1125_; 
v_k_1110_ = lean_ctor_get(v_l_1103_, 1);
v_v_1111_ = lean_ctor_get(v_l_1103_, 2);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_l_1103_);
if (v_isSharedCheck_1125_ == 0)
{
lean_object* v_unused_1126_; lean_object* v_unused_1127_; lean_object* v_unused_1128_; 
v_unused_1126_ = lean_ctor_get(v_l_1103_, 4);
lean_dec(v_unused_1126_);
v_unused_1127_ = lean_ctor_get(v_l_1103_, 3);
lean_dec(v_unused_1127_);
v_unused_1128_ = lean_ctor_get(v_l_1103_, 0);
lean_dec(v_unused_1128_);
v___x_1113_ = v_l_1103_;
v_isShared_1114_ = v_isSharedCheck_1125_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_v_1111_);
lean_inc(v_k_1110_);
lean_dec(v_l_1103_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1125_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1115_; lean_object* v___x_1117_; 
v___x_1115_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1104_, 2);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 4, v_r_1104_);
lean_ctor_set(v___x_1113_, 3, v_r_1104_);
lean_ctor_set(v___x_1113_, 2, v_v_871_);
lean_ctor_set(v___x_1113_, 1, v_k_870_);
lean_ctor_set(v___x_1113_, 0, v___x_1019_);
v___x_1117_ = v___x_1113_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1019_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_k_870_);
lean_ctor_set(v_reuseFailAlloc_1124_, 2, v_v_871_);
lean_ctor_set(v_reuseFailAlloc_1124_, 3, v_r_1104_);
lean_ctor_set(v_reuseFailAlloc_1124_, 4, v_r_1104_);
v___x_1117_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1119_; 
lean_inc(v_r_1104_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 3, v_r_1104_);
lean_ctor_set(v___x_1108_, 0, v___x_1019_);
v___x_1119_ = v___x_1108_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1019_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_k_1105_);
lean_ctor_set(v_reuseFailAlloc_1123_, 2, v_v_1106_);
lean_ctor_set(v_reuseFailAlloc_1123_, 3, v_r_1104_);
lean_ctor_set(v_reuseFailAlloc_1123_, 4, v_r_1104_);
v___x_1119_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1121_; 
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 4, v___x_1119_);
lean_ctor_set(v___x_875_, 3, v___x_1117_);
lean_ctor_set(v___x_875_, 2, v_v_1111_);
lean_ctor_set(v___x_875_, 1, v_k_1110_);
lean_ctor_set(v___x_875_, 0, v___x_1115_);
v___x_1121_ = v___x_875_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1115_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_k_1110_);
lean_ctor_set(v_reuseFailAlloc_1122_, 2, v_v_1111_);
lean_ctor_set(v_reuseFailAlloc_1122_, 3, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1122_, 4, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
}
else
{
lean_object* v_r_1132_; 
v_r_1132_ = lean_ctor_get(v_impl_1018_, 4);
lean_inc(v_r_1132_);
if (lean_obj_tag(v_r_1132_) == 0)
{
lean_object* v_k_1133_; lean_object* v_v_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1145_; 
v_k_1133_ = lean_ctor_get(v_impl_1018_, 1);
v_v_1134_ = lean_ctor_get(v_impl_1018_, 2);
v_isSharedCheck_1145_ = !lean_is_exclusive(v_impl_1018_);
if (v_isSharedCheck_1145_ == 0)
{
lean_object* v_unused_1146_; lean_object* v_unused_1147_; lean_object* v_unused_1148_; 
v_unused_1146_ = lean_ctor_get(v_impl_1018_, 4);
lean_dec(v_unused_1146_);
v_unused_1147_ = lean_ctor_get(v_impl_1018_, 3);
lean_dec(v_unused_1147_);
v_unused_1148_ = lean_ctor_get(v_impl_1018_, 0);
lean_dec(v_unused_1148_);
v___x_1136_ = v_impl_1018_;
v_isShared_1137_ = v_isSharedCheck_1145_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_v_1134_);
lean_inc(v_k_1133_);
lean_dec(v_impl_1018_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1145_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1138_ = lean_unsigned_to_nat(3u);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 4, v_l_1103_);
lean_ctor_set(v___x_1136_, 2, v_v_871_);
lean_ctor_set(v___x_1136_, 1, v_k_870_);
lean_ctor_set(v___x_1136_, 0, v___x_1019_);
v___x_1140_ = v___x_1136_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1019_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_k_870_);
lean_ctor_set(v_reuseFailAlloc_1144_, 2, v_v_871_);
lean_ctor_set(v_reuseFailAlloc_1144_, 3, v_l_1103_);
lean_ctor_set(v_reuseFailAlloc_1144_, 4, v_l_1103_);
v___x_1140_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1142_; 
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 4, v_r_1132_);
lean_ctor_set(v___x_875_, 3, v___x_1140_);
lean_ctor_set(v___x_875_, 2, v_v_1134_);
lean_ctor_set(v___x_875_, 1, v_k_1133_);
lean_ctor_set(v___x_875_, 0, v___x_1138_);
v___x_1142_ = v___x_875_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_k_1133_);
lean_ctor_set(v_reuseFailAlloc_1143_, 2, v_v_1134_);
lean_ctor_set(v_reuseFailAlloc_1143_, 3, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1143_, 4, v_r_1132_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
else
{
lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1149_ = lean_unsigned_to_nat(2u);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 4, v_impl_1018_);
lean_ctor_set(v___x_875_, 3, v_r_1132_);
lean_ctor_set(v___x_875_, 0, v___x_1149_);
v___x_1151_ = v___x_875_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_k_870_);
lean_ctor_set(v_reuseFailAlloc_1152_, 2, v_v_871_);
lean_ctor_set(v_reuseFailAlloc_1152_, 3, v_r_1132_);
lean_ctor_set(v_reuseFailAlloc_1152_, 4, v_impl_1018_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
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
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = lean_unsigned_to_nat(1u);
v___x_1155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
lean_ctor_set(v___x_1155_, 1, v_k_866_);
lean_ctor_set(v___x_1155_, 2, v_v_867_);
lean_ctor_set(v___x_1155_, 3, v_t_868_);
lean_ctor_set(v___x_1155_, 4, v_t_868_);
return v___x_1155_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(lean_object* v_as_x27_1156_, lean_object* v_b_1157_){
_start:
{
if (lean_obj_tag(v_as_x27_1156_) == 0)
{
return v_b_1157_;
}
else
{
lean_object* v_head_1158_; lean_object* v_tail_1159_; lean_object* v_fst_1160_; lean_object* v_snd_1161_; lean_object* v_r_1162_; 
v_head_1158_ = lean_ctor_get(v_as_x27_1156_, 0);
v_tail_1159_ = lean_ctor_get(v_as_x27_1156_, 1);
v_fst_1160_ = lean_ctor_get(v_head_1158_, 0);
v_snd_1161_ = lean_ctor_get(v_head_1158_, 1);
lean_inc(v_snd_1161_);
lean_inc(v_fst_1160_);
v_r_1162_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_fst_1160_, v_snd_1161_, v_b_1157_);
v_as_x27_1156_ = v_tail_1159_;
v_b_1157_ = v_r_1162_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg___boxed(lean_object* v_as_x27_1164_, lean_object* v_b_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_as_x27_1164_, v_b_1165_);
lean_dec(v_as_x27_1164_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mkObj(lean_object* v_o_1167_){
_start:
{
lean_object* v_r_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v_r_1168_ = lean_box(1);
v___x_1169_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_o_1167_, v_r_1168_);
v___x_1170_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mkObj___boxed(lean_object* v_o_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_Json_mkObj(v_o_1171_);
lean_dec(v_o_1171_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0(lean_object* v_00_u03b2_1173_, lean_object* v_k_1174_, lean_object* v_v_1175_, lean_object* v_t_1176_, lean_object* v_hl_1177_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_1174_, v_v_1175_, v_t_1176_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1(lean_object* v_as_1179_, lean_object* v_as_x27_1180_, lean_object* v_b_1181_, lean_object* v_a_1182_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_as_x27_1180_, v_b_1181_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___boxed(lean_object* v_as_1184_, lean_object* v_as_x27_1185_, lean_object* v_b_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1(v_as_1184_, v_as_x27_1185_, v_b_1186_, v_a_1187_);
lean_dec(v_as_x27_1185_);
lean_dec(v_as_1184_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeNat___lam__0(lean_object* v_n_1189_){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = l_Lean_JsonNumber_fromNat(v_n_1189_);
v___x_1191_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeInt___lam__0(lean_object* v_n_1194_){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = l_Lean_JsonNumber_fromInt(v_n_1194_);
v___x_1196_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeString___lam__0(lean_object* v_s_1199_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1200_, 0, v_s_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeBool___lam__0(uint8_t v_b_1203_){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1204_, 0, v_b_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeBool___lam__0___boxed(lean_object* v_b_1205_){
_start:
{
uint8_t v_b_boxed_1206_; lean_object* v_res_1207_; 
v_b_boxed_1206_ = lean_unbox(v_b_1205_);
v_res_1207_ = l_Lean_Json_instCoeBool___lam__0(v_b_boxed_1206_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instOfNat(lean_object* v_n_1210_){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = l_Lean_JsonNumber_fromNat(v_n_1210_);
v___x_1212_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT uint8_t l_Lean_Json_isNull(lean_object* v_x_1213_){
_start:
{
if (lean_obj_tag(v_x_1213_) == 0)
{
uint8_t v___x_1214_; 
v___x_1214_ = 1;
return v___x_1214_;
}
else
{
uint8_t v___x_1215_; 
v___x_1215_ = 0;
return v___x_1215_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_isNull___boxed(lean_object* v_x_1216_){
_start:
{
uint8_t v_res_1217_; lean_object* v_r_1218_; 
v_res_1217_ = l_Lean_Json_isNull(v_x_1216_);
lean_dec(v_x_1216_);
v_r_1218_ = lean_box(v_res_1217_);
return v_r_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObj_x3f(lean_object* v_x_1222_){
_start:
{
if (lean_obj_tag(v_x_1222_) == 5)
{
lean_object* v_kvPairs_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
v_kvPairs_1223_ = lean_ctor_get(v_x_1222_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_x_1222_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v_x_1222_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_kvPairs_1223_);
lean_dec(v_x_1222_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
lean_ctor_set_tag(v___x_1225_, 1);
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_kvPairs_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
else
{
lean_object* v___x_1231_; 
lean_dec(v_x_1222_);
v___x_1231_ = ((lean_object*)(l_Lean_Json_getObj_x3f___closed__1));
return v___x_1231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getArr_x3f(lean_object* v_x_1235_){
_start:
{
if (lean_obj_tag(v_x_1235_) == 4)
{
lean_object* v_elems_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1243_; 
v_elems_1236_ = lean_ctor_get(v_x_1235_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_x_1235_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1238_ = v_x_1235_;
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_elems_1236_);
lean_dec(v_x_1235_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1241_; 
if (v_isShared_1239_ == 0)
{
lean_ctor_set_tag(v___x_1238_, 1);
v___x_1241_ = v___x_1238_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_elems_1236_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
else
{
lean_object* v___x_1244_; 
lean_dec(v_x_1235_);
v___x_1244_ = ((lean_object*)(l_Lean_Json_getArr_x3f___closed__1));
return v___x_1244_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getStr_x3f(lean_object* v_x_1248_){
_start:
{
if (lean_obj_tag(v_x_1248_) == 3)
{
lean_object* v_s_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
v_s_1249_ = lean_ctor_get(v_x_1248_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_x_1248_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v_x_1248_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_s_1249_);
lean_dec(v_x_1248_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
lean_ctor_set_tag(v___x_1251_, 1);
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_s_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
else
{
lean_object* v___x_1257_; 
lean_dec(v_x_1248_);
v___x_1257_ = ((lean_object*)(l_Lean_Json_getStr_x3f___closed__1));
return v___x_1257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getNat_x3f(lean_object* v_x_1261_){
_start:
{
if (lean_obj_tag(v_x_1261_) == 2)
{
lean_object* v_n_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1278_; 
v_n_1264_ = lean_ctor_get(v_x_1261_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_x_1261_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1266_ = v_x_1261_;
v_isShared_1267_ = v_isSharedCheck_1278_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_n_1264_);
lean_dec(v_x_1261_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1278_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v_mantissa_1268_; lean_object* v_exponent_1269_; lean_object* v_natZero_1270_; lean_object* v_intZero_1271_; uint8_t v_isNeg_1272_; 
v_mantissa_1268_ = lean_ctor_get(v_n_1264_, 0);
lean_inc(v_mantissa_1268_);
v_exponent_1269_ = lean_ctor_get(v_n_1264_, 1);
lean_inc(v_exponent_1269_);
lean_dec_ref(v_n_1264_);
v_natZero_1270_ = lean_unsigned_to_nat(0u);
v_intZero_1271_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v_isNeg_1272_ = lean_int_dec_lt(v_mantissa_1268_, v_intZero_1271_);
if (v_isNeg_1272_ == 0)
{
uint8_t v___x_1273_; 
v___x_1273_ = lean_nat_dec_eq(v_exponent_1269_, v_natZero_1270_);
lean_dec(v_exponent_1269_);
if (v___x_1273_ == 0)
{
lean_dec(v_mantissa_1268_);
lean_del_object(v___x_1266_);
goto v___jp_1262_;
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1276_; 
v_a_1274_ = lean_nat_abs(v_mantissa_1268_);
lean_dec(v_mantissa_1268_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set_tag(v___x_1266_, 1);
lean_ctor_set(v___x_1266_, 0, v_a_1274_);
v___x_1276_ = v___x_1266_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
else
{
lean_dec(v_exponent_1269_);
lean_dec(v_mantissa_1268_);
lean_del_object(v___x_1266_);
goto v___jp_1262_;
}
}
}
else
{
lean_dec(v_x_1261_);
goto v___jp_1262_;
}
v___jp_1262_:
{
lean_object* v___x_1263_; 
v___x_1263_ = ((lean_object*)(l_Lean_Json_getNat_x3f___closed__1));
return v___x_1263_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getInt_x3f(lean_object* v_x_1282_){
_start:
{
if (lean_obj_tag(v_x_1282_) == 2)
{
lean_object* v_n_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1296_; 
v_n_1285_ = lean_ctor_get(v_x_1282_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v_x_1282_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1287_ = v_x_1282_;
v_isShared_1288_ = v_isSharedCheck_1296_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_n_1285_);
lean_dec(v_x_1282_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1296_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v_mantissa_1289_; lean_object* v_exponent_1290_; lean_object* v___x_1291_; uint8_t v___x_1292_; 
v_mantissa_1289_ = lean_ctor_get(v_n_1285_, 0);
lean_inc(v_mantissa_1289_);
v_exponent_1290_ = lean_ctor_get(v_n_1285_, 1);
lean_inc(v_exponent_1290_);
lean_dec_ref(v_n_1285_);
v___x_1291_ = lean_unsigned_to_nat(0u);
v___x_1292_ = lean_nat_dec_eq(v_exponent_1290_, v___x_1291_);
lean_dec(v_exponent_1290_);
if (v___x_1292_ == 0)
{
lean_dec(v_mantissa_1289_);
lean_del_object(v___x_1287_);
goto v___jp_1283_;
}
else
{
lean_object* v___x_1294_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set_tag(v___x_1287_, 1);
lean_ctor_set(v___x_1287_, 0, v_mantissa_1289_);
v___x_1294_ = v___x_1287_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_mantissa_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
else
{
lean_dec(v_x_1282_);
goto v___jp_1283_;
}
v___jp_1283_:
{
lean_object* v___x_1284_; 
v___x_1284_ = ((lean_object*)(l_Lean_Json_getInt_x3f___closed__1));
return v___x_1284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getBool_x3f(lean_object* v_x_1300_){
_start:
{
if (lean_obj_tag(v_x_1300_) == 1)
{
uint8_t v_b_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v_b_1301_ = lean_ctor_get_uint8(v_x_1300_, 0);
v___x_1302_ = lean_box(v_b_1301_);
v___x_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1302_);
return v___x_1303_;
}
else
{
lean_object* v___x_1304_; 
v___x_1304_ = ((lean_object*)(l_Lean_Json_getBool_x3f___closed__1));
return v___x_1304_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getBool_x3f___boxed(lean_object* v_x_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_Json_getBool_x3f(v_x_1305_);
lean_dec(v_x_1305_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getNum_x3f(lean_object* v_x_1310_){
_start:
{
if (lean_obj_tag(v_x_1310_) == 2)
{
lean_object* v_n_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
v_n_1311_ = lean_ctor_get(v_x_1310_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v_x_1310_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v_x_1310_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_n_1311_);
lean_dec(v_x_1310_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
lean_ctor_set_tag(v___x_1313_, 1);
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_n_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
else
{
lean_object* v___x_1319_; 
lean_dec(v_x_1310_);
v___x_1319_ = ((lean_object*)(l_Lean_Json_getNum_x3f___closed__1));
return v___x_1319_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjVal_x3f(lean_object* v_x_1323_, lean_object* v_x_1324_){
_start:
{
if (lean_obj_tag(v_x_1323_) == 5)
{
lean_object* v_kvPairs_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1343_; 
v_kvPairs_1325_ = lean_ctor_get(v_x_1323_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v_x_1323_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1327_ = v_x_1323_;
v_isShared_1328_ = v_isSharedCheck_1343_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_kvPairs_1325_);
lean_dec(v_x_1323_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1343_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_kvPairs_1325_, v_x_1324_);
lean_dec(v_kvPairs_1325_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1333_; 
v___x_1330_ = ((lean_object*)(l_Lean_Json_getObjVal_x3f___closed__0));
v___x_1331_ = lean_string_append(v___x_1330_, v_x_1324_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set_tag(v___x_1327_, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1331_);
v___x_1333_ = v___x_1327_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
else
{
lean_object* v_val_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
lean_del_object(v___x_1327_);
v_val_1335_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1329_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_val_1335_);
lean_dec(v___x_1329_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_val_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
}
else
{
lean_object* v___x_1344_; 
lean_dec(v_x_1323_);
v___x_1344_ = ((lean_object*)(l_Lean_Json_getObjVal_x3f___closed__1));
return v___x_1344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjVal_x3f___boxed(lean_object* v_x_1345_, lean_object* v_x_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Lean_Json_getObjVal_x3f(v_x_1345_, v_x_1346_);
lean_dec_ref(v_x_1346_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getArrVal_x3f(lean_object* v_x_1351_, lean_object* v_x_1352_){
_start:
{
if (lean_obj_tag(v_x_1351_) == 4)
{
lean_object* v_elems_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1369_; 
v_elems_1353_ = lean_ctor_get(v_x_1351_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v_x_1351_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1355_ = v_x_1351_;
v_isShared_1356_ = v_isSharedCheck_1369_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_elems_1353_);
lean_dec(v_x_1351_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1369_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; uint8_t v___x_1358_; 
v___x_1357_ = lean_array_get_size(v_elems_1353_);
v___x_1358_ = lean_nat_dec_lt(v_x_1352_, v___x_1357_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1363_; 
lean_dec_ref(v_elems_1353_);
v___x_1359_ = ((lean_object*)(l_Lean_Json_getArrVal_x3f___closed__0));
v___x_1360_ = l_Nat_reprFast(v_x_1352_);
v___x_1361_ = lean_string_append(v___x_1359_, v___x_1360_);
lean_dec_ref(v___x_1360_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set_tag(v___x_1355_, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1361_);
v___x_1363_ = v___x_1355_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
else
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
v___x_1365_ = lean_array_fget(v_elems_1353_, v_x_1352_);
lean_dec(v_x_1352_);
lean_dec_ref(v_elems_1353_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set_tag(v___x_1355_, 1);
lean_ctor_set(v___x_1355_, 0, v___x_1365_);
v___x_1367_ = v___x_1355_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
else
{
lean_object* v___x_1370_; 
lean_dec(v_x_1352_);
lean_dec(v_x_1351_);
v___x_1370_ = ((lean_object*)(l_Lean_Json_getArrVal_x3f___closed__1));
return v___x_1370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValD(lean_object* v_j_1371_, lean_object* v_k_1372_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Lean_Json_getObjVal_x3f(v_j_1371_, v_k_1372_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v___x_1374_; 
lean_dec_ref_known(v___x_1373_, 1);
v___x_1374_ = lean_box(0);
return v___x_1374_;
}
else
{
lean_object* v_a_1375_; 
v_a_1375_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_a_1375_);
lean_dec_ref_known(v___x_1373_, 1);
return v_a_1375_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValD___boxed(lean_object* v_j_1376_, lean_object* v_k_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_Lean_Json_getObjValD(v_j_1376_, v_k_1377_);
lean_dec_ref(v_k_1377_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Json_setObjVal_x21_spec__1(lean_object* v_msg_1379_){
_start:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1380_ = lean_box(0);
v___x_1381_ = lean_panic_fn_borrowed(v___x_1380_, v_msg_1379_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(lean_object* v_msg_1382_){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = lean_box(1);
v___x_1384_ = lean_panic_fn_borrowed(v___x_1383_, v_msg_1382_);
return v___x_1384_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1388_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2));
v___x_1389_ = lean_unsigned_to_nat(35u);
v___x_1390_ = lean_unsigned_to_nat(182u);
v___x_1391_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1));
v___x_1392_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1393_ = l_mkPanicMessageWithDecl(v___x_1392_, v___x_1391_, v___x_1390_, v___x_1389_, v___x_1388_);
return v___x_1393_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1394_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2));
v___x_1395_ = lean_unsigned_to_nat(21u);
v___x_1396_ = lean_unsigned_to_nat(183u);
v___x_1397_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1));
v___x_1398_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1399_ = l_mkPanicMessageWithDecl(v___x_1398_, v___x_1397_, v___x_1396_, v___x_1395_, v___x_1394_);
return v___x_1399_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1402_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6));
v___x_1403_ = lean_unsigned_to_nat(35u);
v___x_1404_ = lean_unsigned_to_nat(276u);
v___x_1405_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5));
v___x_1406_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1407_ = l_mkPanicMessageWithDecl(v___x_1406_, v___x_1405_, v___x_1404_, v___x_1403_, v___x_1402_);
return v___x_1407_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1408_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6));
v___x_1409_ = lean_unsigned_to_nat(21u);
v___x_1410_ = lean_unsigned_to_nat(277u);
v___x_1411_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5));
v___x_1412_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1413_ = l_mkPanicMessageWithDecl(v___x_1412_, v___x_1411_, v___x_1410_, v___x_1409_, v___x_1408_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(lean_object* v_k_1414_, lean_object* v_v_1415_, lean_object* v_t_1416_){
_start:
{
if (lean_obj_tag(v_t_1416_) == 0)
{
lean_object* v_size_1417_; lean_object* v_k_1418_; lean_object* v_v_1419_; lean_object* v_l_1420_; lean_object* v_r_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1777_; 
v_size_1417_ = lean_ctor_get(v_t_1416_, 0);
v_k_1418_ = lean_ctor_get(v_t_1416_, 1);
v_v_1419_ = lean_ctor_get(v_t_1416_, 2);
v_l_1420_ = lean_ctor_get(v_t_1416_, 3);
v_r_1421_ = lean_ctor_get(v_t_1416_, 4);
v_isSharedCheck_1777_ = !lean_is_exclusive(v_t_1416_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1423_ = v_t_1416_;
v_isShared_1424_ = v_isSharedCheck_1777_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_r_1421_);
lean_inc(v_l_1420_);
lean_inc(v_v_1419_);
lean_inc(v_k_1418_);
lean_inc(v_size_1417_);
lean_dec(v_t_1416_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1777_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
uint8_t v___x_1425_; 
v___x_1425_ = lean_string_compare(v_k_1414_, v_k_1418_);
switch(v___x_1425_)
{
case 0:
{
lean_object* v___x_1426_; 
lean_dec(v_size_1417_);
v___x_1426_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1414_, v_v_1415_, v_l_1420_);
if (lean_obj_tag(v_r_1421_) == 0)
{
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_size_1427_; lean_object* v_size_1428_; lean_object* v_k_1429_; lean_object* v_v_1430_; lean_object* v_l_1431_; lean_object* v_r_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; uint8_t v___x_1435_; 
v_size_1427_ = lean_ctor_get(v_r_1421_, 0);
v_size_1428_ = lean_ctor_get(v___x_1426_, 0);
v_k_1429_ = lean_ctor_get(v___x_1426_, 1);
v_v_1430_ = lean_ctor_get(v___x_1426_, 2);
v_l_1431_ = lean_ctor_get(v___x_1426_, 3);
v_r_1432_ = lean_ctor_get(v___x_1426_, 4);
lean_inc(v_r_1432_);
v___x_1433_ = lean_unsigned_to_nat(3u);
v___x_1434_ = lean_nat_mul(v___x_1433_, v_size_1427_);
v___x_1435_ = lean_nat_dec_lt(v___x_1434_, v_size_1428_);
lean_dec(v___x_1434_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; 
lean_dec(v_r_1432_);
v___x_1436_ = lean_unsigned_to_nat(1u);
v___x_1437_ = lean_nat_add(v___x_1436_, v_size_1428_);
v___x_1438_ = lean_nat_add(v___x_1437_, v_size_1427_);
lean_dec(v___x_1437_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 3, v___x_1426_);
lean_ctor_set(v___x_1423_, 0, v___x_1438_);
v___x_1440_ = v___x_1423_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_k_1418_);
lean_ctor_set(v_reuseFailAlloc_1441_, 2, v_v_1419_);
lean_ctor_set(v_reuseFailAlloc_1441_, 3, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1441_, 4, v_r_1421_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
else
{
lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1513_; 
lean_inc(v_l_1431_);
lean_inc(v_v_1430_);
lean_inc(v_k_1429_);
lean_inc(v_size_1428_);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1513_ == 0)
{
lean_object* v_unused_1514_; lean_object* v_unused_1515_; lean_object* v_unused_1516_; lean_object* v_unused_1517_; lean_object* v_unused_1518_; 
v_unused_1514_ = lean_ctor_get(v___x_1426_, 4);
lean_dec(v_unused_1514_);
v_unused_1515_ = lean_ctor_get(v___x_1426_, 3);
lean_dec(v_unused_1515_);
v_unused_1516_ = lean_ctor_get(v___x_1426_, 2);
lean_dec(v_unused_1516_);
v_unused_1517_ = lean_ctor_get(v___x_1426_, 1);
lean_dec(v_unused_1517_);
v_unused_1518_ = lean_ctor_get(v___x_1426_, 0);
lean_dec(v_unused_1518_);
v___x_1443_ = v___x_1426_;
v_isShared_1444_ = v_isSharedCheck_1513_;
goto v_resetjp_1442_;
}
else
{
lean_dec(v___x_1426_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1513_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
if (lean_obj_tag(v_l_1431_) == 0)
{
if (lean_obj_tag(v_r_1432_) == 0)
{
lean_object* v_size_1445_; lean_object* v_size_1446_; lean_object* v_k_1447_; lean_object* v_v_1448_; lean_object* v_l_1449_; lean_object* v_r_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; uint8_t v___x_1453_; 
v_size_1445_ = lean_ctor_get(v_l_1431_, 0);
v_size_1446_ = lean_ctor_get(v_r_1432_, 0);
v_k_1447_ = lean_ctor_get(v_r_1432_, 1);
v_v_1448_ = lean_ctor_get(v_r_1432_, 2);
v_l_1449_ = lean_ctor_get(v_r_1432_, 3);
v_r_1450_ = lean_ctor_get(v_r_1432_, 4);
v___x_1451_ = lean_unsigned_to_nat(2u);
v___x_1452_ = lean_nat_mul(v___x_1451_, v_size_1445_);
v___x_1453_ = lean_nat_dec_lt(v_size_1446_, v___x_1452_);
lean_dec(v___x_1452_);
if (v___x_1453_ == 0)
{
lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1483_; 
lean_inc(v_r_1450_);
lean_inc(v_l_1449_);
lean_inc(v_v_1448_);
lean_inc(v_k_1447_);
v_isSharedCheck_1483_ = !lean_is_exclusive(v_r_1432_);
if (v_isSharedCheck_1483_ == 0)
{
lean_object* v_unused_1484_; lean_object* v_unused_1485_; lean_object* v_unused_1486_; lean_object* v_unused_1487_; lean_object* v_unused_1488_; 
v_unused_1484_ = lean_ctor_get(v_r_1432_, 4);
lean_dec(v_unused_1484_);
v_unused_1485_ = lean_ctor_get(v_r_1432_, 3);
lean_dec(v_unused_1485_);
v_unused_1486_ = lean_ctor_get(v_r_1432_, 2);
lean_dec(v_unused_1486_);
v_unused_1487_ = lean_ctor_get(v_r_1432_, 1);
lean_dec(v_unused_1487_);
v_unused_1488_ = lean_ctor_get(v_r_1432_, 0);
lean_dec(v_unused_1488_);
v___x_1455_ = v_r_1432_;
v_isShared_1456_ = v_isSharedCheck_1483_;
goto v_resetjp_1454_;
}
else
{
lean_dec(v_r_1432_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1483_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___x_1471_; lean_object* v___y_1473_; 
v___x_1457_ = lean_unsigned_to_nat(1u);
v___x_1458_ = lean_nat_add(v___x_1457_, v_size_1428_);
lean_dec(v_size_1428_);
v___x_1459_ = lean_nat_add(v___x_1458_, v_size_1427_);
lean_dec(v___x_1458_);
v___x_1471_ = lean_nat_add(v___x_1457_, v_size_1445_);
if (lean_obj_tag(v_l_1449_) == 0)
{
lean_object* v_size_1481_; 
v_size_1481_ = lean_ctor_get(v_l_1449_, 0);
lean_inc(v_size_1481_);
v___y_1473_ = v_size_1481_;
goto v___jp_1472_;
}
else
{
lean_object* v___x_1482_; 
v___x_1482_ = lean_unsigned_to_nat(0u);
v___y_1473_ = v___x_1482_;
goto v___jp_1472_;
}
v___jp_1460_:
{
lean_object* v___x_1464_; lean_object* v___x_1466_; 
v___x_1464_ = lean_nat_add(v___y_1462_, v___y_1463_);
lean_dec(v___y_1463_);
lean_dec(v___y_1462_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 4, v_r_1421_);
lean_ctor_set(v___x_1455_, 3, v_r_1450_);
lean_ctor_set(v___x_1455_, 2, v_v_1419_);
lean_ctor_set(v___x_1455_, 1, v_k_1418_);
lean_ctor_set(v___x_1455_, 0, v___x_1464_);
v___x_1466_ = v___x_1455_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1464_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_k_1418_);
lean_ctor_set(v_reuseFailAlloc_1470_, 2, v_v_1419_);
lean_ctor_set(v_reuseFailAlloc_1470_, 3, v_r_1450_);
lean_ctor_set(v_reuseFailAlloc_1470_, 4, v_r_1421_);
v___x_1466_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
lean_object* v___x_1468_; 
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 4, v___x_1466_);
lean_ctor_set(v___x_1443_, 3, v___y_1461_);
lean_ctor_set(v___x_1443_, 2, v_v_1448_);
lean_ctor_set(v___x_1443_, 1, v_k_1447_);
lean_ctor_set(v___x_1443_, 0, v___x_1459_);
v___x_1468_ = v___x_1443_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1459_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v_k_1447_);
lean_ctor_set(v_reuseFailAlloc_1469_, 2, v_v_1448_);
lean_ctor_set(v_reuseFailAlloc_1469_, 3, v___y_1461_);
lean_ctor_set(v_reuseFailAlloc_1469_, 4, v___x_1466_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
v___jp_1472_:
{
lean_object* v___x_1474_; lean_object* v___x_1476_; 
v___x_1474_ = lean_nat_add(v___x_1471_, v___y_1473_);
lean_dec(v___y_1473_);
lean_dec(v___x_1471_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 4, v_l_1449_);
lean_ctor_set(v___x_1423_, 3, v_l_1431_);
lean_ctor_set(v___x_1423_, 2, v_v_1430_);
lean_ctor_set(v___x_1423_, 1, v_k_1429_);
lean_ctor_set(v___x_1423_, 0, v___x_1474_);
v___x_1476_ = v___x_1423_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_k_1429_);
lean_ctor_set(v_reuseFailAlloc_1480_, 2, v_v_1430_);
lean_ctor_set(v_reuseFailAlloc_1480_, 3, v_l_1431_);
lean_ctor_set(v_reuseFailAlloc_1480_, 4, v_l_1449_);
v___x_1476_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
lean_object* v___x_1477_; 
v___x_1477_ = lean_nat_add(v___x_1457_, v_size_1427_);
if (lean_obj_tag(v_r_1450_) == 0)
{
lean_object* v_size_1478_; 
v_size_1478_ = lean_ctor_get(v_r_1450_, 0);
lean_inc(v_size_1478_);
v___y_1461_ = v___x_1476_;
v___y_1462_ = v___x_1477_;
v___y_1463_ = v_size_1478_;
goto v___jp_1460_;
}
else
{
lean_object* v___x_1479_; 
v___x_1479_ = lean_unsigned_to_nat(0u);
v___y_1461_ = v___x_1476_;
v___y_1462_ = v___x_1477_;
v___y_1463_ = v___x_1479_;
goto v___jp_1460_;
}
}
}
}
}
else
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1495_; 
lean_del_object(v___x_1423_);
v___x_1489_ = lean_unsigned_to_nat(1u);
v___x_1490_ = lean_nat_add(v___x_1489_, v_size_1428_);
lean_dec(v_size_1428_);
v___x_1491_ = lean_nat_add(v___x_1490_, v_size_1427_);
lean_dec(v___x_1490_);
v___x_1492_ = lean_nat_add(v___x_1489_, v_size_1427_);
v___x_1493_ = lean_nat_add(v___x_1492_, v_size_1446_);
lean_dec(v___x_1492_);
lean_inc_ref(v_r_1421_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 4, v_r_1421_);
lean_ctor_set(v___x_1443_, 3, v_r_1432_);
lean_ctor_set(v___x_1443_, 2, v_v_1419_);
lean_ctor_set(v___x_1443_, 1, v_k_1418_);
lean_ctor_set(v___x_1443_, 0, v___x_1493_);
v___x_1495_ = v___x_1443_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1493_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_k_1418_);
lean_ctor_set(v_reuseFailAlloc_1508_, 2, v_v_1419_);
lean_ctor_set(v_reuseFailAlloc_1508_, 3, v_r_1432_);
lean_ctor_set(v_reuseFailAlloc_1508_, 4, v_r_1421_);
v___x_1495_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
v_isSharedCheck_1502_ = !lean_is_exclusive(v_r_1421_);
if (v_isSharedCheck_1502_ == 0)
{
lean_object* v_unused_1503_; lean_object* v_unused_1504_; lean_object* v_unused_1505_; lean_object* v_unused_1506_; lean_object* v_unused_1507_; 
v_unused_1503_ = lean_ctor_get(v_r_1421_, 4);
lean_dec(v_unused_1503_);
v_unused_1504_ = lean_ctor_get(v_r_1421_, 3);
lean_dec(v_unused_1504_);
v_unused_1505_ = lean_ctor_get(v_r_1421_, 2);
lean_dec(v_unused_1505_);
v_unused_1506_ = lean_ctor_get(v_r_1421_, 1);
lean_dec(v_unused_1506_);
v_unused_1507_ = lean_ctor_get(v_r_1421_, 0);
lean_dec(v_unused_1507_);
v___x_1497_ = v_r_1421_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_dec(v_r_1421_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 4, v___x_1495_);
lean_ctor_set(v___x_1497_, 3, v_l_1431_);
lean_ctor_set(v___x_1497_, 2, v_v_1430_);
lean_ctor_set(v___x_1497_, 1, v_k_1429_);
lean_ctor_set(v___x_1497_, 0, v___x_1491_);
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1491_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_k_1429_);
lean_ctor_set(v_reuseFailAlloc_1501_, 2, v_v_1430_);
lean_ctor_set(v_reuseFailAlloc_1501_, 3, v_l_1431_);
lean_ctor_set(v_reuseFailAlloc_1501_, 4, v___x_1495_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
}
else
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
lean_dec_ref_known(v_l_1431_, 5);
lean_del_object(v___x_1443_);
lean_dec(v_v_1430_);
lean_dec(v_k_1429_);
lean_dec(v_size_1428_);
lean_dec_ref_known(v_r_1421_, 5);
lean_del_object(v___x_1423_);
lean_dec(v_v_1419_);
lean_dec(v_k_1418_);
v___x_1509_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3);
v___x_1510_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1509_);
return v___x_1510_;
}
}
else
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
lean_del_object(v___x_1443_);
lean_dec(v_r_1432_);
lean_dec(v_v_1430_);
lean_dec(v_k_1429_);
lean_dec(v_size_1428_);
lean_dec_ref_known(v_r_1421_, 5);
lean_del_object(v___x_1423_);
lean_dec(v_v_1419_);
lean_dec(v_k_1418_);
v___x_1511_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4);
v___x_1512_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1511_);
return v___x_1512_;
}
}
}
}
else
{
lean_object* v_size_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1523_; 
v_size_1519_ = lean_ctor_get(v_r_1421_, 0);
v___x_1520_ = lean_unsigned_to_nat(1u);
v___x_1521_ = lean_nat_add(v___x_1520_, v_size_1519_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 3, v___x_1426_);
lean_ctor_set(v___x_1423_, 0, v___x_1521_);
v___x_1523_ = v___x_1423_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1521_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_k_1418_);
lean_ctor_set(v_reuseFailAlloc_1524_, 2, v_v_1419_);
lean_ctor_set(v_reuseFailAlloc_1524_, 3, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1524_, 4, v_r_1421_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
else
{
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_l_1525_; 
v_l_1525_ = lean_ctor_get(v___x_1426_, 3);
if (lean_obj_tag(v_l_1525_) == 0)
{
lean_object* v_r_1526_; 
lean_inc_ref(v_l_1525_);
v_r_1526_ = lean_ctor_get(v___x_1426_, 4);
lean_inc(v_r_1526_);
if (lean_obj_tag(v_r_1526_) == 0)
{
lean_object* v_size_1527_; lean_object* v_k_1528_; lean_object* v_v_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1543_; 
v_size_1527_ = lean_ctor_get(v___x_1426_, 0);
v_k_1528_ = lean_ctor_get(v___x_1426_, 1);
v_v_1529_ = lean_ctor_get(v___x_1426_, 2);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1543_ == 0)
{
lean_object* v_unused_1544_; lean_object* v_unused_1545_; 
v_unused_1544_ = lean_ctor_get(v___x_1426_, 4);
lean_dec(v_unused_1544_);
v_unused_1545_ = lean_ctor_get(v___x_1426_, 3);
lean_dec(v_unused_1545_);
v___x_1531_ = v___x_1426_;
v_isShared_1532_ = v_isSharedCheck_1543_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_v_1529_);
lean_inc(v_k_1528_);
lean_inc(v_size_1527_);
lean_dec(v___x_1426_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1543_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v_size_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1538_; 
v_size_1533_ = lean_ctor_get(v_r_1526_, 0);
v___x_1534_ = lean_unsigned_to_nat(1u);
v___x_1535_ = lean_nat_add(v___x_1534_, v_size_1527_);
lean_dec(v_size_1527_);
v___x_1536_ = lean_nat_add(v___x_1534_, v_size_1533_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 4, v_r_1421_);
lean_ctor_set(v___x_1531_, 3, v_r_1526_);
lean_ctor_set(v___x_1531_, 2, v_v_1419_);
lean_ctor_set(v___x_1531_, 1, v_k_1418_);
lean_ctor_set(v___x_1531_, 0, v___x_1536_);
v___x_1538_ = v___x_1531_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_k_1418_);
lean_ctor_set(v_reuseFailAlloc_1542_, 2, v_v_1419_);
lean_ctor_set(v_reuseFailAlloc_1542_, 3, v_r_1526_);
lean_ctor_set(v_reuseFailAlloc_1542_, 4, v_r_1421_);
v___x_1538_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
lean_object* v___x_1540_; 
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 4, v___x_1538_);
lean_ctor_set(v___x_1423_, 3, v_l_1525_);
lean_ctor_set(v___x_1423_, 2, v_v_1529_);
lean_ctor_set(v___x_1423_, 1, v_k_1528_);
lean_ctor_set(v___x_1423_, 0, v___x_1535_);
v___x_1540_ = v___x_1423_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1535_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_k_1528_);
lean_ctor_set(v_reuseFailAlloc_1541_, 2, v_v_1529_);
lean_ctor_set(v_reuseFailAlloc_1541_, 3, v_l_1525_);
lean_ctor_set(v_reuseFailAlloc_1541_, 4, v___x_1538_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
else
{
lean_object* v_k_1546_; lean_object* v_v_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1559_; 
v_k_1546_ = lean_ctor_get(v___x_1426_, 1);
v_v_1547_ = lean_ctor_get(v___x_1426_, 2);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1559_ == 0)
{
lean_object* v_unused_1560_; lean_object* v_unused_1561_; lean_object* v_unused_1562_; 
v_unused_1560_ = lean_ctor_get(v___x_1426_, 4);
lean_dec(v_unused_1560_);
v_unused_1561_ = lean_ctor_get(v___x_1426_, 3);
lean_dec(v_unused_1561_);
v_unused_1562_ = lean_ctor_get(v___x_1426_, 0);
lean_dec(v_unused_1562_);
v___x_1549_ = v___x_1426_;
v_isShared_1550_ = v_isSharedCheck_1559_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_v_1547_);
lean_inc(v_k_1546_);
lean_dec(v___x_1426_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1559_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1554_; 
v___x_1551_ = lean_unsigned_to_nat(3u);
v___x_1552_ = lean_unsigned_to_nat(1u);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 3, v_r_1526_);
lean_ctor_set(v___x_1549_, 2, v_v_1419_);
lean_ctor_set(v___x_1549_, 1, v_k_1418_);
lean_ctor_set(v___x_1549_, 0, v___x_1552_);
v___x_1554_ = v___x_1549_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1552_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_k_1418_);
lean_ctor_set(v_reuseFailAlloc_1558_, 2, v_v_1419_);
lean_ctor_set(v_reuseFailAlloc_1558_, 3, v_r_1526_);
lean_ctor_set(v_reuseFailAlloc_1558_, 4, v_r_1526_);
v___x_1554_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
lean_object* v___x_1556_; 
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 4, v___x_1554_);
lean_ctor_set(v___x_1423_, 3, v_l_1525_);
lean_ctor_set(v___x_1423_, 2, v_v_1547_);
lean_ctor_set(v___x_1423_, 1, v_k_1546_);
lean_ctor_set(v___x_1423_, 0, v___x_1551_);
v___x_1556_ = v___x_1423_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1551_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v_k_1546_);
lean_ctor_set(v_reuseFailAlloc_1557_, 2, v_v_1547_);
lean_ctor_set(v_reuseFailAlloc_1557_, 3, v_l_1525_);
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
}
else
{
lean_object* v_r_1563_; 
v_r_1563_ = lean_ctor_get(v___x_1426_, 4);
lean_inc(v_r_1563_);
if (lean_obj_tag(v_r_1563_) == 0)
{
lean_object* v_k_1564_; lean_object* v_v_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1589_; 
lean_inc(v_l_1525_);
v_k_1564_ = lean_ctor_get(v___x_1426_, 1);
v_v_1565_ = lean_ctor_get(v___x_1426_, 2);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1589_ == 0)
{
lean_object* v_unused_1590_; lean_object* v_unused_1591_; lean_object* v_unused_1592_; 
v_unused_1590_ = lean_ctor_get(v___x_1426_, 4);
lean_dec(v_unused_1590_);
v_unused_1591_ = lean_ctor_get(v___x_1426_, 3);
lean_dec(v_unused_1591_);
v_unused_1592_ = lean_ctor_get(v___x_1426_, 0);
lean_dec(v_unused_1592_);
v___x_1567_ = v___x_1426_;
v_isShared_1568_ = v_isSharedCheck_1589_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_v_1565_);
lean_inc(v_k_1564_);
lean_dec(v___x_1426_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1589_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v_k_1569_; lean_object* v_v_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1585_; 
v_k_1569_ = lean_ctor_get(v_r_1563_, 1);
v_v_1570_ = lean_ctor_get(v_r_1563_, 2);
v_isSharedCheck_1585_ = !lean_is_exclusive(v_r_1563_);
if (v_isSharedCheck_1585_ == 0)
{
lean_object* v_unused_1586_; lean_object* v_unused_1587_; lean_object* v_unused_1588_; 
v_unused_1586_ = lean_ctor_get(v_r_1563_, 4);
lean_dec(v_unused_1586_);
v_unused_1587_ = lean_ctor_get(v_r_1563_, 3);
lean_dec(v_unused_1587_);
v_unused_1588_ = lean_ctor_get(v_r_1563_, 0);
lean_dec(v_unused_1588_);
v___x_1572_ = v_r_1563_;
v_isShared_1573_ = v_isSharedCheck_1585_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_v_1570_);
lean_inc(v_k_1569_);
lean_dec(v_r_1563_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1585_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1577_; 
v___x_1574_ = lean_unsigned_to_nat(3u);
v___x_1575_ = lean_unsigned_to_nat(1u);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 4, v_l_1525_);
lean_ctor_set(v___x_1572_, 3, v_l_1525_);
lean_ctor_set(v___x_1572_, 2, v_v_1565_);
lean_ctor_set(v___x_1572_, 1, v_k_1564_);
lean_ctor_set(v___x_1572_, 0, v___x_1575_);
v___x_1577_ = v___x_1572_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1575_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v_k_1564_);
lean_ctor_set(v_reuseFailAlloc_1584_, 2, v_v_1565_);
lean_ctor_set(v_reuseFailAlloc_1584_, 3, v_l_1525_);
lean_ctor_set(v_reuseFailAlloc_1584_, 4, v_l_1525_);
v___x_1577_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
lean_object* v___x_1579_; 
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 4, v_l_1525_);
lean_ctor_set(v___x_1567_, 2, v_v_1419_);
lean_ctor_set(v___x_1567_, 1, v_k_1418_);
lean_ctor_set(v___x_1567_, 0, v___x_1575_);
v___x_1579_ = v___x_1567_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1575_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v_k_1418_);
lean_ctor_set(v_reuseFailAlloc_1583_, 2, v_v_1419_);
lean_ctor_set(v_reuseFailAlloc_1583_, 3, v_l_1525_);
lean_ctor_set(v_reuseFailAlloc_1583_, 4, v_l_1525_);
v___x_1579_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
lean_object* v___x_1581_; 
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 4, v___x_1579_);
lean_ctor_set(v___x_1423_, 3, v___x_1577_);
lean_ctor_set(v___x_1423_, 2, v_v_1570_);
lean_ctor_set(v___x_1423_, 1, v_k_1569_);
lean_ctor_set(v___x_1423_, 0, v___x_1574_);
v___x_1581_ = v___x_1423_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1574_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v_k_1569_);
lean_ctor_set(v_reuseFailAlloc_1582_, 2, v_v_1570_);
lean_ctor_set(v_reuseFailAlloc_1582_, 3, v___x_1577_);
lean_ctor_set(v_reuseFailAlloc_1582_, 4, v___x_1579_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
}
}
else
{
lean_object* v___x_1593_; lean_object* v___x_1595_; 
v___x_1593_ = lean_unsigned_to_nat(2u);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 4, v_r_1563_);
lean_ctor_set(v___x_1423_, 3, v___x_1426_);
lean_ctor_set(v___x_1423_, 0, v___x_1593_);
v___x_1595_ = v___x_1423_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1593_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_k_1418_);
lean_ctor_set(v_reuseFailAlloc_1596_, 2, v_v_1419_);
lean_ctor_set(v_reuseFailAlloc_1596_, 3, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1596_, 4, v_r_1563_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
else
{
lean_object* v___x_1597_; lean_object* v___x_1599_; 
v___x_1597_ = lean_unsigned_to_nat(1u);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 4, v___x_1426_);
lean_ctor_set(v___x_1423_, 3, v___x_1426_);
lean_ctor_set(v___x_1423_, 0, v___x_1597_);
v___x_1599_ = v___x_1423_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v_k_1418_);
lean_ctor_set(v_reuseFailAlloc_1600_, 2, v_v_1419_);
lean_ctor_set(v_reuseFailAlloc_1600_, 3, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1600_, 4, v___x_1426_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
case 1:
{
lean_object* v___x_1602_; 
lean_dec(v_v_1419_);
lean_dec(v_k_1418_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 2, v_v_1415_);
lean_ctor_set(v___x_1423_, 1, v_k_1414_);
v___x_1602_ = v___x_1423_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_size_1417_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_k_1414_);
lean_ctor_set(v_reuseFailAlloc_1603_, 2, v_v_1415_);
lean_ctor_set(v_reuseFailAlloc_1603_, 3, v_l_1420_);
lean_ctor_set(v_reuseFailAlloc_1603_, 4, v_r_1421_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
default: 
{
lean_object* v___x_1604_; 
lean_dec(v_size_1417_);
v___x_1604_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1414_, v_v_1415_, v_r_1421_);
if (lean_obj_tag(v_l_1420_) == 0)
{
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_size_1605_; lean_object* v_size_1606_; lean_object* v_k_1607_; lean_object* v_v_1608_; lean_object* v_l_1609_; lean_object* v_r_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; 
v_size_1605_ = lean_ctor_get(v_l_1420_, 0);
v_size_1606_ = lean_ctor_get(v___x_1604_, 0);
v_k_1607_ = lean_ctor_get(v___x_1604_, 1);
v_v_1608_ = lean_ctor_get(v___x_1604_, 2);
v_l_1609_ = lean_ctor_get(v___x_1604_, 3);
lean_inc(v_l_1609_);
v_r_1610_ = lean_ctor_get(v___x_1604_, 4);
v___x_1611_ = lean_unsigned_to_nat(3u);
v___x_1612_ = lean_nat_mul(v___x_1611_, v_size_1605_);
v___x_1613_ = lean_nat_dec_lt(v___x_1612_, v_size_1606_);
lean_dec(v___x_1612_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1618_; 
lean_dec(v_l_1609_);
v___x_1614_ = lean_unsigned_to_nat(1u);
v___x_1615_ = lean_nat_add(v___x_1614_, v_size_1605_);
v___x_1616_ = lean_nat_add(v___x_1615_, v_size_1606_);
lean_dec(v___x_1615_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 4, v___x_1604_);
lean_ctor_set(v___x_1423_, 0, v___x_1616_);
v___x_1618_ = v___x_1423_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1616_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_k_1418_);
lean_ctor_set(v_reuseFailAlloc_1619_, 2, v_v_1419_);
lean_ctor_set(v_reuseFailAlloc_1619_, 3, v_l_1420_);
lean_ctor_set(v_reuseFailAlloc_1619_, 4, v___x_1604_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
else
{
lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1689_; 
lean_inc(v_r_1610_);
lean_inc(v_v_1608_);
lean_inc(v_k_1607_);
lean_inc(v_size_1606_);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1689_ == 0)
{
lean_object* v_unused_1690_; lean_object* v_unused_1691_; lean_object* v_unused_1692_; lean_object* v_unused_1693_; lean_object* v_unused_1694_; 
v_unused_1690_ = lean_ctor_get(v___x_1604_, 4);
lean_dec(v_unused_1690_);
v_unused_1691_ = lean_ctor_get(v___x_1604_, 3);
lean_dec(v_unused_1691_);
v_unused_1692_ = lean_ctor_get(v___x_1604_, 2);
lean_dec(v_unused_1692_);
v_unused_1693_ = lean_ctor_get(v___x_1604_, 1);
lean_dec(v_unused_1693_);
v_unused_1694_ = lean_ctor_get(v___x_1604_, 0);
lean_dec(v_unused_1694_);
v___x_1621_ = v___x_1604_;
v_isShared_1622_ = v_isSharedCheck_1689_;
goto v_resetjp_1620_;
}
else
{
lean_dec(v___x_1604_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1689_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
if (lean_obj_tag(v_l_1609_) == 0)
{
if (lean_obj_tag(v_r_1610_) == 0)
{
lean_object* v_size_1623_; lean_object* v_k_1624_; lean_object* v_v_1625_; lean_object* v_l_1626_; lean_object* v_r_1627_; lean_object* v_size_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; uint8_t v___x_1631_; 
v_size_1623_ = lean_ctor_get(v_l_1609_, 0);
v_k_1624_ = lean_ctor_get(v_l_1609_, 1);
v_v_1625_ = lean_ctor_get(v_l_1609_, 2);
v_l_1626_ = lean_ctor_get(v_l_1609_, 3);
v_r_1627_ = lean_ctor_get(v_l_1609_, 4);
v_size_1628_ = lean_ctor_get(v_r_1610_, 0);
v___x_1629_ = lean_unsigned_to_nat(2u);
v___x_1630_ = lean_nat_mul(v___x_1629_, v_size_1628_);
v___x_1631_ = lean_nat_dec_lt(v_size_1623_, v___x_1630_);
lean_dec(v___x_1630_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1660_; 
lean_inc(v_r_1627_);
lean_inc(v_l_1626_);
lean_inc(v_v_1625_);
lean_inc(v_k_1624_);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_l_1609_);
if (v_isSharedCheck_1660_ == 0)
{
lean_object* v_unused_1661_; lean_object* v_unused_1662_; lean_object* v_unused_1663_; lean_object* v_unused_1664_; lean_object* v_unused_1665_; 
v_unused_1661_ = lean_ctor_get(v_l_1609_, 4);
lean_dec(v_unused_1661_);
v_unused_1662_ = lean_ctor_get(v_l_1609_, 3);
lean_dec(v_unused_1662_);
v_unused_1663_ = lean_ctor_get(v_l_1609_, 2);
lean_dec(v_unused_1663_);
v_unused_1664_ = lean_ctor_get(v_l_1609_, 1);
lean_dec(v_unused_1664_);
v_unused_1665_ = lean_ctor_get(v_l_1609_, 0);
lean_dec(v_unused_1665_);
v___x_1633_ = v_l_1609_;
v_isShared_1634_ = v_isSharedCheck_1660_;
goto v_resetjp_1632_;
}
else
{
lean_dec(v_l_1609_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1660_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1650_; 
v___x_1635_ = lean_unsigned_to_nat(1u);
v___x_1636_ = lean_nat_add(v___x_1635_, v_size_1605_);
v___x_1637_ = lean_nat_add(v___x_1636_, v_size_1606_);
lean_dec(v_size_1606_);
if (lean_obj_tag(v_l_1626_) == 0)
{
lean_object* v_size_1658_; 
v_size_1658_ = lean_ctor_get(v_l_1626_, 0);
lean_inc(v_size_1658_);
v___y_1650_ = v_size_1658_;
goto v___jp_1649_;
}
else
{
lean_object* v___x_1659_; 
v___x_1659_ = lean_unsigned_to_nat(0u);
v___y_1650_ = v___x_1659_;
goto v___jp_1649_;
}
v___jp_1638_:
{
lean_object* v___x_1642_; lean_object* v___x_1644_; 
v___x_1642_ = lean_nat_add(v___y_1640_, v___y_1641_);
lean_dec(v___y_1641_);
lean_dec(v___y_1640_);
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 4, v_r_1610_);
lean_ctor_set(v___x_1633_, 3, v_r_1627_);
lean_ctor_set(v___x_1633_, 2, v_v_1608_);
lean_ctor_set(v___x_1633_, 1, v_k_1607_);
lean_ctor_set(v___x_1633_, 0, v___x_1642_);
v___x_1644_ = v___x_1633_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1642_);
lean_ctor_set(v_reuseFailAlloc_1648_, 1, v_k_1607_);
lean_ctor_set(v_reuseFailAlloc_1648_, 2, v_v_1608_);
lean_ctor_set(v_reuseFailAlloc_1648_, 3, v_r_1627_);
lean_ctor_set(v_reuseFailAlloc_1648_, 4, v_r_1610_);
v___x_1644_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
lean_object* v___x_1646_; 
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 4, v___x_1644_);
lean_ctor_set(v___x_1621_, 3, v___y_1639_);
lean_ctor_set(v___x_1621_, 2, v_v_1625_);
lean_ctor_set(v___x_1621_, 1, v_k_1624_);
lean_ctor_set(v___x_1621_, 0, v___x_1637_);
v___x_1646_ = v___x_1621_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1637_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v_k_1624_);
lean_ctor_set(v_reuseFailAlloc_1647_, 2, v_v_1625_);
lean_ctor_set(v_reuseFailAlloc_1647_, 3, v___y_1639_);
lean_ctor_set(v_reuseFailAlloc_1647_, 4, v___x_1644_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
v___jp_1649_:
{
lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1651_ = lean_nat_add(v___x_1636_, v___y_1650_);
lean_dec(v___y_1650_);
lean_dec(v___x_1636_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 4, v_l_1626_);
lean_ctor_set(v___x_1423_, 0, v___x_1651_);
v___x_1653_ = v___x_1423_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1651_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_k_1418_);
lean_ctor_set(v_reuseFailAlloc_1657_, 2, v_v_1419_);
lean_ctor_set(v_reuseFailAlloc_1657_, 3, v_l_1420_);
lean_ctor_set(v_reuseFailAlloc_1657_, 4, v_l_1626_);
v___x_1653_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_nat_add(v___x_1635_, v_size_1628_);
if (lean_obj_tag(v_r_1627_) == 0)
{
lean_object* v_size_1655_; 
v_size_1655_ = lean_ctor_get(v_r_1627_, 0);
lean_inc(v_size_1655_);
v___y_1639_ = v___x_1653_;
v___y_1640_ = v___x_1654_;
v___y_1641_ = v_size_1655_;
goto v___jp_1638_;
}
else
{
lean_object* v___x_1656_; 
v___x_1656_ = lean_unsigned_to_nat(0u);
v___y_1639_ = v___x_1653_;
v___y_1640_ = v___x_1654_;
v___y_1641_ = v___x_1656_;
goto v___jp_1638_;
}
}
}
}
}
else
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1671_; 
lean_del_object(v___x_1423_);
v___x_1666_ = lean_unsigned_to_nat(1u);
v___x_1667_ = lean_nat_add(v___x_1666_, v_size_1605_);
v___x_1668_ = lean_nat_add(v___x_1667_, v_size_1606_);
lean_dec(v_size_1606_);
v___x_1669_ = lean_nat_add(v___x_1667_, v_size_1623_);
lean_dec(v___x_1667_);
lean_inc_ref(v_l_1420_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 4, v_l_1609_);
lean_ctor_set(v___x_1621_, 3, v_l_1420_);
lean_ctor_set(v___x_1621_, 2, v_v_1419_);
lean_ctor_set(v___x_1621_, 1, v_k_1418_);
lean_ctor_set(v___x_1621_, 0, v___x_1669_);
v___x_1671_ = v___x_1621_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1669_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_k_1418_);
lean_ctor_set(v_reuseFailAlloc_1684_, 2, v_v_1419_);
lean_ctor_set(v_reuseFailAlloc_1684_, 3, v_l_1420_);
lean_ctor_set(v_reuseFailAlloc_1684_, 4, v_l_1609_);
v___x_1671_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
v_isSharedCheck_1678_ = !lean_is_exclusive(v_l_1420_);
if (v_isSharedCheck_1678_ == 0)
{
lean_object* v_unused_1679_; lean_object* v_unused_1680_; lean_object* v_unused_1681_; lean_object* v_unused_1682_; lean_object* v_unused_1683_; 
v_unused_1679_ = lean_ctor_get(v_l_1420_, 4);
lean_dec(v_unused_1679_);
v_unused_1680_ = lean_ctor_get(v_l_1420_, 3);
lean_dec(v_unused_1680_);
v_unused_1681_ = lean_ctor_get(v_l_1420_, 2);
lean_dec(v_unused_1681_);
v_unused_1682_ = lean_ctor_get(v_l_1420_, 1);
lean_dec(v_unused_1682_);
v_unused_1683_ = lean_ctor_get(v_l_1420_, 0);
lean_dec(v_unused_1683_);
v___x_1673_ = v_l_1420_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_dec(v_l_1420_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 4, v_r_1610_);
lean_ctor_set(v___x_1673_, 3, v___x_1671_);
lean_ctor_set(v___x_1673_, 2, v_v_1608_);
lean_ctor_set(v___x_1673_, 1, v_k_1607_);
lean_ctor_set(v___x_1673_, 0, v___x_1668_);
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1668_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v_k_1607_);
lean_ctor_set(v_reuseFailAlloc_1677_, 2, v_v_1608_);
lean_ctor_set(v_reuseFailAlloc_1677_, 3, v___x_1671_);
lean_ctor_set(v_reuseFailAlloc_1677_, 4, v_r_1610_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
}
else
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
lean_dec_ref_known(v_l_1609_, 5);
lean_del_object(v___x_1621_);
lean_dec(v_v_1608_);
lean_dec(v_k_1607_);
lean_dec(v_size_1606_);
lean_dec_ref_known(v_l_1420_, 5);
lean_del_object(v___x_1423_);
lean_dec(v_v_1419_);
lean_dec(v_k_1418_);
v___x_1685_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7);
v___x_1686_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1685_);
return v___x_1686_;
}
}
else
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
lean_del_object(v___x_1621_);
lean_dec(v_r_1610_);
lean_dec(v_v_1608_);
lean_dec(v_k_1607_);
lean_dec(v_size_1606_);
lean_dec_ref_known(v_l_1420_, 5);
lean_del_object(v___x_1423_);
lean_dec(v_v_1419_);
lean_dec(v_k_1418_);
v___x_1687_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8);
v___x_1688_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1687_);
return v___x_1688_;
}
}
}
}
else
{
lean_object* v_size_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1699_; 
v_size_1695_ = lean_ctor_get(v_l_1420_, 0);
v___x_1696_ = lean_unsigned_to_nat(1u);
v___x_1697_ = lean_nat_add(v___x_1696_, v_size_1695_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 4, v___x_1604_);
lean_ctor_set(v___x_1423_, 0, v___x_1697_);
v___x_1699_ = v___x_1423_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1697_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v_k_1418_);
lean_ctor_set(v_reuseFailAlloc_1700_, 2, v_v_1419_);
lean_ctor_set(v_reuseFailAlloc_1700_, 3, v_l_1420_);
lean_ctor_set(v_reuseFailAlloc_1700_, 4, v___x_1604_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
else
{
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_l_1701_; 
v_l_1701_ = lean_ctor_get(v___x_1604_, 3);
lean_inc(v_l_1701_);
if (lean_obj_tag(v_l_1701_) == 0)
{
lean_object* v_r_1702_; 
v_r_1702_ = lean_ctor_get(v___x_1604_, 4);
lean_inc(v_r_1702_);
if (lean_obj_tag(v_r_1702_) == 0)
{
lean_object* v_size_1703_; lean_object* v_k_1704_; lean_object* v_v_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1719_; 
v_size_1703_ = lean_ctor_get(v___x_1604_, 0);
v_k_1704_ = lean_ctor_get(v___x_1604_, 1);
v_v_1705_ = lean_ctor_get(v___x_1604_, 2);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1719_ == 0)
{
lean_object* v_unused_1720_; lean_object* v_unused_1721_; 
v_unused_1720_ = lean_ctor_get(v___x_1604_, 4);
lean_dec(v_unused_1720_);
v_unused_1721_ = lean_ctor_get(v___x_1604_, 3);
lean_dec(v_unused_1721_);
v___x_1707_ = v___x_1604_;
v_isShared_1708_ = v_isSharedCheck_1719_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_v_1705_);
lean_inc(v_k_1704_);
lean_inc(v_size_1703_);
lean_dec(v___x_1604_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1719_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v_size_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1714_; 
v_size_1709_ = lean_ctor_get(v_l_1701_, 0);
v___x_1710_ = lean_unsigned_to_nat(1u);
v___x_1711_ = lean_nat_add(v___x_1710_, v_size_1703_);
lean_dec(v_size_1703_);
v___x_1712_ = lean_nat_add(v___x_1710_, v_size_1709_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 4, v_l_1701_);
lean_ctor_set(v___x_1707_, 3, v_l_1420_);
lean_ctor_set(v___x_1707_, 2, v_v_1419_);
lean_ctor_set(v___x_1707_, 1, v_k_1418_);
lean_ctor_set(v___x_1707_, 0, v___x_1712_);
v___x_1714_ = v___x_1707_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v___x_1712_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v_k_1418_);
lean_ctor_set(v_reuseFailAlloc_1718_, 2, v_v_1419_);
lean_ctor_set(v_reuseFailAlloc_1718_, 3, v_l_1420_);
lean_ctor_set(v_reuseFailAlloc_1718_, 4, v_l_1701_);
v___x_1714_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v___x_1716_; 
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 4, v_r_1702_);
lean_ctor_set(v___x_1423_, 3, v___x_1714_);
lean_ctor_set(v___x_1423_, 2, v_v_1705_);
lean_ctor_set(v___x_1423_, 1, v_k_1704_);
lean_ctor_set(v___x_1423_, 0, v___x_1711_);
v___x_1716_ = v___x_1423_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1711_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_k_1704_);
lean_ctor_set(v_reuseFailAlloc_1717_, 2, v_v_1705_);
lean_ctor_set(v_reuseFailAlloc_1717_, 3, v___x_1714_);
lean_ctor_set(v_reuseFailAlloc_1717_, 4, v_r_1702_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
else
{
lean_object* v_k_1722_; lean_object* v_v_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1747_; 
v_k_1722_ = lean_ctor_get(v___x_1604_, 1);
v_v_1723_ = lean_ctor_get(v___x_1604_, 2);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1747_ == 0)
{
lean_object* v_unused_1748_; lean_object* v_unused_1749_; lean_object* v_unused_1750_; 
v_unused_1748_ = lean_ctor_get(v___x_1604_, 4);
lean_dec(v_unused_1748_);
v_unused_1749_ = lean_ctor_get(v___x_1604_, 3);
lean_dec(v_unused_1749_);
v_unused_1750_ = lean_ctor_get(v___x_1604_, 0);
lean_dec(v_unused_1750_);
v___x_1725_ = v___x_1604_;
v_isShared_1726_ = v_isSharedCheck_1747_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_v_1723_);
lean_inc(v_k_1722_);
lean_dec(v___x_1604_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1747_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v_k_1727_; lean_object* v_v_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1743_; 
v_k_1727_ = lean_ctor_get(v_l_1701_, 1);
v_v_1728_ = lean_ctor_get(v_l_1701_, 2);
v_isSharedCheck_1743_ = !lean_is_exclusive(v_l_1701_);
if (v_isSharedCheck_1743_ == 0)
{
lean_object* v_unused_1744_; lean_object* v_unused_1745_; lean_object* v_unused_1746_; 
v_unused_1744_ = lean_ctor_get(v_l_1701_, 4);
lean_dec(v_unused_1744_);
v_unused_1745_ = lean_ctor_get(v_l_1701_, 3);
lean_dec(v_unused_1745_);
v_unused_1746_ = lean_ctor_get(v_l_1701_, 0);
lean_dec(v_unused_1746_);
v___x_1730_ = v_l_1701_;
v_isShared_1731_ = v_isSharedCheck_1743_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_v_1728_);
lean_inc(v_k_1727_);
lean_dec(v_l_1701_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1743_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1735_; 
v___x_1732_ = lean_unsigned_to_nat(3u);
v___x_1733_ = lean_unsigned_to_nat(1u);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 4, v_r_1702_);
lean_ctor_set(v___x_1730_, 3, v_r_1702_);
lean_ctor_set(v___x_1730_, 2, v_v_1419_);
lean_ctor_set(v___x_1730_, 1, v_k_1418_);
lean_ctor_set(v___x_1730_, 0, v___x_1733_);
v___x_1735_ = v___x_1730_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1733_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_k_1418_);
lean_ctor_set(v_reuseFailAlloc_1742_, 2, v_v_1419_);
lean_ctor_set(v_reuseFailAlloc_1742_, 3, v_r_1702_);
lean_ctor_set(v_reuseFailAlloc_1742_, 4, v_r_1702_);
v___x_1735_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
lean_object* v___x_1737_; 
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 3, v_r_1702_);
lean_ctor_set(v___x_1725_, 0, v___x_1733_);
v___x_1737_ = v___x_1725_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1733_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v_k_1722_);
lean_ctor_set(v_reuseFailAlloc_1741_, 2, v_v_1723_);
lean_ctor_set(v_reuseFailAlloc_1741_, 3, v_r_1702_);
lean_ctor_set(v_reuseFailAlloc_1741_, 4, v_r_1702_);
v___x_1737_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
lean_object* v___x_1739_; 
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 4, v___x_1737_);
lean_ctor_set(v___x_1423_, 3, v___x_1735_);
lean_ctor_set(v___x_1423_, 2, v_v_1728_);
lean_ctor_set(v___x_1423_, 1, v_k_1727_);
lean_ctor_set(v___x_1423_, 0, v___x_1732_);
v___x_1739_ = v___x_1423_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1732_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_k_1727_);
lean_ctor_set(v_reuseFailAlloc_1740_, 2, v_v_1728_);
lean_ctor_set(v_reuseFailAlloc_1740_, 3, v___x_1735_);
lean_ctor_set(v_reuseFailAlloc_1740_, 4, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1751_; 
v_r_1751_ = lean_ctor_get(v___x_1604_, 4);
lean_inc(v_r_1751_);
if (lean_obj_tag(v_r_1751_) == 0)
{
lean_object* v_k_1752_; lean_object* v_v_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1765_; 
v_k_1752_ = lean_ctor_get(v___x_1604_, 1);
v_v_1753_ = lean_ctor_get(v___x_1604_, 2);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1765_ == 0)
{
lean_object* v_unused_1766_; lean_object* v_unused_1767_; lean_object* v_unused_1768_; 
v_unused_1766_ = lean_ctor_get(v___x_1604_, 4);
lean_dec(v_unused_1766_);
v_unused_1767_ = lean_ctor_get(v___x_1604_, 3);
lean_dec(v_unused_1767_);
v_unused_1768_ = lean_ctor_get(v___x_1604_, 0);
lean_dec(v_unused_1768_);
v___x_1755_ = v___x_1604_;
v_isShared_1756_ = v_isSharedCheck_1765_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_v_1753_);
lean_inc(v_k_1752_);
lean_dec(v___x_1604_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1765_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1760_; 
v___x_1757_ = lean_unsigned_to_nat(3u);
v___x_1758_ = lean_unsigned_to_nat(1u);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 4, v_l_1701_);
lean_ctor_set(v___x_1755_, 2, v_v_1419_);
lean_ctor_set(v___x_1755_, 1, v_k_1418_);
lean_ctor_set(v___x_1755_, 0, v___x_1758_);
v___x_1760_ = v___x_1755_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1758_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v_k_1418_);
lean_ctor_set(v_reuseFailAlloc_1764_, 2, v_v_1419_);
lean_ctor_set(v_reuseFailAlloc_1764_, 3, v_l_1701_);
lean_ctor_set(v_reuseFailAlloc_1764_, 4, v_l_1701_);
v___x_1760_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
lean_object* v___x_1762_; 
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 4, v_r_1751_);
lean_ctor_set(v___x_1423_, 3, v___x_1760_);
lean_ctor_set(v___x_1423_, 2, v_v_1753_);
lean_ctor_set(v___x_1423_, 1, v_k_1752_);
lean_ctor_set(v___x_1423_, 0, v___x_1757_);
v___x_1762_ = v___x_1423_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1757_);
lean_ctor_set(v_reuseFailAlloc_1763_, 1, v_k_1752_);
lean_ctor_set(v_reuseFailAlloc_1763_, 2, v_v_1753_);
lean_ctor_set(v_reuseFailAlloc_1763_, 3, v___x_1760_);
lean_ctor_set(v_reuseFailAlloc_1763_, 4, v_r_1751_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
else
{
lean_object* v___x_1769_; lean_object* v___x_1771_; 
v___x_1769_ = lean_unsigned_to_nat(2u);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 4, v___x_1604_);
lean_ctor_set(v___x_1423_, 3, v_r_1751_);
lean_ctor_set(v___x_1423_, 0, v___x_1769_);
v___x_1771_ = v___x_1423_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1769_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v_k_1418_);
lean_ctor_set(v_reuseFailAlloc_1772_, 2, v_v_1419_);
lean_ctor_set(v_reuseFailAlloc_1772_, 3, v_r_1751_);
lean_ctor_set(v_reuseFailAlloc_1772_, 4, v___x_1604_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
}
else
{
lean_object* v___x_1773_; lean_object* v___x_1775_; 
v___x_1773_ = lean_unsigned_to_nat(1u);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 4, v___x_1604_);
lean_ctor_set(v___x_1423_, 3, v___x_1604_);
lean_ctor_set(v___x_1423_, 0, v___x_1773_);
v___x_1775_ = v___x_1423_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1773_);
lean_ctor_set(v_reuseFailAlloc_1776_, 1, v_k_1418_);
lean_ctor_set(v_reuseFailAlloc_1776_, 2, v_v_1419_);
lean_ctor_set(v_reuseFailAlloc_1776_, 3, v___x_1604_);
lean_ctor_set(v_reuseFailAlloc_1776_, 4, v___x_1604_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = lean_unsigned_to_nat(1u);
v___x_1779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
lean_ctor_set(v___x_1779_, 1, v_k_1414_);
lean_ctor_set(v___x_1779_, 2, v_v_1415_);
lean_ctor_set(v___x_1779_, 3, v_t_1416_);
lean_ctor_set(v___x_1779_, 4, v_t_1416_);
return v___x_1779_;
}
}
}
static lean_object* _init_l_Lean_Json_setObjVal_x21___closed__2(void){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1782_ = ((lean_object*)(l_Lean_Json_setObjVal_x21___closed__1));
v___x_1783_ = lean_unsigned_to_nat(21u);
v___x_1784_ = lean_unsigned_to_nat(290u);
v___x_1785_ = ((lean_object*)(l_Lean_Json_setObjVal_x21___closed__0));
v___x_1786_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0));
v___x_1787_ = l_mkPanicMessageWithDecl(v___x_1786_, v___x_1785_, v___x_1784_, v___x_1783_, v___x_1782_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_setObjVal_x21(lean_object* v_x_1788_, lean_object* v_x_1789_, lean_object* v_x_1790_){
_start:
{
if (lean_obj_tag(v_x_1788_) == 5)
{
lean_object* v_kvPairs_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1799_; 
v_kvPairs_1791_ = lean_ctor_get(v_x_1788_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v_x_1788_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1793_ = v_x_1788_;
v_isShared_1794_ = v_isSharedCheck_1799_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_kvPairs_1791_);
lean_dec(v_x_1788_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1799_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1795_; lean_object* v___x_1797_; 
v___x_1795_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_x_1789_, v_x_1790_, v_kvPairs_1791_);
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 0, v___x_1795_);
v___x_1797_ = v___x_1793_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1795_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
else
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
lean_dec(v_x_1790_);
lean_dec_ref(v_x_1789_);
lean_dec(v_x_1788_);
v___x_1800_ = lean_obj_once(&l_Lean_Json_setObjVal_x21___closed__2, &l_Lean_Json_setObjVal_x21___closed__2_once, _init_l_Lean_Json_setObjVal_x21___closed__2);
v___x_1801_ = l_panic___at___00Lean_Json_setObjVal_x21_spec__1(v___x_1800_);
return v___x_1801_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0(lean_object* v_00_u03b2_1802_, lean_object* v_msg_1803_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v_msg_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0(lean_object* v_00_u03b2_1805_, lean_object* v_k_1806_, lean_object* v_v_1807_, lean_object* v_t_1808_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1806_, v_v_1807_, v_t_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(lean_object* v_init_1810_, lean_object* v_x_1811_){
_start:
{
if (lean_obj_tag(v_x_1811_) == 0)
{
lean_object* v_k_1812_; lean_object* v_v_1813_; lean_object* v_l_1814_; lean_object* v_r_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v_k_1812_ = lean_ctor_get(v_x_1811_, 1);
lean_inc(v_k_1812_);
v_v_1813_ = lean_ctor_get(v_x_1811_, 2);
lean_inc(v_v_1813_);
v_l_1814_ = lean_ctor_get(v_x_1811_, 3);
lean_inc(v_l_1814_);
v_r_1815_ = lean_ctor_get(v_x_1811_, 4);
lean_inc(v_r_1815_);
lean_dec_ref_known(v_x_1811_, 5);
v___x_1816_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_init_1810_, v_l_1814_);
v___x_1817_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1812_, v_v_1813_, v___x_1816_);
v_init_1810_ = v___x_1817_;
v_x_1811_ = v_r_1815_;
goto _start;
}
else
{
return v_init_1810_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mergeObj(lean_object* v_x_1819_, lean_object* v_x_1820_){
_start:
{
if (lean_obj_tag(v_x_1819_) == 5)
{
if (lean_obj_tag(v_x_1820_) == 5)
{
lean_object* v_kvPairs_1821_; lean_object* v_kvPairs_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1830_; 
v_kvPairs_1821_ = lean_ctor_get(v_x_1819_, 0);
lean_inc(v_kvPairs_1821_);
lean_dec_ref_known(v_x_1819_, 1);
v_kvPairs_1822_ = lean_ctor_get(v_x_1820_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v_x_1820_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1824_ = v_x_1820_;
v_isShared_1825_ = v_isSharedCheck_1830_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_kvPairs_1822_);
lean_dec(v_x_1820_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1830_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1826_; lean_object* v___x_1828_; 
v___x_1826_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_kvPairs_1821_, v_kvPairs_1822_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v___x_1826_);
v___x_1828_ = v___x_1824_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1826_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
else
{
lean_dec_ref_known(v_x_1819_, 1);
return v_x_1820_;
}
}
else
{
lean_dec(v_x_1819_);
return v_x_1820_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0(lean_object* v_init_1831_, lean_object* v_t_1832_){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_init_1831_, v_t_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorIdx___impl(lean_object* v_x_1834_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = lean_obj_tag_nat(v_x_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorIdx___impl___boxed(lean_object* v_x_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_Lean_Json_Structured_ctorIdx___impl(v_x_1836_);
lean_dec_ref(v_x_1836_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim___redArg(lean_object* v_t_1838_, lean_object* v_k_1839_){
_start:
{
if (lean_obj_tag(v_t_1838_) == 0)
{
lean_object* v_elems_1840_; lean_object* v___x_1841_; 
v_elems_1840_ = lean_ctor_get(v_t_1838_, 0);
lean_inc_ref(v_elems_1840_);
lean_dec_ref_known(v_t_1838_, 1);
v___x_1841_ = lean_apply_1(v_k_1839_, v_elems_1840_);
return v___x_1841_;
}
else
{
lean_object* v_kvPairs_1842_; lean_object* v___x_1843_; 
v_kvPairs_1842_ = lean_ctor_get(v_t_1838_, 0);
lean_inc(v_kvPairs_1842_);
lean_dec_ref_known(v_t_1838_, 1);
v___x_1843_ = lean_apply_1(v_k_1839_, v_kvPairs_1842_);
return v___x_1843_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim(lean_object* v_motive_1844_, lean_object* v_ctorIdx_1845_, lean_object* v_t_1846_, lean_object* v_h_1847_, lean_object* v_k_1848_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1846_, v_k_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim___boxed(lean_object* v_motive_1850_, lean_object* v_ctorIdx_1851_, lean_object* v_t_1852_, lean_object* v_h_1853_, lean_object* v_k_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_Lean_Json_Structured_ctorElim(v_motive_1850_, v_ctorIdx_1851_, v_t_1852_, v_h_1853_, v_k_1854_);
lean_dec(v_ctorIdx_1851_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_arr_elim___redArg(lean_object* v_t_1856_, lean_object* v_arr_1857_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1856_, v_arr_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_arr_elim(lean_object* v_motive_1859_, lean_object* v_t_1860_, lean_object* v_h_1861_, lean_object* v_arr_1862_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1860_, v_arr_1862_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_obj_elim___redArg(lean_object* v_t_1864_, lean_object* v_obj_1865_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1864_, v_obj_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_obj_elim(lean_object* v_motive_1867_, lean_object* v_t_1868_, lean_object* v_h_1869_, lean_object* v_obj_1870_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1868_, v_obj_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeArrayStructured___lam__0(lean_object* v_elems_1872_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1873_, 0, v_elems_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeRawStringStructured___lam__0(lean_object* v_kvPairs_1876_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1877_, 0, v_kvPairs_1876_);
return v___x_1877_;
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
