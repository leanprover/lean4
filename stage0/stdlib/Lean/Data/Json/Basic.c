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
v___x_150_ = lean_int_dec_lt(v___y_146_, v___y_147_);
if (v___x_150_ == 0)
{
uint8_t v___x_151_; 
v___x_151_ = lean_int_dec_lt(v___y_147_, v___y_146_);
lean_dec(v___y_146_);
lean_dec(v___y_147_);
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
v___y_146_ = v_snd_157_;
v___y_147_ = v_snd_159_;
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
v___y_146_ = v_snd_157_;
v___y_147_ = v_snd_159_;
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
v___x_260_ = lean_nat_add(v___y_258_, v___y_255_);
lean_dec(v___y_255_);
lean_dec(v___y_258_);
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
v___x_268_ = lean_int_dec_eq(v___y_259_, v___x_253_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_269_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__1));
v___x_270_ = l_Int_repr(v___y_259_);
lean_dec(v___y_259_);
v___x_271_ = lean_string_append(v___x_269_, v___x_270_);
lean_dec_ref(v___x_270_);
v___y_240_ = v___y_256_;
v___y_241_ = v___y_257_;
v___y_242_ = v_right_267_;
v___y_243_ = v___x_271_;
goto v___jp_239_;
}
else
{
lean_object* v___x_272_; 
lean_dec(v___y_259_);
v___x_272_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__2));
v___y_240_ = v___y_256_;
v___y_241_ = v___y_257_;
v___y_242_ = v_right_267_;
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
v___y_255_ = v___x_283_;
v___y_256_ = v_left_282_;
v___y_257_ = v___y_275_;
v___y_258_ = v_e_x27_280_;
v___y_259_ = v___y_276_;
goto v___jp_254_;
}
else
{
uint8_t v___x_285_; 
v___x_285_ = lean_int_dec_eq(v___y_276_, v___x_253_);
if (v___x_285_ == 0)
{
v___y_255_ = v___x_283_;
v___y_256_ = v_left_282_;
v___y_257_ = v___y_275_;
v___y_258_ = v_e_x27_280_;
v___y_259_ = v___y_276_;
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
LEAN_EXPORT lean_object* l_Lean_Json_ctorIdx___impl(lean_object* v_x_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = lean_obj_tag_nat(v_x_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorIdx___impl___boxed(lean_object* v_x_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_Json_ctorIdx___impl(v_x_553_);
lean_dec(v_x_553_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorElim___redArg(lean_object* v_t_555_, lean_object* v_k_556_){
_start:
{
switch(lean_obj_tag(v_t_555_))
{
case 0:
{
return v_k_556_;
}
case 1:
{
uint8_t v_b_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v_b_557_ = lean_ctor_get_uint8(v_t_555_, 0);
lean_dec_ref_known(v_t_555_, 0);
v___x_558_ = lean_box(v_b_557_);
v___x_559_ = lean_apply_1(v_k_556_, v___x_558_);
return v___x_559_;
}
case 5:
{
lean_object* v_kvPairs_560_; lean_object* v___x_561_; 
v_kvPairs_560_ = lean_ctor_get(v_t_555_, 0);
lean_inc(v_kvPairs_560_);
lean_dec_ref_known(v_t_555_, 1);
v___x_561_ = lean_apply_1(v_k_556_, v_kvPairs_560_);
return v___x_561_;
}
default: 
{
lean_object* v_n_562_; lean_object* v___x_563_; 
v_n_562_ = lean_ctor_get(v_t_555_, 0);
lean_inc_ref(v_n_562_);
lean_dec(v_t_555_);
v___x_563_ = lean_apply_1(v_k_556_, v_n_562_);
return v___x_563_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorElim(lean_object* v_motive__1_564_, lean_object* v_ctorIdx_565_, lean_object* v_t_566_, lean_object* v_h_567_, lean_object* v_k_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Lean_Json_ctorElim___redArg(v_t_566_, v_k_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorElim___boxed(lean_object* v_motive__1_570_, lean_object* v_ctorIdx_571_, lean_object* v_t_572_, lean_object* v_h_573_, lean_object* v_k_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_Json_ctorElim(v_motive__1_570_, v_ctorIdx_571_, v_t_572_, v_h_573_, v_k_574_);
lean_dec(v_ctorIdx_571_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_null_elim___redArg(lean_object* v_t_576_, lean_object* v_null_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_Json_ctorElim___redArg(v_t_576_, v_null_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_null_elim(lean_object* v_motive__1_579_, lean_object* v_t_580_, lean_object* v_h_581_, lean_object* v_null_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_Json_ctorElim___redArg(v_t_580_, v_null_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_bool_elim___redArg(lean_object* v_t_584_, lean_object* v_bool_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_Json_ctorElim___redArg(v_t_584_, v_bool_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_bool_elim(lean_object* v_motive__1_587_, lean_object* v_t_588_, lean_object* v_h_589_, lean_object* v_bool_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_Json_ctorElim___redArg(v_t_588_, v_bool_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_num_elim___redArg(lean_object* v_t_592_, lean_object* v_num_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_Json_ctorElim___redArg(v_t_592_, v_num_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_num_elim(lean_object* v_motive__1_595_, lean_object* v_t_596_, lean_object* v_h_597_, lean_object* v_num_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_Json_ctorElim___redArg(v_t_596_, v_num_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_str_elim___redArg(lean_object* v_t_600_, lean_object* v_str_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_Json_ctorElim___redArg(v_t_600_, v_str_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_str_elim(lean_object* v_motive__1_603_, lean_object* v_t_604_, lean_object* v_h_605_, lean_object* v_str_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_Json_ctorElim___redArg(v_t_604_, v_str_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_arr_elim___redArg(lean_object* v_t_608_, lean_object* v_arr_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_Json_ctorElim___redArg(v_t_608_, v_arr_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_arr_elim(lean_object* v_motive__1_611_, lean_object* v_t_612_, lean_object* v_h_613_, lean_object* v_arr_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_Lean_Json_ctorElim___redArg(v_t_612_, v_arr_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_obj_elim___redArg(lean_object* v_t_616_, lean_object* v_obj_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Lean_Json_ctorElim___redArg(v_t_616_, v_obj_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_obj_elim(lean_object* v_motive__1_619_, lean_object* v_t_620_, lean_object* v_h_621_, lean_object* v_obj_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_Json_ctorElim___redArg(v_t_620_, v_obj_622_);
return v___x_623_;
}
}
static lean_object* _init_l_Lean_instInhabitedJson_default(void){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = lean_box(0);
return v___x_624_;
}
}
static lean_object* _init_l_Lean_instInhabitedJson(void){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = lean_box(0);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(lean_object* v_init_626_, lean_object* v_x_627_){
_start:
{
if (lean_obj_tag(v_x_627_) == 0)
{
lean_object* v_l_628_; lean_object* v_r_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v_l_628_ = lean_ctor_get(v_x_627_, 3);
v_r_629_ = lean_ctor_get(v_x_627_, 4);
v___x_630_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_626_, v_l_628_);
v___x_631_ = lean_unsigned_to_nat(1u);
v___x_632_ = lean_nat_add(v___x_630_, v___x_631_);
lean_dec(v___x_630_);
v_init_626_ = v___x_632_;
v_x_627_ = v_r_629_;
goto _start;
}
else
{
return v_init_626_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1___boxed(lean_object* v_init_634_, lean_object* v_x_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_634_, v_x_635_);
lean_dec(v_x_635_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(lean_object* v_t_637_, lean_object* v_k_638_){
_start:
{
if (lean_obj_tag(v_t_637_) == 0)
{
lean_object* v_k_639_; lean_object* v_v_640_; lean_object* v_l_641_; lean_object* v_r_642_; uint8_t v___x_643_; 
v_k_639_ = lean_ctor_get(v_t_637_, 1);
v_v_640_ = lean_ctor_get(v_t_637_, 2);
v_l_641_ = lean_ctor_get(v_t_637_, 3);
v_r_642_ = lean_ctor_get(v_t_637_, 4);
v___x_643_ = lean_string_compare(v_k_638_, v_k_639_);
switch(v___x_643_)
{
case 0:
{
v_t_637_ = v_l_641_;
goto _start;
}
case 1:
{
lean_object* v___x_645_; 
lean_inc(v_v_640_);
v___x_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_645_, 0, v_v_640_);
return v___x_645_;
}
default: 
{
v_t_637_ = v_r_642_;
goto _start;
}
}
}
else
{
lean_object* v___x_647_; 
v___x_647_ = lean_box(0);
return v___x_647_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg___boxed(lean_object* v_t_648_, lean_object* v_k_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_t_648_, v_k_649_);
lean_dec_ref(v_k_649_);
lean_dec(v_t_648_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(lean_object* v_szA_662_, lean_object* v_szB_663_, lean_object* v_kvPairs_664_, lean_object* v_init_665_, lean_object* v_x_666_){
_start:
{
if (lean_obj_tag(v_x_666_) == 0)
{
lean_object* v_k_667_; lean_object* v_v_668_; lean_object* v_l_669_; lean_object* v_r_670_; uint8_t v___x_671_; lean_object* v___x_672_; 
v_k_667_ = lean_ctor_get(v_x_666_, 1);
v_v_668_ = lean_ctor_get(v_x_666_, 2);
v_l_669_ = lean_ctor_get(v_x_666_, 3);
v_r_670_ = lean_ctor_get(v_x_666_, 4);
v___x_671_ = lean_nat_dec_eq(v_szA_662_, v_szB_663_);
v___x_672_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_szA_662_, v_szB_663_, v_kvPairs_664_, v_init_665_, v_l_669_);
if (lean_obj_tag(v___x_672_) == 0)
{
return v___x_672_;
}
else
{
lean_object* v___x_673_; lean_object* v___x_677_; 
lean_dec_ref_known(v___x_672_, 1);
v___x_673_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__0));
v___x_677_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_kvPairs_664_, v_k_667_);
if (lean_obj_tag(v___x_677_) == 0)
{
goto v___jp_674_;
}
else
{
lean_object* v_val_678_; uint8_t v___x_679_; 
v_val_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_val_678_);
lean_dec_ref_known(v___x_677_, 1);
v___x_679_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_v_668_, v_val_678_);
lean_dec(v_val_678_);
if (v___x_679_ == 0)
{
goto v___jp_674_;
}
else
{
v_init_665_ = v___x_673_;
v_x_666_ = v_r_670_;
goto _start;
}
}
v___jp_674_:
{
if (v___x_671_ == 0)
{
v_init_665_ = v___x_673_;
v_x_666_ = v_r_670_;
goto _start;
}
else
{
lean_object* v___x_676_; 
v___x_676_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__3));
return v___x_676_;
}
}
}
}
else
{
lean_object* v___x_681_; 
v___x_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_681_, 0, v_init_665_);
return v___x_681_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(lean_object* v_x_682_, lean_object* v_x_683_){
_start:
{
switch(lean_obj_tag(v_x_682_))
{
case 0:
{
if (lean_obj_tag(v_x_683_) == 0)
{
uint8_t v___x_684_; 
v___x_684_ = 1;
return v___x_684_;
}
else
{
uint8_t v___x_685_; 
v___x_685_ = 0;
return v___x_685_;
}
}
case 1:
{
if (lean_obj_tag(v_x_683_) == 1)
{
uint8_t v_b_686_; 
v_b_686_ = lean_ctor_get_uint8(v_x_683_, 0);
if (v_b_686_ == 0)
{
uint8_t v_b_687_; 
v_b_687_ = lean_ctor_get_uint8(v_x_682_, 0);
if (v_b_687_ == 0)
{
uint8_t v___x_688_; 
v___x_688_ = 1;
return v___x_688_;
}
else
{
return v_b_686_;
}
}
else
{
uint8_t v_b_689_; 
v_b_689_ = lean_ctor_get_uint8(v_x_682_, 0);
return v_b_689_;
}
}
else
{
uint8_t v___x_690_; 
v___x_690_ = 0;
return v___x_690_;
}
}
case 2:
{
if (lean_obj_tag(v_x_683_) == 2)
{
lean_object* v_n_691_; lean_object* v_n_692_; uint8_t v___x_693_; 
v_n_691_ = lean_ctor_get(v_x_682_, 0);
v_n_692_ = lean_ctor_get(v_x_683_, 0);
v___x_693_ = l_Lean_instDecidableEqJsonNumber_decEq(v_n_691_, v_n_692_);
return v___x_693_;
}
else
{
uint8_t v___x_694_; 
v___x_694_ = 0;
return v___x_694_;
}
}
case 3:
{
if (lean_obj_tag(v_x_683_) == 3)
{
lean_object* v_s_695_; lean_object* v_s_696_; uint8_t v___x_697_; 
v_s_695_ = lean_ctor_get(v_x_682_, 0);
v_s_696_ = lean_ctor_get(v_x_683_, 0);
v___x_697_ = lean_string_dec_eq(v_s_695_, v_s_696_);
return v___x_697_;
}
else
{
uint8_t v___x_698_; 
v___x_698_ = 0;
return v___x_698_;
}
}
case 4:
{
if (lean_obj_tag(v_x_683_) == 4)
{
lean_object* v_elems_699_; lean_object* v_elems_700_; lean_object* v___x_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v_elems_699_ = lean_ctor_get(v_x_682_, 0);
v_elems_700_ = lean_ctor_get(v_x_683_, 0);
v___x_701_ = lean_array_get_size(v_elems_699_);
v___x_702_ = lean_array_get_size(v_elems_700_);
v___x_703_ = lean_nat_dec_eq(v___x_701_, v___x_702_);
if (v___x_703_ == 0)
{
return v___x_703_;
}
else
{
uint8_t v___x_704_; 
v___x_704_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(v_elems_699_, v_elems_700_, v___x_701_);
return v___x_704_;
}
}
else
{
uint8_t v___x_705_; 
v___x_705_ = 0;
return v___x_705_;
}
}
default: 
{
if (lean_obj_tag(v_x_683_) == 5)
{
lean_object* v_kvPairs_706_; lean_object* v_kvPairs_707_; lean_object* v___x_708_; lean_object* v_szA_709_; lean_object* v_szB_710_; uint8_t v___x_711_; lean_object* v___y_713_; 
v_kvPairs_706_ = lean_ctor_get(v_x_682_, 0);
v_kvPairs_707_ = lean_ctor_get(v_x_683_, 0);
v___x_708_ = lean_unsigned_to_nat(0u);
v_szA_709_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v___x_708_, v_kvPairs_706_);
v_szB_710_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v___x_708_, v_kvPairs_707_);
v___x_711_ = lean_nat_dec_eq(v_szA_709_, v_szB_710_);
if (v___x_711_ == 0)
{
lean_dec(v_szB_710_);
lean_dec(v_szA_709_);
return v___x_711_;
}
else
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v_a_719_; 
v___x_717_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__0));
v___x_718_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_szA_709_, v_szB_710_, v_kvPairs_707_, v___x_717_, v_kvPairs_706_);
lean_dec(v_szB_710_);
lean_dec(v_szA_709_);
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
lean_dec_ref(v___x_718_);
v___y_713_ = v_a_719_;
goto v___jp_712_;
}
v___jp_712_:
{
lean_object* v_fst_714_; 
v_fst_714_ = lean_ctor_get(v___y_713_, 0);
lean_inc(v_fst_714_);
lean_dec_ref(v___y_713_);
if (lean_obj_tag(v_fst_714_) == 0)
{
return v___x_711_;
}
else
{
lean_object* v_val_715_; uint8_t v___x_716_; 
v_val_715_ = lean_ctor_get(v_fst_714_, 0);
lean_inc(v_val_715_);
lean_dec_ref_known(v_fst_714_, 1);
v___x_716_ = lean_unbox(v_val_715_);
lean_dec(v_val_715_);
return v___x_716_;
}
}
}
else
{
uint8_t v___x_720_; 
v___x_720_ = 0;
return v___x_720_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(lean_object* v_xs_721_, lean_object* v_ys_722_, lean_object* v_x_723_){
_start:
{
lean_object* v_zero_724_; uint8_t v_isZero_725_; 
v_zero_724_ = lean_unsigned_to_nat(0u);
v_isZero_725_ = lean_nat_dec_eq(v_x_723_, v_zero_724_);
if (v_isZero_725_ == 1)
{
lean_dec(v_x_723_);
return v_isZero_725_;
}
else
{
lean_object* v_one_726_; lean_object* v_n_727_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v_one_726_ = lean_unsigned_to_nat(1u);
v_n_727_ = lean_nat_sub(v_x_723_, v_one_726_);
lean_dec(v_x_723_);
v___x_728_ = lean_array_fget_borrowed(v_xs_721_, v_n_727_);
v___x_729_ = lean_array_fget_borrowed(v_ys_722_, v_n_727_);
v___x_730_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v___x_728_, v___x_729_);
if (v___x_730_ == 0)
{
lean_dec(v_n_727_);
return v___x_730_;
}
else
{
v_x_723_ = v_n_727_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg___boxed(lean_object* v_xs_732_, lean_object* v_ys_733_, lean_object* v_x_734_){
_start:
{
uint8_t v_res_735_; lean_object* v_r_736_; 
v_res_735_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(v_xs_732_, v_ys_733_, v_x_734_);
lean_dec_ref(v_ys_733_);
lean_dec_ref(v_xs_732_);
v_r_736_ = lean_box(v_res_735_);
return v_r_736_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___boxed(lean_object* v_szA_737_, lean_object* v_szB_738_, lean_object* v_kvPairs_739_, lean_object* v_init_740_, lean_object* v_x_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_szA_737_, v_szB_738_, v_kvPairs_739_, v_init_740_, v_x_741_);
lean_dec(v_x_741_);
lean_dec(v_kvPairs_739_);
lean_dec(v_szB_738_);
lean_dec(v_szA_737_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___boxed(lean_object* v_x_743_, lean_object* v_x_744_){
_start:
{
uint8_t v_res_745_; lean_object* v_r_746_; 
v_res_745_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_x_743_, v_x_744_);
lean_dec(v_x_744_);
lean_dec(v_x_743_);
v_r_746_ = lean_box(v_res_745_);
return v_r_746_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0(lean_object* v_xs_747_, lean_object* v_ys_748_, lean_object* v_hsz_749_, lean_object* v_x_750_, lean_object* v_x_751_){
_start:
{
uint8_t v___x_752_; 
v___x_752_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(v_xs_747_, v_ys_748_, v_x_750_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___boxed(lean_object* v_xs_753_, lean_object* v_ys_754_, lean_object* v_hsz_755_, lean_object* v_x_756_, lean_object* v_x_757_){
_start:
{
uint8_t v_res_758_; lean_object* v_r_759_; 
v_res_758_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0(v_xs_753_, v_ys_754_, v_hsz_755_, v_x_756_, v_x_757_);
lean_dec_ref(v_ys_754_);
lean_dec_ref(v_xs_753_);
v_r_759_ = lean_box(v_res_758_);
return v_r_759_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1(lean_object* v_init_760_, lean_object* v_t_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_760_, v_t_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___boxed(lean_object* v_init_763_, lean_object* v_t_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1(v_init_763_, v_t_764_);
lean_dec(v_t_764_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2(lean_object* v_00_u03b4_766_, lean_object* v_t_767_, lean_object* v_k_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_t_767_, v_k_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___boxed(lean_object* v_00_u03b4_770_, lean_object* v_t_771_, lean_object* v_k_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2(v_00_u03b4_770_, v_t_771_, v_k_772_);
lean_dec_ref(v_k_772_);
lean_dec(v_t_771_);
return v_res_773_;
}
}
LEAN_EXPORT uint8_t l_Lean_Json_instBEq___private__1(lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
uint8_t v___x_776_; 
v___x_776_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_a_774_, v_a_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instBEq___private__1___boxed(lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
uint8_t v_res_779_; lean_object* v_r_780_; 
v_res_779_ = l_Lean_Json_instBEq___private__1(v_a_777_, v_a_778_);
lean_dec(v_a_778_);
lean_dec(v_a_777_);
v_r_780_ = lean_box(v_res_779_);
return v_r_780_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(lean_object* v_as_783_, size_t v_i_784_, size_t v_stop_785_, uint64_t v_b_786_){
_start:
{
uint8_t v___x_787_; 
v___x_787_ = lean_usize_dec_eq(v_i_784_, v_stop_785_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; uint64_t v___x_789_; uint64_t v___x_790_; size_t v___x_791_; size_t v___x_792_; 
v___x_788_ = lean_array_uget_borrowed(v_as_783_, v_i_784_);
v___x_789_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v___x_788_);
v___x_790_ = lean_uint64_mix_hash(v_b_786_, v___x_789_);
v___x_791_ = ((size_t)1ULL);
v___x_792_ = lean_usize_add(v_i_784_, v___x_791_);
v_i_784_ = v___x_792_;
v_b_786_ = v___x_790_;
goto _start;
}
else
{
return v_b_786_;
}
}
}
LEAN_EXPORT uint64_t l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(lean_object* v_x_794_){
_start:
{
switch(lean_obj_tag(v_x_794_))
{
case 0:
{
uint64_t v___x_795_; 
v___x_795_ = 11ULL;
return v___x_795_;
}
case 1:
{
uint8_t v_b_796_; 
v_b_796_ = lean_ctor_get_uint8(v_x_794_, 0);
if (v_b_796_ == 0)
{
uint64_t v___x_797_; 
v___x_797_ = 889925284873970544ULL;
return v___x_797_;
}
else
{
uint64_t v___x_798_; 
v___x_798_ = 7849220421742680397ULL;
return v___x_798_;
}
}
case 2:
{
lean_object* v_n_799_; uint64_t v___x_800_; uint64_t v___x_801_; uint64_t v___x_802_; 
v_n_799_ = lean_ctor_get(v_x_794_, 0);
v___x_800_ = 17ULL;
v___x_801_ = l_Lean_instHashableJsonNumber_hash(v_n_799_);
v___x_802_ = lean_uint64_mix_hash(v___x_800_, v___x_801_);
return v___x_802_;
}
case 3:
{
lean_object* v_s_803_; uint64_t v___x_804_; uint64_t v___x_805_; uint64_t v___x_806_; 
v_s_803_ = lean_ctor_get(v_x_794_, 0);
v___x_804_ = 19ULL;
v___x_805_ = lean_string_hash(v_s_803_);
v___x_806_ = lean_uint64_mix_hash(v___x_804_, v___x_805_);
return v___x_806_;
}
case 4:
{
lean_object* v_elems_807_; lean_object* v___x_808_; lean_object* v___x_809_; uint8_t v___x_810_; 
v_elems_807_ = lean_ctor_get(v_x_794_, 0);
v___x_808_ = lean_unsigned_to_nat(0u);
v___x_809_ = lean_array_get_size(v_elems_807_);
v___x_810_ = lean_nat_dec_lt(v___x_808_, v___x_809_);
if (v___x_810_ == 0)
{
uint64_t v___x_811_; 
v___x_811_ = 179905158410471120ULL;
return v___x_811_;
}
else
{
uint64_t v___x_812_; uint64_t v___x_813_; uint8_t v___x_814_; 
v___x_812_ = 23ULL;
v___x_813_ = 7ULL;
v___x_814_ = lean_nat_dec_le(v___x_809_, v___x_809_);
if (v___x_814_ == 0)
{
if (v___x_810_ == 0)
{
uint64_t v___x_815_; 
v___x_815_ = 179905158410471120ULL;
return v___x_815_;
}
else
{
size_t v___x_816_; size_t v___x_817_; uint64_t v___x_818_; uint64_t v___x_819_; 
v___x_816_ = ((size_t)0ULL);
v___x_817_ = lean_usize_of_nat(v___x_809_);
v___x_818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_elems_807_, v___x_816_, v___x_817_, v___x_813_);
v___x_819_ = lean_uint64_mix_hash(v___x_812_, v___x_818_);
return v___x_819_;
}
}
else
{
size_t v___x_820_; size_t v___x_821_; uint64_t v___x_822_; uint64_t v___x_823_; 
v___x_820_ = ((size_t)0ULL);
v___x_821_ = lean_usize_of_nat(v___x_809_);
v___x_822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_elems_807_, v___x_820_, v___x_821_, v___x_813_);
v___x_823_ = lean_uint64_mix_hash(v___x_812_, v___x_822_);
return v___x_823_;
}
}
}
default: 
{
lean_object* v_kvPairs_824_; uint64_t v___x_825_; uint64_t v___x_826_; uint64_t v___x_827_; uint64_t v___x_828_; 
v_kvPairs_824_ = lean_ctor_get(v_x_794_, 0);
v___x_825_ = 29ULL;
v___x_826_ = 7ULL;
v___x_827_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v___x_826_, v_kvPairs_824_);
v___x_828_ = lean_uint64_mix_hash(v___x_825_, v___x_827_);
return v___x_828_;
}
}
}
}
LEAN_EXPORT uint64_t l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(uint64_t v_init_829_, lean_object* v_x_830_){
_start:
{
if (lean_obj_tag(v_x_830_) == 0)
{
lean_object* v_k_831_; lean_object* v_v_832_; lean_object* v_l_833_; lean_object* v_r_834_; uint64_t v___x_835_; uint64_t v___x_836_; uint64_t v___x_837_; uint64_t v___x_838_; uint64_t v___x_839_; 
v_k_831_ = lean_ctor_get(v_x_830_, 1);
v_v_832_ = lean_ctor_get(v_x_830_, 2);
v_l_833_ = lean_ctor_get(v_x_830_, 3);
v_r_834_ = lean_ctor_get(v_x_830_, 4);
v___x_835_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_829_, v_l_833_);
v___x_836_ = lean_string_hash(v_k_831_);
v___x_837_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_v_832_);
v___x_838_ = lean_uint64_mix_hash(v___x_836_, v___x_837_);
v___x_839_ = lean_uint64_mix_hash(v___x_835_, v___x_838_);
v_init_829_ = v___x_839_;
v_x_830_ = v_r_834_;
goto _start;
}
else
{
return v_init_829_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1___boxed(lean_object* v_init_841_, lean_object* v_x_842_){
_start:
{
uint64_t v_init_boxed_843_; uint64_t v_res_844_; lean_object* v_r_845_; 
v_init_boxed_843_ = lean_unbox_uint64(v_init_841_);
lean_dec_ref(v_init_841_);
v_res_844_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_boxed_843_, v_x_842_);
lean_dec(v_x_842_);
v_r_845_ = lean_box_uint64(v_res_844_);
return v_r_845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0___boxed(lean_object* v_as_846_, lean_object* v_i_847_, lean_object* v_stop_848_, lean_object* v_b_849_){
_start:
{
size_t v_i_boxed_850_; size_t v_stop_boxed_851_; uint64_t v_b_boxed_852_; uint64_t v_res_853_; lean_object* v_r_854_; 
v_i_boxed_850_ = lean_unbox_usize(v_i_847_);
lean_dec(v_i_847_);
v_stop_boxed_851_ = lean_unbox_usize(v_stop_848_);
lean_dec(v_stop_848_);
v_b_boxed_852_ = lean_unbox_uint64(v_b_849_);
lean_dec_ref(v_b_849_);
v_res_853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_as_846_, v_i_boxed_850_, v_stop_boxed_851_, v_b_boxed_852_);
lean_dec_ref(v_as_846_);
v_r_854_ = lean_box_uint64(v_res_853_);
return v_r_854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___boxed(lean_object* v_x_855_){
_start:
{
uint64_t v_res_856_; lean_object* v_r_857_; 
v_res_856_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_x_855_);
lean_dec(v_x_855_);
v_r_857_ = lean_box_uint64(v_res_856_);
return v_r_857_;
}
}
LEAN_EXPORT uint64_t l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1(uint64_t v_init_858_, lean_object* v_t_859_){
_start:
{
uint64_t v___x_860_; 
v___x_860_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_858_, v_t_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1___boxed(lean_object* v_init_861_, lean_object* v_t_862_){
_start:
{
uint64_t v_init_boxed_863_; uint64_t v_res_864_; lean_object* v_r_865_; 
v_init_boxed_863_ = lean_unbox_uint64(v_init_861_);
lean_dec_ref(v_init_861_);
v_res_864_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1(v_init_boxed_863_, v_t_862_);
lean_dec(v_t_862_);
v_r_865_ = lean_box_uint64(v_res_864_);
return v_r_865_;
}
}
LEAN_EXPORT uint64_t l_Lean_Json_instHashable___private__1(lean_object* v_a_866_){
_start:
{
uint64_t v___x_867_; 
v___x_867_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_a_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instHashable___private__1___boxed(lean_object* v_a_868_){
_start:
{
uint64_t v_res_869_; lean_object* v_r_870_; 
v_res_869_ = l_Lean_Json_instHashable___private__1(v_a_868_);
lean_dec(v_a_868_);
v_r_870_ = lean_box_uint64(v_res_869_);
return v_r_870_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(lean_object* v_k_873_, lean_object* v_v_874_, lean_object* v_t_875_){
_start:
{
if (lean_obj_tag(v_t_875_) == 0)
{
lean_object* v_size_876_; lean_object* v_k_877_; lean_object* v_v_878_; lean_object* v_l_879_; lean_object* v_r_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_1160_; 
v_size_876_ = lean_ctor_get(v_t_875_, 0);
v_k_877_ = lean_ctor_get(v_t_875_, 1);
v_v_878_ = lean_ctor_get(v_t_875_, 2);
v_l_879_ = lean_ctor_get(v_t_875_, 3);
v_r_880_ = lean_ctor_get(v_t_875_, 4);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_t_875_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_882_ = v_t_875_;
v_isShared_883_ = v_isSharedCheck_1160_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_r_880_);
lean_inc(v_l_879_);
lean_inc(v_v_878_);
lean_inc(v_k_877_);
lean_inc(v_size_876_);
lean_dec(v_t_875_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_1160_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
uint8_t v___x_884_; 
v___x_884_ = lean_string_compare(v_k_873_, v_k_877_);
switch(v___x_884_)
{
case 0:
{
lean_object* v_impl_885_; lean_object* v___x_886_; 
lean_dec(v_size_876_);
v_impl_885_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_873_, v_v_874_, v_l_879_);
v___x_886_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_880_) == 0)
{
lean_object* v_size_887_; lean_object* v_size_888_; lean_object* v_k_889_; lean_object* v_v_890_; lean_object* v_l_891_; lean_object* v_r_892_; lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
v_size_887_ = lean_ctor_get(v_r_880_, 0);
v_size_888_ = lean_ctor_get(v_impl_885_, 0);
v_k_889_ = lean_ctor_get(v_impl_885_, 1);
v_v_890_ = lean_ctor_get(v_impl_885_, 2);
v_l_891_ = lean_ctor_get(v_impl_885_, 3);
v_r_892_ = lean_ctor_get(v_impl_885_, 4);
lean_inc(v_r_892_);
v___x_893_ = lean_unsigned_to_nat(3u);
v___x_894_ = lean_nat_mul(v___x_893_, v_size_887_);
v___x_895_ = lean_nat_dec_lt(v___x_894_, v_size_888_);
lean_dec(v___x_894_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_899_; 
lean_dec(v_r_892_);
v___x_896_ = lean_nat_add(v___x_886_, v_size_888_);
v___x_897_ = lean_nat_add(v___x_896_, v_size_887_);
lean_dec(v___x_896_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 3, v_impl_885_);
lean_ctor_set(v___x_882_, 0, v___x_897_);
v___x_899_ = v___x_882_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_k_877_);
lean_ctor_set(v_reuseFailAlloc_900_, 2, v_v_878_);
lean_ctor_set(v_reuseFailAlloc_900_, 3, v_impl_885_);
lean_ctor_set(v_reuseFailAlloc_900_, 4, v_r_880_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
else
{
lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_966_; 
lean_inc(v_l_891_);
lean_inc(v_v_890_);
lean_inc(v_k_889_);
lean_inc(v_size_888_);
v_isSharedCheck_966_ = !lean_is_exclusive(v_impl_885_);
if (v_isSharedCheck_966_ == 0)
{
lean_object* v_unused_967_; lean_object* v_unused_968_; lean_object* v_unused_969_; lean_object* v_unused_970_; lean_object* v_unused_971_; 
v_unused_967_ = lean_ctor_get(v_impl_885_, 4);
lean_dec(v_unused_967_);
v_unused_968_ = lean_ctor_get(v_impl_885_, 3);
lean_dec(v_unused_968_);
v_unused_969_ = lean_ctor_get(v_impl_885_, 2);
lean_dec(v_unused_969_);
v_unused_970_ = lean_ctor_get(v_impl_885_, 1);
lean_dec(v_unused_970_);
v_unused_971_ = lean_ctor_get(v_impl_885_, 0);
lean_dec(v_unused_971_);
v___x_902_ = v_impl_885_;
v_isShared_903_ = v_isSharedCheck_966_;
goto v_resetjp_901_;
}
else
{
lean_dec(v_impl_885_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_966_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v_size_904_; lean_object* v_size_905_; lean_object* v_k_906_; lean_object* v_v_907_; lean_object* v_l_908_; lean_object* v_r_909_; lean_object* v___x_910_; lean_object* v___x_911_; uint8_t v___x_912_; 
v_size_904_ = lean_ctor_get(v_l_891_, 0);
v_size_905_ = lean_ctor_get(v_r_892_, 0);
v_k_906_ = lean_ctor_get(v_r_892_, 1);
v_v_907_ = lean_ctor_get(v_r_892_, 2);
v_l_908_ = lean_ctor_get(v_r_892_, 3);
v_r_909_ = lean_ctor_get(v_r_892_, 4);
v___x_910_ = lean_unsigned_to_nat(2u);
v___x_911_ = lean_nat_mul(v___x_910_, v_size_904_);
v___x_912_ = lean_nat_dec_lt(v_size_905_, v___x_911_);
lean_dec(v___x_911_);
if (v___x_912_ == 0)
{
lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_941_; 
lean_inc(v_r_909_);
lean_inc(v_l_908_);
lean_inc(v_v_907_);
lean_inc(v_k_906_);
v_isSharedCheck_941_ = !lean_is_exclusive(v_r_892_);
if (v_isSharedCheck_941_ == 0)
{
lean_object* v_unused_942_; lean_object* v_unused_943_; lean_object* v_unused_944_; lean_object* v_unused_945_; lean_object* v_unused_946_; 
v_unused_942_ = lean_ctor_get(v_r_892_, 4);
lean_dec(v_unused_942_);
v_unused_943_ = lean_ctor_get(v_r_892_, 3);
lean_dec(v_unused_943_);
v_unused_944_ = lean_ctor_get(v_r_892_, 2);
lean_dec(v_unused_944_);
v_unused_945_ = lean_ctor_get(v_r_892_, 1);
lean_dec(v_unused_945_);
v_unused_946_ = lean_ctor_get(v_r_892_, 0);
lean_dec(v_unused_946_);
v___x_914_ = v_r_892_;
v_isShared_915_ = v_isSharedCheck_941_;
goto v_resetjp_913_;
}
else
{
lean_dec(v_r_892_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_941_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___x_929_; lean_object* v___y_931_; 
v___x_916_ = lean_nat_add(v___x_886_, v_size_888_);
lean_dec(v_size_888_);
v___x_917_ = lean_nat_add(v___x_916_, v_size_887_);
lean_dec(v___x_916_);
v___x_929_ = lean_nat_add(v___x_886_, v_size_904_);
if (lean_obj_tag(v_l_908_) == 0)
{
lean_object* v_size_939_; 
v_size_939_ = lean_ctor_get(v_l_908_, 0);
lean_inc(v_size_939_);
v___y_931_ = v_size_939_;
goto v___jp_930_;
}
else
{
lean_object* v___x_940_; 
v___x_940_ = lean_unsigned_to_nat(0u);
v___y_931_ = v___x_940_;
goto v___jp_930_;
}
v___jp_918_:
{
lean_object* v___x_922_; lean_object* v___x_924_; 
v___x_922_ = lean_nat_add(v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec(v___y_920_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 4, v_r_880_);
lean_ctor_set(v___x_914_, 3, v_r_909_);
lean_ctor_set(v___x_914_, 2, v_v_878_);
lean_ctor_set(v___x_914_, 1, v_k_877_);
lean_ctor_set(v___x_914_, 0, v___x_922_);
v___x_924_ = v___x_914_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_922_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v_k_877_);
lean_ctor_set(v_reuseFailAlloc_928_, 2, v_v_878_);
lean_ctor_set(v_reuseFailAlloc_928_, 3, v_r_909_);
lean_ctor_set(v_reuseFailAlloc_928_, 4, v_r_880_);
v___x_924_ = v_reuseFailAlloc_928_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
lean_object* v___x_926_; 
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 4, v___x_924_);
lean_ctor_set(v___x_902_, 3, v___y_919_);
lean_ctor_set(v___x_902_, 2, v_v_907_);
lean_ctor_set(v___x_902_, 1, v_k_906_);
lean_ctor_set(v___x_902_, 0, v___x_917_);
v___x_926_ = v___x_902_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_k_906_);
lean_ctor_set(v_reuseFailAlloc_927_, 2, v_v_907_);
lean_ctor_set(v_reuseFailAlloc_927_, 3, v___y_919_);
lean_ctor_set(v_reuseFailAlloc_927_, 4, v___x_924_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
v___jp_930_:
{
lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_932_ = lean_nat_add(v___x_929_, v___y_931_);
lean_dec(v___y_931_);
lean_dec(v___x_929_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 4, v_l_908_);
lean_ctor_set(v___x_882_, 3, v_l_891_);
lean_ctor_set(v___x_882_, 2, v_v_890_);
lean_ctor_set(v___x_882_, 1, v_k_889_);
lean_ctor_set(v___x_882_, 0, v___x_932_);
v___x_934_ = v___x_882_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v_k_889_);
lean_ctor_set(v_reuseFailAlloc_938_, 2, v_v_890_);
lean_ctor_set(v_reuseFailAlloc_938_, 3, v_l_891_);
lean_ctor_set(v_reuseFailAlloc_938_, 4, v_l_908_);
v___x_934_ = v_reuseFailAlloc_938_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_935_; 
v___x_935_ = lean_nat_add(v___x_886_, v_size_887_);
if (lean_obj_tag(v_r_909_) == 0)
{
lean_object* v_size_936_; 
v_size_936_ = lean_ctor_get(v_r_909_, 0);
lean_inc(v_size_936_);
v___y_919_ = v___x_934_;
v___y_920_ = v___x_935_;
v___y_921_ = v_size_936_;
goto v___jp_918_;
}
else
{
lean_object* v___x_937_; 
v___x_937_ = lean_unsigned_to_nat(0u);
v___y_919_ = v___x_934_;
v___y_920_ = v___x_935_;
v___y_921_ = v___x_937_;
goto v___jp_918_;
}
}
}
}
}
else
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_952_; 
lean_del_object(v___x_882_);
v___x_947_ = lean_nat_add(v___x_886_, v_size_888_);
lean_dec(v_size_888_);
v___x_948_ = lean_nat_add(v___x_947_, v_size_887_);
lean_dec(v___x_947_);
v___x_949_ = lean_nat_add(v___x_886_, v_size_887_);
v___x_950_ = lean_nat_add(v___x_949_, v_size_905_);
lean_dec(v___x_949_);
lean_inc_ref(v_r_880_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 4, v_r_880_);
lean_ctor_set(v___x_902_, 3, v_r_892_);
lean_ctor_set(v___x_902_, 2, v_v_878_);
lean_ctor_set(v___x_902_, 1, v_k_877_);
lean_ctor_set(v___x_902_, 0, v___x_950_);
v___x_952_ = v___x_902_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_950_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_k_877_);
lean_ctor_set(v_reuseFailAlloc_965_, 2, v_v_878_);
lean_ctor_set(v_reuseFailAlloc_965_, 3, v_r_892_);
lean_ctor_set(v_reuseFailAlloc_965_, 4, v_r_880_);
v___x_952_ = v_reuseFailAlloc_965_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
v_isSharedCheck_959_ = !lean_is_exclusive(v_r_880_);
if (v_isSharedCheck_959_ == 0)
{
lean_object* v_unused_960_; lean_object* v_unused_961_; lean_object* v_unused_962_; lean_object* v_unused_963_; lean_object* v_unused_964_; 
v_unused_960_ = lean_ctor_get(v_r_880_, 4);
lean_dec(v_unused_960_);
v_unused_961_ = lean_ctor_get(v_r_880_, 3);
lean_dec(v_unused_961_);
v_unused_962_ = lean_ctor_get(v_r_880_, 2);
lean_dec(v_unused_962_);
v_unused_963_ = lean_ctor_get(v_r_880_, 1);
lean_dec(v_unused_963_);
v_unused_964_ = lean_ctor_get(v_r_880_, 0);
lean_dec(v_unused_964_);
v___x_954_ = v_r_880_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_dec(v_r_880_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 4, v___x_952_);
lean_ctor_set(v___x_954_, 3, v_l_891_);
lean_ctor_set(v___x_954_, 2, v_v_890_);
lean_ctor_set(v___x_954_, 1, v_k_889_);
lean_ctor_set(v___x_954_, 0, v___x_948_);
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_k_889_);
lean_ctor_set(v_reuseFailAlloc_958_, 2, v_v_890_);
lean_ctor_set(v_reuseFailAlloc_958_, 3, v_l_891_);
lean_ctor_set(v_reuseFailAlloc_958_, 4, v___x_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_972_; 
v_l_972_ = lean_ctor_get(v_impl_885_, 3);
if (lean_obj_tag(v_l_972_) == 0)
{
lean_object* v_r_973_; lean_object* v_k_974_; lean_object* v_v_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_986_; 
lean_inc_ref(v_l_972_);
v_r_973_ = lean_ctor_get(v_impl_885_, 4);
v_k_974_ = lean_ctor_get(v_impl_885_, 1);
v_v_975_ = lean_ctor_get(v_impl_885_, 2);
v_isSharedCheck_986_ = !lean_is_exclusive(v_impl_885_);
if (v_isSharedCheck_986_ == 0)
{
lean_object* v_unused_987_; lean_object* v_unused_988_; 
v_unused_987_ = lean_ctor_get(v_impl_885_, 3);
lean_dec(v_unused_987_);
v_unused_988_ = lean_ctor_get(v_impl_885_, 0);
lean_dec(v_unused_988_);
v___x_977_ = v_impl_885_;
v_isShared_978_ = v_isSharedCheck_986_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_r_973_);
lean_inc(v_v_975_);
lean_inc(v_k_974_);
lean_dec(v_impl_885_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_986_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; lean_object* v___x_981_; 
v___x_979_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_973_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 3, v_r_973_);
lean_ctor_set(v___x_977_, 2, v_v_878_);
lean_ctor_set(v___x_977_, 1, v_k_877_);
lean_ctor_set(v___x_977_, 0, v___x_886_);
v___x_981_ = v___x_977_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_k_877_);
lean_ctor_set(v_reuseFailAlloc_985_, 2, v_v_878_);
lean_ctor_set(v_reuseFailAlloc_985_, 3, v_r_973_);
lean_ctor_set(v_reuseFailAlloc_985_, 4, v_r_973_);
v___x_981_ = v_reuseFailAlloc_985_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_983_; 
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 4, v___x_981_);
lean_ctor_set(v___x_882_, 3, v_l_972_);
lean_ctor_set(v___x_882_, 2, v_v_975_);
lean_ctor_set(v___x_882_, 1, v_k_974_);
lean_ctor_set(v___x_882_, 0, v___x_979_);
v___x_983_ = v___x_882_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_979_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v_k_974_);
lean_ctor_set(v_reuseFailAlloc_984_, 2, v_v_975_);
lean_ctor_set(v_reuseFailAlloc_984_, 3, v_l_972_);
lean_ctor_set(v_reuseFailAlloc_984_, 4, v___x_981_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
else
{
lean_object* v_r_989_; 
v_r_989_ = lean_ctor_get(v_impl_885_, 4);
lean_inc(v_r_989_);
if (lean_obj_tag(v_r_989_) == 0)
{
lean_object* v_k_990_; lean_object* v_v_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1014_; 
lean_inc(v_l_972_);
v_k_990_ = lean_ctor_get(v_impl_885_, 1);
v_v_991_ = lean_ctor_get(v_impl_885_, 2);
v_isSharedCheck_1014_ = !lean_is_exclusive(v_impl_885_);
if (v_isSharedCheck_1014_ == 0)
{
lean_object* v_unused_1015_; lean_object* v_unused_1016_; lean_object* v_unused_1017_; 
v_unused_1015_ = lean_ctor_get(v_impl_885_, 4);
lean_dec(v_unused_1015_);
v_unused_1016_ = lean_ctor_get(v_impl_885_, 3);
lean_dec(v_unused_1016_);
v_unused_1017_ = lean_ctor_get(v_impl_885_, 0);
lean_dec(v_unused_1017_);
v___x_993_ = v_impl_885_;
v_isShared_994_ = v_isSharedCheck_1014_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_v_991_);
lean_inc(v_k_990_);
lean_dec(v_impl_885_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1014_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v_k_995_; lean_object* v_v_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1010_; 
v_k_995_ = lean_ctor_get(v_r_989_, 1);
v_v_996_ = lean_ctor_get(v_r_989_, 2);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_r_989_);
if (v_isSharedCheck_1010_ == 0)
{
lean_object* v_unused_1011_; lean_object* v_unused_1012_; lean_object* v_unused_1013_; 
v_unused_1011_ = lean_ctor_get(v_r_989_, 4);
lean_dec(v_unused_1011_);
v_unused_1012_ = lean_ctor_get(v_r_989_, 3);
lean_dec(v_unused_1012_);
v_unused_1013_ = lean_ctor_get(v_r_989_, 0);
lean_dec(v_unused_1013_);
v___x_998_ = v_r_989_;
v_isShared_999_ = v_isSharedCheck_1010_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_v_996_);
lean_inc(v_k_995_);
lean_dec(v_r_989_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1010_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1000_; lean_object* v___x_1002_; 
v___x_1000_ = lean_unsigned_to_nat(3u);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 4, v_l_972_);
lean_ctor_set(v___x_998_, 3, v_l_972_);
lean_ctor_set(v___x_998_, 2, v_v_991_);
lean_ctor_set(v___x_998_, 1, v_k_990_);
lean_ctor_set(v___x_998_, 0, v___x_886_);
v___x_1002_ = v___x_998_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_k_990_);
lean_ctor_set(v_reuseFailAlloc_1009_, 2, v_v_991_);
lean_ctor_set(v_reuseFailAlloc_1009_, 3, v_l_972_);
lean_ctor_set(v_reuseFailAlloc_1009_, 4, v_l_972_);
v___x_1002_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
lean_object* v___x_1004_; 
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 4, v_l_972_);
lean_ctor_set(v___x_993_, 2, v_v_878_);
lean_ctor_set(v___x_993_, 1, v_k_877_);
lean_ctor_set(v___x_993_, 0, v___x_886_);
v___x_1004_ = v___x_993_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v_k_877_);
lean_ctor_set(v_reuseFailAlloc_1008_, 2, v_v_878_);
lean_ctor_set(v_reuseFailAlloc_1008_, 3, v_l_972_);
lean_ctor_set(v_reuseFailAlloc_1008_, 4, v_l_972_);
v___x_1004_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
lean_object* v___x_1006_; 
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 4, v___x_1004_);
lean_ctor_set(v___x_882_, 3, v___x_1002_);
lean_ctor_set(v___x_882_, 2, v_v_996_);
lean_ctor_set(v___x_882_, 1, v_k_995_);
lean_ctor_set(v___x_882_, 0, v___x_1000_);
v___x_1006_ = v___x_882_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1000_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_k_995_);
lean_ctor_set(v_reuseFailAlloc_1007_, 2, v_v_996_);
lean_ctor_set(v_reuseFailAlloc_1007_, 3, v___x_1002_);
lean_ctor_set(v_reuseFailAlloc_1007_, 4, v___x_1004_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
}
}
else
{
lean_object* v___x_1018_; lean_object* v___x_1020_; 
v___x_1018_ = lean_unsigned_to_nat(2u);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 4, v_r_989_);
lean_ctor_set(v___x_882_, 3, v_impl_885_);
lean_ctor_set(v___x_882_, 0, v___x_1018_);
v___x_1020_ = v___x_882_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1018_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_k_877_);
lean_ctor_set(v_reuseFailAlloc_1021_, 2, v_v_878_);
lean_ctor_set(v_reuseFailAlloc_1021_, 3, v_impl_885_);
lean_ctor_set(v_reuseFailAlloc_1021_, 4, v_r_989_);
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
}
case 1:
{
lean_object* v___x_1023_; 
lean_dec(v_v_878_);
lean_dec(v_k_877_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 2, v_v_874_);
lean_ctor_set(v___x_882_, 1, v_k_873_);
v___x_1023_ = v___x_882_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_size_876_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_k_873_);
lean_ctor_set(v_reuseFailAlloc_1024_, 2, v_v_874_);
lean_ctor_set(v_reuseFailAlloc_1024_, 3, v_l_879_);
lean_ctor_set(v_reuseFailAlloc_1024_, 4, v_r_880_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
default: 
{
lean_object* v_impl_1025_; lean_object* v___x_1026_; 
lean_dec(v_size_876_);
v_impl_1025_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_873_, v_v_874_, v_r_880_);
v___x_1026_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_879_) == 0)
{
lean_object* v_size_1027_; lean_object* v_size_1028_; lean_object* v_k_1029_; lean_object* v_v_1030_; lean_object* v_l_1031_; lean_object* v_r_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
v_size_1027_ = lean_ctor_get(v_l_879_, 0);
v_size_1028_ = lean_ctor_get(v_impl_1025_, 0);
v_k_1029_ = lean_ctor_get(v_impl_1025_, 1);
v_v_1030_ = lean_ctor_get(v_impl_1025_, 2);
v_l_1031_ = lean_ctor_get(v_impl_1025_, 3);
lean_inc(v_l_1031_);
v_r_1032_ = lean_ctor_get(v_impl_1025_, 4);
v___x_1033_ = lean_unsigned_to_nat(3u);
v___x_1034_ = lean_nat_mul(v___x_1033_, v_size_1027_);
v___x_1035_ = lean_nat_dec_lt(v___x_1034_, v_size_1028_);
lean_dec(v___x_1034_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1039_; 
lean_dec(v_l_1031_);
v___x_1036_ = lean_nat_add(v___x_1026_, v_size_1027_);
v___x_1037_ = lean_nat_add(v___x_1036_, v_size_1028_);
lean_dec(v___x_1036_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 4, v_impl_1025_);
lean_ctor_set(v___x_882_, 0, v___x_1037_);
v___x_1039_ = v___x_882_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_k_877_);
lean_ctor_set(v_reuseFailAlloc_1040_, 2, v_v_878_);
lean_ctor_set(v_reuseFailAlloc_1040_, 3, v_l_879_);
lean_ctor_set(v_reuseFailAlloc_1040_, 4, v_impl_1025_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
else
{
lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1104_; 
lean_inc(v_r_1032_);
lean_inc(v_v_1030_);
lean_inc(v_k_1029_);
lean_inc(v_size_1028_);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_impl_1025_);
if (v_isSharedCheck_1104_ == 0)
{
lean_object* v_unused_1105_; lean_object* v_unused_1106_; lean_object* v_unused_1107_; lean_object* v_unused_1108_; lean_object* v_unused_1109_; 
v_unused_1105_ = lean_ctor_get(v_impl_1025_, 4);
lean_dec(v_unused_1105_);
v_unused_1106_ = lean_ctor_get(v_impl_1025_, 3);
lean_dec(v_unused_1106_);
v_unused_1107_ = lean_ctor_get(v_impl_1025_, 2);
lean_dec(v_unused_1107_);
v_unused_1108_ = lean_ctor_get(v_impl_1025_, 1);
lean_dec(v_unused_1108_);
v_unused_1109_ = lean_ctor_get(v_impl_1025_, 0);
lean_dec(v_unused_1109_);
v___x_1042_ = v_impl_1025_;
v_isShared_1043_ = v_isSharedCheck_1104_;
goto v_resetjp_1041_;
}
else
{
lean_dec(v_impl_1025_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1104_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v_size_1044_; lean_object* v_k_1045_; lean_object* v_v_1046_; lean_object* v_l_1047_; lean_object* v_r_1048_; lean_object* v_size_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v_size_1044_ = lean_ctor_get(v_l_1031_, 0);
v_k_1045_ = lean_ctor_get(v_l_1031_, 1);
v_v_1046_ = lean_ctor_get(v_l_1031_, 2);
v_l_1047_ = lean_ctor_get(v_l_1031_, 3);
v_r_1048_ = lean_ctor_get(v_l_1031_, 4);
v_size_1049_ = lean_ctor_get(v_r_1032_, 0);
v___x_1050_ = lean_unsigned_to_nat(2u);
v___x_1051_ = lean_nat_mul(v___x_1050_, v_size_1049_);
v___x_1052_ = lean_nat_dec_lt(v_size_1044_, v___x_1051_);
lean_dec(v___x_1051_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1080_; 
lean_inc(v_r_1048_);
lean_inc(v_l_1047_);
lean_inc(v_v_1046_);
lean_inc(v_k_1045_);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_l_1031_);
if (v_isSharedCheck_1080_ == 0)
{
lean_object* v_unused_1081_; lean_object* v_unused_1082_; lean_object* v_unused_1083_; lean_object* v_unused_1084_; lean_object* v_unused_1085_; 
v_unused_1081_ = lean_ctor_get(v_l_1031_, 4);
lean_dec(v_unused_1081_);
v_unused_1082_ = lean_ctor_get(v_l_1031_, 3);
lean_dec(v_unused_1082_);
v_unused_1083_ = lean_ctor_get(v_l_1031_, 2);
lean_dec(v_unused_1083_);
v_unused_1084_ = lean_ctor_get(v_l_1031_, 1);
lean_dec(v_unused_1084_);
v_unused_1085_ = lean_ctor_get(v_l_1031_, 0);
lean_dec(v_unused_1085_);
v___x_1054_ = v_l_1031_;
v_isShared_1055_ = v_isSharedCheck_1080_;
goto v_resetjp_1053_;
}
else
{
lean_dec(v_l_1031_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1080_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1070_; 
v___x_1056_ = lean_nat_add(v___x_1026_, v_size_1027_);
v___x_1057_ = lean_nat_add(v___x_1056_, v_size_1028_);
lean_dec(v_size_1028_);
if (lean_obj_tag(v_l_1047_) == 0)
{
lean_object* v_size_1078_; 
v_size_1078_ = lean_ctor_get(v_l_1047_, 0);
lean_inc(v_size_1078_);
v___y_1070_ = v_size_1078_;
goto v___jp_1069_;
}
else
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_unsigned_to_nat(0u);
v___y_1070_ = v___x_1079_;
goto v___jp_1069_;
}
v___jp_1058_:
{
lean_object* v___x_1062_; lean_object* v___x_1064_; 
v___x_1062_ = lean_nat_add(v___y_1059_, v___y_1061_);
lean_dec(v___y_1061_);
lean_dec(v___y_1059_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 4, v_r_1032_);
lean_ctor_set(v___x_1054_, 3, v_r_1048_);
lean_ctor_set(v___x_1054_, 2, v_v_1030_);
lean_ctor_set(v___x_1054_, 1, v_k_1029_);
lean_ctor_set(v___x_1054_, 0, v___x_1062_);
v___x_1064_ = v___x_1054_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1062_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v_k_1029_);
lean_ctor_set(v_reuseFailAlloc_1068_, 2, v_v_1030_);
lean_ctor_set(v_reuseFailAlloc_1068_, 3, v_r_1048_);
lean_ctor_set(v_reuseFailAlloc_1068_, 4, v_r_1032_);
v___x_1064_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
lean_object* v___x_1066_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 4, v___x_1064_);
lean_ctor_set(v___x_1042_, 3, v___y_1060_);
lean_ctor_set(v___x_1042_, 2, v_v_1046_);
lean_ctor_set(v___x_1042_, 1, v_k_1045_);
lean_ctor_set(v___x_1042_, 0, v___x_1057_);
v___x_1066_ = v___x_1042_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1057_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_k_1045_);
lean_ctor_set(v_reuseFailAlloc_1067_, 2, v_v_1046_);
lean_ctor_set(v_reuseFailAlloc_1067_, 3, v___y_1060_);
lean_ctor_set(v_reuseFailAlloc_1067_, 4, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
v___jp_1069_:
{
lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1071_ = lean_nat_add(v___x_1056_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec(v___x_1056_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 4, v_l_1047_);
lean_ctor_set(v___x_882_, 0, v___x_1071_);
v___x_1073_ = v___x_882_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1071_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v_k_877_);
lean_ctor_set(v_reuseFailAlloc_1077_, 2, v_v_878_);
lean_ctor_set(v_reuseFailAlloc_1077_, 3, v_l_879_);
lean_ctor_set(v_reuseFailAlloc_1077_, 4, v_l_1047_);
v___x_1073_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1074_; 
v___x_1074_ = lean_nat_add(v___x_1026_, v_size_1049_);
if (lean_obj_tag(v_r_1048_) == 0)
{
lean_object* v_size_1075_; 
v_size_1075_ = lean_ctor_get(v_r_1048_, 0);
lean_inc(v_size_1075_);
v___y_1059_ = v___x_1074_;
v___y_1060_ = v___x_1073_;
v___y_1061_ = v_size_1075_;
goto v___jp_1058_;
}
else
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_unsigned_to_nat(0u);
v___y_1059_ = v___x_1074_;
v___y_1060_ = v___x_1073_;
v___y_1061_ = v___x_1076_;
goto v___jp_1058_;
}
}
}
}
}
else
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1090_; 
lean_del_object(v___x_882_);
v___x_1086_ = lean_nat_add(v___x_1026_, v_size_1027_);
v___x_1087_ = lean_nat_add(v___x_1086_, v_size_1028_);
lean_dec(v_size_1028_);
v___x_1088_ = lean_nat_add(v___x_1086_, v_size_1044_);
lean_dec(v___x_1086_);
lean_inc_ref(v_l_879_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 4, v_l_1031_);
lean_ctor_set(v___x_1042_, 3, v_l_879_);
lean_ctor_set(v___x_1042_, 2, v_v_878_);
lean_ctor_set(v___x_1042_, 1, v_k_877_);
lean_ctor_set(v___x_1042_, 0, v___x_1088_);
v___x_1090_ = v___x_1042_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v___x_1088_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_k_877_);
lean_ctor_set(v_reuseFailAlloc_1103_, 2, v_v_878_);
lean_ctor_set(v_reuseFailAlloc_1103_, 3, v_l_879_);
lean_ctor_set(v_reuseFailAlloc_1103_, 4, v_l_1031_);
v___x_1090_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
v_isSharedCheck_1097_ = !lean_is_exclusive(v_l_879_);
if (v_isSharedCheck_1097_ == 0)
{
lean_object* v_unused_1098_; lean_object* v_unused_1099_; lean_object* v_unused_1100_; lean_object* v_unused_1101_; lean_object* v_unused_1102_; 
v_unused_1098_ = lean_ctor_get(v_l_879_, 4);
lean_dec(v_unused_1098_);
v_unused_1099_ = lean_ctor_get(v_l_879_, 3);
lean_dec(v_unused_1099_);
v_unused_1100_ = lean_ctor_get(v_l_879_, 2);
lean_dec(v_unused_1100_);
v_unused_1101_ = lean_ctor_get(v_l_879_, 1);
lean_dec(v_unused_1101_);
v_unused_1102_ = lean_ctor_get(v_l_879_, 0);
lean_dec(v_unused_1102_);
v___x_1092_ = v_l_879_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_dec(v_l_879_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 4, v_r_1032_);
lean_ctor_set(v___x_1092_, 3, v___x_1090_);
lean_ctor_set(v___x_1092_, 2, v_v_1030_);
lean_ctor_set(v___x_1092_, 1, v_k_1029_);
lean_ctor_set(v___x_1092_, 0, v___x_1087_);
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_k_1029_);
lean_ctor_set(v_reuseFailAlloc_1096_, 2, v_v_1030_);
lean_ctor_set(v_reuseFailAlloc_1096_, 3, v___x_1090_);
lean_ctor_set(v_reuseFailAlloc_1096_, 4, v_r_1032_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1110_; 
v_l_1110_ = lean_ctor_get(v_impl_1025_, 3);
lean_inc(v_l_1110_);
if (lean_obj_tag(v_l_1110_) == 0)
{
lean_object* v_r_1111_; lean_object* v_k_1112_; lean_object* v_v_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1136_; 
v_r_1111_ = lean_ctor_get(v_impl_1025_, 4);
v_k_1112_ = lean_ctor_get(v_impl_1025_, 1);
v_v_1113_ = lean_ctor_get(v_impl_1025_, 2);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_impl_1025_);
if (v_isSharedCheck_1136_ == 0)
{
lean_object* v_unused_1137_; lean_object* v_unused_1138_; 
v_unused_1137_ = lean_ctor_get(v_impl_1025_, 3);
lean_dec(v_unused_1137_);
v_unused_1138_ = lean_ctor_get(v_impl_1025_, 0);
lean_dec(v_unused_1138_);
v___x_1115_ = v_impl_1025_;
v_isShared_1116_ = v_isSharedCheck_1136_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_r_1111_);
lean_inc(v_v_1113_);
lean_inc(v_k_1112_);
lean_dec(v_impl_1025_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1136_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v_k_1117_; lean_object* v_v_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1132_; 
v_k_1117_ = lean_ctor_get(v_l_1110_, 1);
v_v_1118_ = lean_ctor_get(v_l_1110_, 2);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_l_1110_);
if (v_isSharedCheck_1132_ == 0)
{
lean_object* v_unused_1133_; lean_object* v_unused_1134_; lean_object* v_unused_1135_; 
v_unused_1133_ = lean_ctor_get(v_l_1110_, 4);
lean_dec(v_unused_1133_);
v_unused_1134_ = lean_ctor_get(v_l_1110_, 3);
lean_dec(v_unused_1134_);
v_unused_1135_ = lean_ctor_get(v_l_1110_, 0);
lean_dec(v_unused_1135_);
v___x_1120_ = v_l_1110_;
v_isShared_1121_ = v_isSharedCheck_1132_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_v_1118_);
lean_inc(v_k_1117_);
lean_dec(v_l_1110_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1132_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1122_; lean_object* v___x_1124_; 
v___x_1122_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1111_, 2);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 4, v_r_1111_);
lean_ctor_set(v___x_1120_, 3, v_r_1111_);
lean_ctor_set(v___x_1120_, 2, v_v_878_);
lean_ctor_set(v___x_1120_, 1, v_k_877_);
lean_ctor_set(v___x_1120_, 0, v___x_1026_);
v___x_1124_ = v___x_1120_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_k_877_);
lean_ctor_set(v_reuseFailAlloc_1131_, 2, v_v_878_);
lean_ctor_set(v_reuseFailAlloc_1131_, 3, v_r_1111_);
lean_ctor_set(v_reuseFailAlloc_1131_, 4, v_r_1111_);
v___x_1124_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
lean_object* v___x_1126_; 
lean_inc(v_r_1111_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 3, v_r_1111_);
lean_ctor_set(v___x_1115_, 0, v___x_1026_);
v___x_1126_ = v___x_1115_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_k_1112_);
lean_ctor_set(v_reuseFailAlloc_1130_, 2, v_v_1113_);
lean_ctor_set(v_reuseFailAlloc_1130_, 3, v_r_1111_);
lean_ctor_set(v_reuseFailAlloc_1130_, 4, v_r_1111_);
v___x_1126_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
lean_object* v___x_1128_; 
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 4, v___x_1126_);
lean_ctor_set(v___x_882_, 3, v___x_1124_);
lean_ctor_set(v___x_882_, 2, v_v_1118_);
lean_ctor_set(v___x_882_, 1, v_k_1117_);
lean_ctor_set(v___x_882_, 0, v___x_1122_);
v___x_1128_ = v___x_882_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1122_);
lean_ctor_set(v_reuseFailAlloc_1129_, 1, v_k_1117_);
lean_ctor_set(v_reuseFailAlloc_1129_, 2, v_v_1118_);
lean_ctor_set(v_reuseFailAlloc_1129_, 3, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1129_, 4, v___x_1126_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
}
}
else
{
lean_object* v_r_1139_; 
v_r_1139_ = lean_ctor_get(v_impl_1025_, 4);
lean_inc(v_r_1139_);
if (lean_obj_tag(v_r_1139_) == 0)
{
lean_object* v_k_1140_; lean_object* v_v_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1152_; 
v_k_1140_ = lean_ctor_get(v_impl_1025_, 1);
v_v_1141_ = lean_ctor_get(v_impl_1025_, 2);
v_isSharedCheck_1152_ = !lean_is_exclusive(v_impl_1025_);
if (v_isSharedCheck_1152_ == 0)
{
lean_object* v_unused_1153_; lean_object* v_unused_1154_; lean_object* v_unused_1155_; 
v_unused_1153_ = lean_ctor_get(v_impl_1025_, 4);
lean_dec(v_unused_1153_);
v_unused_1154_ = lean_ctor_get(v_impl_1025_, 3);
lean_dec(v_unused_1154_);
v_unused_1155_ = lean_ctor_get(v_impl_1025_, 0);
lean_dec(v_unused_1155_);
v___x_1143_ = v_impl_1025_;
v_isShared_1144_ = v_isSharedCheck_1152_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_v_1141_);
lean_inc(v_k_1140_);
lean_dec(v_impl_1025_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1152_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1145_; lean_object* v___x_1147_; 
v___x_1145_ = lean_unsigned_to_nat(3u);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 4, v_l_1110_);
lean_ctor_set(v___x_1143_, 2, v_v_878_);
lean_ctor_set(v___x_1143_, 1, v_k_877_);
lean_ctor_set(v___x_1143_, 0, v___x_1026_);
v___x_1147_ = v___x_1143_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_k_877_);
lean_ctor_set(v_reuseFailAlloc_1151_, 2, v_v_878_);
lean_ctor_set(v_reuseFailAlloc_1151_, 3, v_l_1110_);
lean_ctor_set(v_reuseFailAlloc_1151_, 4, v_l_1110_);
v___x_1147_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_object* v___x_1149_; 
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 4, v_r_1139_);
lean_ctor_set(v___x_882_, 3, v___x_1147_);
lean_ctor_set(v___x_882_, 2, v_v_1141_);
lean_ctor_set(v___x_882_, 1, v_k_1140_);
lean_ctor_set(v___x_882_, 0, v___x_1145_);
v___x_1149_ = v___x_882_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v_k_1140_);
lean_ctor_set(v_reuseFailAlloc_1150_, 2, v_v_1141_);
lean_ctor_set(v_reuseFailAlloc_1150_, 3, v___x_1147_);
lean_ctor_set(v_reuseFailAlloc_1150_, 4, v_r_1139_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
else
{
lean_object* v___x_1156_; lean_object* v___x_1158_; 
v___x_1156_ = lean_unsigned_to_nat(2u);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 4, v_impl_1025_);
lean_ctor_set(v___x_882_, 3, v_r_1139_);
lean_ctor_set(v___x_882_, 0, v___x_1156_);
v___x_1158_ = v___x_882_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_k_877_);
lean_ctor_set(v_reuseFailAlloc_1159_, 2, v_v_878_);
lean_ctor_set(v_reuseFailAlloc_1159_, 3, v_r_1139_);
lean_ctor_set(v_reuseFailAlloc_1159_, 4, v_impl_1025_);
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
}
}
}
}
else
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = lean_unsigned_to_nat(1u);
v___x_1162_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
lean_ctor_set(v___x_1162_, 1, v_k_873_);
lean_ctor_set(v___x_1162_, 2, v_v_874_);
lean_ctor_set(v___x_1162_, 3, v_t_875_);
lean_ctor_set(v___x_1162_, 4, v_t_875_);
return v___x_1162_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(lean_object* v_as_x27_1163_, lean_object* v_b_1164_){
_start:
{
if (lean_obj_tag(v_as_x27_1163_) == 0)
{
return v_b_1164_;
}
else
{
lean_object* v_head_1165_; lean_object* v_tail_1166_; lean_object* v_fst_1167_; lean_object* v_snd_1168_; lean_object* v_r_1169_; 
v_head_1165_ = lean_ctor_get(v_as_x27_1163_, 0);
v_tail_1166_ = lean_ctor_get(v_as_x27_1163_, 1);
v_fst_1167_ = lean_ctor_get(v_head_1165_, 0);
v_snd_1168_ = lean_ctor_get(v_head_1165_, 1);
lean_inc(v_snd_1168_);
lean_inc(v_fst_1167_);
v_r_1169_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_fst_1167_, v_snd_1168_, v_b_1164_);
v_as_x27_1163_ = v_tail_1166_;
v_b_1164_ = v_r_1169_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg___boxed(lean_object* v_as_x27_1171_, lean_object* v_b_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_as_x27_1171_, v_b_1172_);
lean_dec(v_as_x27_1171_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mkObj(lean_object* v_o_1174_){
_start:
{
lean_object* v_r_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v_r_1175_ = lean_box(1);
v___x_1176_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_o_1174_, v_r_1175_);
v___x_1177_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mkObj___boxed(lean_object* v_o_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_Json_mkObj(v_o_1178_);
lean_dec(v_o_1178_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0(lean_object* v_00_u03b2_1180_, lean_object* v_k_1181_, lean_object* v_v_1182_, lean_object* v_t_1183_, lean_object* v_hl_1184_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_1181_, v_v_1182_, v_t_1183_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1(lean_object* v_as_1186_, lean_object* v_as_x27_1187_, lean_object* v_b_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_as_x27_1187_, v_b_1188_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___boxed(lean_object* v_as_1191_, lean_object* v_as_x27_1192_, lean_object* v_b_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1(v_as_1191_, v_as_x27_1192_, v_b_1193_, v_a_1194_);
lean_dec(v_as_x27_1192_);
lean_dec(v_as_1191_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeNat___lam__0(lean_object* v_n_1196_){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = l_Lean_JsonNumber_fromNat(v_n_1196_);
v___x_1198_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeInt___lam__0(lean_object* v_n_1201_){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = l_Lean_JsonNumber_fromInt(v_n_1201_);
v___x_1203_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeString___lam__0(lean_object* v_s_1206_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1207_, 0, v_s_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeBool___lam__0(uint8_t v_b_1210_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1211_, 0, v_b_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeBool___lam__0___boxed(lean_object* v_b_1212_){
_start:
{
uint8_t v_b_boxed_1213_; lean_object* v_res_1214_; 
v_b_boxed_1213_ = lean_unbox(v_b_1212_);
v_res_1214_ = l_Lean_Json_instCoeBool___lam__0(v_b_boxed_1213_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instOfNat(lean_object* v_n_1217_){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = l_Lean_JsonNumber_fromNat(v_n_1217_);
v___x_1219_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT uint8_t l_Lean_Json_isNull(lean_object* v_x_1220_){
_start:
{
if (lean_obj_tag(v_x_1220_) == 0)
{
uint8_t v___x_1221_; 
v___x_1221_ = 1;
return v___x_1221_;
}
else
{
uint8_t v___x_1222_; 
v___x_1222_ = 0;
return v___x_1222_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_isNull___boxed(lean_object* v_x_1223_){
_start:
{
uint8_t v_res_1224_; lean_object* v_r_1225_; 
v_res_1224_ = l_Lean_Json_isNull(v_x_1223_);
lean_dec(v_x_1223_);
v_r_1225_ = lean_box(v_res_1224_);
return v_r_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObj_x3f(lean_object* v_x_1229_){
_start:
{
if (lean_obj_tag(v_x_1229_) == 5)
{
lean_object* v_kvPairs_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
v_kvPairs_1230_ = lean_ctor_get(v_x_1229_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_x_1229_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1232_ = v_x_1229_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_kvPairs_1230_);
lean_dec(v_x_1229_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
lean_ctor_set_tag(v___x_1232_, 1);
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_kvPairs_1230_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
else
{
lean_object* v___x_1238_; 
lean_dec(v_x_1229_);
v___x_1238_ = ((lean_object*)(l_Lean_Json_getObj_x3f___closed__1));
return v___x_1238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getArr_x3f(lean_object* v_x_1242_){
_start:
{
if (lean_obj_tag(v_x_1242_) == 4)
{
lean_object* v_elems_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
v_elems_1243_ = lean_ctor_get(v_x_1242_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v_x_1242_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v_x_1242_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_elems_1243_);
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
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_elems_1243_);
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
v___x_1251_ = ((lean_object*)(l_Lean_Json_getArr_x3f___closed__1));
return v___x_1251_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getStr_x3f(lean_object* v_x_1255_){
_start:
{
if (lean_obj_tag(v_x_1255_) == 3)
{
lean_object* v_s_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
v_s_1256_ = lean_ctor_get(v_x_1255_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v_x_1255_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v_x_1255_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_s_1256_);
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
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_s_1256_);
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
v___x_1264_ = ((lean_object*)(l_Lean_Json_getStr_x3f___closed__1));
return v___x_1264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getNat_x3f(lean_object* v_x_1268_){
_start:
{
if (lean_obj_tag(v_x_1268_) == 2)
{
lean_object* v_n_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1285_; 
v_n_1271_ = lean_ctor_get(v_x_1268_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_x_1268_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1273_ = v_x_1268_;
v_isShared_1274_ = v_isSharedCheck_1285_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_n_1271_);
lean_dec(v_x_1268_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1285_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v_mantissa_1275_; lean_object* v_exponent_1276_; lean_object* v_natZero_1277_; lean_object* v_intZero_1278_; uint8_t v_isNeg_1279_; 
v_mantissa_1275_ = lean_ctor_get(v_n_1271_, 0);
lean_inc(v_mantissa_1275_);
v_exponent_1276_ = lean_ctor_get(v_n_1271_, 1);
lean_inc(v_exponent_1276_);
lean_dec_ref(v_n_1271_);
v_natZero_1277_ = lean_unsigned_to_nat(0u);
v_intZero_1278_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v_isNeg_1279_ = lean_int_dec_lt(v_mantissa_1275_, v_intZero_1278_);
if (v_isNeg_1279_ == 0)
{
uint8_t v___x_1280_; 
v___x_1280_ = lean_nat_dec_eq(v_exponent_1276_, v_natZero_1277_);
lean_dec(v_exponent_1276_);
if (v___x_1280_ == 0)
{
lean_dec(v_mantissa_1275_);
lean_del_object(v___x_1273_);
goto v___jp_1269_;
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; 
v_a_1281_ = lean_nat_abs(v_mantissa_1275_);
lean_dec(v_mantissa_1275_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set_tag(v___x_1273_, 1);
lean_ctor_set(v___x_1273_, 0, v_a_1281_);
v___x_1283_ = v___x_1273_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
else
{
lean_dec(v_exponent_1276_);
lean_dec(v_mantissa_1275_);
lean_del_object(v___x_1273_);
goto v___jp_1269_;
}
}
}
else
{
lean_dec(v_x_1268_);
goto v___jp_1269_;
}
v___jp_1269_:
{
lean_object* v___x_1270_; 
v___x_1270_ = ((lean_object*)(l_Lean_Json_getNat_x3f___closed__1));
return v___x_1270_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getInt_x3f(lean_object* v_x_1289_){
_start:
{
if (lean_obj_tag(v_x_1289_) == 2)
{
lean_object* v_n_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1303_; 
v_n_1292_ = lean_ctor_get(v_x_1289_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v_x_1289_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1294_ = v_x_1289_;
v_isShared_1295_ = v_isSharedCheck_1303_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_n_1292_);
lean_dec(v_x_1289_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1303_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v_mantissa_1296_; lean_object* v_exponent_1297_; lean_object* v___x_1298_; uint8_t v___x_1299_; 
v_mantissa_1296_ = lean_ctor_get(v_n_1292_, 0);
lean_inc(v_mantissa_1296_);
v_exponent_1297_ = lean_ctor_get(v_n_1292_, 1);
lean_inc(v_exponent_1297_);
lean_dec_ref(v_n_1292_);
v___x_1298_ = lean_unsigned_to_nat(0u);
v___x_1299_ = lean_nat_dec_eq(v_exponent_1297_, v___x_1298_);
lean_dec(v_exponent_1297_);
if (v___x_1299_ == 0)
{
lean_dec(v_mantissa_1296_);
lean_del_object(v___x_1294_);
goto v___jp_1290_;
}
else
{
lean_object* v___x_1301_; 
if (v_isShared_1295_ == 0)
{
lean_ctor_set_tag(v___x_1294_, 1);
lean_ctor_set(v___x_1294_, 0, v_mantissa_1296_);
v___x_1301_ = v___x_1294_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_mantissa_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
else
{
lean_dec(v_x_1289_);
goto v___jp_1290_;
}
v___jp_1290_:
{
lean_object* v___x_1291_; 
v___x_1291_ = ((lean_object*)(l_Lean_Json_getInt_x3f___closed__1));
return v___x_1291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getBool_x3f(lean_object* v_x_1307_){
_start:
{
if (lean_obj_tag(v_x_1307_) == 1)
{
uint8_t v_b_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v_b_1308_ = lean_ctor_get_uint8(v_x_1307_, 0);
v___x_1309_ = lean_box(v_b_1308_);
v___x_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
return v___x_1310_;
}
else
{
lean_object* v___x_1311_; 
v___x_1311_ = ((lean_object*)(l_Lean_Json_getBool_x3f___closed__1));
return v___x_1311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getBool_x3f___boxed(lean_object* v_x_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_Json_getBool_x3f(v_x_1312_);
lean_dec(v_x_1312_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getNum_x3f(lean_object* v_x_1317_){
_start:
{
if (lean_obj_tag(v_x_1317_) == 2)
{
lean_object* v_n_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
v_n_1318_ = lean_ctor_get(v_x_1317_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v_x_1317_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v_x_1317_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_n_1318_);
lean_dec(v_x_1317_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
lean_ctor_set_tag(v___x_1320_, 1);
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_n_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
else
{
lean_object* v___x_1326_; 
lean_dec(v_x_1317_);
v___x_1326_ = ((lean_object*)(l_Lean_Json_getNum_x3f___closed__1));
return v___x_1326_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjVal_x3f(lean_object* v_x_1330_, lean_object* v_x_1331_){
_start:
{
if (lean_obj_tag(v_x_1330_) == 5)
{
lean_object* v_kvPairs_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1350_; 
v_kvPairs_1332_ = lean_ctor_get(v_x_1330_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v_x_1330_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1334_ = v_x_1330_;
v_isShared_1335_ = v_isSharedCheck_1350_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_kvPairs_1332_);
lean_dec(v_x_1330_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1350_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1336_; 
v___x_1336_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_kvPairs_1332_, v_x_1331_);
lean_dec(v_kvPairs_1332_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1337_ = ((lean_object*)(l_Lean_Json_getObjVal_x3f___closed__0));
v___x_1338_ = lean_string_append(v___x_1337_, v_x_1331_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set_tag(v___x_1334_, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1338_);
v___x_1340_ = v___x_1334_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
else
{
lean_object* v_val_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_del_object(v___x_1334_);
v_val_1342_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1336_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_val_1342_);
lean_dec(v___x_1336_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_val_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
}
else
{
lean_object* v___x_1351_; 
lean_dec(v_x_1330_);
v___x_1351_ = ((lean_object*)(l_Lean_Json_getObjVal_x3f___closed__1));
return v___x_1351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjVal_x3f___boxed(lean_object* v_x_1352_, lean_object* v_x_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Lean_Json_getObjVal_x3f(v_x_1352_, v_x_1353_);
lean_dec_ref(v_x_1353_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getArrVal_x3f(lean_object* v_x_1358_, lean_object* v_x_1359_){
_start:
{
if (lean_obj_tag(v_x_1358_) == 4)
{
lean_object* v_elems_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1376_; 
v_elems_1360_ = lean_ctor_get(v_x_1358_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v_x_1358_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1362_ = v_x_1358_;
v_isShared_1363_ = v_isSharedCheck_1376_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_elems_1360_);
lean_dec(v_x_1358_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1376_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1364_; uint8_t v___x_1365_; 
v___x_1364_ = lean_array_get_size(v_elems_1360_);
v___x_1365_ = lean_nat_dec_lt(v_x_1359_, v___x_1364_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1370_; 
lean_dec_ref(v_elems_1360_);
v___x_1366_ = ((lean_object*)(l_Lean_Json_getArrVal_x3f___closed__0));
v___x_1367_ = l_Nat_reprFast(v_x_1359_);
v___x_1368_ = lean_string_append(v___x_1366_, v___x_1367_);
lean_dec_ref(v___x_1367_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set_tag(v___x_1362_, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1368_);
v___x_1370_ = v___x_1362_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1368_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1374_; 
v___x_1372_ = lean_array_fget(v_elems_1360_, v_x_1359_);
lean_dec(v_x_1359_);
lean_dec_ref(v_elems_1360_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set_tag(v___x_1362_, 1);
lean_ctor_set(v___x_1362_, 0, v___x_1372_);
v___x_1374_ = v___x_1362_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
else
{
lean_object* v___x_1377_; 
lean_dec(v_x_1359_);
lean_dec(v_x_1358_);
v___x_1377_ = ((lean_object*)(l_Lean_Json_getArrVal_x3f___closed__1));
return v___x_1377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValD(lean_object* v_j_1378_, lean_object* v_k_1379_){
_start:
{
lean_object* v___x_1380_; 
v___x_1380_ = l_Lean_Json_getObjVal_x3f(v_j_1378_, v_k_1379_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v___x_1381_; 
lean_dec_ref_known(v___x_1380_, 1);
v___x_1381_ = lean_box(0);
return v___x_1381_;
}
else
{
lean_object* v_a_1382_; 
v_a_1382_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_a_1382_);
lean_dec_ref_known(v___x_1380_, 1);
return v_a_1382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValD___boxed(lean_object* v_j_1383_, lean_object* v_k_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Lean_Json_getObjValD(v_j_1383_, v_k_1384_);
lean_dec_ref(v_k_1384_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Json_setObjVal_x21_spec__1(lean_object* v_msg_1386_){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1387_ = lean_box(0);
v___x_1388_ = lean_panic_fn_borrowed(v___x_1387_, v_msg_1386_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(lean_object* v_msg_1389_){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = lean_box(1);
v___x_1391_ = lean_panic_fn_borrowed(v___x_1390_, v_msg_1389_);
return v___x_1391_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1395_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2));
v___x_1396_ = lean_unsigned_to_nat(35u);
v___x_1397_ = lean_unsigned_to_nat(182u);
v___x_1398_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1));
v___x_1399_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1400_ = l_mkPanicMessageWithDecl(v___x_1399_, v___x_1398_, v___x_1397_, v___x_1396_, v___x_1395_);
return v___x_1400_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1401_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2));
v___x_1402_ = lean_unsigned_to_nat(21u);
v___x_1403_ = lean_unsigned_to_nat(183u);
v___x_1404_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1));
v___x_1405_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1406_ = l_mkPanicMessageWithDecl(v___x_1405_, v___x_1404_, v___x_1403_, v___x_1402_, v___x_1401_);
return v___x_1406_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1409_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6));
v___x_1410_ = lean_unsigned_to_nat(35u);
v___x_1411_ = lean_unsigned_to_nat(276u);
v___x_1412_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5));
v___x_1413_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1414_ = l_mkPanicMessageWithDecl(v___x_1413_, v___x_1412_, v___x_1411_, v___x_1410_, v___x_1409_);
return v___x_1414_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1415_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6));
v___x_1416_ = lean_unsigned_to_nat(21u);
v___x_1417_ = lean_unsigned_to_nat(277u);
v___x_1418_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5));
v___x_1419_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1420_ = l_mkPanicMessageWithDecl(v___x_1419_, v___x_1418_, v___x_1417_, v___x_1416_, v___x_1415_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(lean_object* v_k_1421_, lean_object* v_v_1422_, lean_object* v_t_1423_){
_start:
{
if (lean_obj_tag(v_t_1423_) == 0)
{
lean_object* v_size_1424_; lean_object* v_k_1425_; lean_object* v_v_1426_; lean_object* v_l_1427_; lean_object* v_r_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1784_; 
v_size_1424_ = lean_ctor_get(v_t_1423_, 0);
v_k_1425_ = lean_ctor_get(v_t_1423_, 1);
v_v_1426_ = lean_ctor_get(v_t_1423_, 2);
v_l_1427_ = lean_ctor_get(v_t_1423_, 3);
v_r_1428_ = lean_ctor_get(v_t_1423_, 4);
v_isSharedCheck_1784_ = !lean_is_exclusive(v_t_1423_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1430_ = v_t_1423_;
v_isShared_1431_ = v_isSharedCheck_1784_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_r_1428_);
lean_inc(v_l_1427_);
lean_inc(v_v_1426_);
lean_inc(v_k_1425_);
lean_inc(v_size_1424_);
lean_dec(v_t_1423_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1784_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
uint8_t v___x_1432_; 
v___x_1432_ = lean_string_compare(v_k_1421_, v_k_1425_);
switch(v___x_1432_)
{
case 0:
{
lean_object* v___x_1433_; 
lean_dec(v_size_1424_);
v___x_1433_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1421_, v_v_1422_, v_l_1427_);
if (lean_obj_tag(v_r_1428_) == 0)
{
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_size_1434_; lean_object* v_size_1435_; lean_object* v_k_1436_; lean_object* v_v_1437_; lean_object* v_l_1438_; lean_object* v_r_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; 
v_size_1434_ = lean_ctor_get(v_r_1428_, 0);
v_size_1435_ = lean_ctor_get(v___x_1433_, 0);
v_k_1436_ = lean_ctor_get(v___x_1433_, 1);
v_v_1437_ = lean_ctor_get(v___x_1433_, 2);
v_l_1438_ = lean_ctor_get(v___x_1433_, 3);
v_r_1439_ = lean_ctor_get(v___x_1433_, 4);
lean_inc(v_r_1439_);
v___x_1440_ = lean_unsigned_to_nat(3u);
v___x_1441_ = lean_nat_mul(v___x_1440_, v_size_1434_);
v___x_1442_ = lean_nat_dec_lt(v___x_1441_, v_size_1435_);
lean_dec(v___x_1441_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1447_; 
lean_dec(v_r_1439_);
v___x_1443_ = lean_unsigned_to_nat(1u);
v___x_1444_ = lean_nat_add(v___x_1443_, v_size_1435_);
v___x_1445_ = lean_nat_add(v___x_1444_, v_size_1434_);
lean_dec(v___x_1444_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 3, v___x_1433_);
lean_ctor_set(v___x_1430_, 0, v___x_1445_);
v___x_1447_ = v___x_1430_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1445_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_k_1425_);
lean_ctor_set(v_reuseFailAlloc_1448_, 2, v_v_1426_);
lean_ctor_set(v_reuseFailAlloc_1448_, 3, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1448_, 4, v_r_1428_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
else
{
lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1520_; 
lean_inc(v_l_1438_);
lean_inc(v_v_1437_);
lean_inc(v_k_1436_);
lean_inc(v_size_1435_);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1520_ == 0)
{
lean_object* v_unused_1521_; lean_object* v_unused_1522_; lean_object* v_unused_1523_; lean_object* v_unused_1524_; lean_object* v_unused_1525_; 
v_unused_1521_ = lean_ctor_get(v___x_1433_, 4);
lean_dec(v_unused_1521_);
v_unused_1522_ = lean_ctor_get(v___x_1433_, 3);
lean_dec(v_unused_1522_);
v_unused_1523_ = lean_ctor_get(v___x_1433_, 2);
lean_dec(v_unused_1523_);
v_unused_1524_ = lean_ctor_get(v___x_1433_, 1);
lean_dec(v_unused_1524_);
v_unused_1525_ = lean_ctor_get(v___x_1433_, 0);
lean_dec(v_unused_1525_);
v___x_1450_ = v___x_1433_;
v_isShared_1451_ = v_isSharedCheck_1520_;
goto v_resetjp_1449_;
}
else
{
lean_dec(v___x_1433_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1520_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
if (lean_obj_tag(v_l_1438_) == 0)
{
if (lean_obj_tag(v_r_1439_) == 0)
{
lean_object* v_size_1452_; lean_object* v_size_1453_; lean_object* v_k_1454_; lean_object* v_v_1455_; lean_object* v_l_1456_; lean_object* v_r_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; 
v_size_1452_ = lean_ctor_get(v_l_1438_, 0);
v_size_1453_ = lean_ctor_get(v_r_1439_, 0);
v_k_1454_ = lean_ctor_get(v_r_1439_, 1);
v_v_1455_ = lean_ctor_get(v_r_1439_, 2);
v_l_1456_ = lean_ctor_get(v_r_1439_, 3);
v_r_1457_ = lean_ctor_get(v_r_1439_, 4);
v___x_1458_ = lean_unsigned_to_nat(2u);
v___x_1459_ = lean_nat_mul(v___x_1458_, v_size_1452_);
v___x_1460_ = lean_nat_dec_lt(v_size_1453_, v___x_1459_);
lean_dec(v___x_1459_);
if (v___x_1460_ == 0)
{
lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1490_; 
lean_inc(v_r_1457_);
lean_inc(v_l_1456_);
lean_inc(v_v_1455_);
lean_inc(v_k_1454_);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_r_1439_);
if (v_isSharedCheck_1490_ == 0)
{
lean_object* v_unused_1491_; lean_object* v_unused_1492_; lean_object* v_unused_1493_; lean_object* v_unused_1494_; lean_object* v_unused_1495_; 
v_unused_1491_ = lean_ctor_get(v_r_1439_, 4);
lean_dec(v_unused_1491_);
v_unused_1492_ = lean_ctor_get(v_r_1439_, 3);
lean_dec(v_unused_1492_);
v_unused_1493_ = lean_ctor_get(v_r_1439_, 2);
lean_dec(v_unused_1493_);
v_unused_1494_ = lean_ctor_get(v_r_1439_, 1);
lean_dec(v_unused_1494_);
v_unused_1495_ = lean_ctor_get(v_r_1439_, 0);
lean_dec(v_unused_1495_);
v___x_1462_ = v_r_1439_;
v_isShared_1463_ = v_isSharedCheck_1490_;
goto v_resetjp_1461_;
}
else
{
lean_dec(v_r_1439_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1490_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___x_1478_; lean_object* v___y_1480_; 
v___x_1464_ = lean_unsigned_to_nat(1u);
v___x_1465_ = lean_nat_add(v___x_1464_, v_size_1435_);
lean_dec(v_size_1435_);
v___x_1466_ = lean_nat_add(v___x_1465_, v_size_1434_);
lean_dec(v___x_1465_);
v___x_1478_ = lean_nat_add(v___x_1464_, v_size_1452_);
if (lean_obj_tag(v_l_1456_) == 0)
{
lean_object* v_size_1488_; 
v_size_1488_ = lean_ctor_get(v_l_1456_, 0);
lean_inc(v_size_1488_);
v___y_1480_ = v_size_1488_;
goto v___jp_1479_;
}
else
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_unsigned_to_nat(0u);
v___y_1480_ = v___x_1489_;
goto v___jp_1479_;
}
v___jp_1467_:
{
lean_object* v___x_1471_; lean_object* v___x_1473_; 
v___x_1471_ = lean_nat_add(v___y_1469_, v___y_1470_);
lean_dec(v___y_1470_);
lean_dec(v___y_1469_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 4, v_r_1428_);
lean_ctor_set(v___x_1462_, 3, v_r_1457_);
lean_ctor_set(v___x_1462_, 2, v_v_1426_);
lean_ctor_set(v___x_1462_, 1, v_k_1425_);
lean_ctor_set(v___x_1462_, 0, v___x_1471_);
v___x_1473_ = v___x_1462_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1471_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v_k_1425_);
lean_ctor_set(v_reuseFailAlloc_1477_, 2, v_v_1426_);
lean_ctor_set(v_reuseFailAlloc_1477_, 3, v_r_1457_);
lean_ctor_set(v_reuseFailAlloc_1477_, 4, v_r_1428_);
v___x_1473_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
lean_object* v___x_1475_; 
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 4, v___x_1473_);
lean_ctor_set(v___x_1450_, 3, v___y_1468_);
lean_ctor_set(v___x_1450_, 2, v_v_1455_);
lean_ctor_set(v___x_1450_, 1, v_k_1454_);
lean_ctor_set(v___x_1450_, 0, v___x_1466_);
v___x_1475_ = v___x_1450_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1466_);
lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_k_1454_);
lean_ctor_set(v_reuseFailAlloc_1476_, 2, v_v_1455_);
lean_ctor_set(v_reuseFailAlloc_1476_, 3, v___y_1468_);
lean_ctor_set(v_reuseFailAlloc_1476_, 4, v___x_1473_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
v___jp_1479_:
{
lean_object* v___x_1481_; lean_object* v___x_1483_; 
v___x_1481_ = lean_nat_add(v___x_1478_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec(v___x_1478_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 4, v_l_1456_);
lean_ctor_set(v___x_1430_, 3, v_l_1438_);
lean_ctor_set(v___x_1430_, 2, v_v_1437_);
lean_ctor_set(v___x_1430_, 1, v_k_1436_);
lean_ctor_set(v___x_1430_, 0, v___x_1481_);
v___x_1483_ = v___x_1430_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1481_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v_k_1436_);
lean_ctor_set(v_reuseFailAlloc_1487_, 2, v_v_1437_);
lean_ctor_set(v_reuseFailAlloc_1487_, 3, v_l_1438_);
lean_ctor_set(v_reuseFailAlloc_1487_, 4, v_l_1456_);
v___x_1483_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
lean_object* v___x_1484_; 
v___x_1484_ = lean_nat_add(v___x_1464_, v_size_1434_);
if (lean_obj_tag(v_r_1457_) == 0)
{
lean_object* v_size_1485_; 
v_size_1485_ = lean_ctor_get(v_r_1457_, 0);
lean_inc(v_size_1485_);
v___y_1468_ = v___x_1483_;
v___y_1469_ = v___x_1484_;
v___y_1470_ = v_size_1485_;
goto v___jp_1467_;
}
else
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_unsigned_to_nat(0u);
v___y_1468_ = v___x_1483_;
v___y_1469_ = v___x_1484_;
v___y_1470_ = v___x_1486_;
goto v___jp_1467_;
}
}
}
}
}
else
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1502_; 
lean_del_object(v___x_1430_);
v___x_1496_ = lean_unsigned_to_nat(1u);
v___x_1497_ = lean_nat_add(v___x_1496_, v_size_1435_);
lean_dec(v_size_1435_);
v___x_1498_ = lean_nat_add(v___x_1497_, v_size_1434_);
lean_dec(v___x_1497_);
v___x_1499_ = lean_nat_add(v___x_1496_, v_size_1434_);
v___x_1500_ = lean_nat_add(v___x_1499_, v_size_1453_);
lean_dec(v___x_1499_);
lean_inc_ref(v_r_1428_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 4, v_r_1428_);
lean_ctor_set(v___x_1450_, 3, v_r_1439_);
lean_ctor_set(v___x_1450_, 2, v_v_1426_);
lean_ctor_set(v___x_1450_, 1, v_k_1425_);
lean_ctor_set(v___x_1450_, 0, v___x_1500_);
v___x_1502_ = v___x_1450_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1500_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v_k_1425_);
lean_ctor_set(v_reuseFailAlloc_1515_, 2, v_v_1426_);
lean_ctor_set(v_reuseFailAlloc_1515_, 3, v_r_1439_);
lean_ctor_set(v_reuseFailAlloc_1515_, 4, v_r_1428_);
v___x_1502_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1509_; 
v_isSharedCheck_1509_ = !lean_is_exclusive(v_r_1428_);
if (v_isSharedCheck_1509_ == 0)
{
lean_object* v_unused_1510_; lean_object* v_unused_1511_; lean_object* v_unused_1512_; lean_object* v_unused_1513_; lean_object* v_unused_1514_; 
v_unused_1510_ = lean_ctor_get(v_r_1428_, 4);
lean_dec(v_unused_1510_);
v_unused_1511_ = lean_ctor_get(v_r_1428_, 3);
lean_dec(v_unused_1511_);
v_unused_1512_ = lean_ctor_get(v_r_1428_, 2);
lean_dec(v_unused_1512_);
v_unused_1513_ = lean_ctor_get(v_r_1428_, 1);
lean_dec(v_unused_1513_);
v_unused_1514_ = lean_ctor_get(v_r_1428_, 0);
lean_dec(v_unused_1514_);
v___x_1504_ = v_r_1428_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_dec(v_r_1428_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 4, v___x_1502_);
lean_ctor_set(v___x_1504_, 3, v_l_1438_);
lean_ctor_set(v___x_1504_, 2, v_v_1437_);
lean_ctor_set(v___x_1504_, 1, v_k_1436_);
lean_ctor_set(v___x_1504_, 0, v___x_1498_);
v___x_1507_ = v___x_1504_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_k_1436_);
lean_ctor_set(v_reuseFailAlloc_1508_, 2, v_v_1437_);
lean_ctor_set(v_reuseFailAlloc_1508_, 3, v_l_1438_);
lean_ctor_set(v_reuseFailAlloc_1508_, 4, v___x_1502_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
}
else
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
lean_dec_ref_known(v_l_1438_, 5);
lean_del_object(v___x_1450_);
lean_dec(v_v_1437_);
lean_dec(v_k_1436_);
lean_dec(v_size_1435_);
lean_dec_ref_known(v_r_1428_, 5);
lean_del_object(v___x_1430_);
lean_dec(v_v_1426_);
lean_dec(v_k_1425_);
v___x_1516_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3);
v___x_1517_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1516_);
return v___x_1517_;
}
}
else
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
lean_del_object(v___x_1450_);
lean_dec(v_r_1439_);
lean_dec(v_v_1437_);
lean_dec(v_k_1436_);
lean_dec(v_size_1435_);
lean_dec_ref_known(v_r_1428_, 5);
lean_del_object(v___x_1430_);
lean_dec(v_v_1426_);
lean_dec(v_k_1425_);
v___x_1518_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4);
v___x_1519_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1518_);
return v___x_1519_;
}
}
}
}
else
{
lean_object* v_size_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1530_; 
v_size_1526_ = lean_ctor_get(v_r_1428_, 0);
v___x_1527_ = lean_unsigned_to_nat(1u);
v___x_1528_ = lean_nat_add(v___x_1527_, v_size_1526_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 3, v___x_1433_);
lean_ctor_set(v___x_1430_, 0, v___x_1528_);
v___x_1530_ = v___x_1430_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1528_);
lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_k_1425_);
lean_ctor_set(v_reuseFailAlloc_1531_, 2, v_v_1426_);
lean_ctor_set(v_reuseFailAlloc_1531_, 3, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1531_, 4, v_r_1428_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
else
{
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_l_1532_; 
v_l_1532_ = lean_ctor_get(v___x_1433_, 3);
if (lean_obj_tag(v_l_1532_) == 0)
{
lean_object* v_r_1533_; 
lean_inc_ref(v_l_1532_);
v_r_1533_ = lean_ctor_get(v___x_1433_, 4);
lean_inc(v_r_1533_);
if (lean_obj_tag(v_r_1533_) == 0)
{
lean_object* v_size_1534_; lean_object* v_k_1535_; lean_object* v_v_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1550_; 
v_size_1534_ = lean_ctor_get(v___x_1433_, 0);
v_k_1535_ = lean_ctor_get(v___x_1433_, 1);
v_v_1536_ = lean_ctor_get(v___x_1433_, 2);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; lean_object* v_unused_1552_; 
v_unused_1551_ = lean_ctor_get(v___x_1433_, 4);
lean_dec(v_unused_1551_);
v_unused_1552_ = lean_ctor_get(v___x_1433_, 3);
lean_dec(v_unused_1552_);
v___x_1538_ = v___x_1433_;
v_isShared_1539_ = v_isSharedCheck_1550_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_v_1536_);
lean_inc(v_k_1535_);
lean_inc(v_size_1534_);
lean_dec(v___x_1433_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1550_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v_size_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1545_; 
v_size_1540_ = lean_ctor_get(v_r_1533_, 0);
v___x_1541_ = lean_unsigned_to_nat(1u);
v___x_1542_ = lean_nat_add(v___x_1541_, v_size_1534_);
lean_dec(v_size_1534_);
v___x_1543_ = lean_nat_add(v___x_1541_, v_size_1540_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 4, v_r_1428_);
lean_ctor_set(v___x_1538_, 3, v_r_1533_);
lean_ctor_set(v___x_1538_, 2, v_v_1426_);
lean_ctor_set(v___x_1538_, 1, v_k_1425_);
lean_ctor_set(v___x_1538_, 0, v___x_1543_);
v___x_1545_ = v___x_1538_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1543_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_k_1425_);
lean_ctor_set(v_reuseFailAlloc_1549_, 2, v_v_1426_);
lean_ctor_set(v_reuseFailAlloc_1549_, 3, v_r_1533_);
lean_ctor_set(v_reuseFailAlloc_1549_, 4, v_r_1428_);
v___x_1545_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
lean_object* v___x_1547_; 
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 4, v___x_1545_);
lean_ctor_set(v___x_1430_, 3, v_l_1532_);
lean_ctor_set(v___x_1430_, 2, v_v_1536_);
lean_ctor_set(v___x_1430_, 1, v_k_1535_);
lean_ctor_set(v___x_1430_, 0, v___x_1542_);
v___x_1547_ = v___x_1430_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1542_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_k_1535_);
lean_ctor_set(v_reuseFailAlloc_1548_, 2, v_v_1536_);
lean_ctor_set(v_reuseFailAlloc_1548_, 3, v_l_1532_);
lean_ctor_set(v_reuseFailAlloc_1548_, 4, v___x_1545_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
}
else
{
lean_object* v_k_1553_; lean_object* v_v_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1566_; 
v_k_1553_ = lean_ctor_get(v___x_1433_, 1);
v_v_1554_ = lean_ctor_get(v___x_1433_, 2);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1566_ == 0)
{
lean_object* v_unused_1567_; lean_object* v_unused_1568_; lean_object* v_unused_1569_; 
v_unused_1567_ = lean_ctor_get(v___x_1433_, 4);
lean_dec(v_unused_1567_);
v_unused_1568_ = lean_ctor_get(v___x_1433_, 3);
lean_dec(v_unused_1568_);
v_unused_1569_ = lean_ctor_get(v___x_1433_, 0);
lean_dec(v_unused_1569_);
v___x_1556_ = v___x_1433_;
v_isShared_1557_ = v_isSharedCheck_1566_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_v_1554_);
lean_inc(v_k_1553_);
lean_dec(v___x_1433_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1566_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1561_; 
v___x_1558_ = lean_unsigned_to_nat(3u);
v___x_1559_ = lean_unsigned_to_nat(1u);
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 3, v_r_1533_);
lean_ctor_set(v___x_1556_, 2, v_v_1426_);
lean_ctor_set(v___x_1556_, 1, v_k_1425_);
lean_ctor_set(v___x_1556_, 0, v___x_1559_);
v___x_1561_ = v___x_1556_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1559_);
lean_ctor_set(v_reuseFailAlloc_1565_, 1, v_k_1425_);
lean_ctor_set(v_reuseFailAlloc_1565_, 2, v_v_1426_);
lean_ctor_set(v_reuseFailAlloc_1565_, 3, v_r_1533_);
lean_ctor_set(v_reuseFailAlloc_1565_, 4, v_r_1533_);
v___x_1561_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
lean_object* v___x_1563_; 
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 4, v___x_1561_);
lean_ctor_set(v___x_1430_, 3, v_l_1532_);
lean_ctor_set(v___x_1430_, 2, v_v_1554_);
lean_ctor_set(v___x_1430_, 1, v_k_1553_);
lean_ctor_set(v___x_1430_, 0, v___x_1558_);
v___x_1563_ = v___x_1430_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1558_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v_k_1553_);
lean_ctor_set(v_reuseFailAlloc_1564_, 2, v_v_1554_);
lean_ctor_set(v_reuseFailAlloc_1564_, 3, v_l_1532_);
lean_ctor_set(v_reuseFailAlloc_1564_, 4, v___x_1561_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
}
else
{
lean_object* v_r_1570_; 
v_r_1570_ = lean_ctor_get(v___x_1433_, 4);
lean_inc(v_r_1570_);
if (lean_obj_tag(v_r_1570_) == 0)
{
lean_object* v_k_1571_; lean_object* v_v_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1596_; 
lean_inc(v_l_1532_);
v_k_1571_ = lean_ctor_get(v___x_1433_, 1);
v_v_1572_ = lean_ctor_get(v___x_1433_, 2);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1596_ == 0)
{
lean_object* v_unused_1597_; lean_object* v_unused_1598_; lean_object* v_unused_1599_; 
v_unused_1597_ = lean_ctor_get(v___x_1433_, 4);
lean_dec(v_unused_1597_);
v_unused_1598_ = lean_ctor_get(v___x_1433_, 3);
lean_dec(v_unused_1598_);
v_unused_1599_ = lean_ctor_get(v___x_1433_, 0);
lean_dec(v_unused_1599_);
v___x_1574_ = v___x_1433_;
v_isShared_1575_ = v_isSharedCheck_1596_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_v_1572_);
lean_inc(v_k_1571_);
lean_dec(v___x_1433_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1596_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v_k_1576_; lean_object* v_v_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1592_; 
v_k_1576_ = lean_ctor_get(v_r_1570_, 1);
v_v_1577_ = lean_ctor_get(v_r_1570_, 2);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_r_1570_);
if (v_isSharedCheck_1592_ == 0)
{
lean_object* v_unused_1593_; lean_object* v_unused_1594_; lean_object* v_unused_1595_; 
v_unused_1593_ = lean_ctor_get(v_r_1570_, 4);
lean_dec(v_unused_1593_);
v_unused_1594_ = lean_ctor_get(v_r_1570_, 3);
lean_dec(v_unused_1594_);
v_unused_1595_ = lean_ctor_get(v_r_1570_, 0);
lean_dec(v_unused_1595_);
v___x_1579_ = v_r_1570_;
v_isShared_1580_ = v_isSharedCheck_1592_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_v_1577_);
lean_inc(v_k_1576_);
lean_dec(v_r_1570_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1592_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1584_; 
v___x_1581_ = lean_unsigned_to_nat(3u);
v___x_1582_ = lean_unsigned_to_nat(1u);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 4, v_l_1532_);
lean_ctor_set(v___x_1579_, 3, v_l_1532_);
lean_ctor_set(v___x_1579_, 2, v_v_1572_);
lean_ctor_set(v___x_1579_, 1, v_k_1571_);
lean_ctor_set(v___x_1579_, 0, v___x_1582_);
v___x_1584_ = v___x_1579_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1582_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v_k_1571_);
lean_ctor_set(v_reuseFailAlloc_1591_, 2, v_v_1572_);
lean_ctor_set(v_reuseFailAlloc_1591_, 3, v_l_1532_);
lean_ctor_set(v_reuseFailAlloc_1591_, 4, v_l_1532_);
v___x_1584_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
lean_object* v___x_1586_; 
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 4, v_l_1532_);
lean_ctor_set(v___x_1574_, 2, v_v_1426_);
lean_ctor_set(v___x_1574_, 1, v_k_1425_);
lean_ctor_set(v___x_1574_, 0, v___x_1582_);
v___x_1586_ = v___x_1574_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1582_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_k_1425_);
lean_ctor_set(v_reuseFailAlloc_1590_, 2, v_v_1426_);
lean_ctor_set(v_reuseFailAlloc_1590_, 3, v_l_1532_);
lean_ctor_set(v_reuseFailAlloc_1590_, 4, v_l_1532_);
v___x_1586_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
lean_object* v___x_1588_; 
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 4, v___x_1586_);
lean_ctor_set(v___x_1430_, 3, v___x_1584_);
lean_ctor_set(v___x_1430_, 2, v_v_1577_);
lean_ctor_set(v___x_1430_, 1, v_k_1576_);
lean_ctor_set(v___x_1430_, 0, v___x_1581_);
v___x_1588_ = v___x_1430_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_k_1576_);
lean_ctor_set(v_reuseFailAlloc_1589_, 2, v_v_1577_);
lean_ctor_set(v_reuseFailAlloc_1589_, 3, v___x_1584_);
lean_ctor_set(v_reuseFailAlloc_1589_, 4, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
}
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1602_; 
v___x_1600_ = lean_unsigned_to_nat(2u);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 4, v_r_1570_);
lean_ctor_set(v___x_1430_, 3, v___x_1433_);
lean_ctor_set(v___x_1430_, 0, v___x_1600_);
v___x_1602_ = v___x_1430_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1600_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_k_1425_);
lean_ctor_set(v_reuseFailAlloc_1603_, 2, v_v_1426_);
lean_ctor_set(v_reuseFailAlloc_1603_, 3, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1603_, 4, v_r_1570_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
else
{
lean_object* v___x_1604_; lean_object* v___x_1606_; 
v___x_1604_ = lean_unsigned_to_nat(1u);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 4, v___x_1433_);
lean_ctor_set(v___x_1430_, 3, v___x_1433_);
lean_ctor_set(v___x_1430_, 0, v___x_1604_);
v___x_1606_ = v___x_1430_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1604_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_k_1425_);
lean_ctor_set(v_reuseFailAlloc_1607_, 2, v_v_1426_);
lean_ctor_set(v_reuseFailAlloc_1607_, 3, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1607_, 4, v___x_1433_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
case 1:
{
lean_object* v___x_1609_; 
lean_dec(v_v_1426_);
lean_dec(v_k_1425_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 2, v_v_1422_);
lean_ctor_set(v___x_1430_, 1, v_k_1421_);
v___x_1609_ = v___x_1430_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_size_1424_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_k_1421_);
lean_ctor_set(v_reuseFailAlloc_1610_, 2, v_v_1422_);
lean_ctor_set(v_reuseFailAlloc_1610_, 3, v_l_1427_);
lean_ctor_set(v_reuseFailAlloc_1610_, 4, v_r_1428_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
default: 
{
lean_object* v___x_1611_; 
lean_dec(v_size_1424_);
v___x_1611_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1421_, v_v_1422_, v_r_1428_);
if (lean_obj_tag(v_l_1427_) == 0)
{
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_size_1612_; lean_object* v_size_1613_; lean_object* v_k_1614_; lean_object* v_v_1615_; lean_object* v_l_1616_; lean_object* v_r_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; 
v_size_1612_ = lean_ctor_get(v_l_1427_, 0);
v_size_1613_ = lean_ctor_get(v___x_1611_, 0);
v_k_1614_ = lean_ctor_get(v___x_1611_, 1);
v_v_1615_ = lean_ctor_get(v___x_1611_, 2);
v_l_1616_ = lean_ctor_get(v___x_1611_, 3);
lean_inc(v_l_1616_);
v_r_1617_ = lean_ctor_get(v___x_1611_, 4);
v___x_1618_ = lean_unsigned_to_nat(3u);
v___x_1619_ = lean_nat_mul(v___x_1618_, v_size_1612_);
v___x_1620_ = lean_nat_dec_lt(v___x_1619_, v_size_1613_);
lean_dec(v___x_1619_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1625_; 
lean_dec(v_l_1616_);
v___x_1621_ = lean_unsigned_to_nat(1u);
v___x_1622_ = lean_nat_add(v___x_1621_, v_size_1612_);
v___x_1623_ = lean_nat_add(v___x_1622_, v_size_1613_);
lean_dec(v___x_1622_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 4, v___x_1611_);
lean_ctor_set(v___x_1430_, 0, v___x_1623_);
v___x_1625_ = v___x_1430_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1623_);
lean_ctor_set(v_reuseFailAlloc_1626_, 1, v_k_1425_);
lean_ctor_set(v_reuseFailAlloc_1626_, 2, v_v_1426_);
lean_ctor_set(v_reuseFailAlloc_1626_, 3, v_l_1427_);
lean_ctor_set(v_reuseFailAlloc_1626_, 4, v___x_1611_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
else
{
lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1696_; 
lean_inc(v_r_1617_);
lean_inc(v_v_1615_);
lean_inc(v_k_1614_);
lean_inc(v_size_1613_);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1696_ == 0)
{
lean_object* v_unused_1697_; lean_object* v_unused_1698_; lean_object* v_unused_1699_; lean_object* v_unused_1700_; lean_object* v_unused_1701_; 
v_unused_1697_ = lean_ctor_get(v___x_1611_, 4);
lean_dec(v_unused_1697_);
v_unused_1698_ = lean_ctor_get(v___x_1611_, 3);
lean_dec(v_unused_1698_);
v_unused_1699_ = lean_ctor_get(v___x_1611_, 2);
lean_dec(v_unused_1699_);
v_unused_1700_ = lean_ctor_get(v___x_1611_, 1);
lean_dec(v_unused_1700_);
v_unused_1701_ = lean_ctor_get(v___x_1611_, 0);
lean_dec(v_unused_1701_);
v___x_1628_ = v___x_1611_;
v_isShared_1629_ = v_isSharedCheck_1696_;
goto v_resetjp_1627_;
}
else
{
lean_dec(v___x_1611_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1696_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
if (lean_obj_tag(v_l_1616_) == 0)
{
if (lean_obj_tag(v_r_1617_) == 0)
{
lean_object* v_size_1630_; lean_object* v_k_1631_; lean_object* v_v_1632_; lean_object* v_l_1633_; lean_object* v_r_1634_; lean_object* v_size_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; uint8_t v___x_1638_; 
v_size_1630_ = lean_ctor_get(v_l_1616_, 0);
v_k_1631_ = lean_ctor_get(v_l_1616_, 1);
v_v_1632_ = lean_ctor_get(v_l_1616_, 2);
v_l_1633_ = lean_ctor_get(v_l_1616_, 3);
v_r_1634_ = lean_ctor_get(v_l_1616_, 4);
v_size_1635_ = lean_ctor_get(v_r_1617_, 0);
v___x_1636_ = lean_unsigned_to_nat(2u);
v___x_1637_ = lean_nat_mul(v___x_1636_, v_size_1635_);
v___x_1638_ = lean_nat_dec_lt(v_size_1630_, v___x_1637_);
lean_dec(v___x_1637_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1667_; 
lean_inc(v_r_1634_);
lean_inc(v_l_1633_);
lean_inc(v_v_1632_);
lean_inc(v_k_1631_);
v_isSharedCheck_1667_ = !lean_is_exclusive(v_l_1616_);
if (v_isSharedCheck_1667_ == 0)
{
lean_object* v_unused_1668_; lean_object* v_unused_1669_; lean_object* v_unused_1670_; lean_object* v_unused_1671_; lean_object* v_unused_1672_; 
v_unused_1668_ = lean_ctor_get(v_l_1616_, 4);
lean_dec(v_unused_1668_);
v_unused_1669_ = lean_ctor_get(v_l_1616_, 3);
lean_dec(v_unused_1669_);
v_unused_1670_ = lean_ctor_get(v_l_1616_, 2);
lean_dec(v_unused_1670_);
v_unused_1671_ = lean_ctor_get(v_l_1616_, 1);
lean_dec(v_unused_1671_);
v_unused_1672_ = lean_ctor_get(v_l_1616_, 0);
lean_dec(v_unused_1672_);
v___x_1640_ = v_l_1616_;
v_isShared_1641_ = v_isSharedCheck_1667_;
goto v_resetjp_1639_;
}
else
{
lean_dec(v_l_1616_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1667_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1657_; 
v___x_1642_ = lean_unsigned_to_nat(1u);
v___x_1643_ = lean_nat_add(v___x_1642_, v_size_1612_);
v___x_1644_ = lean_nat_add(v___x_1643_, v_size_1613_);
lean_dec(v_size_1613_);
if (lean_obj_tag(v_l_1633_) == 0)
{
lean_object* v_size_1665_; 
v_size_1665_ = lean_ctor_get(v_l_1633_, 0);
lean_inc(v_size_1665_);
v___y_1657_ = v_size_1665_;
goto v___jp_1656_;
}
else
{
lean_object* v___x_1666_; 
v___x_1666_ = lean_unsigned_to_nat(0u);
v___y_1657_ = v___x_1666_;
goto v___jp_1656_;
}
v___jp_1645_:
{
lean_object* v___x_1649_; lean_object* v___x_1651_; 
v___x_1649_ = lean_nat_add(v___y_1646_, v___y_1648_);
lean_dec(v___y_1648_);
lean_dec(v___y_1646_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 4, v_r_1617_);
lean_ctor_set(v___x_1640_, 3, v_r_1634_);
lean_ctor_set(v___x_1640_, 2, v_v_1615_);
lean_ctor_set(v___x_1640_, 1, v_k_1614_);
lean_ctor_set(v___x_1640_, 0, v___x_1649_);
v___x_1651_ = v___x_1640_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1649_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_k_1614_);
lean_ctor_set(v_reuseFailAlloc_1655_, 2, v_v_1615_);
lean_ctor_set(v_reuseFailAlloc_1655_, 3, v_r_1634_);
lean_ctor_set(v_reuseFailAlloc_1655_, 4, v_r_1617_);
v___x_1651_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
lean_object* v___x_1653_; 
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 4, v___x_1651_);
lean_ctor_set(v___x_1628_, 3, v___y_1647_);
lean_ctor_set(v___x_1628_, 2, v_v_1632_);
lean_ctor_set(v___x_1628_, 1, v_k_1631_);
lean_ctor_set(v___x_1628_, 0, v___x_1644_);
v___x_1653_ = v___x_1628_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1644_);
lean_ctor_set(v_reuseFailAlloc_1654_, 1, v_k_1631_);
lean_ctor_set(v_reuseFailAlloc_1654_, 2, v_v_1632_);
lean_ctor_set(v_reuseFailAlloc_1654_, 3, v___y_1647_);
lean_ctor_set(v_reuseFailAlloc_1654_, 4, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
v___jp_1656_:
{
lean_object* v___x_1658_; lean_object* v___x_1660_; 
v___x_1658_ = lean_nat_add(v___x_1643_, v___y_1657_);
lean_dec(v___y_1657_);
lean_dec(v___x_1643_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 4, v_l_1633_);
lean_ctor_set(v___x_1430_, 0, v___x_1658_);
v___x_1660_ = v___x_1430_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1658_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v_k_1425_);
lean_ctor_set(v_reuseFailAlloc_1664_, 2, v_v_1426_);
lean_ctor_set(v_reuseFailAlloc_1664_, 3, v_l_1427_);
lean_ctor_set(v_reuseFailAlloc_1664_, 4, v_l_1633_);
v___x_1660_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
lean_object* v___x_1661_; 
v___x_1661_ = lean_nat_add(v___x_1642_, v_size_1635_);
if (lean_obj_tag(v_r_1634_) == 0)
{
lean_object* v_size_1662_; 
v_size_1662_ = lean_ctor_get(v_r_1634_, 0);
lean_inc(v_size_1662_);
v___y_1646_ = v___x_1661_;
v___y_1647_ = v___x_1660_;
v___y_1648_ = v_size_1662_;
goto v___jp_1645_;
}
else
{
lean_object* v___x_1663_; 
v___x_1663_ = lean_unsigned_to_nat(0u);
v___y_1646_ = v___x_1661_;
v___y_1647_ = v___x_1660_;
v___y_1648_ = v___x_1663_;
goto v___jp_1645_;
}
}
}
}
}
else
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1678_; 
lean_del_object(v___x_1430_);
v___x_1673_ = lean_unsigned_to_nat(1u);
v___x_1674_ = lean_nat_add(v___x_1673_, v_size_1612_);
v___x_1675_ = lean_nat_add(v___x_1674_, v_size_1613_);
lean_dec(v_size_1613_);
v___x_1676_ = lean_nat_add(v___x_1674_, v_size_1630_);
lean_dec(v___x_1674_);
lean_inc_ref(v_l_1427_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 4, v_l_1616_);
lean_ctor_set(v___x_1628_, 3, v_l_1427_);
lean_ctor_set(v___x_1628_, 2, v_v_1426_);
lean_ctor_set(v___x_1628_, 1, v_k_1425_);
lean_ctor_set(v___x_1628_, 0, v___x_1676_);
v___x_1678_ = v___x_1628_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1676_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v_k_1425_);
lean_ctor_set(v_reuseFailAlloc_1691_, 2, v_v_1426_);
lean_ctor_set(v_reuseFailAlloc_1691_, 3, v_l_1427_);
lean_ctor_set(v_reuseFailAlloc_1691_, 4, v_l_1616_);
v___x_1678_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
v_isSharedCheck_1685_ = !lean_is_exclusive(v_l_1427_);
if (v_isSharedCheck_1685_ == 0)
{
lean_object* v_unused_1686_; lean_object* v_unused_1687_; lean_object* v_unused_1688_; lean_object* v_unused_1689_; lean_object* v_unused_1690_; 
v_unused_1686_ = lean_ctor_get(v_l_1427_, 4);
lean_dec(v_unused_1686_);
v_unused_1687_ = lean_ctor_get(v_l_1427_, 3);
lean_dec(v_unused_1687_);
v_unused_1688_ = lean_ctor_get(v_l_1427_, 2);
lean_dec(v_unused_1688_);
v_unused_1689_ = lean_ctor_get(v_l_1427_, 1);
lean_dec(v_unused_1689_);
v_unused_1690_ = lean_ctor_get(v_l_1427_, 0);
lean_dec(v_unused_1690_);
v___x_1680_ = v_l_1427_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_dec(v_l_1427_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 4, v_r_1617_);
lean_ctor_set(v___x_1680_, 3, v___x_1678_);
lean_ctor_set(v___x_1680_, 2, v_v_1615_);
lean_ctor_set(v___x_1680_, 1, v_k_1614_);
lean_ctor_set(v___x_1680_, 0, v___x_1675_);
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1675_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_k_1614_);
lean_ctor_set(v_reuseFailAlloc_1684_, 2, v_v_1615_);
lean_ctor_set(v_reuseFailAlloc_1684_, 3, v___x_1678_);
lean_ctor_set(v_reuseFailAlloc_1684_, 4, v_r_1617_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
}
else
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
lean_dec_ref_known(v_l_1616_, 5);
lean_del_object(v___x_1628_);
lean_dec(v_v_1615_);
lean_dec(v_k_1614_);
lean_dec(v_size_1613_);
lean_dec_ref_known(v_l_1427_, 5);
lean_del_object(v___x_1430_);
lean_dec(v_v_1426_);
lean_dec(v_k_1425_);
v___x_1692_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7);
v___x_1693_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1692_);
return v___x_1693_;
}
}
else
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_del_object(v___x_1628_);
lean_dec(v_r_1617_);
lean_dec(v_v_1615_);
lean_dec(v_k_1614_);
lean_dec(v_size_1613_);
lean_dec_ref_known(v_l_1427_, 5);
lean_del_object(v___x_1430_);
lean_dec(v_v_1426_);
lean_dec(v_k_1425_);
v___x_1694_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8);
v___x_1695_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1694_);
return v___x_1695_;
}
}
}
}
else
{
lean_object* v_size_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1706_; 
v_size_1702_ = lean_ctor_get(v_l_1427_, 0);
v___x_1703_ = lean_unsigned_to_nat(1u);
v___x_1704_ = lean_nat_add(v___x_1703_, v_size_1702_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 4, v___x_1611_);
lean_ctor_set(v___x_1430_, 0, v___x_1704_);
v___x_1706_ = v___x_1430_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1704_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_k_1425_);
lean_ctor_set(v_reuseFailAlloc_1707_, 2, v_v_1426_);
lean_ctor_set(v_reuseFailAlloc_1707_, 3, v_l_1427_);
lean_ctor_set(v_reuseFailAlloc_1707_, 4, v___x_1611_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
else
{
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_l_1708_; 
v_l_1708_ = lean_ctor_get(v___x_1611_, 3);
lean_inc(v_l_1708_);
if (lean_obj_tag(v_l_1708_) == 0)
{
lean_object* v_r_1709_; 
v_r_1709_ = lean_ctor_get(v___x_1611_, 4);
lean_inc(v_r_1709_);
if (lean_obj_tag(v_r_1709_) == 0)
{
lean_object* v_size_1710_; lean_object* v_k_1711_; lean_object* v_v_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1726_; 
v_size_1710_ = lean_ctor_get(v___x_1611_, 0);
v_k_1711_ = lean_ctor_get(v___x_1611_, 1);
v_v_1712_ = lean_ctor_get(v___x_1611_, 2);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1726_ == 0)
{
lean_object* v_unused_1727_; lean_object* v_unused_1728_; 
v_unused_1727_ = lean_ctor_get(v___x_1611_, 4);
lean_dec(v_unused_1727_);
v_unused_1728_ = lean_ctor_get(v___x_1611_, 3);
lean_dec(v_unused_1728_);
v___x_1714_ = v___x_1611_;
v_isShared_1715_ = v_isSharedCheck_1726_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_v_1712_);
lean_inc(v_k_1711_);
lean_inc(v_size_1710_);
lean_dec(v___x_1611_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1726_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v_size_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1721_; 
v_size_1716_ = lean_ctor_get(v_l_1708_, 0);
v___x_1717_ = lean_unsigned_to_nat(1u);
v___x_1718_ = lean_nat_add(v___x_1717_, v_size_1710_);
lean_dec(v_size_1710_);
v___x_1719_ = lean_nat_add(v___x_1717_, v_size_1716_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 4, v_l_1708_);
lean_ctor_set(v___x_1714_, 3, v_l_1427_);
lean_ctor_set(v___x_1714_, 2, v_v_1426_);
lean_ctor_set(v___x_1714_, 1, v_k_1425_);
lean_ctor_set(v___x_1714_, 0, v___x_1719_);
v___x_1721_ = v___x_1714_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1719_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_k_1425_);
lean_ctor_set(v_reuseFailAlloc_1725_, 2, v_v_1426_);
lean_ctor_set(v_reuseFailAlloc_1725_, 3, v_l_1427_);
lean_ctor_set(v_reuseFailAlloc_1725_, 4, v_l_1708_);
v___x_1721_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
lean_object* v___x_1723_; 
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 4, v_r_1709_);
lean_ctor_set(v___x_1430_, 3, v___x_1721_);
lean_ctor_set(v___x_1430_, 2, v_v_1712_);
lean_ctor_set(v___x_1430_, 1, v_k_1711_);
lean_ctor_set(v___x_1430_, 0, v___x_1718_);
v___x_1723_ = v___x_1430_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1718_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v_k_1711_);
lean_ctor_set(v_reuseFailAlloc_1724_, 2, v_v_1712_);
lean_ctor_set(v_reuseFailAlloc_1724_, 3, v___x_1721_);
lean_ctor_set(v_reuseFailAlloc_1724_, 4, v_r_1709_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
else
{
lean_object* v_k_1729_; lean_object* v_v_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1754_; 
v_k_1729_ = lean_ctor_get(v___x_1611_, 1);
v_v_1730_ = lean_ctor_get(v___x_1611_, 2);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1754_ == 0)
{
lean_object* v_unused_1755_; lean_object* v_unused_1756_; lean_object* v_unused_1757_; 
v_unused_1755_ = lean_ctor_get(v___x_1611_, 4);
lean_dec(v_unused_1755_);
v_unused_1756_ = lean_ctor_get(v___x_1611_, 3);
lean_dec(v_unused_1756_);
v_unused_1757_ = lean_ctor_get(v___x_1611_, 0);
lean_dec(v_unused_1757_);
v___x_1732_ = v___x_1611_;
v_isShared_1733_ = v_isSharedCheck_1754_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_v_1730_);
lean_inc(v_k_1729_);
lean_dec(v___x_1611_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1754_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v_k_1734_; lean_object* v_v_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1750_; 
v_k_1734_ = lean_ctor_get(v_l_1708_, 1);
v_v_1735_ = lean_ctor_get(v_l_1708_, 2);
v_isSharedCheck_1750_ = !lean_is_exclusive(v_l_1708_);
if (v_isSharedCheck_1750_ == 0)
{
lean_object* v_unused_1751_; lean_object* v_unused_1752_; lean_object* v_unused_1753_; 
v_unused_1751_ = lean_ctor_get(v_l_1708_, 4);
lean_dec(v_unused_1751_);
v_unused_1752_ = lean_ctor_get(v_l_1708_, 3);
lean_dec(v_unused_1752_);
v_unused_1753_ = lean_ctor_get(v_l_1708_, 0);
lean_dec(v_unused_1753_);
v___x_1737_ = v_l_1708_;
v_isShared_1738_ = v_isSharedCheck_1750_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_v_1735_);
lean_inc(v_k_1734_);
lean_dec(v_l_1708_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1750_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1742_; 
v___x_1739_ = lean_unsigned_to_nat(3u);
v___x_1740_ = lean_unsigned_to_nat(1u);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 4, v_r_1709_);
lean_ctor_set(v___x_1737_, 3, v_r_1709_);
lean_ctor_set(v___x_1737_, 2, v_v_1426_);
lean_ctor_set(v___x_1737_, 1, v_k_1425_);
lean_ctor_set(v___x_1737_, 0, v___x_1740_);
v___x_1742_ = v___x_1737_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1740_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v_k_1425_);
lean_ctor_set(v_reuseFailAlloc_1749_, 2, v_v_1426_);
lean_ctor_set(v_reuseFailAlloc_1749_, 3, v_r_1709_);
lean_ctor_set(v_reuseFailAlloc_1749_, 4, v_r_1709_);
v___x_1742_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
lean_object* v___x_1744_; 
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 3, v_r_1709_);
lean_ctor_set(v___x_1732_, 0, v___x_1740_);
v___x_1744_ = v___x_1732_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1740_);
lean_ctor_set(v_reuseFailAlloc_1748_, 1, v_k_1729_);
lean_ctor_set(v_reuseFailAlloc_1748_, 2, v_v_1730_);
lean_ctor_set(v_reuseFailAlloc_1748_, 3, v_r_1709_);
lean_ctor_set(v_reuseFailAlloc_1748_, 4, v_r_1709_);
v___x_1744_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
lean_object* v___x_1746_; 
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 4, v___x_1744_);
lean_ctor_set(v___x_1430_, 3, v___x_1742_);
lean_ctor_set(v___x_1430_, 2, v_v_1735_);
lean_ctor_set(v___x_1430_, 1, v_k_1734_);
lean_ctor_set(v___x_1430_, 0, v___x_1739_);
v___x_1746_ = v___x_1430_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1739_);
lean_ctor_set(v_reuseFailAlloc_1747_, 1, v_k_1734_);
lean_ctor_set(v_reuseFailAlloc_1747_, 2, v_v_1735_);
lean_ctor_set(v_reuseFailAlloc_1747_, 3, v___x_1742_);
lean_ctor_set(v_reuseFailAlloc_1747_, 4, v___x_1744_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1758_; 
v_r_1758_ = lean_ctor_get(v___x_1611_, 4);
lean_inc(v_r_1758_);
if (lean_obj_tag(v_r_1758_) == 0)
{
lean_object* v_k_1759_; lean_object* v_v_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1772_; 
v_k_1759_ = lean_ctor_get(v___x_1611_, 1);
v_v_1760_ = lean_ctor_get(v___x_1611_, 2);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1772_ == 0)
{
lean_object* v_unused_1773_; lean_object* v_unused_1774_; lean_object* v_unused_1775_; 
v_unused_1773_ = lean_ctor_get(v___x_1611_, 4);
lean_dec(v_unused_1773_);
v_unused_1774_ = lean_ctor_get(v___x_1611_, 3);
lean_dec(v_unused_1774_);
v_unused_1775_ = lean_ctor_get(v___x_1611_, 0);
lean_dec(v_unused_1775_);
v___x_1762_ = v___x_1611_;
v_isShared_1763_ = v_isSharedCheck_1772_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_v_1760_);
lean_inc(v_k_1759_);
lean_dec(v___x_1611_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1772_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1767_; 
v___x_1764_ = lean_unsigned_to_nat(3u);
v___x_1765_ = lean_unsigned_to_nat(1u);
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 4, v_l_1708_);
lean_ctor_set(v___x_1762_, 2, v_v_1426_);
lean_ctor_set(v___x_1762_, 1, v_k_1425_);
lean_ctor_set(v___x_1762_, 0, v___x_1765_);
v___x_1767_ = v___x_1762_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1765_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v_k_1425_);
lean_ctor_set(v_reuseFailAlloc_1771_, 2, v_v_1426_);
lean_ctor_set(v_reuseFailAlloc_1771_, 3, v_l_1708_);
lean_ctor_set(v_reuseFailAlloc_1771_, 4, v_l_1708_);
v___x_1767_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
lean_object* v___x_1769_; 
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 4, v_r_1758_);
lean_ctor_set(v___x_1430_, 3, v___x_1767_);
lean_ctor_set(v___x_1430_, 2, v_v_1760_);
lean_ctor_set(v___x_1430_, 1, v_k_1759_);
lean_ctor_set(v___x_1430_, 0, v___x_1764_);
v___x_1769_ = v___x_1430_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1764_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_k_1759_);
lean_ctor_set(v_reuseFailAlloc_1770_, 2, v_v_1760_);
lean_ctor_set(v_reuseFailAlloc_1770_, 3, v___x_1767_);
lean_ctor_set(v_reuseFailAlloc_1770_, 4, v_r_1758_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
else
{
lean_object* v___x_1776_; lean_object* v___x_1778_; 
v___x_1776_ = lean_unsigned_to_nat(2u);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 4, v___x_1611_);
lean_ctor_set(v___x_1430_, 3, v_r_1758_);
lean_ctor_set(v___x_1430_, 0, v___x_1776_);
v___x_1778_ = v___x_1430_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1776_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_k_1425_);
lean_ctor_set(v_reuseFailAlloc_1779_, 2, v_v_1426_);
lean_ctor_set(v_reuseFailAlloc_1779_, 3, v_r_1758_);
lean_ctor_set(v_reuseFailAlloc_1779_, 4, v___x_1611_);
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
lean_object* v___x_1780_; lean_object* v___x_1782_; 
v___x_1780_ = lean_unsigned_to_nat(1u);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 4, v___x_1611_);
lean_ctor_set(v___x_1430_, 3, v___x_1611_);
lean_ctor_set(v___x_1430_, 0, v___x_1780_);
v___x_1782_ = v___x_1430_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1780_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v_k_1425_);
lean_ctor_set(v_reuseFailAlloc_1783_, 2, v_v_1426_);
lean_ctor_set(v_reuseFailAlloc_1783_, 3, v___x_1611_);
lean_ctor_set(v_reuseFailAlloc_1783_, 4, v___x_1611_);
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
}
}
}
else
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = lean_unsigned_to_nat(1u);
v___x_1786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1785_);
lean_ctor_set(v___x_1786_, 1, v_k_1421_);
lean_ctor_set(v___x_1786_, 2, v_v_1422_);
lean_ctor_set(v___x_1786_, 3, v_t_1423_);
lean_ctor_set(v___x_1786_, 4, v_t_1423_);
return v___x_1786_;
}
}
}
static lean_object* _init_l_Lean_Json_setObjVal_x21___closed__2(void){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1789_ = ((lean_object*)(l_Lean_Json_setObjVal_x21___closed__1));
v___x_1790_ = lean_unsigned_to_nat(21u);
v___x_1791_ = lean_unsigned_to_nat(285u);
v___x_1792_ = ((lean_object*)(l_Lean_Json_setObjVal_x21___closed__0));
v___x_1793_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0));
v___x_1794_ = l_mkPanicMessageWithDecl(v___x_1793_, v___x_1792_, v___x_1791_, v___x_1790_, v___x_1789_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_setObjVal_x21(lean_object* v_x_1795_, lean_object* v_x_1796_, lean_object* v_x_1797_){
_start:
{
if (lean_obj_tag(v_x_1795_) == 5)
{
lean_object* v_kvPairs_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1806_; 
v_kvPairs_1798_ = lean_ctor_get(v_x_1795_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_x_1795_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1800_ = v_x_1795_;
v_isShared_1801_ = v_isSharedCheck_1806_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_kvPairs_1798_);
lean_dec(v_x_1795_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1806_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1802_; lean_object* v___x_1804_; 
v___x_1802_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_x_1796_, v_x_1797_, v_kvPairs_1798_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1802_);
v___x_1804_ = v___x_1800_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1802_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
else
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
lean_dec(v_x_1797_);
lean_dec_ref(v_x_1796_);
lean_dec(v_x_1795_);
v___x_1807_ = lean_obj_once(&l_Lean_Json_setObjVal_x21___closed__2, &l_Lean_Json_setObjVal_x21___closed__2_once, _init_l_Lean_Json_setObjVal_x21___closed__2);
v___x_1808_ = l_panic___at___00Lean_Json_setObjVal_x21_spec__1(v___x_1807_);
return v___x_1808_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0(lean_object* v_00_u03b2_1809_, lean_object* v_msg_1810_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v_msg_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0(lean_object* v_00_u03b2_1812_, lean_object* v_k_1813_, lean_object* v_v_1814_, lean_object* v_t_1815_){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1813_, v_v_1814_, v_t_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(lean_object* v_init_1817_, lean_object* v_x_1818_){
_start:
{
if (lean_obj_tag(v_x_1818_) == 0)
{
lean_object* v_k_1819_; lean_object* v_v_1820_; lean_object* v_l_1821_; lean_object* v_r_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v_k_1819_ = lean_ctor_get(v_x_1818_, 1);
lean_inc(v_k_1819_);
v_v_1820_ = lean_ctor_get(v_x_1818_, 2);
lean_inc(v_v_1820_);
v_l_1821_ = lean_ctor_get(v_x_1818_, 3);
lean_inc(v_l_1821_);
v_r_1822_ = lean_ctor_get(v_x_1818_, 4);
lean_inc(v_r_1822_);
lean_dec_ref_known(v_x_1818_, 5);
v___x_1823_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_init_1817_, v_l_1821_);
v___x_1824_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1819_, v_v_1820_, v___x_1823_);
v_init_1817_ = v___x_1824_;
v_x_1818_ = v_r_1822_;
goto _start;
}
else
{
return v_init_1817_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mergeObj(lean_object* v_x_1826_, lean_object* v_x_1827_){
_start:
{
if (lean_obj_tag(v_x_1826_) == 5)
{
if (lean_obj_tag(v_x_1827_) == 5)
{
lean_object* v_kvPairs_1828_; lean_object* v_kvPairs_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1837_; 
v_kvPairs_1828_ = lean_ctor_get(v_x_1826_, 0);
lean_inc(v_kvPairs_1828_);
lean_dec_ref_known(v_x_1826_, 1);
v_kvPairs_1829_ = lean_ctor_get(v_x_1827_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v_x_1827_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1831_ = v_x_1827_;
v_isShared_1832_ = v_isSharedCheck_1837_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_kvPairs_1829_);
lean_dec(v_x_1827_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1837_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1833_; lean_object* v___x_1835_; 
v___x_1833_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_kvPairs_1828_, v_kvPairs_1829_);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1833_);
v___x_1835_ = v___x_1831_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
else
{
lean_dec_ref_known(v_x_1826_, 1);
return v_x_1827_;
}
}
else
{
lean_dec(v_x_1826_);
return v_x_1827_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0(lean_object* v_init_1838_, lean_object* v_t_1839_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_init_1838_, v_t_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorIdx___impl(lean_object* v_x_1841_){
_start:
{
lean_object* v___x_1842_; 
v___x_1842_ = lean_obj_tag_nat(v_x_1841_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorIdx___impl___boxed(lean_object* v_x_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_Json_Structured_ctorIdx___impl(v_x_1843_);
lean_dec_ref(v_x_1843_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim___redArg(lean_object* v_t_1845_, lean_object* v_k_1846_){
_start:
{
if (lean_obj_tag(v_t_1845_) == 0)
{
lean_object* v_elems_1847_; lean_object* v___x_1848_; 
v_elems_1847_ = lean_ctor_get(v_t_1845_, 0);
lean_inc_ref(v_elems_1847_);
lean_dec_ref_known(v_t_1845_, 1);
v___x_1848_ = lean_apply_1(v_k_1846_, v_elems_1847_);
return v___x_1848_;
}
else
{
lean_object* v_kvPairs_1849_; lean_object* v___x_1850_; 
v_kvPairs_1849_ = lean_ctor_get(v_t_1845_, 0);
lean_inc(v_kvPairs_1849_);
lean_dec_ref_known(v_t_1845_, 1);
v___x_1850_ = lean_apply_1(v_k_1846_, v_kvPairs_1849_);
return v___x_1850_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim(lean_object* v_motive_1851_, lean_object* v_ctorIdx_1852_, lean_object* v_t_1853_, lean_object* v_h_1854_, lean_object* v_k_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1853_, v_k_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim___boxed(lean_object* v_motive_1857_, lean_object* v_ctorIdx_1858_, lean_object* v_t_1859_, lean_object* v_h_1860_, lean_object* v_k_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_Json_Structured_ctorElim(v_motive_1857_, v_ctorIdx_1858_, v_t_1859_, v_h_1860_, v_k_1861_);
lean_dec(v_ctorIdx_1858_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_arr_elim___redArg(lean_object* v_t_1863_, lean_object* v_arr_1864_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1863_, v_arr_1864_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_arr_elim(lean_object* v_motive_1866_, lean_object* v_t_1867_, lean_object* v_h_1868_, lean_object* v_arr_1869_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1867_, v_arr_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_obj_elim___redArg(lean_object* v_t_1871_, lean_object* v_obj_1872_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1871_, v_obj_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_obj_elim(lean_object* v_motive_1874_, lean_object* v_t_1875_, lean_object* v_h_1876_, lean_object* v_obj_1877_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1875_, v_obj_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeArrayStructured___lam__0(lean_object* v_elems_1879_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1880_, 0, v_elems_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeRawStringStructured___lam__0(lean_object* v_kvPairs_1883_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1884_, 0, v_kvPairs_1883_);
return v___x_1884_;
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
