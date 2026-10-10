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
uint8_t l_Lean_instDecidableEqJsonNumber_decEq(lean_object* v_x_1_, lean_object* v_x_2_){
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
LEAN_EXPORT void l_Lean_instDecidableEqJsonNumber_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
uint8_t v_res_9_;
v_res_9_ = l_Lean_instDecidableEqJsonNumber_decEq(v_x_1_, v_x_2_);
stack->m_num = v_res_9_;
}
LEAN_EXPORT lean_object* l_Lean_instDecidableEqJsonNumber_decEq___boxed(lean_object* v_x_10_, lean_object* v_x_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_Lean_instDecidableEqJsonNumber_decEq(v_x_10_, v_x_11_);
lean_dec_ref(v_x_11_);
lean_dec_ref(v_x_10_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
uint8_t l_Lean_instDecidableEqJsonNumber(lean_object* v_x_14_, lean_object* v_x_15_){
_start:
{
uint8_t v___x_16_; 
v___x_16_ = l_Lean_instDecidableEqJsonNumber_decEq(v_x_14_, v_x_15_);
return v___x_16_;
}
}
LEAN_EXPORT void l_Lean_instDecidableEqJsonNumber_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_14_ = stack[0].m_obj;
lean_object* v_x_15_ = stack[1].m_obj;
uint8_t v_res_17_;
v_res_17_ = l_Lean_instDecidableEqJsonNumber(v_x_14_, v_x_15_);
stack->m_num = v_res_17_;
}
LEAN_EXPORT lean_object* l_Lean_instDecidableEqJsonNumber___boxed(lean_object* v_x_18_, lean_object* v_x_19_){
_start:
{
uint8_t v_res_20_; lean_object* v_r_21_; 
v_res_20_ = l_Lean_instDecidableEqJsonNumber(v_x_18_, v_x_19_);
lean_dec_ref(v_x_19_);
lean_dec_ref(v_x_18_);
v_r_21_ = lean_box(v_res_20_);
return v_r_21_;
}
}
static lean_object* _init_l_Lean_instHashableJsonNumber_hash___closed__0(void){
_start:
{
lean_object* v_natZero_22_; lean_object* v_intZero_23_; 
v_natZero_22_ = lean_unsigned_to_nat(0u);
v_intZero_23_ = lean_nat_to_int(v_natZero_22_);
return v_intZero_23_;
}
}
uint64_t l_Lean_instHashableJsonNumber_hash(lean_object* v_x_24_){
_start:
{
lean_object* v_mantissa_25_; lean_object* v_exponent_26_; uint64_t v___x_27_; uint64_t v___y_29_; lean_object* v_intZero_33_; uint8_t v_isNeg_34_; 
v_mantissa_25_ = lean_ctor_get(v_x_24_, 0);
v_exponent_26_ = lean_ctor_get(v_x_24_, 1);
v___x_27_ = 0ULL;
v_intZero_33_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v_isNeg_34_ = lean_int_dec_lt(v_mantissa_25_, v_intZero_33_);
if (v_isNeg_34_ == 0)
{
lean_object* v_a_35_; lean_object* v___x_36_; lean_object* v___x_37_; uint64_t v___x_38_; 
v_a_35_ = lean_nat_abs(v_mantissa_25_);
v___x_36_ = lean_unsigned_to_nat(2u);
v___x_37_ = lean_nat_mul(v___x_36_, v_a_35_);
lean_dec(v_a_35_);
v___x_38_ = lean_uint64_of_nat(v___x_37_);
lean_dec(v___x_37_);
v___y_29_ = v___x_38_;
goto v___jp_28_;
}
else
{
lean_object* v_abs_39_; lean_object* v_one_40_; lean_object* v_a_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; uint64_t v___x_45_; 
v_abs_39_ = lean_nat_abs(v_mantissa_25_);
v_one_40_ = lean_unsigned_to_nat(1u);
v_a_41_ = lean_nat_sub(v_abs_39_, v_one_40_);
lean_dec(v_abs_39_);
v___x_42_ = lean_unsigned_to_nat(2u);
v___x_43_ = lean_nat_mul(v___x_42_, v_a_41_);
lean_dec(v_a_41_);
v___x_44_ = lean_nat_add(v___x_43_, v_one_40_);
lean_dec(v___x_43_);
v___x_45_ = lean_uint64_of_nat(v___x_44_);
lean_dec(v___x_44_);
v___y_29_ = v___x_45_;
goto v___jp_28_;
}
v___jp_28_:
{
uint64_t v___x_30_; uint64_t v___x_31_; uint64_t v___x_32_; 
v___x_30_ = lean_uint64_mix_hash(v___x_27_, v___y_29_);
v___x_31_ = lean_uint64_of_nat(v_exponent_26_);
v___x_32_ = lean_uint64_mix_hash(v___x_30_, v___x_31_);
return v___x_32_;
}
}
}
LEAN_EXPORT void l_Lean_instHashableJsonNumber_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_24_ = stack[0].m_obj;
uint64_t v_res_46_;
v_res_46_ = l_Lean_instHashableJsonNumber_hash(v_x_24_);
stack->m_num = v_res_46_;
}
LEAN_EXPORT lean_object* l_Lean_instHashableJsonNumber_hash___boxed(lean_object* v_x_47_){
_start:
{
uint64_t v_res_48_; lean_object* v_r_49_; 
v_res_48_ = l_Lean_instHashableJsonNumber_hash(v_x_47_);
lean_dec_ref(v_x_47_);
v_r_49_ = lean_box_uint64(v_res_48_);
return v_r_49_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_JsonNumber_fromNat_spec__0(lean_object* v_a_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lean_nat_to_int(v_a_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_fromNat(lean_object* v_n_54_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = lean_nat_to_int(v_n_54_);
v___x_56_ = lean_unsigned_to_nat(0u);
v___x_57_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_55_);
lean_ctor_set(v___x_57_, 1, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_fromInt(lean_object* v_n_58_){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_unsigned_to_nat(0u);
v___x_60_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_60_, 0, v_n_58_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOfNat(lean_object* v_n_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_JsonNumber_fromNat(v_n_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits_loop(lean_object* v_n_67_, lean_object* v_digits_68_){
_start:
{
lean_object* v___x_69_; uint8_t v___x_70_; 
v___x_69_ = lean_unsigned_to_nat(9u);
v___x_70_ = lean_nat_dec_le(v_n_67_, v___x_69_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_71_ = lean_unsigned_to_nat(10u);
v___x_72_ = lean_nat_div(v_n_67_, v___x_71_);
lean_dec(v_n_67_);
v___x_73_ = lean_unsigned_to_nat(1u);
v___x_74_ = lean_nat_add(v_digits_68_, v___x_73_);
lean_dec(v_digits_68_);
v_n_67_ = v___x_72_;
v_digits_68_ = v___x_74_;
goto _start;
}
else
{
lean_dec(v_n_67_);
return v_digits_68_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(lean_object* v_n_76_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_unsigned_to_nat(1u);
v___x_78_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits_loop(v_n_76_, v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0___redArg(lean_object* v_upperBound_79_, lean_object* v_a_80_, lean_object* v_b_81_){
_start:
{
uint8_t v___x_82_; 
v___x_82_ = lean_nat_dec_lt(v_a_80_, v_upperBound_79_);
if (v___x_82_ == 0)
{
lean_dec(v_a_80_);
return v_b_81_;
}
else
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = lean_unsigned_to_nat(10u);
v___x_85_ = lean_nat_mod(v_b_81_, v___x_84_);
v___x_86_ = lean_nat_dec_eq(v___x_85_, v___x_83_);
lean_dec(v___x_85_);
if (v___x_86_ == 0)
{
lean_dec(v_a_80_);
return v_b_81_;
}
else
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = lean_nat_div(v_b_81_, v___x_84_);
lean_dec(v_b_81_);
v___x_88_ = lean_unsigned_to_nat(1u);
v___x_89_ = lean_nat_add(v_a_80_, v___x_88_);
lean_dec(v_a_80_);
v_a_80_ = v___x_89_;
v_b_81_ = v___x_87_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0___redArg___boxed(lean_object* v_upperBound_91_, lean_object* v_a_92_, lean_object* v_b_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0___redArg(v_upperBound_91_, v_a_92_, v_b_93_);
lean_dec(v_upperBound_91_);
return v_res_94_;
}
}
static lean_object* _init_l_Lean_JsonNumber_normalize___closed__0(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = lean_unsigned_to_nat(1u);
v___x_96_ = lean_nat_to_int(v___x_95_);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_JsonNumber_normalize___closed__1(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_obj_once(&l_Lean_JsonNumber_normalize___closed__0, &l_Lean_JsonNumber_normalize___closed__0_once, _init_l_Lean_JsonNumber_normalize___closed__0);
v___x_98_ = lean_int_neg(v___x_97_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_JsonNumber_normalize___closed__2(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_99_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v___x_100_ = lean_unsigned_to_nat(0u);
v___x_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v___x_99_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_JsonNumber_normalize___closed__3(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = lean_obj_once(&l_Lean_JsonNumber_normalize___closed__2, &l_Lean_JsonNumber_normalize___closed__2_once, _init_l_Lean_JsonNumber_normalize___closed__2);
v___x_103_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v___x_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
lean_ctor_set(v___x_104_, 1, v___x_102_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_normalize(lean_object* v_x_105_){
_start:
{
lean_object* v_mantissa_106_; lean_object* v_exponent_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_131_; 
v_mantissa_106_ = lean_ctor_get(v_x_105_, 0);
v_exponent_107_ = lean_ctor_get(v_x_105_, 1);
v_isSharedCheck_131_ = !lean_is_exclusive(v_x_105_);
if (v_isSharedCheck_131_ == 0)
{
v___x_109_ = v_x_105_;
v_isShared_110_ = v_isSharedCheck_131_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_exponent_107_);
lean_inc(v_mantissa_106_);
lean_dec(v_x_105_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_131_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v___y_113_; lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_111_ = lean_unsigned_to_nat(0u);
v___x_125_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v___x_126_ = lean_int_dec_eq(v_mantissa_106_, v___x_125_);
if (v___x_126_ == 0)
{
uint8_t v___x_127_; 
v___x_127_ = lean_int_dec_lt(v___x_125_, v_mantissa_106_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; 
v___x_128_ = lean_obj_once(&l_Lean_JsonNumber_normalize___closed__1, &l_Lean_JsonNumber_normalize___closed__1_once, _init_l_Lean_JsonNumber_normalize___closed__1);
v___y_113_ = v___x_128_;
goto v___jp_112_;
}
else
{
lean_object* v___x_129_; 
v___x_129_ = lean_obj_once(&l_Lean_JsonNumber_normalize___closed__0, &l_Lean_JsonNumber_normalize___closed__0_once, _init_l_Lean_JsonNumber_normalize___closed__0);
v___y_113_ = v___x_129_;
goto v___jp_112_;
}
}
else
{
lean_object* v___x_130_; 
lean_del_object(v___x_109_);
lean_dec(v_exponent_107_);
lean_dec(v_mantissa_106_);
v___x_130_ = lean_obj_once(&l_Lean_JsonNumber_normalize___closed__3, &l_Lean_JsonNumber_normalize___closed__3_once, _init_l_Lean_JsonNumber_normalize___closed__3);
return v___x_130_;
}
v___jp_112_:
{
lean_object* v_mAbs_114_; lean_object* v_nDigits_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_122_; 
v_mAbs_114_ = lean_nat_abs(v_mantissa_106_);
lean_dec(v_mantissa_106_);
lean_inc(v_mAbs_114_);
v_nDigits_115_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(v_mAbs_114_);
v___x_116_ = l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0___redArg(v_nDigits_115_, v___x_111_, v_mAbs_114_);
v___x_117_ = lean_nat_to_int(v_exponent_107_);
v___x_118_ = lean_int_neg(v___x_117_);
lean_dec(v___x_117_);
v___x_119_ = lean_nat_to_int(v_nDigits_115_);
v___x_120_ = lean_int_add(v___x_118_, v___x_119_);
lean_dec(v___x_119_);
lean_dec(v___x_118_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 1, v___x_120_);
lean_ctor_set(v___x_109_, 0, v___x_116_);
v___x_122_ = v___x_109_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_116_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v___x_120_);
v___x_122_ = v_reuseFailAlloc_124_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
lean_object* v___x_123_; 
lean_inc(v___y_113_);
v___x_123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_123_, 0, v___y_113_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
return v___x_123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0(lean_object* v_upperBound_132_, lean_object* v_inst_133_, lean_object* v_R_134_, lean_object* v_a_135_, lean_object* v_b_136_, lean_object* v_c_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0___redArg(v_upperBound_132_, v_a_135_, v_b_136_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0___boxed(lean_object* v_upperBound_139_, lean_object* v_inst_140_, lean_object* v_R_141_, lean_object* v_a_142_, lean_object* v_b_143_, lean_object* v_c_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0(v_upperBound_139_, v_inst_140_, v_R_141_, v_a_142_, v_b_143_, v_c_144_);
lean_dec(v_upperBound_139_);
return v_res_145_;
}
}
uint8_t l_Lean_JsonNumber_lt(lean_object* v_a_146_, lean_object* v_b_147_){
_start:
{
lean_object* v_fst_149_; lean_object* v_snd_150_; lean_object* v___x_170_; lean_object* v_fst_171_; lean_object* v_snd_172_; lean_object* v___x_173_; lean_object* v_fst_174_; lean_object* v_snd_175_; uint8_t v___x_176_; 
v___x_170_ = l_Lean_JsonNumber_normalize(v_a_146_);
v_fst_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_fst_171_);
v_snd_172_ = lean_ctor_get(v___x_170_, 1);
lean_inc(v_snd_172_);
lean_dec_ref(v___x_170_);
v___x_173_ = l_Lean_JsonNumber_normalize(v_b_147_);
v_fst_174_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_fst_174_);
v_snd_175_ = lean_ctor_get(v___x_173_, 1);
lean_inc(v_snd_175_);
lean_dec_ref(v___x_173_);
v___x_176_ = lean_int_dec_eq(v_fst_171_, v_fst_174_);
if (v___x_176_ == 0)
{
uint8_t v___x_177_; 
lean_dec(v_snd_175_);
lean_dec(v_snd_172_);
v___x_177_ = lean_int_dec_lt(v_fst_171_, v_fst_174_);
lean_dec(v_fst_174_);
lean_dec(v_fst_171_);
return v___x_177_;
}
else
{
lean_object* v___x_178_; uint8_t v___x_179_; 
lean_dec(v_fst_174_);
v___x_178_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v___x_179_ = lean_int_dec_eq(v_fst_171_, v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_180_ = lean_obj_once(&l_Lean_JsonNumber_normalize___closed__1, &l_Lean_JsonNumber_normalize___closed__1_once, _init_l_Lean_JsonNumber_normalize___closed__1);
v___x_181_ = lean_int_dec_eq(v_fst_171_, v___x_180_);
lean_dec(v_fst_171_);
if (v___x_181_ == 0)
{
v_fst_149_ = v_snd_172_;
v_snd_150_ = v_snd_175_;
goto v___jp_148_;
}
else
{
v_fst_149_ = v_snd_175_;
v_snd_150_ = v_snd_172_;
goto v___jp_148_;
}
}
else
{
uint8_t v___x_182_; 
lean_dec(v_snd_175_);
lean_dec(v_snd_172_);
lean_dec(v_fst_171_);
v___x_182_ = 0;
return v___x_182_;
}
}
v___jp_148_:
{
lean_object* v_fst_151_; lean_object* v_snd_152_; lean_object* v_fst_153_; lean_object* v_snd_154_; uint8_t v___x_155_; 
v_fst_151_ = lean_ctor_get(v_fst_149_, 0);
lean_inc(v_fst_151_);
v_snd_152_ = lean_ctor_get(v_fst_149_, 1);
lean_inc(v_snd_152_);
lean_dec_ref(v_fst_149_);
v_fst_153_ = lean_ctor_get(v_snd_150_, 0);
lean_inc(v_fst_153_);
v_snd_154_ = lean_ctor_get(v_snd_150_, 1);
lean_inc(v_snd_154_);
lean_dec_ref(v_snd_150_);
v___x_155_ = lean_int_dec_lt(v_snd_152_, v_snd_154_);
if (v___x_155_ == 0)
{
uint8_t v___x_156_; 
v___x_156_ = lean_int_dec_lt(v_snd_154_, v_snd_152_);
lean_dec(v_snd_152_);
lean_dec(v_snd_154_);
if (v___x_156_ == 0)
{
lean_object* v_amDigits_157_; lean_object* v_bmDigits_158_; uint8_t v___x_159_; 
lean_inc(v_fst_151_);
v_amDigits_157_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(v_fst_151_);
lean_inc(v_fst_153_);
v_bmDigits_158_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(v_fst_153_);
v___x_159_ = lean_nat_dec_lt(v_amDigits_157_, v_bmDigits_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_160_ = lean_unsigned_to_nat(10u);
v___x_161_ = lean_nat_sub(v_amDigits_157_, v_bmDigits_158_);
lean_dec(v_bmDigits_158_);
lean_dec(v_amDigits_157_);
v___x_162_ = lean_nat_pow(v___x_160_, v___x_161_);
lean_dec(v___x_161_);
v___x_163_ = lean_nat_mul(v_fst_153_, v___x_162_);
lean_dec(v___x_162_);
lean_dec(v_fst_153_);
v___x_164_ = lean_nat_dec_lt(v_fst_151_, v___x_163_);
lean_dec(v___x_163_);
lean_dec(v_fst_151_);
return v___x_164_;
}
else
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_165_ = lean_unsigned_to_nat(10u);
v___x_166_ = lean_nat_sub(v_bmDigits_158_, v_amDigits_157_);
lean_dec(v_amDigits_157_);
lean_dec(v_bmDigits_158_);
v___x_167_ = lean_nat_pow(v___x_165_, v___x_166_);
lean_dec(v___x_166_);
v___x_168_ = lean_nat_mul(v_fst_151_, v___x_167_);
lean_dec(v___x_167_);
lean_dec(v_fst_151_);
v___x_169_ = lean_nat_dec_lt(v___x_168_, v_fst_153_);
lean_dec(v_fst_153_);
lean_dec(v___x_168_);
return v___x_169_;
}
}
else
{
lean_dec(v_fst_153_);
lean_dec(v_fst_151_);
return v___x_155_;
}
}
else
{
lean_dec(v_snd_154_);
lean_dec(v_fst_153_);
lean_dec(v_snd_152_);
lean_dec(v_fst_151_);
return v___x_155_;
}
}
}
}
LEAN_EXPORT void l_Lean_JsonNumber_lt_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_146_ = stack[0].m_obj;
lean_object* v_b_147_ = stack[1].m_obj;
uint8_t v_res_183_;
v_res_183_ = l_Lean_JsonNumber_lt(v_a_146_, v_b_147_);
stack->m_num = v_res_183_;
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_lt___boxed(lean_object* v_a_184_, lean_object* v_b_185_){
_start:
{
uint8_t v_res_186_; lean_object* v_r_187_; 
v_res_186_ = l_Lean_JsonNumber_lt(v_a_184_, v_b_185_);
v_r_187_ = lean_box(v_res_186_);
return v_r_187_;
}
}
static lean_object* _init_l_Lean_JsonNumber_ltProp(void){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = lean_box(0);
return v___x_188_;
}
}
uint8_t l_Lean_JsonNumber_instDecidableLt(lean_object* v_a_189_, lean_object* v_b_190_){
_start:
{
uint8_t v___x_191_; 
v___x_191_ = l_Lean_JsonNumber_lt(v_a_189_, v_b_190_);
return v___x_191_;
}
}
LEAN_EXPORT void l_Lean_JsonNumber_instDecidableLt_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_189_ = stack[0].m_obj;
lean_object* v_b_190_ = stack[1].m_obj;
uint8_t v_res_192_;
v_res_192_ = l_Lean_JsonNumber_instDecidableLt(v_a_189_, v_b_190_);
stack->m_num = v_res_192_;
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instDecidableLt___boxed(lean_object* v_a_193_, lean_object* v_b_194_){
_start:
{
uint8_t v_res_195_; lean_object* v_r_196_; 
v_res_195_ = l_Lean_JsonNumber_instDecidableLt(v_a_193_, v_b_194_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
}
}
uint8_t l_Lean_JsonNumber_instOrd___lam__0(lean_object* v_x_197_, lean_object* v_y_198_){
_start:
{
uint8_t v___x_199_; 
lean_inc_ref(v_y_198_);
lean_inc_ref(v_x_197_);
v___x_199_ = l_Lean_JsonNumber_lt(v_x_197_, v_y_198_);
if (v___x_199_ == 0)
{
uint8_t v___x_200_; 
v___x_200_ = l_Lean_JsonNumber_lt(v_y_198_, v_x_197_);
if (v___x_200_ == 0)
{
uint8_t v___x_201_; 
v___x_201_ = 1;
return v___x_201_;
}
else
{
uint8_t v___x_202_; 
v___x_202_ = 2;
return v___x_202_;
}
}
else
{
uint8_t v___x_203_; 
lean_dec_ref(v_y_198_);
lean_dec_ref(v_x_197_);
v___x_203_ = 0;
return v___x_203_;
}
}
}
LEAN_EXPORT void l_Lean_JsonNumber_instOrd___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_197_ = stack[0].m_obj;
lean_object* v_y_198_ = stack[1].m_obj;
uint8_t v_res_204_;
v_res_204_ = l_Lean_JsonNumber_instOrd___lam__0(v_x_197_, v_y_198_);
stack->m_num = v_res_204_;
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instOrd___lam__0___boxed(lean_object* v_x_205_, lean_object* v_y_206_){
_start:
{
uint8_t v_res_207_; lean_object* v_r_208_; 
v_res_207_ = l_Lean_JsonNumber_instOrd___lam__0(v_x_205_, v_y_206_);
v_r_208_ = lean_box(v_res_207_);
return v_r_208_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0(lean_object* v_s_211_, lean_object* v_begPos_212_, lean_object* v_i_213_){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_214_ = lean_unsigned_to_nat(1u);
v___x_215_ = lean_nat_add(v_begPos_212_, v___x_214_);
v___x_216_ = lean_nat_dec_le(v___x_215_, v_i_213_);
lean_dec(v___x_215_);
if (v___x_216_ == 0)
{
return v_i_213_;
}
else
{
lean_object* v_i_x27_217_; uint8_t v___y_219_; uint8_t v___y_222_; uint32_t v_c_223_; uint32_t v___x_224_; uint8_t v___x_225_; 
v_i_x27_217_ = lean_string_utf8_prev(v_s_211_, v_i_213_);
v_c_223_ = lean_string_utf8_get(v_s_211_, v_i_x27_217_);
v___x_224_ = 48;
v___x_225_ = lean_uint32_dec_eq(v_c_223_, v___x_224_);
if (v___x_225_ == 0)
{
v___y_222_ = v___x_216_;
goto v___jp_221_;
}
else
{
uint8_t v___x_226_; 
v___x_226_ = 0;
v___y_222_ = v___x_226_;
goto v___jp_221_;
}
v___jp_218_:
{
if (v___y_219_ == 0)
{
lean_dec(v_i_213_);
v_i_213_ = v_i_x27_217_;
goto _start;
}
else
{
lean_dec(v_i_x27_217_);
return v_i_213_;
}
}
v___jp_221_:
{
if (v___x_216_ == 0)
{
v___y_219_ = v___x_216_;
goto v___jp_218_;
}
else
{
v___y_219_ = v___y_222_;
goto v___jp_218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0___boxed(lean_object* v_s_227_, lean_object* v_begPos_228_, lean_object* v_i_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0(v_s_227_, v_begPos_228_, v_i_229_);
lean_dec(v_begPos_228_);
lean_dec_ref(v_s_227_);
return v_res_230_;
}
}
static lean_object* _init_l_Lean_JsonNumber_toString___closed__3(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_unsigned_to_nat(9u);
v___x_235_ = lean_nat_to_int(v___x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_toString(lean_object* v_x_237_){
_start:
{
lean_object* v___y_239_; lean_object* v___y_240_; lean_object* v___y_241_; lean_object* v___y_242_; lean_object* v_mantissa_248_; lean_object* v_exponent_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v_mantissa_248_ = lean_ctor_get(v_x_237_, 0);
lean_inc(v_mantissa_248_);
v_exponent_249_ = lean_ctor_get(v_x_237_, 1);
lean_inc(v_exponent_249_);
lean_dec_ref(v_x_237_);
v___x_250_ = lean_unsigned_to_nat(0u);
v___x_251_ = lean_nat_dec_eq(v_exponent_249_, v___x_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; lean_object* v___y_254_; lean_object* v___y_255_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v___y_275_; lean_object* v___y_287_; uint8_t v___x_296_; 
v___x_252_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v___x_296_ = lean_int_dec_le(v___x_252_, v_mantissa_248_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; 
v___x_297_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__4));
v___y_287_ = v___x_297_;
goto v___jp_286_;
}
else
{
lean_object* v___x_298_; 
v___x_298_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__2));
v___y_287_ = v___x_298_;
goto v___jp_286_;
}
v___jp_253_:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v_e_265_; lean_object* v_right_266_; uint8_t v___x_267_; 
v___x_259_ = lean_nat_add(v___y_256_, v___y_257_);
lean_dec(v___y_257_);
lean_dec(v___y_256_);
v___x_260_ = l_Nat_reprFast(v___x_259_);
v___x_261_ = lean_string_utf8_byte_size(v___x_260_);
lean_inc_ref(v___x_260_);
v___x_262_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_262_, 0, v___x_260_);
lean_ctor_set(v___x_262_, 1, v___x_250_);
lean_ctor_set(v___x_262_, 2, v___x_261_);
v___x_263_ = lean_unsigned_to_nat(1u);
v___x_264_ = l_Substring_Raw_nextn(v___x_262_, v___x_263_, v___x_250_);
lean_dec_ref_known(v___x_262_, 3);
v_e_265_ = l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0(v___x_260_, v___x_264_, v___x_261_);
v_right_266_ = lean_string_utf8_extract(v___x_260_, v___x_264_, v_e_265_);
lean_dec(v_e_265_);
lean_dec(v___x_264_);
lean_dec_ref(v___x_260_);
v___x_267_ = lean_int_dec_eq(v___y_254_, v___x_252_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__1));
v___x_269_ = l_Int_repr(v___y_254_);
lean_dec(v___y_254_);
v___x_270_ = lean_string_append(v___x_268_, v___x_269_);
lean_dec_ref(v___x_269_);
v___y_239_ = v___y_255_;
v___y_240_ = v___y_258_;
v___y_241_ = v_right_266_;
v___y_242_ = v___x_270_;
goto v___jp_238_;
}
else
{
lean_object* v___x_271_; 
lean_dec(v___y_254_);
v___x_271_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__2));
v___y_239_ = v___y_255_;
v___y_240_ = v___y_258_;
v___y_241_ = v_right_266_;
v___y_242_ = v___x_271_;
goto v___jp_238_;
}
}
v___jp_272_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v_e_x27_279_; lean_object* v___x_280_; lean_object* v_left_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_276_ = lean_unsigned_to_nat(10u);
v___x_277_ = lean_nat_abs(v___y_275_);
v___x_278_ = lean_nat_sub(v_exponent_249_, v___x_277_);
lean_dec(v___x_277_);
lean_dec(v_exponent_249_);
v_e_x27_279_ = lean_nat_pow(v___x_276_, v___x_278_);
lean_dec(v___x_278_);
v___x_280_ = lean_nat_div(v___y_274_, v_e_x27_279_);
v_left_281_ = l_Nat_reprFast(v___x_280_);
v___x_282_ = lean_nat_mod(v___y_274_, v_e_x27_279_);
lean_dec(v___y_274_);
v___x_283_ = lean_nat_dec_eq(v___x_282_, v___x_250_);
if (v___x_283_ == 0)
{
v___y_254_ = v___y_275_;
v___y_255_ = v___y_273_;
v___y_256_ = v_e_x27_279_;
v___y_257_ = v___x_282_;
v___y_258_ = v_left_281_;
goto v___jp_253_;
}
else
{
uint8_t v___x_284_; 
v___x_284_ = lean_int_dec_eq(v___y_275_, v___x_252_);
if (v___x_284_ == 0)
{
v___y_254_ = v___y_275_;
v___y_255_ = v___y_273_;
v___y_256_ = v_e_x27_279_;
v___y_257_ = v___x_282_;
v___y_258_ = v_left_281_;
goto v___jp_253_;
}
else
{
lean_object* v___x_285_; 
lean_dec(v___x_282_);
lean_dec(v_e_x27_279_);
lean_dec(v___y_275_);
lean_inc_ref(v___y_273_);
v___x_285_ = lean_string_append(v___y_273_, v_left_281_);
lean_dec_ref(v_left_281_);
return v___x_285_;
}
}
}
v___jp_286_:
{
lean_object* v_m_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v_exp_294_; uint8_t v___x_295_; 
v_m_288_ = lean_nat_abs(v_mantissa_248_);
lean_dec(v_mantissa_248_);
v___x_289_ = lean_obj_once(&l_Lean_JsonNumber_toString___closed__3, &l_Lean_JsonNumber_toString___closed__3_once, _init_l_Lean_JsonNumber_toString___closed__3);
lean_inc(v_m_288_);
v___x_290_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(v_m_288_);
v___x_291_ = lean_nat_to_int(v___x_290_);
v___x_292_ = lean_int_add(v___x_289_, v___x_291_);
lean_dec(v___x_291_);
lean_inc(v_exponent_249_);
v___x_293_ = lean_nat_to_int(v_exponent_249_);
v_exp_294_ = lean_int_sub(v___x_292_, v___x_293_);
lean_dec(v___x_293_);
lean_dec(v___x_292_);
v___x_295_ = lean_int_dec_lt(v_exp_294_, v___x_252_);
if (v___x_295_ == 0)
{
lean_dec(v_exp_294_);
v___y_273_ = v___y_287_;
v___y_274_ = v_m_288_;
v___y_275_ = v___x_252_;
goto v___jp_272_;
}
else
{
v___y_273_ = v___y_287_;
v___y_274_ = v_m_288_;
v___y_275_ = v_exp_294_;
goto v___jp_272_;
}
}
}
else
{
lean_object* v___x_299_; 
lean_dec(v_exponent_249_);
v___x_299_ = l_Int_repr(v_mantissa_248_);
lean_dec(v_mantissa_248_);
return v___x_299_;
}
v___jp_238_:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
lean_inc_ref(v___y_239_);
v___x_243_ = lean_string_append(v___y_239_, v___y_240_);
lean_dec_ref(v___y_240_);
v___x_244_ = ((lean_object*)(l_Lean_JsonNumber_toString___closed__0));
v___x_245_ = lean_string_append(v___x_243_, v___x_244_);
v___x_246_ = lean_string_append(v___x_245_, v___y_241_);
lean_dec_ref(v___y_241_);
v___x_247_ = lean_string_append(v___x_246_, v___y_242_);
lean_dec_ref(v___y_242_);
return v___x_247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftl(lean_object* v_x_300_, lean_object* v_x_301_){
_start:
{
lean_object* v_mantissa_302_; lean_object* v_exponent_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_316_; 
v_mantissa_302_ = lean_ctor_get(v_x_300_, 0);
v_exponent_303_ = lean_ctor_get(v_x_300_, 1);
v_isSharedCheck_316_ = !lean_is_exclusive(v_x_300_);
if (v_isSharedCheck_316_ == 0)
{
v___x_305_ = v_x_300_;
v_isShared_306_ = v_isSharedCheck_316_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_exponent_303_);
lean_inc(v_mantissa_302_);
lean_dec(v_x_300_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_316_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_314_; 
v___x_307_ = lean_unsigned_to_nat(10u);
v___x_308_ = lean_nat_sub(v_x_301_, v_exponent_303_);
v___x_309_ = lean_nat_pow(v___x_307_, v___x_308_);
lean_dec(v___x_308_);
v___x_310_ = lean_nat_to_int(v___x_309_);
v___x_311_ = lean_int_mul(v_mantissa_302_, v___x_310_);
lean_dec(v___x_310_);
lean_dec(v_mantissa_302_);
v___x_312_ = lean_nat_sub(v_exponent_303_, v_x_301_);
lean_dec(v_exponent_303_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 1, v___x_312_);
lean_ctor_set(v___x_305_, 0, v___x_311_);
v___x_314_ = v___x_305_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v___x_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftl___boxed(lean_object* v_x_317_, lean_object* v_x_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_JsonNumber_shiftl(v_x_317_, v_x_318_);
lean_dec(v_x_318_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftr(lean_object* v_x_320_, lean_object* v_x_321_){
_start:
{
lean_object* v_mantissa_322_; lean_object* v_exponent_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_331_; 
v_mantissa_322_ = lean_ctor_get(v_x_320_, 0);
v_exponent_323_ = lean_ctor_get(v_x_320_, 1);
v_isSharedCheck_331_ = !lean_is_exclusive(v_x_320_);
if (v_isSharedCheck_331_ == 0)
{
v___x_325_ = v_x_320_;
v_isShared_326_ = v_isSharedCheck_331_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_exponent_323_);
lean_inc(v_mantissa_322_);
lean_dec(v_x_320_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_331_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_327_ = lean_nat_add(v_exponent_323_, v_x_321_);
lean_dec(v_exponent_323_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 1, v___x_327_);
v___x_329_ = v___x_325_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_mantissa_322_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_shiftr___boxed(lean_object* v_x_332_, lean_object* v_x_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_JsonNumber_shiftr(v_x_332_, v_x_333_);
lean_dec(v_x_333_);
return v_res_334_;
}
}
static lean_object* _init_l_Lean_JsonNumber_instRepr___lam__0___closed__4(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = ((lean_object*)(l_Lean_JsonNumber_instRepr___lam__0___closed__0));
v___x_343_ = lean_string_length(v___x_342_);
return v___x_343_;
}
}
static lean_object* _init_l_Lean_JsonNumber_instRepr___lam__0___closed__5(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_obj_once(&l_Lean_JsonNumber_instRepr___lam__0___closed__4, &l_Lean_JsonNumber_instRepr___lam__0___closed__4_once, _init_l_Lean_JsonNumber_instRepr___lam__0___closed__4);
v___x_345_ = lean_nat_to_int(v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instRepr___lam__0(lean_object* v_x_350_, lean_object* v_x_351_){
_start:
{
lean_object* v_mantissa_352_; lean_object* v_exponent_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_382_; 
v_mantissa_352_ = lean_ctor_get(v_x_350_, 0);
v_exponent_353_ = lean_ctor_get(v_x_350_, 1);
v_isSharedCheck_382_ = !lean_is_exclusive(v_x_350_);
if (v_isSharedCheck_382_ == 0)
{
v___x_355_ = v_x_350_;
v_isShared_356_ = v_isSharedCheck_382_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_exponent_353_);
lean_inc(v_mantissa_352_);
lean_dec(v_x_350_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_382_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___y_358_; lean_object* v___x_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_374_ = lean_unsigned_to_nat(0u);
v___x_375_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v___x_376_ = lean_int_dec_lt(v_mantissa_352_, v___x_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = l_Int_repr(v_mantissa_352_);
lean_dec(v_mantissa_352_);
v___x_378_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
v___y_358_ = v___x_378_;
goto v___jp_357_;
}
else
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = l_Int_repr(v_mantissa_352_);
lean_dec(v_mantissa_352_);
v___x_380_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
v___x_381_ = l_Repr_addAppParen(v___x_380_, v___x_374_);
v___y_358_ = v___x_381_;
goto v___jp_357_;
}
v___jp_357_:
{
lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_359_ = ((lean_object*)(l_Lean_JsonNumber_instRepr___lam__0___closed__2));
if (v_isShared_356_ == 0)
{
lean_ctor_set_tag(v___x_355_, 5);
lean_ctor_set(v___x_355_, 1, v___x_359_);
lean_ctor_set(v___x_355_, 0, v___y_358_);
v___x_361_ = v___x_355_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___y_358_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v___x_359_);
v___x_361_ = v_reuseFailAlloc_373_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; uint8_t v___x_371_; lean_object* v___x_372_; 
v___x_362_ = l_Nat_reprFast(v_exponent_353_);
v___x_363_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
v___x_364_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_361_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
v___x_365_ = lean_obj_once(&l_Lean_JsonNumber_instRepr___lam__0___closed__5, &l_Lean_JsonNumber_instRepr___lam__0___closed__5_once, _init_l_Lean_JsonNumber_instRepr___lam__0___closed__5);
v___x_366_ = ((lean_object*)(l_Lean_JsonNumber_instRepr___lam__0___closed__6));
v___x_367_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set(v___x_367_, 1, v___x_364_);
v___x_368_ = ((lean_object*)(l_Lean_JsonNumber_instRepr___lam__0___closed__7));
v___x_369_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_367_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
v___x_370_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_365_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
v___x_371_ = 0;
v___x_372_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_372_, 0, v___x_370_);
lean_ctor_set_uint8(v___x_372_, sizeof(void*)*1, v___x_371_);
return v___x_372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_instRepr___lam__0___boxed(lean_object* v_x_383_, lean_object* v_x_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_JsonNumber_instRepr___lam__0(v_x_383_, v_x_384_);
lean_dec(v_x_384_);
return v_res_385_;
}
}
lean_object* l_Lean_JsonNumber_instOfScientific___lam__0(lean_object* v_mantissa_388_, uint8_t v_exponentSign_389_, lean_object* v_decimalExponent_390_){
_start:
{
if (v_exponentSign_389_ == 0)
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_391_ = lean_unsigned_to_nat(10u);
v___x_392_ = lean_nat_pow(v___x_391_, v_decimalExponent_390_);
lean_dec(v_decimalExponent_390_);
v___x_393_ = lean_nat_mul(v_mantissa_388_, v___x_392_);
lean_dec(v___x_392_);
lean_dec(v_mantissa_388_);
v___x_394_ = lean_nat_to_int(v___x_393_);
v___x_395_ = lean_unsigned_to_nat(0u);
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_394_);
lean_ctor_set(v___x_396_, 1, v___x_395_);
return v___x_396_;
}
else
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = lean_nat_to_int(v_mantissa_388_);
v___x_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v_decimalExponent_390_);
return v___x_398_;
}
}
}
LEAN_EXPORT void l_Lean_JsonNumber_instOfScientific___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mantissa_388_ = stack[0].m_obj;
uint8_t v_exponentSign_389_ = stack[1].m_num;
lean_object* v_decimalExponent_390_ = stack[2].m_obj;
lean_object* v_res_399_;
v_res_399_ = l_Lean_JsonNumber_instOfScientific___lam__0(v_mantissa_388_, v_exponentSign_389_, v_decimalExponent_390_);
stack->m_obj
 = v_res_399_;
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
double l_Lean_JsonNumber_toFloat(lean_object* v_x_429_){
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
LEAN_EXPORT void l_Lean_JsonNumber_toFloat_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_429_ = stack[0].m_obj;
double v_res_444_;
v_res_444_ = l_Lean_JsonNumber_toFloat(v_x_429_);
stack->m_float
 = v_res_444_;
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_toFloat___boxed(lean_object* v_x_445_){
_start:
{
double v_res_446_; lean_object* v_r_447_; 
v_res_446_ = l_Lean_JsonNumber_toFloat(v_x_445_);
v_r_447_ = lean_box_float(v_res_446_);
return v_r_447_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21_spec__0(lean_object* v_msg_448_){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = l_Lean_JsonNumber_instInhabited;
v___x_450_ = lean_panic_fn_borrowed(v___x_449_, v_msg_448_);
return v___x_450_;
}
}
lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(double v_x_454_){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_float_to_string(v_x_454_);
v___x_456_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v___x_455_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_457_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0));
v___x_458_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__1));
v___x_459_ = lean_unsigned_to_nat(164u);
v___x_460_ = lean_unsigned_to_nat(12u);
v___x_461_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__2));
v___x_462_ = lean_string_append(v___x_461_, v___x_455_);
lean_dec_ref(v___x_455_);
v___x_463_ = l_mkPanicMessageWithDecl(v___x_457_, v___x_458_, v___x_459_, v___x_460_, v___x_462_);
lean_dec_ref(v___x_462_);
v___x_464_ = l_panic___at___00__private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21_spec__0(v___x_463_);
return v___x_464_;
}
else
{
lean_object* v_val_465_; lean_object* v_snd_466_; lean_object* v_fst_467_; uint8_t v___x_468_; 
lean_dec_ref(v___x_455_);
v_val_465_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_val_465_);
lean_dec_ref_known(v___x_456_, 1);
v_snd_466_ = lean_ctor_get(v_val_465_, 1);
lean_inc(v_snd_466_);
v_fst_467_ = lean_ctor_get(v_snd_466_, 0);
v___x_468_ = lean_unbox(v_fst_467_);
if (v___x_468_ == 0)
{
lean_object* v_fst_469_; lean_object* v_snd_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_482_; 
v_fst_469_ = lean_ctor_get(v_val_465_, 0);
lean_inc(v_fst_469_);
lean_dec(v_val_465_);
v_snd_470_ = lean_ctor_get(v_snd_466_, 1);
v_isSharedCheck_482_ = !lean_is_exclusive(v_snd_466_);
if (v_isSharedCheck_482_ == 0)
{
lean_object* v_unused_483_; 
v_unused_483_ = lean_ctor_get(v_snd_466_, 0);
lean_dec(v_unused_483_);
v___x_472_ = v_snd_466_;
v_isShared_473_ = v_isSharedCheck_482_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_snd_470_);
lean_dec(v_snd_466_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_482_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_474_ = lean_unsigned_to_nat(10u);
v___x_475_ = lean_nat_pow(v___x_474_, v_snd_470_);
lean_dec(v_snd_470_);
v___x_476_ = lean_nat_mul(v_fst_469_, v___x_475_);
lean_dec(v___x_475_);
lean_dec(v_fst_469_);
v___x_477_ = lean_nat_to_int(v___x_476_);
v___x_478_ = lean_unsigned_to_nat(0u);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 1, v___x_478_);
lean_ctor_set(v___x_472_, 0, v___x_477_);
v___x_480_ = v___x_472_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_477_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v___x_478_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
else
{
lean_object* v_fst_484_; lean_object* v_snd_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_493_; 
v_fst_484_ = lean_ctor_get(v_val_465_, 0);
lean_inc(v_fst_484_);
lean_dec(v_val_465_);
v_snd_485_ = lean_ctor_get(v_snd_466_, 1);
v_isSharedCheck_493_ = !lean_is_exclusive(v_snd_466_);
if (v_isSharedCheck_493_ == 0)
{
lean_object* v_unused_494_; 
v_unused_494_ = lean_ctor_get(v_snd_466_, 0);
lean_dec(v_unused_494_);
v___x_487_ = v_snd_466_;
v_isShared_488_ = v_isSharedCheck_493_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_snd_485_);
lean_dec(v_snd_466_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_493_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_489_ = lean_nat_to_int(v_fst_484_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 0, v___x_489_);
v___x_491_ = v___x_487_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_snd_485_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21_0interp(lean_interpreter_value* stack)
{
double v_x_454_ = stack[0].m_float;
lean_object* v_res_495_;
v_res_495_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(v_x_454_);
stack->m_obj
 = v_res_495_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___boxed(lean_object* v_x_496_){
_start:
{
double v_x_boxed_497_; lean_object* v_res_498_; 
v_x_boxed_497_ = lean_unbox_float(v_x_496_);
lean_dec_ref(v_x_496_);
v_res_498_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(v_x_boxed_497_);
return v_res_498_;
}
}
static double _init_l_Lean_JsonNumber_fromFloat_x3f___closed__0(void){
_start:
{
lean_object* v___x_499_; uint8_t v___x_500_; lean_object* v___x_501_; double v___x_502_; 
v___x_499_ = lean_unsigned_to_nat(1u);
v___x_500_ = 1;
v___x_501_ = lean_unsigned_to_nat(0u);
v___x_502_ = l_Float_ofScientific(v___x_501_, v___x_500_, v___x_499_);
return v___x_502_;
}
}
static lean_object* _init_l_Lean_JsonNumber_fromFloat_x3f___closed__1(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_obj_once(&l_Lean_JsonNumber_instInhabited___closed__0, &l_Lean_JsonNumber_instInhabited___closed__0_once, _init_l_Lean_JsonNumber_instInhabited___closed__0);
v___x_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
return v___x_504_;
}
}
static double _init_l_Lean_JsonNumber_fromFloat_x3f___closed__2(void){
_start:
{
lean_object* v___x_505_; double v___x_506_; 
v___x_505_ = lean_unsigned_to_nat(0u);
v___x_506_ = lean_float_of_nat(v___x_505_);
return v___x_506_;
}
}
lean_object* l_Lean_JsonNumber_fromFloat_x3f(double v_x_516_){
_start:
{
uint8_t v___x_517_; 
v___x_517_ = lean_float_isnan(v_x_516_);
if (v___x_517_ == 0)
{
uint8_t v___x_518_; 
v___x_518_ = lean_float_isinf(v_x_516_);
if (v___x_518_ == 0)
{
double v___x_519_; uint8_t v___x_520_; 
v___x_519_ = lean_float_once(&l_Lean_JsonNumber_fromFloat_x3f___closed__0, &l_Lean_JsonNumber_fromFloat_x3f___closed__0_once, _init_l_Lean_JsonNumber_fromFloat_x3f___closed__0);
v___x_520_ = lean_float_beq(v_x_516_, v___x_519_);
if (v___x_520_ == 0)
{
uint8_t v___x_521_; 
v___x_521_ = lean_float_decLt(v_x_516_, v___x_519_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(v_x_516_);
v___x_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
else
{
double v___x_524_; lean_object* v___x_525_; lean_object* v_mantissa_526_; lean_object* v_exponent_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_536_; 
v___x_524_ = lean_float_negate(v_x_516_);
v___x_525_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(v___x_524_);
v_mantissa_526_ = lean_ctor_get(v___x_525_, 0);
v_exponent_527_ = lean_ctor_get(v___x_525_, 1);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_536_ == 0)
{
v___x_529_ = v___x_525_;
v_isShared_530_ = v_isSharedCheck_536_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_exponent_527_);
lean_inc(v_mantissa_526_);
lean_dec(v___x_525_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_536_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_531_; lean_object* v___x_533_; 
v___x_531_ = lean_int_neg(v_mantissa_526_);
lean_dec(v_mantissa_526_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v___x_531_);
v___x_533_ = v___x_529_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_531_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_exponent_527_);
v___x_533_ = v_reuseFailAlloc_535_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_534_; 
v___x_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
}
}
}
else
{
lean_object* v___x_537_; 
v___x_537_ = lean_obj_once(&l_Lean_JsonNumber_fromFloat_x3f___closed__1, &l_Lean_JsonNumber_fromFloat_x3f___closed__1_once, _init_l_Lean_JsonNumber_fromFloat_x3f___closed__1);
return v___x_537_;
}
}
else
{
double v___x_538_; uint8_t v___x_539_; 
v___x_538_ = lean_float_once(&l_Lean_JsonNumber_fromFloat_x3f___closed__2, &l_Lean_JsonNumber_fromFloat_x3f___closed__2_once, _init_l_Lean_JsonNumber_fromFloat_x3f___closed__2);
v___x_539_ = lean_float_decLt(v___x_538_, v_x_516_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; 
v___x_540_ = ((lean_object*)(l_Lean_JsonNumber_fromFloat_x3f___closed__4));
return v___x_540_;
}
else
{
lean_object* v___x_541_; 
v___x_541_ = ((lean_object*)(l_Lean_JsonNumber_fromFloat_x3f___closed__6));
return v___x_541_;
}
}
}
else
{
lean_object* v___x_542_; 
v___x_542_ = ((lean_object*)(l_Lean_JsonNumber_fromFloat_x3f___closed__8));
return v___x_542_;
}
}
}
LEAN_EXPORT void l_Lean_JsonNumber_fromFloat_x3f_0interp(lean_interpreter_value* stack)
{
double v_x_516_ = stack[0].m_float;
lean_object* v_res_543_;
v_res_543_ = l_Lean_JsonNumber_fromFloat_x3f(v_x_516_);
stack->m_obj
 = v_res_543_;
}
LEAN_EXPORT lean_object* l_Lean_JsonNumber_fromFloat_x3f___boxed(lean_object* v_x_544_){
_start:
{
double v_x_boxed_545_; lean_object* v_res_546_; 
v_x_boxed_545_ = lean_unbox_float(v_x_544_);
lean_dec_ref(v_x_544_);
v_res_546_ = l_Lean_JsonNumber_fromFloat_x3f(v_x_boxed_545_);
return v_res_546_;
}
}
uint8_t l_Lean_strLt(lean_object* v_a_547_, lean_object* v_b_548_){
_start:
{
uint8_t v___x_549_; 
v___x_549_ = lean_string_dec_lt(v_a_547_, v_b_548_);
return v___x_549_;
}
}
LEAN_EXPORT void l_Lean_strLt_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_547_ = stack[0].m_obj;
lean_object* v_b_548_ = stack[1].m_obj;
uint8_t v_res_550_;
v_res_550_ = l_Lean_strLt(v_a_547_, v_b_548_);
stack->m_num = v_res_550_;
}
LEAN_EXPORT lean_object* l_Lean_strLt___boxed(lean_object* v_a_551_, lean_object* v_b_552_){
_start:
{
uint8_t v_res_553_; lean_object* v_r_554_; 
v_res_553_ = l_Lean_strLt(v_a_551_, v_b_552_);
lean_dec_ref(v_b_552_);
lean_dec_ref(v_a_551_);
v_r_554_ = lean_box(v_res_553_);
return v_r_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorIdx___impl(lean_object* v_x_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = lean_obj_tag_nat(v_x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorIdx___impl___boxed(lean_object* v_x_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_Json_ctorIdx___impl(v_x_557_);
lean_dec(v_x_557_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorElim___redArg(lean_object* v_t_559_, lean_object* v_k_560_){
_start:
{
switch(lean_obj_tag(v_t_559_))
{
case 0:
{
return v_k_560_;
}
case 1:
{
uint8_t v_b_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v_b_561_ = lean_ctor_get_uint8(v_t_559_, 0);
lean_dec_ref_known(v_t_559_, 0);
v___x_562_ = lean_box(v_b_561_);
v___x_563_ = lean_apply_1(v_k_560_, v___x_562_);
return v___x_563_;
}
case 5:
{
lean_object* v_kvPairs_564_; lean_object* v___x_565_; 
v_kvPairs_564_ = lean_ctor_get(v_t_559_, 0);
lean_inc(v_kvPairs_564_);
lean_dec_ref_known(v_t_559_, 1);
v___x_565_ = lean_apply_1(v_k_560_, v_kvPairs_564_);
return v___x_565_;
}
default: 
{
lean_object* v_n_566_; lean_object* v___x_567_; 
v_n_566_ = lean_ctor_get(v_t_559_, 0);
lean_inc_ref(v_n_566_);
lean_dec(v_t_559_);
v___x_567_ = lean_apply_1(v_k_560_, v_n_566_);
return v___x_567_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorElim(lean_object* v_motive__1_568_, lean_object* v_ctorIdx_569_, lean_object* v_t_570_, lean_object* v_h_571_, lean_object* v_k_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_Json_ctorElim___redArg(v_t_570_, v_k_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_ctorElim___boxed(lean_object* v_motive__1_574_, lean_object* v_ctorIdx_575_, lean_object* v_t_576_, lean_object* v_h_577_, lean_object* v_k_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_Json_ctorElim(v_motive__1_574_, v_ctorIdx_575_, v_t_576_, v_h_577_, v_k_578_);
lean_dec(v_ctorIdx_575_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_null_elim___redArg(lean_object* v_t_580_, lean_object* v_null_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_Json_ctorElim___redArg(v_t_580_, v_null_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_null_elim(lean_object* v_motive__1_583_, lean_object* v_t_584_, lean_object* v_h_585_, lean_object* v_null_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_Json_ctorElim___redArg(v_t_584_, v_null_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_bool_elim___redArg(lean_object* v_t_588_, lean_object* v_bool_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_Json_ctorElim___redArg(v_t_588_, v_bool_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_bool_elim(lean_object* v_motive__1_591_, lean_object* v_t_592_, lean_object* v_h_593_, lean_object* v_bool_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_Json_ctorElim___redArg(v_t_592_, v_bool_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_num_elim___redArg(lean_object* v_t_596_, lean_object* v_num_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_Json_ctorElim___redArg(v_t_596_, v_num_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_num_elim(lean_object* v_motive__1_599_, lean_object* v_t_600_, lean_object* v_h_601_, lean_object* v_num_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_Json_ctorElim___redArg(v_t_600_, v_num_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_str_elim___redArg(lean_object* v_t_604_, lean_object* v_str_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lean_Json_ctorElim___redArg(v_t_604_, v_str_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_str_elim(lean_object* v_motive__1_607_, lean_object* v_t_608_, lean_object* v_h_609_, lean_object* v_str_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lean_Json_ctorElim___redArg(v_t_608_, v_str_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_arr_elim___redArg(lean_object* v_t_612_, lean_object* v_arr_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_Json_ctorElim___redArg(v_t_612_, v_arr_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_arr_elim(lean_object* v_motive__1_615_, lean_object* v_t_616_, lean_object* v_h_617_, lean_object* v_arr_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Lean_Json_ctorElim___redArg(v_t_616_, v_arr_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_obj_elim___redArg(lean_object* v_t_620_, lean_object* v_obj_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_Json_ctorElim___redArg(v_t_620_, v_obj_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_obj_elim(lean_object* v_motive__1_623_, lean_object* v_t_624_, lean_object* v_h_625_, lean_object* v_obj_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_Json_ctorElim___redArg(v_t_624_, v_obj_626_);
return v___x_627_;
}
}
static lean_object* _init_l_Lean_instInhabitedJson_default(void){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = lean_box(0);
return v___x_628_;
}
}
static lean_object* _init_l_Lean_instInhabitedJson(void){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = lean_box(0);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(lean_object* v_init_630_, lean_object* v_x_631_){
_start:
{
if (lean_obj_tag(v_x_631_) == 0)
{
lean_object* v_l_632_; lean_object* v_r_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v_l_632_ = lean_ctor_get(v_x_631_, 3);
v_r_633_ = lean_ctor_get(v_x_631_, 4);
v___x_634_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_630_, v_l_632_);
v___x_635_ = lean_unsigned_to_nat(1u);
v___x_636_ = lean_nat_add(v___x_634_, v___x_635_);
lean_dec(v___x_634_);
v_init_630_ = v___x_636_;
v_x_631_ = v_r_633_;
goto _start;
}
else
{
return v_init_630_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1___boxed(lean_object* v_init_638_, lean_object* v_x_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_638_, v_x_639_);
lean_dec(v_x_639_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(lean_object* v_t_641_, lean_object* v_k_642_){
_start:
{
if (lean_obj_tag(v_t_641_) == 0)
{
lean_object* v_k_643_; lean_object* v_v_644_; lean_object* v_l_645_; lean_object* v_r_646_; uint8_t v___x_647_; 
v_k_643_ = lean_ctor_get(v_t_641_, 1);
v_v_644_ = lean_ctor_get(v_t_641_, 2);
v_l_645_ = lean_ctor_get(v_t_641_, 3);
v_r_646_ = lean_ctor_get(v_t_641_, 4);
v___x_647_ = lean_string_compare(v_k_642_, v_k_643_);
switch(v___x_647_)
{
case 0:
{
v_t_641_ = v_l_645_;
goto _start;
}
case 1:
{
lean_object* v___x_649_; 
lean_inc(v_v_644_);
v___x_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_649_, 0, v_v_644_);
return v___x_649_;
}
default: 
{
v_t_641_ = v_r_646_;
goto _start;
}
}
}
else
{
lean_object* v___x_651_; 
v___x_651_ = lean_box(0);
return v___x_651_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg___boxed(lean_object* v_t_652_, lean_object* v_k_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_t_652_, v_k_653_);
lean_dec_ref(v_k_653_);
lean_dec(v_t_652_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(lean_object* v_szA_666_, lean_object* v_szB_667_, lean_object* v_kvPairs_668_, lean_object* v_init_669_, lean_object* v_x_670_){
_start:
{
if (lean_obj_tag(v_x_670_) == 0)
{
lean_object* v_k_671_; lean_object* v_v_672_; lean_object* v_l_673_; lean_object* v_r_674_; uint8_t v___x_675_; lean_object* v___x_676_; 
v_k_671_ = lean_ctor_get(v_x_670_, 1);
v_v_672_ = lean_ctor_get(v_x_670_, 2);
v_l_673_ = lean_ctor_get(v_x_670_, 3);
v_r_674_ = lean_ctor_get(v_x_670_, 4);
v___x_675_ = lean_nat_dec_eq(v_szA_666_, v_szB_667_);
v___x_676_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_szA_666_, v_szB_667_, v_kvPairs_668_, v_init_669_, v_l_673_);
if (lean_obj_tag(v___x_676_) == 0)
{
return v___x_676_;
}
else
{
lean_object* v___x_677_; lean_object* v___x_681_; 
lean_dec_ref_known(v___x_676_, 1);
v___x_677_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__0));
v___x_681_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_kvPairs_668_, v_k_671_);
if (lean_obj_tag(v___x_681_) == 0)
{
goto v___jp_678_;
}
else
{
lean_object* v_val_682_; uint8_t v___x_683_; 
v_val_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_val_682_);
lean_dec_ref_known(v___x_681_, 1);
v___x_683_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_v_672_, v_val_682_);
lean_dec(v_val_682_);
if (v___x_683_ == 0)
{
goto v___jp_678_;
}
else
{
v_init_669_ = v___x_677_;
v_x_670_ = v_r_674_;
goto _start;
}
}
v___jp_678_:
{
if (v___x_675_ == 0)
{
v_init_669_ = v___x_677_;
v_x_670_ = v_r_674_;
goto _start;
}
else
{
lean_object* v___x_680_; 
v___x_680_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__3));
return v___x_680_;
}
}
}
}
else
{
lean_object* v___x_685_; 
v___x_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_685_, 0, v_init_669_);
return v___x_685_;
}
}
}
uint8_t l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(lean_object* v_x_686_, lean_object* v_x_687_){
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
v_b_690_ = lean_ctor_get_uint8(v_x_687_, 0);
if (v_b_690_ == 0)
{
uint8_t v_b_691_; 
v_b_691_ = lean_ctor_get_uint8(v_x_686_, 0);
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
v_b_693_ = lean_ctor_get_uint8(v_x_686_, 0);
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
if (v___x_715_ == 0)
{
lean_dec(v_szB_714_);
lean_dec(v_szA_713_);
return v___x_715_;
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v_a_723_; 
v___x_721_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__0));
v___x_722_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_szA_713_, v_szB_714_, v_kvPairs_711_, v___x_721_, v_kvPairs_710_);
lean_dec(v_szB_714_);
lean_dec(v_szA_713_);
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
LEAN_EXPORT void l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_686_ = stack[0].m_obj;
lean_object* v_x_687_ = stack[1].m_obj;
uint8_t v_res_725_;
v_res_725_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_x_686_, v_x_687_);
stack->m_num = v_res_725_;
}
uint8_t l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(lean_object* v_xs_726_, lean_object* v_ys_727_, lean_object* v_x_728_){
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
LEAN_EXPORT void l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_726_ = stack[0].m_obj;
lean_object* v_ys_727_ = stack[1].m_obj;
lean_object* v_x_728_ = stack[2].m_obj;
uint8_t v_res_737_;
v_res_737_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(v_xs_726_, v_ys_727_, v_x_728_);
stack->m_num = v_res_737_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg___boxed(lean_object* v_xs_738_, lean_object* v_ys_739_, lean_object* v_x_740_){
_start:
{
uint8_t v_res_741_; lean_object* v_r_742_; 
v_res_741_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(v_xs_738_, v_ys_739_, v_x_740_);
lean_dec_ref(v_ys_739_);
lean_dec_ref(v_xs_738_);
v_r_742_ = lean_box(v_res_741_);
return v_r_742_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___boxed(lean_object* v_szA_743_, lean_object* v_szB_744_, lean_object* v_kvPairs_745_, lean_object* v_init_746_, lean_object* v_x_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_szA_743_, v_szB_744_, v_kvPairs_745_, v_init_746_, v_x_747_);
lean_dec(v_x_747_);
lean_dec(v_kvPairs_745_);
lean_dec(v_szB_744_);
lean_dec(v_szA_743_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___boxed(lean_object* v_x_749_, lean_object* v_x_750_){
_start:
{
uint8_t v_res_751_; lean_object* v_r_752_; 
v_res_751_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_x_749_, v_x_750_);
lean_dec(v_x_750_);
lean_dec(v_x_749_);
v_r_752_ = lean_box(v_res_751_);
return v_r_752_;
}
}
uint8_t l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0(lean_object* v_xs_753_, lean_object* v_ys_754_, lean_object* v_hsz_755_, lean_object* v_x_756_, lean_object* v_x_757_){
_start:
{
uint8_t v___x_758_; 
v___x_758_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(v_xs_753_, v_ys_754_, v_x_756_);
return v___x_758_;
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_753_ = stack[0].m_obj;
lean_object* v_ys_754_ = stack[1].m_obj;
lean_object* v_x_756_ = stack[3].m_obj;
uint8_t v_res_759_;
v_res_759_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0(v_xs_753_, v_ys_754_, lean_box(0), v_x_756_, lean_box(0));
stack->m_num = v_res_759_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___boxed(lean_object* v_xs_760_, lean_object* v_ys_761_, lean_object* v_hsz_762_, lean_object* v_x_763_, lean_object* v_x_764_){
_start:
{
uint8_t v_res_765_; lean_object* v_r_766_; 
v_res_765_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0(v_xs_760_, v_ys_761_, v_hsz_762_, v_x_763_, v_x_764_);
lean_dec_ref(v_ys_761_);
lean_dec_ref(v_xs_760_);
v_r_766_ = lean_box(v_res_765_);
return v_r_766_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1(lean_object* v_init_767_, lean_object* v_t_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_767_, v_t_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___boxed(lean_object* v_init_770_, lean_object* v_t_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1(v_init_770_, v_t_771_);
lean_dec(v_t_771_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2(lean_object* v_00_u03b4_773_, lean_object* v_t_774_, lean_object* v_k_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_t_774_, v_k_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___boxed(lean_object* v_00_u03b4_777_, lean_object* v_t_778_, lean_object* v_k_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2(v_00_u03b4_777_, v_t_778_, v_k_779_);
lean_dec_ref(v_k_779_);
lean_dec(v_t_778_);
return v_res_780_;
}
}
uint8_t l_Lean_Json_instBEq___private__1(lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
uint8_t v___x_783_; 
v___x_783_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_a_781_, v_a_782_);
return v___x_783_;
}
}
LEAN_EXPORT void l_Lean_Json_instBEq___private__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_781_ = stack[0].m_obj;
lean_object* v_a_782_ = stack[1].m_obj;
uint8_t v_res_784_;
v_res_784_ = l_Lean_Json_instBEq___private__1(v_a_781_, v_a_782_);
stack->m_num = v_res_784_;
}
LEAN_EXPORT lean_object* l_Lean_Json_instBEq___private__1___boxed(lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
uint8_t v_res_787_; lean_object* v_r_788_; 
v_res_787_ = l_Lean_Json_instBEq___private__1(v_a_785_, v_a_786_);
lean_dec(v_a_786_);
lean_dec(v_a_785_);
v_r_788_ = lean_box(v_res_787_);
return v_r_788_;
}
}
uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(lean_object* v_as_791_, size_t v_i_792_, size_t v_stop_793_, uint64_t v_b_794_){
_start:
{
uint8_t v___x_795_; 
v___x_795_ = lean_usize_dec_eq(v_i_792_, v_stop_793_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; uint64_t v___x_797_; uint64_t v___x_798_; size_t v___x_799_; size_t v___x_800_; 
v___x_796_ = lean_array_uget_borrowed(v_as_791_, v_i_792_);
v___x_797_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v___x_796_);
v___x_798_ = lean_uint64_mix_hash(v_b_794_, v___x_797_);
v___x_799_ = ((size_t)1ULL);
v___x_800_ = lean_usize_add(v_i_792_, v___x_799_);
v_i_792_ = v___x_800_;
v_b_794_ = v___x_798_;
goto _start;
}
else
{
return v_b_794_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_791_ = stack[0].m_obj;
size_t v_i_792_ = stack[1].m_num;
size_t v_stop_793_ = stack[2].m_num;
uint64_t v_b_794_ = stack[3].m_num;
uint64_t v_res_802_;
v_res_802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_as_791_, v_i_792_, v_stop_793_, v_b_794_);
stack->m_num = v_res_802_;
}
uint64_t l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(lean_object* v_x_803_){
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
v___x_806_ = 889925284873970544ULL;
return v___x_806_;
}
else
{
uint64_t v___x_807_; 
v___x_807_ = 7849220421742680397ULL;
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
lean_object* v_elems_816_; lean_object* v___x_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v_elems_816_ = lean_ctor_get(v_x_803_, 0);
v___x_817_ = lean_unsigned_to_nat(0u);
v___x_818_ = lean_array_get_size(v_elems_816_);
v___x_819_ = lean_nat_dec_lt(v___x_817_, v___x_818_);
if (v___x_819_ == 0)
{
uint64_t v___x_820_; 
v___x_820_ = 179905158410471120ULL;
return v___x_820_;
}
else
{
uint64_t v___x_821_; uint64_t v___x_822_; uint8_t v___x_823_; 
v___x_821_ = 23ULL;
v___x_822_ = 7ULL;
v___x_823_ = lean_nat_dec_le(v___x_818_, v___x_818_);
if (v___x_823_ == 0)
{
if (v___x_819_ == 0)
{
uint64_t v___x_824_; 
v___x_824_ = 179905158410471120ULL;
return v___x_824_;
}
else
{
size_t v___x_825_; size_t v___x_826_; uint64_t v___x_827_; uint64_t v___x_828_; 
v___x_825_ = ((size_t)0ULL);
v___x_826_ = lean_usize_of_nat(v___x_818_);
v___x_827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_elems_816_, v___x_825_, v___x_826_, v___x_822_);
v___x_828_ = lean_uint64_mix_hash(v___x_821_, v___x_827_);
return v___x_828_;
}
}
else
{
size_t v___x_829_; size_t v___x_830_; uint64_t v___x_831_; uint64_t v___x_832_; 
v___x_829_ = ((size_t)0ULL);
v___x_830_ = lean_usize_of_nat(v___x_818_);
v___x_831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_elems_816_, v___x_829_, v___x_830_, v___x_822_);
v___x_832_ = lean_uint64_mix_hash(v___x_821_, v___x_831_);
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
LEAN_EXPORT void l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_803_ = stack[0].m_obj;
uint64_t v_res_838_;
v_res_838_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_x_803_);
stack->m_num = v_res_838_;
}
uint64_t l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(uint64_t v_init_839_, lean_object* v_x_840_){
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
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
uint64_t v_init_839_ = stack[0].m_num;
lean_object* v_x_840_ = stack[1].m_obj;
uint64_t v_res_851_;
v_res_851_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_839_, v_x_840_);
stack->m_num = v_res_851_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1___boxed(lean_object* v_init_852_, lean_object* v_x_853_){
_start:
{
uint64_t v_init_boxed_854_; uint64_t v_res_855_; lean_object* v_r_856_; 
v_init_boxed_854_ = lean_unbox_uint64(v_init_852_);
lean_dec_ref(v_init_852_);
v_res_855_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_boxed_854_, v_x_853_);
lean_dec(v_x_853_);
v_r_856_ = lean_box_uint64(v_res_855_);
return v_r_856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0___boxed(lean_object* v_as_857_, lean_object* v_i_858_, lean_object* v_stop_859_, lean_object* v_b_860_){
_start:
{
size_t v_i_boxed_861_; size_t v_stop_boxed_862_; uint64_t v_b_boxed_863_; uint64_t v_res_864_; lean_object* v_r_865_; 
v_i_boxed_861_ = lean_unbox_usize(v_i_858_);
lean_dec(v_i_858_);
v_stop_boxed_862_ = lean_unbox_usize(v_stop_859_);
lean_dec(v_stop_859_);
v_b_boxed_863_ = lean_unbox_uint64(v_b_860_);
lean_dec_ref(v_b_860_);
v_res_864_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_as_857_, v_i_boxed_861_, v_stop_boxed_862_, v_b_boxed_863_);
lean_dec_ref(v_as_857_);
v_r_865_ = lean_box_uint64(v_res_864_);
return v_r_865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___boxed(lean_object* v_x_866_){
_start:
{
uint64_t v_res_867_; lean_object* v_r_868_; 
v_res_867_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_x_866_);
lean_dec(v_x_866_);
v_r_868_ = lean_box_uint64(v_res_867_);
return v_r_868_;
}
}
uint64_t l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1(uint64_t v_init_869_, lean_object* v_t_870_){
_start:
{
uint64_t v___x_871_; 
v___x_871_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_869_, v_t_870_);
return v___x_871_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_0interp(lean_interpreter_value* stack)
{
uint64_t v_init_869_ = stack[0].m_num;
lean_object* v_t_870_ = stack[1].m_obj;
uint64_t v_res_872_;
v_res_872_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1(v_init_869_, v_t_870_);
stack->m_num = v_res_872_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1___boxed(lean_object* v_init_873_, lean_object* v_t_874_){
_start:
{
uint64_t v_init_boxed_875_; uint64_t v_res_876_; lean_object* v_r_877_; 
v_init_boxed_875_ = lean_unbox_uint64(v_init_873_);
lean_dec_ref(v_init_873_);
v_res_876_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1(v_init_boxed_875_, v_t_874_);
lean_dec(v_t_874_);
v_r_877_ = lean_box_uint64(v_res_876_);
return v_r_877_;
}
}
uint64_t l_Lean_Json_instHashable___private__1(lean_object* v_a_878_){
_start:
{
uint64_t v___x_879_; 
v___x_879_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_a_878_);
return v___x_879_;
}
}
LEAN_EXPORT void l_Lean_Json_instHashable___private__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_878_ = stack[0].m_obj;
uint64_t v_res_880_;
v_res_880_ = l_Lean_Json_instHashable___private__1(v_a_878_);
stack->m_num = v_res_880_;
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
v_k_902_ = lean_ctor_get(v_impl_898_, 1);
v_v_903_ = lean_ctor_get(v_impl_898_, 2);
v_l_904_ = lean_ctor_get(v_impl_898_, 3);
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
v___x_909_ = lean_nat_add(v___x_899_, v_size_901_);
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
lean_inc(v_l_904_);
lean_inc(v_v_903_);
lean_inc(v_k_902_);
lean_inc(v_size_901_);
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
v___x_935_ = lean_nat_add(v___y_933_, v___y_934_);
lean_dec(v___y_934_);
lean_dec(v___y_933_);
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
lean_ctor_set(v___x_915_, 3, v___y_932_);
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
lean_ctor_set(v_reuseFailAlloc_940_, 3, v___y_932_);
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
v___y_932_ = v___x_947_;
v___y_933_ = v___x_948_;
v___y_934_ = v_size_949_;
goto v___jp_931_;
}
else
{
lean_object* v___x_950_; 
v___x_950_ = lean_unsigned_to_nat(0u);
v___y_932_ = v___x_947_;
v___y_933_ = v___x_948_;
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
if (lean_obj_tag(v_l_985_) == 0)
{
lean_object* v_r_986_; lean_object* v_k_987_; lean_object* v_v_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_999_; 
lean_inc_ref(v_l_985_);
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
lean_inc(v_l_985_);
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
v_k_1042_ = lean_ctor_get(v_impl_1038_, 1);
v_v_1043_ = lean_ctor_get(v_impl_1038_, 2);
v_l_1044_ = lean_ctor_get(v_impl_1038_, 3);
lean_inc(v_l_1044_);
v_r_1045_ = lean_ctor_get(v_impl_1038_, 4);
v___x_1046_ = lean_unsigned_to_nat(3u);
v___x_1047_ = lean_nat_mul(v___x_1046_, v_size_1040_);
v___x_1048_ = lean_nat_dec_lt(v___x_1047_, v_size_1041_);
lean_dec(v___x_1047_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1052_; 
lean_dec(v_l_1044_);
v___x_1049_ = lean_nat_add(v___x_1039_, v_size_1040_);
v___x_1050_ = lean_nat_add(v___x_1049_, v_size_1041_);
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
lean_inc(v_r_1045_);
lean_inc(v_v_1043_);
lean_inc(v_k_1042_);
lean_inc(v_size_1041_);
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
v___x_1075_ = lean_nat_add(v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec(v___y_1073_);
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
lean_ctor_set(v___x_1055_, 3, v___y_1072_);
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
lean_ctor_set(v_reuseFailAlloc_1080_, 3, v___y_1072_);
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
v___y_1072_ = v___x_1086_;
v___y_1073_ = v___x_1087_;
v___y_1074_ = v_size_1088_;
goto v___jp_1071_;
}
else
{
lean_object* v___x_1089_; 
v___x_1089_ = lean_unsigned_to_nat(0u);
v___y_1072_ = v___x_1086_;
v___y_1073_ = v___x_1087_;
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
lean_object* l_Lean_Json_instCoeBool___lam__0(uint8_t v_b_1223_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1224_, 0, v_b_1223_);
return v___x_1224_;
}
}
LEAN_EXPORT void l_Lean_Json_instCoeBool___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_1223_ = stack[0].m_num;
lean_object* v_res_1225_;
v_res_1225_ = l_Lean_Json_instCoeBool___lam__0(v_b_1223_);
stack->m_obj
 = v_res_1225_;
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeBool___lam__0___boxed(lean_object* v_b_1226_){
_start:
{
uint8_t v_b_boxed_1227_; lean_object* v_res_1228_; 
v_b_boxed_1227_ = lean_unbox(v_b_1226_);
v_res_1228_ = l_Lean_Json_instCoeBool___lam__0(v_b_boxed_1227_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instOfNat(lean_object* v_n_1231_){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = l_Lean_JsonNumber_fromNat(v_n_1231_);
v___x_1233_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
return v___x_1233_;
}
}
uint8_t l_Lean_Json_isNull(lean_object* v_x_1234_){
_start:
{
if (lean_obj_tag(v_x_1234_) == 0)
{
uint8_t v___x_1235_; 
v___x_1235_ = 1;
return v___x_1235_;
}
else
{
uint8_t v___x_1236_; 
v___x_1236_ = 0;
return v___x_1236_;
}
}
}
LEAN_EXPORT void l_Lean_Json_isNull_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1234_ = stack[0].m_obj;
uint8_t v_res_1237_;
v_res_1237_ = l_Lean_Json_isNull(v_x_1234_);
stack->m_num = v_res_1237_;
}
LEAN_EXPORT lean_object* l_Lean_Json_isNull___boxed(lean_object* v_x_1238_){
_start:
{
uint8_t v_res_1239_; lean_object* v_r_1240_; 
v_res_1239_ = l_Lean_Json_isNull(v_x_1238_);
lean_dec(v_x_1238_);
v_r_1240_ = lean_box(v_res_1239_);
return v_r_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObj_x3f(lean_object* v_x_1244_){
_start:
{
if (lean_obj_tag(v_x_1244_) == 5)
{
lean_object* v_kvPairs_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
v_kvPairs_1245_ = lean_ctor_get(v_x_1244_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_x_1244_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v_x_1244_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_kvPairs_1245_);
lean_dec(v_x_1244_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
lean_ctor_set_tag(v___x_1247_, 1);
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_kvPairs_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
else
{
lean_object* v___x_1253_; 
lean_dec(v_x_1244_);
v___x_1253_ = ((lean_object*)(l_Lean_Json_getObj_x3f___closed__1));
return v___x_1253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getArr_x3f(lean_object* v_x_1257_){
_start:
{
if (lean_obj_tag(v_x_1257_) == 4)
{
lean_object* v_elems_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
v_elems_1258_ = lean_ctor_get(v_x_1257_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_x_1257_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v_x_1257_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_elems_1258_);
lean_dec(v_x_1257_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
lean_ctor_set_tag(v___x_1260_, 1);
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_elems_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
else
{
lean_object* v___x_1266_; 
lean_dec(v_x_1257_);
v___x_1266_ = ((lean_object*)(l_Lean_Json_getArr_x3f___closed__1));
return v___x_1266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getStr_x3f(lean_object* v_x_1270_){
_start:
{
if (lean_obj_tag(v_x_1270_) == 3)
{
lean_object* v_s_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
v_s_1271_ = lean_ctor_get(v_x_1270_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_x_1270_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v_x_1270_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_s_1271_);
lean_dec(v_x_1270_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
lean_ctor_set_tag(v___x_1273_, 1);
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_s_1271_);
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
lean_object* v___x_1279_; 
lean_dec(v_x_1270_);
v___x_1279_ = ((lean_object*)(l_Lean_Json_getStr_x3f___closed__1));
return v___x_1279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getNat_x3f(lean_object* v_x_1283_){
_start:
{
if (lean_obj_tag(v_x_1283_) == 2)
{
lean_object* v_n_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1300_; 
v_n_1286_ = lean_ctor_get(v_x_1283_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v_x_1283_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1288_ = v_x_1283_;
v_isShared_1289_ = v_isSharedCheck_1300_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_n_1286_);
lean_dec(v_x_1283_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1300_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v_mantissa_1290_; lean_object* v_exponent_1291_; lean_object* v_natZero_1292_; lean_object* v_intZero_1293_; uint8_t v_isNeg_1294_; 
v_mantissa_1290_ = lean_ctor_get(v_n_1286_, 0);
lean_inc(v_mantissa_1290_);
v_exponent_1291_ = lean_ctor_get(v_n_1286_, 1);
lean_inc(v_exponent_1291_);
lean_dec_ref(v_n_1286_);
v_natZero_1292_ = lean_unsigned_to_nat(0u);
v_intZero_1293_ = lean_obj_once(&l_Lean_instHashableJsonNumber_hash___closed__0, &l_Lean_instHashableJsonNumber_hash___closed__0_once, _init_l_Lean_instHashableJsonNumber_hash___closed__0);
v_isNeg_1294_ = lean_int_dec_lt(v_mantissa_1290_, v_intZero_1293_);
if (v_isNeg_1294_ == 0)
{
uint8_t v___x_1295_; 
v___x_1295_ = lean_nat_dec_eq(v_exponent_1291_, v_natZero_1292_);
lean_dec(v_exponent_1291_);
if (v___x_1295_ == 0)
{
lean_dec(v_mantissa_1290_);
lean_del_object(v___x_1288_);
goto v___jp_1284_;
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; 
v_a_1296_ = lean_nat_abs(v_mantissa_1290_);
lean_dec(v_mantissa_1290_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set_tag(v___x_1288_, 1);
lean_ctor_set(v___x_1288_, 0, v_a_1296_);
v___x_1298_ = v___x_1288_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1296_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
else
{
lean_dec(v_exponent_1291_);
lean_dec(v_mantissa_1290_);
lean_del_object(v___x_1288_);
goto v___jp_1284_;
}
}
}
else
{
lean_dec(v_x_1283_);
goto v___jp_1284_;
}
v___jp_1284_:
{
lean_object* v___x_1285_; 
v___x_1285_ = ((lean_object*)(l_Lean_Json_getNat_x3f___closed__1));
return v___x_1285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getInt_x3f(lean_object* v_x_1304_){
_start:
{
if (lean_obj_tag(v_x_1304_) == 2)
{
lean_object* v_n_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1318_; 
v_n_1307_ = lean_ctor_get(v_x_1304_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v_x_1304_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1309_ = v_x_1304_;
v_isShared_1310_ = v_isSharedCheck_1318_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_n_1307_);
lean_dec(v_x_1304_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1318_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v_mantissa_1311_; lean_object* v_exponent_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v_mantissa_1311_ = lean_ctor_get(v_n_1307_, 0);
lean_inc(v_mantissa_1311_);
v_exponent_1312_ = lean_ctor_get(v_n_1307_, 1);
lean_inc(v_exponent_1312_);
lean_dec_ref(v_n_1307_);
v___x_1313_ = lean_unsigned_to_nat(0u);
v___x_1314_ = lean_nat_dec_eq(v_exponent_1312_, v___x_1313_);
lean_dec(v_exponent_1312_);
if (v___x_1314_ == 0)
{
lean_dec(v_mantissa_1311_);
lean_del_object(v___x_1309_);
goto v___jp_1305_;
}
else
{
lean_object* v___x_1316_; 
if (v_isShared_1310_ == 0)
{
lean_ctor_set_tag(v___x_1309_, 1);
lean_ctor_set(v___x_1309_, 0, v_mantissa_1311_);
v___x_1316_ = v___x_1309_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_mantissa_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
else
{
lean_dec(v_x_1304_);
goto v___jp_1305_;
}
v___jp_1305_:
{
lean_object* v___x_1306_; 
v___x_1306_ = ((lean_object*)(l_Lean_Json_getInt_x3f___closed__1));
return v___x_1306_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getBool_x3f(lean_object* v_x_1322_){
_start:
{
if (lean_obj_tag(v_x_1322_) == 1)
{
uint8_t v_b_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_b_1323_ = lean_ctor_get_uint8(v_x_1322_, 0);
v___x_1324_ = lean_box(v_b_1323_);
v___x_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
return v___x_1325_;
}
else
{
lean_object* v___x_1326_; 
v___x_1326_ = ((lean_object*)(l_Lean_Json_getBool_x3f___closed__1));
return v___x_1326_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getBool_x3f___boxed(lean_object* v_x_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_Json_getBool_x3f(v_x_1327_);
lean_dec(v_x_1327_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getNum_x3f(lean_object* v_x_1332_){
_start:
{
if (lean_obj_tag(v_x_1332_) == 2)
{
lean_object* v_n_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
v_n_1333_ = lean_ctor_get(v_x_1332_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v_x_1332_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v_x_1332_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_n_1333_);
lean_dec(v_x_1332_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
lean_ctor_set_tag(v___x_1335_, 1);
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_n_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
else
{
lean_object* v___x_1341_; 
lean_dec(v_x_1332_);
v___x_1341_ = ((lean_object*)(l_Lean_Json_getNum_x3f___closed__1));
return v___x_1341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjVal_x3f(lean_object* v_x_1345_, lean_object* v_x_1346_){
_start:
{
if (lean_obj_tag(v_x_1345_) == 5)
{
lean_object* v_kvPairs_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1365_; 
v_kvPairs_1347_ = lean_ctor_get(v_x_1345_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v_x_1345_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1349_ = v_x_1345_;
v_isShared_1350_ = v_isSharedCheck_1365_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_kvPairs_1347_);
lean_dec(v_x_1345_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1365_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_kvPairs_1347_, v_x_1346_);
lean_dec(v_kvPairs_1347_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1355_; 
v___x_1352_ = ((lean_object*)(l_Lean_Json_getObjVal_x3f___closed__0));
v___x_1353_ = lean_string_append(v___x_1352_, v_x_1346_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set_tag(v___x_1349_, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1353_);
v___x_1355_ = v___x_1349_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1353_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
else
{
lean_object* v_val_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_del_object(v___x_1349_);
v_val_1357_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1351_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_val_1357_);
lean_dec(v___x_1351_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_val_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
}
else
{
lean_object* v___x_1366_; 
lean_dec(v_x_1345_);
v___x_1366_ = ((lean_object*)(l_Lean_Json_getObjVal_x3f___closed__1));
return v___x_1366_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjVal_x3f___boxed(lean_object* v_x_1367_, lean_object* v_x_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lean_Json_getObjVal_x3f(v_x_1367_, v_x_1368_);
lean_dec_ref(v_x_1368_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getArrVal_x3f(lean_object* v_x_1373_, lean_object* v_x_1374_){
_start:
{
if (lean_obj_tag(v_x_1373_) == 4)
{
lean_object* v_elems_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1391_; 
v_elems_1375_ = lean_ctor_get(v_x_1373_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v_x_1373_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1377_ = v_x_1373_;
v_isShared_1378_ = v_isSharedCheck_1391_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_elems_1375_);
lean_dec(v_x_1373_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1391_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1379_; uint8_t v___x_1380_; 
v___x_1379_ = lean_array_get_size(v_elems_1375_);
v___x_1380_ = lean_nat_dec_lt(v_x_1374_, v___x_1379_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1385_; 
lean_dec_ref(v_elems_1375_);
v___x_1381_ = ((lean_object*)(l_Lean_Json_getArrVal_x3f___closed__0));
v___x_1382_ = l_Nat_reprFast(v_x_1374_);
v___x_1383_ = lean_string_append(v___x_1381_, v___x_1382_);
lean_dec_ref(v___x_1382_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set_tag(v___x_1377_, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1383_);
v___x_1385_ = v___x_1377_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1383_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
else
{
lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1387_ = lean_array_fget(v_elems_1375_, v_x_1374_);
lean_dec(v_x_1374_);
lean_dec_ref(v_elems_1375_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set_tag(v___x_1377_, 1);
lean_ctor_set(v___x_1377_, 0, v___x_1387_);
v___x_1389_ = v___x_1377_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
else
{
lean_object* v___x_1392_; 
lean_dec(v_x_1374_);
lean_dec(v_x_1373_);
v___x_1392_ = ((lean_object*)(l_Lean_Json_getArrVal_x3f___closed__1));
return v___x_1392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValD(lean_object* v_j_1393_, lean_object* v_k_1394_){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = l_Lean_Json_getObjVal_x3f(v_j_1393_, v_k_1394_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v___x_1396_; 
lean_dec_ref_known(v___x_1395_, 1);
v___x_1396_ = lean_box(0);
return v___x_1396_;
}
else
{
lean_object* v_a_1397_; 
v_a_1397_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1397_);
lean_dec_ref_known(v___x_1395_, 1);
return v_a_1397_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValD___boxed(lean_object* v_j_1398_, lean_object* v_k_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_Json_getObjValD(v_j_1398_, v_k_1399_);
lean_dec_ref(v_k_1399_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Json_setObjVal_x21_spec__1(lean_object* v_msg_1401_){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = lean_box(0);
v___x_1403_ = lean_panic_fn_borrowed(v___x_1402_, v_msg_1401_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(lean_object* v_msg_1404_){
_start:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1405_ = lean_box(1);
v___x_1406_ = lean_panic_fn_borrowed(v___x_1405_, v_msg_1404_);
return v___x_1406_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1410_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2));
v___x_1411_ = lean_unsigned_to_nat(35u);
v___x_1412_ = lean_unsigned_to_nat(182u);
v___x_1413_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1));
v___x_1414_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1415_ = l_mkPanicMessageWithDecl(v___x_1414_, v___x_1413_, v___x_1412_, v___x_1411_, v___x_1410_);
return v___x_1415_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1416_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2));
v___x_1417_ = lean_unsigned_to_nat(21u);
v___x_1418_ = lean_unsigned_to_nat(183u);
v___x_1419_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1));
v___x_1420_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1421_ = l_mkPanicMessageWithDecl(v___x_1420_, v___x_1419_, v___x_1418_, v___x_1417_, v___x_1416_);
return v___x_1421_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1424_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6));
v___x_1425_ = lean_unsigned_to_nat(35u);
v___x_1426_ = lean_unsigned_to_nat(276u);
v___x_1427_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5));
v___x_1428_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1429_ = l_mkPanicMessageWithDecl(v___x_1428_, v___x_1427_, v___x_1426_, v___x_1425_, v___x_1424_);
return v___x_1429_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1430_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6));
v___x_1431_ = lean_unsigned_to_nat(21u);
v___x_1432_ = lean_unsigned_to_nat(277u);
v___x_1433_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5));
v___x_1434_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0));
v___x_1435_ = l_mkPanicMessageWithDecl(v___x_1434_, v___x_1433_, v___x_1432_, v___x_1431_, v___x_1430_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(lean_object* v_k_1436_, lean_object* v_v_1437_, lean_object* v_t_1438_){
_start:
{
if (lean_obj_tag(v_t_1438_) == 0)
{
lean_object* v_size_1439_; lean_object* v_k_1440_; lean_object* v_v_1441_; lean_object* v_l_1442_; lean_object* v_r_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1799_; 
v_size_1439_ = lean_ctor_get(v_t_1438_, 0);
v_k_1440_ = lean_ctor_get(v_t_1438_, 1);
v_v_1441_ = lean_ctor_get(v_t_1438_, 2);
v_l_1442_ = lean_ctor_get(v_t_1438_, 3);
v_r_1443_ = lean_ctor_get(v_t_1438_, 4);
v_isSharedCheck_1799_ = !lean_is_exclusive(v_t_1438_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1445_ = v_t_1438_;
v_isShared_1446_ = v_isSharedCheck_1799_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_r_1443_);
lean_inc(v_l_1442_);
lean_inc(v_v_1441_);
lean_inc(v_k_1440_);
lean_inc(v_size_1439_);
lean_dec(v_t_1438_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1799_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
uint8_t v___x_1447_; 
v___x_1447_ = lean_string_compare(v_k_1436_, v_k_1440_);
switch(v___x_1447_)
{
case 0:
{
lean_object* v___x_1448_; 
lean_dec(v_size_1439_);
v___x_1448_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1436_, v_v_1437_, v_l_1442_);
if (lean_obj_tag(v_r_1443_) == 0)
{
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_size_1449_; lean_object* v_size_1450_; lean_object* v_k_1451_; lean_object* v_v_1452_; lean_object* v_l_1453_; lean_object* v_r_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; 
v_size_1449_ = lean_ctor_get(v_r_1443_, 0);
v_size_1450_ = lean_ctor_get(v___x_1448_, 0);
v_k_1451_ = lean_ctor_get(v___x_1448_, 1);
v_v_1452_ = lean_ctor_get(v___x_1448_, 2);
v_l_1453_ = lean_ctor_get(v___x_1448_, 3);
v_r_1454_ = lean_ctor_get(v___x_1448_, 4);
lean_inc(v_r_1454_);
v___x_1455_ = lean_unsigned_to_nat(3u);
v___x_1456_ = lean_nat_mul(v___x_1455_, v_size_1449_);
v___x_1457_ = lean_nat_dec_lt(v___x_1456_, v_size_1450_);
lean_dec(v___x_1456_);
if (v___x_1457_ == 0)
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1462_; 
lean_dec(v_r_1454_);
v___x_1458_ = lean_unsigned_to_nat(1u);
v___x_1459_ = lean_nat_add(v___x_1458_, v_size_1450_);
v___x_1460_ = lean_nat_add(v___x_1459_, v_size_1449_);
lean_dec(v___x_1459_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 3, v___x_1448_);
lean_ctor_set(v___x_1445_, 0, v___x_1460_);
v___x_1462_ = v___x_1445_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v_k_1440_);
lean_ctor_set(v_reuseFailAlloc_1463_, 2, v_v_1441_);
lean_ctor_set(v_reuseFailAlloc_1463_, 3, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1463_, 4, v_r_1443_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
else
{
lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1535_; 
lean_inc(v_l_1453_);
lean_inc(v_v_1452_);
lean_inc(v_k_1451_);
lean_inc(v_size_1450_);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1535_ == 0)
{
lean_object* v_unused_1536_; lean_object* v_unused_1537_; lean_object* v_unused_1538_; lean_object* v_unused_1539_; lean_object* v_unused_1540_; 
v_unused_1536_ = lean_ctor_get(v___x_1448_, 4);
lean_dec(v_unused_1536_);
v_unused_1537_ = lean_ctor_get(v___x_1448_, 3);
lean_dec(v_unused_1537_);
v_unused_1538_ = lean_ctor_get(v___x_1448_, 2);
lean_dec(v_unused_1538_);
v_unused_1539_ = lean_ctor_get(v___x_1448_, 1);
lean_dec(v_unused_1539_);
v_unused_1540_ = lean_ctor_get(v___x_1448_, 0);
lean_dec(v_unused_1540_);
v___x_1465_ = v___x_1448_;
v_isShared_1466_ = v_isSharedCheck_1535_;
goto v_resetjp_1464_;
}
else
{
lean_dec(v___x_1448_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1535_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
if (lean_obj_tag(v_l_1453_) == 0)
{
if (lean_obj_tag(v_r_1454_) == 0)
{
lean_object* v_size_1467_; lean_object* v_size_1468_; lean_object* v_k_1469_; lean_object* v_v_1470_; lean_object* v_l_1471_; lean_object* v_r_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; uint8_t v___x_1475_; 
v_size_1467_ = lean_ctor_get(v_l_1453_, 0);
v_size_1468_ = lean_ctor_get(v_r_1454_, 0);
v_k_1469_ = lean_ctor_get(v_r_1454_, 1);
v_v_1470_ = lean_ctor_get(v_r_1454_, 2);
v_l_1471_ = lean_ctor_get(v_r_1454_, 3);
v_r_1472_ = lean_ctor_get(v_r_1454_, 4);
v___x_1473_ = lean_unsigned_to_nat(2u);
v___x_1474_ = lean_nat_mul(v___x_1473_, v_size_1467_);
v___x_1475_ = lean_nat_dec_lt(v_size_1468_, v___x_1474_);
lean_dec(v___x_1474_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1505_; 
lean_inc(v_r_1472_);
lean_inc(v_l_1471_);
lean_inc(v_v_1470_);
lean_inc(v_k_1469_);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_r_1454_);
if (v_isSharedCheck_1505_ == 0)
{
lean_object* v_unused_1506_; lean_object* v_unused_1507_; lean_object* v_unused_1508_; lean_object* v_unused_1509_; lean_object* v_unused_1510_; 
v_unused_1506_ = lean_ctor_get(v_r_1454_, 4);
lean_dec(v_unused_1506_);
v_unused_1507_ = lean_ctor_get(v_r_1454_, 3);
lean_dec(v_unused_1507_);
v_unused_1508_ = lean_ctor_get(v_r_1454_, 2);
lean_dec(v_unused_1508_);
v_unused_1509_ = lean_ctor_get(v_r_1454_, 1);
lean_dec(v_unused_1509_);
v_unused_1510_ = lean_ctor_get(v_r_1454_, 0);
lean_dec(v_unused_1510_);
v___x_1477_ = v_r_1454_;
v_isShared_1478_ = v_isSharedCheck_1505_;
goto v_resetjp_1476_;
}
else
{
lean_dec(v_r_1454_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1505_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___x_1493_; lean_object* v___y_1495_; 
v___x_1479_ = lean_unsigned_to_nat(1u);
v___x_1480_ = lean_nat_add(v___x_1479_, v_size_1450_);
lean_dec(v_size_1450_);
v___x_1481_ = lean_nat_add(v___x_1480_, v_size_1449_);
lean_dec(v___x_1480_);
v___x_1493_ = lean_nat_add(v___x_1479_, v_size_1467_);
if (lean_obj_tag(v_l_1471_) == 0)
{
lean_object* v_size_1503_; 
v_size_1503_ = lean_ctor_get(v_l_1471_, 0);
lean_inc(v_size_1503_);
v___y_1495_ = v_size_1503_;
goto v___jp_1494_;
}
else
{
lean_object* v___x_1504_; 
v___x_1504_ = lean_unsigned_to_nat(0u);
v___y_1495_ = v___x_1504_;
goto v___jp_1494_;
}
v___jp_1482_:
{
lean_object* v___x_1486_; lean_object* v___x_1488_; 
v___x_1486_ = lean_nat_add(v___y_1484_, v___y_1485_);
lean_dec(v___y_1485_);
lean_dec(v___y_1484_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 4, v_r_1443_);
lean_ctor_set(v___x_1477_, 3, v_r_1472_);
lean_ctor_set(v___x_1477_, 2, v_v_1441_);
lean_ctor_set(v___x_1477_, 1, v_k_1440_);
lean_ctor_set(v___x_1477_, 0, v___x_1486_);
v___x_1488_ = v___x_1477_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v_k_1440_);
lean_ctor_set(v_reuseFailAlloc_1492_, 2, v_v_1441_);
lean_ctor_set(v_reuseFailAlloc_1492_, 3, v_r_1472_);
lean_ctor_set(v_reuseFailAlloc_1492_, 4, v_r_1443_);
v___x_1488_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v___x_1490_; 
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 4, v___x_1488_);
lean_ctor_set(v___x_1465_, 3, v___y_1483_);
lean_ctor_set(v___x_1465_, 2, v_v_1470_);
lean_ctor_set(v___x_1465_, 1, v_k_1469_);
lean_ctor_set(v___x_1465_, 0, v___x_1481_);
v___x_1490_ = v___x_1465_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1481_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_k_1469_);
lean_ctor_set(v_reuseFailAlloc_1491_, 2, v_v_1470_);
lean_ctor_set(v_reuseFailAlloc_1491_, 3, v___y_1483_);
lean_ctor_set(v_reuseFailAlloc_1491_, 4, v___x_1488_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
v___jp_1494_:
{
lean_object* v___x_1496_; lean_object* v___x_1498_; 
v___x_1496_ = lean_nat_add(v___x_1493_, v___y_1495_);
lean_dec(v___y_1495_);
lean_dec(v___x_1493_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 4, v_l_1471_);
lean_ctor_set(v___x_1445_, 3, v_l_1453_);
lean_ctor_set(v___x_1445_, 2, v_v_1452_);
lean_ctor_set(v___x_1445_, 1, v_k_1451_);
lean_ctor_set(v___x_1445_, 0, v___x_1496_);
v___x_1498_ = v___x_1445_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_k_1451_);
lean_ctor_set(v_reuseFailAlloc_1502_, 2, v_v_1452_);
lean_ctor_set(v_reuseFailAlloc_1502_, 3, v_l_1453_);
lean_ctor_set(v_reuseFailAlloc_1502_, 4, v_l_1471_);
v___x_1498_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_nat_add(v___x_1479_, v_size_1449_);
if (lean_obj_tag(v_r_1472_) == 0)
{
lean_object* v_size_1500_; 
v_size_1500_ = lean_ctor_get(v_r_1472_, 0);
lean_inc(v_size_1500_);
v___y_1483_ = v___x_1498_;
v___y_1484_ = v___x_1499_;
v___y_1485_ = v_size_1500_;
goto v___jp_1482_;
}
else
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_unsigned_to_nat(0u);
v___y_1483_ = v___x_1498_;
v___y_1484_ = v___x_1499_;
v___y_1485_ = v___x_1501_;
goto v___jp_1482_;
}
}
}
}
}
else
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1517_; 
lean_del_object(v___x_1445_);
v___x_1511_ = lean_unsigned_to_nat(1u);
v___x_1512_ = lean_nat_add(v___x_1511_, v_size_1450_);
lean_dec(v_size_1450_);
v___x_1513_ = lean_nat_add(v___x_1512_, v_size_1449_);
lean_dec(v___x_1512_);
v___x_1514_ = lean_nat_add(v___x_1511_, v_size_1449_);
v___x_1515_ = lean_nat_add(v___x_1514_, v_size_1468_);
lean_dec(v___x_1514_);
lean_inc_ref(v_r_1443_);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 4, v_r_1443_);
lean_ctor_set(v___x_1465_, 3, v_r_1454_);
lean_ctor_set(v___x_1465_, 2, v_v_1441_);
lean_ctor_set(v___x_1465_, 1, v_k_1440_);
lean_ctor_set(v___x_1465_, 0, v___x_1515_);
v___x_1517_ = v___x_1465_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1515_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_k_1440_);
lean_ctor_set(v_reuseFailAlloc_1530_, 2, v_v_1441_);
lean_ctor_set(v_reuseFailAlloc_1530_, 3, v_r_1454_);
lean_ctor_set(v_reuseFailAlloc_1530_, 4, v_r_1443_);
v___x_1517_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1524_; 
v_isSharedCheck_1524_ = !lean_is_exclusive(v_r_1443_);
if (v_isSharedCheck_1524_ == 0)
{
lean_object* v_unused_1525_; lean_object* v_unused_1526_; lean_object* v_unused_1527_; lean_object* v_unused_1528_; lean_object* v_unused_1529_; 
v_unused_1525_ = lean_ctor_get(v_r_1443_, 4);
lean_dec(v_unused_1525_);
v_unused_1526_ = lean_ctor_get(v_r_1443_, 3);
lean_dec(v_unused_1526_);
v_unused_1527_ = lean_ctor_get(v_r_1443_, 2);
lean_dec(v_unused_1527_);
v_unused_1528_ = lean_ctor_get(v_r_1443_, 1);
lean_dec(v_unused_1528_);
v_unused_1529_ = lean_ctor_get(v_r_1443_, 0);
lean_dec(v_unused_1529_);
v___x_1519_ = v_r_1443_;
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
else
{
lean_dec(v_r_1443_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1522_; 
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 4, v___x_1517_);
lean_ctor_set(v___x_1519_, 3, v_l_1453_);
lean_ctor_set(v___x_1519_, 2, v_v_1452_);
lean_ctor_set(v___x_1519_, 1, v_k_1451_);
lean_ctor_set(v___x_1519_, 0, v___x_1513_);
v___x_1522_ = v___x_1519_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1513_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_k_1451_);
lean_ctor_set(v_reuseFailAlloc_1523_, 2, v_v_1452_);
lean_ctor_set(v_reuseFailAlloc_1523_, 3, v_l_1453_);
lean_ctor_set(v_reuseFailAlloc_1523_, 4, v___x_1517_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
}
else
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
lean_dec_ref_known(v_l_1453_, 5);
lean_del_object(v___x_1465_);
lean_dec(v_v_1452_);
lean_dec(v_k_1451_);
lean_dec(v_size_1450_);
lean_dec_ref_known(v_r_1443_, 5);
lean_del_object(v___x_1445_);
lean_dec(v_v_1441_);
lean_dec(v_k_1440_);
v___x_1531_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3);
v___x_1532_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1531_);
return v___x_1532_;
}
}
else
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
lean_del_object(v___x_1465_);
lean_dec(v_r_1454_);
lean_dec(v_v_1452_);
lean_dec(v_k_1451_);
lean_dec(v_size_1450_);
lean_dec_ref_known(v_r_1443_, 5);
lean_del_object(v___x_1445_);
lean_dec(v_v_1441_);
lean_dec(v_k_1440_);
v___x_1533_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4);
v___x_1534_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1533_);
return v___x_1534_;
}
}
}
}
else
{
lean_object* v_size_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1545_; 
v_size_1541_ = lean_ctor_get(v_r_1443_, 0);
v___x_1542_ = lean_unsigned_to_nat(1u);
v___x_1543_ = lean_nat_add(v___x_1542_, v_size_1541_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 3, v___x_1448_);
lean_ctor_set(v___x_1445_, 0, v___x_1543_);
v___x_1545_ = v___x_1445_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1543_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v_k_1440_);
lean_ctor_set(v_reuseFailAlloc_1546_, 2, v_v_1441_);
lean_ctor_set(v_reuseFailAlloc_1546_, 3, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1546_, 4, v_r_1443_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
else
{
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_l_1547_; 
v_l_1547_ = lean_ctor_get(v___x_1448_, 3);
if (lean_obj_tag(v_l_1547_) == 0)
{
lean_object* v_r_1548_; 
lean_inc_ref(v_l_1547_);
v_r_1548_ = lean_ctor_get(v___x_1448_, 4);
lean_inc(v_r_1548_);
if (lean_obj_tag(v_r_1548_) == 0)
{
lean_object* v_size_1549_; lean_object* v_k_1550_; lean_object* v_v_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1565_; 
v_size_1549_ = lean_ctor_get(v___x_1448_, 0);
v_k_1550_ = lean_ctor_get(v___x_1448_, 1);
v_v_1551_ = lean_ctor_get(v___x_1448_, 2);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1565_ == 0)
{
lean_object* v_unused_1566_; lean_object* v_unused_1567_; 
v_unused_1566_ = lean_ctor_get(v___x_1448_, 4);
lean_dec(v_unused_1566_);
v_unused_1567_ = lean_ctor_get(v___x_1448_, 3);
lean_dec(v_unused_1567_);
v___x_1553_ = v___x_1448_;
v_isShared_1554_ = v_isSharedCheck_1565_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_v_1551_);
lean_inc(v_k_1550_);
lean_inc(v_size_1549_);
lean_dec(v___x_1448_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1565_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v_size_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1560_; 
v_size_1555_ = lean_ctor_get(v_r_1548_, 0);
v___x_1556_ = lean_unsigned_to_nat(1u);
v___x_1557_ = lean_nat_add(v___x_1556_, v_size_1549_);
lean_dec(v_size_1549_);
v___x_1558_ = lean_nat_add(v___x_1556_, v_size_1555_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 4, v_r_1443_);
lean_ctor_set(v___x_1553_, 3, v_r_1548_);
lean_ctor_set(v___x_1553_, 2, v_v_1441_);
lean_ctor_set(v___x_1553_, 1, v_k_1440_);
lean_ctor_set(v___x_1553_, 0, v___x_1558_);
v___x_1560_ = v___x_1553_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1558_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v_k_1440_);
lean_ctor_set(v_reuseFailAlloc_1564_, 2, v_v_1441_);
lean_ctor_set(v_reuseFailAlloc_1564_, 3, v_r_1548_);
lean_ctor_set(v_reuseFailAlloc_1564_, 4, v_r_1443_);
v___x_1560_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
lean_object* v___x_1562_; 
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 4, v___x_1560_);
lean_ctor_set(v___x_1445_, 3, v_l_1547_);
lean_ctor_set(v___x_1445_, 2, v_v_1551_);
lean_ctor_set(v___x_1445_, 1, v_k_1550_);
lean_ctor_set(v___x_1445_, 0, v___x_1557_);
v___x_1562_ = v___x_1445_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1557_);
lean_ctor_set(v_reuseFailAlloc_1563_, 1, v_k_1550_);
lean_ctor_set(v_reuseFailAlloc_1563_, 2, v_v_1551_);
lean_ctor_set(v_reuseFailAlloc_1563_, 3, v_l_1547_);
lean_ctor_set(v_reuseFailAlloc_1563_, 4, v___x_1560_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
else
{
lean_object* v_k_1568_; lean_object* v_v_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1581_; 
v_k_1568_ = lean_ctor_get(v___x_1448_, 1);
v_v_1569_ = lean_ctor_get(v___x_1448_, 2);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1581_ == 0)
{
lean_object* v_unused_1582_; lean_object* v_unused_1583_; lean_object* v_unused_1584_; 
v_unused_1582_ = lean_ctor_get(v___x_1448_, 4);
lean_dec(v_unused_1582_);
v_unused_1583_ = lean_ctor_get(v___x_1448_, 3);
lean_dec(v_unused_1583_);
v_unused_1584_ = lean_ctor_get(v___x_1448_, 0);
lean_dec(v_unused_1584_);
v___x_1571_ = v___x_1448_;
v_isShared_1572_ = v_isSharedCheck_1581_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_v_1569_);
lean_inc(v_k_1568_);
lean_dec(v___x_1448_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1581_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1576_; 
v___x_1573_ = lean_unsigned_to_nat(3u);
v___x_1574_ = lean_unsigned_to_nat(1u);
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 3, v_r_1548_);
lean_ctor_set(v___x_1571_, 2, v_v_1441_);
lean_ctor_set(v___x_1571_, 1, v_k_1440_);
lean_ctor_set(v___x_1571_, 0, v___x_1574_);
v___x_1576_ = v___x_1571_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1574_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_k_1440_);
lean_ctor_set(v_reuseFailAlloc_1580_, 2, v_v_1441_);
lean_ctor_set(v_reuseFailAlloc_1580_, 3, v_r_1548_);
lean_ctor_set(v_reuseFailAlloc_1580_, 4, v_r_1548_);
v___x_1576_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v___x_1578_; 
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 4, v___x_1576_);
lean_ctor_set(v___x_1445_, 3, v_l_1547_);
lean_ctor_set(v___x_1445_, 2, v_v_1569_);
lean_ctor_set(v___x_1445_, 1, v_k_1568_);
lean_ctor_set(v___x_1445_, 0, v___x_1573_);
v___x_1578_ = v___x_1445_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1573_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v_k_1568_);
lean_ctor_set(v_reuseFailAlloc_1579_, 2, v_v_1569_);
lean_ctor_set(v_reuseFailAlloc_1579_, 3, v_l_1547_);
lean_ctor_set(v_reuseFailAlloc_1579_, 4, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
}
else
{
lean_object* v_r_1585_; 
v_r_1585_ = lean_ctor_get(v___x_1448_, 4);
lean_inc(v_r_1585_);
if (lean_obj_tag(v_r_1585_) == 0)
{
lean_object* v_k_1586_; lean_object* v_v_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1611_; 
lean_inc(v_l_1547_);
v_k_1586_ = lean_ctor_get(v___x_1448_, 1);
v_v_1587_ = lean_ctor_get(v___x_1448_, 2);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1611_ == 0)
{
lean_object* v_unused_1612_; lean_object* v_unused_1613_; lean_object* v_unused_1614_; 
v_unused_1612_ = lean_ctor_get(v___x_1448_, 4);
lean_dec(v_unused_1612_);
v_unused_1613_ = lean_ctor_get(v___x_1448_, 3);
lean_dec(v_unused_1613_);
v_unused_1614_ = lean_ctor_get(v___x_1448_, 0);
lean_dec(v_unused_1614_);
v___x_1589_ = v___x_1448_;
v_isShared_1590_ = v_isSharedCheck_1611_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_v_1587_);
lean_inc(v_k_1586_);
lean_dec(v___x_1448_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1611_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v_k_1591_; lean_object* v_v_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1607_; 
v_k_1591_ = lean_ctor_get(v_r_1585_, 1);
v_v_1592_ = lean_ctor_get(v_r_1585_, 2);
v_isSharedCheck_1607_ = !lean_is_exclusive(v_r_1585_);
if (v_isSharedCheck_1607_ == 0)
{
lean_object* v_unused_1608_; lean_object* v_unused_1609_; lean_object* v_unused_1610_; 
v_unused_1608_ = lean_ctor_get(v_r_1585_, 4);
lean_dec(v_unused_1608_);
v_unused_1609_ = lean_ctor_get(v_r_1585_, 3);
lean_dec(v_unused_1609_);
v_unused_1610_ = lean_ctor_get(v_r_1585_, 0);
lean_dec(v_unused_1610_);
v___x_1594_ = v_r_1585_;
v_isShared_1595_ = v_isSharedCheck_1607_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_v_1592_);
lean_inc(v_k_1591_);
lean_dec(v_r_1585_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1607_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1599_; 
v___x_1596_ = lean_unsigned_to_nat(3u);
v___x_1597_ = lean_unsigned_to_nat(1u);
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 4, v_l_1547_);
lean_ctor_set(v___x_1594_, 3, v_l_1547_);
lean_ctor_set(v___x_1594_, 2, v_v_1587_);
lean_ctor_set(v___x_1594_, 1, v_k_1586_);
lean_ctor_set(v___x_1594_, 0, v___x_1597_);
v___x_1599_ = v___x_1594_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1606_, 1, v_k_1586_);
lean_ctor_set(v_reuseFailAlloc_1606_, 2, v_v_1587_);
lean_ctor_set(v_reuseFailAlloc_1606_, 3, v_l_1547_);
lean_ctor_set(v_reuseFailAlloc_1606_, 4, v_l_1547_);
v___x_1599_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v___x_1601_; 
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 4, v_l_1547_);
lean_ctor_set(v___x_1589_, 2, v_v_1441_);
lean_ctor_set(v___x_1589_, 1, v_k_1440_);
lean_ctor_set(v___x_1589_, 0, v___x_1597_);
v___x_1601_ = v___x_1589_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_k_1440_);
lean_ctor_set(v_reuseFailAlloc_1605_, 2, v_v_1441_);
lean_ctor_set(v_reuseFailAlloc_1605_, 3, v_l_1547_);
lean_ctor_set(v_reuseFailAlloc_1605_, 4, v_l_1547_);
v___x_1601_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
lean_object* v___x_1603_; 
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 4, v___x_1601_);
lean_ctor_set(v___x_1445_, 3, v___x_1599_);
lean_ctor_set(v___x_1445_, 2, v_v_1592_);
lean_ctor_set(v___x_1445_, 1, v_k_1591_);
lean_ctor_set(v___x_1445_, 0, v___x_1596_);
v___x_1603_ = v___x_1445_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1596_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_k_1591_);
lean_ctor_set(v_reuseFailAlloc_1604_, 2, v_v_1592_);
lean_ctor_set(v_reuseFailAlloc_1604_, 3, v___x_1599_);
lean_ctor_set(v_reuseFailAlloc_1604_, 4, v___x_1601_);
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
}
}
else
{
lean_object* v___x_1615_; lean_object* v___x_1617_; 
v___x_1615_ = lean_unsigned_to_nat(2u);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 4, v_r_1585_);
lean_ctor_set(v___x_1445_, 3, v___x_1448_);
lean_ctor_set(v___x_1445_, 0, v___x_1615_);
v___x_1617_ = v___x_1445_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1615_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v_k_1440_);
lean_ctor_set(v_reuseFailAlloc_1618_, 2, v_v_1441_);
lean_ctor_set(v_reuseFailAlloc_1618_, 3, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1618_, 4, v_r_1585_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
else
{
lean_object* v___x_1619_; lean_object* v___x_1621_; 
v___x_1619_ = lean_unsigned_to_nat(1u);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 4, v___x_1448_);
lean_ctor_set(v___x_1445_, 3, v___x_1448_);
lean_ctor_set(v___x_1445_, 0, v___x_1619_);
v___x_1621_ = v___x_1445_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1619_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v_k_1440_);
lean_ctor_set(v_reuseFailAlloc_1622_, 2, v_v_1441_);
lean_ctor_set(v_reuseFailAlloc_1622_, 3, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1622_, 4, v___x_1448_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
case 1:
{
lean_object* v___x_1624_; 
lean_dec(v_v_1441_);
lean_dec(v_k_1440_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 2, v_v_1437_);
lean_ctor_set(v___x_1445_, 1, v_k_1436_);
v___x_1624_ = v___x_1445_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_size_1439_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v_k_1436_);
lean_ctor_set(v_reuseFailAlloc_1625_, 2, v_v_1437_);
lean_ctor_set(v_reuseFailAlloc_1625_, 3, v_l_1442_);
lean_ctor_set(v_reuseFailAlloc_1625_, 4, v_r_1443_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
default: 
{
lean_object* v___x_1626_; 
lean_dec(v_size_1439_);
v___x_1626_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1436_, v_v_1437_, v_r_1443_);
if (lean_obj_tag(v_l_1442_) == 0)
{
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_size_1627_; lean_object* v_size_1628_; lean_object* v_k_1629_; lean_object* v_v_1630_; lean_object* v_l_1631_; lean_object* v_r_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; 
v_size_1627_ = lean_ctor_get(v_l_1442_, 0);
v_size_1628_ = lean_ctor_get(v___x_1626_, 0);
v_k_1629_ = lean_ctor_get(v___x_1626_, 1);
v_v_1630_ = lean_ctor_get(v___x_1626_, 2);
v_l_1631_ = lean_ctor_get(v___x_1626_, 3);
lean_inc(v_l_1631_);
v_r_1632_ = lean_ctor_get(v___x_1626_, 4);
v___x_1633_ = lean_unsigned_to_nat(3u);
v___x_1634_ = lean_nat_mul(v___x_1633_, v_size_1627_);
v___x_1635_ = lean_nat_dec_lt(v___x_1634_, v_size_1628_);
lean_dec(v___x_1634_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1640_; 
lean_dec(v_l_1631_);
v___x_1636_ = lean_unsigned_to_nat(1u);
v___x_1637_ = lean_nat_add(v___x_1636_, v_size_1627_);
v___x_1638_ = lean_nat_add(v___x_1637_, v_size_1628_);
lean_dec(v___x_1637_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 4, v___x_1626_);
lean_ctor_set(v___x_1445_, 0, v___x_1638_);
v___x_1640_ = v___x_1445_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1638_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_k_1440_);
lean_ctor_set(v_reuseFailAlloc_1641_, 2, v_v_1441_);
lean_ctor_set(v_reuseFailAlloc_1641_, 3, v_l_1442_);
lean_ctor_set(v_reuseFailAlloc_1641_, 4, v___x_1626_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
else
{
lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1711_; 
lean_inc(v_r_1632_);
lean_inc(v_v_1630_);
lean_inc(v_k_1629_);
lean_inc(v_size_1628_);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1711_ == 0)
{
lean_object* v_unused_1712_; lean_object* v_unused_1713_; lean_object* v_unused_1714_; lean_object* v_unused_1715_; lean_object* v_unused_1716_; 
v_unused_1712_ = lean_ctor_get(v___x_1626_, 4);
lean_dec(v_unused_1712_);
v_unused_1713_ = lean_ctor_get(v___x_1626_, 3);
lean_dec(v_unused_1713_);
v_unused_1714_ = lean_ctor_get(v___x_1626_, 2);
lean_dec(v_unused_1714_);
v_unused_1715_ = lean_ctor_get(v___x_1626_, 1);
lean_dec(v_unused_1715_);
v_unused_1716_ = lean_ctor_get(v___x_1626_, 0);
lean_dec(v_unused_1716_);
v___x_1643_ = v___x_1626_;
v_isShared_1644_ = v_isSharedCheck_1711_;
goto v_resetjp_1642_;
}
else
{
lean_dec(v___x_1626_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1711_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
if (lean_obj_tag(v_l_1631_) == 0)
{
if (lean_obj_tag(v_r_1632_) == 0)
{
lean_object* v_size_1645_; lean_object* v_k_1646_; lean_object* v_v_1647_; lean_object* v_l_1648_; lean_object* v_r_1649_; lean_object* v_size_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; 
v_size_1645_ = lean_ctor_get(v_l_1631_, 0);
v_k_1646_ = lean_ctor_get(v_l_1631_, 1);
v_v_1647_ = lean_ctor_get(v_l_1631_, 2);
v_l_1648_ = lean_ctor_get(v_l_1631_, 3);
v_r_1649_ = lean_ctor_get(v_l_1631_, 4);
v_size_1650_ = lean_ctor_get(v_r_1632_, 0);
v___x_1651_ = lean_unsigned_to_nat(2u);
v___x_1652_ = lean_nat_mul(v___x_1651_, v_size_1650_);
v___x_1653_ = lean_nat_dec_lt(v_size_1645_, v___x_1652_);
lean_dec(v___x_1652_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1682_; 
lean_inc(v_r_1649_);
lean_inc(v_l_1648_);
lean_inc(v_v_1647_);
lean_inc(v_k_1646_);
v_isSharedCheck_1682_ = !lean_is_exclusive(v_l_1631_);
if (v_isSharedCheck_1682_ == 0)
{
lean_object* v_unused_1683_; lean_object* v_unused_1684_; lean_object* v_unused_1685_; lean_object* v_unused_1686_; lean_object* v_unused_1687_; 
v_unused_1683_ = lean_ctor_get(v_l_1631_, 4);
lean_dec(v_unused_1683_);
v_unused_1684_ = lean_ctor_get(v_l_1631_, 3);
lean_dec(v_unused_1684_);
v_unused_1685_ = lean_ctor_get(v_l_1631_, 2);
lean_dec(v_unused_1685_);
v_unused_1686_ = lean_ctor_get(v_l_1631_, 1);
lean_dec(v_unused_1686_);
v_unused_1687_ = lean_ctor_get(v_l_1631_, 0);
lean_dec(v_unused_1687_);
v___x_1655_ = v_l_1631_;
v_isShared_1656_ = v_isSharedCheck_1682_;
goto v_resetjp_1654_;
}
else
{
lean_dec(v_l_1631_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1682_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1672_; 
v___x_1657_ = lean_unsigned_to_nat(1u);
v___x_1658_ = lean_nat_add(v___x_1657_, v_size_1627_);
v___x_1659_ = lean_nat_add(v___x_1658_, v_size_1628_);
lean_dec(v_size_1628_);
if (lean_obj_tag(v_l_1648_) == 0)
{
lean_object* v_size_1680_; 
v_size_1680_ = lean_ctor_get(v_l_1648_, 0);
lean_inc(v_size_1680_);
v___y_1672_ = v_size_1680_;
goto v___jp_1671_;
}
else
{
lean_object* v___x_1681_; 
v___x_1681_ = lean_unsigned_to_nat(0u);
v___y_1672_ = v___x_1681_;
goto v___jp_1671_;
}
v___jp_1660_:
{
lean_object* v___x_1664_; lean_object* v___x_1666_; 
v___x_1664_ = lean_nat_add(v___y_1662_, v___y_1663_);
lean_dec(v___y_1663_);
lean_dec(v___y_1662_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 4, v_r_1632_);
lean_ctor_set(v___x_1655_, 3, v_r_1649_);
lean_ctor_set(v___x_1655_, 2, v_v_1630_);
lean_ctor_set(v___x_1655_, 1, v_k_1629_);
lean_ctor_set(v___x_1655_, 0, v___x_1664_);
v___x_1666_ = v___x_1655_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1664_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v_k_1629_);
lean_ctor_set(v_reuseFailAlloc_1670_, 2, v_v_1630_);
lean_ctor_set(v_reuseFailAlloc_1670_, 3, v_r_1649_);
lean_ctor_set(v_reuseFailAlloc_1670_, 4, v_r_1632_);
v___x_1666_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
lean_object* v___x_1668_; 
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 4, v___x_1666_);
lean_ctor_set(v___x_1643_, 3, v___y_1661_);
lean_ctor_set(v___x_1643_, 2, v_v_1647_);
lean_ctor_set(v___x_1643_, 1, v_k_1646_);
lean_ctor_set(v___x_1643_, 0, v___x_1659_);
v___x_1668_ = v___x_1643_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1659_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_k_1646_);
lean_ctor_set(v_reuseFailAlloc_1669_, 2, v_v_1647_);
lean_ctor_set(v_reuseFailAlloc_1669_, 3, v___y_1661_);
lean_ctor_set(v_reuseFailAlloc_1669_, 4, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
v___jp_1671_:
{
lean_object* v___x_1673_; lean_object* v___x_1675_; 
v___x_1673_ = lean_nat_add(v___x_1658_, v___y_1672_);
lean_dec(v___y_1672_);
lean_dec(v___x_1658_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 4, v_l_1648_);
lean_ctor_set(v___x_1445_, 0, v___x_1673_);
v___x_1675_ = v___x_1445_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1673_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v_k_1440_);
lean_ctor_set(v_reuseFailAlloc_1679_, 2, v_v_1441_);
lean_ctor_set(v_reuseFailAlloc_1679_, 3, v_l_1442_);
lean_ctor_set(v_reuseFailAlloc_1679_, 4, v_l_1648_);
v___x_1675_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
lean_object* v___x_1676_; 
v___x_1676_ = lean_nat_add(v___x_1657_, v_size_1650_);
if (lean_obj_tag(v_r_1649_) == 0)
{
lean_object* v_size_1677_; 
v_size_1677_ = lean_ctor_get(v_r_1649_, 0);
lean_inc(v_size_1677_);
v___y_1661_ = v___x_1675_;
v___y_1662_ = v___x_1676_;
v___y_1663_ = v_size_1677_;
goto v___jp_1660_;
}
else
{
lean_object* v___x_1678_; 
v___x_1678_ = lean_unsigned_to_nat(0u);
v___y_1661_ = v___x_1675_;
v___y_1662_ = v___x_1676_;
v___y_1663_ = v___x_1678_;
goto v___jp_1660_;
}
}
}
}
}
else
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1693_; 
lean_del_object(v___x_1445_);
v___x_1688_ = lean_unsigned_to_nat(1u);
v___x_1689_ = lean_nat_add(v___x_1688_, v_size_1627_);
v___x_1690_ = lean_nat_add(v___x_1689_, v_size_1628_);
lean_dec(v_size_1628_);
v___x_1691_ = lean_nat_add(v___x_1689_, v_size_1645_);
lean_dec(v___x_1689_);
lean_inc_ref(v_l_1442_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 4, v_l_1631_);
lean_ctor_set(v___x_1643_, 3, v_l_1442_);
lean_ctor_set(v___x_1643_, 2, v_v_1441_);
lean_ctor_set(v___x_1643_, 1, v_k_1440_);
lean_ctor_set(v___x_1643_, 0, v___x_1691_);
v___x_1693_ = v___x_1643_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1691_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v_k_1440_);
lean_ctor_set(v_reuseFailAlloc_1706_, 2, v_v_1441_);
lean_ctor_set(v_reuseFailAlloc_1706_, 3, v_l_1442_);
lean_ctor_set(v_reuseFailAlloc_1706_, 4, v_l_1631_);
v___x_1693_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
v_isSharedCheck_1700_ = !lean_is_exclusive(v_l_1442_);
if (v_isSharedCheck_1700_ == 0)
{
lean_object* v_unused_1701_; lean_object* v_unused_1702_; lean_object* v_unused_1703_; lean_object* v_unused_1704_; lean_object* v_unused_1705_; 
v_unused_1701_ = lean_ctor_get(v_l_1442_, 4);
lean_dec(v_unused_1701_);
v_unused_1702_ = lean_ctor_get(v_l_1442_, 3);
lean_dec(v_unused_1702_);
v_unused_1703_ = lean_ctor_get(v_l_1442_, 2);
lean_dec(v_unused_1703_);
v_unused_1704_ = lean_ctor_get(v_l_1442_, 1);
lean_dec(v_unused_1704_);
v_unused_1705_ = lean_ctor_get(v_l_1442_, 0);
lean_dec(v_unused_1705_);
v___x_1695_ = v_l_1442_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_dec(v_l_1442_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 4, v_r_1632_);
lean_ctor_set(v___x_1695_, 3, v___x_1693_);
lean_ctor_set(v___x_1695_, 2, v_v_1630_);
lean_ctor_set(v___x_1695_, 1, v_k_1629_);
lean_ctor_set(v___x_1695_, 0, v___x_1690_);
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1690_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_k_1629_);
lean_ctor_set(v_reuseFailAlloc_1699_, 2, v_v_1630_);
lean_ctor_set(v_reuseFailAlloc_1699_, 3, v___x_1693_);
lean_ctor_set(v_reuseFailAlloc_1699_, 4, v_r_1632_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
}
else
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
lean_dec_ref_known(v_l_1631_, 5);
lean_del_object(v___x_1643_);
lean_dec(v_v_1630_);
lean_dec(v_k_1629_);
lean_dec(v_size_1628_);
lean_dec_ref_known(v_l_1442_, 5);
lean_del_object(v___x_1445_);
lean_dec(v_v_1441_);
lean_dec(v_k_1440_);
v___x_1707_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7);
v___x_1708_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1707_);
return v___x_1708_;
}
}
else
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
lean_del_object(v___x_1643_);
lean_dec(v_r_1632_);
lean_dec(v_v_1630_);
lean_dec(v_k_1629_);
lean_dec(v_size_1628_);
lean_dec_ref_known(v_l_1442_, 5);
lean_del_object(v___x_1445_);
lean_dec(v_v_1441_);
lean_dec(v_k_1440_);
v___x_1709_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8);
v___x_1710_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_1709_);
return v___x_1710_;
}
}
}
}
else
{
lean_object* v_size_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1721_; 
v_size_1717_ = lean_ctor_get(v_l_1442_, 0);
v___x_1718_ = lean_unsigned_to_nat(1u);
v___x_1719_ = lean_nat_add(v___x_1718_, v_size_1717_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 4, v___x_1626_);
lean_ctor_set(v___x_1445_, 0, v___x_1719_);
v___x_1721_ = v___x_1445_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1719_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_k_1440_);
lean_ctor_set(v_reuseFailAlloc_1722_, 2, v_v_1441_);
lean_ctor_set(v_reuseFailAlloc_1722_, 3, v_l_1442_);
lean_ctor_set(v_reuseFailAlloc_1722_, 4, v___x_1626_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
else
{
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_l_1723_; 
v_l_1723_ = lean_ctor_get(v___x_1626_, 3);
lean_inc(v_l_1723_);
if (lean_obj_tag(v_l_1723_) == 0)
{
lean_object* v_r_1724_; 
v_r_1724_ = lean_ctor_get(v___x_1626_, 4);
lean_inc(v_r_1724_);
if (lean_obj_tag(v_r_1724_) == 0)
{
lean_object* v_size_1725_; lean_object* v_k_1726_; lean_object* v_v_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1741_; 
v_size_1725_ = lean_ctor_get(v___x_1626_, 0);
v_k_1726_ = lean_ctor_get(v___x_1626_, 1);
v_v_1727_ = lean_ctor_get(v___x_1626_, 2);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1741_ == 0)
{
lean_object* v_unused_1742_; lean_object* v_unused_1743_; 
v_unused_1742_ = lean_ctor_get(v___x_1626_, 4);
lean_dec(v_unused_1742_);
v_unused_1743_ = lean_ctor_get(v___x_1626_, 3);
lean_dec(v_unused_1743_);
v___x_1729_ = v___x_1626_;
v_isShared_1730_ = v_isSharedCheck_1741_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_v_1727_);
lean_inc(v_k_1726_);
lean_inc(v_size_1725_);
lean_dec(v___x_1626_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1741_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v_size_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1736_; 
v_size_1731_ = lean_ctor_get(v_l_1723_, 0);
v___x_1732_ = lean_unsigned_to_nat(1u);
v___x_1733_ = lean_nat_add(v___x_1732_, v_size_1725_);
lean_dec(v_size_1725_);
v___x_1734_ = lean_nat_add(v___x_1732_, v_size_1731_);
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 4, v_l_1723_);
lean_ctor_set(v___x_1729_, 3, v_l_1442_);
lean_ctor_set(v___x_1729_, 2, v_v_1441_);
lean_ctor_set(v___x_1729_, 1, v_k_1440_);
lean_ctor_set(v___x_1729_, 0, v___x_1734_);
v___x_1736_ = v___x_1729_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1734_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_k_1440_);
lean_ctor_set(v_reuseFailAlloc_1740_, 2, v_v_1441_);
lean_ctor_set(v_reuseFailAlloc_1740_, 3, v_l_1442_);
lean_ctor_set(v_reuseFailAlloc_1740_, 4, v_l_1723_);
v___x_1736_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
lean_object* v___x_1738_; 
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 4, v_r_1724_);
lean_ctor_set(v___x_1445_, 3, v___x_1736_);
lean_ctor_set(v___x_1445_, 2, v_v_1727_);
lean_ctor_set(v___x_1445_, 1, v_k_1726_);
lean_ctor_set(v___x_1445_, 0, v___x_1733_);
v___x_1738_ = v___x_1445_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1733_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_k_1726_);
lean_ctor_set(v_reuseFailAlloc_1739_, 2, v_v_1727_);
lean_ctor_set(v_reuseFailAlloc_1739_, 3, v___x_1736_);
lean_ctor_set(v_reuseFailAlloc_1739_, 4, v_r_1724_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
else
{
lean_object* v_k_1744_; lean_object* v_v_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1769_; 
v_k_1744_ = lean_ctor_get(v___x_1626_, 1);
v_v_1745_ = lean_ctor_get(v___x_1626_, 2);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1769_ == 0)
{
lean_object* v_unused_1770_; lean_object* v_unused_1771_; lean_object* v_unused_1772_; 
v_unused_1770_ = lean_ctor_get(v___x_1626_, 4);
lean_dec(v_unused_1770_);
v_unused_1771_ = lean_ctor_get(v___x_1626_, 3);
lean_dec(v_unused_1771_);
v_unused_1772_ = lean_ctor_get(v___x_1626_, 0);
lean_dec(v_unused_1772_);
v___x_1747_ = v___x_1626_;
v_isShared_1748_ = v_isSharedCheck_1769_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_v_1745_);
lean_inc(v_k_1744_);
lean_dec(v___x_1626_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1769_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v_k_1749_; lean_object* v_v_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1765_; 
v_k_1749_ = lean_ctor_get(v_l_1723_, 1);
v_v_1750_ = lean_ctor_get(v_l_1723_, 2);
v_isSharedCheck_1765_ = !lean_is_exclusive(v_l_1723_);
if (v_isSharedCheck_1765_ == 0)
{
lean_object* v_unused_1766_; lean_object* v_unused_1767_; lean_object* v_unused_1768_; 
v_unused_1766_ = lean_ctor_get(v_l_1723_, 4);
lean_dec(v_unused_1766_);
v_unused_1767_ = lean_ctor_get(v_l_1723_, 3);
lean_dec(v_unused_1767_);
v_unused_1768_ = lean_ctor_get(v_l_1723_, 0);
lean_dec(v_unused_1768_);
v___x_1752_ = v_l_1723_;
v_isShared_1753_ = v_isSharedCheck_1765_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_v_1750_);
lean_inc(v_k_1749_);
lean_dec(v_l_1723_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1765_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1757_; 
v___x_1754_ = lean_unsigned_to_nat(3u);
v___x_1755_ = lean_unsigned_to_nat(1u);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 4, v_r_1724_);
lean_ctor_set(v___x_1752_, 3, v_r_1724_);
lean_ctor_set(v___x_1752_, 2, v_v_1441_);
lean_ctor_set(v___x_1752_, 1, v_k_1440_);
lean_ctor_set(v___x_1752_, 0, v___x_1755_);
v___x_1757_ = v___x_1752_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1755_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v_k_1440_);
lean_ctor_set(v_reuseFailAlloc_1764_, 2, v_v_1441_);
lean_ctor_set(v_reuseFailAlloc_1764_, 3, v_r_1724_);
lean_ctor_set(v_reuseFailAlloc_1764_, 4, v_r_1724_);
v___x_1757_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
lean_object* v___x_1759_; 
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 3, v_r_1724_);
lean_ctor_set(v___x_1747_, 0, v___x_1755_);
v___x_1759_ = v___x_1747_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1755_);
lean_ctor_set(v_reuseFailAlloc_1763_, 1, v_k_1744_);
lean_ctor_set(v_reuseFailAlloc_1763_, 2, v_v_1745_);
lean_ctor_set(v_reuseFailAlloc_1763_, 3, v_r_1724_);
lean_ctor_set(v_reuseFailAlloc_1763_, 4, v_r_1724_);
v___x_1759_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
lean_object* v___x_1761_; 
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 4, v___x_1759_);
lean_ctor_set(v___x_1445_, 3, v___x_1757_);
lean_ctor_set(v___x_1445_, 2, v_v_1750_);
lean_ctor_set(v___x_1445_, 1, v_k_1749_);
lean_ctor_set(v___x_1445_, 0, v___x_1754_);
v___x_1761_ = v___x_1445_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1754_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_k_1749_);
lean_ctor_set(v_reuseFailAlloc_1762_, 2, v_v_1750_);
lean_ctor_set(v_reuseFailAlloc_1762_, 3, v___x_1757_);
lean_ctor_set(v_reuseFailAlloc_1762_, 4, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1773_; 
v_r_1773_ = lean_ctor_get(v___x_1626_, 4);
lean_inc(v_r_1773_);
if (lean_obj_tag(v_r_1773_) == 0)
{
lean_object* v_k_1774_; lean_object* v_v_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1787_; 
v_k_1774_ = lean_ctor_get(v___x_1626_, 1);
v_v_1775_ = lean_ctor_get(v___x_1626_, 2);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1787_ == 0)
{
lean_object* v_unused_1788_; lean_object* v_unused_1789_; lean_object* v_unused_1790_; 
v_unused_1788_ = lean_ctor_get(v___x_1626_, 4);
lean_dec(v_unused_1788_);
v_unused_1789_ = lean_ctor_get(v___x_1626_, 3);
lean_dec(v_unused_1789_);
v_unused_1790_ = lean_ctor_get(v___x_1626_, 0);
lean_dec(v_unused_1790_);
v___x_1777_ = v___x_1626_;
v_isShared_1778_ = v_isSharedCheck_1787_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_v_1775_);
lean_inc(v_k_1774_);
lean_dec(v___x_1626_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1787_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1782_; 
v___x_1779_ = lean_unsigned_to_nat(3u);
v___x_1780_ = lean_unsigned_to_nat(1u);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 4, v_l_1723_);
lean_ctor_set(v___x_1777_, 2, v_v_1441_);
lean_ctor_set(v___x_1777_, 1, v_k_1440_);
lean_ctor_set(v___x_1777_, 0, v___x_1780_);
v___x_1782_ = v___x_1777_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1780_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_k_1440_);
lean_ctor_set(v_reuseFailAlloc_1786_, 2, v_v_1441_);
lean_ctor_set(v_reuseFailAlloc_1786_, 3, v_l_1723_);
lean_ctor_set(v_reuseFailAlloc_1786_, 4, v_l_1723_);
v___x_1782_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1784_; 
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 4, v_r_1773_);
lean_ctor_set(v___x_1445_, 3, v___x_1782_);
lean_ctor_set(v___x_1445_, 2, v_v_1775_);
lean_ctor_set(v___x_1445_, 1, v_k_1774_);
lean_ctor_set(v___x_1445_, 0, v___x_1779_);
v___x_1784_ = v___x_1445_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1779_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_k_1774_);
lean_ctor_set(v_reuseFailAlloc_1785_, 2, v_v_1775_);
lean_ctor_set(v_reuseFailAlloc_1785_, 3, v___x_1782_);
lean_ctor_set(v_reuseFailAlloc_1785_, 4, v_r_1773_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
else
{
lean_object* v___x_1791_; lean_object* v___x_1793_; 
v___x_1791_ = lean_unsigned_to_nat(2u);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 4, v___x_1626_);
lean_ctor_set(v___x_1445_, 3, v_r_1773_);
lean_ctor_set(v___x_1445_, 0, v___x_1791_);
v___x_1793_ = v___x_1445_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v_k_1440_);
lean_ctor_set(v_reuseFailAlloc_1794_, 2, v_v_1441_);
lean_ctor_set(v_reuseFailAlloc_1794_, 3, v_r_1773_);
lean_ctor_set(v_reuseFailAlloc_1794_, 4, v___x_1626_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
else
{
lean_object* v___x_1795_; lean_object* v___x_1797_; 
v___x_1795_ = lean_unsigned_to_nat(1u);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 4, v___x_1626_);
lean_ctor_set(v___x_1445_, 3, v___x_1626_);
lean_ctor_set(v___x_1445_, 0, v___x_1795_);
v___x_1797_ = v___x_1445_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1795_);
lean_ctor_set(v_reuseFailAlloc_1798_, 1, v_k_1440_);
lean_ctor_set(v_reuseFailAlloc_1798_, 2, v_v_1441_);
lean_ctor_set(v_reuseFailAlloc_1798_, 3, v___x_1626_);
lean_ctor_set(v_reuseFailAlloc_1798_, 4, v___x_1626_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = lean_unsigned_to_nat(1u);
v___x_1801_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
lean_ctor_set(v___x_1801_, 1, v_k_1436_);
lean_ctor_set(v___x_1801_, 2, v_v_1437_);
lean_ctor_set(v___x_1801_, 3, v_t_1438_);
lean_ctor_set(v___x_1801_, 4, v_t_1438_);
return v___x_1801_;
}
}
}
static lean_object* _init_l_Lean_Json_setObjVal_x21___closed__2(void){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1804_ = ((lean_object*)(l_Lean_Json_setObjVal_x21___closed__1));
v___x_1805_ = lean_unsigned_to_nat(21u);
v___x_1806_ = lean_unsigned_to_nat(290u);
v___x_1807_ = ((lean_object*)(l_Lean_Json_setObjVal_x21___closed__0));
v___x_1808_ = ((lean_object*)(l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0));
v___x_1809_ = l_mkPanicMessageWithDecl(v___x_1808_, v___x_1807_, v___x_1806_, v___x_1805_, v___x_1804_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_setObjVal_x21(lean_object* v_x_1810_, lean_object* v_x_1811_, lean_object* v_x_1812_){
_start:
{
if (lean_obj_tag(v_x_1810_) == 5)
{
lean_object* v_kvPairs_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1821_; 
v_kvPairs_1813_ = lean_ctor_get(v_x_1810_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v_x_1810_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1815_ = v_x_1810_;
v_isShared_1816_ = v_isSharedCheck_1821_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_kvPairs_1813_);
lean_dec(v_x_1810_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1821_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1817_; lean_object* v___x_1819_; 
v___x_1817_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_x_1811_, v_x_1812_, v_kvPairs_1813_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v___x_1817_);
v___x_1819_ = v___x_1815_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
else
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
lean_dec(v_x_1812_);
lean_dec_ref(v_x_1811_);
lean_dec(v_x_1810_);
v___x_1822_ = lean_obj_once(&l_Lean_Json_setObjVal_x21___closed__2, &l_Lean_Json_setObjVal_x21___closed__2_once, _init_l_Lean_Json_setObjVal_x21___closed__2);
v___x_1823_ = l_panic___at___00Lean_Json_setObjVal_x21_spec__1(v___x_1822_);
return v___x_1823_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0(lean_object* v_00_u03b2_1824_, lean_object* v_msg_1825_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v_msg_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0(lean_object* v_00_u03b2_1827_, lean_object* v_k_1828_, lean_object* v_v_1829_, lean_object* v_t_1830_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1828_, v_v_1829_, v_t_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(lean_object* v_init_1832_, lean_object* v_x_1833_){
_start:
{
if (lean_obj_tag(v_x_1833_) == 0)
{
lean_object* v_k_1834_; lean_object* v_v_1835_; lean_object* v_l_1836_; lean_object* v_r_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v_k_1834_ = lean_ctor_get(v_x_1833_, 1);
lean_inc(v_k_1834_);
v_v_1835_ = lean_ctor_get(v_x_1833_, 2);
lean_inc(v_v_1835_);
v_l_1836_ = lean_ctor_get(v_x_1833_, 3);
lean_inc(v_l_1836_);
v_r_1837_ = lean_ctor_get(v_x_1833_, 4);
lean_inc(v_r_1837_);
lean_dec_ref_known(v_x_1833_, 5);
v___x_1838_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_init_1832_, v_l_1836_);
v___x_1839_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_1834_, v_v_1835_, v___x_1838_);
v_init_1832_ = v___x_1839_;
v_x_1833_ = v_r_1837_;
goto _start;
}
else
{
return v_init_1832_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_mergeObj(lean_object* v_x_1841_, lean_object* v_x_1842_){
_start:
{
if (lean_obj_tag(v_x_1841_) == 5)
{
if (lean_obj_tag(v_x_1842_) == 5)
{
lean_object* v_kvPairs_1843_; lean_object* v_kvPairs_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1852_; 
v_kvPairs_1843_ = lean_ctor_get(v_x_1841_, 0);
lean_inc(v_kvPairs_1843_);
lean_dec_ref_known(v_x_1841_, 1);
v_kvPairs_1844_ = lean_ctor_get(v_x_1842_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v_x_1842_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1846_ = v_x_1842_;
v_isShared_1847_ = v_isSharedCheck_1852_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_kvPairs_1844_);
lean_dec(v_x_1842_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1852_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1848_; lean_object* v___x_1850_; 
v___x_1848_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_kvPairs_1843_, v_kvPairs_1844_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1848_);
v___x_1850_ = v___x_1846_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1848_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
else
{
lean_dec_ref_known(v_x_1841_, 1);
return v_x_1842_;
}
}
else
{
lean_dec(v_x_1841_);
return v_x_1842_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0(lean_object* v_init_1853_, lean_object* v_t_1854_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_init_1853_, v_t_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorIdx___impl(lean_object* v_x_1856_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = lean_obj_tag_nat(v_x_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorIdx___impl___boxed(lean_object* v_x_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_Lean_Json_Structured_ctorIdx___impl(v_x_1858_);
lean_dec_ref(v_x_1858_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim___redArg(lean_object* v_t_1860_, lean_object* v_k_1861_){
_start:
{
if (lean_obj_tag(v_t_1860_) == 0)
{
lean_object* v_elems_1862_; lean_object* v___x_1863_; 
v_elems_1862_ = lean_ctor_get(v_t_1860_, 0);
lean_inc_ref(v_elems_1862_);
lean_dec_ref_known(v_t_1860_, 1);
v___x_1863_ = lean_apply_1(v_k_1861_, v_elems_1862_);
return v___x_1863_;
}
else
{
lean_object* v_kvPairs_1864_; lean_object* v___x_1865_; 
v_kvPairs_1864_ = lean_ctor_get(v_t_1860_, 0);
lean_inc(v_kvPairs_1864_);
lean_dec_ref_known(v_t_1860_, 1);
v___x_1865_ = lean_apply_1(v_k_1861_, v_kvPairs_1864_);
return v___x_1865_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim(lean_object* v_motive_1866_, lean_object* v_ctorIdx_1867_, lean_object* v_t_1868_, lean_object* v_h_1869_, lean_object* v_k_1870_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1868_, v_k_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_ctorElim___boxed(lean_object* v_motive_1872_, lean_object* v_ctorIdx_1873_, lean_object* v_t_1874_, lean_object* v_h_1875_, lean_object* v_k_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_Json_Structured_ctorElim(v_motive_1872_, v_ctorIdx_1873_, v_t_1874_, v_h_1875_, v_k_1876_);
lean_dec(v_ctorIdx_1873_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_arr_elim___redArg(lean_object* v_t_1878_, lean_object* v_arr_1879_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1878_, v_arr_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_arr_elim(lean_object* v_motive_1881_, lean_object* v_t_1882_, lean_object* v_h_1883_, lean_object* v_arr_1884_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1882_, v_arr_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_obj_elim___redArg(lean_object* v_t_1886_, lean_object* v_obj_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1886_, v_obj_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_obj_elim(lean_object* v_motive_1889_, lean_object* v_t_1890_, lean_object* v_h_1891_, lean_object* v_obj_1892_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_1890_, v_obj_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeArrayStructured___lam__0(lean_object* v_elems_1894_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1895_, 0, v_elems_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instCoeRawStringStructured___lam__0(lean_object* v_kvPairs_1898_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1899_, 0, v_kvPairs_1898_);
return v___x_1899_;
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
